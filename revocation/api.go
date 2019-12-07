/*
Package revocation implements the RSA-B accumulator and associated zero knowledge proofs, introduced
in "Dynamic Accumulators and Application to Efficient Revocation of Anonymous Credentials",
Jan Camenisch and Anna Lysyanskaya, CRYPTO 2002, DOI https://doi.org/10.1007/3-540-45708-9_5,
http://static.cs.brown.edu/people/alysyans/papers/camlys02.pdf, and "Accumulators with Applications
to Anonymity-Preserving Revocation", Foteini Baldimtsi et al, IEEE 2017,
DOI https://doi.org/10.1109/EuroSP.2017.13, https://eprint.iacr.org/2017/043.pdf.

In short, revocation works as follows.

- Revokable credentials receive a "nonrevocation witness" consisting of two numbers, u and e,
of which e is added to the credential as a new (hidden) "nonrevocation attribute".

- The issuer publishes an Accumulator, i.e a bigint Nu (the greek letter 𝛎). The witness is valid
only if u^e = Nu mod N where N is the modulus of the (Idemix) public key of the issuer, i.e. e is
"accumulated" in Nu.

- The client can during an IRMA disclosure session prove in zero knowledge that it knows numbers u
and e such that (1) u^e = Nu mod N (2) e equals the credential's nonrevocation attribute, from
which the verifier concludes that the credential is not currently revoked.

- The issuer can revoke a credential by removing its nonrevocation attribute e from the accumulator, by
  (1) Updating the accumulator value as follows:
         NewNu := Nu^(1/e mod (P-1)*(Q-1))
      where P, Q is the issuer Idemix private key
  (2) Broadcasting (NewNu, e) to all IRMA apps and verifiers
  (3) All IRMA clients update their nonrevocation witness, using an algorithm taking the broadcast
      message and the client's current witness, resulting in a new u which is such that
      u^e = NewNu mod N. This algorithm is guaranteed to fail for the credential containing the
      revoked nonrevocation attribute e.

To keep track of previous and current accumulators, each Accumulator has an index which is
incremented each time a credential is revoked and the accumulator changes value.

Issuers supporting revocation use ECDSA private/public keys to sign the accumulator update messages.
All IRMA participants (client, verifier, issuer) require the latest revocation record to be able
to function. The client additionally needs to know the complete chain of all events to be able to
update its witness to the latest accumulator.

Notes

By revoking, the issuer changes the value of the accumulator, of which all IRMA clients and
verifiers need to be made aware before the client can prove to the verifier that its credential is
not revoked against the new accumulator. If the client and verifier do not agree on the current
value of the accumulator (for example, the client has not received all revocation broadcast messages
while the verifier has), then the client cannot prove nonrevocation, leading the verifier to reject
the client. The issuer thus has an important responsibility to ensure that all its revocation
broadcast messages are always available to all IRMA participants.

If one thinks of the accumulator as a "nonrevocation public key", then the witness can be thought of
as a "nonrevocation signature" which verifies against that public key (either directly or in zero
knowledge). (That this "nonrevocation public key" changes when a credential is revoked, i.e. the
accumulator is updated, has however no equivalent in signature schemes.)

Unlike ours, accumulators generally have both an Add and Remove algorithm, adding or removing stuff
from the accumulator. The RSA-B has the property that the Add algorithm does nothing, i.e. all
revocation witnesses e are added to it "automatically", and only removing one from the accumulator
actually constitutes work (and broadcasting update messages).

In the literature the agent that is able to revoke (using a PrivateKey) is usually called the
"revocation authority", which generally need not be the same agent as the issuer. In IRMA the design
choice was made instead that the issuer is always the revocation authority.
*/
package revocation

import (
	"crypto/ecdsa"
	"crypto/sha256"
	"database/sql/driver" // only imported to refer to the driver.Value type
	"encoding/base64"
	"encoding/binary"
	"encoding/json"

	"github.com/go-errors/errors"
	"github.com/jinzhu/gorm"

	"github.com/privacybydesign/gabi/big"
	"github.com/privacybydesign/gabi/internal/common"
	"github.com/privacybydesign/gabi/signed"
)

type (
	// Accumulator is an RSA-B accumulator against which clients with a corresponding Witness
	// having the same Index can prove that their witness is accumulated, i.e. not revoked.
	Accumulator struct {
		Nu        *big.Int
		Index     uint64
		EventHash Hash
	}

	// SignedAccumulator is the above signed with the issuer's ECDSA key, along with the key index.
	SignedAccumulator struct {
		Message signed.Message
		PKIndex uint
	}

	// Event contains the data clients need to update to the Accumulator of the specified index,
	// after it has been updated by the issuer by revoking. Forms a chain through the
	// ParentHash which is the SHA256 hash of its parent.
	Event struct {
		Index      uint64 `gorm:"primary_key"`
		E          *big.Int
		ParentHash Hash
	}

	// Update contains all information for clients to update their witness to the latest accumulator:
	// the accumulator itself and a set of revocation attributes.
	// Its hash structure makes this message into a chain with the SignedAccumulator on top:
	// The accumulator contains the hash of the first Event, and each Event has a hash of its parent.
	// Thus the signature over the accumulator effectively signs the entire Update message,
	// and the partial tree specified by Events is verifiable regardless of its length.
	Update struct { // TODO: make these not pointers?
		SignedAccumulator *SignedAccumulator
		Events            []*Event
	}

	// Hash represents a SHA256 hash and has marshaling methods to/from JSON and SQL tables.
	Hash [32]byte

	// Witness is a witness for the RSA-B accumulator, used for proving nonrevocation against the
	// Accumulator with the same Index.
	Witness struct {
		// U^E = Accumulator.Nu mod N
		U, E *big.Int
		// Accumulator against which the witness verifies.
		SignedAccumulator *SignedAccumulator
		// Accumulator value for local computations, extracted from verified SignedAccumulator
		Accumulator *Accumulator `json:"-"`

		randomizer *big.Int
	}

	// PrivateKey is the private key needed for revoking.
	PrivateKey struct {
		Counter uint
		ECDSA   *ecdsa.PrivateKey
		P, Q, N *big.Int
	}

	// PublicKey is the public key corresponding to PrivateKey, against which witness (zero-knowledge
	// proofs) are verified (containing fixed data as opposed to the Accumulator).
	PublicKey struct {
		Counter uint
		ECDSA   *ecdsa.PublicKey
		Group   *QrGroup
	}
)

// Hash returns the SHA256 hash of the Event.
func (event *Event) Hash() Hash {
	// TODO
	bts := make([]byte, 8, 8+len(event.ParentHash)+int(parameters.attributeMaxSize)/8)
	binary.BigEndian.PutUint64(bts, event.Index)
	bts = append(bts, event.ParentHash[:]...)
	bts = append(bts, event.E.Bytes()...)
	return sha256.Sum256(bts)
}

const AccumulatorStartIndex uint64 = 1

func NewAccumulator(sk *PrivateKey) (*Update, error) {
	initialEvent := &Event{
		Index:      AccumulatorStartIndex,
		E:          big.NewInt(0),
		ParentHash: Hash{},
	}
	acc := &Accumulator{
		Nu:        common.RandomQR(sk.N),
		Index:     AccumulatorStartIndex,
		EventHash: initialEvent.Hash(),
	}
	sig, err := acc.Sign(sk)
	if err != nil {
		return nil, err
	}
	return &Update{
		SignedAccumulator: sig,
		Events:            []*Event{initialEvent},
	}, nil
}

// Sign the accumulator into a SignedAccumulator (c.f. SignedAccumulator.UnmarshalVerify()).
func (acc *Accumulator) Sign(sk *PrivateKey) (*SignedAccumulator, error) {
	sig, err := signed.MarshalSign(sk.ECDSA, acc)
	if err != nil {
		return nil, err
	}
	return &SignedAccumulator{Message: sig, PKIndex: sk.Counter}, nil
}

// Remove generates a new accumulator with the specified e removed from it; signs it;
// and returns an Update message for clients to update their witness.
func (acc *Accumulator) Remove(sk *PrivateKey, e *big.Int, parent *Event) (*Update, error) {
	eInverse, ok := common.ModInverse(e, new(big.Int).Mul(sk.P, sk.Q))
	if !ok {
		// since N = P*Q and P, Q prime, e has no inverse if and only if e equals either P or Q
		return nil, errors.New("revocation attribute has no inverse")
	}

	newAcc := Accumulator{
		Index: acc.Index + 1,
		Nu:    new(big.Int).Exp(acc.Nu, eInverse, sk.N),
	}
	event := &Event{
		Index:      newAcc.Index,
		E:          e,
		ParentHash: parent.Hash(),
	}
	newAcc.EventHash = event.Hash()

	sig, err := newAcc.Sign(sk)
	if err != nil {
		return nil, err
	}

	return &Update{
		SignedAccumulator: sig,
		Events:            []*Event{event},
	}, nil
}

// UnmarshalVerify verifies the signature and unmarshals the accumulator
// (c.f. Accumulator.Sign()).
func (s *SignedAccumulator) UnmarshalVerify(pk *PublicKey) (*Accumulator, error) {
	msg := &Accumulator{}
	if pk.Counter != s.PKIndex {
		return nil, errors.New("wrong public key")
	}
	if err := signed.UnmarshalVerify(pk.ECDSA, s.Message, msg); err != nil {
		return nil, err
	}
	return msg, nil
}

// Verify the witness against its SignedAccumulator.
func (w *Witness) Verify(pk *PublicKey) error {
	acc, err := w.SignedAccumulator.UnmarshalVerify(pk)
	if err != nil {
		return err
	}
	w.Accumulator = acc
	if !verify(w.U, w.E, w.Accumulator, pk.Group) {
		return errors.New("invalid witness")
	}
	return nil
}

func (hash *Hash) MarshalJSON() ([]byte, error) {
	return json.Marshal(hash.String())
}

func (hash *Hash) UnmarshalJSON(b []byte) error {
	var s string
	err := json.Unmarshal(b, &s)
	if err != nil {
		return err
	}
	b, err = base64.URLEncoding.DecodeString(s)
	if err != nil {
		return err
	}
	copy(hash[:], b)
	return nil
}

func (hash Hash) String() string {
	return base64.URLEncoding.EncodeToString(hash[:])
}

func (hash Hash) Value() (driver.Value, error) {
	return hash[:], nil
}

func (hash *Hash) Scan(src interface{}) error {
	s, ok := src.([]byte)
	if !ok {
		return errors.New("cannot convert source: not a []byte")
	}
	copy((*hash)[:], s)
	return nil
}

func (Hash) GormDataType(dialect gorm.Dialect) string {
	switch dialect.GetName() {
	case "postgres":
		return "bytea"
	case "mysql":
		return "blob"
	default:
		return ""
	}
}
