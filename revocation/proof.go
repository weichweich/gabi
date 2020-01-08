package revocation

import (
	"crypto/rand"

	"github.com/go-errors/errors"
	"github.com/privacybydesign/gabi/big"
	"github.com/privacybydesign/gabi/pkg/common"
	"github.com/privacybydesign/gabi/keyproof"
)

/*
This implements the zero knowledge proof of the RSA-B accumulator for revocation, introduced in
"Dynamic Accumulators and Application to Efficient Revocation of Anonymous Credentials",
Jan Camenisch and Anna Lysyanskaya, CRYPTO 2002, DOI https://doi.org/10.1007/3-540-45708-9_5,
http://static.cs.brown.edu/people/alysyans/papers/camlys02.pdf. This accumulator is only updated
when revoking and does not change when adding new revocation handles to the accumulator.

The user proves knowledge of two numbers u and e, called the witness, which are such that the relation
    u^e = 𝛎 mod n
holds, where 𝛎 (greek letter "nu") is the accumulator (the issuer's current "non-revocation publickey").
Both u and e are kept secret to the user. Elsewhere the number e is included as an attribute in an
IRMA credential, and this zero-knowledge proof convinces the verifier that the containing credential
is not revoked.

This is an implementation of the zero-knowledge proof at page 8 and 15 of the pdf linked to above,
with the following differences.
1. In the zero knowledge proof conjunction on page 8 of the pdf, we skip the first, second and
   third items in the conjunction: these only serve to prove that the secret e is committed to
   in an element of a known prime order group. We don't need to do this as we have no such group:
   in our case everything happens within QR_n.
2. The fifth relation C_e = g^e * h^r1 is replaced by the Idemix relation
   Z = A^epsilon * S^v * Ri^mi * Re^e which is already proved elsewhere by the calling code.
3. The interval [A, B] from which the witness e is chosen does not satisfy the relation
   B*2^(k'+k''+1) < A^2 - 1, which is unnecessary: as long as A > 2 witnesses are unforgeable,
   by a simple extension of the unforgeability proof of Theorem 3. See below.
In the following we follow the lead of the other zero knowledge proofs implemented elsehwere in gabi.
4. Secrets and randomizers within the zero-knowledge proofs are taken positive, instead of from
   symmetric intervals [-A,A].
5. We use addition in the zero-knowledge proof responses: response = randomizer + challenge*secret.
6. We use the Fiat-Shamir heuristic.
7. We include the challenge c in the proof, and then verify by hashing the Schnorr commitments
   reconstructed from the proof, obtaining c' which must then equal c.

We claim, prove, and implement the following:
Let [A, B] be the interval from which the number e from the witness (u,e) is chosen, as in the paper.
Then witnesses are unforgeable as in theorem 3, if A > 2 and B < 2^(l_n-1) where l_n
is the bitsize of the modulus n. In particular, it is not necesary to assume A^2 > B
like theorem 3 does.

Proof: let (u')^(x') = u^x where x = x_1*...*x_n, and set d = gcd(x, x'), as in the proof.
Suppose that d is not relatively prime to phi(n) = 4*p'*q', i.e. d divides 4*p'*q'.
Now d <= x' < 2^(l_n-1) < phi(n), and d > 2 because x_j > 2 for all j.
So d can only equal p' or q' or p'*q'. In the first two cases, we have succeeded in factoring
n = p*q = (2p'+1)(2q'+1). In the third case, given p'*q' it is easy to check if
4*p'*q' = (p-1)(q-1) is the group modulus. If so then p and q, thus also p' and q',
can be reconstructed. Thus n is also factored.
The remainder of the proof which handles the other case, where d is relatively prime
to phi(n), works as is.
The claim "d = gcd(x,x') => (d = 1 or d = x_j)" in the middle of the proof, which requires
A^2 > B for its proof, is thus not necessary to use in the proof of theorem 3.

Thus for unforgeability the size of e is not relevant. However, e should be chosen from a set so large
that it is overhelmingly unlikely that any one prime e is chosen twice. Combining the prime counting
function with the birthday paradox and simplifying, one finds the following: if N witnesses are chosen
from the set of primes smaller than B, then the collision chance P approximately equals
   P = 1 - e^(-N^2 ln(B)/B).
At n = 10^9 we have P = 1/2^128 if B = 2^195.
The client also proves to the verifier that e < B * 2^(k'+k''+2) = 2^(k'+k''+197),
where k' = 128 is the security parameter of the statistical zero-knoweldgeness of the proof
and k'' = 256 is the length of the challenge used in the zero knowledge proof. This is far
below the limit 2^(l_n-1).
*/

type (
	// Proof is a proof that a Witness is valid against the Accumulator from the specified
	// SignedAccumulator.
	Proof struct {
		Cr                *big.Int            `json:"C_r"` // Cr = g^r2 * h^r3      = g^epsilon * h^zeta
		Cu                *big.Int            `json:"C_u"` // Cu = u    * h^r2
		Nu                *big.Int            `json:"-"`   // nu = Cu^e * h^(-e*r2) = Cu^alpha * h^-beta
		Challenge         *big.Int            `json:"-"`
		Responses         map[string]*big.Int `json:"responses"`
		SignedAccumulator *SignedAccumulator  `json:"sacc"`
		acc               *Accumulator        // Extracted from SignedAccumulator during verification
	}

	// ProofCommit contains the commitment state of a nonrevocation Proof.
	ProofCommit struct {
		cu, cr, nu  *big.Int
		secrets     map[string]*big.Int
		randomizers map[string]*big.Int
		g           *qrGroup
		sacc        *SignedAccumulator
	}

	proofStructure struct {
		cr  qrRepresentationProofStructure
		nu  qrRepresentationProofStructure
		one qrRepresentationProofStructure
	}

	// We implement the keyproof interfaces, containing exported methods, without exposing those
	// methods outside the package by implementing them on unexported structs - at the cost of
	// having to cast back and forth between these equivalent types when crossing the API boundary
	proof       Proof
	proofCommit ProofCommit
	accumulator Accumulator
	witness     Witness
	qrGroup     QrGroup
)

var (
	ErrorRevoked = errors.New("revoked")

	parameters = struct {
		attributeSize    uint     // maximum size in bits for prime e
		challengeLength  uint     // k'  = len(SHA256) = 256
		zkStat           uint     // k'' = 128
		twoZk, bTwoZk, b *big.Int // 2^(k'+k''), B*2^(k'+k''+1), 2^attributeSize
	}{
		attributeSize:   195,
		challengeLength: 256,
		zkStat:          128,
	}

	bigOne         = big.NewInt(1)
	secretNames    = []string{"alpha", "beta", "delta", "epsilon", "zeta"}
	proofstructure = proofStructure{
		cr: qrRepresentationProofStructure{
			Lhs: []keyproof.LhsContribution{{Base: "cr", Power: bigOne}},
			Rhs: []keyproof.RhsContribution{
				{Base: "g", Secret: "epsilon", Power: 1}, // r2
				{Base: "h", Secret: "zeta", Power: 1},    // r3
			},
		},
		nu: qrRepresentationProofStructure{
			Lhs: []keyproof.LhsContribution{{Base: "nu", Power: bigOne}},
			Rhs: []keyproof.RhsContribution{
				{Base: "cu", Secret: "alpha", Power: 1}, // e
				{Base: "h", Secret: "beta", Power: -1},  // e r2
			},
		},
		one: qrRepresentationProofStructure{
			Lhs: []keyproof.LhsContribution{{Base: "one", Power: bigOne}},
			Rhs: []keyproof.RhsContribution{
				{Base: "cr", Secret: "alpha", Power: 1}, // e
				{Base: "g", Secret: "beta", Power: -1},  // e r2
				{Base: "h", Secret: "delta", Power: -1}, // e r3
			},
		},
	}
)

func init() {
	// Compute derivative parameters
	parameters.b = new(big.Int).Lsh(bigOne, parameters.attributeSize)
	parameters.twoZk = new(big.Int).Lsh(bigOne, parameters.challengeLength+parameters.zkStat)
	parameters.bTwoZk = new(big.Int).Mul(parameters.b, new(big.Int).Mul(parameters.twoZk, big.NewInt(2)))
}

// API

// NewProofRandomizer returns a bigint suitable for use as the randomizer in a nonrevocation
// zero knowledge proof.
func NewProofRandomizer() *big.Int {
	return common.FastRandomBigInt(new(big.Int).Mul(parameters.b, parameters.twoZk))
}

// RandomWitness returns a new random Witness valid against the specified Accumulator.
func RandomWitness(sk *PrivateKey, acc *Accumulator) (*Witness, error) {
	e, err := common.RandomPrimeInRange(rand.Reader, 3, parameters.attributeSize)
	if err != nil {
		return nil, err
	}
	return newWitness(sk, acc, e)
}

// NewProofCommit performs the first move in the Schnorr zero-knowledge protocol: committing to randomizers.
func NewProofCommit(grp *QrGroup, witn *Witness, randomizer *big.Int) ([]*big.Int, *ProofCommit, error) {
	witn.randomizer = randomizer
	if randomizer == nil {
		witn.randomizer = NewProofRandomizer()
	}
	if !proofstructure.isTrue((*witness)(witn), witn.Accumulator.Nu, grp.N) {
		return nil, nil, errors.New("non-revocation relation does not hold")
	}

	bases := keyproof.NewBaseMerge((*qrGroup)(grp), &accumulator{Nu: witn.Accumulator.Nu})
	list, commit := proofstructure.generateCommitmentsFromSecrets((*qrGroup)(grp), []*big.Int{}, &bases, (*witness)(witn))
	commit.sacc = witn.SignedAccumulator
	return list, (*ProofCommit)(&commit), nil
}

// SetExpected sets certain values of the proof to expected values, inferred from the containing proofs,
// before verification.
func (p *Proof) SetExpected(pk *PublicKey, challenge, response *big.Int) error {
	acc, err := p.SignedAccumulator.UnmarshalVerify(pk)
	if err != nil {
		return err
	}
	p.Nu = acc.Nu
	p.Challenge = challenge
	p.Responses["alpha"] = response
	return nil
}

func (p *Proof) ChallengeContributions(grp *QrGroup) []*big.Int {
	return proofstructure.generateCommitmentsFromProof((*qrGroup)(grp), []*big.Int{},
		p.Challenge, (*qrGroup)(grp), (*proof)(p), (*proof)(p))
}

func (p *Proof) VerifyWithChallenge(pk *PublicKey, reconstructedChallenge *big.Int) bool {
	if !proofstructure.verifyProofStructure((*proof)(p)) {
		return false
	}
	if (*proof)(p).GetResult("alpha").Cmp(parameters.bTwoZk) > 0 {
		return false
	}
	acc, err := p.SignedAccumulator.UnmarshalVerify(pk)
	if err != nil {
		return false
	}
	p.acc = acc
	if p.Nu.Cmp(p.acc.Nu) != 0 {
		return false
	}
	return p.Challenge.Cmp(reconstructedChallenge) == 0
}

func (c *ProofCommit) BuildProof(challenge *big.Int) *Proof {
	responses := make(map[string]*big.Int, 5)
	for _, name := range secretNames {
		responses[name] = new(big.Int).Add(
			(*proofCommit)(c).GetRandomizer(name),
			new(big.Int).Mul(
				challenge,
				(*proofCommit)(c).GetSecret(name)),
		)
	}

	return &Proof{
		Cr: c.cr, Cu: c.cu, Nu: c.nu,
		Challenge:         challenge,
		Responses:         responses,
		SignedAccumulator: c.sacc,
	}
}

func (c *ProofCommit) Update(commitments []*big.Int, witness *Witness) {
	c.cu = new(big.Int).Exp(c.g.H, c.secrets["epsilon"], c.g.N)
	c.cu.Mul(c.cu, witness.U)
	c.nu = witness.Accumulator.Nu
	c.sacc = witness.SignedAccumulator

	commit := (*proofCommit)(c)
	b := keyproof.NewBaseMerge(c.g, commit)
	l := proofstructure.nu.generateCommitmentsFromSecrets(c.g, []*big.Int{}, &b, commit)

	commitments[1] = c.cu
	commitments[2] = witness.Accumulator.Nu
	commitments[4] = l[0]
}

// Update updates the witness using the specified update data from the issuer,
// after which the witness can be used to prove nonrevocation against the latest Accumulator
// (contained in the update message).
func (w *Witness) Update(pk *PublicKey, update *Update) error {
	acc, prod, err := update.Verify(pk, w.Accumulator.Index)
	if err != nil {
		return err
	}

	startIndex, endIndex := update.Events[0].Index, acc.Index
	if endIndex <= w.Accumulator.Index || startIndex > w.Accumulator.Index+1 {
		return nil // update is already applied or too new
	}
	var a, b big.Int
	if new(big.Int).GCD(&a, &b, w.E, prod).Cmp(bigOne) != 0 {
		return ErrorRevoked
	}

	// u' = u^b * newNu^a mod n
	newU := new(big.Int)
	newU.Mul(
		new(big.Int).Exp(w.U, &b, pk.Group.N),
		new(big.Int).Exp(acc.Nu, &a, pk.Group.N),
	).Mod(newU, pk.Group.N)

	if !verify(newU, w.E, acc, pk.Group) {
		return errors.New("nonrevocation witness invalidated by update")
	}

	// Update witness state only now after all possible errors have not occured
	w.U = newU
	w.SignedAccumulator = update.SignedAccumulator
	w.Accumulator = acc

	return nil
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

// Zero-knowledge proof methods

func (c *proofCommit) Exp(ret *big.Int, name string, exp, n *big.Int) bool {
	ret.Exp(c.GetBase(name), exp, n)
	return true
}

func (c *proofCommit) GetBase(name string) *big.Int {
	switch name {
	case "cu":
		return c.cu
	case "cr":
		return c.cr
	case "nu":
		return c.nu
	case "one":
		return big.NewInt(1)
	default:
		return nil
	}
}

func (c *proofCommit) GetNames() []string {
	return []string{"cu", "cr", "nu", "one"}
}

func (c *proofCommit) GetSecret(name string) *big.Int {
	return c.secrets[name]
}

func (c *proofCommit) GetRandomizer(name string) *big.Int {
	return c.randomizers[name]
}

func (p *proof) GetResult(name string) *big.Int {
	return p.Responses[name]
}

func (p *proof) verify(pk *PublicKey) bool {
	grp := (*qrGroup)(pk.Group)
	commitments := proofstructure.generateCommitmentsFromProof(grp, []*big.Int{}, p.Challenge, grp, p, p)
	return (*Proof)(p).VerifyWithChallenge(pk, common.HashCommit(commitments, false))
}

func (s *proofStructure) generateCommitmentsFromSecrets(g *qrGroup, list []*big.Int, bases keyproof.BaseLookup, secretdata keyproof.SecretLookup) ([]*big.Int, proofCommit) {
	commit := proofCommit{
		g:           g,
		secrets:     make(map[string]*big.Int, 5),
		randomizers: make(map[string]*big.Int, 5),
		cu:          new(big.Int),
		cr:          new(big.Int),
		nu:          bases.GetBase("nu"),
	}

	r2 := common.FastRandomBigInt(g.nDiv4)
	r3 := common.FastRandomBigInt(g.nDiv4)

	alpha := secretdata.GetSecret("alpha")
	commit.secrets["alpha"] = alpha
	commit.secrets["beta"] = new(big.Int).Mul(alpha, r2)
	commit.secrets["delta"] = new(big.Int).Mul(alpha, r3)
	commit.secrets["epsilon"] = r2
	commit.secrets["zeta"] = r3

	commit.randomizers["alpha"] = secretdata.GetRandomizer("alpha")
	commit.randomizers["beta"] = common.FastRandomBigInt(g.nbDiv4twoZk)
	commit.randomizers["delta"] = common.FastRandomBigInt(g.nbDiv4twoZk)
	commit.randomizers["epsilon"] = common.FastRandomBigInt(g.nDiv4twoZk)
	commit.randomizers["zeta"] = common.FastRandomBigInt(g.nDiv4twoZk)

	var tmp big.Int

	// Set C_r = g^r2 * h^r3
	bases.Exp(commit.cr, "g", r2, g.N)
	bases.Exp(&tmp, "h", r3, g.N)
	commit.cr.Mul(commit.cr, &tmp).Mod(commit.cr, g.N)
	// Set C_u = u * h^r2
	bases.Exp(&tmp, "h", r2, g.N)
	commit.cu.Mul(secretdata.GetSecret("u"), &tmp).Mod(commit.cu, g.N)

	list = append(list, commit.cr, commit.cu, commit.nu)

	b := keyproof.NewBaseMerge(bases, &commit)
	list = s.cr.generateCommitmentsFromSecrets(g, list, &b, &commit)
	list = s.nu.generateCommitmentsFromSecrets(g, list, &b, &commit)
	list = s.one.generateCommitmentsFromSecrets(g, list, &b, &commit)

	return list, commit
}

func (s *proofStructure) generateCommitmentsFromProof(g *qrGroup, list []*big.Int, challenge *big.Int, bases keyproof.BaseLookup, proofdata keyproof.ProofLookup, proof *proof) []*big.Int {
	proofs := keyproof.NewProofMerge(proof, proofdata)

	b := keyproof.NewBaseMerge(g, &proofCommit{cr: proof.Cr, cu: proof.Cu, nu: proof.Nu})

	list = append(list, proof.Cr, proof.Cu, proof.Nu)
	list = s.cr.generateCommitmentsFromProof(g, list, challenge, &b, &proofs)
	list = s.nu.generateCommitmentsFromProof(g, list, challenge, &b, &proofs)
	list = s.one.generateCommitmentsFromProof(g, list, challenge, &b, &proofs)

	return list
}

func (s *proofStructure) verifyProofStructure(p *proof) bool {
	for _, name := range secretNames {
		if p.Responses[name] == nil {
			return false
		}
	}
	return p.Cr != nil && p.Cu != nil && p.Nu != nil && p.Challenge != nil
}

func (s *proofStructure) isTrue(secretdata keyproof.SecretLookup, nu, n *big.Int) bool {
	return new(big.Int).
		Exp(secretdata.GetSecret("u"), secretdata.GetSecret("alpha"), n).
		Cmp(nu) == 0
}

func (b accumulator) GetBase(name string) *big.Int {
	if name == "nu" {
		return b.Nu
	}
	return nil
}

func (b accumulator) Exp(ret *big.Int, name string, exp, n *big.Int) bool {
	if name == "nu" {
		ret.Exp(b.Nu, exp, n)
		return true
	}
	return false
}

func (b accumulator) GetNames() []string {
	return []string{"nu"}
}

func (w *witness) GetSecret(name string) *big.Int {
	switch name {
	case "alpha":
		return w.E
	case "u":
		return w.U
	}

	return nil
}

func (w *witness) GetRandomizer(name string) *big.Int {
	if name == "alpha" {
		return w.randomizer
	}
	return nil
}

// Helpers

func verify(u, e *big.Int, acc *Accumulator, grp *QrGroup) bool {
	return new(big.Int).Exp(u, e, grp.N).Cmp(acc.Nu) == 0
}

func newWitness(sk *PrivateKey, acc *Accumulator, e *big.Int) (*Witness, error) {
	order := new(big.Int).Mul(sk.P, sk.Q)
	eInverse, ok := common.ModInverse(e, order)
	if !ok {
		return nil, errors.New("failed to compute modular inverse")
	}
	u := new(big.Int).Exp(acc.Nu, eInverse, sk.N)
	return &Witness{U: u, E: e}, nil
}