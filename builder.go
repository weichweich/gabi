// Copyright 2016 Maarten Everts. All rights reserved.
// Use of this source code is governed by a BSD-style
// license that can be found in the LICENSE file.

package gabi

import (
	"encoding/json"

	"github.com/go-errors/errors"

	"github.com/privacybydesign/gabi/big"
	"github.com/privacybydesign/gabi/internal/common"
	"github.com/privacybydesign/gabi/revocation"
)

// IssueCommitmentMessage encapsulates the messages sent by the receiver to the
// issuer in the second step of the issuance protocol.
type IssueCommitmentMessage struct {
	U          *big.Int          `json:"U,omitempty"`
	Nonce2     *big.Int          `json:"n_2"`
	Proofs     ProofList         `json:"combinedProofs"`
	ProofPjwt  string            `json:"proofPJwt,omitempty"`
	ProofPjwts map[string]string `json:"proofPJwts,omitempty"`
}

// UnmarshalJSON implements json.Unmarshaler (json's default unmarshaler
// is unable to handle a list of interfaces).
func (pl *ProofList) UnmarshalJSON(bytes []byte) error {
	proofs := []Proof{}
	temp := []json.RawMessage{}
	if err := json.Unmarshal(bytes, &temp); err != nil {
		return err
	}
	for _, proofbytes := range temp {
		proofd := &ProofD{}
		if err := json.Unmarshal(proofbytes, proofd); err != nil {
			return err
		}
		if proofd.A != nil {
			proofs = append(proofs, proofd)
			continue
		}
		proofu := &ProofU{}
		if err := json.Unmarshal(proofbytes, proofu); err != nil {
			return err
		}
		if proofu.U != nil {
			proofs = append(proofs, proofu)
			continue
		}
		return errors.New("Unknown proof type found in ProofList")
	}
	*pl = proofs
	return nil
}

// IssueSignatureMessage encapsulates the messages sent from the issuer to the
// reciver in the final step of the issuance protocol.
type IssueSignatureMessage struct {
	Proof                *ProofS             `json:"proof"`
	Signature            *CLSignature        `json:"signature"`
	NonRevocationWitness *revocation.Witness `json:"nonrev,omitempty"`
}

// commitmentToSecret produces a commitment to the provided secret
func commitmentToSecret(pk *PublicKey, secret *big.Int) (vPrime, U *big.Int) {
	vPrime, _ = common.RandomBigInt(pk.Params.LvPrime)
	// U = S^{vPrime} * R_0^{s}
	Sv := new(big.Int).Exp(pk.S, vPrime, pk.N)
	R0s := new(big.Int).Exp(pk.R[0], secret, pk.N)
	U = new(big.Int).Mul(Sv, R0s)
	U.Mod(U, pk.N)
	return
}

// NewCredentialBuilder creates a new credential builder. The resulting credential builder
// is already committed to the provided secret.
func NewCredentialBuilder(pk *PublicKey, context, secret *big.Int, nonce2 *big.Int) *CredentialBuilder {
	vPrime, U := commitmentToSecret(pk, secret)

	return &CredentialBuilder{
		Pk:      pk,
		Context: context,
		Secret:  secret,
		VPrime:  vPrime,
		U:       U,
		UCommit: big.NewInt(1),
		Nonce2:  nonce2,
	}
}

// CommitToSecretAndProve creates the response to the initial challenge nonce
// nonce1 sent by the issuer. The response consists of a commitment to the
// secret (set on creation of the builder, see NewBuilder) and a proof of
// correctness of this commitment.
func (b *CredentialBuilder) CommitToSecretAndProve(nonce1 *big.Int) *IssueCommitmentMessage {
	proofU := b.proveCommitment(b.U, nonce1)

	return &IssueCommitmentMessage{U: b.U, Proofs: ProofList{proofU}, Nonce2: b.Nonce2}
}

// CreateIssueCommitmentMessage creates the IssueCommitmentMessage based on the
// provided prooflist, to be sent to the issuer.
func (b *CredentialBuilder) CreateIssueCommitmentMessage(proofs ProofList) *IssueCommitmentMessage {
	return &IssueCommitmentMessage{U: b.U, Proofs: proofs, Nonce2: b.Nonce2}
}

var (
	// ErrIncorrectProofOfSignatureCorrectness is issued when the the proof of
	// correctness on the signature does not verify.
	ErrIncorrectProofOfSignatureCorrectness = errors.New("Proof of correctness on signature does not verify.")
	// ErrIncorrectAttributeSignature is issued when the signature on the
	// attributes is not correct.
	ErrIncorrectAttributeSignature = errors.New("The Signature on the attributes is not correct.")
)

// ConstructCredential creates a credential using the IssueSignatureMessage from
// the issuer and the content of the attributes.
func (b *CredentialBuilder) ConstructCredential(msg *IssueSignatureMessage, attributes []*big.Int) (*Credential, error) {
	if !msg.Proof.Verify(b.Pk, msg.Signature, b.Context, b.Nonce2) {
		return nil, ErrIncorrectProofOfSignatureCorrectness
	}

	// Construct actual signature
	signature := &CLSignature{
		A: msg.Signature.A,
		E: msg.Signature.E,
		V: new(big.Int).Add(msg.Signature.V, b.VPrime),
	}
	if b.ProofPcomm != nil {
		signature.KeyshareP = b.ProofPcomm.P
	}

	// Verify signature
	exponents := make([]*big.Int, len(attributes)+1)
	exponents[0] = b.Secret
	copy(exponents[1:], attributes)

	var nonrevAttr *big.Int
	if msg.NonRevocationWitness != nil {
		nonrevAttr = msg.NonRevocationWitness.E
		rpk, err := b.Pk.RevocationKey()
		if err != nil {
			return nil, err
		}
		if err = msg.NonRevocationWitness.Verify(rpk); err != nil {
			return nil, err
		}
	}
	if !signature.Verify(b.Pk, exponents, nonrevAttr) {
		return nil, ErrIncorrectAttributeSignature
	}
	return &Credential{
		Pk:                   b.Pk,
		Signature:            signature,
		Attributes:           exponents,
		NonRevocationWitness: msg.NonRevocationWitness,
	}, nil
}

func (b *CredentialBuilder) proveCommitment(U, nonce1 *big.Int) *ProofU {
	sCommit, _ := common.RandomBigInt(b.Pk.Params.LsCommit)
	vPrimeCommit, _ := common.RandomBigInt(b.Pk.Params.LvPrimeCommit)

	// Ucommit = S^{vPrimeCommit} * R_0^{sCommit}
	Sv := new(big.Int).Exp(b.Pk.S, vPrimeCommit, b.Pk.N)
	R0s := new(big.Int).Exp(b.Pk.R[0], sCommit, b.Pk.N)
	Ucommit := new(big.Int).Mul(Sv, R0s)
	Ucommit.Mod(Ucommit, b.Pk.N)

	c := common.HashCommit([]*big.Int{b.Context, U, Ucommit, nonce1}, false)
	sResponse := new(big.Int).Mul(c, b.Secret)
	sResponse.Add(sResponse, sCommit)

	vPrimeResponse := new(big.Int).Mul(c, b.VPrime)
	vPrimeResponse.Add(vPrimeResponse, vPrimeCommit)

	return &ProofU{U: U, C: c, VPrimeResponse: vPrimeResponse, SResponse: sResponse}
}

// CredentialBuilder is a temporary object to hold some state for the protocol
// that is used to create (build) a credential. It also implements the
// ProofBuilder interface.
type CredentialBuilder struct {
	Secret       *big.Int `json:"Secret"`
	VPrime       *big.Int `json:"VPrime"`
	VPrimeCommit *big.Int `json:"VPrimeCommit"`
	Nonce2       *big.Int `json:"Nonce2"`
	U            *big.Int `json:"U"`
	UCommit      *big.Int `json:"UCommit"`
	SkRandomizer *big.Int `json:"SkRandomizer"`

	Pk         *PublicKey        `json:"Pk"`
	Context    *big.Int          `json:"Context"`
	ProofPcomm *ProofPCommitment `json:"ProofPcomm"`
}

func (b *CredentialBuilder) MergeProofPCommitment(commitment *ProofPCommitment) {
	b.ProofPcomm = commitment
	b.UCommit.Mod(
		b.UCommit.Mul(b.UCommit, commitment.Pcommit),
		b.Pk.N,
	)
}

// PublicKey returns the Idemix public key against which the credential will verify.
func (b *CredentialBuilder) PublicKey() *PublicKey {
	return b.Pk
}

// Commit commits to the secret (first) attribute using the provided randomizer.
func (b *CredentialBuilder) Commit(randomizers map[string]*big.Int) []*big.Int {
	b.SkRandomizer = randomizers["secretkey"]
	// vPrimeCommit
	b.VPrimeCommit, _ = common.RandomBigInt(b.Pk.Params.LvPrimeCommit)

	// U_commit = U_commit * S^{v_prime_commit} * R_0^{s_commit}
	sv := new(big.Int).Exp(b.Pk.S, b.VPrimeCommit, b.Pk.N)
	r0s := new(big.Int).Exp(b.Pk.R[0], b.SkRandomizer, b.Pk.N)
	b.UCommit.Mul(b.UCommit, sv).Mul(b.UCommit, r0s).Mod(b.UCommit, b.Pk.N)

	ucomm := new(big.Int).Set(b.U)
	if b.ProofPcomm != nil {
		ucomm.Mul(ucomm, b.ProofPcomm.P).Mod(ucomm, b.Pk.N)
	}
	return []*big.Int{ucomm, b.UCommit}
}

// CreateProof creates a (ProofU) Proof using the provided challenge.
func (b *CredentialBuilder) CreateProof(challenge *big.Int) Proof {
	sResponse := new(big.Int).Add(b.SkRandomizer, new(big.Int).Mul(challenge, b.Secret))
	vPrimeResponse := new(big.Int).Add(b.VPrimeCommit, new(big.Int).Mul(challenge, b.VPrime))

	return &ProofU{U: b.U, C: challenge, VPrimeResponse: vPrimeResponse, SResponse: sResponse}
}
