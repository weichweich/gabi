package keyproof

import "github.com/privacybydesign/gabi/pkg/common"
import "github.com/privacybydesign/gabi/big"

type expStepStructure struct {
	bitname string
	stepa   expStepAStructure
	stepb   expStepBStructure
}

type expStepCommit struct {
	isTypeA bool

	acommit    expStepACommit
	aproof     ExpStepAProof
	achallenge *big.Int

	bcommit    expStepBCommit
	bproof     ExpStepBProof
	bchallenge *big.Int
}

type ExpStepProof struct {
	Achallenge *big.Int
	Aproof     ExpStepAProof

	Bchallenge *big.Int
	Bproof     ExpStepBProof
}

func newExpStepStructure(bitname, prename, postname, mulname, modname string, bitlen uint) expStepStructure {
	var structure expStepStructure
	structure.bitname = bitname
	structure.stepa = newExpStepAStructure(bitname, prename, postname)
	structure.stepb = newExpStepBStructure(bitname, prename, postname, mulname, modname, bitlen)
	return structure
}

func (s *expStepStructure) numRangeProofs() int {
	return s.stepa.numRangeProofs() + s.stepb.numRangeProofs()
}

func (s *expStepStructure) numCommitments() int {
	return s.stepa.numCommitments() + s.stepb.numCommitments()
}

func (s *expStepStructure) generateCommitmentsFromSecrets(g group, list []*big.Int, bases BaseLookup, secretdata SecretLookup) ([]*big.Int, expStepCommit) {
	var commit expStepCommit

	if secretdata.GetSecret(s.bitname).Cmp(big.NewInt(0)) == 0 {
		commit.isTypeA = true

		// prove a
		list, commit.acommit = s.stepa.generateCommitmentsFromSecrets(g, list, bases, secretdata)

		// fake b
		commit.bchallenge = common.FastRandomBigInt(new(big.Int).Lsh(big.NewInt(1), 256))
		commit.bproof = s.stepb.fakeProof(g)
		list = s.stepb.generateCommitmentsFromProof(g, list, commit.bchallenge, bases, commit.bproof)
	} else {
		commit.isTypeA = false

		// fake a
		commit.achallenge = common.FastRandomBigInt(new(big.Int).Lsh(big.NewInt(1), 256))
		commit.aproof = s.stepa.fakeProof(g)
		list = s.stepa.generateCommitmentsFromProof(g, list, commit.achallenge, bases, commit.aproof)

		// prove b
		list, commit.bcommit = s.stepb.generateCommitmentsFromSecrets(g, list, bases, secretdata)
	}

	return list, commit
}

func (s *expStepStructure) buildProof(g group, challenge *big.Int, commit expStepCommit, secretdata SecretLookup) ExpStepProof {
	var proof ExpStepProof

	if commit.isTypeA {
		// Build a proof
		proof.Achallenge = new(big.Int).Xor(challenge, commit.bchallenge)
		proof.Aproof = s.stepa.buildProof(g, proof.Achallenge, commit.acommit, secretdata)

		// Copy b proof
		proof.Bchallenge = commit.bchallenge
		proof.Bproof = commit.bproof
	} else {
		// Copy a proof
		proof.Achallenge = commit.achallenge
		proof.Aproof = commit.aproof

		// Build b proof
		proof.Bchallenge = new(big.Int).Xor(challenge, commit.achallenge)
		proof.Bproof = s.stepb.buildProof(g, proof.Bchallenge, commit.bcommit, secretdata)
	}

	return proof
}

func (s *expStepStructure) fakeProof(g group, challenge *big.Int) ExpStepProof {
	var proof ExpStepProof

	proof.Achallenge = common.FastRandomBigInt(new(big.Int).Lsh(big.NewInt(1), 256))
	proof.Bchallenge = new(big.Int).Xor(challenge, proof.Achallenge)
	proof.Aproof = s.stepa.fakeProof(g)
	proof.Bproof = s.stepb.fakeProof(g)

	return proof
}

func (s *expStepStructure) verifyProofStructure(challenge *big.Int, proof ExpStepProof) bool {
	if proof.Achallenge == nil || proof.Bchallenge == nil {
		return false
	}

	if challenge.Cmp(new(big.Int).Xor(proof.Achallenge, proof.Bchallenge)) != 0 {
		return false
	}

	return s.stepa.verifyProofStructure(proof.Aproof) && s.stepb.verifyProofStructure(proof.Bproof)
}

func (s *expStepStructure) generateCommitmentsFromProof(g group, list []*big.Int, challenge *big.Int, bases BaseLookup, proof ExpStepProof) []*big.Int {
	list = s.stepa.generateCommitmentsFromProof(g, list, proof.Achallenge, bases, proof.Aproof)
	list = s.stepb.generateCommitmentsFromProof(g, list, proof.Bchallenge, bases, proof.Bproof)
	return list
}

func (s *expStepStructure) isTrue(secretdata SecretLookup) bool {
	return s.stepa.isTrue(secretdata) || s.stepb.isTrue(secretdata)
}
