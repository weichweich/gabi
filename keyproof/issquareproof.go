package keyproof

import (
	"fmt"
	"strings"

	"github.com/privacybydesign/gabi/big"
	"github.com/privacybydesign/gabi/pkg/common"
)

type (
	isSquareProofStructure struct {
		n               *big.Int
		nPedersen       pedersenStructure
		squares         []*big.Int
		squaresPedersen []pedersenStructure

		nRep RepresentationProofStructure

		squaresRep []RepresentationProofStructure
		rootsRep   []pedersenStructure
		rootsRange []rangeProofStructure
		rootsValid []multiplicationProofStructure
	}

	IsSquareProof struct {
		NProof          PedersenProof
		SquaresProof    []PedersenProof
		RootsProof      []PedersenProof
		RootsRangeProof []RangeProof
		RootsValidProof []MultiplicationProof
	}

	isSquareProofCommit struct {
		squares []pedersenCommit
		roots   []pedersenCommit
		n       pedersenCommit

		rootRangeCommit []rangeCommit
		rootValidCommit []multiplicationProofCommit
	}
)

func newIsSquareProofStructure(N *big.Int, Squares []*big.Int) isSquareProofStructure {
	// Setup basic structure
	result := isSquareProofStructure{
		n:               new(big.Int).Set(N),
		nPedersen:       newPedersenStructure("N"),
		squares:         make([]*big.Int, len(Squares)),
		squaresPedersen: make([]pedersenStructure, len(Squares)),
		nRep: RepresentationProofStructure{
			[]LhsContribution{
				{"N", big.NewInt(-1)},
				{"g", new(big.Int).Set(N)},
			},
			[]RhsContribution{
				{"h", "N_hider", -1},
			},
		},
		squaresRep: make([]RepresentationProofStructure, len(Squares)),
		rootsRep:   make([]pedersenStructure, len(Squares)),
		rootsRange: make([]rangeProofStructure, len(Squares)),
		rootsValid: make([]multiplicationProofStructure, len(Squares)),
	}

	// Copy values of squares and make pedersen structures for them
	for i, val := range Squares {
		result.squares[i] = new(big.Int).Set(val)
		result.squaresPedersen[i] = newPedersenStructure(strings.Join([]string{"s", fmt.Sprintf("%v", i)}, "_"))
	}

	// Setup representation proofs of square
	for i, val := range result.squares {
		result.squaresRep[i] = RepresentationProofStructure{
			[]LhsContribution{
				{strings.Join([]string{"s", fmt.Sprintf("%v", i)}, "_"), big.NewInt(-1)},
				{"g", new(big.Int).Set(val)},
			},
			[]RhsContribution{
				{"h", strings.Join([]string{"s", fmt.Sprintf("%v", i), "hider"}, "_"), -1},
			},
		}
	}

	// Setup representation proofs of roots
	for i := range Squares {
		result.rootsRep[i] = newPedersenStructure(
			strings.Join([]string{"r", fmt.Sprintf("%v", i)}, "_"))
	}

	// Setup range proof of roots
	for i := range Squares {
		result.rootsRange[i] = newPedersenRangeProofStructure(
			strings.Join([]string{"r", fmt.Sprintf("%v", i)}, "_"),
			0,
			uint(N.BitLen()))
	}

	// Setup proofs that the roots are roots
	for i := range Squares {
		result.rootsValid[i] = newMultiplicationProofStructure(
			strings.Join([]string{"r", fmt.Sprintf("%v", i)}, "_"),
			strings.Join([]string{"r", fmt.Sprintf("%v", i)}, "_"),
			"N",
			strings.Join([]string{"s", fmt.Sprintf("%v", i)}, "_"),
			uint(N.BitLen()))
	}

	return result
}

func (s *isSquareProofStructure) commitmentsFromSecrets(g group, list []*big.Int, P *big.Int, Q *big.Int) ([]*big.Int, isSquareProofCommit) {
	// Setup commit structure
	commit := isSquareProofCommit{
		squares:         make([]pedersenCommit, len(s.squares)),
		roots:           make([]pedersenCommit, len(s.squares)),
		rootRangeCommit: make([]rangeCommit, len(s.squares)),
		rootValidCommit: make([]multiplicationProofCommit, len(s.squares)),
	}

	// Build up the secrets
	for i, val := range s.squares {
		list, commit.squares[i] = s.squaresPedersen[i].commitmentsFromSecrets(g, list, val)
	}
	for i, val := range s.squares {
		root, ok := common.ModSqrt(val, []*big.Int{P, Q})
		if !ok {
			panic("Incorrect key")
		}
		list, commit.roots[i] = s.rootsRep[i].commitmentsFromSecrets(g, list, root)
	}
	list, commit.n = s.nPedersen.commitmentsFromSecrets(g, list, s.n)

	// Build up bases and secrets (this is ugly code, hopefully go2 will make this better someday)
	var baseList []BaseLookup
	var secretList []SecretLookup
	for i := range commit.squares {
		baseList = append(baseList, &commit.squares[i])
		secretList = append(secretList, &commit.squares[i])
	}
	for i := range commit.roots {
		baseList = append(baseList, &commit.roots[i])
		secretList = append(secretList, &commit.roots[i])
	}
	baseList = append(baseList, &commit.n)
	secretList = append(secretList, &commit.n)
	baseList = append(baseList, &g)
	bases := NewBaseMerge(baseList...)
	secrets := NewSecretMerge(secretList...)

	// Generate commitments
	list = append(list, s.n)
	for _, val := range s.squares {
		list = append(list, val)
	}
	list = s.nRep.commitmentsFromSecrets(g, list, &bases, &secrets)
	for i := range s.squaresRep {
		list = s.squaresRep[i].commitmentsFromSecrets(g, list, &bases, &secrets)
	}
	for i := range s.rootsRange {
		list, commit.rootRangeCommit[i] = s.rootsRange[i].commitmentsFromSecrets(g, list, &bases, &secrets)
	}
	for i := range s.rootsValid {
		list, commit.rootValidCommit[i] = s.rootsValid[i].commitmentsFromSecrets(g, list, &bases, &secrets)
	}

	return list, commit
}

func (s *isSquareProofStructure) buildProof(g group, challenge *big.Int, commit isSquareProofCommit) IsSquareProof {
	// Build up secrets (this is ugly code, hopefully go2 will make this better someday)
	var secretList []SecretLookup
	for i := range commit.squares {
		secretList = append(secretList, &commit.squares[i])
	}
	for i := range commit.roots {
		secretList = append(secretList, &commit.roots[i])
	}
	secretList = append(secretList, &commit.n)
	secrets := NewSecretMerge(secretList...)

	// Calculate proofs
	proof := IsSquareProof{
		NProof:          s.nPedersen.buildProof(g, challenge, commit.n),
		SquaresProof:    make([]PedersenProof, len(s.squares)),
		RootsProof:      make([]PedersenProof, len(s.squares)),
		RootsRangeProof: make([]RangeProof, len(s.squares)),
		RootsValidProof: make([]MultiplicationProof, len(s.squares)),
	}
	for i := range commit.squares {
		proof.SquaresProof[i] = s.squaresPedersen[i].buildProof(g, challenge, commit.squares[i])
	}
	for i := range commit.roots {
		proof.RootsProof[i] = s.rootsRep[i].buildProof(g, challenge, commit.roots[i])
	}
	for i := range s.rootsRange {
		proof.RootsRangeProof[i] = s.rootsRange[i].buildProof(g, challenge, commit.rootRangeCommit[i], &secrets)
	}
	for i := range s.rootsValid {
		proof.RootsValidProof[i] = s.rootsValid[i].buildProof(g, challenge, commit.rootValidCommit[i], &secrets)
	}

	return proof
}

func (s *isSquareProofStructure) verifyProofStructure(proof IsSquareProof) bool {
	if !s.nPedersen.verifyProofStructure(proof.NProof) {
		return false
	}
	if len(proof.SquaresProof) != len(s.squares) || len(proof.RootsProof) != len(s.squares) {
		return false
	}
	if len(proof.RootsRangeProof) != len(s.squares) || len(proof.RootsValidProof) != len(s.squares) {
		return false
	}
	for i := range s.squares {
		if !s.squaresPedersen[i].verifyProofStructure(proof.SquaresProof[i]) {
			return false
		}
		if !s.rootsRep[i].verifyProofStructure(proof.RootsProof[i]) {
			return false
		}
		if !s.rootsRange[i].verifyProofStructure(proof.RootsRangeProof[i]) {
			return false
		}
		if !s.rootsValid[i].verifyProofStructure(proof.RootsValidProof[i]) {
			return false
		}
	}

	return true
}

func (s *isSquareProofStructure) commitmentsFromProof(g group, list []*big.Int, challenge *big.Int, proof IsSquareProof) []*big.Int {
	// Setup names in pedersen proofs
	proof.NProof.setName("N")
	for i := range s.squares {
		proof.SquaresProof[i].setName(strings.Join([]string{"s", fmt.Sprintf("%v", i)}, "_"))
		proof.RootsProof[i].setName(strings.Join([]string{"r", fmt.Sprintf("%v", i)}, "_"))
	}

	// Build up bases and proofs mergers
	var baseList []BaseLookup
	var proofList []ProofLookup
	for i := range s.squares {
		baseList = append(baseList, &proof.SquaresProof[i])
		proofList = append(proofList, &proof.SquaresProof[i])
	}
	for i := range s.squares {
		baseList = append(baseList, &proof.RootsProof[i])
		proofList = append(proofList, &proof.RootsProof[i])
	}
	baseList = append(baseList, &proof.NProof)
	proofList = append(proofList, &proof.NProof)
	baseList = append(baseList, &g)
	var bases = NewBaseMerge(baseList...)
	var proofs = NewProofMerge(proofList...)

	// Build up commitment list
	for i := range s.squares {
		list = s.squaresPedersen[i].commitmentsFromProof(g, list, challenge, proof.SquaresProof[i])
	}
	for i := range s.squares {
		list = s.rootsRep[i].commitmentsFromProof(g, list, challenge, proof.RootsProof[i])
	}
	list = s.nPedersen.commitmentsFromProof(g, list, challenge, proof.NProof)
	list = append(list, s.n)
	for _, val := range s.squares {
		list = append(list, val)
	}
	list = s.nRep.commitmentsFromProof(g, list, challenge, &bases, &proofs)
	for i := range s.squares {
		list = s.squaresRep[i].commitmentsFromProof(g, list, challenge, &bases, &proofs)
	}
	for i := range s.squares {
		list = s.rootsRange[i].commitmentsFromProof(g, list, challenge, &bases, proof.RootsRangeProof[i])
	}
	for i := range s.squares {
		list = s.rootsValid[i].commitmentsFromProof(g, list, challenge, &bases, &proofs, proof.RootsValidProof[i])
	}

	return list
}

func (s *isSquareProofStructure) numRangeProofs() int {
	result := 0
	for _, ms := range s.rootsValid {
		result += ms.numRangeProofs()
	}

	return result + len(s.rootsRange)
}

func (s *isSquareProofStructure) numCommitments() int {
	// Constants
	res := 1 + len(s.squares)
	// Pedersens
	res += s.nPedersen.numCommitments()
	for i, _ := range s.squaresPedersen {
		res += s.squaresPedersen[i].numCommitments()
	}
	for i, _ := range s.rootsRep {
		res += s.rootsRep[i].numCommitments()
	}
	// Representationproofs
	res += s.nRep.numCommitments()
	for i, _ := range s.squaresRep {
		res += s.squaresRep[i].numCommitments()
	}
	// ValidityProofs
	for i := range s.rootsRange {
		res += s.rootsRange[i].numCommitments()
	}
	for i := range s.rootsValid {
		res += s.rootsValid[i].numCommitments()
	}
	return res
}
