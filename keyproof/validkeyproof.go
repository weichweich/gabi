package keyproof

import "github.com/privacybydesign/gabi/pkg/common"
import "github.com/privacybydesign/gabi/big"

type ValidKeyProofStructure struct {
	n          *big.Int
	pRep       RepresentationProofStructure
	qRep       RepresentationProofStructure
	pprimeRep  RepresentationProofStructure
	qprimeRep  RepresentationProofStructure
	pPprimeRel RepresentationProofStructure
	qQprimeRel RepresentationProofStructure
	pQNRel     RepresentationProofStructure

	pprimeIsPrime primeProofStructure
	qprimeIsPrime primeProofStructure

	basesValid isSquareProofStructure
}

type ValidKeyProof struct {
	PProof      PedersonProof
	QProof      PedersonProof
	PprimeProof PedersonProof
	QprimeProof PedersonProof
	PQNRel      *big.Int
	Challenge   *big.Int
	GroupPrime  *big.Int

	PprimeIsPrimeProof PrimeProof
	QprimeIsPrimeProof PrimeProof

	QSPPproof QuasiSafePrimeProductProof

	BasesValidProof IsSquareProof
}

type safePrimeSecret struct {
	pQNRel           *big.Int
	pQNRelRandomizer *big.Int
}

func (s *safePrimeSecret) GetSecret(name string) *big.Int {
	if name == "pqnrel" {
		return s.pQNRel
	}
	return nil
}

func (s *safePrimeSecret) GetRandomizer(name string) *big.Int {
	if name == "pqnrel" {
		return s.pQNRelRandomizer
	}
	return nil
}

func (p *ValidKeyProof) GetResult(name string) *big.Int {
	if name == "pqnrel" {
		return p.PQNRel
	}
	return nil
}

func NewValidKeyProofStructure(N *big.Int, Z *big.Int, S *big.Int, Bases []*big.Int) ValidKeyProofStructure {
	var structure ValidKeyProofStructure

	structure.n = new(big.Int).Set(N)
	structure.pRep = newPedersonRepresentationProofStructure("p")
	structure.qRep = newPedersonRepresentationProofStructure("q")
	structure.pprimeRep = newPedersonRepresentationProofStructure("pprime")
	structure.qprimeRep = newPedersonRepresentationProofStructure("qprime")

	structure.pPprimeRel = RepresentationProofStructure{
		[]LhsContribution{
			{"p", big.NewInt(1)},
			{"pprime", big.NewInt(-2)},
			{"g", big.NewInt(-1)},
		},
		[]RhsContribution{
			{"h", "p_hider", 1},
			{"h", "pprime_hider", -2},
		},
	}

	structure.qQprimeRel = RepresentationProofStructure{
		[]LhsContribution{
			{"q", big.NewInt(1)},
			{"qprime", big.NewInt(-2)},
			{"g", big.NewInt(-1)},
		},
		[]RhsContribution{
			{"h", "q_hider", 1},
			{"h", "qprime_hider", -2},
		},
	}

	structure.pQNRel = RepresentationProofStructure{
		[]LhsContribution{
			{"g", new(big.Int).Set(N)},
		},
		[]RhsContribution{
			{"p", "q", 1},
			{"h", "pqnrel", -1},
		},
	}

	structure.pprimeIsPrime = newPrimeProofStructure("pprime", uint((N.BitLen()+1)/2))
	structure.qprimeIsPrime = newPrimeProofStructure("qprime", uint((N.BitLen()+1)/2))

	BaseList := append([]*big.Int{Z, S}, Bases...)
	structure.basesValid = newIsSquareProofStructure(N, BaseList)

	return structure
}

func (s *ValidKeyProofStructure) numRangeProofs() int {
	return s.pprimeIsPrime.numRangeProofs() + s.qprimeIsPrime.numRangeProofs() + s.basesValid.numRangeProofs()
}

func (s *ValidKeyProofStructure) BuildProof(Pprime *big.Int, Qprime *big.Int) ValidKeyProof {
	// Generate proof group
	Follower.StepStart("Generating group prime", 0)
	primeSize := s.n.BitLen() + 2*rangeProofEpsilon + 10

	GroupPrime := findSafePrime(primeSize)
	g, gok := buildGroup(GroupPrime)
	if !gok {
		panic("Safe prime generated by gabi was not a safe prime!?")
	}
	Follower.StepDone()

	Follower.StepStart("Generating commitments", s.numRangeProofs())

	// Build up some derived values
	P := new(big.Int).Add(new(big.Int).Lsh(Pprime, 1), big.NewInt(1))
	Q := new(big.Int).Add(new(big.Int).Lsh(Qprime, 1), big.NewInt(1))

	// Build up the secrets
	PprimeSecret := newPedersonSecret(g, "pprime", Pprime)
	QprimeSecret := newPedersonSecret(g, "qprime", Qprime)
	PSecret := newPedersonSecret(g, "p", P)
	QSecret := newPedersonSecret(g, "q", Q)

	PQNRelSecret := safePrimeSecret{
		new(big.Int).Mod(new(big.Int).Mul(PSecret.hider, QSecret.secret), g.order),
		common.FastRandomBigInt(g.order),
	}

	// Build up bases and secrets structures
	bases := NewBaseMerge(&g, &PSecret, &QSecret, &PprimeSecret, &QprimeSecret)
	secrets := NewSecretMerge(&PSecret, &QSecret, &PprimeSecret, &QprimeSecret, &PQNRelSecret)

	// Build up commitment list
	var list []*big.Int
	var PprimeIsPrimeCommit primeProofCommit
	var QprimeIsPrimeCommit primeProofCommit
	var QSPPcommit quasiSafePrimeProductCommit
	var BasesValidCommit isSquareProofCommit
	list = append(list, GroupPrime)
	list = append(list, s.n)
	list = PprimeSecret.generateCommitments(list)
	list = QprimeSecret.generateCommitments(list)
	list = PSecret.generateCommitments(list)
	list = QSecret.generateCommitments(list)
	list = s.pRep.generateCommitmentsFromSecrets(g, list, &bases, &secrets)
	list = s.qRep.generateCommitmentsFromSecrets(g, list, &bases, &secrets)
	list = s.pprimeRep.generateCommitmentsFromSecrets(g, list, &bases, &secrets)
	list = s.qprimeRep.generateCommitmentsFromSecrets(g, list, &bases, &secrets)
	list = s.pPprimeRel.generateCommitmentsFromSecrets(g, list, &bases, &secrets)
	list = s.qQprimeRel.generateCommitmentsFromSecrets(g, list, &bases, &secrets)
	list = s.pQNRel.generateCommitmentsFromSecrets(g, list, &bases, &secrets)
	list, PprimeIsPrimeCommit = s.pprimeIsPrime.generateCommitmentsFromSecrets(g, list, &bases, &secrets)
	list, QprimeIsPrimeCommit = s.qprimeIsPrime.generateCommitmentsFromSecrets(g, list, &bases, &secrets)
	list, QSPPcommit = quasiSafePrimeProductBuildCommitments(list, Pprime, Qprime)
	list, BasesValidCommit = s.basesValid.generateCommitmentsFromSecrets(g, list, P, Q)
	Follower.StepDone()

	Follower.StepStart("Generating proof", 0)
	// Calculate challenge
	challenge := common.HashCommit(list, false)

	// Calculate proofs
	var proof ValidKeyProof
	proof.GroupPrime = GroupPrime
	proof.PQNRel = new(big.Int).Mod(
		new(big.Int).Sub(
			PQNRelSecret.pQNRelRandomizer,
			new(big.Int).Mul(
				challenge,
				PQNRelSecret.pQNRel)),
		g.order)
	proof.PProof = PSecret.buildProof(g, challenge)
	proof.QProof = QSecret.buildProof(g, challenge)
	proof.PprimeProof = PprimeSecret.buildProof(g, challenge)
	proof.QprimeProof = QprimeSecret.buildProof(g, challenge)
	proof.Challenge = challenge
	proof.PprimeIsPrimeProof = s.pprimeIsPrime.buildProof(g, challenge, PprimeIsPrimeCommit, &secrets)
	proof.QprimeIsPrimeProof = s.qprimeIsPrime.buildProof(g, challenge, QprimeIsPrimeCommit, &secrets)
	proof.QSPPproof = quasiSafePrimeProductBuildProof(Pprime, Qprime, challenge, QSPPcommit)
	proof.BasesValidProof = s.basesValid.buildProof(g, challenge, BasesValidCommit)
	Follower.StepDone()

	return proof
}

func (s *ValidKeyProofStructure) VerifyProof(proof ValidKeyProof) bool {
	// Check proof structure
	Follower.StepStart("Verifying structure", 0)
	defer Follower.StepDone()
	if proof.GroupPrime == nil || proof.GroupPrime.BitLen() < s.n.BitLen()+2*rangeProofEpsilon+10 {
		return false
	}
	if !proof.GroupPrime.ProbablyPrime(80) || !new(big.Int).Rsh(proof.GroupPrime, 1).ProbablyPrime(80) {
		return false
	}
	if proof.PQNRel == nil || proof.Challenge == nil {
		return false
	}
	if !proof.PProof.verifyStructure() || !proof.QProof.verifyStructure() {
		return false
	}
	if !proof.PprimeProof.verifyStructure() || !proof.QprimeProof.verifyStructure() {
		return false
	}
	if !s.pprimeIsPrime.verifyProofStructure(proof.Challenge, proof.PprimeIsPrimeProof) ||
		!s.qprimeIsPrime.verifyProofStructure(proof.Challenge, proof.QprimeIsPrimeProof) {
		return false
	}
	if !quasiSafePrimeProductVerifyStructure(proof.QSPPproof) {
		return false
	}
	if !s.basesValid.verifyProofStructure(proof.BasesValidProof) {
		return false
	}
	Follower.StepDone()

	Follower.StepStart("Rebuilding commitments", s.numRangeProofs())

	// Rebuild group
	g, gok := buildGroup(proof.GroupPrime)
	if !gok {
		return false
	}

	// Setup names in the pederson proofs
	proof.PProof.setName("p")
	proof.QProof.setName("q")
	proof.PprimeProof.setName("pprime")
	proof.QprimeProof.setName("qprime")

	// Build up bases and secrets
	bases := NewBaseMerge(&g, &proof.PProof, &proof.QProof, &proof.PprimeProof, &proof.QprimeProof)
	proofs := NewProofMerge(&proof.PProof, &proof.QProof, &proof.PprimeProof, &proof.QprimeProof, &proof)

	// Build up commitment list
	var list []*big.Int
	list = append(list, proof.GroupPrime)
	list = append(list, s.n)
	list = proof.PprimeProof.generateCommitments(list)
	list = proof.QprimeProof.generateCommitments(list)
	list = proof.PProof.generateCommitments(list)
	list = proof.QProof.generateCommitments(list)
	list = s.pRep.generateCommitmentsFromProof(g, list, proof.Challenge, &bases, &proofs)
	list = s.qRep.generateCommitmentsFromProof(g, list, proof.Challenge, &bases, &proofs)
	list = s.pprimeRep.generateCommitmentsFromProof(g, list, proof.Challenge, &bases, &proofs)
	list = s.qprimeRep.generateCommitmentsFromProof(g, list, proof.Challenge, &bases, &proofs)
	list = s.pPprimeRel.generateCommitmentsFromProof(g, list, proof.Challenge, &bases, &proofs)
	list = s.qQprimeRel.generateCommitmentsFromProof(g, list, proof.Challenge, &bases, &proofs)
	list = s.pQNRel.generateCommitmentsFromProof(g, list, proof.Challenge, &bases, &proofs)
	list = s.pprimeIsPrime.generateCommitmentsFromProof(g, list, proof.Challenge, &bases, &proofs, proof.PprimeIsPrimeProof)
	list = s.qprimeIsPrime.generateCommitmentsFromProof(g, list, proof.Challenge, &bases, &proofs, proof.QprimeIsPrimeProof)
	list = quasiSafePrimeProductExtractCommitments(list, proof.QSPPproof)
	list = s.basesValid.generateCommitmentsFromProof(g, list, proof.Challenge, proof.BasesValidProof)

	Follower.StepDone()

	Follower.StepStart("Verifying proof", 0)

	// Check challenge
	if proof.Challenge.Cmp(common.HashCommit(list, false)) != 0 {
		return false
	}

	// And the QSPP proof
	return quasiSafePrimeProductVerifyProof(s.n, proof.Challenge, proof.QSPPproof)
}
