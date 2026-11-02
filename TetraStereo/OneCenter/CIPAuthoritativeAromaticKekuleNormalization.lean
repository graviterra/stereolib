import TetraStereo.OneCenter.CIPAuthoritativeRule6P92Enumeration
import TetraStereo.OneCenter.ProductionCIPRule1aMatchingRealization

set_option autoImplicit false

namespace TetraStereo.OneCenter.AuthoritativeCIPAromaticKekuleNormalization

open RawMolecule
open AuthoritativeCIPMancudeTotality
open AuthoritativeCIPMoleculeCursorRanking
open AuthoritativeCIPRule6P92Enumeration

/-!
# Complete finite Kekulé normalization of declared aromatic bonds

Lowercase/aromatic input stores delocalized bonds with raw order one.  The canonical CIP digraph,
however, needs one fixed Kekulé form so that its multiple-bond duplicate occurrences exist, while
Rule 1a subsequently averages those occurrences over every maximum matching.  This module closes
that representation gap by exhaustively considering every single/double assignment to the finite
set of declared aromatic bonds and accepting exactly assignments satisfying explicit structural,
valence, localization, and maximum-written-matching conditions.

The search is complete by construction: `List.sublists` enumerates every subset of the aromatic
bond occurrences.  No heuristic ring choice, size cap, or compiler-evaluated proof is involved.
-/

/-- Declared delocalized bond occurrences in source order. -/
def aromaticBondOccurrences (source : RawMolecule) : List RawBond :=
  source.bonds.filter fun bond => bond.kind == ParsedBondKind.aromatic

/-- Assign one proposed subset of declared aromatic bonds as double and all remaining declared
aromatic bonds as single.  Atoms, endpoints, bond order in the list, and written-neighbour order
are preserved. -/
def withAromaticKekuleSelectionBond (selectedDouble : List RawBond)
    (bond : RawBond) : RawBond :=
  if bond.kind == ParsedBondKind.aromatic then
    { bond with kind :=
        if selectedDouble.contains bond then ParsedBondKind.double
        else ParsedBondKind.single }
  else bond

def withAromaticKekuleSelection (source : RawMolecule)
    (selectedDouble : List RawBond) : RawMolecule :=
  { source with
    bonds := source.bonds.map (withAromaticKekuleSelectionBond selectedDouble) }

/-- Every possible localized single/double assignment of the declared aromatic occurrences. -/
def aromaticKekuleCandidates (source : RawMolecule) : List RawMolecule :=
  (aromaticBondOccurrences source).sublists.map
    (withAromaticKekuleSelection source)

@[simp] theorem withAromaticKekuleSelection_atoms
    (source : RawMolecule) (selectedDouble : List RawBond) :
    (withAromaticKekuleSelection source selectedDouble).atoms = source.atoms := rfl

@[simp] theorem withAromaticKekuleSelection_neighborOrder
    (source : RawMolecule) (selectedDouble : List RawBond) :
    (withAromaticKekuleSelection source selectedDouble).neighborOrder = source.neighborOrder := rfl

@[simp] theorem withAromaticKekuleSelection_introductionPredecessors
    (source : RawMolecule) (selectedDouble : List RawBond) :
    (withAromaticKekuleSelection source selectedDouble).introductionPredecessors =
      source.introductionPredecessors := rfl

@[simp] theorem withAromaticKekuleSelection_atomCount
    (source : RawMolecule) (selectedDouble : List RawBond) :
    (withAromaticKekuleSelection source selectedDouble).atomCount = source.atomCount := rfl

@[simp] theorem withAromaticKekuleSelection_bonds_length
    (source : RawMolecule) (selectedDouble : List RawBond) :
    (withAromaticKekuleSelection source selectedDouble).bonds.length = source.bonds.length := by
  simp [withAromaticKekuleSelection]

@[simp] theorem withAromaticKekuleSelectionBond_source
    (selectedDouble : List RawBond) (bond : RawBond) :
    (withAromaticKekuleSelectionBond selectedDouble bond).source = bond.source := by
  unfold withAromaticKekuleSelectionBond
  split <;> rfl

@[simp] theorem withAromaticKekuleSelectionBond_target
    (selectedDouble : List RawBond) (bond : RawBond) :
    (withAromaticKekuleSelectionBond selectedDouble bond).target = bond.target := by
  unfold withAromaticKekuleSelectionBond
  split <;> rfl

@[simp] theorem withAromaticKekuleSelectionBond_edgeKey
    (selectedDouble : List RawBond) (bond : RawBond) :
    RawBond.edgeKey (withAromaticKekuleSelectionBond selectedDouble bond) =
      RawBond.edgeKey bond := by
  simp [RawBond.edgeKey]

@[simp] theorem withAromaticKekuleSelectionBond_connects
    (selectedDouble : List RawBond) (bond : RawBond) (left right : Nat) :
    (withAromaticKekuleSelectionBond selectedDouble bond).connects left right =
      bond.connects left right := by
  simp [RawBond.connects]

@[simp] theorem withAromaticKekuleSelection_edgeKeys
    (source : RawMolecule) (selectedDouble : List RawBond) :
    ((withAromaticKekuleSelection source selectedDouble).bonds.map RawBond.edgeKey) =
      source.bonds.map RawBond.edgeKey := by
  simp [withAromaticKekuleSelection, List.map_map, Function.comp_def]

/-- Kekulization changes bond multiplicity but never changes the constitutional edge relation. -/
theorem withAromaticKekuleSelection_bondOrder_pos_iff
    (source : RawMolecule) (selectedDouble : List RawBond) (left right : Nat) :
    0 < (withAromaticKekuleSelection source selectedDouble).bondOrder left right ↔
      0 < source.bondOrder left right := by
  by_cases distinct : left = right
  · subst right
    simp [RawMolecule.bondOrder_self]
  · rw [RawMolecule.bondOrder_pos_iff_exists_bond _ distinct,
      RawMolecule.bondOrder_pos_iff_exists_bond _ distinct]
    constructor
    · rintro ⟨bond, bondMember, connects⟩
      rcases List.mem_map.mp bondMember with ⟨sourceBond, sourceBondMember, rfl⟩
      exact ⟨sourceBond, sourceBondMember, by simpa using connects⟩
    · rintro ⟨bond, bondMember, connects⟩
      exact ⟨withAromaticKekuleSelectionBond selectedDouble bond,
        List.mem_map.mpr ⟨bond, bondMember, rfl⟩, by simpa using connects⟩

@[simp] theorem withAromaticKekuleSelection_writtenNeighbors
    (source : RawMolecule) (selectedDouble : List RawBond) (atom : Nat) :
    (withAromaticKekuleSelection source selectedDouble).writtenNeighbors atom =
      source.writtenNeighbors atom := by
  unfold RawMolecule.writtenNeighbors
  cases observed : source.neighborOrder[atom]? with
  | some order => simp [withAromaticKekuleSelection, observed]
  | none =>
      simp only [withAromaticKekuleSelection, observed, List.filterMap_map]
      congr 1
      funext bond
      simp

/-- Changing aromatic bond multiplicities preserves every source-introduction check, including
the directed introducing edge and its first position in the written-neighbour frame. -/
@[simp] theorem withAromaticKekuleSelection_introductionPredecessorsValid
    (source : RawMolecule) (selectedDouble : List RawBond) :
    (withAromaticKekuleSelection source selectedDouble).introductionPredecessorsValid? =
      source.introductionPredecessorsValid? := by
  simp only [RawMolecule.introductionPredecessorsValid?,
    withAromaticKekuleSelection_introductionPredecessors,
    withAromaticKekuleSelection_atomCount, withAromaticKekuleSelection_writtenNeighbors]
  simp [withAromaticKekuleSelection, List.any_map, Function.comp_def]

/-- Default-bond normalization also preserves the provenance admission predicate. -/
@[simp] theorem normalizeUnspecifiedBonds_introductionPredecessorsValid
    (source : RawMolecule) :
    source.normalizeUnspecifiedBonds.introductionPredecessorsValid? =
      source.introductionPredecessorsValid? := by
  simp only [RawMolecule.introductionPredecessorsValid?,
    RawMolecule.normalizeUnspecifiedBonds_writtenNeighbors]
  simp [RawMolecule.normalizeUnspecifiedBonds, RawMolecule.atomCount,
    List.any_map, Function.comp_def]

/-- Exact written-neighbour/parity frames survive every generated Kekulé assignment. -/
theorem withAromaticKekuleSelection_writtenNeighborExact
    (source : RawMolecule) (selectedDouble : List RawBond)
    (exact : source.WrittenNeighborExact) :
    (withAromaticKekuleSelection source selectedDouble).WrittenNeighborExact := by
  apply RawMolecule.WrittenNeighborExact.of_at
  intro center
  change Fin source.atomCount at center
  have clauses := RawMolecule.WrittenNeighborExact.at source exact center
  simpa only [withAromaticKekuleSelection_writtenNeighbors,
    withAromaticKekuleSelection_atomCount,
    withAromaticKekuleSelection_bondOrder_pos_iff] using clauses

/-- Structural edge admission is invariant under every generated Kekulé assignment. -/
theorem withAromaticKekuleSelection_admissible_iff
    (source : RawMolecule) (selectedDouble : List RawBond) :
    (withAromaticKekuleSelection source selectedDouble).Admissible ↔ source.Admissible := by
  constructor
  · rintro ⟨wellFormed, unique⟩
    constructor
    · intro bond bondMember
      have mappedMember :
          withAromaticKekuleSelectionBond selectedDouble bond ∈
            (withAromaticKekuleSelection source selectedDouble).bonds :=
        List.mem_map.mpr ⟨bond, bondMember, rfl⟩
      simpa [RawMolecule.BondEndpointsOK] using
        wellFormed (withAromaticKekuleSelectionBond selectedDouble bond) mappedMember
    · simpa [RawMolecule.BondRecordsUnique] using unique
  · rintro ⟨wellFormed, unique⟩
    constructor
    · intro bond bondMember
      rcases List.mem_map.mp bondMember with ⟨sourceBond, sourceBondMember, rfl⟩
      simpa [RawMolecule.BondEndpointsOK] using wellFormed sourceBond sourceBondMember
    · simpa [RawMolecule.BondRecordsUnique] using unique

/-- Every source aromatic bond must become an edge of the exact localized mancude graph.  This
excludes noncyclic or otherwise chemically inconsistent uses of the aromatic bond marker. -/
def AromaticBondsLocalized (source candidate : RawMolecule) : Prop :=
  ∀ bond, bond ∈ aromaticBondOccurrences source →
    containsUndirectedEdge candidate.localizedMancudeEdges bond.source bond.target = true

def aromaticBondsLocalized? (source candidate : RawMolecule) : Bool :=
  (aromaticBondOccurrences source).all fun bond =>
    containsUndirectedEdge candidate.localizedMancudeEdges bond.source bond.target

@[simp] theorem aromaticBondsLocalized?_eq_true_iff
    (source candidate : RawMolecule) :
    aromaticBondsLocalized? source candidate = true ↔
      AromaticBondsLocalized source candidate := by
  simp [aromaticBondsLocalized?, AromaticBondsLocalized, List.all_eq_true]

/-- Executable reflection of the maximum-written-matching proposition at every finite component.
Membership in the explicit maximum family is equivalent to the independent maximality predicate. -/
def localizedMancudeKekuleAdmissible? (mol : RawMolecule) : Bool :=
  (List.range mol.atomCount).all fun attached =>
    let edges := mol.localizedMancudeComponentEdges attached
    let written := edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2
    decide (written ∈
      maximumMancudeEdgeMatchings (exhaustiveMancudeEdgeMatchings edges))

@[simp] theorem localizedMancudeKekuleAdmissible?_eq_true_iff (mol : RawMolecule) :
    localizedMancudeKekuleAdmissible? mol = true ↔
      LocalizedMancudeKekuleAdmissible mol := by
  unfold localizedMancudeKekuleAdmissible? LocalizedMancudeKekuleAdmissible
  rw [List.all_eq_true]
  constructor
  · intro checked attached
    have atAttached := checked attached.val (List.mem_range.mpr attached.isLt)
    simp only [decide_eq_true_eq] at atAttached
    exact (mem_maximum_exhaustiveMancudeEdgeMatchings_iff
      (mol.localizedMancudeComponentEdges attached.val)
      ((mol.localizedMancudeComponentEdges attached.val).filter fun edge =>
        mol.bondOrder edge.1 edge.2 == 2)).1 atAttached
  · intro admissible attached attachedMem
    have maximum := admissible ⟨attached, List.mem_range.mp attachedMem⟩
    exact decide_eq_true
      ((mem_maximum_exhaustiveMancudeEdgeMatchings_iff
        (mol.localizedMancudeComponentEdges attached)
        ((mol.localizedMancudeComponentEdges attached).filter fun edge =>
          mol.bondOrder edge.1 edge.2 == 2)).2 maximum)

/-- Exact acceptance conditions for one generated Kekulé form. -/
def AromaticKekuleCandidateValid (source candidate : RawMolecule) : Prop :=
  candidate.Admissible ∧
    candidate.ValenceOK ∧
    LocalizedMancudeKekuleAdmissible candidate ∧
    AromaticBondsLocalized source candidate

def aromaticKekuleCandidateValid? (source candidate : RawMolecule) : Bool :=
  candidate.admissible? && candidate.valenceOK? &&
    localizedMancudeKekuleAdmissible? candidate &&
      aromaticBondsLocalized? source candidate

@[simp] theorem aromaticKekuleCandidateValid?_eq_true_iff
    (source candidate : RawMolecule) :
    aromaticKekuleCandidateValid? source candidate = true ↔
      AromaticKekuleCandidateValid source candidate := by
  simp only [aromaticKekuleCandidateValid?, Bool.and_eq_true,
    RawMolecule.admissible?_eq_true_iff, RawMolecule.valenceOK?_eq_true_iff,
    localizedMancudeKekuleAdmissible?_eq_true_iff,
    aromaticBondsLocalized?_eq_true_iff]
  unfold AromaticKekuleCandidateValid
  tauto

/-- Proof-bearing meaning of an accepted normalization result. -/
structure AromaticKekuleNormalizationCertificate
    (source candidate : RawMolecule) : Prop where
  generated : candidate ∈ aromaticKekuleCandidates source
  valid : AromaticKekuleCandidateValid source candidate

/-- Graph-theoretic chemical applicability of aromatic input: at least one complete localized
Kekulé assignment satisfies structural admission, the valence table, and exact Rule-1a maximum
matching semantics. -/
def AromaticKekuleNormalizable (source : RawMolecule) : Prop :=
  ∃ candidate, Nonempty (AromaticKekuleNormalizationCertificate source candidate)

/-- Complete finite normalizer. -/
def normalizeAromaticKekule? (source : RawMolecule) : Option RawMolecule :=
  (aromaticKekuleCandidates source).find?
    (aromaticKekuleCandidateValid? source)

/-- Every returned result carries the full mathematical normalization certificate. -/
theorem normalizeAromaticKekule?_certificate
    (source candidate : RawMolecule)
    (computed : normalizeAromaticKekule? source = some candidate) :
    AromaticKekuleNormalizationCertificate source candidate := by
  have validBool : aromaticKekuleCandidateValid? source candidate = true :=
    List.find?_some computed
  have candidateMember : candidate ∈ aromaticKekuleCandidates source := by
    rcases (List.find?_eq_some_iff_append.mp computed).2 with
      ⟨before, after, candidatesEq, _beforeRejected⟩
    rw [candidatesEq]
    simp
  exact {
    generated := candidateMember
    valid := (aromaticKekuleCandidateValid?_eq_true_iff source candidate).mp validBool }

theorem normalizeAromaticKekule?_sound
    (source candidate : RawMolecule)
    (computed : normalizeAromaticKekule? source = some candidate) :
    Nonempty (AromaticKekuleNormalizationCertificate source candidate) :=
  ⟨normalizeAromaticKekule?_certificate source candidate computed⟩

/-- Executable proof-bearing output of the exhaustive Kekulé search. -/
structure CertifiedAromaticKekuleOutput (source : RawMolecule) where
  candidate : RawMolecule
  computed : normalizeAromaticKekule? source = some candidate
  certificate : AromaticKekuleNormalizationCertificate source candidate

def normalizeAromaticKekuleCertified? (source : RawMolecule) :
    Option (CertifiedAromaticKekuleOutput source) :=
  match computed : normalizeAromaticKekule? source with
  | none => none
  | some candidate => some
      { candidate := candidate
        computed := computed
        certificate := normalizeAromaticKekule?_certificate source candidate computed }

@[simp] theorem normalizeAromaticKekuleCertified?_isSome
    (source : RawMolecule) :
    (normalizeAromaticKekuleCertified? source).isSome =
      (normalizeAromaticKekule? source).isSome := by
  unfold normalizeAromaticKekuleCertified?
  split <;> simp_all

private theorem generatedCandidate_eq_selection
    {source candidate : RawMolecule}
    (generated : candidate ∈ aromaticKekuleCandidates source) :
    ∃ selectedDouble,
      candidate = withAromaticKekuleSelection source selectedDouble := by
  rcases List.mem_map.mp generated with ⟨selectedDouble, _selectedMember, candidateEq⟩
  exact ⟨selectedDouble, candidateEq.symm⟩

/-- A returned Kekulé form contains exactly the source atoms.  This includes element, isotope,
charge, aromatic-input, explicit-hydrogen, and tetrahedral-parity fields. -/
theorem normalizeAromaticKekule?_atoms
    {source candidate : RawMolecule}
    (computed : normalizeAromaticKekule? source = some candidate) :
    candidate.atoms = source.atoms := by
  rcases normalizeAromaticKekule?_sound source candidate computed with ⟨certificate⟩
  rcases generatedCandidate_eq_selection certificate.generated with ⟨selectedDouble, rfl⟩
  rfl

/-- A returned Kekulé form retains every per-atom OpenSMILES written-neighbour order exactly. -/
theorem normalizeAromaticKekule?_neighborOrder
    {source candidate : RawMolecule}
    (computed : normalizeAromaticKekule? source = some candidate) :
    candidate.neighborOrder = source.neighborOrder := by
  rcases normalizeAromaticKekule?_sound source candidate computed with ⟨certificate⟩
  rcases generatedCandidate_eq_selection certificate.generated with ⟨selectedDouble, rfl⟩
  rfl

/-- The available introduction prefix is preserved exactly, including legacy empty metadata. -/
theorem normalizeAromaticKekule?_introductionPredecessors
    {source candidate : RawMolecule}
    (computed : normalizeAromaticKekule? source = some candidate) :
    candidate.introductionPredecessors = source.introductionPredecessors := by
  rcases normalizeAromaticKekule?_sound source candidate computed with ⟨certificate⟩
  rcases generatedCandidate_eq_selection certificate.generated with ⟨selectedDouble, rfl⟩
  rfl

theorem normalizeAromaticKekule?_introductionPredecessorsValid
    {source candidate : RawMolecule}
    (computed : normalizeAromaticKekule? source = some candidate) :
    candidate.introductionPredecessorsValid? = source.introductionPredecessorsValid? := by
  rcases normalizeAromaticKekule?_sound source candidate computed with ⟨certificate⟩
  rcases generatedCandidate_eq_selection certificate.generated with ⟨selectedDouble, rfl⟩
  exact withAromaticKekuleSelection_introductionPredecessorsValid source selectedDouble

/-- A returned Kekulé form has exactly the source unordered edge identities, in source order. -/
theorem normalizeAromaticKekule?_edgeKeys
    {source candidate : RawMolecule}
    (computed : normalizeAromaticKekule? source = some candidate) :
    candidate.bonds.map RawBond.edgeKey = source.bonds.map RawBond.edgeKey := by
  rcases normalizeAromaticKekule?_sound source candidate computed with ⟨certificate⟩
  rcases generatedCandidate_eq_selection certificate.generated with ⟨selectedDouble, rfl⟩
  exact withAromaticKekuleSelection_edgeKeys source selectedDouble

/-- A returned Kekulé form changes multiplicity but neither creates nor deletes adjacency. -/
theorem normalizeAromaticKekule?_bondOrder_pos_iff
    {source candidate : RawMolecule}
    (computed : normalizeAromaticKekule? source = some candidate)
    (left right : Nat) :
    0 < candidate.bondOrder left right ↔ 0 < source.bondOrder left right := by
  rcases normalizeAromaticKekule?_sound source candidate computed with ⟨certificate⟩
  rcases generatedCandidate_eq_selection certificate.generated with ⟨selectedDouble, rfl⟩
  exact withAromaticKekuleSelection_bondOrder_pos_iff source selectedDouble left right

/-- Every written-neighbour list, including the bond-list fallback, is exactly preserved. -/
theorem normalizeAromaticKekule?_writtenNeighbors
    {source candidate : RawMolecule}
    (computed : normalizeAromaticKekule? source = some candidate)
    (atom : Nat) :
    candidate.writtenNeighbors atom = source.writtenNeighbors atom := by
  rcases normalizeAromaticKekule?_sound source candidate computed with ⟨certificate⟩
  rcases generatedCandidate_eq_selection certificate.generated with ⟨selectedDouble, rfl⟩
  exact withAromaticKekuleSelection_writtenNeighbors source selectedDouble atom

/-- Therefore a returned form preserves the exact parity-frame admission established at intake. -/
theorem normalizeAromaticKekule?_writtenNeighborExact
    {source candidate : RawMolecule}
    (computed : normalizeAromaticKekule? source = some candidate)
    (exact : source.WrittenNeighborExact) :
    candidate.WrittenNeighborExact := by
  rcases normalizeAromaticKekule?_sound source candidate computed with ⟨certificate⟩
  rcases generatedCandidate_eq_selection certificate.generated with ⟨selectedDouble, rfl⟩
  exact withAromaticKekuleSelection_writtenNeighborExact source selectedDouble exact

/-- Rule-2 atom data is invariant because Kekulization changes only aromatic bond kinds. -/
theorem normalizeAromaticKekule?_rule2MassesKnown_iff
    {source candidate : RawMolecule}
    (computed : normalizeAromaticKekule? source = some candidate) :
    candidate.Rule2MassesKnown ↔ source.Rule2MassesKnown := by
  rw [RawMolecule.Rule2MassesKnown, RawMolecule.Rule2MassesKnown,
    normalizeAromaticKekule?_atoms computed]

/-- The returned form is fully stereochemically admissible whenever the source parity frame was
exact.  Structural admission comes from the independently checked candidate certificate. -/
theorem normalizeAromaticKekule?_stereochemicalAdmissible
    {source candidate : RawMolecule}
    (computed : normalizeAromaticKekule? source = some candidate)
    (exact : source.WrittenNeighborExact) :
    candidate.StereochemicalAdmissible := by
  rcases normalizeAromaticKekule?_sound source candidate computed with ⟨certificate⟩
  exact ⟨certificate.valid.1,
    normalizeAromaticKekule?_writtenNeighborExact computed exact⟩

/-- Search success is equivalent to the independent existence of a valid generated assignment.
Thus normalization has no hidden search-order or finite-fuel incompleteness. -/
theorem normalizeAromaticKekule?_isSome_iff_normalizable (source : RawMolecule) :
    (normalizeAromaticKekule? source).isSome = true ↔
      AromaticKekuleNormalizable source := by
  unfold normalizeAromaticKekule? AromaticKekuleNormalizable
  rw [List.find?_isSome]
  constructor
  · rintro ⟨candidate, candidateMember, validBool⟩
    exact ⟨candidate, ⟨{
      generated := candidateMember
      valid := (aromaticKekuleCandidateValid?_eq_true_iff source candidate).mp validBool }⟩⟩
  · rintro ⟨candidate, ⟨certificate⟩⟩
    exact ⟨candidate, certificate.generated,
      (aromaticKekuleCandidateValid?_eq_true_iff source candidate).mpr certificate.valid⟩

/-- A graph-theoretically normalizable finite input has a returned certified Kekulé form. -/
theorem normalizeAromaticKekule?_exists (source : RawMolecule)
    (normalizable : AromaticKekuleNormalizable source) :
    ∃ candidate,
      normalizeAromaticKekule? source = some candidate ∧
        Nonempty (AromaticKekuleNormalizationCertificate source candidate) := by
  have present : (normalizeAromaticKekule? source).isSome = true :=
    (normalizeAromaticKekule?_isSome_iff_normalizable source).2 normalizable
  rcases Option.isSome_iff_exists.mp present with ⟨candidate, computed⟩
  exact ⟨candidate, computed, normalizeAromaticKekule?_sound source candidate computed⟩

/-- Build the ordinary chemistry-normalization payload directly over an already localized
Kekulé form.  In particular, this does not erase the selected double bonds by returning to the
delocalized parser representation. -/
def aromaticKekuleChemistryNormalizationResult
    (candidate : RawMolecule) (cycles : List AromaticCycle := []) :
    ChemistryNormalizationResult where
  parsed := candidate
  graph := candidate.toMoleculeGraph
  valenceOK := candidate.ValenceOK
  aromaticCycles := cycles
  resonance := resonanceNormalize candidate
  stereobonds := stereobondSemantics candidate
  tautomer := tautomerNormalize candidate

/-- Package any returned form as the standard structural chemistry certificate. The normalizer itself
supplies structural admission and valence; the source intake supplies exact parity ordering and
Rule-2 mass data, both of which have been proved invariant above. As with direct construction of
`CertifiedChemistryNormalizationResult`, this proof-only constructor does not imply successful
checked intake; `normalizeAromaticChemistryCertified?` separately validates provenance. -/
def certifiedAromaticKekuleChemistryNormalizationResult
    (source candidate : RawMolecule) (cycles : List AromaticCycle)
    (computed : normalizeAromaticKekule? source = some candidate)
    (certificate : AromaticKekuleNormalizationCertificate source candidate)
    (sourceWrittenNeighborExact : source.WrittenNeighborExact)
    (sourceRule2MassesKnown : source.Rule2MassesKnown) :
    CertifiedChemistryNormalizationResult where
  result := aromaticKekuleChemistryNormalizationResult candidate cycles
  admissible := certificate.valid.1
  writtenNeighborExact :=
    normalizeAromaticKekule?_writtenNeighborExact computed sourceWrittenNeighborExact
  valenceOK := certificate.valid.2.1
  rule2MassesKnown :=
    (normalizeAromaticKekule?_rule2MassesKnown_iff computed).2 sourceRule2MassesKnown

@[simp] theorem certifiedAromaticKekuleChemistryNormalizationResult_parsed
    (source candidate : RawMolecule) (cycles : List AromaticCycle)
    (computed : normalizeAromaticKekule? source = some candidate)
    (certificate : AromaticKekuleNormalizationCertificate source candidate)
    (sourceWrittenNeighborExact : source.WrittenNeighborExact)
    (sourceRule2MassesKnown : source.Rule2MassesKnown) :
    (certifiedAromaticKekuleChemistryNormalizationResult source candidate cycles computed
      certificate sourceWrittenNeighborExact sourceRule2MassesKnown).result.parsed = candidate := rfl

/-- Executable certified chemistry intake for an explicitly aromatic source. The source must pass
introduction-provenance, parity-frame and Rule-2 admission, followed by the complete finite Kekulé
search. Empty legacy provenance remains admitted. -/
def normalizeAromaticChemistryCertified? (source : RawMolecule)
    (cycles : List AromaticCycle := []) : Option CertifiedChemistryNormalizationResult :=
  if source.introductionPredecessorsValid? then
    if exact : source.writtenNeighborExact? = true then
      if masses : source.rule2MassesKnown? = true then
        match normalizeAromaticKekuleCertified? source with
        | none => none
        | some normalized =>
            some (certifiedAromaticKekuleChemistryNormalizationResult
              source normalized.candidate cycles normalized.computed normalized.certificate
              ((source.writtenNeighborExact?_eq_true_iff).mp exact)
              ((source.rule2MassesKnown?_eq_true_iff).mp masses))
      else none
    else none
  else none

/-- Exact rejection theorem for the executable certified intake. -/
theorem normalizeAromaticChemistryCertified?_isSome_iff
    (source : RawMolecule) (cycles : List AromaticCycle := []) :
    (normalizeAromaticChemistryCertified? source cycles).isSome = true ↔
      source.introductionPredecessorsValid? = true ∧ source.WrittenNeighborExact ∧
        source.Rule2MassesKnown ∧ AromaticKekuleNormalizable source := by
  by_cases introductionValid : source.introductionPredecessorsValid? = true
  swap
  · simp [normalizeAromaticChemistryCertified?, introductionValid]
  simp only [introductionValid, true_and]
  unfold normalizeAromaticChemistryCertified?
  simp only [introductionValid, ↓reduceIte]
  split <;> rename_i exact
  · split <;> rename_i masses
    · have outputIsSome :
          (match normalizeAromaticKekuleCertified? source with
            | none => none
            | some normalized =>
                some (certifiedAromaticKekuleChemistryNormalizationResult
                  source normalized.candidate cycles normalized.computed normalized.certificate
                  ((source.writtenNeighborExact?_eq_true_iff).mp exact)
                  ((source.rule2MassesKnown?_eq_true_iff).mp masses))).isSome =
            (normalizeAromaticKekuleCertified? source).isSome := by
          cases observed : normalizeAromaticKekuleCertified? source <;> rfl
      rw [outputIsSome, normalizeAromaticKekuleCertified?_isSome,
        normalizeAromaticKekule?_isSome_iff_normalizable]
      exact ⟨fun normalizable =>
          ⟨(source.writtenNeighborExact?_eq_true_iff).mp exact,
            (source.rule2MassesKnown?_eq_true_iff).mp masses, normalizable⟩,
        fun applicable => applicable.2.2⟩
    · have notKnown : ¬ source.Rule2MassesKnown := by
        intro known
        exact masses ((source.rule2MassesKnown?_eq_true_iff).mpr known)
      simp [notKnown]
  · have notExact : ¬ source.WrittenNeighborExact := by
      intro writtenExact
      exact exact ((source.writtenNeighborExact?_eq_true_iff).mpr writtenExact)
    simp [notExact]

/-- A successful checked aromatic intake validates its actual returned molecular prefix. This
guarantee is attached to the executable observation, not merely to the certificate's type. -/
theorem normalizeAromaticChemistryCertified?_introduction_valid
    (source : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (observed : normalizeAromaticChemistryCertified? source cycles = some certified) :
    certified.result.parsed.introductionPredecessorsValid? = true := by
  unfold normalizeAromaticChemistryCertified? at observed
  split at observed
  · rename_i introductionValid
    split at observed
    · split at observed
      · cases normalized : normalizeAromaticKekuleCertified? source with
        | none => simp [normalized] at observed
        | some output =>
            simp only [normalized, Option.some.injEq] at observed
            subst certified
            exact (normalizeAromaticKekule?_introductionPredecessorsValid
              output.computed).trans introductionValid
      · contradiction
    · contradiction
  · contradiction

/-- Production raw-molecule entry point: first apply the already proved default-bond
normalization, then the complete aromatic/Kekulé normalization and certified chemistry admission. -/
def normalizeRawMoleculeAuthoritativeAromaticCertified? (source : RawMolecule)
    (cycles : List AromaticCycle := []) : Option CertifiedChemistryNormalizationResult :=
  normalizeAromaticChemistryCertified? source.normalizeUnspecifiedBonds cycles

/-- Exact success boundary of the production raw-molecule entry point. -/
theorem normalizeRawMoleculeAuthoritativeAromaticCertified?_isSome_iff
    (source : RawMolecule) (cycles : List AromaticCycle := []) :
    (normalizeRawMoleculeAuthoritativeAromaticCertified? source cycles).isSome = true ↔
      source.introductionPredecessorsValid? = true ∧
        source.normalizeUnspecifiedBonds.WrittenNeighborExact ∧
        source.normalizeUnspecifiedBonds.Rule2MassesKnown ∧
          AromaticKekuleNormalizable source.normalizeUnspecifiedBonds := by
  simpa only [normalizeUnspecifiedBonds_introductionPredecessorsValid] using
    normalizeAromaticChemistryCertified?_isSome_iff source.normalizeUnspecifiedBonds cycles

/-- Every source satisfying the explicit applicability premises reaches the standard certified
chemistry carrier. -/
theorem normalizeRawMoleculeAuthoritativeAromaticCertified?_complete
    (source : RawMolecule) (cycles : List AromaticCycle := [])
    (sourceIntroductionValid : source.introductionPredecessorsValid? = true)
    (sourceWrittenNeighborExact : source.WrittenNeighborExact)
    (sourceRule2MassesKnown : source.Rule2MassesKnown)
    (normalizable : AromaticKekuleNormalizable source.normalizeUnspecifiedBonds) :
    (normalizeRawMoleculeAuthoritativeAromaticCertified? source cycles).isSome = true := by
  apply (normalizeRawMoleculeAuthoritativeAromaticCertified?_isSome_iff source cycles).2
  exact ⟨sourceIntroductionValid,
    source.normalizeUnspecifiedBonds_writtenNeighborExact sourceWrittenNeighborExact,
    (source.normalizeUnspecifiedBonds_rule2MassesKnown).2 sourceRule2MassesKnown,
    normalizable⟩

theorem normalizeRawMoleculeAuthoritativeAromaticCertified?_introduction_valid
    (source : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (observed : normalizeRawMoleculeAuthoritativeAromaticCertified? source cycles =
      some certified) :
    certified.result.parsed.introductionPredecessorsValid? = true :=
  normalizeAromaticChemistryCertified?_introduction_valid
    source.normalizeUnspecifiedBonds cycles certified observed

/-- Proof-only existence of the standard structural chemistry certificate for a normalizable
source with exact parity and Rule-2 atom data. This does not assert success of checked intake:
that stronger operational conclusion additionally requires valid introduction provenance, as
stated by `normalizeRawMoleculeAuthoritativeAromaticCertified?_complete`. -/
theorem AromaticKekuleNormalizable.exists_certifiedChemistryNormalizationResult
    {source : RawMolecule}
    (normalizable : AromaticKekuleNormalizable source)
    (sourceWrittenNeighborExact : source.WrittenNeighborExact)
    (sourceRule2MassesKnown : source.Rule2MassesKnown)
    (cycles : List AromaticCycle := []) :
    ∃ candidate, ∃ certified : CertifiedChemistryNormalizationResult,
      normalizeAromaticKekule? source = some candidate ∧
        certified.result.parsed = candidate ∧
        Nonempty (AromaticKekuleNormalizationCertificate source candidate) := by
  rcases normalizeAromaticKekule?_exists source normalizable with
    ⟨candidate, computed, ⟨certificate⟩⟩
  exact ⟨candidate,
    certifiedAromaticKekuleChemistryNormalizationResult source candidate cycles computed
      certificate sourceWrittenNeighborExact sourceRule2MassesKnown,
    computed, rfl, ⟨certificate⟩⟩

/-- Every normalized result supplies precisely the chemical premises consumed by the uncapped
Rules-1a--6 occurrence comparator. -/
theorem normalizeAromaticKekule?_chemical_applicability
    (source candidate : RawMolecule)
    (computed : normalizeAromaticKekule? source = some candidate) :
    candidate.WellFormed ∧ candidate.BondRecordsUnique ∧ candidate.ValenceOK ∧
      LocalizedMancudeKekuleAdmissible candidate ∧
      AromaticBondsLocalized source candidate := by
  rcases normalizeAromaticKekule?_sound source candidate computed with ⟨certificate⟩
  exact ⟨certificate.valid.1.1, certificate.valid.1.2, certificate.valid.2.1,
    certificate.valid.2.2.1, certificate.valid.2.2.2⟩

/-- End-to-end operational consequence of aromatic normalization: every P-92 reference position
of a generated occurrence has a completed uncapped authoritative ranking. -/
theorem normalizedAromatic_positionRankingBackend_total
    {source candidate : RawMolecule} {state : OccurrenceAuxState} {center : Nat}
    (computed : normalizeAromaticKekule? source = some candidate)
    (centerBound : center < candidate.atomCount)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated : CanonicalCenterTreeNode candidate center occurrence)
    (ligands : List Nat) :
    ∀ referencePosition,
      ∃ ranking,
        authoritativeOccurrenceRule6PositionRankingBackend candidate state
            (2 * candidate.atomCount + 1) (occurrenceLigandCursors candidate occurrence) ligands
            referencePosition = some ranking := by
  rcases normalizeAromaticKekule?_chemical_applicability source candidate computed with
    ⟨wellFormed, unique, valence, kekule, _localized⟩
  exact authoritativeOccurrenceRule6PositionRankingBackend_total_of_chemical_applicability
    centerBound wellFormed unique valence kekule occurrenceGenerated ligands

end TetraStereo.OneCenter.AuthoritativeCIPAromaticKekuleNormalization
