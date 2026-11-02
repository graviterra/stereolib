import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo
namespace UniversalProof
namespace CyclicFirstConstitutionalDifferenceProofs
namespace CyclicFirstConstitutionalDifference

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
















































































/-! ## 1. General engine: the equal-Z boundary and the deeper-sphere first difference -/

/-- Exact Rule-1a label at a `realAtom` node (recovered locally; no import beyond the frozen
production module). -/
theorem canonicalRule1aLabel?_realAtom (mol : RawMolecule) (node : CanonicalBranchNode)
    (h : node.provenance = CanonicalNodeProvenance.realAtom) :
    mol.canonicalRule1aLabel? node =
      some { numerator := mol.atomZAt node.atom, denominator := 1 } := by
  cases hp : node.provenance with
  | realAtom => simp [RawMolecule.canonicalRule1aLabel?, hp]
  | ringDuplicate distance => simp [RawMolecule.canonicalRule1aLabel?, hp]
  | multipleBondDuplicate distance => simp_all
  | phantom distance => simp_all

/-- Exact Rule-1a label at a production phantom node: the `0/1` padding label. -/
theorem canonicalRule1aLabel?_phantom (mol : RawMolecule) (parent distance : ℕ) :
    mol.canonicalRule1aLabel? (mol.canonicalPhantom parent distance) =
      some { numerator := 0, denominator := 1 } := by
  simp [RawMolecule.canonicalPhantom, RawMolecule.canonicalRule1aLabel?]

/-- The exact rational label comparator on two integral labels is the plain atomic-number
comparison. -/
theorem compareCIPAtomicLabel_unitValue (a b : ℕ) :
    RawMolecule.compareCIPAtomicLabel { numerator := a, denominator := 1 }
      { numerator := b, denominator := 1 } = compare a b := by
  simp [RawMolecule.compareCIPAtomicLabel, RawMolecule.CIPAtomicLabel.effectiveDenominator]

/-- **The equal-Z boundary of the checked Rule-1a engine.**  At two `realAtom` roots carrying the
*same* atomic number the production node comparator returns `Ordering.eq`, so the checked
atomic-difference bridge cannot reach a strict result.  This restates exactly why a genuinely new
mechanism is needed for equal-Z cyclic roots. -/
theorem rule1aRealTied_eq (mol : RawMolecule) (left right : CanonicalBranchNode)
    (hL : left.provenance = CanonicalNodeProvenance.realAtom)
    (hR : right.provenance = CanonicalNodeProvenance.realAtom)
    (tied : mol.atomZAt left.atom = mol.atomZAt right.atom) :
    mol.compareCanonicalNodeRule? RawMolecule.CanonicalRuleStage.rule1a left right =
      some Ordering.eq := by
  have hLeft := canonicalRule1aLabel?_realAtom mol left hL
  have hRight := canonicalRule1aLabel?_realAtom mol right hR
  have hEq : RawMolecule.compareCIPAtomicLabel
      { numerator := mol.atomZAt left.atom, denominator := 1 }
      { numerator := mol.atomZAt right.atom, denominator := 1 } = Ordering.eq := by
    rw [compareCIPAtomicLabel_unitValue, tied]
    exact Nat.compare_eq_eq.mpr rfl
  simp [RawMolecule.compareCanonicalNodeRule?, hLeft, hRight, hEq]

/-- **Strict phantom-vs-real first-sphere difference.**  A production phantom padding slot (label
`0/1`) ranks strictly below a real node carrying a positive atomic number, with no atomic-number
*difference* premise between two real atoms.  This is the atom-level core of the equal-Z mechanism. -/
theorem compareCIPAtomicLabel_phantom_lt_real (z : ℕ) (hpos : 0 < z) :
    RawMolecule.compareCIPAtomicLabel { numerator := 0, denominator := 1 }
      { numerator := z, denominator := 1 } = Ordering.lt := by
  rw [compareCIPAtomicLabel_unitValue]
  exact Nat.compare_eq_lt.mpr hpos

/-- The production node comparator returns `lt` for a paired `(phantom, real positive-Z)` sphere. -/
theorem compareCanonicalNodeRule?_rule1a_phantom_real (mol : RawMolecule) (parent distance : ℕ)
    (node : CanonicalBranchNode) (h : node.provenance = CanonicalNodeProvenance.realAtom)
    (hpos : 0 < mol.atomZAt node.atom) :
    mol.compareCanonicalNodeRule? RawMolecule.CanonicalRuleStage.rule1a
        (mol.canonicalPhantom parent distance) node = some Ordering.lt := by
  have phantomLabel := canonicalRule1aLabel?_phantom mol parent distance
  have realLabel := canonicalRule1aLabel?_realAtom mol node h
  have hLt : RawMolecule.compareCIPAtomicLabel
      { numerator := 0, denominator := 1 }
      { numerator := mol.atomZAt node.atom, denominator := 1 } = Ordering.lt :=
    compareCIPAtomicLabel_phantom_lt_real (mol.atomZAt node.atom) hpos
  simp [RawMolecule.compareCanonicalNodeRule?, phantomLabel, realLabel, hLt]

/-- The cursor-sphere comparator returns `lt` on the single paired `(phantom, real positive-Z)`
sphere. -/
theorem compareCursorPairLabels_rule1a_phantom_real_single (mol : RawMolecule)
    (parent distance : ℕ) (node : CanonicalBranchNode)
    (h : node.provenance = CanonicalNodeProvenance.realAtom)
    (hpos : 0 < mol.atomZAt node.atom) :
    compareCursorPairLabels mol RawMolecule.CanonicalRuleStage.rule1a
        [(({ node := mol.canonicalPhantom parent distance } : CanonicalRerootCursor),
          ({ node := node } : CanonicalRerootCursor))] = some Ordering.lt := by
  have hNode := compareCanonicalNodeRule?_rule1a_phantom_real mol parent distance node h hpos
  simp [compareCursorPairLabels, hNode]

/-- The cursor rule returns `lt` on the single paired `(phantom, real positive-Z)` sphere,
independently of the recursive sibling callback and for every step budget. -/
theorem compareCursorRule_rule1a_single_phantom_real (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering) (fuel : ℕ)
    (parent distance : ℕ) (node : CanonicalBranchNode)
    (h : node.provenance = CanonicalNodeProvenance.realAtom)
    (hpos : 0 < mol.atomZAt node.atom) :
    compareCursorRule mol before RawMolecule.CanonicalRuleStage.rule1a (fuel + 1)
        [(({ node := mol.canonicalPhantom parent distance } : CanonicalRerootCursor),
          ({ node := node } : CanonicalRerootCursor))] = some Ordering.lt := by
  have hPair := compareCursorPairLabels_rule1a_phantom_real_single mol parent distance node h hpos
  simp [compareCursorRule, hPair, RawMolecule.defaultBranchWidthCap]

/-! ## 2. The conservative gate: strict result passes through when no swap exists -/

/-- The fail-closed conflict gate is `false` whenever the production exhaustive symmetry search
reports no constitution automorphism exchanging the two compared nodes around a shared incoming
frame.  Derived from the actual gate body; no acyclicity premise and no tied-result premise. -/
theorem occurrenceRootsProvedAutomorphic_eq_false_of_swapping_false (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (compiled : Ordering) (root : CanonicalBranchNode)
    (hl : left.previous? = some root) (hr : right.previous? = some root)
    (swapFalse : mol.hasConstitutionAutomorphismSwapping root.atom left.node.atom
      right.node.atom = false) :
    occurrenceRootsProvedAutomorphic mol fuel left right compiled = false := by
  simp [occurrenceRootsProvedAutomorphic, hl, hr, swapFalse]

/-- General factorization of the conservative certified stage: a successful raw constitutional
comparison the gate does not reject is returned unchanged. -/
theorem certifiedConstitutionalStage?_eq_of_gate_false (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (decision : Ordering)
    (raw : compareCursorBranchAt mol fuel RawMolecule.CanonicalRuleStage.rule2 left right =
      some decision)
    (gate : occurrenceRootsProvedAutomorphic mol fuel left right decision = false) :
    certifiedConstitutionalStage? mol fuel left right = some decision := by
  simp [certifiedConstitutionalStage?, raw, gate]

/-- General factorization of the uncapped authoritative certified stage. -/
theorem certifiedConstitutionalStageAuthoritative?_eq_of_gate_false (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (decision : Ordering)
    (raw : compareCursorBranchAtAuthoritative? mol fuel RawMolecule.CanonicalRuleStage.rule2
      left right = some decision)
    (gate : occurrenceRootsProvedAutomorphic mol fuel left right decision = false) :
    certifiedConstitutionalStageAuthoritative? mol fuel left right = some decision := by
  simp [certifiedConstitutionalStageAuthoritative?, raw, gate]

/-- A strict certified constitutional stage is returned verbatim by the fast occurrence protocol,
with no pseudo history and no Rule-4c carrier. -/
theorem compareOccurrenceBranches?_eq_of_constitutional (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (left right : CanonicalRerootCursor) (d : Ordering)
    (constitutional : certifiedConstitutionalStage? mol fuel left right = some d)
    (strict : d ≠ Ordering.eq) :
    compareOccurrenceBranches? mol state fuel left right = some { ordering := d, pseudo := false } := by
  cases d with
  | lt => simp [compareOccurrenceBranches?, constitutional]
  | gt => simp [compareOccurrenceBranches?, constitutional]
  | eq => exact absurd rfl strict

/-- A strict certified authoritative constitutional stage is returned verbatim by the authoritative
occurrence protocol. -/
theorem compareOccurrenceBranchesAuthoritative?_eq_of_constitutional (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (left right : CanonicalRerootCursor) (d : Ordering)
    (constitutional : certifiedConstitutionalStageAuthoritative? mol fuel left right = some d)
    (strict : d ≠ Ordering.eq) :
    compareOccurrenceBranchesAuthoritative? mol state fuel left right =
      some { ordering := d, pseudo := false } := by
  cases d with
  | lt => simp [compareOccurrenceBranchesAuthoritative?, constitutional]
  | gt => simp [compareOccurrenceBranchesAuthoritative?, constitutional]
  | eq => exact absurd rfl strict

/-- The composed fast-then-authoritative entry point returns the strict ordering because the fast
path already succeeds. -/
theorem compareOccurrenceBranchesComplete?_eq_of_fast (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : ℕ) (left right : CanonicalRerootCursor) (decision : OccurrenceComparison)
    (fast : compareOccurrenceBranches? mol state fuel left right = some decision) :
    compareOccurrenceBranchesComplete? mol state fuel left right = some decision := by
  simp [compareOccurrenceBranchesComplete?, fast]









theorem legacyOccurrenceFactAuthoritative?_eq_some_of_adjacent_strict (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List CanonicalRerootCursor) (pseudo : ℕ) (positions : List ℕ)
    (decisions : List OccurrenceComparison) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (atomObserved : mol.atomAt? node.atom = some spec)
    (parityObserved : spec.tetrahedral? = some parity)
    (frame : occurrenceLigandFrame? mol node = some roots)
    (sortedComputed : sortOccurrencesTrackedAuthoritative? mol state fuel roots =
      some (sorted, pseudo))
    (positionsComputed :
      (sorted.mapM fun cursor =>
        ((mol.ligandsWithLonePair node.atom).zipIdx.find?
          (fun entry => entry.1 == cursor.node.atom)).map Prod.snd) = some positions)
    (decisionsComputed : compareOccurrenceAdjacentPairsAuthoritative? mol state fuel sorted =
      some decisions)
    (strict : decisions.all (fun decision => decision.ordering != Ordering.eq) = true) :
    legacyOccurrenceFactAuthoritative? mol fuel state node =
      some { key := canonicalOccurrenceKey node
             atom := node.atom
             descriptor := RawMolecule.descriptorOfParity parity
               (RawMolecule.permutationIsEven positions)
             uppercase := (decisions.filter (fun decision => decision.pseudo)).length % 2 == 0
             priorityPositions := positions } := by
  have allStrict : ∀ decision ∈ decisions, ¬ decision.ordering = Ordering.eq := by
    simpa using strict
  unfold legacyOccurrenceFactAuthoritative?
  simp [atomObserved, parityObserved, frame, sortedComputed, positionsComputed,
    decisionsComputed]
  exact allStrict

/-- Public dispatch specialization: the primitive legacy derivation is used only when the
generated-real-tree profile is unavailable. Concrete cyclic witnesses establish this below. -/
theorem occurrenceFactAuthoritative?_eq_some_of_adjacent_strict (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (node : CanonicalBranchNode) (roots : List CanonicalRerootCursor)
    (sorted : List CanonicalRerootCursor) (pseudo : ℕ) (positions : List ℕ)
    (decisions : List OccurrenceComparison) (spec : AtomSpec) (parity : TetrahedralInputParity)
    (atomObserved : mol.atomAt? node.atom = some spec)
    (parityObserved : spec.tetrahedral? = some parity)
    (frame : occurrenceLigandFrame? mol node = some roots)
    (sortedComputed : sortOccurrencesTrackedAuthoritative? mol state fuel roots =
      some (sorted, pseudo))
    (positionsComputed :
      (sorted.mapM fun cursor =>
        ((mol.ligandsWithLonePair node.atom).zipIdx.find?
          (fun entry => entry.1 == cursor.node.atom)).map Prod.snd) = some positions)
    (decisionsComputed : compareOccurrenceAdjacentPairsAuthoritative? mol state fuel sorted =
      some decisions)
    (strict : decisions.all (fun decision => decision.ordering != Ordering.eq) = true)
    (profileUnavailable : FrameRuntime.profile? mol node = none) :
    occurrenceFactAuthoritative? mol fuel state node =
      some { key := canonicalOccurrenceKey node
             atom := node.atom
             descriptor := RawMolecule.descriptorOfParity parity
               (RawMolecule.permutationIsEven positions)
             uppercase := (decisions.filter (fun decision => decision.pseudo)).length % 2 == 0
             priorityPositions := positions } := by
  rw [occurrenceFactAuthoritative?_eq_legacy_of_profile_none mol fuel state node profileUnavailable]
  have allStrict : ∀ decision ∈ decisions, ¬ decision.ordering = Ordering.eq := by
    simpa using strict
  unfold legacyOccurrenceFactAuthoritative?
  simp [atomObserved, parityObserved, frame, sortedComputed, positionsComputed,
    decisionsComputed]
  exact allStrict

/-! ## 4. The independently specified equal-Z cyclic witness -/

/-- Finite comparison and cycle-test fuel.  It exceeds both ring lengths and the comparison
recursion depth, so the actual `ringPairCount`/`reachableAvoiding` cycle test fires and the cursor
comparison descends to the first ring-closure sphere.  This is a *finite-fuel* test, not unrestricted
graph classification. -/
def witnessFuel : ℕ := 6

/-- The annotated tetrahedral centre carbon: an ordinary aliphatic carbon with an explicit
`clockwise` configuration tag, so the production occurrence pipeline is actually invoked on it. -/
def centreAtom : AtomSpec :=
  { AtomSpec.aliphatic Element.C with tetrahedral? := some TetrahedralInputParity.clockwise }

/-- One written ordinary single bond. -/
def singleBond (left right : ℕ) : RawBond :=
  { source := left, target := right, kind := ParsedBondKind.single }

/-- The four-ligand carbon source.  Centre `0` carries a three-membered all-carbon ring `1-2-3-1`, a
four-membered all-carbon ring `4-5-6-7-4` (the two cyclic arms, both equal-Z carbon roots), a
terminal methyl `8`, and an ethyl `9-10`, all by ordinary single bonds.  Written directly from raw
bond data with no supplied comparison, ordering, key or auxiliary fact. -/
def witness : RawMolecule where
  atoms :=
    [centreAtom,
     AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C,
     AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C,
     AtomSpec.aliphatic Element.C,
     AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C]
  bonds :=
    [singleBond 0 1, singleBond 0 4, singleBond 0 8, singleBond 0 9,
     singleBond 1 2, singleBond 2 3, singleBond 3 1,
     singleBond 4 5, singleBond 5 6, singleBond 6 7, singleBond 7 4,
     singleBond 9 10]

/-- The actual generated runtime cursor for the centre's ligand `atom`: a real canonical root with
the real previous reference root, exactly the production shape. -/
def rootCursor (atom : ℕ) : CanonicalRerootCursor :=
  { node := canonicalRoot 0 atom, previous? := some (canonicalCenterRoot 0) }

/-- The four actual generated runtime cursors of the centre. -/
def generatedFrame : List CanonicalRerootCursor :=
  [rootCursor 1, rootCursor 4, rootCursor 8, rootCursor 9]

/-- The three-membered-ring arm cursor (equal-Z carbon root). -/
def leftCursor : CanonicalRerootCursor := rootCursor 1

/-- The four-membered-ring arm cursor (equal-Z carbon root). -/
def rightCursor : CanonicalRerootCursor := rootCursor 4

/-! ## 5. Independent structural certificate read from the source record alone -/

/-- Undirected written-bond existence read directly from the maintained source bond list; consults
neither `ringPairCount` nor the comparator. -/
def writtenBonded (mol : RawMolecule) (left right : ℕ) : Bool :=
  mol.bonds.any fun bond => bond.connects left right

/-- An explicit simple closed write-order bond path: at least three atoms, pairwise distinct, every
cyclic consecutive pair written as a source bond.  Independent structural certificate. -/
def ClosedBondPath (mol : RawMolecule) (cycle : List ℕ) : Bool :=
  decide (3 ≤ cycle.length) && decide cycle.Nodup &&
    (List.range cycle.length).all fun index =>
      writtenBonded mol (cycle.getD index 0) (cycle.getD ((index + 1) % cycle.length) 0)

/-- Every atom of an explicit path lies inside the molecule's own atom bound. -/
def allBelowAtomCount (mol : RawMolecule) (cycle : List ℕ) : Bool :=
  cycle.all fun atom => decide (atom < mol.atomCount)

/-! ## 6. Source-record and admission facts (independent of the comparator) -/

theorem witness_atomCount : witness.atomCount = 11 := by decide +kernel

theorem witness_wellFormed : witness.WellFormed := by
  rw [wellFormed_iff_all_bondEndpointsOK]
  decide +kernel

theorem witness_bondRecordsUnique : witness.BondRecordsUnique :=
  (bondRecordsUnique?_eq_true_iff witness).mp (by decide +kernel)

theorem witness_admissible : witness.Admissible :=
  ⟨witness_wellFormed, witness_bondRecordsUnique⟩

theorem witness_writtenNeighborExact : witness.WrittenNeighborExact := by
  unfold RawMolecule.WrittenNeighborExact
  decide +kernel

theorem witness_stereochemicalAdmissible : witness.StereochemicalAdmissible :=
  ⟨witness_admissible, witness_writtenNeighborExact⟩

theorem witness_threeRing_closed : ClosedBondPath witness [1, 2, 3] = true := by decide +kernel

theorem witness_fourRing_closed : ClosedBondPath witness [4, 5, 6, 7] = true := by decide +kernel

theorem witness_threeRing_bounded : allBelowAtomCount witness [1, 2, 3] = true := by decide +kernel

theorem witness_fourRing_bounded : allBelowAtomCount witness [4, 5, 6, 7] = true := by
  decide +kernel

/-- The two cyclic arms are different atom lists of different lengths, so they are genuinely
distinct rings of *different ring size*, not two enumerations of one ring. -/
theorem witness_rings_distinct :
    ([1, 2, 3] : List ℕ) ≠ [4, 5, 6, 7] ∧
      ([1, 2, 3] : List ℕ).length ≠ ([4, 5, 6, 7] : List ℕ).length := by
  decide +kernel

/-! ## 7. Physical generation, shared frame and root meaning -/

/-- The actual production generator returns exactly the four declared cursors, in its real order. -/
theorem witness_frame_generated :
    occurrenceLigandCursors witness (canonicalCenterRoot 0) = generatedFrame := by
  decide +kernel

/-- The actual production four-ligand frame is exactly the four generated cursors. -/
theorem witness_frame :
    occurrenceLigandFrame? witness (canonicalCenterRoot 0) = some generatedFrame := by
  decide +kernel

theorem witness_left_member : leftCursor ∈ generatedFrame := by
  rw [← witness_frame_generated]; exact List.mem_cons_self

theorem witness_right_member : rightCursor ∈ generatedFrame := by
  rw [← witness_frame_generated]
  exact List.mem_cons_of_mem _ List.mem_cons_self

theorem witness_roots_distinct : leftCursor.node.atom ≠ rightCursor.node.atom := by
  decide +kernel

/-- Both compared cursors carry one *shared* explicit incoming frame and each compared node is a
literal member of that frame's generated sibling family: exact production frame membership, not a
pair of nodes whose legacy occurrence keys merely collide. -/
theorem witness_shared_generated_frame :
    leftCursor.previous? = some (canonicalCenterRoot 0) ∧
      rightCursor.previous? = some (canonicalCenterRoot 0) ∧
      leftCursor.node ∈
        (({ node := canonicalCenterRoot 0 } : CanonicalRerootCursor).neighbors witness) ∧
      rightCursor.node ∈
        (({ node := canonicalCenterRoot 0 } : CanonicalRerootCursor).neighbors witness) := by
  refine ⟨rfl, rfl, ?_, ?_⟩ <;> decide +kernel

/-! ## 8. Equal-Z meaning and the actual cycle markers -/

theorem witness_left_atomZAt : witness.atomZAt leftCursor.node.atom = 6 := by decide +kernel

theorem witness_right_atomZAt : witness.atomZAt rightCursor.node.atom = 6 := by decide +kernel

/-- The two cyclic roots are **atomic-number tied**: the checked atomic-difference bridge genuinely
does not apply here. -/
theorem witness_tiedZ :
    witness.atomZAt leftCursor.node.atom = witness.atomZAt rightCursor.node.atom := by
  decide +kernel

/-- The actual production cycle test is `true` for the three-membered-ring arm root. -/
theorem witness_left_cyclic :
    witness.atomLiesInCycle witnessFuel leftCursor.node.atom = true := by decide +kernel

/-- The actual production cycle test is `true` for the four-membered-ring arm root. -/
theorem witness_right_cyclic :
    witness.atomLiesInCycle witnessFuel rightCursor.node.atom = true := by decide +kernel

/-- The shared centre is itself acyclic: the two rings meet only through atom `0`. -/
theorem witness_center_acyclic :
    witness.atomLiesInCycle witnessFuel 0 = false := by decide +kernel

/-! ## 9. The actual raw, authoritative, certified and protocol comparison, both directions -/

/-- Actual raw strict comparison, forward: the production cursor comparator returns `lt` on the two
equal-Z cyclic cursors (the three-membered arm ranks below the four-membered arm).  Derived by kernel
computation over the frozen production code, not assumed. -/
theorem witness_raw_forward :
    compareCursorBranchAt witness witnessFuel RawMolecule.CanonicalRuleStage.rule2 leftCursor
        rightCursor = some Ordering.lt := by
  decide +kernel

/-- Actual raw strict comparison, reverse: the same two generated cursors compared the other way
give `gt`.  Together with the forward direction this is the genuine directional sphere comparison. -/
theorem witness_raw_reverse :
    compareCursorBranchAt witness witnessFuel RawMolecule.CanonicalRuleStage.rule2 rightCursor
        leftCursor = some Ordering.gt := by
  decide +kernel

/-- The uncapped authoritative raw comparison agrees, forward. -/
theorem witness_authoritative_raw_forward :
    compareCursorBranchAtAuthoritative? witness witnessFuel RawMolecule.CanonicalRuleStage.rule2
        leftCursor rightCursor = some Ordering.lt := by
  decide +kernel

/-- The uncapped authoritative raw comparison agrees, reverse. -/
theorem witness_authoritative_raw_reverse :
    compareCursorBranchAtAuthoritative? witness witnessFuel RawMolecule.CanonicalRuleStage.rule2
        rightCursor leftCursor = some Ordering.gt := by
  decide +kernel

/-- **The exact new guard obstruction.**  Unequal ring size admits no constitution-preserving
bijection fixing the centre and exchanging the two arms; the actual exhaustive production symmetry
search reports `false`.  This is derived by the search itself, not supplied. -/
theorem witness_no_swapping :
    witness.hasConstitutionAutomorphismSwapping 0 leftCursor.node.atom
        rightCursor.node.atom = false := by
  decide +kernel

/-- The fail-closed conflict gate is `false` on this pair, in the forward direction. -/
theorem witness_gate_false_forward :
    occurrenceRootsProvedAutomorphic witness witnessFuel leftCursor rightCursor Ordering.lt = false :=
  occurrenceRootsProvedAutomorphic_eq_false_of_swapping_false witness witnessFuel leftCursor
    rightCursor Ordering.lt (canonicalCenterRoot 0) rfl rfl witness_no_swapping

/-- The fail-closed conflict gate is `false` on this pair, in the reverse direction. -/
theorem witness_gate_false_reverse :
    occurrenceRootsProvedAutomorphic witness witnessFuel rightCursor leftCursor Ordering.gt = false := by
  have reverseSwap : witness.hasConstitutionAutomorphismSwapping 0
      rightCursor.node.atom leftCursor.node.atom = false := by decide +kernel
  exact occurrenceRootsProvedAutomorphic_eq_false_of_swapping_false witness witnessFuel rightCursor
    leftCursor Ordering.gt (canonicalCenterRoot 0) rfl rfl reverseSwap

/-- The certified constitutional stage returns the strict ordering, forward. -/
theorem witness_certifiedStage_forward :
    certifiedConstitutionalStage? witness witnessFuel leftCursor rightCursor = some Ordering.lt :=
  certifiedConstitutionalStage?_eq_of_gate_false witness witnessFuel leftCursor rightCursor
    Ordering.lt witness_raw_forward witness_gate_false_forward

/-- The certified constitutional stage returns the strict ordering, reverse. -/
theorem witness_certifiedStage_reverse :
    certifiedConstitutionalStage? witness witnessFuel rightCursor leftCursor = some Ordering.gt :=
  certifiedConstitutionalStage?_eq_of_gate_false witness witnessFuel rightCursor leftCursor
    Ordering.gt witness_raw_reverse witness_gate_false_reverse

/-- The uncapped authoritative certified stage returns the strict ordering, forward. -/
theorem witness_authoritativeCertifiedStage_forward :
    certifiedConstitutionalStageAuthoritative? witness witnessFuel leftCursor rightCursor =
      some Ordering.lt :=
  certifiedConstitutionalStageAuthoritative?_eq_of_gate_false witness witnessFuel leftCursor
    rightCursor Ordering.lt witness_authoritative_raw_forward witness_gate_false_forward

/-- The uncapped authoritative certified stage returns the strict ordering, reverse. -/
theorem witness_authoritativeCertifiedStage_reverse :
    certifiedConstitutionalStageAuthoritative? witness witnessFuel rightCursor leftCursor =
      some Ordering.gt :=
  certifiedConstitutionalStageAuthoritative?_eq_of_gate_false witness witnessFuel rightCursor
    leftCursor Ordering.gt witness_authoritative_raw_reverse witness_gate_false_reverse

/-- **Actual occurrence/protocol comparison, forward.**  The production occurrence comparator returns
a strict decision on the two equal-Z cyclic ligand cursors: the three-membered ring ranks below the
four-membered ring. -/
theorem witness_protocol_forward :
    compareOccurrenceBranches? witness ([] : OccurrenceAuxState) witnessFuel leftCursor rightCursor =
      some ({ ordering := Ordering.lt, pseudo := false } : OccurrenceComparison) :=
  compareOccurrenceBranches?_eq_of_constitutional witness [] witnessFuel leftCursor rightCursor
    Ordering.lt witness_certifiedStage_forward (by decide)

/-- **Actual occurrence/protocol comparison, reverse.**  Compared the other way the same generated
pair gives `gt`, so the derived comparison is genuinely directional. -/
theorem witness_protocol_reverse :
    compareOccurrenceBranches? witness ([] : OccurrenceAuxState) witnessFuel rightCursor leftCursor =
      some ({ ordering := Ordering.gt, pseudo := false } : OccurrenceComparison) :=
  compareOccurrenceBranches?_eq_of_constitutional witness [] witnessFuel rightCursor leftCursor
    Ordering.gt witness_certifiedStage_reverse (by decide)

/-- The uncapped authoritative protocol agrees, forward. -/
theorem witness_authoritativeProtocol_forward :
    compareOccurrenceBranchesAuthoritative? witness ([] : OccurrenceAuxState) witnessFuel leftCursor
        rightCursor = some ({ ordering := Ordering.lt, pseudo := false } : OccurrenceComparison) :=
  compareOccurrenceBranchesAuthoritative?_eq_of_constitutional witness [] witnessFuel leftCursor
    rightCursor Ordering.lt witness_authoritativeCertifiedStage_forward (by decide)

/-- The uncapped authoritative protocol agrees, reverse. -/
theorem witness_authoritativeProtocol_reverse :
    compareOccurrenceBranchesAuthoritative? witness ([] : OccurrenceAuxState) witnessFuel rightCursor
        leftCursor = some ({ ordering := Ordering.gt, pseudo := false } : OccurrenceComparison) :=
  compareOccurrenceBranchesAuthoritative?_eq_of_constitutional witness [] witnessFuel rightCursor
    leftCursor Ordering.gt witness_authoritativeCertifiedStage_reverse (by decide)

/-- The composed `fast`-then-`authoritative` entry point returns the same strict outcome, both
directions, because the fast path already succeeds. -/
theorem witness_complete_protocol :
    compareOccurrenceBranchesComplete? witness ([] : OccurrenceAuxState) witnessFuel leftCursor
        rightCursor = some ({ ordering := Ordering.lt, pseudo := false } : OccurrenceComparison) ∧
      compareOccurrenceBranchesComplete? witness ([] : OccurrenceAuxState) witnessFuel rightCursor
        leftCursor = some ({ ordering := Ordering.gt, pseudo := false } : OccurrenceComparison) :=
  ⟨compareOccurrenceBranchesComplete?_eq_of_fast witness [] witnessFuel leftCursor rightCursor
      _ witness_protocol_forward,
    compareOccurrenceBranchesComplete?_eq_of_fast witness [] witnessFuel rightCursor leftCursor
      _ witness_protocol_reverse⟩

/-- The forward strict outcome is neither a refusal nor a tie. -/
theorem witness_protocol_forward_not_tie :
    (compareOccurrenceBranches? witness ([] : OccurrenceAuxState) witnessFuel leftCursor
        rightCursor).map OccurrenceComparison.ordering ≠ some Ordering.eq := by
  rw [witness_protocol_forward]; decide

/-- The forward strict outcome is decidably non-refusing. -/
theorem witness_protocol_forward_ne_none :
    compareOccurrenceBranches? witness ([] : OccurrenceAuxState) witnessFuel leftCursor rightCursor ≠
      none := by
  rw [witness_protocol_forward]; simp

/-! ## 10. The four-root production sort and the actual local consumer -/

/-- The actual production tracked sort on the four generated cursors returns the four roots in
strict descending priority order with zero pseudo comparisons.  This is *derived* by evaluating the
production sorter, not supplied. -/
theorem witness_sort :
    sortOccurrencesTrackedAuthoritative? witness ([] : OccurrenceAuxState) witnessFuel generatedFrame =
      some ([rootCursor 4, rootCursor 1, rootCursor 9, rootCursor 8], 0) := by
  decide +kernel

/-- The actual adjacent-comparison driver on the sorted four-root frame returns three strict
decisions, so the descriptor-strictness guard genuinely holds. -/
theorem witness_adjacent_strict :
    compareOccurrenceAdjacentPairsAuthoritative? witness ([] : OccurrenceAuxState) witnessFuel
        [rootCursor 4, rootCursor 1, rootCursor 9, rootCursor 8] =
      some [ { ordering := Ordering.gt, pseudo := false },
             { ordering := Ordering.gt, pseudo := false },
             { ordering := Ordering.gt, pseudo := false } ] := by
  decide +kernel

/-- The strictness guard value on the actual adjacent list is `true`. -/
theorem witness_adjacent_all_strict :
    (([{ ordering := Ordering.gt, pseudo := false },
       { ordering := Ordering.gt, pseudo := false },
       { ordering := Ordering.gt, pseudo := false }] : List OccurrenceComparison).all
      (fun decision => decision.ordering != Ordering.eq)) = true := by
  decide +kernel

/-- The actual written-slot projection of the sorted frame. -/
theorem witness_positions :
    ([rootCursor 4, rootCursor 1, rootCursor 9, rootCursor 8].mapM fun cursor =>
      ((witness.ligandsWithLonePair 0).zipIdx.find?
        (fun entry => entry.1 == cursor.node.atom)).map Prod.snd) = some [1, 0, 3, 2] := by
  decide +kernel

/-- The cyclic canonical tree is outside the repaired real-tree profile. -/
theorem witness_profile_unavailable :
    FrameRuntime.profile? witness (canonicalCenterRoot 0) = none := by
  decide +kernel





theorem witness_local_fact :
    occurrenceFactAuthoritative? witness witnessFuel ([] : OccurrenceAuxState)
        (canonicalCenterRoot 0) =
      some { key := canonicalOccurrenceKey (canonicalCenterRoot 0)
             atom := 0
             descriptor := RawMolecule.descriptorOfParity TetrahedralInputParity.clockwise
               (RawMolecule.permutationIsEven [1, 0, 3, 2])
             uppercase := true
             priorityPositions := [1, 0, 3, 2] } := by
  have h := occurrenceFactAuthoritative?_eq_some_of_adjacent_strict witness witnessFuel []
    (canonicalCenterRoot 0) generatedFrame
    [rootCursor 4, rootCursor 1, rootCursor 9, rootCursor 8] 0 [1, 0, 3, 2]
    [ { ordering := Ordering.gt, pseudo := false },
      { ordering := Ordering.gt, pseudo := false },
      { ordering := Ordering.gt, pseudo := false } ]
    centreAtom TetrahedralInputParity.clockwise rfl rfl witness_frame witness_sort
    (by exact witness_positions) witness_adjacent_strict witness_adjacent_all_strict witness_profile_unavailable
  simpa using h

/-- The actual local production consumer does **not** refuse the equal-Z cyclic frame. -/
theorem witness_local_fact_ne_none :
    occurrenceFactAuthoritative? witness witnessFuel ([] : OccurrenceAuxState)
        (canonicalCenterRoot 0) ≠ none := by
  rw [witness_local_fact]; simp

/-- A strict adjacent decision between the two equal-Z cyclic carbon roots is literally consumed by
the production sort: the sorted frame's first adjacent pair is exactly the four-membered-then-
three-membered comparison derived above. -/
theorem witness_sort_consumes_equalZ_pair :
    (compareOccurrenceAdjacentPairsAuthoritative? witness ([] : OccurrenceAuxState) witnessFuel
        [rootCursor 4, rootCursor 1, rootCursor 9, rootCursor 8]).map
        (fun comparisons => comparisons.map (fun comparison => comparison.ordering)) =
      some [Ordering.gt, Ordering.gt, Ordering.gt] ∧
      rightCursor = rootCursor 4 ∧ leftCursor = rootCursor 1 := by
  refine ⟨?_, rfl, rfl⟩
  rw [witness_adjacent_strict]
  rfl

/-! ## 11. The finite independent domain, bundled -/

/-- The finite independent structural domain of the witness, all read from the source record alone:
atom count, well-formedness, both closed ring paths of different size, both atom bounds, distinct
ring paths and distinct equal-Z cyclic roots.  No clause consults the marker, the gate or the
comparator. -/
theorem witness_independent_domain :
    witness.atomCount = 11 ∧
      witness.WellFormed ∧
      ClosedBondPath witness [1, 2, 3] = true ∧
      ClosedBondPath witness [4, 5, 6, 7] = true ∧
      allBelowAtomCount witness [1, 2, 3] = true ∧
      allBelowAtomCount witness [4, 5, 6, 7] = true ∧
      ([1, 2, 3] : List ℕ) ≠ [4, 5, 6, 7] ∧
      leftCursor.node.atom ≠ rightCursor.node.atom :=
  ⟨witness_atomCount, witness_wellFormed, witness_threeRing_closed, witness_fourRing_closed,
    witness_threeRing_bounded, witness_fourRing_bounded, witness_rings_distinct.1,
    witness_roots_distinct⟩

/-- Bundled headline deliverable: the two equal-Z cyclic carbon arms are actual generated members of
one four-root production frame, both cyclic, strictly compared in both directions by the actual
protocol, with the guard `false`, and the actual four-root sort/consumer strictly resolves them. -/
theorem witness_equalZ_cyclic_first_difference :
    leftCursor ∈ generatedFrame ∧ rightCursor ∈ generatedFrame ∧
      witness.atomLiesInCycle witnessFuel leftCursor.node.atom = true ∧
      witness.atomLiesInCycle witnessFuel rightCursor.node.atom = true ∧
      witness.atomZAt leftCursor.node.atom = witness.atomZAt rightCursor.node.atom ∧
      compareOccurrenceBranches? witness ([] : OccurrenceAuxState) witnessFuel leftCursor
          rightCursor = some ({ ordering := Ordering.lt, pseudo := false } :
            OccurrenceComparison) ∧
      compareOccurrenceBranches? witness ([] : OccurrenceAuxState) witnessFuel rightCursor
          leftCursor = some ({ ordering := Ordering.gt, pseudo := false } :
            OccurrenceComparison) ∧
      witness.hasConstitutionAutomorphismSwapping 0 leftCursor.node.atom
          rightCursor.node.atom = false :=
  ⟨witness_left_member, witness_right_member, witness_left_cyclic, witness_right_cyclic,
    witness_tiedZ, witness_protocol_forward, witness_protocol_reverse, witness_no_swapping⟩

end CyclicFirstConstitutionalDifference
end CyclicFirstConstitutionalDifferenceProofs
end UniversalProof
end TetraStereo
