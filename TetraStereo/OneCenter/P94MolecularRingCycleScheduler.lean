import TetraStereo.OneCenter.P94CoordinateRingWitnessDiscovery
import Mathlib.Data.List.Cycle

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Exhaustive molecular P-94 ring-cycle scheduling

The coordinate P-94 pipeline formerly required a caller to choose and order every cyclic atom
carrier.  This module removes that boundary for the represented ring-conformation families.  It
exhausts every duplicate-free list of in-bounds raw-molecule atoms, validates the closed traversal
against the actual molecular bonds, and keeps exactly one least ordered traversal for each atom
set.  Consequently rotations and reversals cannot create duplicate scheduled carriers.

## Ring-definition scope

“Ring” is not harmless terminology in fused and bridged systems: different chemical purposes use
different cycle bases.  The independent predicate below is therefore deliberately basis-neutral.
It recognizes a **chordless induced molecular cycle**: the named consecutive/closing bonds exist,
and no additional molecular bond joins two nonconsecutive atoms of the same carrier.  Every such
cycle is scheduled, including overlapping chordless cycles in fused or bridged components.  This
module does *not* identify those cycles with an SSSR, a minimum cycle basis, or any other unstated
chemical ring-selection convention.  `P94RingCarrierOverlapAmbiguous` exposes exactly the case in
which overlapping admitted carriers remain.  A future source-backed ring-basis rule can filter the
same exhaustive scheduler without changing its finite completeness theorem.
-/

namespace P94MolecularRingCycleScheduler

open BlueBookP94
open BlueBookP94.CoordinateRing

/-! ## Exhaustive bounded traversal universe -/

/-- Every duplicate-free list whose entries lie in `0 .. atomCount-1`.

The definition first chooses an atom subset and then enumerates every permutation of that subset.
It is finite and exhaustive; no ring-size or search-depth heuristic occurs here. -/
noncomputable def boundedNodupTraversals (atomCount : ℕ) : Finset (List ℕ) := by
  classical
  exact
    (((Finset.range atomCount).powerset.toList.flatMap fun vertices =>
      vertices.toList.permutations).toFinset)

/-- Exact finite-universe theorem: enumeration membership is neither weaker nor stronger than
duplicate-free in-bounds atom numbering. -/
theorem mem_boundedNodupTraversals_iff (atomCount : ℕ) (atoms : List ℕ) :
    atoms ∈ boundedNodupTraversals atomCount ↔
      atoms.Nodup ∧ ∀ atom ∈ atoms, atom < atomCount := by
  classical
  constructor
  · intro present
    have listPresent :
        atoms ∈ (Finset.range atomCount).powerset.toList.flatMap
          (fun vertices => vertices.toList.permutations) := by
      simpa [boundedNodupTraversals] using present
    rcases List.mem_flatMap.mp listPresent with
      ⟨vertices, verticesPresent, permutationPresent⟩
    have verticesSubset : vertices ⊆ Finset.range atomCount :=
      Finset.mem_powerset.mp (by simpa using verticesPresent)
    have permutation : atoms.Perm vertices.toList :=
      List.mem_permutations.mp permutationPresent
    refine ⟨permutation.nodup_iff.mpr vertices.nodup_toList, ?_⟩
    intro atom atomPresent
    have vertexPresent : atom ∈ vertices.toList :=
      permutation.mem_iff.mp atomPresent
    exact Finset.mem_range.mp (verticesSubset (by simpa using vertexPresent))
  · rintro ⟨nodup, bounded⟩
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    refine ⟨atoms.toFinset, ?_, ?_⟩
    · have subset : atoms.toFinset ⊆ Finset.range atomCount := by
        intro atom atomPresent
        exact Finset.mem_range.mpr (bounded atom (List.mem_toFinset.mp atomPresent))
      simpa using Finset.mem_powerset.mpr subset
    · apply List.mem_permutations.mpr
      exact (atoms.toFinset_toList nodup).symm

/-! ## Independent molecular carrier semantics -/

/-- An undirected edge belonging to the named closed cyclic traversal.

Using `List.next` and `List.prev` makes the unoriented nature of the edge explicit and, unlike a
bare permutation of the vertex list, retains exactly the cyclic incidence needed below. -/
def IsNamedCycleEdge (atoms : List ℕ) (left right : ℕ) : Prop :=
  ∃ leftMember : left ∈ atoms,
    atoms.next left leftMember = right ∨ atoms.prev left leftMember = right

noncomputable instance isNamedCycleEdgeDecidable (atoms : List ℕ) (left right : ℕ) :
    Decidable (IsNamedCycleEdge atoms left right) :=
  Classical.propDecidable _

/-- A dummy-kind unit used only to reuse the kind-independent molecular `CycleCarrier` check. -/
private def traversalUnit (atoms : List ℕ) : P94ConformationUnit :=
  { kind := .fiveMemberedRing, atoms := atoms }

/-- Independent ordered witness for one chordless induced molecular cycle.

`CyclicallyBonded` retains the raw-record existence semantics used by `ValidFor`, while
`CycleCarrier` additionally requires a positive normalized bond order for every closing and
consecutive edge.  The final biconditional excludes chords and states that the traversal accounts
for every molecular bond internal to the carrier. -/
def IndependentP94RingTraversal (molecule : RawMolecule) (atoms : List ℕ) : Prop :=
  3 ≤ atoms.length ∧
    atoms.Nodup ∧
    (∀ atom ∈ atoms, atom < molecule.atomCount) ∧
    P94ConformationUnit.CyclicallyBonded molecule atoms ∧
    (traversalUnit atoms).CycleCarrier molecule ∧
    ∀ left ∈ atoms, ∀ right ∈ atoms, left ≠ right →
      (P94ConformationUnit.Bonded molecule left right ↔
        IsNamedCycleEdge atoms left right)

noncomputable instance independentP94RingTraversalDecidable
    (molecule : RawMolecule) (atoms : List ℕ) :
    Decidable (IndependentP94RingTraversal molecule atoms) :=
  Classical.propDecidable _

/-- Basis-neutral, ordering-independent carrier: a finite atom set admitting a chordless induced
molecular-cycle traversal.  The existential traversal is specification evidence, not caller input
to the scheduler. -/
def DeclarativeP94RingCarrier (molecule : RawMolecule) (vertices : Finset ℕ) : Prop :=
  ∃ atoms,
    atoms.toFinset = vertices ∧ IndependentP94RingTraversal molecule atoms

/-- Explicit fused/bridged ambiguity boundary.  It holds when an admitted carrier overlaps a
different admitted chordless carrier.  The scheduler retains both rather than silently choosing a
cycle basis. -/
def P94RingCarrierOverlapAmbiguous
    (molecule : RawMolecule) (vertices : Finset ℕ) : Prop :=
  DeclarativeP94RingCarrier molecule vertices ∧
    ∃ other,
      DeclarativeP94RingCarrier molecule other ∧
      other ≠ vertices ∧
      ¬Disjoint vertices other

/-- The P-94 conformation-unit kind admitted at a given cycle length.

Five-membered carriers feed envelope perception; six-membered carriers feed chair, boat,
half-chair, and twist perception; length eight has both tub and crown carrier roles; and every
larger even length at least eight has a crown role. -/
def P94RingKindSupportsLength (kind : P94ConformationUnitKind) (length : ℕ) : Prop :=
  match kind with
  | .fiveMemberedRing => length = 5
  | .sixMemberedRing => length = 6
  | .crownRing => 8 ≤ length ∧ Even length
  | .eightMemberedTubRing => length = 8
  | .wholeMoleculeConformation | .torsionAxis | .bicyclicBridge => False

instance p94RingKindSupportsLengthDecidable
    (kind : P94ConformationUnitKind) (length : ℕ) :
    Decidable (P94RingKindSupportsLength kind length) := by
  cases kind <;> simp [P94RingKindSupportsLength] <;> infer_instance

/-- Exactly the unit kinds created by this molecular ring scheduler. -/
def p94ScheduledRingKinds : Finset P94ConformationUnitKind :=
  [.fiveMemberedRing, .sixMemberedRing, .crownRing, .eightMemberedTubRing].toFinset

@[simp] theorem mem_p94ScheduledRingKinds_iff (kind : P94ConformationUnitKind) :
    kind ∈ p94ScheduledRingKinds ↔
      kind = .fiveMemberedRing ∨ kind = .sixMemberedRing ∨
        kind = .crownRing ∨ kind = .eightMemberedTubRing := by
  simp [p94ScheduledRingKinds]

theorem kind_mem_p94ScheduledRingKinds_of_supportsLength
    (kind : P94ConformationUnitKind) (length : ℕ)
    (supported : P94RingKindSupportsLength kind length) :
    kind ∈ p94ScheduledRingKinds := by
  cases kind <;> simp_all [P94RingKindSupportsLength, p94ScheduledRingKinds]

theorem independentP94RingTraversal_mem_bounded
    (molecule : RawMolecule) (atoms : List ℕ)
    (independent : IndependentP94RingTraversal molecule atoms) :
    atoms ∈ boundedNodupTraversals molecule.atomCount :=
  (mem_boundedNodupTraversals_iff molecule.atomCount atoms).mpr
    ⟨independent.2.1, independent.2.2.1⟩

/-! ## Rigidity of a chordless cycle traversal -/

private theorem isNamedCycleEdge_iff_of_isRotated
    {first second : List ℕ} (rotated : first ~r second)
    (firstNodup : first.Nodup) (left right : ℕ) :
    IsNamedCycleEdge first left right ↔ IsNamedCycleEdge second left right := by
  constructor
  · rintro ⟨leftMember, forward | backward⟩
    · refine ⟨rotated.mem_iff.mp leftMember, Or.inl ?_⟩
      rw [← List.isRotated_next_eq rotated firstNodup leftMember]
      exact forward
    · refine ⟨rotated.mem_iff.mp leftMember, Or.inr ?_⟩
      rw [← List.isRotated_prev_eq rotated firstNodup leftMember]
      exact backward
  · intro edge
    rcases edge with ⟨leftMember, forward | backward⟩
    · refine ⟨rotated.symm.mem_iff.mp leftMember, Or.inl ?_⟩
      rw [← List.isRotated_next_eq rotated.symm
        (rotated.nodup_iff.mp firstNodup) leftMember]
      exact forward
    · refine ⟨rotated.symm.mem_iff.mp leftMember, Or.inr ?_⟩
      rw [← List.isRotated_prev_eq rotated.symm
        (rotated.nodup_iff.mp firstNodup) leftMember]
      exact backward

private theorem isNamedCycleEdge_reverse_iff
    (atoms : List ℕ) (nodup : atoms.Nodup) (left right : ℕ) :
    IsNamedCycleEdge atoms.reverse left right ↔ IsNamedCycleEdge atoms left right := by
  constructor
  · rintro ⟨leftMember, forward | backward⟩
    · refine ⟨List.mem_reverse.mp leftMember, Or.inr ?_⟩
      exact (List.next_reverse_eq_prev atoms nodup left
        (List.mem_reverse.mp leftMember)).symm.trans forward
    · refine ⟨List.mem_reverse.mp leftMember, Or.inl ?_⟩
      exact (List.prev_reverse_eq_next atoms nodup left
        (List.mem_reverse.mp leftMember)).symm.trans backward
  · rintro ⟨leftMember, forward | backward⟩
    · refine ⟨List.mem_reverse.mpr leftMember, Or.inr ?_⟩
      exact (List.prev_reverse_eq_next atoms nodup left leftMember).trans forward
    · refine ⟨List.mem_reverse.mpr leftMember, Or.inl ?_⟩
      exact (List.next_reverse_eq_prev atoms nodup left leftMember).trans backward

private theorem isNamedCycleEdge_ne
    {atoms : List ℕ} (three : 3 ≤ atoms.length) (nodup : atoms.Nodup)
    {left right : ℕ} (edge : IsNamedCycleEdge atoms left right) :
    left ≠ right := by
  rintro rfl
  rcases edge with ⟨member, forward | backward⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem member
    rw [List.next_getElem atoms nodup i hi] at forward
    have indexIdentity : (i + 1) % atoms.length = i :=
      nodup.getElem_inj_iff.mp forward
    by_cases wraps : i + 1 = atoms.length
    · rw [wraps, Nat.mod_self] at indexIdentity
      omega
    · have beforeEnd : i + 1 < atoms.length := by omega
      rw [Nat.mod_eq_of_lt beforeEnd] at indexIdentity
      omega
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem member
    rw [List.prev_getElem atoms nodup i hi] at backward
    have indexIdentity : (i + (atoms.length - 1)) % atoms.length = i :=
      nodup.getElem_inj_iff.mp backward
    by_cases zero : i = 0
    · subst i
      have predecessorIdentity :
          (0 + (atoms.length - 1)) % atoms.length = atoms.length - 1 := by
        rw [Nat.zero_add, Nat.mod_eq_of_lt]
        omega
      omega
    · have sumIdentity : i + (atoms.length - 1) = atoms.length + (i - 1) := by
        omega
      have predecessorIdentity :
          (i + (atoms.length - 1)) % atoms.length = i - 1 := by
        rw [sumIdentity, Nat.add_mod_left, Nat.mod_eq_of_lt]
        omega
      omega

/-- `List.next` and `List.prev` carry membership proofs in their types; this helper transports
equal vertex values without relying on fragile dependent rewriting of those proof arguments. -/
private theorem next_congr_of_eq {Alpha : Type*} [DecidableEq Alpha] (atoms : List Alpha)
    {first second : Alpha} (equal : first = second)
    (firstMember : first ∈ atoms) (secondMember : second ∈ atoms) :
    atoms.next first firstMember = atoms.next second secondMember := by
  subst second
  rfl

private theorem prev_congr_of_eq {Alpha : Type*} [DecidableEq Alpha] (atoms : List Alpha)
    {first second : Alpha} (equal : first = second)
    (firstMember : first ∈ atoms) (secondMember : second ∈ atoms) :
    atoms.prev first firstMember = atoms.prev second secondMember := by
  subst second
  rfl

private theorem list_eq_of_same_head_next_and_named_edges
    {first second : List ℕ}
    (three : 3 ≤ first.length)
    (sameLength : first.length = second.length)
    (firstNodup : first.Nodup) (secondNodup : second.Nodup)
    (sameHead :
      first.get ⟨0, by omega⟩ = second.get ⟨0, by omega⟩)
    (sameNext :
      first.next (first.get ⟨0, by omega⟩) (List.get_mem first ⟨0, by omega⟩) =
        second.next (second.get ⟨0, by omega⟩) (List.get_mem second ⟨0, by omega⟩))
    (edgeSubset : ∀ left right,
      IsNamedCycleEdge second left right → IsNamedCycleEdge first left right) :
    first = second := by
  apply List.ext_getElem
  · exact sameLength
  · intro position firstBound secondBound
    have allPositions :
        ∀ index (firstIndexBound : index < first.length)
          (secondIndexBound : index < second.length),
          first[index] = second[index] := by
      intro index
      induction index using Nat.strong_induction_on with
      | h index earlier =>
          intro firstIndexBound secondIndexBound
          by_cases atHead : index = 0
          · subst index
            exact sameHead
          by_cases atSecond : index = 1
          · subst index
            have firstNext :
                first.next (first.get ⟨0, by omega⟩)
                    (List.get_mem first ⟨0, by omega⟩) =
                  first.get ⟨1, by omega⟩ := by
              simpa [Nat.mod_eq_of_lt (by omega : 1 < first.length)] using
                List.next_getElem first firstNodup 0 (by omega)
            have secondNext :
                second.next (second.get ⟨0, by omega⟩)
                    (List.get_mem second ⟨0, by omega⟩) =
                  second.get ⟨1, by omega⟩ := by
              simpa [Nat.mod_eq_of_lt (by omega : 1 < second.length)] using
                List.next_getElem second secondNodup 0 (by omega)
            exact firstNext.symm.trans (sameNext.trans secondNext)
          have twoLe : 2 ≤ index := by omega
          have predecessorFirstBound : index - 1 < first.length := by omega
          have predecessorSecondBound : index - 1 < second.length := by omega
          have priorFirstBound : index - 2 < first.length := by omega
          have priorSecondBound : index - 2 < second.length := by omega
          have predecessorIdentity := earlier (index - 1) (by omega)
            predecessorFirstBound predecessorSecondBound
          have priorIdentity := earlier (index - 2) (by omega)
            priorFirstBound priorSecondBound
          have secondEdge :
              IsNamedCycleEdge second second[index - 1] second[index] := by
            refine ⟨List.get_mem second ⟨index - 1, predecessorSecondBound⟩, Or.inl ?_⟩
            rw [List.next_getElem second secondNodup (index - 1)
              predecessorSecondBound]
            congr 1
            rw [Nat.sub_add_cancel (by omega : 1 ≤ index),
              Nat.mod_eq_of_lt secondIndexBound]
          have firstEdge := edgeSubset _ _ secondEdge
          rw [← predecessorIdentity] at firstEdge
          rcases firstEdge with ⟨_, forward | backward⟩
          · rw [List.next_getElem first firstNodup (index - 1)
              predecessorFirstBound] at forward
            have successorIndex : ((index - 1) + 1) % first.length = index := by
              rw [Nat.sub_add_cancel (by omega : 1 ≤ index),
                Nat.mod_eq_of_lt firstIndexBound]
            have successorFin :
                (⟨((index - 1) + 1) % first.length, by omega⟩ : Fin first.length) =
                  ⟨index, firstIndexBound⟩ := Fin.ext successorIndex
            exact (congrArg first.get successorFin).symm.trans forward
          · rw [List.prev_getElem first firstNodup (index - 1)
              predecessorFirstBound] at backward
            have sumIdentity :
                (index - 1) + (first.length - 1) =
                  first.length + (index - 2) := by
              omega
            have predecessorIndex :
                ((index - 1) + (first.length - 1)) % first.length = index - 2 := by
              rw [sumIdentity, Nat.add_mod_left, Nat.mod_eq_of_lt priorFirstBound]
            have predecessorFin :
                (⟨((index - 1) + (first.length - 1)) % first.length, by omega⟩ :
                    Fin first.length) = ⟨index - 2, priorFirstBound⟩ :=
              Fin.ext predecessorIndex
            have backward' : first[index - 2] = second[index] :=
              (congrArg first.get predecessorFin).symm.trans backward
            have collision : second[index - 2] = second[index] :=
              priorIdentity.symm.trans backward'
            have impossible : index - 2 = index :=
              secondNodup.getElem_inj_iff.mp collision
            omega
    exact allPositions position firstBound secondBound

/-- Two independent traversals of the same chordless carrier differ only by a cyclic rotation or
by reversal followed by a cyclic rotation.  Equal vertex sets alone would not imply this for an
arbitrary graph; the proof uses both chordless edge biconditionals to identify the complete
induced edge graph, then uses `Nodup` and length at least three to force one consistent direction
around that graph. -/
theorem independentP94RingTraversals_dihedrallyRelated
    (molecule : RawMolecule) (first second : List ℕ)
    (firstIndependent : IndependentP94RingTraversal molecule first)
    (secondIndependent : IndependentP94RingTraversal molecule second)
    (sameVertices : first.toFinset = second.toFinset) :
    first ~r second ∨ first.reverse ~r second := by
  classical
  have firstNodup := firstIndependent.2.1
  have secondNodup := secondIndependent.2.1
  have firstThree := firstIndependent.1
  have secondThree := secondIndependent.1
  have sameLength : first.length = second.length := by
    rw [← List.toFinset_card_of_nodup firstNodup,
      ← List.toFinset_card_of_nodup secondNodup, sameVertices]
  have sameEdges : ∀ left right,
      IsNamedCycleEdge first left right ↔ IsNamedCycleEdge second left right := by
    intro left right
    constructor
    · intro edge
      have leftFirst := edge.choose
      have rightFirst : right ∈ first := by
        rcases edge.choose_spec with forward | backward
        · exact forward ▸ List.next_mem first left edge.choose
        · exact backward ▸ List.prev_mem first left edge.choose
      have leftSecond : left ∈ second := by
        rw [← List.mem_toFinset, ← sameVertices, List.mem_toFinset]
        exact leftFirst
      have rightSecond : right ∈ second := by
        rw [← List.mem_toFinset, ← sameVertices, List.mem_toFinset]
        exact rightFirst
      have distinct := isNamedCycleEdge_ne firstThree firstNodup edge
      have firstChordless := firstIndependent.2.2.2.2.2
      have secondChordless := secondIndependent.2.2.2.2.2
      specialize firstChordless left leftFirst right rightFirst distinct
      specialize secondChordless left leftSecond right rightSecond distinct
      exact secondChordless.mp (firstChordless.mpr edge)
    · intro edge
      have leftSecond := edge.choose
      have rightSecond : right ∈ second := by
        rcases edge.choose_spec with forward | backward
        · exact forward ▸ List.next_mem second left edge.choose
        · exact backward ▸ List.prev_mem second left edge.choose
      have leftFirst : left ∈ first := by
        rw [← List.mem_toFinset, sameVertices, List.mem_toFinset]
        exact leftSecond
      have rightFirst : right ∈ first := by
        rw [← List.mem_toFinset, sameVertices, List.mem_toFinset]
        exact rightSecond
      have distinct := isNamedCycleEdge_ne secondThree secondNodup edge
      have firstChordless := firstIndependent.2.2.2.2.2
      have secondChordless := secondIndependent.2.2.2.2.2
      specialize secondChordless left leftSecond right rightSecond distinct
      specialize firstChordless left leftFirst right rightFirst distinct
      exact firstChordless.mp (secondChordless.mpr edge)
  have secondZeroBound : 0 < second.length := by omega
  have secondHeadMember : second[0] ∈ second :=
    List.get_mem second ⟨0, secondZeroBound⟩
  have secondHeadFirstMember : second[0] ∈ first := by
    rw [← List.mem_toFinset, sameVertices, List.mem_toFinset]
    exact secondHeadMember
  obtain ⟨offset, offsetBound, offsetValue⟩ :=
    List.getElem_of_mem secondHeadFirstMember
  let aligned := first.rotate offset
  have firstToAligned : first ~r aligned := ⟨offset, rfl⟩
  have alignedNodup : aligned.Nodup := firstToAligned.nodup_iff.mp firstNodup
  have alignedLength : aligned.length = second.length := by
    simp [aligned, sameLength]
  have alignedThree : 3 ≤ aligned.length := by simpa [aligned] using firstThree
  have alignedHead :
      aligned.get ⟨0, by omega⟩ = second.get ⟨0, secondZeroBound⟩ := by
    dsimp only [aligned]
    rw [List.get_rotate]
    simpa [Nat.mod_eq_of_lt offsetBound] using offsetValue
  have alignedEdges : ∀ left right,
      IsNamedCycleEdge aligned left right ↔ IsNamedCycleEdge second left right := by
    intro left right
    exact (isNamedCycleEdge_iff_of_isRotated firstToAligned firstNodup left right).symm.trans
      (sameEdges left right)
  have secondOneBound : 1 < second.length := by omega
  have secondInitialEdge : IsNamedCycleEdge second second[0] second[1] := by
    refine ⟨List.get_mem second ⟨0, secondZeroBound⟩, Or.inl ?_⟩
    rw [List.next_getElem second secondNodup 0 secondZeroBound]
    simp [Nat.mod_eq_of_lt secondOneBound]
  have alignedInitialEdge := (alignedEdges _ _).mpr secondInitialEdge
  have alignedHeadValue : aligned[0] = second[0] := alignedHead
  have secondNextAtHead :
      second.next (second.get ⟨0, secondZeroBound⟩) secondHeadMember =
        second.get ⟨1, secondOneBound⟩ := by
    simpa [Nat.mod_eq_of_lt secondOneBound] using
      List.next_getElem second secondNodup 0 secondZeroBound
  simp only [← alignedHeadValue] at alignedInitialEdge
  rcases alignedInitialEdge with ⟨_, sameDirection | oppositeDirection⟩
  · have sameNext :
        aligned.next (aligned.get ⟨0, by omega⟩)
            (List.get_mem aligned ⟨0, by omega⟩) =
          second.next (second.get ⟨0, secondZeroBound⟩) secondHeadMember := by
      have sameDirection' :
          aligned.next (aligned.get ⟨0, by omega⟩)
              (List.get_mem aligned ⟨0, by omega⟩) =
            second.get ⟨1, secondOneBound⟩ := by
        simpa only using sameDirection
      exact sameDirection'.trans secondNextAtHead.symm
    have equal := list_eq_of_same_head_next_and_named_edges alignedThree alignedLength
      alignedNodup secondNodup alignedHead sameNext
      (fun left right edge => (alignedEdges left right).mpr edge)
    exact Or.inl (firstToAligned.trans (equal ▸ List.IsRotated.refl second))
  · have reverseFirstNodup : first.reverse.Nodup := List.nodup_reverse.mpr firstNodup
    have secondHeadReverseMember : second[0] ∈ first.reverse :=
      List.mem_reverse.mpr secondHeadFirstMember
    obtain ⟨reverseOffset, reverseOffsetBound, reverseOffsetValue⟩ :=
      List.getElem_of_mem secondHeadReverseMember
    let reflected := first.reverse.rotate reverseOffset
    have reverseToReflected : first.reverse ~r reflected := ⟨reverseOffset, rfl⟩
    have reflectedNodup : reflected.Nodup :=
      reverseToReflected.nodup_iff.mp reverseFirstNodup
    have reflectedLength : reflected.length = second.length := by
      simp [reflected, sameLength]
    have reflectedThree : 3 ≤ reflected.length := by simpa [reflected] using firstThree
    have reflectedHead :
        reflected.get ⟨0, by omega⟩ = second.get ⟨0, secondZeroBound⟩ := by
      dsimp only [reflected]
      rw [List.get_rotate]
      simpa only [Nat.zero_add, Nat.mod_eq_of_lt reverseOffsetBound] using reverseOffsetValue
    have reflectedHeadValue : reflected[0] = second[0] := reflectedHead
    have reflectedEdges : ∀ left right,
        IsNamedCycleEdge reflected left right ↔ IsNamedCycleEdge second left right := by
      intro left right
      exact (isNamedCycleEdge_iff_of_isRotated reverseToReflected reverseFirstNodup
        left right).symm.trans
        ((isNamedCycleEdge_reverse_iff first firstNodup left right).trans
          (sameEdges left right))
    have reflectedNext :
        reflected.next (reflected.get ⟨0, by omega⟩)
            (List.get_mem reflected ⟨0, by omega⟩) =
          aligned.prev (aligned.get ⟨0, by omega⟩)
            (List.get_mem aligned ⟨0, by omega⟩) := by
      calc
        reflected.next (reflected.get ⟨0, by omega⟩)
            (List.get_mem reflected ⟨0, by omega⟩) =
            first.reverse.next second[0]
              (List.mem_reverse.mpr secondHeadFirstMember) := by
                exact (next_congr_of_eq reflected reflectedHeadValue
                  (List.get_mem reflected ⟨0, by omega⟩)
                  (reverseToReflected.mem_iff.mp
                    (List.mem_reverse.mpr secondHeadFirstMember))).trans
                  (List.isRotated_next_eq reverseToReflected reverseFirstNodup
                    (List.mem_reverse.mpr secondHeadFirstMember)).symm
        _ = first.prev second[0] secondHeadFirstMember := by
              exact List.next_reverse_eq_prev first firstNodup second[0]
                secondHeadFirstMember
        _ = aligned.prev second[0] (firstToAligned.mem_iff.mp secondHeadFirstMember) :=
              List.isRotated_prev_eq firstToAligned firstNodup secondHeadFirstMember
        _ = aligned.prev (aligned.get ⟨0, by omega⟩)
              (List.get_mem aligned ⟨0, by omega⟩) := by
                exact prev_congr_of_eq aligned alignedHeadValue.symm
                  (firstToAligned.mem_iff.mp secondHeadFirstMember)
                  (List.get_mem aligned ⟨0, by omega⟩)
    have sameNext :
        reflected.next (reflected.get ⟨0, by omega⟩)
            (List.get_mem reflected ⟨0, by omega⟩) =
          second.next (second.get ⟨0, secondZeroBound⟩) secondHeadMember := by
      have reflectedDirection :
          reflected.next (reflected.get ⟨0, by omega⟩)
              (List.get_mem reflected ⟨0, by omega⟩) =
            second.get ⟨1, secondOneBound⟩ := by
        simpa only using reflectedNext.trans oppositeDirection
      exact reflectedDirection.trans secondNextAtHead.symm
    have equal := list_eq_of_same_head_next_and_named_edges reflectedThree reflectedLength
      reflectedNodup secondNodup reflectedHead sameNext
      (fun left right edge => (reflectedEdges left right).mpr edge)
    exact Or.inr (reverseToReflected.trans (equal ▸ List.IsRotated.refl second))

/-! ## Canonical representative and exhaustive scheduler -/

/-- The canonical ordered representative of a carrier is the least admitted traversal of the
same atom set in the ordinary linear order on finite natural-number lists.  Minimization occurs
over the explicit finite universe above, making the relation decidable and proof-transparent. -/
def CanonicalP94RingTraversal (molecule : RawMolecule) (atoms : List ℕ) : Prop :=
  IndependentP94RingTraversal molecule atoms ∧
    ∀ other ∈ boundedNodupTraversals molecule.atomCount,
      IndependentP94RingTraversal molecule other →
      other.toFinset = atoms.toFinset → atoms ≤ other

noncomputable instance canonicalP94RingTraversalDecidable
    (molecule : RawMolecule) (atoms : List ℕ) :
    Decidable (CanonicalP94RingTraversal molecule atoms) :=
  Classical.propDecidable _

noncomputable def canonicalP94RingTraversals
    (molecule : RawMolecule) : Finset (List ℕ) := by
  classical
  exact (boundedNodupTraversals molecule.atomCount).filter
    (CanonicalP94RingTraversal molecule)

@[simp] theorem mem_canonicalP94RingTraversals_iff
    (molecule : RawMolecule) (atoms : List ℕ) :
    atoms ∈ canonicalP94RingTraversals molecule ↔
      CanonicalP94RingTraversal molecule atoms := by
  classical
  constructor
  · intro present
    exact (Finset.mem_filter.mp present).2
  · intro canonical
    exact Finset.mem_filter.mpr
      ⟨independentP94RingTraversal_mem_bounded molecule atoms canonical.1, canonical⟩

/-- Every independently admitted traversal has a canonical representative with exactly the same
atom set.  This is the central finite-completeness step; it uses no graph-size bound. -/
theorem exists_canonicalP94RingTraversal_sameCarrier
    (molecule : RawMolecule) (atoms : List ℕ)
    (independent : IndependentP94RingTraversal molecule atoms) :
    ∃ canonical,
      canonical ∈ canonicalP94RingTraversals molecule ∧
      canonical.toFinset = atoms.toFinset := by
  classical
  let sameCarrierCandidates :=
    (boundedNodupTraversals molecule.atomCount).filter fun other =>
      IndependentP94RingTraversal molecule other ∧
        other.toFinset = atoms.toFinset
  have atomsPresent : atoms ∈ sameCarrierCandidates := by
    exact Finset.mem_filter.mpr
      ⟨independentP94RingTraversal_mem_bounded molecule atoms independent,
        independent, rfl⟩
  have candidatesNonempty : sameCarrierCandidates.Nonempty :=
    ⟨atoms, atomsPresent⟩
  let canonical := sameCarrierCandidates.min' candidatesNonempty
  have canonicalPresent : canonical ∈ sameCarrierCandidates :=
    sameCarrierCandidates.min'_mem candidatesNonempty
  have canonicalFacts := Finset.mem_filter.mp canonicalPresent
  refine ⟨canonical, (mem_canonicalP94RingTraversals_iff molecule canonical).mpr ?_,
    canonicalFacts.2.2⟩
  refine ⟨canonicalFacts.2.1, ?_⟩
  intro other otherBounded otherIndependent sameVertices
  apply sameCarrierCandidates.min'_le
  exact Finset.mem_filter.mpr
    ⟨otherBounded, otherIndependent, sameVertices.trans canonicalFacts.2.2⟩

/-- Canonical selection does not merely preserve the carrier's vertex set: the selected ordering
lies in the original ordering's actual dihedral orbit. -/
theorem exists_canonicalP94RingTraversal_dihedrallyRelated
    (molecule : RawMolecule) (atoms : List ℕ)
    (independent : IndependentP94RingTraversal molecule atoms) :
    ∃ canonical,
      canonical ∈ canonicalP94RingTraversals molecule ∧
      canonical.toFinset = atoms.toFinset ∧
      (atoms ~r canonical ∨ atoms.reverse ~r canonical) := by
  rcases exists_canonicalP94RingTraversal_sameCarrier molecule atoms independent with
    ⟨canonical, canonicalPresent, sameVertices⟩
  have canonicalIndependent :=
    ((mem_canonicalP94RingTraversals_iff molecule canonical).mp canonicalPresent).1
  exact ⟨canonical, canonicalPresent, sameVertices,
    independentP94RingTraversals_dihedrallyRelated molecule atoms canonical
      independent canonicalIndependent sameVertices.symm⟩

/-- There is at most one canonical traversal on a fixed carrier. -/
theorem canonicalP94RingTraversal_eq_of_sameCarrier
    (molecule : RawMolecule) (first second : List ℕ)
    (firstCanonical : CanonicalP94RingTraversal molecule first)
    (secondCanonical : CanonicalP94RingTraversal molecule second)
    (sameVertices : first.toFinset = second.toFinset) :
    first = second := by
  apply le_antisymm
  · exact firstCanonical.2 second
      (independentP94RingTraversal_mem_bounded molecule second secondCanonical.1)
      secondCanonical.1 sameVertices.symm
  · exact secondCanonical.2 first
      (independentP94RingTraversal_mem_bounded molecule first firstCanonical.1)
      firstCanonical.1 sameVertices

/-- The canonical traversal finset contains exactly one representative of the dihedral class of
every independently admitted traversal. -/
theorem existsUnique_canonicalP94RingTraversal_dihedralClass
    (molecule : RawMolecule) (atoms : List ℕ)
    (independent : IndependentP94RingTraversal molecule atoms) :
    ∃! canonical,
      canonical ∈ canonicalP94RingTraversals molecule ∧
      (atoms ~r canonical ∨ atoms.reverse ~r canonical) := by
  rcases exists_canonicalP94RingTraversal_dihedrallyRelated molecule atoms independent with
    ⟨canonical, canonicalPresent, _, related⟩
  refine ⟨canonical, ⟨canonicalPresent, related⟩, ?_⟩
  intro other otherFacts
  have canonicalJudged :=
    (mem_canonicalP94RingTraversals_iff molecule canonical).mp canonicalPresent
  have otherJudged :=
    (mem_canonicalP94RingTraversals_iff molecule other).mp otherFacts.1
  have sameVertices : canonical.toFinset = other.toFinset := by
    have canonicalPerm : atoms.Perm canonical := by
      rcases related with rotated | reversed
      · exact rotated.perm
      · exact atoms.reverse_perm.symm.trans reversed.perm
    have otherPerm : atoms.Perm other := by
      rcases otherFacts.2 with rotated | reversed
      · exact rotated.perm
      · exact atoms.reverse_perm.symm.trans reversed.perm
    exact List.toFinset_eq_of_perm _ _ (canonicalPerm.symm.trans otherPerm)
  exact (canonicalP94RingTraversal_eq_of_sameCarrier molecule canonical other
    canonicalJudged otherJudged sameVertices).symm

/-- The complete finite scheduler.  The outer `biUnion` ranges over canonical atom traversals; the
inner image creates every P-94 unit role supported by that traversal's length. -/
noncomputable def p94MolecularRingCycleScheduler
    (molecule : RawMolecule) : Finset P94ConformationUnit := by
  classical
  exact (canonicalP94RingTraversals molecule).biUnion fun atoms =>
    (p94ScheduledRingKinds.filter fun kind =>
      P94RingKindSupportsLength kind atoms.length).image fun kind =>
        { kind := kind, atoms := atoms }

/-- Exact scheduler membership, separating physical carrier semantics from the family role
assigned to that carrier. -/
theorem mem_p94MolecularRingCycleScheduler_iff
    (molecule : RawMolecule) (unit : P94ConformationUnit) :
    unit ∈ p94MolecularRingCycleScheduler molecule ↔
      unit.torsionParticipants? = none ∧
      unit.kind ∈ p94ScheduledRingKinds ∧
      P94RingKindSupportsLength unit.kind unit.atoms.length ∧
      CanonicalP94RingTraversal molecule unit.atoms := by
  classical
  constructor
  · intro present
    rcases Finset.mem_biUnion.mp present with
      ⟨atoms, atomsPresent, unitPresent⟩
    rcases Finset.mem_image.mp unitPresent with
      ⟨kind, kindPresent, unitIdentity⟩
    have kindFacts := Finset.mem_filter.mp kindPresent
    rw [← unitIdentity]
    exact ⟨rfl, kindFacts.1, kindFacts.2,
      (mem_canonicalP94RingTraversals_iff molecule atoms).mp atomsPresent⟩
  · rintro ⟨participantsNone, kindPresent, supported, canonical⟩
    apply Finset.mem_biUnion.mpr
    refine ⟨unit.atoms,
      (mem_canonicalP94RingTraversals_iff molecule unit.atoms).mpr canonical, ?_⟩
    apply Finset.mem_image.mpr
    refine ⟨unit.kind, Finset.mem_filter.mpr ⟨kindPresent, supported⟩, ?_⟩
    cases unit with
    | mk kind atoms participants =>
        simp only at participantsNone ⊢
        subst participants
        rfl

/-- The list view consumed by deterministic downstream schedulers contains no duplicate units. -/
theorem p94MolecularRingCycleScheduler_toList_nodup (molecule : RawMolecule) :
    (p94MolecularRingCycleScheduler molecule).toList.Nodup :=
  Finset.nodup_toList _

/-- Every scheduled unit satisfies the exact positive-bond closed-cycle validator. -/
theorem scheduler_member_cycleCarrier
    (molecule : RawMolecule) (unit : P94ConformationUnit)
    (present : unit ∈ p94MolecularRingCycleScheduler molecule) :
    unit.CycleCarrier molecule := by
  have independent :=
    ((mem_p94MolecularRingCycleScheduler_iff molecule unit).mp present).2.2.2.1
  change (traversalUnit unit.atoms).CycleCarrier molecule
  exact independent.2.2.2.2.1

/-- Every scheduled unit is already admissible to the existing molecule-bound P-94 pipeline. -/
theorem scheduler_member_validFor
    (molecule : RawMolecule) (unit : P94ConformationUnit)
    (present : unit ∈ p94MolecularRingCycleScheduler molecule) :
    unit.ValidFor molecule := by
  have scheduled := (mem_p94MolecularRingCycleScheduler_iff molecule unit).mp present
  have independent := scheduled.2.2.2.1
  rcases independent with
    ⟨atLeastThree, nodup, bounded, cyclicallyBonded, cycleCarrier, chordless⟩
  unfold P94ConformationUnit.ValidFor
  cases kindIdentity : unit.kind <;>
    simp_all [P94RingKindSupportsLength]

/-- The scheduler emits exactly the represented P-94 ring-size roles. -/
theorem scheduler_member_supported_length
    (molecule : RawMolecule) (unit : P94ConformationUnit)
    (present : unit ∈ p94MolecularRingCycleScheduler molecule) :
    P94RingKindSupportsLength unit.kind unit.atoms.length :=
  ((mem_p94MolecularRingCycleScheduler_iff molecule unit).mp present).2.2.1

/-- Canonicalization removes every duplicate having the same atom set and family role. -/
theorem scheduler_same_carrier_unique
    (molecule : RawMolecule) (first second : P94ConformationUnit)
    (firstPresent : first ∈ p94MolecularRingCycleScheduler molecule)
    (secondPresent : second ∈ p94MolecularRingCycleScheduler molecule)
    (sameKind : first.kind = second.kind)
    (sameVertices : first.atoms.toFinset = second.atoms.toFinset) :
    first = second := by
  have firstScheduled :=
    (mem_p94MolecularRingCycleScheduler_iff molecule first).mp firstPresent
  have secondScheduled :=
    (mem_p94MolecularRingCycleScheduler_iff molecule second).mp secondPresent
  have firstCanonical := firstScheduled.2.2.2
  have secondCanonical := secondScheduled.2.2.2
  have firstAtomsLe : first.atoms ≤ second.atoms :=
    firstCanonical.2 second.atoms
      (independentP94RingTraversal_mem_bounded molecule second.atoms secondCanonical.1)
      secondCanonical.1 sameVertices.symm
  have secondAtomsLe : second.atoms ≤ first.atoms :=
    secondCanonical.2 first.atoms
      (independentP94RingTraversal_mem_bounded molecule first.atoms firstCanonical.1)
      firstCanonical.1 sameVertices
  have sameAtoms : first.atoms = second.atoms := le_antisymm firstAtomsLe secondAtomsLe
  cases first with
  | mk firstKind firstAtoms firstParticipants =>
      cases second with
      | mk secondKind secondAtoms secondParticipants =>
          simp only at firstScheduled secondScheduled sameKind sameAtoms ⊢
          subst secondKind
          subst secondAtoms
          have firstNone : firstParticipants = none := firstScheduled.1
          have secondNone : secondParticipants = none := secondScheduled.1
          subst firstParticipants
          subst secondParticipants
          rfl

/-- In particular, rotations and reversals of one cyclic traversal cannot survive as distinct
scheduled units of the same kind. -/
theorem scheduler_rotation_reversal_unique
    (molecule : RawMolecule) (first second : P94ConformationUnit) (offset : ℕ)
    (firstPresent : first ∈ p94MolecularRingCycleScheduler molecule)
    (secondPresent : second ∈ p94MolecularRingCycleScheduler molecule)
    (sameKind : first.kind = second.kind)
    (dihedrallyRelated :
      second.atoms = first.atoms.rotate offset ∨
        second.atoms = first.atoms.reverse.rotate offset) :
    first = second := by
  apply scheduler_same_carrier_unique molecule first second
    firstPresent secondPresent sameKind
  rcases dihedrallyRelated with rotated | reversed
  · rw [rotated]
    exact List.toFinset_eq_of_perm _ _ (List.rotate_perm first.atoms offset).symm
  · rw [reversed]
    exact List.toFinset_eq_of_perm _ _
      ((List.rotate_perm first.atoms.reverse offset).trans
        (List.reverse_perm first.atoms)).symm

/-- For every admitted traversal and supported P-94 role, the scheduler contains exactly one unit
whose atom ordering belongs to that traversal's dihedral class. -/
theorem existsUnique_scheduler_unit_dihedralClass
    (molecule : RawMolecule) (atoms : List ℕ) (kind : P94ConformationUnitKind)
    (independent : IndependentP94RingTraversal molecule atoms)
    (supported : P94RingKindSupportsLength kind atoms.length) :
    ∃! unit,
      unit ∈ p94MolecularRingCycleScheduler molecule ∧
      unit.kind = kind ∧
      (atoms ~r unit.atoms ∨ atoms.reverse ~r unit.atoms) := by
  classical
  rcases exists_canonicalP94RingTraversal_dihedrallyRelated molecule atoms independent with
    ⟨canonical, canonicalPresent, sameVertices, related⟩
  have canonicalJudged :=
    (mem_canonicalP94RingTraversals_iff molecule canonical).mp canonicalPresent
  have canonicalLength : canonical.length = atoms.length := by
    rw [← List.toFinset_card_of_nodup canonicalJudged.1.2.1,
      ← List.toFinset_card_of_nodup independent.2.1, sameVertices]
  have canonicalSupported : P94RingKindSupportsLength kind canonical.length := by
    rwa [canonicalLength]
  let selected : P94ConformationUnit := { kind := kind, atoms := canonical }
  have selectedPresent : selected ∈ p94MolecularRingCycleScheduler molecule := by
    apply (mem_p94MolecularRingCycleScheduler_iff molecule selected).mpr
    exact ⟨rfl,
      kind_mem_p94ScheduledRingKinds_of_supportsLength kind canonical.length
        canonicalSupported,
      canonicalSupported, canonicalJudged⟩
  refine ⟨selected, ⟨selectedPresent, rfl, related⟩, ?_⟩
  intro other otherFacts
  symm
  apply scheduler_same_carrier_unique molecule selected other selectedPresent otherFacts.1
    otherFacts.2.1.symm
  have selectedPerm : atoms.Perm selected.atoms := by
    rcases related with rotated | reversed
    · exact rotated.perm
    · exact atoms.reverse_perm.symm.trans reversed.perm
  have otherPerm : atoms.Perm other.atoms := by
    rcases otherFacts.2.2 with rotated | reversed
    · exact rotated.perm
    · exact atoms.reverse_perm.symm.trans reversed.perm
  exact List.toFinset_eq_of_perm _ _ (selectedPerm.symm.trans otherPerm)

/-- End-to-end finite completeness of carrier scheduling.  The left side is an actual canonical
scheduled unit.  The right side is the ordering-independent chordless carrier judgment plus the
requested P-94 family role. -/
theorem scheduler_complete_iff_declarativeCarrier
    (molecule : RawMolecule) (vertices : Finset ℕ)
    (kind : P94ConformationUnitKind) :
    (∃ unit,
      unit ∈ p94MolecularRingCycleScheduler molecule ∧
      unit.kind = kind ∧ unit.atoms.toFinset = vertices) ↔
      P94RingKindSupportsLength kind vertices.card ∧
        DeclarativeP94RingCarrier molecule vertices := by
  classical
  constructor
  · rintro ⟨unit, present, kindIdentity, verticesIdentity⟩
    have scheduled := (mem_p94MolecularRingCycleScheduler_iff molecule unit).mp present
    have independent := scheduled.2.2.2.1
    have cardIdentity : vertices.card = unit.atoms.length := by
      rw [← verticesIdentity, List.toFinset_card_of_nodup independent.2.1]
    refine ⟨?_, unit.atoms, verticesIdentity, independent⟩
    rw [← kindIdentity, cardIdentity]
    exact scheduled.2.2.1
  · rintro ⟨supported, atoms, verticesIdentity, independent⟩
    rcases exists_canonicalP94RingTraversal_sameCarrier molecule atoms independent with
      ⟨canonical, canonicalPresent, canonicalVertices⟩
    have canonicalJudged :=
      (mem_canonicalP94RingTraversals_iff molecule canonical).mp canonicalPresent
    have canonicalVerticesIdentity : canonical.toFinset = vertices :=
      canonicalVertices.trans verticesIdentity
    have canonicalLengthIdentity : canonical.length = vertices.card := by
      rw [← canonicalVerticesIdentity,
        List.toFinset_card_of_nodup canonicalJudged.1.2.1]
    have canonicalSupported : P94RingKindSupportsLength kind canonical.length := by
      rw [canonicalLengthIdentity]
      exact supported
    let unit : P94ConformationUnit := { kind := kind, atoms := canonical }
    refine ⟨unit, ?_, rfl, canonicalVerticesIdentity⟩
    apply (mem_p94MolecularRingCycleScheduler_iff molecule unit).mpr
    exact ⟨rfl,
      kind_mem_p94ScheduledRingKinds_of_supportsLength kind canonical.length
        canonicalSupported,
      canonicalSupported, canonicalJudged⟩

/-! ## Interface to automatic coordinate-witness discovery -/

/-- Exact relationship between a scheduled molecular unit and one witness-free coordinate request.
Six-membered units intentionally create both the chair/boat request and the half-chair request;
the coordinate judgments decide which, if either, is supported. -/
def AutomaticCoordinateRingInputMatches
    (unit : P94ConformationUnit) : AutomaticCoordinateRingInput → Prop
  | .envelope inputUnit =>
      inputUnit = unit ∧ unit.kind = .fiveMemberedRing
  | .sixRing inputUnit =>
      inputUnit = unit ∧ unit.kind = .sixMemberedRing
  | .halfChair inputUnit =>
      inputUnit = unit ∧ unit.kind = .sixMemberedRing
  | .crown inputUnit =>
      inputUnit = unit ∧ unit.kind = .crownRing
  | .tub inputUnit =>
      inputUnit = unit ∧ unit.kind = .eightMemberedTubRing

instance automaticCoordinateRingInputMatchesDecidable
    (unit : P94ConformationUnit) (input : AutomaticCoordinateRingInput) :
    Decidable (AutomaticCoordinateRingInputMatches unit input) := by
  cases input <;> simp [AutomaticCoordinateRingInputMatches] <;> infer_instance

def automaticCoordinateRingInputsForUnit
    (unit : P94ConformationUnit) : Finset AutomaticCoordinateRingInput :=
  match unit.kind with
  | .fiveMemberedRing => { .envelope unit }
  | .sixMemberedRing => { .sixRing unit, .halfChair unit }
  | .crownRing => { .crown unit }
  | .eightMemberedTubRing => { .tub unit }
  | .wholeMoleculeConformation | .torsionAxis | .bicyclicBridge => ∅

@[simp] theorem mem_automaticCoordinateRingInputsForUnit_iff
    (unit : P94ConformationUnit) (input : AutomaticCoordinateRingInput) :
    input ∈ automaticCoordinateRingInputsForUnit unit ↔
      AutomaticCoordinateRingInputMatches unit input := by
  cases unitKind : unit.kind <;> cases input <;>
    simp_all [automaticCoordinateRingInputsForUnit,
      AutomaticCoordinateRingInputMatches]

/-- All witness-free coordinate requests generated without a caller-supplied ring traversal. -/
noncomputable def scheduledAutomaticCoordinateRingInputs
    (molecule : RawMolecule) : Finset AutomaticCoordinateRingInput := by
  classical
  exact (p94MolecularRingCycleScheduler molecule).biUnion
    automaticCoordinateRingInputsForUnit

theorem mem_scheduledAutomaticCoordinateRingInputs_iff
    (molecule : RawMolecule) (input : AutomaticCoordinateRingInput) :
    input ∈ scheduledAutomaticCoordinateRingInputs molecule ↔
      ∃ unit,
        unit ∈ p94MolecularRingCycleScheduler molecule ∧
        AutomaticCoordinateRingInputMatches unit input := by
  classical
  constructor
  · intro present
    rcases Finset.mem_biUnion.mp present with ⟨unit, unitPresent, inputPresent⟩
    exact ⟨unit, unitPresent,
      (mem_automaticCoordinateRingInputsForUnit_iff unit input).mp inputPresent⟩
  · rintro ⟨unit, unitPresent, matching⟩
    exact Finset.mem_biUnion.mpr
      ⟨unit, unitPresent,
        (mem_automaticCoordinateRingInputsForUnit_iff unit input).mpr matching⟩

theorem scheduledAutomaticCoordinateRingInputs_toList_nodup
    (molecule : RawMolecule) :
    (scheduledAutomaticCoordinateRingInputs molecule).toList.Nodup :=
  Finset.nodup_toList _

end P94MolecularRingCycleScheduler
end TetraStereo.OneCenter
