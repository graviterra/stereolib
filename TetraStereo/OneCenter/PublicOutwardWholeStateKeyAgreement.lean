import TetraStereo.OneCenter.PublicParametricRule45Availability
import TetraStereo.OneCenter.PublicParametricCompoundRule45Key
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-!
# Whole-state and restricted reads agree on public outward reroot branches

`PublicParametricCumulativeRule45Key` and `PublicParametricCompoundRule45Key` separate label
*reading* from key *construction* on the public `AuthoritativeChemicalInput` source-canonical
occurrence zipper.  Both modules already prove reader congruence: two total readers that agree on
every cursor reachable through the actual executable reroot edge build the same whole `Option`
key.  What was missing on the public source is the *read-support* fact that makes the two reads
agree in the first place: the restricted dependency read
`aromaticCanonicalDependencyLabel target view` is `none` at every cursor that is not strictly below
the target, while the unrestricted whole-state read
`AromaticCanonicalAuxiliaryState` is defined everywhere.

This module supplies that fact from the actual public occurrence geometry and composes it with the
existing parametric builders.  The only structural input is `AromaticCanonicalRerootCursorValid`
plus a strict-depth start, exactly as in the localized analogue
`LocalizedOutwardRerootDependencySupport` / `LocalizedOutwardWholeStateKeyAgreement`.

## Main results

* `aromaticCanonicalOutwardRerootCursor_edge` — from a path-valid cursor whose recorded incoming
  coordinate is strictly shallower, every emitted child extends the address by one slot, keeps the
  root, records the cursor occurrence as its incoming cut, is again path-valid, and is strictly
  deeper.  This is proved from the actual `aromaticCanonicalRerootChildren` membership, the actual
  cut filter `intendedAromaticCanonicalRerootChildFrames`, and the actual carrier adjacency, not
  from any assumed classification.
* `aromaticCanonicalOutwardRerootCursor_reachable` — the outward property is preserved along every
  reflexive-transitive path of the executable reroot edge.
* `aromaticCanonicalDependencyLabel_eq_wholeState_of_dependency` — for any cursor that is a strict
  depth dependency of `target`, the restricted read through
  `aromaticCanonicalDependencyView state target` is exactly the whole-state lookup
  `state cursor.occurrence`.
* `aromaticCanonicalWholeStateReader_eq_restrictedReader_of_outward_reachable` — the reader
  agreement consumed by the existing reachable-congruence theorems.
* `buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable` and
  `buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable` —
  exact equality of the *whole* `Option` key between the whole-state reader and the shipped
  restricted production builder, at every evaluation fuel, including the fail-closed `none`
  outcome.
* `..._wholeState_key_eq_of_outward_reachable` / `..._wholeState_rankedLabels_eq_of_outward_reachable`
  — successful builds return the same key (hence the same ranked labels and the same Rule-4b
  reference population).
* `aromaticCanonicalFinalOccurrence_outward_first` and the `..._of_finalOutward` endpoints — at a
  final center (address `[]`) every actual root ligand child is automatically strictly outward, so
  no parent-insulation or availability hypothesis is needed, and the equalities hold for every
  evaluation fuel.
* `exists_..._wholeState_at_twice_of_outward_reachable` — at the structural bound
  `2 * (carrierFuel + 1)` both the whole-state and the production builders return the *same*
  actual key, so the equality is not a vacuous `none = none` statement.

## Scope

Structural mathematics only.  The parent branch (the target-start cursor and anything reached by
moving back toward the root) is deliberately excluded: at the target the restricted read is `none`
while the whole-state read is `state target.occurrence`, so no parent-branch agreement is claimed.
No descriptor assignment, chemical correctness, solver or evaluation strategy is asserted.  Every
statement is about the exact existing builders and preserves their `Option`/fail-closed behaviour.
-/

/-! ## The public whole-state reader and the outward cursor predicate -/

/-- The unrestricted whole-state read on the public source-canonical reroot zipper: the state
lookup at the cursor occurrence, with no dependency restriction. -/
def aromaticCanonicalWholeStateReader
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (state : source.AromaticCanonicalAuxiliaryState fuel) :
    source.AromaticCanonicalRerootCursor fuel → Option AromaticCanonicalAuxiliaryLabel :=
  fun cursor => state cursor.occurrence

/-- A public reroot cursor reached by moving strictly outward from `target`: it is path-valid, is a
strict depth dependency of `target` (same root, strictly longer occurrence address), and records an
incoming coordinate of strictly smaller address length. -/
def AromaticCanonicalOutwardRerootCursor
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (target : source.AromaticCanonicalOccurrence fuel)
    (cursor : source.AromaticCanonicalRerootCursor fuel) : Prop :=
  source.AromaticCanonicalRerootCursorValid cursor ∧
    source.AromaticCanonicalDepthDependency cursor.occurrence target ∧
    ∃ previous : source.AromaticCanonicalOccurrence fuel,
      cursor.previous? = some previous ∧
        previous.1.address.length < cursor.occurrence.1.address.length

/-- The strict source occurrence dependency is transitive. -/
theorem aromaticCanonicalDepthDependency_trans
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    {first second third : source.AromaticCanonicalOccurrence fuel}
    (firstSecond : source.AromaticCanonicalDepthDependency first second)
    (secondThird : source.AromaticCanonicalDepthDependency second third) :
    source.AromaticCanonicalDepthDependency first third :=
  ⟨firstSecond.1.trans secondThird.1, lt_trans secondThird.2 firstSecond.2⟩

/-! ## One actual executable step moves strictly outward -/

/-- From a path-valid cursor reached from a strictly shallower incoming coordinate, every actual
executable child moves strictly outward: its address is the cursor address extended by one slot, it
keeps the cursor root, records the cursor occurrence as its incoming cut, and is path-valid.

The decisive fact is the actual cut: a parent-branch candidate would have address equal to
`cursor.address.dropLast`, which is exactly the recorded incoming address, and is therefore removed
by the production filter.  Duplicate terminal leaves are handled by the same argument: their
intended cut-neighbourhood is empty, so there is nothing to preserve. -/
theorem aromaticCanonicalOutwardRerootCursor_edge
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor child : source.AromaticCanonicalRerootCursor fuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor)
    (previous : source.AromaticCanonicalOccurrence fuel)
    (previousEq : cursor.previous? = some previous)
    (parentShorter : previous.1.address.length < cursor.occurrence.1.address.length)
    (edge : child ∈ source.aromaticCanonicalRerootChildren cursor) :
    child.occurrence.1.address.dropLast = cursor.occurrence.1.address ∧
      child.occurrence.1.address.length = cursor.occurrence.1.address.length + 1 ∧
      child.occurrence.1.root = cursor.occurrence.1.root ∧
      child.previous? = some cursor.occurrence ∧
      source.AromaticCanonicalRerootCursorValid child := by
  have derived : source.DeclarativeAromaticCanonicalRerootChildren cursor
      (source.aromaticCanonicalRerootChildren cursor) :=
    source.aromaticCanonicalRerootChildren_sound cursor
  have childIntended : child.occurrence.1 ∈
      source.intendedAromaticCanonicalRerootChildFrames cursor := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child, edge, rfl⟩
  have childNeighbor : child.occurrence.1 ∈
      source.aromaticCanonicalRerootNeighborFrames (fuel := fuel) cursor.occurrence.1 :=
    source.mem_aromaticCanonicalRerootNeighborFrames_of_mem_intended cursor
      child.occurrence.1 childIntended
  have childAdjacent : source.AromaticCanonicalCarrierTreeAdjacent
      child.occurrence.1 cursor.occurrence.1 :=
    (source.mem_aromaticCanonicalRerootNeighborFrames_iff
      cursor.occurrence.1 child.occurrence.1).mp childNeighbor |>.2
  have childRoot : child.occurrence.1.root = cursor.occurrence.1.root :=
    childAdjacent.1
  have cursorNeighbor : cursor.occurrence.1 ∈
      source.aromaticCanonicalRerootNeighborFrames (fuel := fuel) previous.1 := by
    unfold AromaticCanonicalRerootCursorValid at valid
    rw [previousEq] at valid
    change cursor.occurrence.1 ∈ source.aromaticCanonicalRerootNeighborFrames
      (fuel := fuel) previous.1 at valid
    exact valid
  have currentAdjacent : source.AromaticCanonicalCarrierTreeAdjacent
      cursor.occurrence.1 previous.1 :=
    (source.mem_aromaticCanonicalRerootNeighborFrames_iff previous.1
      cursor.occurrence.1).mp cursorNeighbor |>.2
  have currentOutward :
      previous.1.address.length + 1 = cursor.occurrence.1.address.length ∧
        previous.1.address = cursor.occurrence.1.address.dropLast := by
    rcases currentAdjacent with ⟨_sameRoot, currentAsParent | currentAsOutward⟩
    · have impossible : ¬ cursor.occurrence.1.address.length + 1 =
          previous.1.address.length := by omega
      exact (impossible currentAsParent.1).elim
    · exact currentAsOutward
  have childOutward :
      cursor.occurrence.1.address.length + 1 = child.occurrence.1.address.length ∧
        cursor.occurrence.1.address = child.occurrence.1.address.dropLast := by
    rcases childAdjacent with ⟨_sameRoot, childAsParent | childAsOutward⟩
    · have sameParentAddress : child.occurrence.1.address = previous.1.address :=
        childAsParent.2.trans currentOutward.2.symm
      exact (source.address_ne_previous_of_mem_aromaticCanonicalIntended cursor previous
        previousEq child.occurrence.1 childIntended sameParentAddress).elim
    · exact childAsOutward
  have childPrevious : child.previous? = some cursor.occurrence := derived.2 child edge
  have childValid : source.AromaticCanonicalRerootCursorValid child :=
    source.aromaticCanonicalRerootChild_valid cursor child
      (source.aromaticCanonicalRerootChildren cursor) derived edge
  exact ⟨childOutward.2.symm, childOutward.1.symm, childRoot, childPrevious, childValid⟩

/-- An outward executable step never returns to its incoming coordinate. -/
theorem aromaticCanonicalOutwardRerootCursor_edge_excludes_previous
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor child : source.AromaticCanonicalRerootCursor fuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor)
    (previous : source.AromaticCanonicalOccurrence fuel)
    (previousEq : cursor.previous? = some previous)
    (parentShorter : previous.1.address.length < cursor.occurrence.1.address.length)
    (edge : child ∈ source.aromaticCanonicalRerootChildren cursor) :
    child.occurrence.1.address ≠ previous.1.address := by
  have step := source.aromaticCanonicalOutwardRerootCursor_edge cursor child valid previous
    previousEq parentShorter edge
  have childLength : child.occurrence.1.address.length =
      cursor.occurrence.1.address.length + 1 := step.2.1
  have childLonger : cursor.occurrence.1.address.length <
      child.occurrence.1.address.length := by
    rw [childLength]
    exact Nat.lt_succ_self _
  have previousShorter : previous.1.address.length <
      child.occurrence.1.address.length :=
    lt_trans parentShorter childLonger
  intro sameAddress
  have sameLength : child.occurrence.1.address.length =
      previous.1.address.length := congrArg List.length sameAddress
  exact Nat.lt_irrefl previous.1.address.length (sameLength ▸ previousShorter)

/-- The outward property is preserved by one actual executable edge. -/
theorem aromaticCanonicalOutwardRerootCursor_edge_preserves
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (target : source.AromaticCanonicalOccurrence fuel)
    (cursor child : source.AromaticCanonicalRerootCursor fuel)
    (outward : source.AromaticCanonicalOutwardRerootCursor target cursor)
    (edge : source.aromaticCanonicalRerootEdge cursor child) :
    source.AromaticCanonicalOutwardRerootCursor target child := by
  rcases outward with ⟨valid, dependency, previous, previousEq, parentShorter⟩
  rcases source.aromaticCanonicalOutwardRerootCursor_edge cursor child valid previous
      previousEq parentShorter edge with
    ⟨_dropLast, lengthEq, rootEq, previousChild, childValid⟩
  have childIncomingShorter : cursor.occurrence.1.address.length <
      child.occurrence.1.address.length := by
    rw [lengthEq]
    exact Nat.lt_succ_self _
  have childDeeper : target.1.address.length < child.occurrence.1.address.length :=
    lt_trans dependency.2 childIncomingShorter
  exact ⟨childValid, ⟨rootEq.trans dependency.1, childDeeper⟩, cursor.occurrence,
    previousChild, childIncomingShorter⟩

/-- An actual first executable child of the target-start cursor that is strictly deeper than the
target is an outward cursor.  The strict-depth fact is supplied by the caller (or derived below
from the address-`[]` geometry); only cursor validity is derived from the executable expansion. -/
theorem aromaticCanonicalOutwardRerootCursor_first
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (target : source.AromaticCanonicalOccurrence fuel)
    (first : source.AromaticCanonicalRerootCursor fuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length) :
    source.AromaticCanonicalOutwardRerootCursor target first := by
  let start : source.AromaticCanonicalRerootCursor fuel :=
    { occurrence := target, previous? := none }
  have derived : source.DeclarativeAromaticCanonicalRerootChildren start
      (source.aromaticCanonicalRerootChildren start) :=
    source.aromaticCanonicalRerootChildren_sound start
  have firstValid : source.AromaticCanonicalRerootCursorValid first :=
    source.aromaticCanonicalRerootChild_valid start first
      (source.aromaticCanonicalRerootChildren start) derived firstChild
  have firstRoot : first.occurrence.1.root = target.1.root :=
    source.aromaticCanonicalRerootChildren_root_eq start first firstChild
  have firstPrevious : first.previous? = some target := by
    simpa [start] using derived.2 first firstChild
  exact ⟨firstValid, ⟨firstRoot, firstDeeper⟩, target, firstPrevious, firstDeeper⟩

/-- The outward property propagates along every reflexive-transitive path of the actual executable
reroot edge. -/
theorem aromaticCanonicalOutwardRerootCursor_reachable
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (target : source.AromaticCanonicalOccurrence fuel)
    (first child : source.AromaticCanonicalRerootCursor fuel)
    (firstOutward : source.AromaticCanonicalOutwardRerootCursor target first)
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child) :
    source.AromaticCanonicalOutwardRerootCursor target child := by
  induction reachable with
  | refl => exact firstOutward
  | tail _path step inductionHypothesis =>
      exact source.aromaticCanonicalOutwardRerootCursor_edge_preserves target _ _ inductionHypothesis step

/-- Every cursor reachable from an actual strictly-deeper first child of the target-start cursor is
a strict depth dependency of the target and is path-valid. -/
theorem aromaticCanonicalOutwardRerootCursor_dependency
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (target : source.AromaticCanonicalOccurrence fuel)
    (first child : source.AromaticCanonicalRerootCursor fuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child) :
    source.AromaticCanonicalDepthDependency child.occurrence target ∧
      source.AromaticCanonicalRerootCursorValid child := by
  have allOutward : source.AromaticCanonicalOutwardRerootCursor target child :=
    source.aromaticCanonicalOutwardRerootCursor_reachable target first child
      (source.aromaticCanonicalOutwardRerootCursor_first target first firstChild firstDeeper)
      reachable
  exact ⟨allOutward.2.1, allOutward.1⟩

/-! ## Restricted reads equal whole-state reads on strict dependencies -/

/-- Reading a cursor that is already a strict dependency of the target through the restricted
dependency view returns the unrestricted whole-state label.  No read-support predicate is
assumed. -/
theorem aromaticCanonicalDependencyLabel_eq_wholeState_of_dependency
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (target : source.AromaticCanonicalOccurrence fuel)
    (state : source.AromaticCanonicalAuxiliaryState fuel)
    (cursor : source.AromaticCanonicalRerootCursor fuel)
    (dependency : source.AromaticCanonicalDepthDependency cursor.occurrence target) :
    source.aromaticCanonicalDependencyLabel target
      (source.aromaticCanonicalDependencyView state target) cursor =
      state cursor.occurrence := by
  unfold aromaticCanonicalDependencyLabel
  rw [dif_pos dependency]
  rfl

/-- Restricted and unrestricted reads agree throughout the whole outward subtree below an actual
strictly-deeper first child of the target. -/
theorem aromaticCanonicalOutwardRerootCursor_dependencyLabel_eq_state
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (target : source.AromaticCanonicalOccurrence fuel)
    (state : source.AromaticCanonicalAuxiliaryState fuel)
    (first child : source.AromaticCanonicalRerootCursor fuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child) :
    source.aromaticCanonicalDependencyLabel target
      (source.aromaticCanonicalDependencyView state target) child =
      state child.occurrence := by
  have facts := source.aromaticCanonicalOutwardRerootCursor_dependency target first child
    firstChild firstDeeper reachable
  exact source.aromaticCanonicalDependencyLabel_eq_wholeState_of_dependency
    target state child facts.1

/-- The reader agreement consumed by the existing reachable-congruence theorems: on an outward
branch the whole-state reader and the restricted dependency reader agree at every cursor reachable
from the branch point. -/
theorem aromaticCanonicalWholeStateReader_eq_restrictedReader_of_outward_reachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (first child : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child) :
    source.AromaticCanonicalRerootReadersAgreeOnReachable
      (source.aromaticCanonicalWholeStateReader state)
      (fun cursor => source.aromaticCanonicalDependencyLabel target
        (source.aromaticCanonicalDependencyView state target) cursor)
      child := by
  intro cursor cursorReach
  have facts := source.aromaticCanonicalOutwardRerootCursor_dependency target first cursor
    firstChild firstDeeper (reachable.trans cursorReach)
  exact (source.aromaticCanonicalDependencyLabel_eq_wholeState_of_dependency
    target state cursor facts.1).symm

/-! ## Explicit child classification on the public cut-neighbourhood -/

/-- Every actual executable child of a cursor with a recorded incoming coordinate is either an
outward child whose address extends the cursor address by one slot and whose `dropLast` is the
cursor address, or is the parent coordinate at `cursor.address.dropLast`, whose address the
production cut forces to differ from the recorded incoming coordinate.  This is the raw
`single parent + outward` dichotomy behind the outward exclusion; no validity or depth hypothesis
is needed for it. -/
theorem aromaticCanonicalRerootChild_outward_or_parentCoordinate
    (source : AuthoritativeChemicalInput) {fuel : Nat}
    (cursor child : source.AromaticCanonicalRerootCursor fuel)
    (previous : source.AromaticCanonicalOccurrence fuel)
    (previousEq : cursor.previous? = some previous)
    (edge : child ∈ source.aromaticCanonicalRerootChildren cursor) :
    (child.occurrence.1.address.dropLast = cursor.occurrence.1.address ∧
        child.occurrence.1.address.length = cursor.occurrence.1.address.length + 1) ∨
      (child.occurrence.1.address.length + 1 = cursor.occurrence.1.address.length ∧
        child.occurrence.1.address = cursor.occurrence.1.address.dropLast ∧
        child.occurrence.1.address ≠ previous.1.address) := by
  have derived : source.DeclarativeAromaticCanonicalRerootChildren cursor
      (source.aromaticCanonicalRerootChildren cursor) :=
    source.aromaticCanonicalRerootChildren_sound cursor
  have childIntended : child.occurrence.1 ∈
      source.intendedAromaticCanonicalRerootChildFrames cursor := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child, edge, rfl⟩
  have childNeighbor : child.occurrence.1 ∈
      source.aromaticCanonicalRerootNeighborFrames (fuel := fuel) cursor.occurrence.1 :=
    source.mem_aromaticCanonicalRerootNeighborFrames_of_mem_intended cursor
      child.occurrence.1 childIntended
  have childAdjacent : source.AromaticCanonicalCarrierTreeAdjacent
      child.occurrence.1 cursor.occurrence.1 :=
    (source.mem_aromaticCanonicalRerootNeighborFrames_iff
      cursor.occurrence.1 child.occurrence.1).mp childNeighbor |>.2
  rcases childAdjacent with ⟨_sameRoot, childAsParent | childAsOutward⟩
  · refine Or.inr ⟨childAsParent.1, childAsParent.2, ?_⟩
    exact source.address_ne_previous_of_mem_aromaticCanonicalIntended cursor previous
      previousEq child.occurrence.1 childIntended
  · exact Or.inl ⟨childAsOutward.2.symm, childAsOutward.1.symm⟩

/-! ## Whole-state versus production cumulative keys -/

/-- **Cumulative whole-state agreement.**  On an outward branch the whole-state parametric build
equals the shipped restricted production builder at every stage and every evaluation fuel.  The
equality is of the whole `Option` key, so the fail-closed `none` outcome is equal too; no
comparison ordering is used and no key equality is assumed. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (first child : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child) :
    ∀ fuel : Nat,
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage
        (source.aromaticCanonicalWholeStateReader state) fuel child =
      source.buildAromaticCanonicalCumulativeRule45Key? stage target
        (source.aromaticCanonicalDependencyView state target) fuel child := by
  intro fuel
  calc
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage
        (source.aromaticCanonicalWholeStateReader state) fuel child =
        source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage
          (fun cursor => source.aromaticCanonicalDependencyLabel target
            (source.aromaticCanonicalDependencyView state target) cursor) fuel child :=
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_congr_of_reachable
        stage (source.aromaticCanonicalWholeStateReader state)
        (fun cursor => source.aromaticCanonicalDependencyLabel target
          (source.aromaticCanonicalDependencyView state target) cursor)
        child
        (source.aromaticCanonicalWholeStateReader_eq_restrictedReader_of_outward_reachable
          target state first child firstChild firstDeeper reachable)
        fuel child Relation.ReflTransGen.refl
    _ = source.buildAromaticCanonicalCumulativeRule45Key? stage target
          (source.aromaticCanonicalDependencyView state target) fuel child :=
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
        stage target (source.aromaticCanonicalDependencyView state target) fuel child

/-- Successful whole-state and shipped cumulative compilations on an outward branch yield the
*same* key, not merely comparable projections. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_key_eq_of_outward_reachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (first child : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child)
    (fuel : Nat)
    (wholeKey shippedKey : source.AromaticCanonicalCumulativeRule45Key)
    (wholeComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage
      (source.aromaticCanonicalWholeStateReader state) fuel child = some wholeKey)
    (shippedComputed : source.buildAromaticCanonicalCumulativeRule45Key? stage target
      (source.aromaticCanonicalDependencyView state target) fuel child = some shippedKey) :
    wholeKey = shippedKey := by
  have total :=
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
      stage target state first child firstChild firstDeeper reachable fuel
  rw [wholeComputed, shippedComputed] at total
  exact Option.some.inj total

/-- On an outward branch the whole-state ranked labels are exactly the shipped ranked labels, so
the Rule-4b reference population is exactly the shipped one. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_rankedLabels_eq_of_outward_reachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (first child : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child)
    (fuel : Nat)
    (wholeKey shippedKey : source.AromaticCanonicalCumulativeRule45Key)
    (wholeComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage
      (source.aromaticCanonicalWholeStateReader state) fuel child = some wholeKey)
    (shippedComputed : source.buildAromaticCanonicalCumulativeRule45Key? stage target
      (source.aromaticCanonicalDependencyView state target) fuel child = some shippedKey) :
    wholeKey.rankedLabels = shippedKey.rankedLabels := by
  have keyEq :=
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_key_eq_of_outward_reachable
      stage target state first child firstChild firstDeeper reachable fuel
      wholeKey shippedKey wholeComputed shippedComputed
  subst shippedKey
  rfl

/-! ## Whole-state versus production compound Rules-4b/4c/5 keys -/

/-- **Compound whole-state agreement.**  On an outward branch the whole-state parametric compound
through-Rule-5 build equals the shipped restricted production builder at every evaluation fuel.
The equality is of the whole `Option` key, so the fail-closed `none` outcome is covered. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (first child : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child) :
    ∀ fuel : Nat,
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        (source.aromaticCanonicalWholeStateReader state) fuel child =
      source.buildAromaticCanonicalRerootCompoundRule45Key? target
        (source.aromaticCanonicalDependencyView state target) fuel child := by
  intro fuel
  calc
    source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        (source.aromaticCanonicalWholeStateReader state) fuel child =
        source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
          (fun cursor => source.aromaticCanonicalDependencyLabel target
            (source.aromaticCanonicalDependencyView state target) cursor) fuel child :=
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_congr_of_readersAgreeOnReachable
        (source.aromaticCanonicalWholeStateReader state)
        (fun cursor => source.aromaticCanonicalDependencyLabel target
          (source.aromaticCanonicalDependencyView state target) cursor)
        child
        (source.aromaticCanonicalWholeStateReader_eq_restrictedReader_of_outward_reachable
          target state first child firstChild firstDeeper reachable)
        fuel child Relation.ReflTransGen.refl
    _ = source.buildAromaticCanonicalRerootCompoundRule45Key? target
          (source.aromaticCanonicalDependencyView state target) fuel child :=
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_eq_aromaticCanonicalDependencyLabel
        target (source.aromaticCanonicalDependencyView state target) fuel child

/-- Successful whole-state and shipped compound builds on an outward branch yield the same key. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_key_eq_of_outward_reachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (first child : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child)
    (fuel : Nat)
    (wholeKey shippedKey : source.AromaticCanonicalRerootCompoundRule45Key)
    (wholeComputed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      (source.aromaticCanonicalWholeStateReader state) fuel child = some wholeKey)
    (shippedComputed : source.buildAromaticCanonicalRerootCompoundRule45Key? target
      (source.aromaticCanonicalDependencyView state target) fuel child = some shippedKey) :
    wholeKey = shippedKey := by
  have total :=
    source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable
      target state first child firstChild firstDeeper reachable fuel
  rw [wholeComputed, shippedComputed] at total
  exact Option.some.inj total

/-! ## Both sides actually succeed at the structural fuel bound -/

/-- At the structural bound `2 * (carrierFuel + 1)` the whole-state and the shipped cumulative
builders return the *same actual key* on an outward branch.  This rules out a vacuous
`none = none` reading of the equality above. -/
theorem exists_buildAromaticCanonicalCumulativeRule45Key?_wholeState_at_twice_of_outward_reachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (first child : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child) :
    ∃ key,
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage
          (source.aromaticCanonicalWholeStateReader state)
          (2 * (carrierFuel + 1)) child = some key ∧
        source.buildAromaticCanonicalCumulativeRule45Key? stage target
          (source.aromaticCanonicalDependencyView state target)
          (2 * (carrierFuel + 1)) child = some key := by
  have valid := (source.aromaticCanonicalOutwardRerootCursor_dependency target first child
    firstChild firstDeeper reachable).2
  obtain ⟨key, wholeComputed⟩ :=
    source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
      stage (source.aromaticCanonicalWholeStateReader state) child valid
  refine ⟨key, wholeComputed, ?_⟩
  rw [← source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
    stage target state first child firstChild firstDeeper reachable]
  exact wholeComputed

/-- At the structural bound `2 * (carrierFuel + 1)` the whole-state and the shipped compound
through-Rule-5 builders return the *same actual key* on an outward branch. -/
theorem exists_buildAromaticCanonicalRerootCompoundRule45Key?_wholeState_at_twice_of_outward_reachable
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (first child : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child) :
    ∃ key,
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
          (source.aromaticCanonicalWholeStateReader state)
          (2 * (carrierFuel + 1)) child = some key ∧
        source.buildAromaticCanonicalRerootCompoundRule45Key? target
          (source.aromaticCanonicalDependencyView state target)
          (2 * (carrierFuel + 1)) child = some key := by
  have valid := (source.aromaticCanonicalOutwardRerootCursor_dependency target first child
    firstChild firstDeeper reachable).2
  obtain ⟨key, wholeComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_at_twice
      (source.aromaticCanonicalWholeStateReader state) child valid
  refine ⟨key, wholeComputed, ?_⟩
  rw [← source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable
    target state first child firstChild firstDeeper reachable]
  exact wholeComputed

/-! ## Final-root four-ligand frames: every actual ligand child is outward -/

/-- Every actual child of the final occurrence's start cursor is exactly an official direct-child
frame at a fresh root slot: its root is the center atom and its address is `[slot]` for a slot in
the official source-canonical child enumeration.  This is the concrete four-ligand frame
decomposition that siblings need; no cardinality or chemistry-specific slot count is asserted. -/
theorem aromaticCanonicalFinalOccurrence_child_eq_slot_frame
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (first : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := source.aromaticCanonicalFinalOccurrence carrierFuel center,
        previous? := none }) :
    ∃ child slot,
      (child, slot) ∈
          (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
            source.molecule.atomCount (OfficialCIPNode.root center.1)).zipIdx ∧
        first.occurrence.1 =
          { root := center.1
            address := [slot]
            node := child
            remaining := carrierFuel } := by
  have derived : source.DeclarativeAromaticCanonicalRerootChildren
      { occurrence := source.aromaticCanonicalFinalOccurrence carrierFuel center,
        previous? := none }
      (source.aromaticCanonicalRerootChildren
        { occurrence := source.aromaticCanonicalFinalOccurrence carrierFuel center,
          previous? := none }) :=
    source.aromaticCanonicalRerootChildren_sound _
  have intended : first.occurrence.1 ∈
      source.intendedAromaticCanonicalRerootChildFrames
        { occurrence := source.aromaticCanonicalFinalOccurrence carrierFuel center,
          previous? := none } := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨first, firstChild, rfl⟩
  rw [aromaticCanonicalFinalOccurrence_intendedChildren_eq_outward
    source carrierFuel center] at intended
  exact (mem_aromaticCanonicalCarrierOutwardChildFrames_final_iff
    source carrierFuel center first.occurrence.1).mp intended

/-- At a final center the target occurrence has address `[]`, so the parent coordinate cannot be
reached: every actual child of the target-start cursor extends the address to length one.  Hence
every actual ligand child is automatically strictly outward, with the target itself as its
recorded incoming coordinate. -/
theorem aromaticCanonicalFinalOccurrence_outward_first
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (first : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := source.aromaticCanonicalFinalOccurrence carrierFuel center,
        previous? := none }) :
    source.AromaticCanonicalOutwardRerootCursor
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) first := by
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let start : source.AromaticCanonicalRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  have derived : source.DeclarativeAromaticCanonicalRerootChildren start
      (source.aromaticCanonicalRerootChildren start) :=
    source.aromaticCanonicalRerootChildren_sound start
  have firstIntended : first.occurrence.1 ∈
      source.intendedAromaticCanonicalRerootChildFrames start := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨first, firstChild, rfl⟩
  have firstNeighbor : first.occurrence.1 ∈
      source.aromaticCanonicalRerootNeighborFrames (fuel := carrierFuel) start.occurrence.1 :=
    source.mem_aromaticCanonicalRerootNeighborFrames_of_mem_intended start
      first.occurrence.1 firstIntended
  have firstAdjacent : source.AromaticCanonicalCarrierTreeAdjacent
      first.occurrence.1 start.occurrence.1 :=
    (source.mem_aromaticCanonicalRerootNeighborFrames_iff
      start.occurrence.1 first.occurrence.1).mp firstNeighbor |>.2
  have targetAddress : target.1.address = [] := rfl
  have firstLength : first.occurrence.1.address.length = 1 := by
    rcases firstAdjacent.2 with asParent | asOutward
    · rw [targetAddress, List.length_nil] at asParent
      exact (Nat.succ_ne_zero _ asParent.1).elim
    · rw [targetAddress, List.length_nil] at asOutward
      simpa using asOutward.1.symm
  have firstRoot : first.occurrence.1.root = target.1.root := by
    have := firstAdjacent.1
    simpa [start] using this
  have firstDeeper : target.1.address.length < first.occurrence.1.address.length := by
    rw [targetAddress, List.length_nil, firstLength]
    exact Nat.zero_lt_one
  have firstValid : source.AromaticCanonicalRerootCursorValid first :=
    source.aromaticCanonicalRerootChild_valid start first
      (source.aromaticCanonicalRerootChildren start) derived firstChild
  have firstPrevious : first.previous? = some target := by
    simpa [start] using derived.2 first firstChild
  exact ⟨firstValid, ⟨firstRoot, firstDeeper⟩, target, firstPrevious, firstDeeper⟩

/-- **Final-root cumulative whole-state equality.**  For an actual-root ligand child of the final
occurrence frame there is no parent branch at all, so the whole-state and production cumulative
builders agree exactly at every evaluation fuel with no further hypothesis. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_eq_of_finalOutward
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (stage : LocalizedCumulativeRule45Stage)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (first child : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := source.aromaticCanonicalFinalOccurrence carrierFuel center,
        previous? := none })
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child) :
    ∀ fuel : Nat,
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage
        (source.aromaticCanonicalWholeStateReader state) fuel child =
      source.buildAromaticCanonicalCumulativeRule45Key? stage
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        (source.aromaticCanonicalDependencyView state
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)) fuel child :=
  fun fuel =>
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
      stage (source.aromaticCanonicalFinalOccurrence carrierFuel center) state first child
      firstChild
      (source.aromaticCanonicalFinalOccurrence_outward_first center first firstChild).2.1.2
      reachable fuel

/-- **Final-root compound whole-state equality.**  For an actual-root ligand child of the final
occurrence frame the whole-state and production compound through-Rule-5 builders agree exactly at
every evaluation fuel with no further hypothesis. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_of_finalOutward
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (first child : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := source.aromaticCanonicalFinalOccurrence carrierFuel center,
        previous? := none })
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child) :
    ∀ fuel : Nat,
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        (source.aromaticCanonicalWholeStateReader state) fuel child =
      source.buildAromaticCanonicalRerootCompoundRule45Key?
        (source.aromaticCanonicalFinalOccurrence carrierFuel center)
        (source.aromaticCanonicalDependencyView state
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)) fuel child :=
  fun fuel =>
    source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) state first child firstChild
      (source.aromaticCanonicalFinalOccurrence_outward_first center first firstChild).2.1.2
      reachable fuel

/-- At the structural bound the final-root cumulative whole-state and production builders return
the same actual key for every actual ligand child, with no hypothesis beyond membership in the
final occurrence frame's actual children. -/
theorem exists_buildAromaticCanonicalCumulativeRule45Key?_wholeState_at_twice_of_finalOutward
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (stage : LocalizedCumulativeRule45Stage)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (first child : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := source.aromaticCanonicalFinalOccurrence carrierFuel center,
        previous? := none })
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child) :
    ∃ key,
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead? stage
          (source.aromaticCanonicalWholeStateReader state)
          (2 * (carrierFuel + 1)) child = some key ∧
        source.buildAromaticCanonicalCumulativeRule45Key? stage
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)
          (source.aromaticCanonicalDependencyView state
            (source.aromaticCanonicalFinalOccurrence carrierFuel center))
          (2 * (carrierFuel + 1)) child = some key :=
  source.exists_buildAromaticCanonicalCumulativeRule45Key?_wholeState_at_twice_of_outward_reachable
    stage (source.aromaticCanonicalFinalOccurrence carrierFuel center) state first child
    firstChild
    (source.aromaticCanonicalFinalOccurrence_outward_first center first firstChild).2.1.2
    reachable

/-- At the structural bound the final-root compound whole-state and production builders return the
same actual key for every actual ligand child. -/
theorem exists_buildAromaticCanonicalRerootCompoundRule45Key?_wholeState_at_twice_of_finalOutward
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalTetrahedralCenter)
    (state : source.AromaticCanonicalAuxiliaryState carrierFuel)
    (first child : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstChild : first ∈ source.aromaticCanonicalRerootChildren
      { occurrence := source.aromaticCanonicalFinalOccurrence carrierFuel center,
        previous? := none })
    (reachable : Relation.ReflTransGen (aromaticCanonicalRerootEdge source) first child) :
    ∃ key,
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
          (source.aromaticCanonicalWholeStateReader state)
          (2 * (carrierFuel + 1)) child = some key ∧
        source.buildAromaticCanonicalRerootCompoundRule45Key?
          (source.aromaticCanonicalFinalOccurrence carrierFuel center)
          (source.aromaticCanonicalDependencyView state
            (source.aromaticCanonicalFinalOccurrence carrierFuel center))
          (2 * (carrierFuel + 1)) child = some key :=
  source.exists_buildAromaticCanonicalRerootCompoundRule45Key?_wholeState_at_twice_of_outward_reachable
    (source.aromaticCanonicalFinalOccurrence carrierFuel center) state first child firstChild
    (source.aromaticCanonicalFinalOccurrence_outward_first center first firstChild).2.1.2
    reachable

end AuthoritativeChemicalInput
end TetraStereo.OneCenter

/-! ## Kernel-authority guards

Every exported declaration is guarded.  `assert_kernel_only` permits exactly `propext`,
`Classical.choice` and `Quot.sound`; it rejects `sorryAx`, project axioms and native/compiler
trust. -/

assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalWholeStateReader
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.AromaticCanonicalOutwardRerootCursor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalDepthDependency_trans
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOutwardRerootCursor_edge
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOutwardRerootCursor_edge_excludes_previous
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOutwardRerootCursor_edge_preserves
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOutwardRerootCursor_first
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOutwardRerootCursor_reachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOutwardRerootCursor_dependency
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalDependencyLabel_eq_wholeState_of_dependency
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalOutwardRerootCursor_dependencyLabel_eq_state
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalWholeStateReader_eq_restrictedReader_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRerootChild_outward_or_parentCoordinate
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_key_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_rankedLabels_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_key_eq_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalCumulativeRule45Key?_wholeState_at_twice_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalRerootCompoundRule45Key?_wholeState_at_twice_of_outward_reachable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalFinalOccurrence_child_eq_slot_frame
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalFinalOccurrence_outward_first
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_wholeState_eq_of_finalOutward
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_wholeState_eq_of_finalOutward
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalCumulativeRule45Key?_wholeState_at_twice_of_finalOutward
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalRerootCompoundRule45Key?_wholeState_at_twice_of_finalOutward
