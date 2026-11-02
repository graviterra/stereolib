import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Outward reroot dependency support

Once a localized reroot cursor is reached by moving strictly outward from its descriptor target,
every later executable step stays strictly outward.  This module proves that structural invariant
for the *total* executable edge from `LocalizedRerootChildrenExecutable` and derives its two
downstream consequences without assuming any read-support predicate:

* every cursor reachable from an actual strictly-deeper first child of the target-start cursor is
  a `LocalizedDepthDependency` of the target and is path-valid, so the restricted dependency read
  `localizedDependencyLabel target (localizedDependencyView s target) cursor` equals the
  unrestricted whole-state read `s cursor.occurrence`;
* every such cursor admits an eager compound Rules-4/5 key at the proved twice-depth bound, via the
  existing `exists_buildLocalizedRerootCompoundRule45Key?_at_twice`.

The decisive geometric fact is that an outward-arriving cursor cuts only its parent coordinate:
the incoming cut is excluded by `address_ne_previous_of_mem_intended`, and `LocalizedCarrierTreeAdjacent`
then leaves only the strictly longer outward children.  Duplicate terminal leaves are included
naturally, because a duplicate node has an empty intended cut-neighborhood and is therefore a
terminal of the edge relation.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-- The helper reroot edge `E c d`: `d` is an executable child of `c` in the total cut-neighborhood
expansion.  No membership test is performed; the edge is the plain list membership in
`executableLocalizedRerootChildren`. -/
def E (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel) : Prop :=
  child ∈ input.executableLocalizedRerootChildren cursor

/-- A cursor reached by moving strictly outward from `target`: it is path-valid, is a strict
depth dependency of `target`, and records an incoming coordinate of strictly smaller address
length. -/
def OutwardRerootCursor
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (cursor : input.LocalizedRerootCursor fuel) : Prop :=
  input.LocalizedRerootCursorValid cursor ∧
    input.LocalizedDepthDependency cursor.occurrence target ∧
    ∃ previous : input.LocalizedCIPOccurrence fuel,
      cursor.previous? = some previous ∧
        previous.1.address.length < cursor.occurrence.1.address.length

/-- From a path-valid cursor reached from a strictly shallower incoming coordinate, every
executable child moves strictly outward: its address is the cursor address extended by one slot,
it keeps the cursor root, records the cursor occurrence as its incoming cut, and is path-valid. -/
theorem outward_edge
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : input.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some previous)
    (parentShorter : previous.1.address.length < cursor.occurrence.1.address.length)
    (edge : E input cursor child) :
    child.occurrence.1.address.dropLast = cursor.occurrence.1.address ∧
      child.occurrence.1.address.length = cursor.occurrence.1.address.length + 1 ∧
      child.occurrence.1.root = cursor.occurrence.1.root ∧
      child.previous? = some cursor.occurrence ∧
      input.LocalizedRerootCursorValid child := by
  have derived : input.DeclarativeLocalizedRerootChildren cursor
      (input.executableLocalizedRerootChildren cursor) :=
    input.executableLocalizedRerootChildren_declarative cursor
  have childIntended : child.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames cursor := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨child, edge, rfl⟩
  have childNeighbor : child.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := fuel) cursor.occurrence.1 :=
    input.mem_localizedRerootNeighborFrames_of_mem_intended cursor child.occurrence.1 childIntended
  have childAdjacent : input.LocalizedCarrierTreeAdjacent
      child.occurrence.1 cursor.occurrence.1 :=
    (input.mem_localizedRerootNeighborFrames_iff
      cursor.occurrence.1 child.occurrence.1).mp childNeighbor |>.2
  have childRoot : child.occurrence.1.root = cursor.occurrence.1.root :=
    childAdjacent.1
  have cursorNeighbor : cursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := fuel) previous.1 := by
    unfold LocalizedRerootCursorValid at valid
    rw [previousEq] at valid
    change cursor.occurrence.1 ∈ input.localizedRerootNeighborFrames
      (fuel := fuel) previous.1 at valid
    exact valid
  have currentAdjacent : input.LocalizedCarrierTreeAdjacent
      cursor.occurrence.1 previous.1 :=
    (input.mem_localizedRerootNeighborFrames_iff previous.1 cursor.occurrence.1).mp
      cursorNeighbor |>.2
  have currentOutward :
      previous.1.address.length + 1 = cursor.occurrence.1.address.length ∧
        previous.1.address = cursor.occurrence.1.address.dropLast := by
    rcases currentAdjacent with ⟨_sameRoot, currentAsParent | currentAsOutward⟩
    · have notCurrentAsParent : ¬
          cursor.occurrence.1.address.length + 1 = previous.1.address.length := by omega
      exact (notCurrentAsParent currentAsParent.1).elim
    · exact currentAsOutward
  have childOutward :
      cursor.occurrence.1.address.length + 1 = child.occurrence.1.address.length ∧
        cursor.occurrence.1.address = child.occurrence.1.address.dropLast := by
    rcases childAdjacent with ⟨_sameRoot, childAsParent | childAsOutward⟩
    · have sameParentAddress : child.occurrence.1.address = previous.1.address :=
        childAsParent.2.trans currentOutward.2.symm
      exact (input.address_ne_previous_of_mem_intended cursor previous previousEq
        child.occurrence.1 childIntended sameParentAddress).elim
    · exact childAsOutward
  have childPrevious : child.previous? = some cursor.occurrence :=
    derived.2 child edge
  have childValid : input.LocalizedRerootCursorValid child :=
    input.localizedRerootChild_valid cursor child
      (input.executableLocalizedRerootChildren cursor) derived edge
  exact ⟨childOutward.2.symm, childOutward.1.symm, childRoot, childPrevious, childValid⟩

/-- An outward executable step never returns to its incoming coordinate.  The child address is
strictly longer than the excluded parent address, so the cut parent is genuinely left behind. -/
theorem outward_edge_excludes_previous
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (valid : input.LocalizedRerootCursorValid cursor)
    (previous : input.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some previous)
    (parentShorter : previous.1.address.length < cursor.occurrence.1.address.length)
    (edge : E input cursor child) :
    child.occurrence.1.address ≠ previous.1.address := by
  have step := outward_edge input cursor child valid previous previousEq parentShorter edge
  have childLength : child.occurrence.1.address.length =
      cursor.occurrence.1.address.length + 1 := step.2.1
  intro sameAddress
  have sameLength : child.occurrence.1.address.length =
      previous.1.address.length := congrArg List.length sameAddress
  omega

/-- The outward property is preserved by one executable edge. -/
theorem outward_edge_preserves
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (cursor child : input.LocalizedRerootCursor fuel)
    (outward : OutwardRerootCursor input target cursor)
    (edge : E input cursor child) :
    OutwardRerootCursor input target child := by
  rcases outward with ⟨valid, dependency, previous, previousEq, parentShorter⟩
  rcases outward_edge input cursor child valid previous previousEq parentShorter edge with
    ⟨_dropLast, lengthEq, rootEq, previousChild, childValid⟩
  refine ⟨childValid, ?_, cursor.occurrence, previousChild, ?_⟩
  · have childDeeperThanCursor :
        input.LocalizedDepthDependency child.occurrence cursor.occurrence :=
      ⟨rootEq, by omega⟩
    exact input.localizedDepthDependency_trans childDeeperThanCursor dependency
  · omega

/-- An actual first executable child of the target-start cursor that is strictly deeper than the
target is already an outward cursor.  The strict-depth fact is supplied by the caller, not assumed:
it is exactly the construction binding the first child to the deeper address. -/
theorem outward_first_cursor
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (first : input.LocalizedRerootCursor fuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length) :
    OutwardRerootCursor input target first := by
  let start : input.LocalizedRerootCursor fuel := { occurrence := target, previous? := none }
  have derived : input.DeclarativeLocalizedRerootChildren start
      (input.executableLocalizedRerootChildren start) :=
    input.executableLocalizedRerootChildren_declarative start
  have firstValid : input.LocalizedRerootCursorValid first :=
    input.localizedRerootChild_valid start first
      (input.executableLocalizedRerootChildren start) derived firstChild
  have firstRoot : first.occurrence.1.root = target.1.root :=
    input.localizedRerootChildren_root_eq start first
      (input.executableLocalizedRerootChildren start) derived firstChild
  have firstPrevious : first.previous? = some target := by
    simpa [start] using (input.executableLocalizedRerootChildren_previous start first firstChild)
  refine ⟨firstValid, ⟨firstRoot, firstDeeper⟩, target, firstPrevious, firstDeeper⟩

/-- The outward property propagates along every reflexive-transitive `E`-path. -/
theorem outward_reachable_cursor
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (first child : input.LocalizedRerootCursor fuel)
    (firstOutward : OutwardRerootCursor input target first)
    (reachable : Relation.ReflTransGen (E input) first child) :
    OutwardRerootCursor input target child := by
  induction reachable with
  | refl => exact firstOutward
  | tail _path step ih => exact outward_edge_preserves input target _ _ ih step

/-- Every cursor reachable from an actual strictly-deeper first child of the target-start cursor is
a strict depth dependency of the target and is path-valid. -/
theorem outward_reachable_dependency
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (first child : input.LocalizedRerootCursor fuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child) :
    input.LocalizedDepthDependency child.occurrence target ∧
      input.LocalizedRerootCursorValid child := by
  have allOutward : OutwardRerootCursor input target child :=
    outward_reachable_cursor input target first child
      (outward_first_cursor input target first firstChild firstDeeper) reachable
  exact ⟨allOutward.2.1, allOutward.1⟩

/-- Reading a cursor that is already known to be a strict dependency of the target through the
restricted view returns the unrestricted whole-state label.  This is the structural agreement of
restricted and unrestricted reads; no read-support predicate is assumed. -/
theorem localizedDependencyLabel_eq_state_of_dependency
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (cursor : input.LocalizedRerootCursor fuel)
    (dependency : input.LocalizedDepthDependency cursor.occurrence target) :
    input.localizedDependencyLabel target (input.localizedDependencyView state target) cursor =
      state cursor.occurrence := by
  unfold localizedDependencyLabel
  rw [dif_pos dependency]
  unfold localizedDependencyView
  rfl

/-- Restricted and unrestricted reads agree throughout the whole outward subtree below an actual
strictly-deeper first child of the target. -/
theorem outward_reachable_dependencyLabel_eq_state
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (state : input.LocalizedAuxiliaryState fuel)
    (first child : input.LocalizedRerootCursor fuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child) :
    input.localizedDependencyLabel target (input.localizedDependencyView state target) child =
      state child.occurrence := by
  have facts := outward_reachable_dependency input target first child
    firstChild firstDeeper reachable
  exact localizedDependencyLabel_eq_state_of_dependency input target state child facts.1

/-- Every cursor reachable from an actual strictly-deeper first child of the target admits the
eager compound Rules-4/5 key at the proved twice-depth bound.  Totality is not reproved here; it is
the existing `exists_buildLocalizedRerootCompoundRule45Key?_at_twice`. -/
theorem outward_reachable_compound_key_exists
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (first child : input.LocalizedRerootCursor carrierFuel)
    (firstChild : first ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (firstDeeper : target.1.address.length < first.occurrence.1.address.length)
    (reachable : Relation.ReflTransGen (E input) first child) :
    ∃ key, input.buildLocalizedRerootCompoundRule45Key?
      target view (2 * (carrierFuel + 1)) child = some key := by
  have facts := outward_reachable_dependency input target first child
    firstChild firstDeeper reachable
  exact input.exists_buildLocalizedRerootCompoundRule45Key?_at_twice target view child facts.2

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outward_edge
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outward_edge_excludes_previous
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outward_edge_preserves
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outward_first_cursor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outward_reachable_cursor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outward_reachable_dependency
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDependencyLabel_eq_state_of_dependency
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outward_reachable_dependencyLabel_eq_state
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outward_reachable_compound_key_exists

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
