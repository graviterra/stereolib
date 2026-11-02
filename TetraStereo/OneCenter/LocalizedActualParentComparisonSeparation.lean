import TetraStereo.OneCenter.LocalizedParentBranchConstitutionalSeparation
import TetraStereo.OneCenter.LocalizedParentFrameHistory
import TetraStereo.OneCenter.LocalizedRerootRootObservation
import TetraStereo.OneCenter.LocalizedConstitutionalRootSeparation
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput




















































/-! ## The primitive instance: every outward child separates from the parent

The parent frame certificate supplies the exact `current :: parentCurrent :: tail` history shape.
The outward child's node is recovered as an actual executable official child of the target node by
inverting the carrier derivation across the appended sibling slot
(`declarativeLocalizedOccurrence_immediate_child`); this is what feeds the stored
parent-branch-separation primitive. -/

/-- **Occurrence-level parent/outward-child Rule-1b separation.**

For an active-simple carrier occurrence `target` and an actual parent-frame certificate of it,
every outward executable reroot child of the target cursor -- identified by the explicit appended
sibling slot -- has a Rule-1b root distance distinct from the parent frame's.  The proof derives
the child node's membership in `executableOfficialCIPChildren target.1.node` from the carrier
derivation, then applies the already-proved primitive
`LocalizedParentBranchConstitutionalSeparation.parentRule1bDistance_ne_childRule1bDistance`. -/
theorem outwardChild_rule1bRootDistance_ne_parent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := some certificate.parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      certificate.parent.1.node.rule1bRootDistance ≠
        child.occurrence.1.node.rule1bRootDistance := by
  obtain ⟨current, parentCurrent, tail, currentEq, _parentCurrentEq, historyEq,
    parentHistoryEq⟩ := certificate.history_shape input
  let targetCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := some certificate.parent }
  have childrenDerived := input.executableLocalizedRerootChildren_declarative targetCursor
  intro child slot childPresent childAddress
  have sameRoot : child.occurrence.1.root = target.1.root :=
    input.localizedRerootChildren_root_eq targetCursor child
      (input.executableLocalizedRerootChildren targetCursor) childrenDerived childPresent
  have targetDerived : input.DeclarativeLocalizedOccurrence carrierFuel target.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel target.1).mp target.2
  have childDerived : input.DeclarativeLocalizedOccurrence carrierFuel child.occurrence.1 :=
    (input.mem_localizedOccurrences_iff carrierFuel child.occurrence.1).mp child.occurrence.2
  obtain ⟨childNode, childAtSlot, childFrameEq⟩ :=
    input.declarativeLocalizedOccurrence_immediate_child
      targetDerived childDerived sameRoot slot childAddress
  have childNodeEq : child.occurrence.1.node = childNode := by
    simpa using (congrArg (fun (frame : input.LocalizedCIPOccurrenceFrame) => frame.node)
      childFrameEq)
  have childNodePresent : childNode ∈ input.executableOfficialCIPChildren target.1.node :=
    List.fst_mem_of_mem_zipIdx childAtSlot
  have childNodeMem : child.occurrence.1.node ∈
      input.executableOfficialCIPChildren target.1.node := by
    rw [childNodeEq]
    exact childNodePresent
  have distanceNe :=
    LocalizedParentBranchConstitutionalSeparation.parentRule1bDistance_ne_childRule1bDistance
      input target.1.node certificate.parent.1.node current parentCurrent tail
      targetActive currentEq historyEq (certificate.parent_provenance input)
      parentHistoryEq child.occurrence.1.node childNodeMem
  exact fun h => distanceNe h.symm

/-! ## Comparator separation from distinct first Rule-1b spheres

This is the pure compositional step: given two already-built cumulative keys whose constitutional
keys begin with singleton Rule-1b spheres at distinct distances, the constitutional comparator is
strict and the full cumulative comparator is already decided at that constitutional component, so
the descriptor projection is not consulted. -/

/-- **Constitutional strictness with descriptor noninterference, from built keys.**

If two cumulative keys have first Rule-1b spheres `[([], leftDistance)]` and
`[([], rightDistance)]` with `leftDistance ≠ rightDistance`, then (1) their constitutional keys
compare strictly, and (2) the full cumulative comparator equals that constitutional comparison, so
the descriptor projection is never reached. -/
theorem builtCumulativeKeys_constitutionalCompare_ne_eq
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    {leftDistance rightDistance : ℕ}
    (leftHead : left.constitutional.rule1b.head? = some [([], leftDistance)])
    (rightHead : right.constitutional.rule1b.head? = some [([], rightDistance)])
    (different : leftDistance ≠ rightDistance) :
    OfficialRuleMajorKey.compare left.constitutional right.constitutional ≠ Ordering.eq ∧
      input.compareLocalizedRerootCumulativeRule45Keys left right =
        OfficialRuleMajorKey.compare left.constitutional right.constitutional := by
  have constitutionalNe :
      OfficialRuleMajorKey.compare left.constitutional right.constitutional ≠ Ordering.eq :=
    OfficialRuleMajorKey.compare_ne_eq_of_rule1b_head_distances leftHead rightHead different
  refine ⟨constitutionalNe, ?_⟩
  unfold compareLocalizedRerootCumulativeRule45Keys
  simpa [Ordering.byKey] using
    (ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq
      (Ordering.byKey (fun key : input.LocalizedRerootCumulativeRule45Key => key.constitutional)
        OfficialRuleMajorKey.compare)
      (Ordering.byKey (fun key : input.LocalizedRerootCumulativeRule45Key => key.descriptor)
        (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority))
      left right
      (by simpa [Ordering.byKey] using constitutionalNe))

/-! ## The composed endpoint: parent-side versus every outward-side cursor

The parent-side cursor is the actual carrier parent frame reached *from the target*
(`previous? := some target`).  This is the incoming cut of a genuine traversal step from the target
to its parent: with `previous? := none` the compiler would be free to step back through the target,
so `none` describes an uncut start cursor rather than the parent ligand.  The outward-side cursors
are the executable reroot children of the target cursor in the outward direction.  Both cursors
are path-valid, so `LocalizedRerootFuelCompleteness` constructs their cumulative keys at twice the
carrier depth, and the two preceding facts combine into strict constitutional separation decided
before the descriptor projection. -/

/-- **The actual parent ligand cursor is an executable child of the target-start cursor.**

The parent frame is an uncut tree neighbor of the target
(`LocalizedParentFrameHistory.parent_mem_neighborFrames`), and the target's real-atom provenance
makes it non-duplicate, so the parent frame lies in the intended child frames of the target-start
cursor `{occurrence := target, previous? := none}`.  The emitted cursor records `target` as its
incoming cut, i.e. exactly `{occurrence := certificate.parent, previous? := some target}`. -/
theorem parentCursor_mem_executableLocalizedRerootChildren
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target) :
    ({ occurrence := certificate.parent, previous? := some target } :
        input.LocalizedRerootCursor carrierFuel) ∈
      input.executableLocalizedRerootChildren
        { occurrence := target, previous? := none } := by
  have neighbor : certificate.parent.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 :=
    certificate.parent_mem_neighborFrames input
  have notDuplicate : target.1.node.isDuplicateLeaf = false := by
    simp [OfficialCIPNode.isDuplicateLeaf, targetActive.1]
  have intended : certificate.parent.1 ∈
      input.intendedLocalizedRerootChildFrames
        { occurrence := target, previous? := none } := by
    simp [intendedLocalizedRerootChildFrames, notDuplicate, neighbor]
  unfold executableLocalizedRerootChildren
  rw [List.mem_map]
  refine ⟨⟨certificate.parent.1, intended⟩, List.mem_attach _ _, ?_⟩
  apply LocalizedRerootCursor.ext
  · exact Subtype.ext rfl
  · rfl

/-- **Parent-side vs every outward-side cursor: strict constitutional comparison.**

For an active-simple carrier occurrence `target` with an actual parent-frame certificate, an
arbitrary cumulative stage and an arbitrary dependency view of `target`, every outward executable
reroot child of the target cursor compiles a cumulative key whose constitutional comparison against
the parent-side key is strict, and the full cumulative comparator is already decided at that
constitutional component (the descriptor projection is not reached).  The parent-side cursor keeps
the target as its incoming cut (`previous? := some target`), so the compilation cannot step back
through the target. -/
theorem parentSide_outwardChild_constitutionalCompare_ne_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (certificate : input.LocalizedParentFrameHistory target)
    (stage : LocalizedCumulativeRule45Stage)
    (view : input.LocalizedDependencyView target) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target, previous? := some certificate.parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      ∃ parentKey childKey,
        input.buildLocalizedRerootCumulativeRule45Key? stage target view
            (2 * (carrierFuel + 1))
            { occurrence := certificate.parent, previous? := some target } = some parentKey ∧
        input.buildLocalizedRerootCumulativeRule45Key? stage target view
            (2 * (carrierFuel + 1)) child = some childKey ∧
        OfficialRuleMajorKey.compare parentKey.constitutional childKey.constitutional ≠ Ordering.eq ∧
        input.compareLocalizedRerootCumulativeRule45Keys parentKey childKey =
          OfficialRuleMajorKey.compare parentKey.constitutional childKey.constitutional := by
  let parentCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := certificate.parent, previous? := some target }
  let targetCursor : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := some certificate.parent }
  intro child slot childPresent childAddress
  have parentValid : input.LocalizedRerootCursorValid
      { occurrence := certificate.parent, previous? := some target } := by
    change certificate.parent.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1
    exact certificate.parent_mem_neighborFrames input
  have childrenDerived := input.executableLocalizedRerootChildren_declarative targetCursor
  have childValid : input.LocalizedRerootCursorValid child :=
    input.localizedRerootChild_valid targetCursor child
      (input.executableLocalizedRerootChildren targetCursor) childrenDerived childPresent
  obtain ⟨parentKey, parentBuilt⟩ :=
    input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      stage target view parentCursor parentValid
  obtain ⟨childKey, childBuilt⟩ :=
    input.exists_buildLocalizedRerootCumulativeRule45Key?_at_twice
      stage target view child childValid
  have parentHead := input.buildLocalizedRerootCumulativeRule45Key?_constitutional_rule1b_head
    stage target view (2 * (carrierFuel + 1)) parentCursor parentKey parentBuilt
  have childHead := input.buildLocalizedRerootCumulativeRule45Key?_constitutional_rule1b_head
    stage target view (2 * (carrierFuel + 1)) child childKey childBuilt
  have distanceNe := input.outwardChild_rule1bRootDistance_ne_parent
    target targetActive certificate child slot childPresent childAddress
  have compareResult := input.builtCumulativeKeys_constitutionalCompare_ne_eq
    parentKey childKey parentHead childHead distanceNe
  exact ⟨parentKey, childKey, parentBuilt, childBuilt, compareResult.1, compareResult.2⟩

/-! ## Canonical parent-selector instantiation

The endpoints above take an explicit parent-frame certificate.  For a non-root carrier occurrence
that certificate is not an extra hypothesis about the data: `exists_localizedParentFrameHistory`
constructs it from carrier reachability, `parent_unique` shows the parent is unique, and
`LocalizedParentFrameHistory.carrierParentFrames_eq_singleton` /
`LocalizedParentFrameHistory.localizedRule3CarrierParentFrame?_eq_some` identify the executable
singleton parent selector `localizedRule3CarrierParentFrame?` with exactly that actual parent
frame.

The following corollaries therefore derive, rather than assume, the parent history shape, the
parent-side cursor, and the selector equality.  In particular no final history is assumed and no
strict comparison is assumed: existence of both keys is still constructed at fuel
`2 * (carrierFuel + 1)`, and strictness is still derived from the Rule-1b root-distance
separation. -/

/-- **Occurrence-level separation with a derived parent certificate.**

For an active-simple non-root carrier occurrence, the canonical parent-frame certificate is
obtained from `exists_localizedParentFrameHistory`; every outward executable reroot child then
has a Rule-1b root distance distinct from the actual parent's.  No parent history is assumed. -/
theorem outwardChild_rule1bRootDistance_ne_parent_of_carrier
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (nonroot : target.1.address ≠ []) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target,
          previous? := some (input.localizedParentFrameHistory target nonroot).parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      (input.localizedParentFrameHistory target nonroot).parent.1.node.rule1bRootDistance ≠
        child.occurrence.1.node.rule1bRootDistance := by
  intro child slot childPresent childAddress
  exact input.outwardChild_rule1bRootDistance_ne_parent target targetActive
    (input.localizedParentFrameHistory target nonroot) child slot childPresent childAddress

/-- **Actual parent selector versus every outward-side cursor.**

For an active-simple non-root carrier occurrence `target`, the executable singleton parent
selector returns exactly the canonical certificate's actual parent frame; at an arbitrary
cumulative stage and dependency view, every outward executable reroot child compiles a key whose
constitutional Rule-1b first sphere is its own node's root distance, the parent-side key's first
sphere is the actual parent's root distance, the constitutional comparison is strict, and the
full cumulative comparator is already decided at that constitutional component.  Both key
existences are concluded from `LocalizedRerootFuelCompleteness`, not assumed, and the literal
parent ligand cursor `{parent, previous? := some target}` is itself exposed as an executable child
of the target-start cursor. -/
theorem parentSide_outwardChild_constitutionalCompare_ne_eq_of_carrier
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (targetActive : target.1.node.ActiveSimple)
    (nonroot : target.1.address ≠ [])
    (stage : LocalizedCumulativeRule45Stage)
    (view : input.LocalizedDependencyView target) :
    ∀ (child : input.LocalizedRerootCursor carrierFuel) (slot : Nat),
      child ∈ input.executableLocalizedRerootChildren
        { occurrence := target,
          previous? := some (input.localizedParentFrameHistory target nonroot).parent } →
      child.occurrence.1.address = target.1.address ++ [slot] →
      ({ occurrence := (input.localizedParentFrameHistory target nonroot).parent,
          previous? := some target } : input.LocalizedRerootCursor carrierFuel) ∈
        input.executableLocalizedRerootChildren
          { occurrence := target, previous? := none } ∧
      input.localizedRule3CarrierParentFrame? target =
          some (input.localizedParentFrameHistory target nonroot).parent.1 ∧
      ∃ parentKey childKey,
        input.buildLocalizedRerootCumulativeRule45Key? stage target view
            (2 * (carrierFuel + 1))
            { occurrence := (input.localizedParentFrameHistory target nonroot).parent,
              previous? := some target } = some parentKey ∧
        input.buildLocalizedRerootCumulativeRule45Key? stage target view
            (2 * (carrierFuel + 1)) child = some childKey ∧
        parentKey.constitutional.rule1b.head? =
          some [([], (input.localizedParentFrameHistory target nonroot).parent.1.node.rule1bRootDistance)] ∧
        childKey.constitutional.rule1b.head? =
          some [([], child.occurrence.1.node.rule1bRootDistance)] ∧
        OfficialRuleMajorKey.compare parentKey.constitutional childKey.constitutional ≠
          Ordering.eq ∧
        input.compareLocalizedRerootCumulativeRule45Keys parentKey childKey =
          OfficialRuleMajorKey.compare parentKey.constitutional childKey.constitutional := by
  intro child slot childPresent childAddress
  have parentMembership :=
    input.parentCursor_mem_executableLocalizedRerootChildren target targetActive
      (input.localizedParentFrameHistory target nonroot)
  obtain ⟨parentKey, childKey, parentBuilt, childBuilt, constitutionalNe, comparisonEq⟩ :=
    input.parentSide_outwardChild_constitutionalCompare_ne_eq target targetActive
      (input.localizedParentFrameHistory target nonroot) stage view child slot
      childPresent childAddress
  have parentHead :=
    input.buildLocalizedRerootCumulativeRule45Key?_constitutional_rule1b_head
      stage target view (2 * (carrierFuel + 1))
      { occurrence := (input.localizedParentFrameHistory target nonroot).parent,
        previous? := some target } parentKey parentBuilt
  have childHead :=
    input.buildLocalizedRerootCumulativeRule45Key?_constitutional_rule1b_head
      stage target view (2 * (carrierFuel + 1)) child childKey childBuilt
  have selected :=
    (input.localizedParentFrameHistory target nonroot).localizedRule3CarrierParentFrame?_eq_some
      input
  exact ⟨parentMembership, selected, parentKey, childKey, parentBuilt, childBuilt, parentHead,
    childHead, constitutionalNe, comparisonEq⟩

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

/-! ## Kernel-authority assertions

`assert_kernel_only` permits exactly `propext`, `Classical.choice` and `Quot.sound`, and rejects
`sorryAx`, project axioms and native/compiler trust. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outwardChild_rule1bRootDistance_ne_parent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.builtCumulativeKeys_constitutionalCompare_ne_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parentSide_outwardChild_constitutionalCompare_ne_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parentCursor_mem_executableLocalizedRerootChildren
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.outwardChild_rule1bRootDistance_ne_parent_of_carrier
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.parentSide_outwardChild_constitutionalCompare_ne_eq_of_carrier
