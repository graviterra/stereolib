import TetraStereo.OneCenter.LocalizedChemicalRingPromotedConstitutionReadback
import TetraStereo.OneCenter.LocalizedRetainedRule4aCanonicalBridge
import TetraStereo.OneCenter.LocalizedMarkedRetainedFuelSaturation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Stereochemical observations at a common canonical address

The address reader keeps two distinct absence cases: an unoccupied address and an occupied
node whose stereochemical evidence is absent. At a dense addressing sorted by the independent
ordinary key, the reader equals the corresponding key observation. Equal keys therefore give
equal stereochemical observations at the same addresses, including ring-duplicate positions.

The operational lemmas recover exact successful stage builds from their traces and identify
Rule-4a subtree keys with the prefix of the complete ordinary key compiled at their source.
These use the actual fixed reader and derive fuel independence from successful builds.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingPromotedStereoReadback

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge RootedDigraph
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedCanonicalFrame
open LocalizedMarkedRetainedCanonicalMarker LocalizedMarkedRetainedSubtreeContext
open LocalizedMarkedRetainedPromotedKey LocalizedChemicalRingPromotedConstitutionReadback

noncomputable section
open scoped Classical

section Address

variable {Atom : Type} (graph : RootedDigraph Atom)
  (observe : ConstitutionalRule → graph.Node → ℤ)
  (evidence : StereochemicalEvidence graph)

def stereoAt (addressing : graph.Addressing) (rule : StereochemicalRule)
    (position : List Nat) : WithBot StereoLabel :=
  if h : ∃ node, addressing.address node = position then
    (stereoLabel graph evidence rule (Classical.choose h) : WithBot StereoLabel) else ⊥

theorem stereoAt_of_address (addressing : graph.Addressing) (rule : StereochemicalRule)
    (node : graph.Node) :
    stereoAt graph evidence addressing rule (addressing.address node) =
      (stereoLabel graph evidence rule node : WithBot StereoLabel) := by
  have present : ∃ found, addressing.address found = addressing.address node := ⟨node, rfl⟩
  unfold stereoAt
  rw [dif_pos present]
  congr 2
  exact addressing.address_injective (Classical.choose_spec present)

theorem stereoAt_of_unoccupied (addressing : graph.Addressing) (rule : StereochemicalRule)
    {position : List Nat} (absent : ∀ node, addressing.address node ≠ position) :
    stereoAt graph evidence addressing rule position = ⊥ := by
  unfold stereoAt
  rw [dif_neg (by simpa using absent)]

theorem stereoAt_eq_keyObservation (W D : Nat) {addressing : graph.Addressing}
    (dense : Dense addressing)
    (sorted : KeySorted (ordinaryKeyWithObservations graph observe evidence W D) addressing)
    (rule : StereochemicalRule) :
    ∀ (path : List Nat) (node : graph.Node),
      (∀ slot ∈ path, slot < W) → path.length ≤ D →
      observedStereoNodePathObservation graph observe evidence W D rule node path =
        stereoAt graph evidence addressing rule (addressing.address node ++ path)
  | [], node, _, _ => by
      rw [List.append_nil, stereoAt_of_address, observedStereoNodePathObservation_nil]
  | slot :: path, node, digits, length => by
      have slotBound : slot < W := digits slot (by simp)
      have pathBounds : ∀ i ∈ path, i < W := fun i hi => digits i (by simp [hi])
      have pathDepth : path.length < D := by simp at length; omega
      obtain ⟨count, countDense⟩ := dense node
      have ranked := sortDesc_childKeys_eq_slotOrder
        (ordinaryKeyWithObservations graph observe evidence W D) countDense sorted
      have order : ((slotList addressing node count).map
          (ordinaryKeyWithObservations graph observe evidence W D)).Pairwise (fun x y => y ≤ x) := by
        rw [← ranked]
        exact Certificate.CanonicalSphereKey.sortDesc_pairwise _
      rw [observedStereoNodePathObservation_cons graph observe evidence W D rule node
        (slotList_perm countDense) order, if_pos ⟨slotBound, pathDepth⟩]
      by_cases occupied : slot < count
      · obtain ⟨child, childAt, childAddress⟩ := slotList_getD_of_lt countDense occupied
        rw [childAt, Option.map_some, Option.getD_some]
        have position : addressing.address node ++ slot :: path =
            addressing.address child ++ path := by rw [childAddress]; simp
        rw [position]
        exact stereoAt_eq_keyObservation W D dense sorted rule path child pathBounds (by omega)
      · have noChild : (slotList addressing node count)[slot]? = none := by
          simp [slotList]; omega
        have absent : ∀ found,
            addressing.address found ≠ addressing.address node ++ slot :: path := by
          intro found foundAt
          obtain ⟨ancestor, ancestorAt⟩ := addressing.prefix_occupied found
            (addressing.address node ++ [slot]) path (by rw [foundAt]; simp)
          exact occupied ((countDense slot).mp ⟨ancestor, ancestorAt⟩)
        rw [noChild, Option.map_none, Option.getD_none,
          stereoAt_of_unoccupied graph evidence addressing rule absent]

private theorem stereoAt_outside (addressing : graph.Addressing) (dense : Dense addressing)
    {W D : Nat} (width : graph.width ≤ W) (height : graph.height ≤ D)
    (position : List Nat) (outside : ¬ ((∀ slot ∈ position, slot < W) ∧ position.length ≤ D))
    (rule : StereochemicalRule) : stereoAt graph evidence addressing rule position = ⊥ := by
  apply stereoAt_of_unoccupied
  intro node equal
  apply outside
  constructor
  · intro slot member
    rw [← equal] at member
    exact (address_slots_lt_width dense node slot member).trans_le width
  · rw [← equal]
    exact (address_length_le_height addressing node).trans height

theorem stereoAt_eq_of_component_eq
    (right : RootedDigraph Atom) (obsR : ConstitutionalRule → right.Node → ℤ)
    (evidenceR : StereochemicalEvidence right) (W D : Nat)
    (widthL : graph.width ≤ W) (heightL : graph.height ≤ D)
    (widthR : right.width ≤ W) (heightR : right.height ≤ D)
    (addressL : graph.Addressing) (addressR : right.Addressing)
    (denseL : Dense addressL) (denseR : Dense addressR)
    (sortedL : KeySorted (ordinaryKeyWithObservations graph observe evidence W D) addressL)
    (sortedR : KeySorted (ordinaryKeyWithObservations right obsR evidenceR W D) addressR)
    (rule : StereochemicalRule)
    (keys : (ofLex (ordinaryKeyWithObservations graph observe evidence W D graph.root)).2.getD
        (stereoIndex rule) [] =
      (ofLex (ordinaryKeyWithObservations right obsR evidenceR W D right.root)).2.getD
        (stereoIndex rule) []) (position : List Nat) :
    stereoAt graph evidence addressL rule position = stereoAt right evidenceR addressR rule position := by
  by_cases inside : (∀ slot ∈ position, slot < W) ∧ position.length ≤ D
  · have readL := stereoAt_eq_keyObservation graph observe evidence W D denseL sortedL rule
      position graph.root inside.1 inside.2
    have readR := stereoAt_eq_keyObservation right obsR evidenceR W D denseR sortedR rule
      position right.root inside.1 inside.2
    rw [addressL.root_address, List.nil_append] at readL
    rw [addressR.root_address, List.nil_append] at readR
    unfold observedStereoNodePathObservation at readL readR
    rw [keys] at readL
    exact readL.symm.trans readR
  · rw [stereoAt_outside graph evidence addressL denseL widthL heightL position inside rule,
      stereoAt_outside right evidenceR addressR denseR widthR heightR position inside rule]

end Address

section Actual

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

theorem trace_built {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input stage read fuel tree key) :
    input.buildRuleMajorCumulativeWithRead? stage read fuel tree.source = some key := by
  cases trace with
  | terminal fuel cursor children computed empty matched realized =>
      cases fuel <;> simp [buildRuleMajorCumulativeWithRead?, localizedRootTree, computed, empty]
  | node fuel cursor children childKeys sortedKeys sortedTrees computed nonempty built
      sorted constitutional descending matched realized traced =>
      simp [buildRuleMajorCumulativeWithRead?, localizedRootTree, computed, nonempty, built, sorted]

theorem builds_unique {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {leftFuel rightFuel : Nat} {cursor : input.LocalizedRerootCursor carrierFuel}
    {left right : input.LocalizedRerootCumulativeRule45Key}
    (leftBuilt : input.buildRuleMajorCumulativeWithRead? stage read leftFuel cursor = some left)
    (rightBuilt : input.buildRuleMajorCumulativeWithRead? stage read rightFuel cursor = some right) :
    left = right := by
  have l := LocalizedMarkedRetainedFuelSaturation.build_mono input stage read leftFuel
    (max leftFuel rightFuel) (le_max_left _ _) cursor left leftBuilt
  have r := LocalizedMarkedRetainedFuelSaturation.build_mono input stage read rightFuel
    (max leftFuel rightFuel) (le_max_right _ _) cursor right rightBuilt
  exact Option.some.inj (l.symm.trans r)

theorem subtree_rule4a_eq_ordinary
    (target : input.LocalizedCIPOccurrence carrierFuel) (view : input.LocalizedDependencyView target)
    {fuel : Nat} {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (trace : LocalizedRuleMajorSortTrace input .rule4a
      (input.localizedDependencyLabel target view) fuel tree key)
    (compound : input.LocalizedRerootCompoundRule45Key)
    (built : ordinaryKey? input target view tree.source = some compound) :
    key = compound.prior.rule4aKey :=
  builds_unique (trace_built trace) (ordinary_rule4a_built target view tree.source compound built)

theorem rule4a_ne_lt_of_full_ne_lt (left right : input.LocalizedRerootCompoundRule45Key)
    (ordered : (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering ≠ .lt) :
    input.compareLocalizedRerootCumulativeRule45Keys left.prior.rule4aKey right.prior.rule4aKey ≠ .lt := by
  intro less
  apply ordered
  simp [CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5,
    CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys, compareLex,
    Ordering.byKey, less]

theorem rule4a_eq_of_full_eq (left right : input.LocalizedRerootCompoundRule45Key)
    (tie : (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering = .eq) :
    input.compareLocalizedRerootCumulativeRule45Keys left.prior.rule4aKey right.prior.rule4aKey = .eq := by
  cases h : input.compareLocalizedRerootCumulativeRule45Keys left.prior.rule4aKey right.prior.rule4aKey
    <;> simp_all [CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5,
      CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule4bcKeys, compareLex, Ordering.byKey]

end Actual
end
end TetraStereo.OneCenter.LocalizedChemicalRingPromotedStereoReadback

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedStereoReadback.stereoAt_eq_keyObservation
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedStereoReadback.stereoAt_eq_of_component_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedStereoReadback.trace_built
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedStereoReadback.builds_unique
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedStereoReadback.subtree_rule4a_eq_ordinary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedStereoReadback.rule4a_ne_lt_of_full_ne_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedStereoReadback.rule4a_eq_of_full_eq
