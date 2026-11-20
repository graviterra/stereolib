import TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Actual promoted ties preserve reference membership at promoted canonical addresses

An actual refined-key tie supplies equal independent marker columns. At a layout covering both
actual arm hierarchies, this constructs two dense promoted-canonical addressings whose reference
observations agree at every address. The addressings and their canonicality are derived, not
assumed. They also respect the independent deep ordinary priorities.

This is the marker half of joint constitutional/marker readback. It does not identify an absent
position with an occupied unmarked node, construct a residual path equivalence, or assert that
the original constitutional tree addressing is promoted-canonical. The remaining bridge must
recover constitutional observations and occupied positions at these same re-ranked addresses
before applying the colored component reconstruction.
-/

namespace TetraStereo.OneCenter.LocalizedChemicalRingPromotedColorReadback

open DeclarativeCIP DeclarativeCIP.PromotedCanonical
open RootedDigraph

noncomputable section
open scoped Classical

universe u

section Addressing

variable {Atom : Type u} {P : Type*} [LinearOrder P]

/-- Address digits need a bound on each child list, not on the total expanded-node count. -/
theorem address_slots_lt_of_branching {graph : RootedDigraph Atom}
    {addressing : graph.Addressing} (dense : Dense addressing) {W : Nat}
    (branching : ∀ node, (graph.childList node).length ≤ W) (node : graph.Node) :
    ∀ slot ∈ addressing.address node, slot < W := by
  induction graph.reachable node with
  | refl => simp [addressing.root_address]
  | @tail parent node _ edge ih =>
      obtain ⟨last, address⟩ := (addressing.child_iff parent node).mp edge
      obtain ⟨count, countDense⟩ := dense parent
      have countEq : count = (graph.childList parent).length := by
        simpa [slotList] using (slotList_perm countDense).length_eq
      have lastBound : last < count := (countDense last).mp ⟨node, address⟩
      intro slot member
      rw [address, List.mem_append, List.mem_singleton] at member
      rcases member with member | rfl
      · exact ih slot member
      · exact lastBound.trans_le (countEq ▸ branching parent)

private theorem marker_zero_outside {graph : RootedDigraph Atom}
    (mark : graph.Node → Nat) (addressing : graph.Addressing) (dense : Dense addressing)
    {W D : Nat} (width : ∀ node, (graph.childList node).length ≤ W)
    (height : graph.height ≤ D)
    (position : List Nat)
    (outside : ¬ ((∀ slot ∈ position, slot < W) ∧ position.length ≤ D)) :
    addressMarker mark addressing position = 0 := by
  apply addressMarker_of_unoccupied
  intro node equal
  apply outside
  constructor
  · intro slot member
    rw [← equal] at member
    exact address_slots_lt_of_branching dense width node slot member
  · rw [← equal]
    exact (address_length_le_height addressing node).trans height

/-- Equal root markers give equal observations between two different covered hierarchies. -/
theorem addressMarkers_eq_of_root_marker_eq
    (left right : RootedDigraph Atom)
    (priorL : left.Node → P) (priorR : right.Node → P)
    (markL : left.Node → Nat) (markR : right.Node → Nat)
    (W D : Nat) (widthL : ∀ node, (left.childList node).length ≤ W)
    (heightL : left.height ≤ D)
    (widthR : ∀ node, (right.childList node).length ≤ W) (heightR : right.height ≤ D)
    {addressL : left.Addressing} {addressR : right.Addressing}
    (canonicalL : PromotedCanonical.CanonicalAddressing left priorL markL W D addressL)
    (canonicalR : PromotedCanonical.CanonicalAddressing right priorR markR W D addressR)
    (equal : markerKey left priorL markL W D left.root =
      markerKey right priorR markR W D right.root) (position : List Nat) :
    addressMarker markL addressL position = addressMarker markR addressR position := by
  by_cases inside : (∀ slot ∈ position, slot < W) ∧ position.length ≤ D
  · have readL := addressMarker_eq_keyObservation left priorL markL W D
      canonicalL.1 canonicalL.2 position left.root inside.1 inside.2
    have readR := addressMarker_eq_keyObservation right priorR markR W D
      canonicalR.1 canonicalR.2 position right.root inside.1 inside.2
    rw [addressL.root_address, List.nil_append] at readL
    rw [addressR.root_address, List.nil_append] at readR
    exact readL.symm.trans ((congrArg
      (fun column => markerObservation column position.length
        (Certificate.CanonicalSphereKey.slotOf W position)) equal).trans readR)
  · rw [marker_zero_outside markL addressL canonicalL.1 widthL heightL position inside,
      marker_zero_outside markR addressR canonicalR.1 widthR heightR position inside]

/-- Two constructed promoted-canonical addressings with one common marker observation column.
The structure makes no assertion about equality of their occupied positions. -/
structure MatchedMarkerAddressings (left right : RootedDigraph Atom)
    (priorL : left.Node → P) (priorR : right.Node → P)
    (markL : left.Node → Nat) (markR : right.Node → Nat) (W D : Nat) where
  leftAddressing : left.Addressing
  rightAddressing : right.Addressing
  leftCanonical : PromotedCanonical.CanonicalAddressing left priorL markL W D leftAddressing
  rightCanonical : PromotedCanonical.CanonicalAddressing right priorR markR W D rightAddressing
  same : ∀ position, addressMarker markL leftAddressing position =
    addressMarker markR rightAddressing position

namespace MatchedMarkerAddressings

variable {left right : RootedDigraph Atom}
  {priorL : left.Node → P} {priorR : right.Node → P}
  {markL : left.Node → Nat} {markR : right.Node → Nat} {W D : Nat}
  (matched : MatchedMarkerAddressings left right priorL priorR markL markR W D)

/-- Promotion only refines the independent earlier priority at every parent. -/
theorem prior_sorted : KeySorted priorL matched.leftAddressing ∧
    KeySorted priorR matched.rightAddressing :=
  ⟨canonicalAddressing_prior_sorted left priorL markL W D matched.leftCanonical,
    canonicalAddressing_prior_sorted right priorR markR W D matched.rightCanonical⟩

/-- Actual occupied nodes sharing a promoted address have the same marker. -/
theorem marks_eq (x : left.Node) (y : right.Node)
    (address : matched.leftAddressing.address x = matched.rightAddressing.address y) :
    markL x = markR y := by
  have same := matched.same (matched.leftAddressing.address x)
  rw [addressMarker_of_address, address, addressMarker_of_address] at same
  exact same

end MatchedMarkerAddressings

/-- Canonicality is constructed from arbitrary base tree addressings and equal root markers. -/
theorem exists_matched_marker_addressings
    (left right : RootedDigraph Atom)
    (priorL : left.Node → P) (priorR : right.Node → P)
    (markL : left.Node → Nat) (markR : right.Node → Nat)
    (W D : Nat) (widthL : ∀ node, (left.childList node).length ≤ W)
    (heightL : left.height ≤ D)
    (widthR : ∀ node, (right.childList node).length ≤ W) (heightR : right.height ≤ D)
    (baseL : left.Addressing) (baseR : right.Addressing)
    (equal : markerKey left priorL markL W D left.root =
      markerKey right priorR markR W D right.root) :
    Nonempty (MatchedMarkerAddressings left right priorL priorR markL markR W D) := by
  obtain ⟨addressL, canonicalL⟩ := exists_canonicalAddressing left priorL markL W D baseL
  obtain ⟨addressR, canonicalR⟩ := exists_canonicalAddressing right priorR markR W D baseR
  exact ⟨⟨addressL, addressR, canonicalL, canonicalR,
    addressMarkers_eq_of_root_marker_eq left right priorL priorR markL markR W D
      widthL heightL widthR heightR canonicalL canonicalR equal⟩⟩

end Addressing

section Actual

open CertifiedLocalizedCIPInput Rule4aTableBridge LocalizedCumulativeDecoratedTree
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedPromotedKey LocalizedMarkedRetainedMolecularSelection

variable (input : CertifiedLocalizedCIPInput)
  (single : input.moleculeGraph.SimpleBonded) (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (reference : input.Atom) (W D : Nat) (fallback : CompleteLigandRule5Key)

/-- Marker readback for the actual successful slot compilations, from the actual refined-key
tie alone. Width and depth bounds state that the chosen marker layout covers both finite arms. -/
theorem actual_tie_matched_marker_addressings (left right : Fin 4)
    (widthL : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).childList node).length ≤ W)
    (heightL : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left)).height ≤ D)
    (widthR : ∀ node, ((ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).childList node).length ≤ W)
    (heightR : (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right)).height ≤ D)
    (tie : refinedKey input single state target real unit targetUnit reference W D left =
      refinedKey input single state target real unit targetUnit reference W D right) :
    Nonempty (MatchedMarkerAddressings
      (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit left))
      (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit right))
      (deepPrior (rawStateDescriptorMap input state) target fallback
        (slotTree input single state target real unit targetUnit left))
      (deepPrior (rawStateDescriptorMap input state) target fallback
        (slotTree input single state target real unit targetUnit right))
      (referenceMark input reference (slotTree input single state target real unit targetUnit left))
      (referenceMark input reference (slotTree input single state target real unit targetUnit right)) W D) := by
  rw [refinedKey_eq_canonical input single state target real unit targetUnit reference W D fallback,
    refinedKey_eq_canonical input single state target real unit targetUnit reference W D fallback] at tie
  have markers := congrArg (fun value : RefinedKey => (ofLex value).2) tie
  exact exists_matched_marker_addressings _ _ _ _ _ _ W D widthL heightL widthR heightR
    (toOfficialSourceTree (slotTree input single state target real unit targetUnit left)).declarativeAddressing
    (toOfficialSourceTree (slotTree input single state target real unit targetUnit right)).declarativeAddressing
    markers

/-- The observed marker is equality to the actual molecular reference atom, including duplicate
occurrences. Thus equal markers preserve the reference predicate at jointly occupied addresses. -/
theorem reference_atoms_iff_of_matched_addresses
    {carrierFuel : Nat} (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel)
    {P : Type*} [LinearOrder P]
    {priorL : (ruleMajorTreeGraph treeL).Node → P}
    {priorR : (ruleMajorTreeGraph treeR).Node → P}
    (matched : MatchedMarkerAddressings (ruleMajorTreeGraph treeL) (ruleMajorTreeGraph treeR)
      priorL priorR (referenceMark input reference treeL) (referenceMark input reference treeR) W D)
    (x : (ruleMajorTreeGraph treeL).Node) (y : (ruleMajorTreeGraph treeR).Node)
    (address : matched.leftAddressing.address x = matched.rightAddressing.address y) :
    (nodeSource input treeL x).occurrence.1.node.current? = some reference ↔
      (nodeSource input treeR y).occurrence.1.node.current? = some reference := by
  have same := matched.marks_eq x y address
  unfold referenceMark referenceBit at same
  by_cases left : (nodeSource input treeL x).occurrence.1.node.current? = some reference <;>
    by_cases right : (nodeSource input treeR y).occurrence.1.node.current? = some reference <;>
    simp_all

end Actual
end

end TetraStereo.OneCenter.LocalizedChemicalRingPromotedColorReadback

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedColorReadback.address_slots_lt_of_branching
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedColorReadback.addressMarkers_eq_of_root_marker_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedColorReadback.MatchedMarkerAddressings
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedColorReadback.MatchedMarkerAddressings.prior_sorted
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedColorReadback.MatchedMarkerAddressings.marks_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedColorReadback.exists_matched_marker_addressings
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedColorReadback.actual_tie_matched_marker_addressings
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedColorReadback.reference_atoms_iff_of_matched_addresses
