import TetraStereo.OneCenter.LocalizedChemicalRingRetainedKeyTransport
import TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame
import TetraStereo.OneCenter.LocalizedChemicalRingPromotedTransportSort
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3000000

/-! Transport of actual promoted markers, preserving the original reader cutoff. -/

namespace TetraStereo.OneCenter.LocalizedChemicalRingPromotedTransport

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedMolecularRule5
open LocalizedMarkedRetainedPromotedKey LocalizedMarkedRetainedVirtualTarget
open LocalizedMarkedRetainedCanonicalMarker LocalizedMarkedRetainedCanonicalFrame
open LocalizedChemicalRingRetainedKeyTransport DeclarativeCIP.PromotedCanonical

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput)

theorem cutMap_transport (e : input.moleculeGraph.Aut)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)) (bound : Nat) :
    cutMap (input.transportDescriptorMap e descriptorMap) bound =
      input.transportDescriptorMap e (cutMap descriptorMap bound) := by
  funext unit
  simp [cutMap, transportDescriptorMap, transportDetectedOccurrence, transportOccurrenceUnit]

theorem aligned_of_reach {fuel : Nat} (t : input.LocalizedCIPOccurrence fuel)
    {cursor : input.LocalizedRerootCursor fuel}
    (reach : Relation.ReflTransGen (E input) ⟨t, none⟩ cursor) :
    input.cursorPreviousRootAligned cursor := by
  induction reach with
  | refl => exact input.cursorPreviousRootAligned_of_none _ rfl
  | @tail parent child _ edge _ =>
      exact input.executableLocalizedRerootChildren_cursorAligned parent child edge

theorem reach_transport (single : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {fuel : Nat} (t : input.LocalizedCIPOccurrence fuel)
    {cursor : input.LocalizedRerootCursor fuel}
    (reach : Relation.ReflTransGen (E input) ⟨t, none⟩ cursor) :
    Relation.ReflTransGen (E input) ⟨input.transportOccurrence single e t, none⟩
      (input.transportCursor single e cursor) := by
  induction reach with
  | refl => exact Relation.ReflTransGen.refl
  | @tail parent child before edge ih =>
      exact ih.tail ((input.executableLocalizedRerootChildren_transport_mem_iff single e
        (aligned_of_reach input t before) child).mp edge)

theorem referenceBit_transport (single : input.moleculeGraph.SimpleBonded)
    (e : input.moleculeGraph.Aut) {fuel : Nat} (reference : input.Atom)
    (cursor : input.LocalizedRerootCursor fuel) :
    referenceBit input ((e : Equiv.Perm input.Atom) reference)
      (input.transportCursor single e cursor) = referenceBit input reference cursor := by
  simp only [referenceBit, transportCursor_occurrence, transportOccurrence_node, mapOfficialNode]
  have same : ∀ value : Option input.Atom,
      value.map (e : Equiv.Perm input.Atom) = some ((e : Equiv.Perm input.Atom) reference) ↔
        value = some reference := by
    intro value
    cases value <;> simp
  simp only [same]

/-- Ordinary sibling transport at any reached parent, with the original cutoff retained. -/
theorem ordinary_pair_transport (single : input.moleculeGraph.SimpleBonded)
    (e : input.moleculeGraph.Aut)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetra : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (t : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (parent left right : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (reach : Relation.ReflTransGen (E input) ⟨t, none⟩ parent)
    (childL : E input parent left) (childR : E input parent right)
    (a b a' b' : input.LocalizedRerootCompoundRule45Key)
    (ha : ordinaryKey? input t (input.molecularView descriptorMap t) left = some a)
    (hb : ordinaryKey? input t (input.molecularView descriptorMap t) right = some b)
    (ha' : ordinaryKey? input (input.transportOccurrence single e t)
      (input.molecularView (input.transportDescriptorMap e descriptorMap)
        (input.transportOccurrence single e t)) (input.transportCursor single e left) = some a')
    (hb' : ordinaryKey? input (input.transportOccurrence single e t)
      (input.molecularView (input.transportDescriptorMap e descriptorMap)
        (input.transportOccurrence single e t)) (input.transportCursor single e right) = some b') :
    (input.compareLocalizedRerootCompoundThroughRule5 a' b').ordering =
      (input.compareLocalizedRerootCompoundThroughRule5 a b).ordering := by
  have aligned := aligned_of_reach input t reach
  have reach' := reach_transport input single e t reach
  have childL' := (input.executableLocalizedRerootChildren_transport_mem_iff single e aligned left).mp childL
  have childR' := (input.executableLocalizedRerootChildren_transport_mem_iff single e aligned right).mp childR
  unfold ordinaryKey? at ha hb ha' hb'
  rw [ordinary_eq_virtual descriptorMap t reach childL] at ha
  rw [ordinary_eq_virtual descriptorMap t reach childR] at hb
  rw [ordinary_eq_virtual _ _ reach' childL', input.transportOccurrence_address_length,
    cutMap_transport input] at ha'
  rw [ordinary_eq_virtual _ _ reach' childR', input.transportOccurrence_address_length,
    cutMap_transport input] at hb'
  exact actual_pair_ordering_transport input single e (cutMap descriptorMap t.1.address.length)
    (cutMap_tetrahedral descriptorMap tetra _) parent left right aligned childL childR
    a b a' b' ha hb ha' hb'

/-- The source-side common parent window supplies a linear order for all its actual children. -/
theorem deepKey_compare (single : input.moleculeGraph.SimpleBonded)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetra : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (t : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (parent left right : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (reach : Relation.ReflTransGen (E input) ⟨t, none⟩ parent)
    (childL : E input parent left) (childR : E input parent right)
    (fallback : CompleteLigandRule5Key) (a b : input.LocalizedRerootCompoundRule45Key)
    (ha : ordinaryKey? input t (input.molecularView descriptorMap t) left = some a)
    (hb : ordinaryKey? input t (input.molecularView descriptorMap t) right = some b) :
    (input.compareLocalizedRerootCompoundThroughRule5 a b).ordering =
      @compare CompleteLigandRule5Key (inferInstance : LinearOrder CompleteLigandRule5Key).toOrd
        (deepKey descriptorMap t fallback parent left)
        (deepKey descriptorMap t fallback parent right) := by
  change left ∈ input.executableLocalizedRerootChildren parent at childL
  change right ∈ input.executableLocalizedRerootChildren parent at childR
  simp only [deepKey, dif_pos childL, dif_pos childR]
  exact (virtual_sibling_compare descriptorMap tetra single t parent left right reach childL childR
    _ _ (childStages_width_le descriptorMap t _ _ childL)
    (childStages_depth_le descriptorMap t _ _ childL)
    (childStages_width_le descriptorMap t _ _ childR)
    (childStages_depth_le descriptorMap t _ _ childR) ha hb).trans
    (linear_compare_eq _ completeLigandRule5Key_compare_lt_iff
      completeLigandRule5Key_compare_eq_iff _ _)

/-- Actual successful marker builds transport at every reachable cursor and every common layout
and marker fuel. Ordinary ordering and all marker observations are derived. -/
theorem build_marker_transport (single : input.moleculeGraph.SimpleBonded)
    (e : input.moleculeGraph.Aut)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetra : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (t : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (reference : input.Atom) (W D : Nat) :
    ∀ fuel (cursor : input.LocalizedRerootCursor (retainedCarrierFuel input)),
      Relation.ReflTransGen (E input) ⟨t, none⟩ cursor →
      ∀ a b : PromotedKey input,
        build? input t (input.molecularView descriptorMap t) reference W D fuel cursor = some a →
        build? input (input.transportOccurrence single e t)
          (input.molecularView (input.transportDescriptorMap e descriptorMap)
            (input.transportOccurrence single e t)) ((e : Equiv.Perm input.Atom) reference)
          W D fuel (input.transportCursor single e cursor) = some b →
        b.marker = a.marker := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor reach a b ha hb
      simp only [build?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        executableLocalizedRerootChildren?_eq_some, Option.some.injEq] at ha hb
      obtain ⟨pa, _, ca, _, restA⟩ := ha
      obtain ⟨pb, _, cb, _, restB⟩ := hb
      split at restA
      · split at restB
        · cases Option.some.inj restA
          cases Option.some.inj restB
          simp only [referenceBit_transport]
        · cases restB
      · cases restA
  | succ fuel ih =>
      intro cursor reach a b ha hb
      simp only [build?, Option.bind_eq_bind, Option.bind_eq_some_iff,
        executableLocalizedRerootChildren?_eq_some, Option.some.injEq] at ha hb
      obtain ⟨pa, _, ca, caEq, keys, keysEq, sameA⟩ := ha
      obtain ⟨pb, _, cb, cbEq, imageKeys, imageKeysEq, sameB⟩ := hb
      subst caEq
      subst cbEq
      subst sameA
      subst sameB
      let f := build? input t (input.molecularView descriptorMap t) reference W D fuel
      let f' := build? input (input.transportOccurrence single e t)
        (input.molecularView (input.transportDescriptorMap e descriptorMap)
          (input.transportOccurrence single e t)) ((e : Equiv.Perm input.Atom) reference) W D fuel
      let prior := deepKey descriptorMap t (default : CompleteLigandRule5Key) cursor
      let mark := fun c => ((f c).map PromotedKey.marker).getD []
      let image := input.transportCursor single e (fuel := retainedCarrierFuel input)
      let preimage := input.transportCursor single (e⁻¹) (fuel := retainedCarrierFuel input)
      have aligned := aligned_of_reach input t reach
      have preMember : ∀ c ∈ input.executableLocalizedRerootChildren (image cursor),
          preimage c ∈ input.executableLocalizedRerootChildren cursor := by
        intro c hc
        apply (input.executableLocalizedRerootChildren_transport_mem_iff single e aligned
          (preimage c)).mpr
        simpa only [image, preimage, transportCursor_apply_inv] using hc
      have sourceSorted := sorted_markers_mapM input
        (input.executableLocalizedRerootChildren cursor) f keys keysEq prior default mark
        (by
          intro x hx y hy kx ky hkx hky
          exact deepKey_compare input single descriptorMap tetra t cursor x y reach hx hy _ _ _
            (build?_prior input t _ reference W D fuel x kx hkx)
            (build?_prior input t _ reference W D fuel y ky hky))
        (by
          intro x _ k hk
          simp only [mark, hk, Option.map_some, Option.getD_some])
      have imageSorted := sorted_markers_mapM input
        (input.executableLocalizedRerootChildren (image cursor)) f' imageKeys imageKeysEq
        (fun c => prior (preimage c)) default (fun c => mark (preimage c))
        (by
          intro x hx y hy kx ky hkx hky
          have hx₀ := preMember x hx
          have hy₀ := preMember y hy
          obtain ⟨kx₀, hkx₀⟩ := mapM_available f _ _ keysEq _ hx₀
          obtain ⟨ky₀, hky₀⟩ := mapM_available f _ _ keysEq _ hy₀
          have ox := build?_prior input t _ reference W D fuel (preimage x) kx₀ hkx₀
          have oy := build?_prior input t _ reference W D fuel (preimage y) ky₀ hky₀
          have ox' := build?_prior input (input.transportOccurrence single e t) _
            ((e : Equiv.Perm input.Atom) reference) W D fuel x kx hkx
          have oy' := build?_prior input (input.transportOccurrence single e t) _
            ((e : Equiv.Perm input.Atom) reference) W D fuel y ky hky
          have transported := ordinary_pair_transport input single e descriptorMap tetra t cursor
            (preimage x) (preimage y) reach hx₀ hy₀ kx₀.prior ky₀.prior kx.prior ky.prior ox oy
            (by simpa only [preimage, transportCursor_apply_inv] using ox')
            (by simpa only [preimage, transportCursor_apply_inv] using oy')
          exact transported.trans
            (deepKey_compare input single descriptorMap tetra t cursor _ _ reach hx₀ hy₀ _ _ _ ox oy))
        (by
          intro x hx k hk
          have hx₀ := preMember x hx
          obtain ⟨k₀, hk₀⟩ := mapM_available f _ _ keysEq _ hx₀
          have eq := ih (preimage x) (reach.tail hx₀) k₀ k hk₀
            (by simpa only [preimage, transportCursor_apply_inv] using hk)
          simpa only [mark, hk₀, Option.map_some, Option.getD_some] using eq)
      have childrenPerm := input.executableLocalizedRerootChildren_transport_perm single e aligned
      have columnPerm :
          ((input.executableLocalizedRerootChildren (image cursor)).map
            fun c => toLex (prior (preimage c), mark (preimage c))).Perm
          ((input.executableLocalizedRerootChildren cursor).map fun c => toLex (prior c, mark c)) := by
        simpa only [List.map_map, Function.comp_def, image, preimage, transportCursor_inv_apply]
          using childrenPerm.symm.map (fun c => toLex (prior (preimage c), mark (preimage c)))
      change assembleMarker W D _ ((sortKeys input imageKeys).map PromotedKey.marker) =
        assembleMarker W D _ ((sortKeys input keys).map PromotedKey.marker)
      rw [referenceBit_transport, sourceSorted, imageSorted,
        Certificate.CanonicalSphereKey.sortDesc_eq_of_perm columnPerm]

/-- The actual promoted comparison of root-frame children transports, with build success
derived from their executable membership rather than supplied as a premise. -/
theorem compareAt_transport (single : input.moleculeGraph.SimpleBonded)
    (e : input.moleculeGraph.Aut)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetra : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (t : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (reference : input.Atom) (W D : Nat)
    (left right : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (childL : left ∈ input.executableLocalizedRerootChildren ⟨t, none⟩)
    (childR : right ∈ input.executableLocalizedRerootChildren ⟨t, none⟩) :
    compareAt? input (input.transportOccurrence single e t)
      (input.molecularView (input.transportDescriptorMap e descriptorMap)
        (input.transportOccurrence single e t)) ((e : Equiv.Perm input.Atom) reference) W D
      (input.transportCursor single e left) (input.transportCursor single e right) =
    compareAt? input t (input.molecularView descriptorMap t) reference W D left right := by
  have aligned : input.cursorPreviousRootAligned (⟨t, none⟩ : input.LocalizedRerootCursor _) :=
    input.cursorPreviousRootAligned_of_none _ rfl
  have childL' := (input.executableLocalizedRerootChildren_transport_mem_iff single e aligned left).mp childL
  have childR' := (input.executableLocalizedRerootChildren_transport_mem_iff single e aligned right).mp childR
  have validL := input.localizedRerootChild_valid _ left _
    (input.executableLocalizedRerootChildren_declarative _) childL
  have validR := input.localizedRerootChild_valid _ right _
    (input.executableLocalizedRerootChildren_declarative _) childR
  have validL' := input.localizedRerootChild_valid _ _ _
    (input.executableLocalizedRerootChildren_declarative _) childL'
  have validR' := input.localizedRerootChild_valid _ _ _
    (input.executableLocalizedRerootChildren_declarative _) childR'
  obtain ⟨a, ha⟩ := build?_exists input t (input.molecularView descriptorMap t) reference W D left validL
  obtain ⟨b, hb⟩ := build?_exists input t (input.molecularView descriptorMap t) reference W D right validR
  obtain ⟨a', ha'⟩ := build?_exists input (input.transportOccurrence single e t)
    (input.molecularView (input.transportDescriptorMap e descriptorMap)
      (input.transportOccurrence single e t)) ((e : Equiv.Perm input.Atom) reference) W D
    (input.transportCursor single e left) validL'
  obtain ⟨b', hb'⟩ := build?_exists input (input.transportOccurrence single e t)
    (input.molecularView (input.transportDescriptorMap e descriptorMap)
      (input.transportOccurrence single e t)) ((e : Equiv.Perm input.Atom) reference) W D
    (input.transportCursor single e right) validR'
  have markerL := build_marker_transport input single e descriptorMap tetra t reference W D
    _ left (Relation.ReflTransGen.single childL) a a' ha ha'
  have markerR := build_marker_transport input single e descriptorMap tetra t reference W D
    _ right (Relation.ReflTransGen.single childR) b b' hb hb'
  have ordinary := ordinary_pair_transport input single e descriptorMap tetra t ⟨t, none⟩ left right
    Relation.ReflTransGen.refl childL childR a.prior b.prior a'.prior b'.prior
    (build?_prior input t _ reference W D _ left a ha)
    (build?_prior input t _ reference W D _ right b hb)
    (build?_prior input _ _ ((e : Equiv.Perm input.Atom) reference) W D _ _ a' ha')
    (build?_prior input _ _ ((e : Equiv.Perm input.Atom) reference) W D _ _ b' hb')
  simp only [compareAt?, ha, hb, ha', hb', Option.bind_eq_bind, Option.bind_some]
  simp only [compareKeys, ordinary, markerL, markerR]

end
end TetraStereo.OneCenter.LocalizedChemicalRingPromotedTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedTransport.ordinary_pair_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedTransport.deepKey_compare
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedTransport.build_marker_transport
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPromotedTransport.compareAt_transport
