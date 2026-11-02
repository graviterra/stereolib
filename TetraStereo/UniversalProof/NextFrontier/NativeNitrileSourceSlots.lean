import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceFrames

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

-- Avoid reducing the complete converter during slot elaboration.
attribute [local irreducible] expanded

def nitrileAtom (parity : TetrahedralInputParity) (n index : Nat)
    (bound : index < (expanded parity n).atomCount) :
    (nitrileSource parity n).AromaticCanonicalAtom :=
  (expanded parity n).convertedAtomIndex (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n).1 ⟨index, bound⟩

theorem nitrile_role_slot_exists (parity : TetrahedralInputParity) (n carrierFuel atom : Nat)
    (member : atom ∈ [n + 7, 1, 2, 4]) :
    ∃ slot : Fin 4, nitrileSlotAtom parity n carrierFuel slot = atom := by
  obtain ⟨slot, _, equal⟩ := List.mem_map.mp ((nitrile_slot_ids parity n carrierFuel).mem_iff.mpr member)
  exact ⟨slot, equal⟩

noncomputable def nitrileRoleSlot (parity : TetrahedralInputParity) (n carrierFuel atom : Nat)
    (member : atom ∈ [n + 7, 1, 2, 4]) : Fin 4 :=
  Classical.choose (nitrile_role_slot_exists parity n carrierFuel atom member)

theorem nitrile_role_slot_index (parity : TetrahedralInputParity) (n carrierFuel atom : Nat)
    (member : atom ∈ [n + 7, 1, 2, 4]) :
    nitrileSlotAtom parity n carrierFuel (nitrileRoleSlot parity n carrierFuel atom member) = atom :=
  Classical.choose_spec (nitrile_role_slot_exists parity n carrierFuel atom member)

theorem nitrile_role_root_node (parity : TetrahedralInputParity) (n carrierFuel atom : Nat)
    (member : atom ∈ [n + 7, 1, 2, 4]) (bound : atom < (expanded parity n).atomCount) :
    ((nitrileFrame parity n carrierFuel).cursorAt
      (nitrileRoleSlot parity n carrierFuel atom member)).occurrence.1.node =
      OfficialCIPNode.rootFromEdge (nitrileCenter parity n).1 (nitrileAtom parity n atom bound) := by
  exact actual_slot_root_node (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n).1 carrierFuel (nitrileCenter parity n)
    (nitrileRecordDomain parity n) (nitrile_four_records parity n)
    (nitrileRoleSlot parity n carrierFuel atom member) (nitrileAtom parity n atom bound)
    (nitrile_role_slot_index parity n carrierFuel atom member)

theorem nitrile_frame_cursor_mem (parity : TetrahedralInputParity) (n carrierFuel : Nat)
    (slot : Fin 4) :
    (nitrileFrame parity n carrierFuel).cursorAt slot ∈
      finalOccurrenceRoots (nitrileSource parity n) carrierFuel (nitrileCenter parity n) :=
  actual_frame_cursor_mem (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n).1 carrierFuel (nitrileCenter parity n)
    (nitrileRecordDomain parity n) (nitrile_four_records parity n) slot

theorem nitrile_roots_real (parity : TetrahedralInputParity) (n carrierFuel : Nat) :
    OccurrenceRootsReal (nitrileSource parity n) (nitrileFrame parity n carrierFuel) :=
  actual_roots_real _ _ (expanded_source_annotation_agreement parity n).1 carrierFuel
    (nitrileCenter parity n) (nitrileRecordDomain parity n) (nitrile_four_records parity n)

noncomputable def nitrileViewKeys (parity : TetrahedralInputParity) (n carrierFuel : Nat)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence carrierFuel (nitrileCenter parity n))) :
    (nitrileSource parity n).AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel :=
  Classical.choose (nitrile_source_keys_exist parity n carrierFuel view)

theorem nitrile_view_keys_computed (parity : TetrahedralInputParity) (n carrierFuel : Nat)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence carrierFuel (nitrileCenter parity n))) :
    (nitrileSource parity n).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence carrierFuel (nitrileCenter parity n))
      view (2 * (carrierFuel + 1)) (nitrileFrame parity n carrierFuel).roots =
        some (nitrileViewKeys parity n carrierFuel view) :=
  Classical.choose_spec (nitrile_source_keys_exist parity n carrierFuel view)

noncomputable def sourceNitrileCursor (parity : TetrahedralInputParity) (n : Nat) :
    (nitrileSource parity n).AromaticCanonicalRerootCursor 1 :=
  (nitrileFrame parity n 1).cursorAt (nitrileRoleSlot parity n 1 2 (by simp))

noncomputable def sourceAminoCursor (parity : TetrahedralInputParity) (n : Nat) :
    (nitrileSource parity n).AromaticCanonicalRerootCursor 1 :=
  (nitrileFrame parity n 1).cursorAt (nitrileRoleSlot parity n 1 4 (by simp))

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
