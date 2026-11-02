import TetraStereo.UniversalProof.NextFrontier.NativeNitrileStructuralAdmission
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileRecordGeometry
import TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

-- Source-frame proofs reuse the physical expansion lemmas without unfolding the graph.
attribute [local irreducible] expanded

/-- The source is the actual independent conversion of the production hydrogen expansion. -/
def nitrileSource (parity : TetrahedralInputParity) (n : Nat) : AuthoritativeChemicalInput :=
  ownSource (expanded parity n)

def nitrileCenter (parity : TetrahedralInputParity) (n : Nat) :
    (nitrileSource parity n).AromaticCanonicalTetrahedralCenter :=
  NativeNitrileSourceInput.actualCenter _ (expandedSourceInput parity n)
    ⟨0, by rw [expanded_atomCount]; omega⟩ (materializedAtomSpec (centerSpec parity))
    (expanded_original_atom parity n 0 (centerSpec parity) (raw_center parity n))
    (by trivial) (by rw [expanded_center_row]; rfl)

@[simp] theorem nitrile_center_index (parity : TetrahedralInputParity) (n : Nat) :
    (nitrileCenter parity n).1.val = 0 := rfl

def nitrileRecordDomain (parity : TetrahedralInputParity) (n : Nat) :
    SourceRecordDomain (expanded parity n) (nitrileCenter parity n).1.val :=
  ⟨(expanded_admissible parity n).1, expanded_records_nodup parity n 0,
    expanded_incident_single parity n 0 (by decide) (by decide)⟩

theorem nitrile_four_records (parity : TetrahedralInputParity) (n : Nat) :
    (recordNeighbors (expanded parity n) (nitrileCenter parity n).1.val).length = 4 :=
  (expanded_center_records parity n).length_eq

noncomputable def nitrileFrame (parity : TetrahedralInputParity) (n carrierFuel : Nat) :
    (nitrileSource parity n).AromaticCanonicalOccurrenceFourLigandFrame carrierFuel :=
  actualFrame (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n).1 carrierFuel (nitrileCenter parity n)
    (nitrileRecordDomain parity n) (nitrile_four_records parity n)

theorem nitrile_returned_frame (parity : TetrahedralInputParity) (n carrierFuel : Nat) :
    (nitrileSource parity n).aromaticCanonicalOccurrenceLigandFrame?
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence carrierFuel (nitrileCenter parity n)) =
      some (nitrileFrame parity n carrierFuel).roots :=
  (actual_returned_four_roots _ _ (expanded_source_annotation_agreement parity n).1
    carrierFuel (nitrileCenter parity n) (nitrileRecordDomain parity n)
    (nitrile_four_records parity n)).1

noncomputable def nitrileSlotAtom (parity : TetrahedralInputParity) (n carrierFuel : Nat) :
    Fin 4 → Nat :=
  slotAtomID (expanded parity n) (nitrileSource parity n)
    (expanded_source_annotation_agreement parity n).1 carrierFuel (nitrileCenter parity n)
    (nitrileRecordDomain parity n) (nitrile_four_records parity n)

theorem nitrile_slot_ids (parity : TetrahedralInputParity) (n carrierFuel : Nat) :
    ((List.finRange 4).map (nitrileSlotAtom parity n carrierFuel)).Perm [n + 7, 1, 2, 4] :=
  (actual_slot_ids_perm _ _ (expanded_source_annotation_agreement parity n).1 carrierFuel
    (nitrileCenter parity n) (nitrileRecordDomain parity n) (nitrile_four_records parity n)).trans
    (expanded_center_records parity n)

theorem nitrile_slot_ids_injective (parity : TetrahedralInputParity) (n carrierFuel : Nat) :
    Function.Injective (nitrileSlotAtom parity n carrierFuel) :=
  actual_slot_ids_injective _ _ (expanded_source_annotation_agreement parity n).1 carrierFuel
    (nitrileCenter parity n) (nitrileRecordDomain parity n) (nitrile_four_records parity n)

/-- Key construction succeeds for every dependency view and every carrier depth. This is
readiness only; neither the second-sphere projection nor the final scheduled descriptor is
assumed here. -/
theorem nitrile_source_keys_exist (parity : TetrahedralInputParity) (n carrierFuel : Nat)
    (view : (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence carrierFuel (nitrileCenter parity n))) :
    ∃ keys, (nitrileSource parity n).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence carrierFuel (nitrileCenter parity n))
      view (2 * (carrierFuel + 1)) (nitrileFrame parity n carrierFuel).roots = some keys :=
  actual_source_key_frame_exists _ _ (expanded_source_annotation_agreement parity n).1 carrierFuel
    (nitrileCenter parity n) (nitrileRecordDomain parity n) (nitrile_four_records parity n) view
    (expanded_source_no_double parity n)

def nitrileConstitutionalView (parity : TetrahedralInputParity) (n carrierFuel : Nat) :
    (nitrileSource parity n).AromaticCanonicalDependencyView
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence carrierFuel (nitrileCenter parity n)) :=
  fun _ _ => none

noncomputable def nitrileKeys (parity : TetrahedralInputParity) (n carrierFuel : Nat) :
    (nitrileSource parity n).AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel :=
  Classical.choose (nitrile_source_keys_exist parity n carrierFuel
    (nitrileConstitutionalView parity n carrierFuel))

theorem nitrile_keys_computed (parity : TetrahedralInputParity) (n carrierFuel : Nat) :
    (nitrileSource parity n).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      ((nitrileSource parity n).aromaticCanonicalFinalOccurrence carrierFuel (nitrileCenter parity n))
      (nitrileConstitutionalView parity n carrierFuel) (2 * (carrierFuel + 1))
      (nitrileFrame parity n carrierFuel).roots = some (nitrileKeys parity n carrierFuel) :=
  Classical.choose_spec (nitrile_source_keys_exist parity n carrierFuel
    (nitrileConstitutionalView parity n carrierFuel))

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
