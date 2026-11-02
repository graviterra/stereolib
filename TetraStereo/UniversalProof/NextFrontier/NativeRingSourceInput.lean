import TetraStereo.UniversalProof.NextFrontier.NativeRingRuntimeAtoms
import TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NativeRingSourceInput

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingRuntimeGraphFacts
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering

theorem expanded_known_elements (n : Nat) (parity : TetrahedralInputParity) :
    ∀ spec ∈ (expanded n parity).atoms, spec.element ≠ .wildcard := by
  intro spec member unknown
  obtain ⟨mass, known⟩ := expanded_rule2_masses n parity spec member
  simp [rule2MassPico?, unknown] at known

def ringInput (n : Nat) (parity : TetrahedralInputParity) : OrdinarySourceInput (expanded n parity) :=
  ⟨(expanded_stereochemical_admissible n parity).1.1,
    (expanded_stereochemical_admissible n parity).2,
    expanded_known_elements n parity, expanded_bonds_single n parity⟩

/-- The independent source is the actual converter output on the actual expanded physical graph. -/
def ringSource (n : Nat) (parity : TetrahedralInputParity) : AuthoritativeChemicalInput :=
  ownSource (expanded n parity)

theorem ring_source_conversion (n : Nat) (parity : TetrahedralInputParity) :
    (expanded n parity).toAuthoritativeChemicalInput? = some (ringSource n parity) :=
  actual_source_conversion _ (ringInput n parity)

theorem ring_annotation_agreement (n : Nat) (parity : TetrahedralInputParity) :
    RawAnnotationAgreement (expanded n parity) (ringSource n parity) :=
  actual_annotation_agreement _ (ringInput n parity)

theorem ring_source_no_double (n : Nat) (parity : TetrahedralInputParity) :
    (ringSource n parity).NoAromaticCanonicalOrdinaryDoubleBond :=
  actual_source_no_double _ (ringInput n parity)

def ringCenter (n : Nat) (parity : TetrahedralInputParity) :
    (ringSource n parity).AromaticCanonicalTetrahedralCenter :=
  actualCenter _ (ringInput n parity)
    ⟨0, by rw [expanded_atom_count]; omega⟩
    (materializedAtomSpec (taggedCarbon parity))
    (expanded_original_atom n parity 0 _ (ringRaw_atomAt_zero n parity))
    (by trivial) (by rw [expanded_root_written_row]; rfl)

@[simp] theorem ring_center_index (n : Nat) (parity : TetrahedralInputParity) :
    (ringCenter n parity).1.val = 0 := rfl

def ringRecordDomain (n : Nat) (parity : TetrahedralInputParity) (atom : Nat) :
    SourceRecordDomain (expanded n parity) atom :=
  ⟨(expanded_stereochemical_admissible n parity).1.1,
    recordNeighbors_nodup _ (expanded_stereochemical_admissible n parity).1.2 atom,
    fun bond member _ => expanded_bonds_single n parity bond member⟩

theorem ring_four_records (n : Nat) (parity : TetrahedralInputParity) :
    (recordNeighbors (expanded n parity) (ringCenter n parity).1.val).length = 4 :=
  (expanded_root_records n parity).length_eq

noncomputable def ringFrame (n : Nat) (parity : TetrahedralInputParity) (carrierFuel : Nat) :
    (ringSource n parity).AromaticCanonicalOccurrenceFourLigandFrame carrierFuel :=
  actualFrame (expanded n parity) (ringSource n parity) (ring_annotation_agreement n parity).1
    carrierFuel (ringCenter n parity) (ringRecordDomain n parity 0) (ring_four_records n parity)

theorem ring_roots_real (n : Nat) (parity : TetrahedralInputParity) (carrierFuel : Nat) :
    OccurrenceRootsReal (ringSource n parity) (ringFrame n parity carrierFuel) :=
  actual_roots_real _ _ (ring_annotation_agreement n parity).1 carrierFuel (ringCenter n parity)
    (ringRecordDomain n parity 0) (ring_four_records n parity)

theorem ring_frame_cursor_mem (n : Nat) (parity : TetrahedralInputParity)
    (carrierFuel : Nat) (slot : Fin 4) :
    (ringFrame n parity carrierFuel).cursorAt slot ∈
      finalOccurrenceRoots (ringSource n parity) carrierFuel (ringCenter n parity) :=
  actual_frame_cursor_mem (expanded n parity) (ringSource n parity)
    (ring_annotation_agreement n parity).1 carrierFuel (ringCenter n parity)
    (ringRecordDomain n parity 0) (ring_four_records n parity) slot

/-- Readiness is proved for every dependency view, without requesting a successful key frame as
an input. The subsequent source projection must still establish the ring's C/C distinction. -/
theorem ring_view_keys_exist (n : Nat) (parity : TetrahedralInputParity) (carrierFuel : Nat)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence carrierFuel (ringCenter n parity))) :
    ∃ keys, (ringSource n parity).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      ((ringSource n parity).aromaticCanonicalFinalOccurrence carrierFuel (ringCenter n parity))
      view (2 * (carrierFuel + 1)) (ringFrame n parity carrierFuel).roots = some keys :=
  actual_source_key_frame_exists _ _ (ring_annotation_agreement n parity).1 carrierFuel
    (ringCenter n parity) (ringRecordDomain n parity 0) (ring_four_records n parity) view
    (ring_source_no_double n parity)

noncomputable def ringViewKeys (n : Nat) (parity : TetrahedralInputParity) (carrierFuel : Nat)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence carrierFuel (ringCenter n parity))) :
    (ringSource n parity).AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel :=
  Classical.choose (ring_view_keys_exist n parity carrierFuel view)

theorem ring_view_keys_computed (n : Nat) (parity : TetrahedralInputParity) (carrierFuel : Nat)
    (view : (ringSource n parity).AromaticCanonicalDependencyView
      ((ringSource n parity).aromaticCanonicalFinalOccurrence carrierFuel (ringCenter n parity))) :
    (ringSource n parity).buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      ((ringSource n parity).aromaticCanonicalFinalOccurrence carrierFuel (ringCenter n parity))
      view (2 * (carrierFuel + 1)) (ringFrame n parity carrierFuel).roots =
        some (ringViewKeys n parity carrierFuel view) :=
  Classical.choose_spec (ring_view_keys_exist n parity carrierFuel view)

end TetraStereo.UniversalProof.NativeRingSourceInput
