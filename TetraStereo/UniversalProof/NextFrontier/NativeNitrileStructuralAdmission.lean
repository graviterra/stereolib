import TetraStereo.UniversalProof.NextFrontier.NativeNitrilePhysicalAdmission
import TetraStereo.UniversalProof.NextFrontier.NativeNitrileSourceInput

set_option autoImplicit false

namespace TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery

def expandedSourceInput (parity : TetrahedralInputParity) (n : Nat) :
    NativeNitrileSourceInput.SupportedSourceInput (expanded parity n) where
  well := (expanded_admissible parity n).1
  written := expanded_written_exact parity n
  known := expanded_known_elements parity n
  resolved := by
    intro bond retained
    rcases expanded_bond_kinds parity n bond retained with single | triple
    · rw [single]; decide
    · rw [triple]; decide
  nondirectional := by
    intro bond retained
    rcases expanded_bond_kinds parity n bond retained with single | triple
    · rw [single]; rfl
    · rw [triple]; rfl


theorem expanded_source_conversion (parity : TetrahedralInputParity) (n : Nat) :
    (expanded parity n).toAuthoritativeChemicalInput? = some (ownSource (expanded parity n)) :=
  NativeNitrileSourceInput.actual_conversion _ (expanded_known_elements parity n)

theorem expanded_source_annotation_agreement (parity : TetrahedralInputParity) (n : Nat) :
    SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement.RawAnnotationAgreement
      (expanded parity n) (ownSource (expanded parity n)) :=
  NativeNitrileSourceInput.actual_annotation_agreement _ (expandedSourceInput parity n)

theorem expanded_source_no_double (parity : TetrahedralInputParity) (n : Nat) :
    (ownSource (expanded parity n)).NoAromaticCanonicalOrdinaryDoubleBond :=
  NativeNitrileSourceInput.actual_source_no_double _
    (expanded_known_elements parity n) (expanded_bond_kinds parity n)

end TetraStereo.UniversalProof.NextFrontier.NativeNitrileFamily
