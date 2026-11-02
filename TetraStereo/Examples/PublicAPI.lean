import TetraStereo.Engine.PublicAPI
import TetraStereo.Examples.OnePhenylethanol

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace PublicAPI

open OneCenter

noncomputable section

/-!
  Public-engine smoke tests.

  These examples intentionally consume `TetraStereo.Engine.PublicAPI`, not the raw deterministic
  research-kernel functions.  They are the demo-facing proof that a public descriptor success is a
  safe descriptor success.

  Descriptor calibration: the tetrahedral assignment uses the IUPAC convention in which a
  negative oriented volume denotes `R` (`RS.ofHandedness (-1) = RS.R`).  Consequently the canonical
  Cartesian *right*-hand realization of 1-phenylethanol carries descriptor `S`, and the *left*-hand
  realization carries descriptor `R`.  The historical theorem identifiers are retained below as
  aliases with their statements corrected; accurate identifiers are exported alongside them.
-/

/-- The public priority surface exposes the safe descriptor permutation for 1-phenylethanol. -/
theorem onePhenylethanol_publicPriority_permutation_eq_some :
    (Engine.descriptorPriority OnePhenylethanol.oneCenter).permutation? =
      some OnePhenylethanol.oneCenter.cipPermutationDescriptor := by
  simpa [Engine.descriptorPriority] using
    OnePhenylethanol.cipPermutationDescriptor?_eq_some

/-- The public-priority success implies resolved descriptor priorities, not a raw tie-break. -/
theorem onePhenylethanol_publicPriority_success_resolved :
    OnePhenylethanol.oneCenter.ResolvedCIPDescriptor :=
  (Engine.DescriptorPriorityResult.resolved_of_permutation_some
    (Engine.descriptorPriority OnePhenylethanol.oneCenter)
    onePhenylethanol_publicPriority_permutation_eq_some)

/-- The right-hand 1-phenylethanol realization has public safe descriptor `S`. -/
theorem onePhenylethanol_publicRS_right_eq_some_S :
    (Engine.descriptorRS OnePhenylethanol.oneCenter OnePhenylethanol.rightRealization).descriptor? =
      some RS.S := by
  simpa [Engine.descriptorRS] using
    OnePhenylethanol.rsCIP?_right_eq_some_S

/-- Historical API key retained; corrected statement: the right-hand descriptor is `S`. -/
theorem onePhenylethanol_publicRS_right_eq_some_R :
    (Engine.descriptorRS OnePhenylethanol.oneCenter OnePhenylethanol.rightRealization).descriptor? =
      some RS.S :=
  onePhenylethanol_publicRS_right_eq_some_S

/-- The left-hand 1-phenylethanol realization has public safe descriptor `R`. -/
theorem onePhenylethanol_publicRS_left_eq_some_R :
    (Engine.descriptorRS OnePhenylethanol.oneCenter OnePhenylethanol.leftRealization).descriptor? =
      some RS.R := by
  simpa [Engine.descriptorRS] using
    OnePhenylethanol.rsCIP?_left_eq_some_R

/-- Historical API key retained; corrected statement: the left-hand descriptor is `R`. -/
theorem onePhenylethanol_publicRS_left_eq_some_S :
    (Engine.descriptorRS OnePhenylethanol.oneCenter OnePhenylethanol.leftRealization).descriptor? =
      some RS.R :=
  onePhenylethanol_publicRS_left_eq_some_R

/-- The two distinct 1-phenylethanol realizations disagree at the public descriptor surface. -/
theorem onePhenylethanol_publicRS_right_descriptor_ne_left_descriptor :
    (Engine.descriptorRS OnePhenylethanol.oneCenter OnePhenylethanol.rightRealization).descriptor? ≠
      (Engine.descriptorRS OnePhenylethanol.oneCenter OnePhenylethanol.leftRealization).descriptor? := by
  rw [onePhenylethanol_publicRS_right_eq_some_S,
    onePhenylethanol_publicRS_left_eq_some_R]
  decide

/-- A public `S` result yields a certified assignment object for the right realization. -/
def onePhenylethanol_publicRightAssignment :
    Engine.CertifiedRSAssignment OnePhenylethanol.oneCenter OnePhenylethanol.rightRealization :=
  { descriptor := RS.S
    certificate := by
      exact (Engine.descriptorRS OnePhenylethanol.oneCenter OnePhenylethanol.rightRealization).safe_some
        onePhenylethanol_publicRS_right_eq_some_S }

/-- A certified public assignment implies resolved descriptor priorities. -/
theorem onePhenylethanol_publicRightAssignment_resolved :
    OnePhenylethanol.oneCenter.ResolvedCIPDescriptor :=
  onePhenylethanol_publicRightAssignment.resolved

/-- The public assignment can be converted into the existing theorem-artifact export format. -/
def onePhenylethanol_publicRightArtifact : LeanCertificateArtifact :=
  let base :=
    onePhenylethanol_publicRightAssignment.toCertificateArtifact
      "one_phenylethanol_public_right_rs"
      "(TetraStereo.Engine.descriptorRS TetraStereo.Examples.OnePhenylethanol.oneCenter TetraStereo.Examples.OnePhenylethanol.rightRealization).descriptor?"
      "TetraStereo.OneCenter.RS.S"
      "  exact TetraStereo.Examples.PublicAPI.onePhenylethanol_publicRS_right_eq_some_S"
  { base with
    theoremExport :=
      { base.theoremExport with
        imports :=
          [ "TetraStereo.OneCenter.CertificateExport"
          , "TetraStereo.Engine.PublicAPI"
          , "TetraStereo.Examples.OnePhenylethanol"
          , "TetraStereo.Examples.PublicAPI"
          ] } }

/-- The public API artifact is still a checked Lean certificate artifact. -/
theorem onePhenylethanol_publicRightArtifact_checked :
    onePhenylethanol_publicRightArtifact.claim :=
  onePhenylethanol_publicRightArtifact.checked

end
end PublicAPI
end Examples
end TetraStereo
