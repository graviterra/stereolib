import TetraStereo.Engine.Intake
import TetraStereo.OneCenter.ProductionCIPTwoViewSemantics

set_option autoImplicit false

namespace TetraStereo
namespace Engine

noncomputable section

open OneCenter
open OneCenter.DeclarativeCIP

namespace CertifiedIntakeSuccess

/-- The normalized raw molecule consumed by proof-facing production after safe intake. -/
def productionMolecule {request : ImportRequest}
    (success : CertifiedIntakeSuccess request) : RawMolecule :=
  success.result.normalized.normalized.parsed

/-- Safe intake certifies the exact structural contract required by the hierarchy realization
proof on the normalized molecule actually consumed by production. -/
theorem productionMolecule_admissible {request : ImportRequest}
    (success : CertifiedIntakeSuccess request) : success.productionMolecule.Admissible :=
  success.normalizedAdmissible

/-- End-to-end bridge from certified public intake to the independent paired-view specification.

No caller-supplied well-formedness or bond-record uniqueness premise remains: those hypotheses are
reflected once at intake and preserved through normalization.  Successful complete compilation and
the positive root relation remain explicit semantic premises rather than being manufactured by the
adapter. -/
theorem branchCanonicalKey?_certifiedPairedViewFaithfulExactRule1a
    {request : ImportRequest} (success : CertifiedIntakeSuccess request)
    (center ligand : Fin success.productionMolecule.atomCount)
    (key : RawMolecule.CanonicalBranchKey)
    (hkey : branchCanonicalKey? success.productionMolecule center ligand = some key)
    (hcomplete : key.complete = true)
    (hrootBond :
      (success.productionMolecule.constitutionalViews center ligand).expansion.Adj center ligand) :
    RawMolecule.PairedViewFaithfulExactRule1a
      success.productionMolecule center ligand key := by
  exact success.productionMolecule.branchCanonicalKey?_certifiedPairedViewFaithfulExactRule1a
    center ligand key success.productionMolecule_admissible.1
      success.productionMolecule_admissible.2 hkey hcomplete hrootBond

end CertifiedIntakeSuccess

end
end Engine
end TetraStereo
