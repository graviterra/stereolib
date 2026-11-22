import TetraStereo.Engine.LocalizedChemicalRingExactCertificate
import TetraStereo.OneCenter.LocalizedChemicalRingFrozenChronology

set_option autoImplicit false

namespace TetraStereo.Engine.LocalizedChemicalRing

open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRingPhysicalAdmission (detectedCoordinateCfg)

open LocalizedChemicalRingRegeneratedLifetime (frames)
open LocalizedChemicalRingJointPreparedSourceModelExistence (finalQuery)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingJointPreparedSourceQueries (SourceQuery)
open LocalizedGenericMarkedRecalculation (Geometry mirror)

open LocalizedChemicalRingFrozenChronology (solution Impact)

/-- The witness required of an actual center when its outcome differs from the
unmarked frozen source solution. It identifies both the selected atom and the
strictly deeper query whose descriptor changes under that atom. -/
def FrozenOutcomeImpact (input : Input)
    (p : LocalizedChemicalRingJointPreparedSourceModel.Profile input.certified input.molecule)
    (c : input.certified.detectedMultiCenterMolecule.Center) (outcome : Option LocalizedAuxiliaryLabel) : Prop :=
    let frame := frames input.certified input.molecule input.agreement input.admissible input.supported input.single
    let q := finalQuery input.certified input.molecule input.agreement c
    let g := inputGeometry input.certified
    outcome ≠ solution input.certified input.molecule input.single frame g q →
      ∃ (parent : SourceQuery input.certified input.molecule) (side : Geometry),
        (parent = q ∨ LocalizedMarkedTerminalReferenceScope.StrictDescendant input.molecule q.1 parent.1) ∧
        (side = g ∨ side = mirror g) ∧ Impact input.certified input.molecule input.single frame p parent side

/-- A change to a public report entry under frozen chronology requires a changed
promoted reading and a changed downstream label for the atom selected in that trial. -/
theorem ExactSourceMeaning.frozen_disagreement {profile : Profile} {input : Input} {cfg p}
    (meaning : ExactSourceMeaning profile input cfg p)
    (c : input.certified.detectedMultiCenterMolecule.Center) (outcome : Option LocalizedAuxiliaryLabel)
    (member : (c.1.val, outcome) ∈ analyze profile input) :
    FrozenOutcomeImpact input p c outcome := by
  intro different
  apply LocalizedChemicalRingFrozenChronology.report_impact input.certified input.molecule
    input.admissible input.single _ p meaning.model
  rw [analyze_eq_prepared, LocalizedChemicalRingJointPreparedReport.mem_analyze_at_center_iff,
    LocalizedChemicalRingJointPreparedSourceModelExistence.assignCenter_eq_sourceModel input.certified
      input.molecule input.agreement input.admissible input.supported input.single meaning.model] at member
  rw [member]
  exact different

end TetraStereo.Engine.LocalizedChemicalRing
assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.ExactSourceMeaning.frozen_disagreement
