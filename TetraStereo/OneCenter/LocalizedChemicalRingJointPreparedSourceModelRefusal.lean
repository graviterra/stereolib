import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRefusalCharacterization
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Physical meaning of refusals in the unique independent recursive source model.
At a reached detected occurrence inside a tied root branch, a source-model refusal is equivalent
to an odd molecular symmetry fixing the history and every accumulated reference, and proper at
all centers outside the history. Thus refusals in the source equations have an independent
physical obstruction; they are not merely matching failures of two computations. The exact
tied-root-branch scope of the physical reconstruction theorem is retained.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelRefusal

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointPreparedSourceQueries (SourceQuery)
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence
open LocalizedChemicalRingJointPreparedRefusalCharacterization
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported charge calibrated in
/-- A source-model refusal has exactly the independent odd-boundary obstruction.
The query's reachability and real provenance come from its molecular domain, not extra premises. -/
theorem sourceModel_refusal_iff_oddBoundary {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (center : input.detectedMultiCenterMolecule.Center)
    (current : query.1.atom = center.1.val) (data : OccurrenceData input mol center query.1)
    (branch : TiedRootBranch input data.target) (boundary references : List input.Atom)
    (history : data.target.1.node.history.reverse = boundary ++ [center.1])
    (outside : center.1 ∉ boundary) :
    candidate (inputGeometry input) references query = none ↔
      OddBoundarySymmetry input cfg center boundary references := by
  rw [sourceModel_eq_actual input mol agreement admissible supported single model]
  exact refusal_iff_oddBoundary input mol agreement admissible supported single charge cfg
    calibrated center query.1 data query.2.1 query.2.2.1 current branch boundary references
    history outside

include agreement admissible supported charge calibrated in
/-- In the same physical branch scope, an independent source descriptor exists exactly when
no odd boundary symmetry exists. Both directions include the full accumulated reference list. -/
theorem sourceModel_success_iff_no_oddBoundary {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (center : input.detectedMultiCenterMolecule.Center)
    (current : query.1.atom = center.1.val) (data : OccurrenceData input mol center query.1)
    (branch : TiedRootBranch input data.target) (boundary references : List input.Atom)
    (history : data.target.1.node.history.reverse = boundary ++ [center.1])
    (outside : center.1 ∉ boundary) :
    (∃ descriptor, candidate (inputGeometry input) references query = some descriptor) ↔
      ¬ OddBoundarySymmetry input cfg center boundary references := by
  rw [sourceModel_eq_actual input mol agreement admissible supported single model]
  exact success_iff_no_oddBoundary input mol agreement admissible supported single charge cfg
    calibrated center query.1 data query.2.1 query.2.2.1 current branch boundary references
    history outside

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelRefusal

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelRefusal.sourceModel_refusal_iff_oddBoundary
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelRefusal.sourceModel_success_iff_no_oddBoundary
