import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The unique molecular source model, the actual detected-center report and physical
classification meet in one endpoint. Recursive auxiliary labels, accumulated reference
contexts and mirror-side regeneration are derived through the source-model existence proof.
At each properly distinguishable center, the actual descriptor exists and is lowercase exactly
when the independent physical pair count is one. The exact descriptor, including its absolute
letter, equals the unique source-model value. This is correctness for the stated accumulated
reference profile; no assertion of normative IUPAC reference-policy fidelity is made here.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelPhysicalReport

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence
open LocalizedChemicalRingJointPreparedReport
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open MultiCenterMolecule (PairwiseProperDistinguishable)

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

include admissible supported charge calibrated in
/-- Actual report membership, exact independent source-model value and independent physical
classification are obtained together, with no auxiliary-label or execution-success premises. -/
theorem sourceModel_detected_entry {candidate : Profile input mol}
    (model : SourceModel input mol single candidate)
    (center : input.detectedMultiCenterMolecule.Center)
    (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg center) :
    ∃ descriptor,
      candidate (inputGeometry input) [] (finalQuery input mol agreement center) =
        some descriptor ∧
      (center.1.val, some descriptor) ∈ analyze input mol ∧
      (descriptor.IsLowercase ↔
        physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg center = 1) := by
  obtain ⟨descriptor, member, physical⟩ := detected_entry_physical input mol
    agreement admissible supported single charge cfg calibrated center properDistinct
  have computed := (mem_analyze_at_center_iff input mol center _).mp member
  rw [assignCenter_eq_sourceModel input mol agreement admissible supported single model] at computed
  exact ⟨descriptor, computed, member, physical⟩

include admissible supported charge calibrated in
/-- End-to-end ring endpoint. There is exactly one solution of the independent recursive
equations; the complete actual report is its final-query projection, including refusals;
every physically properly distinguishable detected center has a descriptor with the exact
physical lowercase criterion. Rings and stereochemically dependent non-root centers are allowed.
No acyclicity, selected reference, comparison strictness or supplied auxiliary state is assumed. -/
theorem existsUnique_sourceModel_physical_report :
    ∃! candidate : Profile input mol,
      SourceModel input mol single candidate ∧
      (∀ atom outcome, (atom, outcome) ∈ analyze input mol ↔
        ∃ center : input.detectedMultiCenterMolecule.Center, center.1.val = atom ∧
          candidate (inputGeometry input) [] (finalQuery input mol agreement center) = outcome) ∧
      (∀ center : input.detectedMultiCenterMolecule.Center,
        PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg center →
        ∃ descriptor,
          candidate (inputGeometry input) [] (finalQuery input mol agreement center) =
            some descriptor ∧
          (center.1.val, some descriptor) ∈ analyze input mol ∧
          (descriptor.IsLowercase ↔
            physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg center = 1)) := by
  obtain ⟨candidate, model, unique⟩ := existsUnique_sourceModel input mol
    agreement admissible supported single
  refine ⟨candidate, ⟨model, ?_, ?_⟩, ?_⟩
  · exact mem_analyze_iff_sourceModel input mol agreement admissible supported single model
  · exact sourceModel_detected_entry input mol agreement admissible supported single charge cfg
      calibrated model
  · intro other satisfied
    exact unique other satisfied.1

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelPhysicalReport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelPhysicalReport.sourceModel_detected_entry
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelPhysicalReport.existsUnique_sourceModel_physical_report
