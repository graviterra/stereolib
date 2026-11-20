import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceProper
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual key ties yield one physically source-proper molecular map fixing every retained
reference. No witness, correction oracle, desired label or moving-refusal exclusion is supplied.
This endpoint concerns reached non-root occurrences inside tied root branches; root assignment
and the complete molecular report remain separate consumers. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualTiePhysical

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingJointSelectedTieWitness (joint_matched_of_tie)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingJointPreparedOccurrenceCorrection (SourceProper)
open LocalizedChemicalRingJointPreparedSourceProper (claim_all)
open LocalizedChemicalRingProperRotationConsensus (slot_current)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

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
/-- **Every actual prepared joint-key tie in a tied root branch is source-proper.** The entry atoms are the two tied slots' own ligand atoms. Any reached occurrence, every retained reference list, either geometry side, the actual generated state at the structural depth. -/
theorem tie_sourceProper (node : RawMolecule.CanonicalBranchNode)
    (reached : Reached mol node) (c : input.detectedMultiCenterMolecule.Center)
    (current : node.atom = c.1.val) (data : OccurrenceData input mol c node)
    (branch : TiedRootBranch input data.target) (references : List input.Atom) (reflected : Bool)
    (left right : Fin 4) (distinct : left ≠ right)
    (tie : slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references left =
      slotKeys input mol single c node data
        (sideState input mol node (inputGeometry input) references reflected) references right) :
    SourceProper input cfg data.target references (referenceAt input mol c node data left)
        (referenceAt input mol c node data right) := by
  obtain ⟨a, b, different, ⟨w⟩⟩ := joint_matched_of_tie input mol single charge c node data branch _
    references left right distinct tie
  have atLeft : a = referenceAt input mol c node data left :=
    Option.some.inj (w.leftCurrent.symm.trans (slot_current input mol single c node data _ left))
  have atRight : b = referenceAt input mol c node data right :=
    Option.some.inj (w.rightCurrent.symm.trans (slot_current input mol single c node data _ right))
  subst atLeft
  subst atRight
  exact claim_all input mol agreement admissible supported single charge cfg calibrated
    (structuralDepth mol node) node rfl reached c current data branch references reflected left right
    _ _ different w


end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualTiePhysical

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualTiePhysical.tie_sourceProper
