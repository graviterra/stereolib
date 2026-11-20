import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedActualTiePhysical
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Every actual prepared key tie in the physical auxiliary branch domain has a molecular
symmetry that moves the specified tied ligand atoms and is proper at every center outside
the actual occurrence history. All accumulated references are fixed. This strengthens the
source-component-only interface by using the existing component reextension theorem.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedTieBoundary

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointPreparedActualTiePhysical (tie_sourceProper)
open LocalizedChemicalRingJointPreparedCorrectionWitness (sideState)
open LocalizedChemicalRingJointMarkerFrameExecution (slotKeys)
open LocalizedChemicalRingReferenceConsensusCorrectionInduction (reextend_proper)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)
open LocalizedMarkedReachableConfigurations (Reached)
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
/-- Actual ties derive one all-reference-fixing symmetry proper everywhere off the history.
No symmetry, physical-sign oracle, generated-label correspondence or sorting success is supplied. -/
theorem tie_boundaryProper (node : RawMolecule.CanonicalBranchNode)
    (reached : Reached mol node) (center : input.detectedMultiCenterMolecule.Center)
    (current : node.atom = center.1.val) (data : OccurrenceData input mol center node)
    (branch : TiedRootBranch input data.target) (references : List input.Atom) (reflected : Bool)
    (left right : Fin 4) (distinct : left ≠ right)
    (tie : slotKeys input mol single center node data
        (sideState input mol node (inputGeometry input) references reflected) references left =
      slotKeys input mol single center node data
        (sideState input mol node (inputGeometry input) references reflected) references right) :
    ∃ symmetry : input.detectedMultiCenterMolecule.Aut,
      (∀ atom ∈ data.target.1.node.history,
        (symmetry : Equiv.Perm input.Atom) atom = atom) ∧
      (symmetry : Equiv.Perm input.Atom) (referenceAt input mol center node data left) =
        referenceAt input mol center node data right ∧
      (∀ reference ∈ references, (symmetry : Equiv.Perm input.Atom) reference = reference) ∧
      ∀ d : input.detectedMultiCenterMolecule.Center, d.1 ∉ data.target.1.node.history →
        relativeSign input.detectedMultiCenterMolecule cfg symmetry d = 1 := by
  obtain ⟨source, fixed, entry, refs, proper⟩ := tie_sourceProper input mol agreement admissible
    supported single charge cfg calibrated node reached center current data branch references
    reflected left right distinct tie
  have different : referenceAt input mol center node data left ≠
      referenceAt input mol center node data right := by
    intro equal
    exact distinct (data.ligandOf.injective
      (input.detectedMultiCenterMolecule.ligandAtomAt_injective center equal))
  obtain ⟨symmetry, fixedAll, _support, moved, keeps, properAll⟩ := reextend_proper input cfg
    data.target.1.node.history.reverse (referenceAt input mol center node data left)
    (referenceAt input mol center node data right) source
    (fun atom member => fixed atom (List.mem_reverse.mp member)) entry different proper
  exact ⟨symmetry, fun atom member => fixedAll atom (List.mem_reverse.mpr member), moved,
    fun reference member => keeps reference (refs reference member),
    fun d outside => properAll d (fun member => outside (List.mem_reverse.mp member))⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedTieBoundary

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedTieBoundary.tie_boundaryProper
