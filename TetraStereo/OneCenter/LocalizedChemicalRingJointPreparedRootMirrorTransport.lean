import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootSourceMirror
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The uniformly negative source map produced by signed correction is exactly an
independent physical mirror transport at an original root. The source component may overlap
other arms: no branch-disjointness or acyclicity hypothesis is used. The witness-based
corollary still explicitly requires the cross-state witness and structural query adapter. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootMirrorTransport

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry RootedTetrahedralBranchSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointPreparedRootPhysicalTransport (root_history)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign relativeSign_eq_iff)
open LocalizedCyclicMatchedReadingPhysicalTransport (ligandBranchReaches_implies_inComponent)
open LocalizedChemicalRingJointPreparedMirrorCorrectionWitness (MirrorWitness)
open LocalizedChemicalRingJointPreparedRootSourceMirror (sourceMirror_of_queryBranches)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingBoundaryWitnessFactMatch (boundaryPath)
open LocalizedChemicalRingWitnessFactMatch (rawPathNode)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)
  (cfg : input.detectedMultiCenterMolecule.Configuration)

theorem mirrorTransport_of_sourceMirror
    (rootAddress : data.target.1.address = []) (current : node.atom = c.1.val)
    (left right : Fin 4) (e : input.detectedMultiCenterMolecule.Aut)
    (fixed : ∀ atom ∈ data.target.1.node.history, (e : Equiv.Perm input.Atom) atom = atom)
    (entry : (e : Equiv.Perm input.Atom) (referenceAt input mol c node data left) =
      referenceAt input mol c node data right)
    (negative : ∀ d : input.detectedMultiCenterMolecule.Center,
      InComponent input.moleculeGraph data.target.1.node.history.reverse
        (referenceAt input mol c node data left) d.1 →
        relativeSign input.detectedMultiCenterMolecule cfg e d = -1) :
    MirrorTransport input.detectedMultiCenterMolecule cfg c
      (data.ligandOf left) (data.ligandOf right) := by
  have history := root_history input mol c node data rootAddress current
  have rootFixed : input.detectedMultiCenterMolecule.centerPerm e c = c := by
    apply (centerPerm_eq_iff _ _ _).mpr
    exact fixed c.1 (history.symm ▸ List.mem_singleton.mpr rfl)
  refine ⟨e, rootFixed, ?_, ?_⟩
  · apply input.detectedMultiCenterMolecule.ligandAtomAt_injective c
    have transported := input.detectedMultiCenterMolecule.ligandAtomAt_ligandPermAt e c
      (data.ligandOf left)
    rw [rootFixed] at transported
    exact transported.trans entry
  · intro d member
    have component := ligandBranchReaches_implies_inComponent
      input.detectedMultiCenterMolecule c (data.ligandOf left) d.1 member
    have sign := negative d
      (by simpa only [history, List.reverse_singleton, referenceAt] using component)
    exact (relativeSign_eq_iff input.detectedMultiCenterMolecule cfg e d (-1)).mp sign

theorem mirrorTransport_of_witness
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
      ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)
    (reached : Reached mol node)
    (rootAddress : data.target.1.address = []) (current : node.atom = c.1.val)
    (references : List input.Atom) (left right : Fin 4)
    (W : MirrorWitness input mol c node data references
      (referenceAt input mol c node data left) (referenceAt input mol c node data right))
    (queryBranch : ∀ p : List input.Atom,
      ResidualObsPath input.moleculeGraph data.target.1.node.history.reverse
        (referenceAt input mol c node data left) p →
      ∀ (d : input.detectedMultiCenterMolecule.Center) (query : RawMolecule.CanonicalBranchNode),
      rawPathNode data.target.1.root (boundaryPath data.target p) = query →
      ∀ actual : OccurrenceData input mol d query, TiedRootBranch input actual.target) :
    MirrorTransport input.detectedMultiCenterMolecule cfg c
      (data.ligandOf left) (data.ligandOf right) := by
  obtain ⟨e, fixed, entry, _, negative⟩ := sourceMirror_of_queryBranches input mol agreement
    admissible supported single charge cfg calibrated node reached c data references
    (referenceAt input mol c node data left) (referenceAt input mol c node data right) W queryBranch
  exact mirrorTransport_of_sourceMirror input mol c node data cfg rootAddress current
    left right e fixed entry negative

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootMirrorTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootMirrorTransport.mirrorTransport_of_sourceMirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootMirrorTransport.mirrorTransport_of_witness
