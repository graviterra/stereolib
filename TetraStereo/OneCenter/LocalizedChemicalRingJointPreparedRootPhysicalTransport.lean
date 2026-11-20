import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootWitness
import TetraStereo.OneCenter.LocalizedCyclicMatchedReadingPhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Conversion of source-component properness at an original root into the independent,
frame-aware physical branch transport. No branch disjointness or acyclicity is needed.
This module is only the geometric conversion; the actual root-key reconstruction is separate. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalTransport

open CertifiedLocalizedCIPInput RetainedCoherentSymmetry RootedTetrahedralBranchSymmetry
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData referenceAt)
open LocalizedChemicalRingJointPreparedOccurrenceCorrection (SourceProper)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign_eq_iff)
open LocalizedCyclicMatchedReadingPhysicalTransport (ligandBranchReaches_implies_inComponent)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (c : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
  (data : OccurrenceData input mol c node)

theorem root_history (rootAddress : data.target.1.address = [])
    (current : node.atom = c.1.val) : data.target.1.node.history = [c.1] := by
  have equality := input.declarativeLocalizedOccurrence_eq_root_of_address_nil
    ((input.mem_localizedOccurrences_iff _ _).mp data.target.2) rootAddress
  have nodeEq := congrArg (fun occurrence => occurrence.node) equality
  change data.target.1.node = OfficialCIPNode.root data.target.1.root at nodeEq
  have sound := (LocalizedMarkedCarrierLookup.lookup?_sound input node data.target data.found).current
  rw [nodeEq] at sound
  have rootEq : data.target.1.root = c.1 := by
    apply Fin.ext
    exact (Option.some.inj sound).trans current
  rw [nodeEq]
  change [data.target.1.root] = [c.1]
  rw [rootEq]

/-- A single source-proper automorphism supplies the independent physical transport. -/
theorem properTransport_of_sourceProper
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (rootAddress : data.target.1.address = []) (current : node.atom = c.1.val)
    (references : List input.Atom) (left right : Fin 4)
    (source : SourceProper input cfg data.target references
      (referenceAt input mol c node data left) (referenceAt input mol c node data right)) :
    ProperTransport input.detectedMultiCenterMolecule cfg c
      (data.ligandOf left) (data.ligandOf right) := by
  obtain ⟨e, fixed, entry, _, proper⟩ := source
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
    have sign := proper d (by simpa only [history, List.reverse_singleton, referenceAt] using component)
    exact (relativeSign_eq_iff input.detectedMultiCenterMolecule cfg e d 1).mp sign

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalTransport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalTransport.root_history
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalTransport.properTransport_of_sourceProper
