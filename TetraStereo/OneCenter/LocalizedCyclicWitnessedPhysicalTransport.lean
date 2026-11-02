import TetraStereo.OneCenter.LocalizedActualBoundaryPathReadingCorrespondence
import TetraStereo.OneCenter.DeclarativeCIPBoundaryComponentReconstruction
import TetraStereo.OneCenter.LocalizedRetainedPhysicalConfigurationTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-! # Witnessed actual cyclic branch transport

Constitutional equality of two actual current root arms produces one molecular automorphism.
The component reconstruction supplies one full residual path per vertex, and the actual current
trees locate that path and its automorphic image at the same ranked address.
-/

namespace TetraStereo.OneCenter
namespace LocalizedCyclicWitnessedPhysicalTransport

open CertifiedLocalizedCIPInput
open LocalizedActualOutwardRule1bEquivalence
open LocalizedActualBoundaryPathReadingCorrespondence
open LocalizedActualBoundaryObservationReadback
open LocalizedActualBoundaryPathRealization
open RetainedCoherentSymmetry
open BoundaryComponentReconstruction
open LocalizedCumulativeDecoratedTree

noncomputable section

/-- From an actual constitutional tie of two current root-arm RuleMajorContextArms, reconstruct a
single molecular automorphism fixing the root. Every vertex of the source residual component has
one path witness whose actual decorated source nodes in the two very arm trees occupy one common
ranked address and whose histories are related by that automorphism.
-/
theorem currentRootArm_witnessedAutomorphism
    (input : CertifiedLocalizedCIPInput)
    (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (pair : ActualOutwardSiblingPair input (input.certified.input.molecule.atomCount + 1))
    (root : input.Atom)
    (rootBoundary : pair.target.occurrence.1.node.history.reverse = [root])
    (rootCurrent : pair.target.occurrence.1.node.current? = some root)
    (targetReal : pair.target.occurrence.1.node.provenance = .realAtom)
    (leftReal : pair.left.occurrence.1.node.provenance = .realAtom)
    (rightReal : pair.right.occurrence.1.node.provenance = .realAtom)
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    (armL : input.RuleMajorContextArm (input.certified.input.molecule.atomCount + 1)
      stageL read pair.left)
    (armR : input.RuleMajorContextArm (input.certified.input.molecule.atomCount + 1)
      stageR read pair.right)
    (tie : OfficialRuleMajorKey.compare armL.key.constitutional
      armR.key.constitutional = Ordering.eq) :
    ∃ π : Equiv.Perm input.Atom,
      input.moleculeGraph.IsAutomorphism π ∧ π root = root ∧
      ∃ a b : input.Atom,
        pair.left.occurrence.1.node.current? = some a ∧
        pair.right.occurrence.1.node.current? = some b ∧ π a = b ∧
        ∀ z, RetainedCoherentSymmetry.InComponent input.moleculeGraph
            pair.target.occurrence.1.node.history.reverse a z →
          ∃ (path : {p : List input.Atom // RetainedCoherentSymmetry.ResidualObsPath
              input.moleculeGraph pair.target.occurrence.1.node.history.reverse a p})
            (address : List ℕ) (leftNode rightNode :
              LocalizedCumulativeDecoratedTree input
                (input.certified.input.molecule.atomCount + 1)),
            RetainedCoherentSymmetry.pathTerminal path.1 path.2.nonempty = z ∧
            armL.tree.decoratedSubtreeAt? address = some leftNode ∧
            armR.tree.decoratedSubtreeAt? address = some rightNode ∧
            leftNode.source.occurrence.1.node = boundaryNode
              pair.target.occurrence.1.node.history.reverse path.1 ∧
            rightNode.source.occurrence.1.node = boundaryNode
              pair.target.occurrence.1.node.history.reverse (path.1.map π) := by
  obtain ⟨a, b, ha, hb, equiv, sameAddress⟩ :=
    contextArms_equiv_with_same_address input simple charge pair targetReal leftReal rightReal
      armL armR tie
  obtain ⟨actualA, aNode, _aAdj, aNotHistory⟩ := outwardChild_atom_facts input simple
    pair.target pair.left pair.leftRoot pair.leftSlot pair.leftAddress targetReal leftReal rootCurrent
  have aEq : a = actualA := by
    rw [aNode] at ha
    simp only [OfficialCIPNode.extend_current?] at ha
    exact (Option.some.inj ha).symm
  have aNotBoundary : a ∉ pair.target.occurrence.1.node.history.reverse := by
    intro aMem
    have rootMem : root ∈ pair.target.occurrence.1.node.history := by
      apply List.mem_reverse.mp
      rw [rootBoundary]
      simp
    have aIsRoot : a = root := by simpa [rootBoundary] using aMem
    apply aNotHistory
    rw [← aEq, aIsRoot]
    exact rootMem
  obtain ⟨π, hAut, fixesBoundary, sendsEntry, _outside, witness⟩ :=
    BoundaryComponentReconstruction.exists_sameBoundary_automorphism equiv aNotBoundary
  have fixesRoot : π root = root := fixesBoundary root (by rw [rootBoundary]; simp)
  refine ⟨π, hAut, fixesRoot, a, b, ha, hb, sendsEntry, ?_⟩
  intro z hz
  obtain ⟨path, terminal, mapped⟩ := witness z hz
  obtain ⟨address, leftAt, rightAt⟩ := sameAddress path
  have leftOfficial := sourceAtAddress?_toOfficialSourceTree input armL.tree address
  have rightOfficial := sourceAtAddress?_toOfficialSourceTree input armR.tree address
  rw [leftOfficial] at leftAt
  rw [rightOfficial] at rightAt
  obtain ⟨leftNode, leftAt, leftSource⟩ := Option.map_eq_some_iff.mp leftAt
  obtain ⟨rightNode, rightAt, rightSource⟩ := Option.map_eq_some_iff.mp rightAt
  refine ⟨path, address, leftNode, rightNode, terminal, leftAt, rightAt, ?_, ?_⟩
  · exact leftSource
  · calc
      rightNode.source.occurrence.1.node =
          boundaryNode pair.target.occurrence.1.node.history.reverse (equiv.toEquiv path).1 :=
        rightSource
      _ = boundaryNode pair.target.occurrence.1.node.history.reverse (path.1.map π) := by rw [mapped]

end
end LocalizedCyclicWitnessedPhysicalTransport
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicWitnessedPhysicalTransport.currentRootArm_witnessedAutomorphism
