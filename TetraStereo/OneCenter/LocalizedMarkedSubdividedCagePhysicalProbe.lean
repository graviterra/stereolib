import TetraStereo.OneCenter.LocalizedMarkedSubdividedCageProbe
import TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision
import TetraStereo.OneCenter.FinitePhysicalBranchSearch
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 0

/-!
# Certified source and independent physical checks of the subdivided cage

The source and nondegenerate coordinate checks are kernel proofs. The pruned physical-transport
checks are executable diagnostics of the already verified decision procedure, not kernel proofs
of their particular results. No universal completeness claim or production change is made here.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedSubdividedCagePhysicalProbe

open LocalizedMarkedSubdividedCageProbe LocalizedActualPhysicalBranchDecision
open FinitePhysicalBranchSearch

def source : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := LocalizedRecursiveAuxiliaryPhysicalCompletion.cageSource.molecule.atoms ++
          List.replicate 6 LocalizedRecursiveAuxiliaryPhysicalCompletion.oxygen
        interactions := mol.bonds.map fun b =>
          LocalizedCyclicPseudoInputWitness.singleBond b.source b.target }
    spatial? := some { positions := points } }

theorem source_wellFormed : source.structurallyWellFormed? = true := by decide +kernel
theorem source_graphReady : source.molecule.localizedCIPGraphReady? = true := by decide +kernel

def certified : CertifiedLocalizedCIPInput where
  certified :=
    { input := source
      structurallyWellFormed :=
        (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp source_wellFormed }
  graphReady := source.molecule.localizedCIPGraphReady?_eq_true_iff.mp source_graphReady

theorem source_spatial : source.SpatialIndicesWellFormed := by
  change points.length = 21
  decide +kernel

abbrev physical : MultiCenterMolecule (Fin 21) := actualCanonicalMolecule certified

theorem detected_centers : physical.centers = {0,3,8,9,14} := by decide +kernel

def root : physical.Center := ⟨0, by decide +kernel⟩

private def neighbors (a : Fin 21) : List (Fin 21) :=
  if a = 0 then [1,2,3,9] else if a = 3 then [0,5,6,7]
  else if a = 8 then [4,15,16,17] else if a = 9 then [0,11,12,13]
  else [10,18,19,20]

private theorem neighbor_data : ∀ a : Fin 21, a ∈ physical.centers →
    certified.moleculeGraph.neighborFinset a = (neighbors a).toFinset ∧
      (neighbors a).Nodup ∧ (neighbors a).Pairwise (· ≤ ·) := by decide +kernel

private theorem canonical_neighbors (c : physical.Center) :
    certified.canonicalNeighborList c = neighbors c.1 := by
  obtain ⟨members, nodup, sorted⟩ := neighbor_data c.1 c.2
  change (certified.moleculeGraph.neighborFinset c.1).sort (· ≤ ·) = _
  rw [members]
  exact (List.toFinset_sort (· ≤ ·) nodup).mpr sorted

private theorem neighbors_length (a : Fin 21) : (neighbors a).length = 4 := by
  unfold neighbors
  split_ifs <;> rfl

private theorem ligand_atom (c : physical.Center) (i : Fin 4) :
    physical.ligandAtomAt c i =
      (neighbors c.1).get (Fin.cast (neighbors_length c.1).symm i) := by
  change (certified.canonicalNeighborList c).get _ = _
  simp [canonical_neighbors c]
  rfl

theorem every_center_nondegenerate : ∀ c : physical.Center,
    ((coordinateVolume? certified c).map (fun v => v != 0)).getD false = true := by
  intro c
  have members : c.1 ∈ ({0,3,8,9,14} : Finset (Fin 21)) := by
    simpa only [detected_centers] using c.2
  simp only [Finset.mem_insert, Finset.mem_singleton] at members
  simp only [coordinateVolume?, ligand_atom]
  rcases c with ⟨a, ha⟩
  rcases members with rfl | rfl | rfl | rfl | rfl <;> decide +kernel +revert

/- Independent whole-graph transport tests, using coordinates rather than evaluator labels. -/
/-- info: false -/
#guard_msgs in
#eval decideProperTransportPruned physical (coordinateCfg certified) root 2 3 (List.finRange 21)

/-- info: false -/
#guard_msgs in
#eval decideMirrorTransportPruned physical (coordinateCfg certified) root 2 3 (List.finRange 21)

end TetraStereo.OneCenter.LocalizedMarkedSubdividedCagePhysicalProbe

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedSubdividedCagePhysicalProbe.source_wellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedSubdividedCagePhysicalProbe.source_graphReady
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedSubdividedCagePhysicalProbe.source_spatial
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedSubdividedCagePhysicalProbe.detected_centers
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedSubdividedCagePhysicalProbe.every_center_nondegenerate
