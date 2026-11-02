import TetraStereo.OneCenter.LocalizedRuleMajorCanonicalBridge
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! One actual molecular reader and its successful whole-rule stages, packaged together for
compound-level proofs.  The finite R/S family supplies a single width and depth bound shared by
every stage graph. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP
open Rule4aTableBridge
noncomputable section

/-- Actual stage arms for one certified ligand and one molecular descriptor reader. -/
structure RuleMajorBranchStages (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence
      (input.certified.input.molecule.atomCount + 1)) where
  a : input.RuleMajorRootArm center index .rule4a
    (input.molecularReader descriptorMap target)
  b : ∀ reference : RS, input.RuleMajorRootArm center index (.rule4b reference)
    (input.molecularReader descriptorMap target)
  c : ∀ reference : RS, input.RuleMajorRootArm center index (.rule4c reference)
    (input.molecularReader descriptorMap target)
  noReference : input.RuleMajorRootArm center index .rule4cNoReference
    (input.molecularReader descriptorMap target)

/-- The stage family exists without assumptions on molecular labels or reference populations. -/
theorem exists_ruleMajorBranchStages (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (target : input.LocalizedCIPOccurrence
      (input.certified.input.molecule.atomCount + 1)) :
    Nonempty (input.RuleMajorBranchStages center index descriptorMap target) := by
  let read := input.molecularReader descriptorMap target
  obtain ⟨a⟩ := input.exists_ruleMajorRootArm center index .rule4a read
  obtain ⟨bR⟩ := input.exists_ruleMajorRootArm center index (.rule4b .R) read
  obtain ⟨bS⟩ := input.exists_ruleMajorRootArm center index (.rule4b .S) read
  obtain ⟨cR⟩ := input.exists_ruleMajorRootArm center index (.rule4c .R) read
  obtain ⟨cS⟩ := input.exists_ruleMajorRootArm center index (.rule4c .S) read
  obtain ⟨noReference⟩ := input.exists_ruleMajorRootArm center index .rule4cNoReference read
  exact ⟨{ a := a, b := fun
    | .R => bR
    | .S => bS, c := fun
    | .R => cR
    | .S => cS, noReference := noReference }⟩

namespace RuleMajorBranchStages

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
  {index : Fin 4} {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
  {target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1)}

/-- The canonical physical expansion retained by the `.rule4a` arm. -/
abbrev graph (stages : input.RuleMajorBranchStages center index descriptorMap target) :
    RootedDigraph input.Atom := ruleMajorArmGraph stages.a

private def finiteReferences : List RS := [.R, .S]

/-- All actual branch graphs, including both members of every finite R/S stage family. -/
def graphs (stages : input.RuleMajorBranchStages center index descriptorMap target) :
    List (RootedDigraph input.Atom) :=
  [ruleMajorArmGraph stages.a, ruleMajorArmGraph stages.noReference] ++
    (finiteReferences.map fun reference => ruleMajorArmGraph (stages.b reference)) ++
    (finiteReferences.map fun reference => ruleMajorArmGraph (stages.c reference))

/-- Common width bound for all six actual stage graphs. -/
def widthBound (stages : input.RuleMajorBranchStages center index descriptorMap target) : Nat :=
  (stages.graphs.map fun graph => graph.width).foldl max 0

/-- Common depth bound for all six actual stage graphs. -/
def depthBound (stages : input.RuleMajorBranchStages center index descriptorMap target) : Nat :=
  (stages.graphs.map fun graph => graph.height).foldl max 0

private theorem start_le_foldl_max (values : List Nat) (initial : Nat) :
    initial ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => simp
  | cons value values ih =>
      simp only [List.foldl_cons]
      exact Nat.le_trans (Nat.le_max_left initial value) (ih (max initial value))

private theorem le_foldl_max_of_mem (values : List Nat) (value : Nat)
    (present : value ∈ values) (initial : Nat) : value ≤ values.foldl max initial := by
  induction values generalizing initial with
  | nil => simp at present
  | cons head tail ih =>
      rw [List.foldl_cons]
      rcases List.mem_cons.mp present with equal | present
      · rw [equal]
        exact Nat.le_trans (Nat.le_max_right initial head) (start_le_foldl_max tail _)
      · exact ih present (max initial head)

private theorem width_le_of_mem (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (graph : RootedDigraph input.Atom) (present : graph ∈ stages.graphs) :
    graph.width ≤ stages.widthBound := by
  unfold widthBound
  apply le_foldl_max_of_mem
  exact List.mem_map.mpr ⟨graph, present, rfl⟩

private theorem height_le_of_mem (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (graph : RootedDigraph input.Atom) (present : graph ∈ stages.graphs) :
    graph.height ≤ stages.depthBound := by
  unfold depthBound
  apply le_foldl_max_of_mem
  exact List.mem_map.mpr ⟨graph, present, rfl⟩

theorem a_width_le (stages : input.RuleMajorBranchStages center index descriptorMap target) :
    (ruleMajorArmGraph stages.a).width ≤ stages.widthBound :=
  width_le_of_mem stages _ (by simp [graphs])

theorem a_depth_le (stages : input.RuleMajorBranchStages center index descriptorMap target) :
    (ruleMajorArmGraph stages.a).height ≤ stages.depthBound :=
  height_le_of_mem stages _ (by simp [graphs])

theorem noReference_width_le
    (stages : input.RuleMajorBranchStages center index descriptorMap target) :
    (ruleMajorArmGraph stages.noReference).width ≤ stages.widthBound :=
  width_le_of_mem stages _ (by simp [graphs])

theorem noReference_depth_le
    (stages : input.RuleMajorBranchStages center index descriptorMap target) :
    (ruleMajorArmGraph stages.noReference).height ≤ stages.depthBound :=
  height_le_of_mem stages _ (by simp [graphs])

theorem b_width_le (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (reference : RS) : (ruleMajorArmGraph (stages.b reference)).width ≤ stages.widthBound := by
  apply width_le_of_mem stages _
  cases reference <;> simp [graphs, finiteReferences]

theorem b_depth_le (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (reference : RS) : (ruleMajorArmGraph (stages.b reference)).height ≤ stages.depthBound := by
  apply height_le_of_mem stages _
  cases reference <;> simp [graphs, finiteReferences]

theorem c_width_le (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (reference : RS) : (ruleMajorArmGraph (stages.c reference)).width ≤ stages.widthBound := by
  apply width_le_of_mem stages _
  cases reference <;> simp [graphs, finiteReferences]

theorem c_depth_le (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (reference : RS) : (ruleMajorArmGraph (stages.c reference)).height ≤ stages.depthBound := by
  apply height_le_of_mem stages _
  cases reference <;> simp [graphs, finiteReferences]

end RuleMajorBranchStages
end
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorBranchStages
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_ruleMajorBranchStages
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorBranchStages.graphs
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorBranchStages.widthBound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorBranchStages.depthBound
