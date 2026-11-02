import TetraStereo.OneCenter.LocalizedRuleMajorBranchStages
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual rule-major stage families at one arbitrary reroot cursor and one fixed reader.
Every stage uses the same cursor and reader; each arm retains the source tree, actual build
equation, and recursive sorting trace that produced its key. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP
open Rule4aTableBridge
noncomputable section

/-- One successful cumulative-rule trace at an arbitrary valid context cursor. -/
structure RuleMajorContextArm (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel) where
  tree : LocalizedCumulativeDecoratedTree input carrierFuel
  key : input.LocalizedRerootCumulativeRule45Key
  sourceEq : tree.source = cursor
  built : input.buildRuleMajorCumulativeWithRead? stage read
    (2 * (carrierFuel + 1)) cursor = some key
  trace : LocalizedRuleMajorSortTrace input stage read
    (2 * (carrierFuel + 1)) tree key

/-- Every path-valid context cursor admits an actual trace arm, with success derived from the
twice-carrier-fuel availability theorem. -/
theorem exists_ruleMajorContextArm (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    Nonempty (input.RuleMajorContextArm carrierFuel stage read cursor) := by
  obtain ⟨tree, key, sourceEq, built, trace⟩ :=
    exists_ruleMajorTrace_at_twice input stage read cursor valid
  exact ⟨⟨tree, key, sourceEq, built, trace⟩⟩

/-- The six actual stage families needed by a complete contextual Rules-4/5 comparison.
All six share the exact same reroot cursor and label reader. -/
structure RuleMajorContextStages (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel) where
  a : input.RuleMajorContextArm carrierFuel .rule4a read cursor
  b : ∀ reference : RS,
    input.RuleMajorContextArm carrierFuel (.rule4b reference) read cursor
  c : ∀ reference : RS,
    input.RuleMajorContextArm carrierFuel (.rule4c reference) read cursor
  noReference : input.RuleMajorContextArm carrierFuel .rule4cNoReference read cursor

/-- Every path-valid cursor admits the full family; no stereo labels or reference populations
are assumed. -/
theorem exists_ruleMajorContextStages (input : CertifiedLocalizedCIPInput)
    (carrierFuel : Nat)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    Nonempty (input.RuleMajorContextStages carrierFuel read cursor) := by
  obtain ⟨a⟩ := input.exists_ruleMajorContextArm carrierFuel .rule4a read cursor valid
  obtain ⟨bR⟩ := input.exists_ruleMajorContextArm carrierFuel (.rule4b .R) read cursor valid
  obtain ⟨bS⟩ := input.exists_ruleMajorContextArm carrierFuel (.rule4b .S) read cursor valid
  obtain ⟨cR⟩ := input.exists_ruleMajorContextArm carrierFuel (.rule4c .R) read cursor valid
  obtain ⟨cS⟩ := input.exists_ruleMajorContextArm carrierFuel (.rule4c .S) read cursor valid
  obtain ⟨noReference⟩ :=
    input.exists_ruleMajorContextArm carrierFuel .rule4cNoReference read cursor valid
  refine ⟨⟨a, ?_, ?_, noReference⟩⟩
  · intro reference
    cases reference <;> assumption
  · intro reference
    cases reference <;> assumption

/-- Every executable actual child is path-valid by the declarative child characterization, so its
full stage family can be derived without supplying any successful build. -/
theorem exists_ruleMajorContextStages_at_actualChild
    (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (parent cursor : input.LocalizedRerootCursor carrierFuel)
    (child : cursor ∈ input.executableLocalizedRerootChildren parent) :
    Nonempty (input.RuleMajorContextStages carrierFuel read cursor) := by
  have children := input.executableLocalizedRerootChildren_declarative parent
  have valid := input.localizedRerootChild_valid parent cursor
    (input.executableLocalizedRerootChildren parent) children child
  exact input.exists_ruleMajorContextStages carrierFuel read cursor valid

namespace RuleMajorContextArm

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {stage : LocalizedCumulativeRule45Stage}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
  {cursor : input.LocalizedRerootCursor carrierFuel}

/-- The declarative graph erased from this arm's actual tree. -/
abbrev graph (arm : input.RuleMajorContextArm carrierFuel stage read cursor) :
    DeclarativeCIP.RootedDigraph input.Atom := ruleMajorTreeGraph arm.tree

end RuleMajorContextArm

namespace RuleMajorContextStages

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
  {cursor : input.LocalizedRerootCursor carrierFuel}

private def finiteReferences : List RS := [.R, .S]

/-- All six actual graphs in the common context family. -/
def graphs (stages : input.RuleMajorContextStages carrierFuel read cursor) :
    List (DeclarativeCIP.RootedDigraph input.Atom) :=
  [ruleMajorTreeGraph stages.a.tree, ruleMajorTreeGraph stages.noReference.tree] ++
    (finiteReferences.map fun reference => ruleMajorTreeGraph (stages.b reference).tree) ++
    (finiteReferences.map fun reference => ruleMajorTreeGraph (stages.c reference).tree)

/-- Common width window for all six actual contextual stage graphs. -/
def widthBound (stages : input.RuleMajorContextStages carrierFuel read cursor) : Nat :=
  (stages.graphs.map fun graph => graph.width).foldl max 0

/-- Common depth window for all six actual contextual stage graphs. -/
def depthBound (stages : input.RuleMajorContextStages carrierFuel read cursor) : Nat :=
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

private theorem width_le_of_mem (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (graph : DeclarativeCIP.RootedDigraph input.Atom) (present : graph ∈ stages.graphs) :
    graph.width ≤ stages.widthBound := by
  unfold widthBound
  apply le_foldl_max_of_mem
  exact List.mem_map.mpr ⟨graph, present, rfl⟩

private theorem height_le_of_mem (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (graph : DeclarativeCIP.RootedDigraph input.Atom) (present : graph ∈ stages.graphs) :
    graph.height ≤ stages.depthBound := by
  unfold depthBound
  apply le_foldl_max_of_mem
  exact List.mem_map.mpr ⟨graph, present, rfl⟩

theorem a_width_le (stages : input.RuleMajorContextStages carrierFuel read cursor) :
    (ruleMajorTreeGraph stages.a.tree).width ≤ stages.widthBound :=
  width_le_of_mem stages _ (by simp [graphs])

theorem a_depth_le (stages : input.RuleMajorContextStages carrierFuel read cursor) :
    (ruleMajorTreeGraph stages.a.tree).height ≤ stages.depthBound :=
  height_le_of_mem stages _ (by simp [graphs])

theorem noReference_width_le (stages : input.RuleMajorContextStages carrierFuel read cursor) :
    (ruleMajorTreeGraph stages.noReference.tree).width ≤ stages.widthBound :=
  width_le_of_mem stages _ (by simp [graphs])

theorem noReference_depth_le (stages : input.RuleMajorContextStages carrierFuel read cursor) :
    (ruleMajorTreeGraph stages.noReference.tree).height ≤ stages.depthBound :=
  height_le_of_mem stages _ (by simp [graphs])

theorem b_width_le (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (reference : RS) :
    (ruleMajorTreeGraph (stages.b reference).tree).width ≤ stages.widthBound := by
  apply width_le_of_mem stages _
  cases reference <;> simp [graphs, finiteReferences]

theorem b_depth_le (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (reference : RS) :
    (ruleMajorTreeGraph (stages.b reference).tree).height ≤ stages.depthBound := by
  apply height_le_of_mem stages _
  cases reference <;> simp [graphs, finiteReferences]

theorem c_width_le (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (reference : RS) :
    (ruleMajorTreeGraph (stages.c reference).tree).width ≤ stages.widthBound := by
  apply width_le_of_mem stages _
  cases reference <;> simp [graphs, finiteReferences]

theorem c_depth_le (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (reference : RS) :
    (ruleMajorTreeGraph (stages.c reference).tree).height ≤ stages.depthBound := by
  apply height_le_of_mem stages _
  cases reference <;> simp [graphs, finiteReferences]

end RuleMajorContextStages
end
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_ruleMajorContextArm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_ruleMajorContextStages
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_ruleMajorContextStages_at_actualChild
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextArm.graph
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages.graphs
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages.widthBound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages.depthBound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages.a_width_le
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages.a_depth_le
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages.noReference_width_le
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages.noReference_depth_le
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages.b_width_le
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages.b_depth_le
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages.c_width_le
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorContextStages.c_depth_le
