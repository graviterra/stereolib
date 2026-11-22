import TetraStereo.Examples.RingSharedArmsBoundary
import TetraStereo.Engine.RingSharedArmRefusal

set_option autoImplicit false
set_option maxRecDepth 40000
set_option maxHeartbeats 3500000

namespace TetraStereo.Examples.RingSharedArmRefusal
open OneCenter Engine RingChemicalPriority LocalizedGenericMarkedRecalculation
open RingSharedArmsBoundary (molecule input)

def symm : Engine.RingSharedArmRefusal.Hint := ⟨1,2,[(1,2),(6,8),(7,9)]⟩

def hints (_ : Nat) : Option Engine.RingSharedArmRefusal.Hint := none

theorem certified : (Engine.RingSharedArmRefusal.check? molecule 1 0 symm).isSome = true := by
  decide +kernel

private theorem previous_missing (g : Geometry) : RecursiveSigned.carbon? molecule g 1 0 = none := by
  obtain ⟨direct,term,rec,fr,silent⟩ := RingSharedArmsBoundary.five_routes_missing g 1
  unfold FrozenSigned.check? at fr
  simp [RecursiveSigned.carbon?,term,direct,RecursiveSigned.cacheAtRoot_exact,rec,fr,silent]

theorem official : (Engine.RingSharedArmRefusal.officialCheck? input 1 0 symm).isSome = true := by
  decide +kernel

theorem discovered : (Engine.RingSharedArmRefusal.discover? input 1 0).isSome = true := by
  decide +kernel

private theorem repaired_target :
    (Engine.RingSharedArmRefusal.carbon? input 1 0 (hints 0)).map
      Engine.RingSharedArmRefusal.label = some none := by
  obtain ⟨c,ok⟩ := Option.isSome_iff_exists.mp discovered
  have old := previous_missing (LocalizedChemicalRingPhysicalSense.inputGeometry input.certified)
  change RecursiveSigned.carbon? input.molecule _ 1 0 = none at old
  have member : 0 ∈ RingCarbonReport.carbons input.molecule := by decide +kernel
  simp [Engine.RingSharedArmRefusal.carbon?,member,old,hints,ok,Engine.RingSharedArmRefusal.label]

private theorem repaired_other (i : Nat) (known : i = 1 ∨ i = 2) :
    (Engine.RingSharedArmRefusal.carbon? input 1 i (hints i)).map
      Engine.RingSharedArmRefusal.label = some none := by
  have found : (RingTerminalPair.check? molecule i).isSome = true := by rcases known with rfl | rfl <;> decide +kernel
  obtain ⟨c,present⟩ := Option.isSome_iff_exists.mp found
  change RingTerminalPair.check? input.molecule i = some c at present
  have member : i ∈ RingCarbonReport.carbons input.molecule := by rcases known with rfl | rfl <;> decide +kernel
  simp [Engine.RingSharedArmRefusal.carbon?,member,RecursiveSigned.carbon?,present,
    Engine.RingSharedArmRefusal.label,RecursiveSigned.CarbonVerdict.label]

theorem repaired_report :
    (Engine.RingSharedArmRefusal.report? input 1).map Engine.RingSharedArmRefusal.labels =
      some [(0,none),(1,none),(2,none)] := by
  have row (i : Nat) (ok : i = 0 ∨ i = 1 ∨ i = 2) : ∃ v,
      Engine.RingSharedArmRefusal.carbon? input 1 i (hints i) = some v ∧
      Engine.RingSharedArmRefusal.label v = none := by
    have h : (Engine.RingSharedArmRefusal.carbon? input 1 i (hints i)).map
        Engine.RingSharedArmRefusal.label = some none := by
      rcases ok with rfl | tail
      · exact repaired_target
      · exact repaired_other i tail
    exact Option.map_eq_some_iff.mp h
  obtain ⟨v0,h0,l0⟩ := row 0 (by simp)
  obtain ⟨v1,h1,l1⟩ := row 1 (by simp)
  obtain ⟨v2,h2,l2⟩ := row 2 (by simp)
  unfold Engine.RingSharedArmRefusal.report? Engine.RingSharedArmRefusal.labels
  change ((RingCarbonReport.carbons molecule).mapM (m := Option) (fun i =>
    (Engine.RingSharedArmRefusal.carbon? input 1 i (hints i)).map (Sigma.mk i))).map _ = _
  rw [RingSharedArmsBoundary.carbon_geometries.1]
  simp [List.mapM_cons,h0,h1,h2,l0,l1,l2]

end TetraStereo.Examples.RingSharedArmRefusal

assert_kernel_only TetraStereo.Examples.RingSharedArmRefusal.certified
assert_kernel_only TetraStereo.Examples.RingSharedArmRefusal.repaired_report

assert_kernel_only TetraStereo.Examples.RingSharedArmRefusal.official

assert_kernel_only TetraStereo.Examples.RingSharedArmRefusal.discovered
