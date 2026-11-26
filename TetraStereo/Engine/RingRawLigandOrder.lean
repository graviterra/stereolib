import TetraStereo.Engine.RingLigandNativeAnswers
import TetraStereo.Engine.RingRawComparisonLift
import TetraStereo.Engine.RingIndependentInventory

/-! From a complete raw request to a single observable ligand comparison. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingRawLigandOrder
open OneCenter
open LocalizedChemicalRing (Input coordinatesAdmitted)
open RingUniversalLigandOrder (Oracle Fact Witness)
open RingGlobalComparison (Called prior)
open RingRawComparisonLift (RawTrace)
open RingActiveDistanceSchedule (height)

abbrev Comparisons := (i : Input) → Oracle i

def evaluate (other : Comparisons) : RingRawComparisonLift.TypedEvaluation := fun i atoms =>
  if valid : coordinatesAdmitted i = true then RingUniversalLigandOrder.report valid (other i) atoms
  else none

def fromRaw? (other : Comparisons) := RingRawComparisonLift.fromRaw (evaluate other)

theorem admitted {m g ids i atoms} (trace : RawTrace m g ids i atoms) :
    coordinatesAdmitted i = true := by
  obtain ⟨_,_,_,_,inner⟩ := trace
  obtain ⟨_,_,_,_,_,_,h⟩ := inner.prepared
  exact h

/-- An alternative comparator changes a raw report only if an actual placement
and requested root lead to a differing published cell. Both runs reached that
cell with identical addressed stores. An available directed pair differs there. -/
theorem disagreement (other : Comparisons) (m : RawMolecule) (g : SpatialConfiguration)
    (ids : List Nat) (different : fromRaw? other m g ids ≠ RingHydrogenReport.fromRaw? m g ids) :
    ∃ i atoms, ∃ (trace : RawTrace m g ids i atoms), ∃ a ∈ atoms, a.val ∈ ids ∧
      ∃ k ≤ height i + 1, ∃ q, Witness (admitted trace) (other i) a k q := by
  rw [←RingRawComparisonLift.native] at different
  obtain ⟨i,atoms,trace,bad⟩ := RingRawComparisonLift.difference _ _ m g ids different
  have valid := admitted trace
  simp only [evaluate, dif_pos valid] at bad
  obtain ⟨a,ha,k,bound,q,w⟩ := RingUniversalLigandOrder.report_disagreement valid (other i) atoms bad
  have member : a.val ∈ ids := trace.ids ▸ List.mem_map_of_mem (f := Fin.val) ha
  exact ⟨i,atoms,trace,a,ha,member,k,bound,q,w⟩

/-- Comparison agreement is needed only on a placement and occurrence reachable
from this request. The conclusion includes raw admission and placement failures. -/
theorem exact_of_comparisons (other : Comparisons) (m : RawMolecule) (g : SpatialConfiguration)
    (ids : List Nat)
    (agree : ∀ i atoms, RawTrace m g ids i atoms → ∀ a ∈ atoms, ∀ k q, Called i a k q →
      ∀ t b, Fact (RingUniversalLigandOrder.observe i q (prior i a k)) t b →
        other i q (prior i a k) t = b) :
    fromRaw? other m g ids = RingHydrogenReport.fromRaw? m g ids := by
  by_contra bad
  obtain ⟨i,atoms,trace,a,ha,_,k,_,q,call,_,_,t,b,f,wrong⟩ := disagreement other m g ids bad
  exact wrong (agree i atoms trace a ha k q call t b f)

/-- Unconditional equality for every raw graph, coordinate list, and request.
The comparison-only reconstruction computes each sphere from its own prior store. -/
theorem native (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) :
    fromRaw? RingLigandNativeAnswers.nativeOracle m g ids = RingHydrogenReport.fromRaw? m g ids := by
  apply exact_of_comparisons
  intro i atoms _ a _ k q _ t b f
  exact RingLigandNativeAnswers.nativeAnswer_of_fact f

end TetraStereo.Engine.RingRawLigandOrder
assert_kernel_only TetraStereo.Engine.RingRawLigandOrder.disagreement
assert_kernel_only TetraStereo.Engine.RingRawLigandOrder.native

namespace TetraStereo.Engine.RingRawPolicy
open OneCenter
open LocalizedChemicalRing (Input)
open RingIndependentInventory (Policy)
open RingActiveDistanceSchedule (Visible frozen evaluate)
open RingRawComparisonLift (RawTrace)

abbrev Policies := (i : Input) → Policy i

def report (s : Policies) : RingRawComparisonLift.TypedEvaluation := fun i atoms =>
  let p := s i
  atoms.mapM fun a => (RingEligibleGraph.root i p.eligible p.rule a).map fun v => (a.val,v)

def fromRaw? (s : Policies) := RingRawComparisonLift.fromRaw (report s)

theorem report_of_roots (s : Policies) (i : Input) (atoms : List i.certified.Atom)
    (agree : ∀ a ∈ atoms, RingChemicalGraphProof.root i a =
      RingEligibleGraph.root i (s i).eligible (s i).rule a) :
    report s i atoms = RingChemicalReport.report? i atoms := by
  apply RingFrameTransport.mapM_congr_mem
  intro a mem
  exact congrArg (Option.map (fun v => (a.val,v))) (agree a mem).symm

theorem native (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat) :
    fromRaw? RingIndependentInventory.native m g ids = RingHydrogenReport.fromRaw? m g ids := by
  apply RingRawComparisonLift.eq_native
  intro i atoms _
  apply report_of_roots
  intro a _
  rw [RingIndependentInventory.native_rule]
  rfl

/-- A raw alternative may select different centers as well as different rankings.
Every changed report reaches a requested root and a center-selection or publication
disagreement on identical independent frozen readers in that root's digraph. -/
theorem disagreement (s : Policies) (m : RawMolecule) (g : SpatialConfiguration) (ids : List Nat)
    (different : fromRaw? s m g ids ≠ RingHydrogenReport.fromRaw? m g ids) :
    ∃ i atoms, RawTrace m g ids i atoms ∧ ∃ a ∈ atoms, a.val ∈ ids ∧
      ∃ q, (q = RingGroupedReport.origin i a ∨ Visible (RingGroupedReport.origin i a) q) ∧
        frozen (RingChemicalGraphProof.state i) q = frozen (evaluate (s i).rule) q ∧
        RingIndependentInventory.LocalDifference (RingIndependentInventory.native i) (s i) q
          (frozen (RingChemicalGraphProof.state i) q) := by
  classical
  rw [←RingRawComparisonLift.native] at different
  obtain ⟨i,atoms,trace,_,idsEq,bad⟩ := RingRawComparisonLift.difference_admitted _ _ m g ids different
  have rootBad : ∃ a ∈ atoms, RingChemicalGraphProof.root i a ≠
        RingEligibleGraph.root i (s i).eligible (s i).rule a := by
    by_contra! allRoots
    exact bad (report_of_roots s i atoms allRoots)
  obtain ⟨a,mem,wrong⟩ := rootBad
  rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i),
      RingEligibleGraph.root_exact _ (s i).skips] at wrong
  exact ⟨i,atoms,trace,a,mem,idsEq ▸ List.mem_map_of_mem (f := Fin.val) mem,
    RingIndependentInventory.native_difference i (s i) _ wrong⟩

end TetraStereo.Engine.RingRawPolicy
assert_kernel_only TetraStereo.Engine.RingRawPolicy.disagreement
assert_kernel_only TetraStereo.Engine.RingRawPolicy.native
