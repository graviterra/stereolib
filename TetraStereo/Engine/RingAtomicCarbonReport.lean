import TetraStereo.Engine.LocalizedChemicalRingPublic
import TetraStereo.OneCenter.LocalizedChemicalRingPhysicalSense
import TetraStereo.Engine.RingReferenceDerivation
import TetraStereo.Engine.RingCarbonReport

set_option autoImplicit false

namespace TetraStereo.Engine
open OneCenter RingChemicalPriority RingChemicalPriority.Recursive

inductive ReferenceCarbonVerdict (m : RawMolecule) (g : LocalizedGenericMarkedRecalculation.Geometry)
    (i : Nat) where
  | hydrogens (equalPair : RingCarbonReport.HydrogenPair m i)
  | derived (certificate : ReferenceDerivation.Certificate m g [i])

def ReferenceCarbonVerdict.reading? {m g i} : ReferenceCarbonVerdict m g i → Option Reading
  | .hydrogens _ => none
  | .derived c => c.verdict

end TetraStereo.Engine

namespace TetraStereo.Engine.AtomicCarbonReport
open OneCenter LocalizedGenericMarkedRecalculation RingChemicalPriority Recursive
open LocalizedChemicalRingPhysicalSense (inputGeometry)

/-- Every row on this public, single-bond profile has either two
constitutionally identical terminal hydrogens or a strict atomic-number
ranking and nondegenerate absolute readbacks in both geometries. -/
inductive Verdict (m : RawMolecule) (g : Geometry) (depth i : Nat) where
  | hydrogens (equalPair : RingCarbonReport.HydrogenPair m i)
  | strict (order : List Nat) (ranked : atomicOrder? m [i] depth = some order)
      (reading : Reading) (observed : geometric g order order = some reading)

def Verdict.toReference {m g depth i} : Verdict m g depth i → ReferenceCarbonVerdict m g i
  | .hydrogens pair => .hydrogens pair
  | .strict _ ranked r observed => .derived
      ⟨some r,[],by simp,by simp,by simp,.atomic ranked observed⟩

/-- Recover the actual incident occurrences and their pairwise strict,
molecular atomic-number keys for an assigned row. -/
theorem Verdict.strict_ranking {m i depth order} (ranked : atomicOrder? m [i] depth = some order) :
    ∃ ranking : AtomicRanking m [i] depth, atomicRanking? m [i] depth = some ranking ∧
      ranking.arms.map (fun a => a.cursor.node.atom) = order :=
  Option.map_eq_some_iff.mp ranked

theorem Verdict.strict_letter {m g depth i order r} (ranked : atomicOrder? m [i] depth = some order)
    (observed : geometric g order order = some r) :
    (Verdict.strict order ranked r observed).toReference.reading?.bind Reading.label = some (.chiral r.actual) ∧
      readback? g order = some r.actual ∧ r.reflected = r.actual.swap := by
  obtain ⟨actual,reflected,label⟩ := constitutional_casing observed
  exact ⟨label,actual,reflected⟩

def at? (m : RawMolecule) (g : Geometry) (depth i : Nat) : Option (Verdict m g depth i) :=
  match RingCarbonReport.hydrogens? m i with
  | some pair => some (.hydrogens pair)
  | none =>
    match ranked : atomicOrder? m [i] depth with
    | none => none
    | some order =>
      match seen : geometric g order order with
      | none => none
      | some r => some (.strict order ranked r seen)

/-- These independent tests exactly characterize the inputs for which the
single-center constructor returns a verdict. -/
theorem at?_isSome_iff (m : RawMolecule) (g : Geometry) (depth i : Nat) :
    (at? m g depth i).isSome = true ↔
      (RingCarbonReport.hydrogens? m i).isSome = true ∨
      ∃ order r, atomicOrder? m [i] depth = some order ∧ geometric g order order = some r := by
  unfold at?
  split
  · simp_all
  · split
    · simp_all
    · split <;> simp_all


structure Report (input : LocalizedChemicalRing.Input) (depth : Nat) where
  rows : List ((i : Nat) × Verdict input.molecule (inputGeometry input.certified) depth i)
  inventory : rows.map Sigma.fst = RingCarbonReport.carbons input.molecule

def Report.labels {input depth} (r : Report input depth) :=
  r.rows.map fun row => (row.1,row.2.toReference.reading?.bind Reading.label)

private def collect (m : RawMolecule) (g : Geometry) (depth : Nat) :
    (ids : List Nat) → Option {rows : List ((i : Nat) × Verdict m g depth i) // rows.map Sigma.fst = ids}
  | [] => some ⟨[],rfl⟩
  | i :: ids => do
    let v ← at? m g depth i
    let tail ← collect m g depth ids
    return ⟨⟨i,v⟩ :: tail.val,by simp [tail.property]⟩

private theorem collect_isSome (m : RawMolecule) (g : Geometry) (depth : Nat) (ids : List Nat) :
    (collect m g depth ids).isSome = true ↔ ∀ i ∈ ids, (at? m g depth i).isSome = true := by
  induction ids with
  | nil => simp [collect]
  | cons i ids ih =>
    cases h : at? m g depth i <;> cases t : collect m g depth ids <;>
      simp [collect,h,t] at ih ⊢ <;> tauto

/-- Try this report when every carbon is decided by Rule 1a or has
equivalent terminal hydrogens. The input supplies public structural
admission. Each assigned row checks its own coordinates. -/
def check (input : LocalizedChemicalRing.Input) (depth : Nat) : Option (Report input depth) := do
  let rows ← collect input.molecule (inputGeometry input.certified) depth (RingCarbonReport.carbons input.molecule)
  return ⟨rows.val,rows.property⟩

theorem check_isSome_iff (input : LocalizedChemicalRing.Input) (depth : Nat) :
    (check input depth).isSome = true ↔ ∀ i ∈ RingCarbonReport.carbons input.molecule,
      (RingCarbonReport.hydrogens? input.molecule i).isSome = true ∨
      ∃ order r, atomicOrder? input.molecule [i] depth = some order ∧
        geometric (inputGeometry input.certified) order order = some r := by
  have result : (check input depth).isSome = (collect input.molecule (inputGeometry input.certified)
      depth (RingCarbonReport.carbons input.molecule)).isSome := by
    unfold check
    cases collect input.molecule (inputGeometry input.certified) depth (RingCarbonReport.carbons input.molecule) <;> rfl
  rw [result,collect_isSome]
  simp only [at?_isSome_iff]

end TetraStereo.Engine.AtomicCarbonReport

assert_kernel_only TetraStereo.Engine.AtomicCarbonReport.Verdict.strict_letter
assert_kernel_only TetraStereo.Engine.AtomicCarbonReport.check_isSome_iff

assert_kernel_only TetraStereo.Engine.AtomicCarbonReport.Verdict.strict_ranking
