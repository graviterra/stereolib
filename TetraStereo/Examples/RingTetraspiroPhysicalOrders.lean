import TetraStereo.Examples.RingPublishedTetraspiro
import TetraStereo.Engine.RingChemicalPriority
import TetraStereo.Engine.RingActiveMagnitude

set_option autoImplicit false
set_option maxRecDepth 60000
set_option maxHeartbeats 5000000

namespace TetraStereo.Examples.RingTetraspiroPhysicalOrders
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingPublishedTetraspiro (molecule spatial reflected)

/-- All 24 possible orders of the incident molecular directions are tested
against their first two Rule 1a spheres and the hand specified by the label. -/
def compatible? (xyz : SpatialConfiguration) (focus : Nat) (label : LocalizedAuxiliaryLabel) :
    Option (List (List Nat)) := do
  let ids ← frameAtoms? molecule (canonicalCenterRoot focus)
  let rows ← ids.mapM fun id => do
    return (id, ← RingChemicalPriority.ligandRows? molecule [focus] id 1)
  let allowed := rows.permutations'.filter fun rank =>
    decide (rank.Pairwise fun a b => b.2 ≤ a.2) &&
      readback? (fun k => xyz.positions[k]?) (rank.map Prod.fst) == some (CentresRing.MirrorCasing.hand label)
  return allowed.map (List.map Prod.fst)

/-- The four target labels are from IUPAC P-93.5.3.2, Example 5.
Atom identifiers here are the published locants minus one. -/
def published : List (Nat × LocalizedAuxiliaryLabel) :=
  [(2,.chiral .R),(3,.pseudoasymmetric .r),(6,.chiral .S),(9,.pseudoasymmetric .s)]

theorem required_orders :
    published.mapM (fun (i,d) => compatible? spatial i d) =
      some [[[0,9,3,1]],[[4,6,2,5]],[[7,9,3,8]],[[10,2,6,11]]] ∧
    published.mapM (fun (i,d) => compatible? reflected i (CentresRing.MirrorCasing.reflectLabel d)) =
      some [[[0,9,3,1]],[[4,2,6,5]],[[7,9,3,8]],[[10,6,2,11]]] := by
  decide +kernel

/-- A context-free preference must put the same ordered ligand pair in the
same relative order wherever it occurs. The published pseudoasymmetric hands
and the two atomic-number spheres already make this impossible. -/
theorem no_atom_pair_preference :
    ¬ ∃ (senior : Nat → Nat → Bool) (atFour atTen : List Nat),
      compatible? spatial 3 (.pseudoasymmetric .r) = some [atFour] ∧
      compatible? spatial 9 (.pseudoasymmetric .s) = some [atTen] ∧
      senior 6 2 = decide (atFour.idxOf 6 < atFour.idxOf 2) ∧
      senior 6 2 = decide (atTen.idxOf 6 < atTen.idxOf 2) := by
  rintro ⟨senior,f,t,hf,ht,cf,ct⟩
  have four : compatible? spatial 3 (.pseudoasymmetric .r) = some [[4,6,2,5]] := by decide +kernel
  have ten : compatible? spatial 9 (.pseudoasymmetric .s) = some [[10,2,6,11]] := by decide +kernel
  have fe := (List.cons.inj (Option.some.inj (hf.symm.trans four))).1
  have te := (List.cons.inj (Option.some.inj (ht.symm.trans ten))).1
  subst f
  subst t
  exact Bool.noConfusion (cf.symm.trans ct)

private def fits (value : Int) (order : List Nat) (left right : Nat) :=
  order.contains left && order.contains right &&
    (if order.idxOf left < order.idxOf right then decide (0 < value) else decide (value < 0))

/-- Filter the physically allowed signed two-geometry scores by the
permitted ranked coordinate readings. No observation of a Java comparison
enters this calculation. -/
def compatibleScores? (focus : Nat) (label : LocalizedAuxiliaryLabel) (left right : Nat) :
    Option (List (Int × Int)) := do
  let actual ← compatible? spatial focus label
  let mirror ← compatible? reflected focus (CentresRing.MirrorCasing.reflectLabel label)
  return RingActivePairs.molecularValues.filter fun score =>
    actual.any (fun order => fits score.1 order left right) &&
    mirror.any (fun order => fits score.2 order left right)

/-- Within the molecular score alphabet, the published hands constrain both
signed magnitudes independently of the reference implementation. The same
ordered pair has opposite doubled scores in the two lowercase contexts. -/
theorem required_magnitudes :
    compatibleScores? 2 (.chiral .R) 9 3 = some [(1,1)] ∧
    compatibleScores? 3 (.pseudoasymmetric .r) 6 2 = some [(2,-2)] ∧
    compatibleScores? 6 (.chiral .S) 9 3 = some [(1,1)] ∧
    compatibleScores? 9 (.pseudoasymmetric .s) 6 2 = some [(-2,2)] := by decide +kernel

/-- Any cache for this ordered pair that fits both published physical readings
must distinguish the two contexts. The key may encode the frozen state or
occurrence instead of a raw focus identifier. -/
theorem cache_must_distinguish {K : Type} (key : Nat → K) (score : K → Int × Int)
    (four : score (key 3) ∈ (compatibleScores? 3 (.pseudoasymmetric .r) 6 2).getD [])
    (ten : score (key 9) ∈ (compatibleScores? 9 (.pseudoasymmetric .s) 6 2).getD []) :
    key 3 ≠ key 9 := by
  intro same
  rw [required_magnitudes.2.1] at four
  rw [required_magnitudes.2.2.2] at ten
  have pos : score (key 3) = (2,-2) := List.mem_singleton.mp four
  have neg : score (key 9) = (-2,2) := List.mem_singleton.mp ten
  rw [same,neg] at pos
  contradiction

end TetraStereo.Examples.RingTetraspiroPhysicalOrders
assert_kernel_only TetraStereo.Examples.RingTetraspiroPhysicalOrders.required_orders
assert_kernel_only TetraStereo.Examples.RingTetraspiroPhysicalOrders.no_atom_pair_preference
assert_kernel_only TetraStereo.Examples.RingTetraspiroPhysicalOrders.required_magnitudes
assert_kernel_only TetraStereo.Examples.RingTetraspiroPhysicalOrders.cache_must_distinguish
