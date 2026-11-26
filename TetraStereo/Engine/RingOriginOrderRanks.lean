import TetraStereo.Engine.RingOriginRootAll
import Mathlib.Data.Finset.Sort

/-! Two ways to measure duplicate origins may have different numerical gaps.
Represent their common observed order by consecutive ranks, including ties. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginOrderRanks

private def extend {n : Nat} (v : Fin n → Nat) (j : Nat) : Nat :=
  if h : j < n then v ⟨j,h⟩ else Finset.univ.sup v + 1 + j

private theorem extend_mono {n : Nat} {v : Fin n → Nat} (inc : StrictMono v) :
    StrictMono (extend v) := by
  intro a b lt
  unfold extend
  split_ifs with ha hb hb
  · exact inc (show (⟨a,ha⟩ : Fin n) < ⟨b,hb⟩ from lt)
  · have bound := Finset.le_sup (f := v) (Finset.mem_univ (⟨a,ha⟩ : Fin n))
    omega
  · omega
  · omega

/-- A bounded native coordinate and an order-preserving alternative admit
two total, strictly increasing decodings from the same rank. Nothing is
assumed about gaps in either scale or the number of observations. -/
theorem compress (P : Nat → Nat → Prop) (N : Nat) (bound : ∀ x y, P x y → x ≤ N)
    (order : ∀ x y u v, P x y → P u v → (x < u ↔ y < v)) :
    ∃ (rank g h : Nat → Nat), StrictMono g ∧ StrictMono h ∧
      ∀ x y, P x y → g (rank x) = x ∧ h (rank x) = y := by
  classical
  let s := (Finset.range (N+1)).filter fun x => ∃ y, P x y
  have mem {x y} (pair : P x y) : x ∈ s :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (bound x y pair)),y,pair⟩
  have has (x : s) : ∃ y, P x.val y := (Finset.mem_filter.mp x.property).2
  let image := fun x : s => (has x).choose
  have picked (x : s) : P x.val (image x) := (has x).choose_spec
  have inc : StrictMono image := fun a b lt =>
    (order a _ b _ (picked a) (picked b)).mp lt
  let e := s.orderIsoOfFin rfl
  let rank := fun x => if h : x ∈ s then ((e.symm ⟨x,h⟩).val) else 0
  refine ⟨rank,extend (fun j => (e j).val),extend (fun j => image (e j)),
    extend_mono (fun _ _ lt => e.strictMono lt),extend_mono (inc.comp e.strictMono),?_⟩
  intro x y pair
  let t : s := ⟨x,mem pair⟩
  have same : image t = y := by
    have l := order _ _ _ _ (picked t) pair
    have r := order _ _ _ _ pair (picked t)
    change (x < x ↔ image t < y) at l
    change (x < x ↔ y < image t) at r
    omega
  have atRank : rank x = (e.symm t).val := by simp [rank,mem pair,t]
  rw [atRank]
  simp only [extend,dif_pos (e.symm t).isLt,Fin.eta,e.apply_symm_apply]
  exact ⟨rfl,same⟩

end TetraStereo.Engine.RingOriginOrderRanks
assert_kernel_only TetraStereo.Engine.RingOriginOrderRanks.compress
