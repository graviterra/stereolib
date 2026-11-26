import TetraStereo.Engine.OrientedBranchOrbit
import TetraStereo.Examples.FigureEightArmPriority
import TetraStereo.KernelOnly

/-! A molecular-shape realization of the finite VS262 arm exchanges.
The parent edge is fixed at every tetrahedron. Distinct leaf labels retain
H, Cl and terminal methyl identity; nitrogen has no orientation sign.
A true sign denotes negative determinant in [parent, displayed children] order.
The proximal and distal displays are [Cl,H,Q] and [Cl,H,methyl]; the
central display is [H,D1,D2]. These frames agree by even permutation with
the coordinate model's chemical frames.
This bridge asserts physical legal exchanges, not CIP priority completeness. -/
namespace TetraStereo.Examples.FigureEightOrientedBranches
open TetraStereo.Engine.OrientedBranchOrbit
open FigureEightArmOrbits

/-- A terminal carbon with distinct H, Cl and methyl children. -/
def tip (s : Bool) : Tree := .tetra 6 s (.leaf 17) (.leaf 1) (.leaf 106)

/-- The central carbon has H and two constitutionally identical distal tips. -/
def central (b : Branch) : Tree :=
  .tetra 6 b.2.1 (.leaf 1) (tip b.2.2.1) (tip b.2.2.2)

/-- A proximal carbon retains its distinct H and chlorine side ligands. -/
def branch (b : Branch) : Tree :=
  .tetra 6 b.1 (.leaf 17) (.leaf 1) (central b)

/-- An unoriented nitrogen joins the two proximal branches. -/
def arm (a : Arm) : Tree := .ordinary 7 (branch a.1) (branch a.2)

theorem central_twin (b : Branch) : Legal (central b) (central (twin b)) := by
  exact Legal.swap23 6 b.2.1 (.leaf 1) (tip b.2.2.1) (tip b.2.2.2)

theorem branch_twin (b : Branch) : Legal (branch b) (branch (twin b)) := by
  exact Legal.tetra 6 b.1 (Legal.refl _) (Legal.refl _) (central_twin b)

theorem branch_legal_of_swap {a b : Branch} (h : BranchSwap a b) :
    Legal (branch a) (branch b) := by
  rcases h with rfl | rfl
  · exact Legal.refl _
  · exact branch_twin a

/-- Every physical exchange in the eight-sign model is an independently
specified legal recursive branch relabelling. -/
theorem legal_of_physicalSwap {a b : Arm} (h : PhysicalSwap a b) :
    Legal (arm a) (arm b) := by
  rcases h with h | h
  · exact Legal.ordinary 7 (branch_legal_of_swap h.1) (branch_legal_of_swap h.2)
  · exact Legal.trans
      (Legal.ordinary 7 (branch_legal_of_swap h.1) (branch_legal_of_swap h.2))
      (Legal.ordinarySwap 7 _ _)

theorem canonical_eq_of_physicalSwap {a b : Arm} (h : PhysicalSwap a b) :
    canonical (arm a) = canonical (arm b) :=
  canonical_eq_of_legal (legal_of_physicalSwap h)

theorem canonical_eq_of_orbit_eq {a b : Arm} (h : orbit a = orbit b) :
    canonical (arm a) = canonical (arm b) :=
  canonical_eq_of_physicalSwap ((orbit_eq_iff a b).mp h)

/-- A small discriminator used only for the converse. Hash collisions on
arbitrary trees are harmless: only separation of the eight branch types is used. -/
private def pair (a b : Nat) : Nat := (a + b) * (a + b + 1) + 2*b
private def display (n : Nat) (s : Bool) (a b c : Nat) : Nat :=
  (pair n (pair (if s then 1 else 0) (pair a (pair b c)))) % 1000003
private def six (n : Nat) (s : Bool) (a b c : Nat) : Nat :=
  min (display n s a b c) (min (display n s b c a)
    (min (display n s c a b) (min (display n (!s) b a c)
      (min (display n (!s) a c b) (display n (!s) c b a)))))
private def invariant : Tree → Nat
  | .leaf n => n
  | .unary n a => pair n (invariant a)
  | .ordinary n a b => pair n (pair (min (invariant a) (invariant b))
      (max (invariant a) (invariant b)))
  | .tetra n s a b c => six n s (invariant a) (invariant b) (invariant c)

private theorem invariant_legal {t u : Tree} (h : Legal t u) : invariant t = invariant u := by
  induction h with
  | refl => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | unary n _ ih => simp only [invariant, ih]
  | ordinary n _ _ ih₁ ih₂ => simp only [invariant, ih₁, ih₂]
  | tetra n s _ _ _ ih₁ ih₂ ih₃ => simp only [invariant, ih₁, ih₂, ih₃]
  | ordinarySwap n a b => simp only [invariant, min_comm, max_comm]
  | swap12 n s a b c => simp only [invariant, six, Bool.not_not]; omega
  | swap23 n s a b c => simp only [invariant, six, Bool.not_not]; omega

private def branchInvariant (i : Fin 8) : Nat := invariant (branch (representative i))

private theorem branch_invariant (b : Branch) :
    invariant (branch b) = branchInvariant (branchCode b) := by
  rcases b with ⟨p,c,d,e⟩
  cases p <;> cases c <;> cases d <;> cases e <;> decide

private theorem branchInvariant_injective : Function.Injective branchInvariant := by decide

private theorem pair_injective {a b c d : Nat} (h : pair a b = pair c d) : a = c ∧ b = d := by
  unfold pair at h
  have hs : a+b = c+d := by nlinarith
  constructor <;> nlinarith

/-- Arbitrary recursive legal relabellings introduce no additional arm identifications. -/
theorem physicalSwap_of_legal {a b : Arm} (h : Legal (arm a) (arm b)) : PhysicalSwap a b := by
  have hi := invariant_legal h
  simp only [arm, invariant, branch_invariant] at hi
  have hp := pair_injective (pair_injective hi).2
  have values :
      (branchInvariant (branchCode a.1) = branchInvariant (branchCode b.1) ∧
       branchInvariant (branchCode a.2) = branchInvariant (branchCode b.2)) ∨
      (branchInvariant (branchCode a.1) = branchInvariant (branchCode b.2) ∧
       branchInvariant (branchCode a.2) = branchInvariant (branchCode b.1)) := by
    simp only [min_def, max_def] at hp
    split_ifs at hp <;> omega
  rcases values with h | h
  · exact Or.inl ⟨(branchCode_eq_iff _ _).mp (branchInvariant_injective h.1),
      (branchCode_eq_iff _ _).mp (branchInvariant_injective h.2)⟩
  · exact Or.inr ⟨(branchCode_eq_iff _ _).mp (branchInvariant_injective h.1),
      (branchCode_eq_iff _ _).mp (branchInvariant_injective h.2)⟩

theorem legal_iff_physicalSwap (a b : Arm) : Legal (arm a) (arm b) ↔ PhysicalSwap a b :=
  ⟨physicalSwap_of_legal, legal_of_physicalSwap⟩

theorem canonical_eq_iff_physicalSwap (a b : Arm) :
    canonical (arm a) = canonical (arm b) ↔ PhysicalSwap a b := by
  rw [canonical_eq_iff_legal, legal_iff_physicalSwap]

/-- The finite four-pass motif priority ties exactly on legal recursive
relabellings of this VS262 shape; this is not a universal CIP claim. -/
theorem priority_tie_iff_legal (a b : Arm) :
    FigureEightArmPriority.armPriority a = FigureEightArmPriority.armPriority b ↔
      Legal (arm a) (arm b) := by
  rw [FigureEightArmPriority.tie_iff_exchange, legal_iff_physicalSwap]

assert_kernel_only priority_tie_iff_legal
assert_kernel_only legal_iff_physicalSwap
assert_kernel_only canonical_eq_iff_physicalSwap
assert_kernel_only legal_of_physicalSwap
assert_kernel_only canonical_eq_of_physicalSwap
assert_kernel_only canonical_eq_of_orbit_eq
end TetraStereo.Examples.FigureEightOrientedBranches
