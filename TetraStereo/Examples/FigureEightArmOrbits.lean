import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import TetraStereo.KernelOnly

/-!
A finite orientation model for the VS262 arm motif. Its eight raw signs are unrestricted.
This file proves only the quotient by the stated physical exchanges and reflection;
it does not establish a CIP priority order or the direction of any source comparison.
-/
namespace TetraStereo.Examples.FigureEightArmOrbits

/-- Proximal sign, central sign, and the two distal signs, in that order. -/
abbrev Branch := Bool × Bool × Bool × Bool
abbrev Arm := Branch × Branch

theorem raw_orientation_count : Fintype.card Arm = 256 := by simp [Arm, Branch]

/-- Exchanging the distal twins is odd at the central frame. -/
def twin (b : Branch) : Branch := (b.1, !b.2.1, b.2.2.2, b.2.2.1)

def branchCode (b : Branch) : Fin 8 :=
  ⟨(if b.1 then 4 else 0) +
    (if b.2.2.1 then (if b.2.2.2 then 1 else if b.2.1 then 2 else 3)
     else if b.2.2.2 then (if b.2.1 then 3 else 2) else 0), by
    rcases b with ⟨p,c,d,e⟩
    cases p <;> cases c <;> cases d <;> cases e <;> decide⟩

/-- Either leave a branch fixed or physically exchange its distal twins. -/
def BranchSwap (a b : Branch) : Prop := b = a ∨ b = twin a

instance (a b : Branch) : Decidable (BranchSwap a b) := inferInstanceAs (Decidable (_ ∨ _))

/-- This is the complete local orbit classification, including homogeneous twins. -/
theorem branchCode_eq_iff (a b : Branch) :
    branchCode a = branchCode b ↔ BranchSwap a b := by
  rcases a with ⟨p,c,d,e⟩
  rcases b with ⟨q,f,g,h⟩
  cases p <;> cases c <;> cases d <;> cases e <;>
    cases q <;> cases f <;> cases g <;> cases h <;> decide

/-- Independent twin exchanges, optionally followed by the nitrogen branch exchange. -/
def PhysicalSwap (a b : Arm) : Prop :=
  (BranchSwap a.1 b.1 ∧ BranchSwap a.2 b.2) ∨
  (BranchSwap a.1 b.2 ∧ BranchSwap a.2 b.1)

/-- The unordered pair of the eight branch types. -/
def orbit (a : Arm) : Fin 8 × Fin 8 :=
  (min (branchCode a.1) (branchCode a.2), max (branchCode a.1) (branchCode a.2))

theorem orbit_eq_iff (a b : Arm) : orbit a = orbit b ↔ PhysicalSwap a b := by
  simp only [orbit, Prod.mk.injEq, PhysicalSwap, ← branchCode_eq_iff]
  have ha := (branchCode a.1).isLt
  have hb := (branchCode a.2).isLt
  have hc := (branchCode b.1).isLt
  have hd := (branchCode b.2).isLt
  simp only [min_def, max_def]
  split_ifs <;> omega

/-- A raw representative of each of the eight branch types. -/
def representative (i : Fin 8) : Branch :=
  (decide (4 ≤ i.val), false,
    decide (i.val % 4 = 1 ∨ i.val % 4 = 3),
    decide (i.val % 4 = 1 ∨ i.val % 4 = 2))

theorem representative_code : ∀ i : Fin 8, branchCode (representative i) = i := by decide

/-- Every sorted pair is realized by a raw eight-sign orientation. -/
theorem orbit_surjective (i j : Fin 8) (h : i ≤ j) :
    orbit (representative i, representative j) = (i,j) := by
  simp [orbit, representative_code, min_eq_left h, max_eq_right h]

def orbitTypes : Finset (Fin 8 × Fin 8) := Finset.univ.filter (fun x => x.1 ≤ x.2)

theorem thirty_six_orbits : orbitTypes.card = 36 := by decide

/-- Every branch type has precisely two raw spellings. -/
theorem branch_fiber_size : ∀ i : Fin 8,
    (Finset.univ.filter fun b : Branch => branchCode b = i).card = 2 := by decide

/-- The fiber sizes distinguish a repeated branch type from two distinct types. -/
def fiberSize (x : Fin 8 × Fin 8) : Nat :=
  (Finset.univ.filter fun a : Arm => orbit a = x).card

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem raw_fiber_sizes : ∀ i j : Fin 8, i ≤ j →
    fiberSize (i,j) = if i = j then 4 else 8 := by decide

/-- Number of ordered pairs of raw orientations in a common physical orbit,
computed as the sum of squared fiber sizes. A separate molecular priority theorem
is needed before interpreting physical orbit equality as a priority tie. -/
def sameOrbitPairCount : Nat := ∑ x ∈ orbitTypes, fiberSize x * fiberSize x

theorem same_orbit_pair_count : sameOrbitPairCount = 1920 := by
  unfold sameOrbitPairCount
  have h : ∀ x ∈ orbitTypes,
      fiberSize x * fiberSize x =
        (if x.1 = x.2 then 4 else 8) * (if x.1 = x.2 then 4 else 8) := by
    intro x hx
    have hle : x.1 ≤ x.2 := (Finset.mem_filter.mp hx).2
    rw [raw_fiber_sizes x.1 x.2 hle]
  rw [Finset.sum_congr rfl h]
  decide

def mirrorBranch (b : Branch) : Branch := (!b.1, !b.2.1, !b.2.2.1, !b.2.2.2)
def mirror (a : Arm) : Arm := (mirrorBranch a.1, mirrorBranch a.2)
def mirrorCode (i : Fin 8) : Fin 8 := branchCode (mirrorBranch (representative i))

theorem mirror_code (b : Branch) :
    branchCode (mirrorBranch b) = mirrorCode (branchCode b) := by
  rcases b with ⟨p,c,d,e⟩
  cases p <;> cases c <;> cases d <;> cases e <;> decide

def selfMirrorTypes : Finset (Fin 8 × Fin 8) := orbitTypes.filter fun x =>
  (min (mirrorCode x.1) (mirrorCode x.2), max (mirrorCode x.1) (mirrorCode x.2)) = x

theorem four_self_mirror_orbits : selfMirrorTypes.card = 4 := by decide

assert_kernel_only raw_orientation_count
assert_kernel_only branchCode_eq_iff
assert_kernel_only orbit_eq_iff
assert_kernel_only orbit_surjective
assert_kernel_only thirty_six_orbits
assert_kernel_only branch_fiber_size
assert_kernel_only raw_fiber_sizes
assert_kernel_only same_orbit_pair_count
assert_kernel_only mirror_code
assert_kernel_only four_self_mirror_orbits

end TetraStereo.Examples.FigureEightArmOrbits
