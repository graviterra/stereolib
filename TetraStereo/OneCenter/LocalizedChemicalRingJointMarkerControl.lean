
























































import TetraStereo.KernelOnly
import Mathlib.Data.Fintype.Basic
import Mathlib.Logic.Equiv.Defs

set_option autoImplicit false

namespace TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerControl

/-! ## 1. The minimum invariant: single ties versus joint ties -/

section Generic

variable {V : Type*}

/-- `g` fixes every point satisfying the predicate `P`. -/
def Fixes (g : Equiv.Perm V) (P : V → Prop) : Prop :=
  ∀ v, P v → g v = v

/-- A joint tie: an admissible permutation `g` (admissibility is the predicate `G`) fixes
every marked point and sends the entry `e` to `e'`. -/
def JointTie (G : Equiv.Perm V → Prop) (P : V → Prop) (e e' : V) : Prop :=
  ∃ g : Equiv.Perm V, G g ∧ Fixes g P ∧ g e = e'

/-- A tie under a single mark `m`.  This is the abstract counterpart of "the one-mark key
agrees on the two slots". -/
def SingleTie (G : Equiv.Perm V → Prop) (m e e' : V) : Prop :=
  JointTie G (fun v => v = m) e e'

/-- Monotonicity of the mark constraint: if `P ⊆ Q` then fixing `Q` is stronger, so a
joint tie under `Q` is a joint tie under `P`. -/
theorem jointTie_mono {G : Equiv.Perm V → Prop} {P Q : V → Prop} {e e' : V}
    (hPQ : ∀ v, P v → Q v) (h : JointTie G Q e e') : JointTie G P e e' := by
  rcases h with ⟨g, hG, hfix, hmove⟩
  exact ⟨g, hG, fun v hv => hfix v (hPQ v hv), hmove⟩

/-- A joint tie is a single tie for each of its marks.  This is the soundness direction:
the joint key can only be finer than (a consequence of) every single-mark key. -/
theorem jointTie_to_single {G : Equiv.Perm V → Prop} {P : V → Prop} {e e' : V} (m : V)
    (hm : P m) (h : JointTie G P e e') : SingleTie G m e e' :=
  jointTie_mono (P := fun v => v = m) (Q := P) (fun _ hv => hv.symm ▸ hm) h

/-- Adding a mark that is already marked does not change the joint tie.  Duplicate marks
are therefore redundant as constraints. No de-duplication requirement for an executable
encoding or canonical layout is established here. -/
theorem jointTie_insert_iff {G : Equiv.Perm V → Prop} {P : V → Prop} {e e' m : V}
    (hm : P m) :
    JointTie G (fun v => v = m ∨ P v) e e' ↔ JointTie G P e e' := by
  constructor
  · intro h
    exact jointTie_mono (P := P) (Q := fun v => v = m ∨ P v) (fun v hv => Or.inr hv) h
  · intro h
    exact jointTie_mono (P := fun v => v = m ∨ P v) (Q := P)
      (fun v hv => hv.elim (fun hvm => hvm.symm ▸ hm) (fun hp => hp)) h

/-- If a compared entry is itself fixed by the mark set, no joint tie can move it.  This
covers both "the mark coincides with the entry" and "the entry is a history endpoint that
was pushed into the mark list". -/
theorem not_jointTie_of_fixed_entry {G : Equiv.Perm V → Prop} {P : V → Prop} {e e' : V}
    (hPe : P e) (hne : e ≠ e') : ¬ JointTie G P e e' := by
  rintro ⟨g, _hG, hfix, hmove⟩
  have h : g e = e := hfix e hPe
  rw [h] at hmove
  exact hne hmove

/-- Corollary: a mark that coincides with the compared entry kills the tie. -/
theorem not_jointTie_of_entry_mark {G : Equiv.Perm V → Prop} {P : V → Prop} {e e' : V}
    (hne : e ≠ e') : ¬ JointTie G (fun v => v = e ∨ P v) e e' :=
  not_jointTie_of_fixed_entry (G := G) (P := fun v => v = e ∨ P v) (Or.inl rfl) hne

/-- Reflexivity: if the identity is admissible, every entry is jointly tied to itself. -/
theorem jointTie_refl {G : Equiv.Perm V → Prop} (hG : G (Equiv.refl V)) {P : V → Prop}
    (e : V) : JointTie G P e e :=
  ⟨Equiv.refl V, hG, fun _ _ => rfl, rfl⟩

end Generic

/-! ## 2. Concrete six-point Klein-four witness

Carrier `Fin 6`, read as
`0 = a`, `1 = a'`, `2 = b`, `3 = b'`, `4 = x`, `5 = y`.

The admissible symmetries are the four permutations

* `alpha = (x y)(b b')`   — fixes `a`, `a'`; moves `b`; ties `x ↦ y`;
* `beta  = (x y)(a a')`   — fixes `b`, `b'`; moves `a`; ties `x ↦ y`;
* `gamma = (a a')(b b')`  — fixes `x`, `y`; moves both `a` and `b`;
* `refl`.

They form a Klein four-group.  `alpha` is a single-mark tie for `a`, `beta` is a
single-mark tie for `b`, yet no one of the four fixes both `a` and `b` while moving
`x ↦ y`: the two single-mark layouts admit no common isomorphism. -/

abbrev V6 := Fin 6

/-- The `a`-mark. -/
def markA : V6 := 0
/-- The other atom of the `a`-pair. -/
def markA' : V6 := 1
/-- The `b`-mark. -/
def markB : V6 := 2
/-- The first compared entry. -/
def entryX : V6 := 4
/-- The second compared entry. -/
def entryY : V6 := 5

/-- The involution `(x y)(b b') = (4 5)(2 3)`. -/
def alphaFun (v : V6) : V6 :=
  if v = 4 then 5 else if v = 5 then 4 else if v = 2 then 3 else if v = 3 then 2 else v

/-- The involution `(x y)(a a') = (4 5)(0 1)`. -/
def betaFun (v : V6) : V6 :=
  if v = 4 then 5 else if v = 5 then 4 else if v = 0 then 1 else if v = 1 then 0 else v

/-- The involution `(a a')(b b') = (0 1)(2 3)`. -/
def gammaFun (v : V6) : V6 :=
  if v = 2 then 3 else if v = 3 then 2 else if v = 0 then 1 else if v = 1 then 0 else v

theorem alphaFun_involutive : ∀ v : V6, alphaFun (alphaFun v) = v := by decide

theorem betaFun_involutive : ∀ v : V6, betaFun (betaFun v) = v := by decide

theorem gammaFun_involutive : ∀ v : V6, gammaFun (gammaFun v) = v := by decide

/-- `alpha = (x y)(b b')`. -/
def alpha : Equiv.Perm V6 := ⟨alphaFun, alphaFun, alphaFun_involutive, alphaFun_involutive⟩

/-- `beta = (x y)(a a')`. -/
def beta : Equiv.Perm V6 := ⟨betaFun, betaFun, betaFun_involutive, betaFun_involutive⟩

/-- `gamma = (a a')(b b')`. -/
def gamma : Equiv.Perm V6 := ⟨gammaFun, gammaFun, gammaFun_involutive, gammaFun_involutive⟩

/-- The declared symmetry group of the control structure: the four Klein-four elements. -/
def Admissible (g : Equiv.Perm V6) : Prop :=
  g = Equiv.refl V6 ∨ g = alpha ∨ g = beta ∨ g = gamma

theorem admissible_alpha : Admissible alpha := Or.inr (Or.inl rfl)

theorem admissible_beta : Admissible beta := Or.inr (Or.inr (Or.inl rfl))

theorem admissible_gamma : Admissible gamma := Or.inr (Or.inr (Or.inr rfl))

theorem admissible_refl : Admissible (Equiv.refl V6) := Or.inl rfl

/-! ### Concrete action facts (closed computations on `Fin 6`) -/

theorem alpha_fixes_A : alpha markA = markA := by decide

theorem alpha_fixes_A' : alpha markA' = markA' := by decide

theorem alpha_moves_B : alpha markB ≠ markB := by decide

theorem alpha_moves_entry : alpha entryX = entryY := by decide

theorem beta_fixes_B : beta markB = markB := by decide

theorem beta_moves_A : beta markA ≠ markA := by decide

theorem beta_moves_entry : beta entryX = entryY := by decide

theorem gamma_moves_A : gamma markA ≠ markA := by decide

theorem gamma_fixes_entry : gamma entryX ≠ entryY := by decide

theorem refl_fixes_entry : (Equiv.refl V6) entryX ≠ entryY := by decide

/-! ### The core witness -/

/-- Single-mark key for `a` ties the two entries (witnessed by `alpha`). -/
theorem single_markA : SingleTie Admissible markA entryX entryY := by
  refine ⟨alpha, admissible_alpha, ?_, alpha_moves_entry⟩
  intro v hv
  rw [hv]
  exact alpha_fixes_A

/-- Single-mark key for `b` ties the two entries (witnessed by `beta`). -/
theorem single_markB : SingleTie Admissible markB entryX entryY := by
  refine ⟨beta, admissible_beta, ?_, beta_moves_entry⟩
  intro v hv
  rw [hv]
  exact beta_fixes_B

/-- No admissible symmetry fixes both marks and moves the entry. -/
theorem no_joint_AB :
    ¬ JointTie Admissible (fun v => v = markA ∨ v = markB) entryX entryY := by
  rintro ⟨g, hg, hfix, hX⟩
  have hA : g markA = markA := hfix markA (Or.inl rfl)
  have hB : g markB = markB := hfix markB (Or.inr rfl)
  rcases hg with h | h | h | h
  · rw [h] at hX; exact absurd hX (by decide)
  · rw [h] at hB; exact absurd hB (by decide)
  · rw [h] at hA; exact absurd hA (by decide)
  · rw [h] at hA; exact absurd hA (by decide)

/-- **Main control statement.**  Separate single-mark fixing symmetries exist on `(entryX, entryY)`, but no
admissible symmetry fixes both marks. No executable canonical key is evaluated here. -/
theorem single_keys_agree_joint_fails :
    SingleTie Admissible markA entryX entryY ∧
    SingleTie Admissible markB entryX entryY ∧
    ¬ JointTie Admissible (fun v => v = markA ∨ v = markB) entryX entryY :=
  ⟨single_markA, single_markB, no_joint_AB⟩




theorem single_ties_do_not_imply_joint :
    ¬ (∀ (V : Type) (G : Equiv.Perm V → Prop) (a b x y : V),
        SingleTie G a x y → SingleTie G b x y →
        JointTie G (fun v => v = a ∨ v = b) x y) := by
  intro h
  exact no_joint_AB (h V6 Admissible markA markB entryX entryY single_markA single_markB)

/-! ### Over-refinement: retaining every mark can destroy a valid tie -/

/-- With only the two marks `a`, `a'`, `alpha` is a joint tie of the entries. -/
theorem joint_small :
    JointTie Admissible (fun v => v = markA ∨ v = markA') entryX entryY := by
  refine ⟨alpha, admissible_alpha, ?_, alpha_moves_entry⟩
  intro v hv
  rcases hv with h | h
  · rw [h]; exact alpha_fixes_A
  · rw [h]; exact alpha_fixes_A'

/-- Adding the third mark `b` destroys exactly that tie. -/
theorem not_joint_big :
    ¬ JointTie Admissible (fun v => v = markA ∨ v = markA' ∨ v = markB) entryX entryY := by
  rintro ⟨g, hg, hfix, hX⟩
  have hA : g markA = markA := hfix markA (Or.inl rfl)
  have hB : g markB = markB := hfix markB (Or.inr (Or.inr rfl))
  rcases hg with h | h | h | h
  · rw [h] at hX; exact absurd hX (by decide)
  · rw [h] at hB; exact absurd hB (by decide)
  · rw [h] at hA; exact absurd hA (by decide)
  · rw [h] at hA; exact absurd hA (by decide)

/-- **Over-refinement control.**  The full mark list is strictly finer: a joint tie under
`{a, a'}` need not survive the addition of `b`.  If the physical report only requires
fixing a subset of marks, retaining all of them can silently lose corrections. -/
theorem retains_all_marks_over_refines :
    JointTie Admissible (fun v => v = markA ∨ v = markA') entryX entryY ∧
    ¬ JointTie Admissible (fun v => v = markA ∨ v = markA' ∨ v = markB) entryX entryY :=
  ⟨joint_small, not_joint_big⟩

/-! ### Duplicate marks and entry/history degeneracies -/

/-- Duplicate `a` in the mark list leaves the joint tie unchanged (set semantics). -/
theorem duplicate_mark_AB :
    JointTie Admissible (fun v => v = markA ∨ (v = markA ∨ v = markB)) entryX entryY ↔
    JointTie Admissible (fun v => v = markA ∨ v = markB) entryX entryY :=
  jointTie_insert_iff (G := Admissible) (P := fun v => v = markA ∨ v = markB)
    (m := markA) (e := entryX) (e' := entryY) (Or.inl rfl)

/-- If the compared entry `entryX` is itself retained as a mark, no joint tie is possible.
This is the intended separation imposed by fixing the entry; it establishes no special
treatment requirement for duplicate occurrences or history endpoints. -/
theorem entry_mark_kills_tie :
    ¬ JointTie Admissible (fun v => v = entryX ∨ (v = markA ∨ v = markB)) entryX entryY :=
  not_jointTie_of_entry_mark (G := Admissible) (P := fun v => v = markA ∨ v = markB)
    (e := entryX) (e' := entryY) (by decide)

end TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerControl

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerControl.single_keys_agree_joint_fails
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerControl.single_ties_do_not_imply_joint
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerControl.retains_all_marks_over_refines
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerControl.duplicate_mark_AB
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerControl.entry_mark_kills_tie
