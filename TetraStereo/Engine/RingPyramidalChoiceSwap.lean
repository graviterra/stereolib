import TetraStereo.Engine.RingHydrogenReport

/-! Changing the order of the two retained neighbors at any number of
pyramidal hydrogen sites permutes the complete placement search. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPyramidalChoices
open OneCenter RingHydrogenCompletion

def Site.flip (s : Site) : Site :=
  ⟨s.parent,s.hydrogen,s.second,s.first,s.center,s.secondPoint,s.firstPoint⟩

@[simp] theorem Site.flip_flip (s : Site) : s.flip.flip = s := rfl

@[simp] theorem Site.flip_plus (s : Site) : s.flip.plus = s.minus := by
  change CartesianPoint3.mk _ _ _ = CartesianPoint3.mk _ _ _
  rw [CartesianPoint3.mk.injEq]
  refine ⟨?_,?_,?_⟩ <;> dsimp [Site.flip,pairPlus,pairMinus,vadd,vsub,vcross] <;> ring

@[simp] theorem Site.flip_minus (s : Site) : s.flip.minus = s.plus :=
  (s.flip.flip_plus).symm

theorem Site.flip_normal_nonzero (s : Site) : s.flip.normal ≠ zeroVector ↔ s.normal ≠ zeroVector := by
  have one (t : Site) (h : t.normal = zeroVector) : t.flip.normal = zeroVector := by
    have x := congrArg CartesianPoint3.x h
    have y := congrArg CartesianPoint3.y h
    have z := congrArg CartesianPoint3.z h
    change CartesianPoint3.mk _ _ _ = CartesianPoint3.mk _ _ _
    rw [CartesianPoint3.mk.injEq]
    refine ⟨?_,?_,?_⟩ <;> dsimp [Site.flip,Site.normal,zeroVector,vcross,vsub] at * <;> linarith
  exact not_congr ⟨one s.flip, one s⟩

theorem choices_perm_of_related {xs ys : List Site}
    (related : List.Forall₂ (fun a b => b = a ∨ b = a.flip) xs ys) (ps : List Point) :
    (choices xs ps).Perm (choices ys ps) := by
  induction related generalizing ps with
  | nil => rfl
  | @cons a b xs ys h _ ih =>
    rcases h with h | h
    · subst b
      simpa only [choices] using
        (ih (ps.set a.hydrogen a.plus)).append (ih (ps.set a.hydrogen a.minus))
    · subst b
      simp only [choices,Site.flip_plus,Site.flip_minus]
      exact ((ih _).append (ih _)).trans List.perm_append_comm

end TetraStereo.Engine.RingPyramidalChoices
assert_kernel_only TetraStereo.Engine.RingPyramidalChoices.choices_perm_of_related
