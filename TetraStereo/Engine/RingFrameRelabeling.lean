import TetraStereo.Engine.RingGeometryCriterion

set_option autoImplicit false

namespace TetraStereo.Engine.RingFrameRelabeling
open OneCenter
open RingActivePairReport (Slot)
open LocalizedChemicalRing.ConstitutionalPartition (Pair pairs)

private def factor : Ordering → Int
  | .lt => -1 | .eq => 0 | .gt => 1

private theorem product {α : Type} (xs : List α) (cmp : α → Ordering) :
    (xs.map (fun x => factor (cmp x))).prod =
      if xs.any (fun x => cmp x == .eq) then 0
      else if xs.countP (fun x => cmp x == .lt) % 2 = 0 then 1 else -1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases h : cmp x <;> simp only [List.map_cons,List.prod_cons,List.any_cons,List.countP_cons,h,ih]
    all_goals
      cases t : xs.any (fun x => cmp x == .eq) <;>
        by_cases even : xs.countP (fun x => cmp x == .lt) % 2 = 0 <;>
        simp [factor,even,Nat.add_mod] <;> omega

private def image (s : Slot → Slot) (p : Pair) : Pair :=
  if s p.1 < s p.2 then (s p.1,s p.2) else (s p.2,s p.1)

private def direction (s : Slot → Slot) (p : Pair) : Int := if s p.1 < s p.2 then 1 else -1

def sign (s : Equiv.Perm Slot) : Int := if RawMolecule.permutationIsEven ((List.finRange 4).map (fun k => (s k).val)) then 1 else -1

private theorem transport_pairs (s : Equiv.Perm Slot) :
    (pairs.map (image s)).Perm pairs ∧ (pairs.map (direction s)).prod = sign s := by
  have all : ∀ a b c d : Slot, [a,b,c,d].Perm (List.finRange 4) →
      let f (k : Slot) := [a,b,c,d][k.val]!
      (pairs.map (image f)).Perm pairs ∧ (pairs.map (direction f)).prod =
        (if RawMolecule.permutationIsEven ([a,b,c,d].map Fin.val) then 1 else -1) := by decide +kernel
  have listed : [s 0,s 1,s 2,s 3].Perm (List.finRange 4) := s.map_finRange_perm
  have eqn : (fun k : Slot => [s 0,s 1,s 2,s 3][k.val]!) = s := by funext k; fin_cases k <;> rfl
  simpa only [eqn] using all _ _ _ _ listed

theorem alternating {α : Type} [Ord α] [Std.OrientedOrd α] (s : Equiv.Perm Slot) (key : Slot → α) :
    RingOrientation.orientation (fun k => key (s k)) = sign s * RingOrientation.orientation key := by
  let weight (p : Pair) := factor (compare (key p.1) (key p.2))
  have same (p : Pair) : factor (compare (key (s p.1)) (key (s p.2))) = direction s p * weight (image s p) := by
    unfold direction image weight
    split
    · simp
    · rw [Std.OrientedCmp.eq_swap (cmp := compare) (a := key (s p.1)) (b := key (s p.2))]
      cases compare (key (s p.2)) (key (s p.1)) <;> decide
  change _ = sign s * (if _ then _ else _)
  rw [RingOrientation.orientation,← product,← product]
  simp only [same,List.prod_map_mul,(transport_pairs s).2]
  exact congrArg (sign s * ·) (by
    have h := ((transport_pairs s).1.map weight).prod_eq
    simpa [List.map_map,Function.comp_def,weight] using h)

theorem sign_squared (s : Equiv.Perm Slot) : sign s * sign s = 1 := by unfold sign; split <;> decide

theorem pairs_unchanged (s : Equiv.Perm Slot) (p : Pair → Bool)
    (symmetric : ∀ j k : Slot, p (j,k) = p (k,j)) :
    pairs.countP (fun z => p (s z.1,s z.2)) = pairs.countP p := by
  have h := (transport_pairs s).1.countP_eq p
  rw [List.countP_map] at h
  apply Eq.trans _ h
  apply (List.Perm.refl pairs).countP_congr
  intro z _
  dsimp only [Function.comp_apply,image]
  split <;> first | rfl | exact symmetric _ _

end TetraStereo.Engine.RingFrameRelabeling
assert_kernel_only TetraStereo.Engine.RingFrameRelabeling.alternating
