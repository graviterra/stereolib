import TetraStereo.Engine.LocalizedChemicalRingExactCertificate

set_option autoImplicit false

namespace TetraStereo.Engine.LocalizedChemicalRing

open OneCenter
open scoped Classical

/-- Give only the marked slot a fresh preference inside its copied class. -/
def directKey {K : Type} (old : Fin 4 → K) (mark i : Fin 4) : Lex (K × Bool) :=
  toLex (old i, decide (i = mark))

open LocalizedMarkedRetainedOrdinaryRanking (keyOrder keyOrder_perm)
open LocalizedGenericMarkedRecalculation (Geometry readback? consensus)

/-- Direct marking reads a letter only from a fully distinguished four-slot order.
Geometry is indexed by slot, so it can be the pullback of any molecular frame. -/
noncomputable def directReading {K : Type} [LinearOrder K] (geom : Geometry)
    (old : Fin 4 → K) (mark : Fin 4) : Option RS :=
  if Function.Injective (directKey old mark) then
    readback? geom ((keyOrder (directKey old mark) (List.finRange 4)).map Fin.val)
  else none

private theorem directReading_opposite {K : Type} [LinearOrder K] (geom : Geometry)
    (old : Fin 4 → K) (tied : ¬ Function.Injective old) (a b : Fin 4) (ne : a ≠ b)
    (sa : Function.Injective (directKey old a)) (sb : Function.Injective (directKey old b)) :
    directReading geom old b = (directReading geom old a).map RS.swap := by
  have cover (m : Fin 4) (strict : Function.Injective (directKey old m)) (x y : Fin 4)
      (diff : x ≠ y) (same : old x = old y) : x = m ∨ y = m := by
    by_contra! h
    exact diff ((directMark_injective_iff old m).mp strict x y h.1 h.2 same)
  have ab : old a = old b := by
    obtain ⟨x,y,same,diff⟩ : ∃ x y, old x = old y ∧ x ≠ y := by
      by_contra! h
      exact tied (fun {x y} eq => h x y eq)
    rcases cover a sa x y diff same with xa | ya <;>
      rcases cover b sb x y diff same with xb | yb <;> grind
  let e := Equiv.swap a b
  have exchange (x : Fin 4) : directKey old b (e x) = directKey old a x := by
    by_cases ha : x = a
    · subst x
      simp [directKey,e,ab]
    by_cases hb : x = b
    · subst x
      simp [directKey,e,ne,ne.symm,ab]
    simp [directKey,e,Equiv.swap_apply_of_ne_of_ne ha hb,ha,hb]
  let ranked := keyOrder (directKey old a) (List.finRange 4)
  have order := LocalizedChemicalRingOrderingTransport.keyOrder_transport_of_injective
    e (directKey old a) (directKey old b) _ _ e.map_finRange_perm.symm
    (fun i _ => exchange i) (fun _ _ _ _ h => sa h)
  have natSwap (i : Fin 4) :
      (e i).val = LocalizedMarkedTerminalGaugeSwap.swapAtom a.val b.val i.val := by
    by_cases ha : i = a
    · subst i
      simp [e, LocalizedMarkedTerminalGaugeSwap.swapAtom]
    by_cases hb : i = b
    · subst i
      simp [e, LocalizedMarkedTerminalGaugeSwap.swapAtom, Fin.val_inj, ne.symm]
    simp [e, Equiv.swap_apply_of_ne_of_ne ha hb,
      LocalizedMarkedTerminalGaugeSwap.swapAtom, Fin.val_inj, ha,hb]
  have perm : ranked.Perm (List.finRange 4) := keyOrder_perm _ _
  have mem (x : Fin 4) : x.val ∈ ranked.map Fin.val :=
    List.mem_map.mpr ⟨x, perm.mem_iff.mpr (List.mem_finRange x), rfl⟩
  have mapped : (ranked.map e).map Fin.val =
      (ranked.map Fin.val).map (LocalizedMarkedTerminalGaugeSwap.swapAtom a.val b.val) := by
    simp only [List.map_map]
    exact List.map_congr_left (fun i _ => natSwap i)
  simp only [directReading,if_pos sa,if_pos sb,order]
  rw [show ((keyOrder (directKey old a) (List.finRange 4)).map e).map Fin.val = _ from mapped]
  exact LocalizedMarkedTerminalGaugeSwap.readback_swapAtom geom a.val b.val
    (fun h => ne (Fin.ext h)) _ ((perm.nodup_iff.mpr (List.nodup_finRange 4)).map Fin.val_injective)
    (by simpa using perm.length_eq) (mem a) (mem b)

/-- In a tied frame, arbitrarily many direct point promotions cannot agree on a letter
when at least two distinct marks are tried. This includes arbitrary geometries and
incomplete readings. Both fresh and copied direct-only policies therefore refuse
whenever each starts its trials from a tied partition. -/
theorem directPromotion_consensus_none {K : Type} [LinearOrder K] (geom : Geometry)
    (old : Fin 4 → K) (tied : ¬ Function.Injective old) (marks : List (Fin 4))
    (a b : Fin 4) (ha : a ∈ marks) (hb : b ∈ marks) (ne : a ≠ b) :
    consensus (marks.map (directReading geom old)) = none := by
  cases h : consensus (marks.map (directReading geom old)) with
  | none => rfl
  | some letter =>
    have same := ((LocalizedChemicalRingSenseTransport.consensus_eq_some_iff _ _).mp h).2
    have value (m : Fin 4) (hm : m ∈ marks) : directReading geom old m = some letter :=
      same _ (List.mem_map.mpr ⟨m,hm,rfl⟩)
    have strict (m : Fin 4) (hm : m ∈ marks) : Function.Injective (directKey old m) := by
      by_contra missing
      simpa [directReading,missing] using value m hm
    have opp := directReading_opposite geom old tied a b ne (strict a ha) (strict b hb)
    rw [value a ha,value b hb] at opp
    cases letter <;> contradiction

end TetraStereo.Engine.LocalizedChemicalRing

assert_kernel_only TetraStereo.Engine.LocalizedChemicalRing.directPromotion_consensus_none
