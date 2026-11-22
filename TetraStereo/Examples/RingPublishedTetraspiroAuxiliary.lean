import TetraStereo.Examples.RingTetraspiroVisitRules

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 60000

namespace TetraStereo.Examples.RingPublishedTetraspiroAuxiliary
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingChemicalPriority RingSeededPairs RingPublishedTetraspiro

/-- Every unconfigured tetrahedral carbon in this molecule carries two
constitutionally and isotopically interchangeable terminal ligands. -/
theorem omitted_carbons :
    ∀ k : Fin molecule.atomCount, RingTerminalPair.Focus molecule k.val →
      k.val ∉ centers → (RingTerminalPair.check? molecule k.val).isSome = true := by
  decide +kernel

private theorem map_of_rows {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : List.Forall₂ (fun x y => f x = some y) xs ys) : xs.mapM f = some ys := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [head,ih]

local macro "each_row" : tactic =>
  `(tactic| (apply map_of_rows; repeat' first | apply List.Forall₂.cons | exact List.Forall₂.nil | decide +kernel))

theorem all_occurrences :
    paths.mapM (auxiliary spatial) = some hands ∧
    paths.mapM (auxiliary reflected) = some (hands.map RS.swap) := by
  constructor <;> each_row

theorem all_arms :
    arms.mapM (fun (root,arm) => summary? spatial root arm) = some words ∧
    arms.mapM (fun (root,arm) => summary? reflected root arm) = some (words.map (List.map RS.swap)) := by
  constructor <;> each_row

/-- For all eight molecular branches these are the fifteen unfiltered
positions. Exactly three sites publish a hand. -/
def occupied : List RS → List (Option RS)
  | [a,b,c] => [some a,none,some b,none,none,none,some c] ++ List.replicate 8 none
  | _ => []

private theorem sample_walk : sourceWalk? spatial 2 9 = some (occupied [.S,.S,.S]) := by
  decide +kernel

theorem sourceWalk_table :
    arms.mapM (fun (r,a) => sourceWalk? spatial r a) = some (words.map occupied) ∧
    arms.mapM (fun (r,a) => sourceWalk? reflected r a) = some (words.map fun w => occupied (w.map RS.swap)) := by
  constructor <;> each_row

private theorem read_rows {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (seen : xs.mapM f = some ys) : List.Forall₂ (fun x y => f x = some y) xs ys := by
  induction xs generalizing ys with
  | nil => obtain rfl := Option.some.inj seen; exact .nil
  | cons x xs ih =>
    rw [List.mapM_cons] at seen
    cases h : f x <;> cases t : xs.mapM f <;> simp [h,t] at seen
    subst ys
    exact .cons h (ih t)

theorem original_walk (k : Fin 8) :
    sourceWalk? spatial (arms.get ⟨k.val,k.isLt⟩).1 (arms.get ⟨k.val,k.isLt⟩).2 =
      some (occupied (words.get ⟨k.val,k.isLt⟩)) := by
  have f := (read_rows sourceWalk_table.1).get (i := k.val) k.isLt (by simp [words])
  simpa using f

theorem reflected_walk (k : Fin 8) :
    sourceWalk? reflected (arms.get ⟨k.val,k.isLt⟩).1 (arms.get ⟨k.val,k.isLt⟩).2 =
      some (occupied ((words.get ⟨k.val,k.isLt⟩).map RS.swap)) := by
  have f := (read_rows sourceWalk_table.2).get (i := k.val) k.isLt (by simp [words])
  simpa using f

theorem all_matches : edges.mapM (fun (r,x,y) => matched? r x y) = some [true,true,true,true] := by
  each_row

private theorem edge_of {sp r x y xs ys} {d : Decision} (match' : matched? r x y = some true)
    (l : sourceWalk? sp r x = some xs) (s : sourceWalk? sp r y = some ys)
    (score : fromVisits? xs ys xs ys xs ys = some d) : forward? sp r x y = some d := by
  simp [forward?,match',l,s,score]

theorem forward_edges :
    edges.mapM (fun (r,x,y) => forward? spatial r x y) =
      some [⟨1,none⟩,⟨0,some 2⟩,⟨1,none⟩,⟨0,some (-2)⟩] ∧
    edges.mapM (fun (r,x,y) => forward? reflected r x y) =
      some [⟨1,none⟩,⟨0,some (-2)⟩,⟨1,none⟩,⟨0,some 2⟩] := by
  have matchAt (i : Fin 4) := (read_rows all_matches).get (i := i.val) i.isLt i.isLt
  constructor <;> apply map_of_rows
  · refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
    · exact edge_of (matchAt 0) (original_walk 0) (original_walk 1) (by decide +kernel)
    · exact edge_of (matchAt 1) (original_walk 2) (original_walk 3) (by decide +kernel)
    · exact edge_of (matchAt 2) (original_walk 4) (original_walk 5) (by decide +kernel)
    · exact edge_of (matchAt 3) (original_walk 6) (original_walk 7) (by decide +kernel)
  · refine .cons ?_ (.cons ?_ (.cons ?_ (.cons ?_ .nil)))
    · exact edge_of (matchAt 0) (reflected_walk 0) (reflected_walk 1) (by decide +kernel)
    · exact edge_of (matchAt 1) (reflected_walk 2) (reflected_walk 3) (by decide +kernel)
    · exact edge_of (matchAt 2) (reflected_walk 4) (reflected_walk 5) (by decide +kernel)
    · exact edge_of (matchAt 3) (reflected_walk 6) (reflected_walk 7) (by decide +kernel)

end TetraStereo.Examples.RingPublishedTetraspiroAuxiliary

assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.omitted_carbons
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.all_occurrences
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.all_arms
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.sourceWalk_table
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.all_matches
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.forward_edges
