import TetraStereo.Examples.RingTetraspiroVisitRules

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
set_option maxRecDepth 60000

namespace TetraStereo.Examples.RingPublishedTetraspiroAuxiliary
open OneCenter Engine CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingChemicalPriority RingSeededPairs RingPublishedTetraspiro

private theorem map_of_rows {α β : Type} {f : α → Option β} {xs : List α} {ys : List β}
    (h : List.Forall₂ (fun x y => f x = some y) xs ys) : xs.mapM f = some ys := by
  induction h with
  | nil => rfl
  | cons head _ ih => simp [head,ih]

local macro "each_row" : tactic =>
  `(tactic| (apply map_of_rows; repeat' first | apply List.Forall₂.cons | exact List.Forall₂.nil | decide +kernel))

theorem complete_occurrence_orders : paths.mapM completeRanking? = some (List.replicate 24 true) := by
  each_row

theorem complete_queue_orders :
    arms.mapM (fun (r,a) => fullQueue? spatial r a) = some (List.replicate 8 true) ∧
    arms.mapM (fun (r,a) => fullQueue? reflected r a) = some (List.replicate 8 true) := by
  constructor <;> each_row


end TetraStereo.Examples.RingPublishedTetraspiroAuxiliary

assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.complete_occurrence_orders
assert_kernel_only TetraStereo.Examples.RingPublishedTetraspiroAuxiliary.complete_queue_orders
