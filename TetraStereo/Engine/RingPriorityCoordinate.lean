import TetraStereo.Engine.RingFullPathEligibility

/-! Change just the duplicate coordinate in constitutional prefixes of stereo
keys. Later stages append observations to the same list. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingPriorityCoordinate

def second {α : Type*} (g : α → α) : List α → List α
  | a :: b :: rest => a :: g b :: rest
  | xs => xs

theorem second_append {α : Type*} (g : α → α) (xs ys : List α) (h : 2 ≤ xs.length) :
    second g (xs ++ ys) = second g xs ++ ys := by
  cases xs with
  | nil => simp at h
  | cons a xs => cases xs <;> first | rfl | simp at h

theorem second_compare {α : Type} [Ord α] (g : α → α)
    (preserves : ∀ a b, compare (g a) (g b) = compare a b) (xs ys : List α) :
    compare (second g xs) (second g ys) = compare xs ys := by
  cases xs with
  | nil => cases ys with | nil => rfl | cons b bs => cases bs <;> rfl
  | cons a as =>
    cases ys with
    | nil => cases as <;> rfl
    | cons b bs =>
      cases as <;> cases bs <;> simp only [second,List.compare_cons_cons,preserves] <;> rfl

theorem map_strictMono {α : Type*} [LinearOrder α] {g : α → α} (h : StrictMono g) :
    StrictMono (List.map g) := by
  intro xs ys lt
  induction lt with
  | nil => exact List.Lex.nil
  | rel lt => exact List.Lex.rel (h lt)
  | cons _ ih => exact List.Lex.cons ih

theorem second_strictMono {α : Type*} [LinearOrder α] {g : α → α} (h : StrictMono g) :
    StrictMono (second g) := by
  intro xs ys lt
  cases lt with
  | nil => rename_i b bs; cases bs <;> exact List.Lex.nil
  | rel lt => rename_i a as b bs; cases as <;> cases bs <;> exact List.Lex.rel lt
  | cons rest =>
    cases rest with
    | nil => exact List.Lex.cons List.Lex.nil
    | rel lt => exact List.Lex.cons (List.Lex.rel (h lt))
    | cons tail => exact List.Lex.cons (List.Lex.cons tail)

/-- Only the second word through Rule 4a encodes ring-duplicate priorities.
Every other coordinate of the complete ligand key is retained. -/
def fullKey (g : Nat → Nat) (k : RingFullPathEligibility.Key) : RingFullPathEligibility.Key :=
  {k with throughFourA := second (List.map (List.map g)) k.throughFourA}

end TetraStereo.Engine.RingPriorityCoordinate
assert_kernel_only TetraStereo.Engine.RingPriorityCoordinate.second_strictMono
