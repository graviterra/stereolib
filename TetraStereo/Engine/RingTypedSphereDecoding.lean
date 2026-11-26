import TetraStereo.Engine.RingStereoPriorityBlocks

/-! Sequential recovery of signed sphere populations. The unsigned inventory
supplies boundaries; only the reference word supplies the hands. Empty rows
consume no bits but still perform the structural transition. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingTypedSphereDecoding
open RingStereoPriorityBlocks

/-- A pre-sign class retains its full path key and invisible neutral population. -/
structure Shape where
  parent : RingRetainedReferenceGroup.Path
  earlier : List RingRetainedChemicalTrace.Word
  neutral : Nat
  width : Nat
  deriving DecidableEq, Repr

def shape (c : Class) : Shape := ⟨c.parent, c.earlier, c.neutral, c.like + c.unlike⟩

def decodeRow : List Shape → List Bool → List Class × List Bool
  | [], bits => ([], bits)
  | s :: ss, bits =>
    let n := (bits.take s.width).count true
    let rest := decodeRow ss (bits.drop s.width)
    (⟨s.parent, s.earlier, s.neutral, n, s.width - n⟩ :: rest.1, rest.2)

/-- Exact pre decoding, with an arbitrary suffix for all later spheres. -/
theorem decodeRow_word (cs : List Class) (tail : List Bool) :
    decodeRow (cs.map shape) (word cs ++ tail) = (cs, tail) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have take : (c.word ++ (word cs ++ tail)).take (c.like + c.unlike) = c.word := by
      rw [← Class.word_length c, List.take_left]
    have drop : (c.word ++ (word cs ++ tail)).drop (c.like + c.unlike) = word cs ++ tail := by
      rw [← Class.word_length c, List.drop_left]
    simp only [List.map_cons, word, List.flatMap_cons, List.append_assoc] at *
    simp only [decodeRow, shape, take, drop, Class.word_count, ih]
    congr 2
    cases c
    simp

/-- Structural evolution is a fixed function, separate from reading the word.
It may use the recovered signed paths to compute the next unsigned inventory. -/
structure System (Frontier : Type) where
  inventory : Frontier → List Shape
  advance : Frontier → List Class → Frontier

/-- A bounded executable decoder. A depth bound is necessary because arbitrarily
many empty spheres cannot be counted from an empty bit string. -/
def decode {F : Type} (sys : System F) : Nat → F → List Bool → List (List Class) × List Bool
  | 0, _, bits => ([], bits)
  | n+1, frontier, bits =>
    let row := decodeRow (sys.inventory frontier) bits
    let rest := decode sys n (sys.advance frontier row.1) row.2
    (row.1 :: rest.1, rest.2)

/-- An admissible history binds each unsigned row to the current frontier;
there is no equality hypothesis on its signed populations. -/
def Admissible {F : Type} (sys : System F) : F → List (List Class) → Prop
  | _, [] => True
  | frontier, row :: rows =>
    sys.inventory frontier = row.map shape ∧
      Admissible sys (sys.advance frontier row) rows

def referenceWord (rows : List (List Class)) : List Bool := rows.flatMap word

/-- Global decoding includes every sphere, even an empty interior or terminal
sphere, and leaves an arbitrary subsequent reference suffix untouched. -/
theorem decode_referenceWord {F : Type} (sys : System F) (rows : List (List Class))
    (frontier : F) (valid : Admissible sys frontier rows) (tail : List Bool) :
    decode sys rows.length frontier (referenceWord rows ++ tail) = (rows, tail) := by
  induction rows generalizing frontier with
  | nil => rfl
  | cons row rows ih =>
    obtain ⟨inventory, valid⟩ := valid
    simp only [List.length_cons, referenceWord, List.flatMap_cons, List.append_assoc]
    simp only [decode, inventory, decodeRow_word]
    exact congrArg (fun p : List (List Class) × List Bool => (row :: p.1, p.2))
      (ih _ valid)

/-- The same complete word and initial unsigned frontier uniquely determine
all signed class populations, hence their full signed-path lists/multisets. -/
theorem history_unique {F : Type} (sys : System F) (frontier : F)
    (xs ys : List (List Class)) (hx : Admissible sys frontier xs)
    (hy : Admissible sys frontier ys) (depth : xs.length = ys.length)
    (same : referenceWord xs = referenceWord ys) : xs = ys := by
  have a := decode_referenceWord sys xs frontier hx []
  have b := decode_referenceWord sys ys frontier hy []
  rw [depth, same] at a
  exact congrArg Prod.fst (a.symm.trans b)

/-- Equal signed prefixes generate the same next unsigned boundaries. -/
theorem next_shapes {F : Type} (sys : System F) (pre : List (List Class))
    (frontier : F) (x y : List Class) (xs ys : List (List Class))
    (hx : Admissible sys frontier (pre ++ x :: xs))
    (hy : Admissible sys frontier (pre ++ y :: ys)) : x.map shape = y.map shape := by
  induction pre generalizing frontier with
  | nil => exact hx.1.symm.trans hy.1
  | cons p ps ih => exact ih (sys.advance frontier p) hx.2 hy.2

private theorem widths_of_shapes (xs ys : List Class) (h : xs.map shape = ys.map shape) :
    List.Forall₂ (fun a b : Class => a.like + a.unlike = b.like + b.unlike) xs ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      have parts := List.cons.inj h
      exact .cons (congrArg Shape.width parts.1) (ih ys parts.2)

/-- At the first possibly unequal sphere, earlier recovered populations force
its boundaries to agree. The exact molecular-word comparison is consequently
lexicographic comparison of its class-wise like populations. Apply this at the
first unequal row; no assumption of equal widths is supplied by the caller. -/
theorem next_word_compare {F : Type} (sys : System F) (pre : List (List Class))
    (frontier : F) (x y : List Class) (xs ys : List (List Class))
    (hx : Admissible sys frontier (pre ++ x :: xs))
    (hy : Admissible sys frontier (pre ++ y :: ys)) :
    compare (word x) (word y) = compare (x.map Class.like) (y.map Class.like) :=
  word_compare x y (widths_of_shapes x y (next_shapes sys pre frontier x y xs ys hx hy))

end TetraStereo.Engine.RingTypedSphereDecoding
assert_kernel_only TetraStereo.Engine.RingTypedSphereDecoding.decodeRow_word
assert_kernel_only TetraStereo.Engine.RingTypedSphereDecoding.decode_referenceWord
assert_kernel_only TetraStereo.Engine.RingTypedSphereDecoding.history_unique
assert_kernel_only TetraStereo.Engine.RingTypedSphereDecoding.next_shapes
assert_kernel_only TetraStereo.Engine.RingTypedSphereDecoding.next_word_compare
