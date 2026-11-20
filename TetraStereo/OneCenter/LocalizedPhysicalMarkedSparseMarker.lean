import TetraStereo.OneCenter.DeclarativeCIPPromotedCanonicalAddressing
import TetraStereo.KernelOnly
import Mathlib.Data.List.GetD

set_option autoImplicit false

/-!
# Sparse storage for zero-padded promotion markers

The dense reference column has `W ^ level` entries at each level, including absent positions.
Only nonzero observations need storage. Each sparse entry retains its exact positional index;
absent and explicitly zero observations still compare identically. Comparison is proved against
the dense reference, not a changed promotion rule.
-/

namespace TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker

open DeclarativeCIP.PromotedCanonical

abbrev Row := List (Nat × Nat)
abbrev SparseMarker := List Row

def shift (offset : Nat) (row : Row) : Row :=
  row.map fun entry => (offset + entry.1, entry.2)

def encodeRow : List Nat → Row
  | [] => []
  | value :: rest =>
      if value = 0 then shift 1 (encodeRow rest)
      else (0, value) :: shift 1 (encodeRow rest)

def encode (key : MarkerKey) : SparseMarker := key.map encodeRow

@[simp] theorem shift_nil (offset : Nat) : shift offset [] = [] := rfl

@[simp] theorem shift_cons (offset : Nat) (entry : Nat × Nat) (rest : Row) :
    shift offset (entry :: rest) = (offset + entry.1, entry.2) :: shift offset rest := rfl

@[simp] theorem shift_zero (row : Row) : shift 0 row = row := by
  simp [shift]

theorem shift_append (offset : Nat) (left right : Row) :
    shift offset (left ++ right) = shift offset left ++ shift offset right := by
  simp [shift]

theorem shift_shift (a b : Nat) (row : Row) :
    shift a (shift b row) = shift (a + b) row := by
  simp [shift, List.map_map, Nat.add_assoc]

theorem encodeRow_append (left right : List Nat) :
    encodeRow (left ++ right) = encodeRow left ++ shift left.length (encodeRow right) := by
  induction left with
  | nil => simp [encodeRow]
  | cons value rest ih =>
      by_cases zero : value = 0
      · simp [encodeRow, zero, ih, shift_append, shift_shift, Nat.add_comm]
      · simp [encodeRow, zero, ih, shift_append, shift_shift, Nat.add_comm]

@[simp] theorem encodeRow_zeros (length : Nat) : encodeRow (List.replicate length 0) = [] := by
  induction length with
  | zero => rfl
  | succ length ih => simp [List.replicate_succ, encodeRow, ih]

/-- Concatenation of fixed-width rows using offsets, without materializing absent entries. -/
def packRows (width : Nat) : List Row → Row
  | [] => []
  | row :: rest => row ++ shift width (packRows width rest)

theorem encodeRow_flatten (width : Nat) (rows : List (List Nat))
    (lengths : ∀ row ∈ rows, row.length = width) :
    encodeRow rows.flatten = packRows width (rows.map encodeRow) := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      simp only [List.flatten_cons, List.map_cons, packRows, encodeRow_append]
      rw [lengths row (by simp), ih (fun xs member => lengths xs (by simp [member]))]

/-- The dense reference's assembly with the same width/depth and exact zero-default meaning. -/
def assemble (W D mark : Nat) (children : List SparseMarker) : SparseMarker :=
  (if mark = 0 then [] else [(0, mark)]) ::
    (List.range D).map fun level =>
      packRows (W ^ level)
        ((List.range W).map fun slot => (children.getD slot []).getD level [])

private theorem getD_encode (children : List MarkerKey) (slot : Nat) :
    (children.map encode).getD slot [] = encode (children.getD slot []) := by
  exact List.getD_map children [] encode

private theorem getD_encodeRow (key : MarkerKey) (level : Nat) (padding : List Nat)
    (zero : encodeRow padding = []) :
    (encode key).getD level [] = encodeRow (key.getD level padding) := by
  rw [← zero]
  exact List.getD_map key padding encodeRow

/-- Sparse assembly is exactly the encoding of dense assembly for well-shaped child markers. -/
theorem assemble_eq_encode (W D mark : Nat) (children : List MarkerKey)
    (shaped : ∀ child ∈ children, MarkerWellShaped W D child) :
    assemble W D mark (children.map encode) = encode (assembleMarker W D mark children) := by
  unfold assemble assembleMarker encode
  simp only [List.map_cons, List.map_map]
  congr 1
  apply List.map_congr_left
  intro level member
  have bound : level < D := List.mem_range.mp member
  have lengths : ∀ row ∈ (List.range W).map
      (fun slot => (children.getD slot []).getD level (markerPad W level)),
      row.length = W ^ level := by
    intro row present
    obtain ⟨slot, _, rfl⟩ := List.mem_map.mp present
    exact markerSlotLevel_length shaped bound slot
  dsimp only [Function.comp_apply]
  rw [List.flatMap_def, encodeRow_flatten (W ^ level) _ lengths]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left
  intro slot _
  change ((children.map encode).getD slot []).getD level [] = _
  rw [getD_encode]
  exact getD_encodeRow _ level (markerPad W level) (encodeRow_zeros _)

def compareEntry (left right : Nat × Nat) : Ordering :=
  if left.1 < right.1 then .gt
  else if right.1 < left.1 then .lt
  else compare left.2 right.2

def compareRow : Row → Row → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | left :: ls, right :: rs => (compareEntry left right).then (compareRow ls rs)

def compareMarker : SparseMarker → SparseMarker → Ordering := List.compareLex compareRow

theorem compareEntry_shift (offset : Nat) (a b : Nat × Nat) :
    compareEntry (offset + a.1, a.2) (offset + b.1, b.2) = compareEntry a b := by
  simp [compareEntry]

theorem compareRow_shift (offset : Nat) (left right : Row) :
    compareRow (shift offset left) (shift offset right) = compareRow left right := by
  induction left generalizing right with
  | nil => cases right <;> rfl
  | cons a rest ih =>
      cases right with
      | nil => rfl
      | cons b tail => simp only [shift_cons, compareRow, compareEntry_shift, ih]

private theorem compareRow_zero_positive (left right : Row) (positive : Nat) :
    compareRow (shift 1 left) ((0, positive + 1) :: shift 1 right) = .lt := by
  cases left with
  | nil => rfl
  | cons a rest => simp [compareRow, compareEntry]

private theorem compareRow_positive_zero (left right : Row) (positive : Nat) :
    compareRow ((0, positive + 1) :: shift 1 left) (shift 1 right) = .gt := by
  cases right with
  | nil => rfl
  | cons b rest => simp [compareRow, compareEntry]

/-- Exact comparison of equally long dense rows. Nonzero entries keep both position and value. -/
theorem compareRow_encode (left right : List Nat) (lengths : left.length = right.length) :
    compareRow (encodeRow left) (encodeRow right) = compare left right := by
  induction left generalizing right with
  | nil =>
      have empty : right = [] := List.length_eq_zero_iff.mp lengths.symm
      subst right
      rfl
  | cons a rest ih =>
      cases right with
      | nil => simp at lengths
      | cons b tail =>
          have shorter : rest.length = tail.length := by simpa using lengths
          cases a with
          | zero =>
              cases b with
              | zero => simpa [encodeRow, compareRow_shift] using ih tail shorter
              | succ b => simpa [encodeRow] using compareRow_zero_positive (encodeRow rest) (encodeRow tail) b
          | succ a =>
              cases b with
              | zero => simpa [encodeRow] using compareRow_positive_zero (encodeRow rest) (encodeRow tail) a
              | succ b =>
                  simp only [encodeRow, Nat.succ_ne_zero,
                    ↓reduceIte, compareRow, compareEntry, lt_self_iff_false, compareRow_shift]
                  rw [ih tail shorter]
                  exact List.compare_cons_cons.symm

/-- The complete sphere-major comparison is unchanged when corresponding row lengths agree. -/
theorem compareMarker_encode (left right : MarkerKey)
    (lengths : left.map List.length = right.map List.length) :
    compareMarker (encode left) (encode right) = compare left right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons row rest => simp at lengths
  | cons row rest ih =>
      cases right with
      | nil => simp at lengths
      | cons other tail =>
          have parts : row.length = other.length ∧
              rest.map List.length = tail.map List.length := by simpa using lengths
          rw [show encode (row :: rest) = encodeRow row :: encode rest from rfl,
            show encode (other :: tail) = encodeRow other :: encode tail from rfl]
          unfold compareMarker
          rw [List.compareLex_cons_cons]
          rw [compareRow_encode row other parts.1]
          change (compare row other).then (compareMarker (encode rest) (encode tail)) = _
          rw [ih tail parts.2]
          exact List.compare_cons_cons.symm

theorem compareMarker_encode_shaped {W D : Nat} (left right : MarkerKey)
    (leftShape : MarkerWellShaped W D left) (rightShape : MarkerWellShaped W D right) :
    compareMarker (encode left) (encode right) = compare left right := by
  apply compareMarker_encode
  apply List.ext_getElem
  · simp [leftShape.1, rightShape.1]
  · intro i hi hj
    simp only [List.getElem_map]
    exact (leftShape.2 i (by simpa using hi)).trans
      (rightShape.2 i (by simpa using hj)).symm

/-- A leaf allocates only its possible nonzero root observation, even at enormous layouts. -/
theorem assemble_leaf (W D mark : Nat) :
    assemble W D mark [] =
      (if mark = 0 then [] else [(0, mark)]) :: List.replicate D [] := by
  have pack : ∀ n width, packRows width (List.replicate n []) = [] := by
    intro n width
    induction n with
    | zero => rfl
    | succ n ih => simp [List.replicate_succ, packRows, ih]
  simp [assemble, List.map_const', pack]

/-- The layout that exhausted the dense probe remains cheap for actual sparse assembly. -/
theorem large_layout_leaf : (assemble 22 46 1 []).flatten = [(0, 1)] := by
  decide +kernel

/-- An earlier nonzero address is decisive even when a later value is larger. -/
theorem earlier_address_control :
    compareRow (encodeRow [0, 5, 0]) (encodeRow [0, 0, 9]) = .gt := by
  decide +kernel

/-- Explicit zero observations disappear without creating an occupancy distinction. -/
theorem zero_padding_control :
    encodeRow [0, 0, 0] = [] := by
  decide +kernel

end TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker

assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker.encodeRow_append
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker.encodeRow_flatten
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker.assemble_eq_encode
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker.compareRow_encode
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker.compareMarker_encode_shaped
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker.assemble_leaf
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker.large_layout_leaf
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker.earlier_address_control
assert_kernel_only TetraStereo.OneCenter.LocalizedPhysicalMarkedSparseMarker.zero_padding_control
