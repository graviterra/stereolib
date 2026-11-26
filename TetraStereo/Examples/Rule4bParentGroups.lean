import TetraStereo.Engine.RingFullPathPairs

/-! Which terminal hands can be exchanged in one equal-rank Rule 4b sphere? -/
set_option autoImplicit false
namespace TetraStereo.Examples.Rule4bParentGroups
open Engine.RingFullPathPairs (bitOf stepKey bitOf_snoc)
open Engine.RingRetainedReferenceGroup (Path)
open Engine.RingRetainedChemicalTrace (Word)
open Engine.RingStereoSiblingPass (order legal_order)

private def leaf (parent : Path) (priority : List Word) (bit : Bool) : Path :=
  parent ++ [stepKey priority (some bit)]

/-- Use exactly the full-path sphere sorter and terminal bit decoder. The parent
rows here have the same complete path and the leaves have equal earlier priorities. -/
def emit (parent : Path) (priority : List Word) (rows : List (List Bool)) : List Bool :=
  (order id (rows.flatten.map (leaf parent priority))).filterMap bitOf

private theorem retains (parent : Path) (priority : List Word) (rows : List (List Bool)) :
    (emit parent priority rows).Perm rows.flatten := by
  have h := ((legal_order id (rows.flatten.map (leaf parent priority))).perm).filterMap bitOf
  simpa [emit,List.filterMap_map,Function.comp_def,leaf,bitOf_snoc] using h

/-- For any number or sizes of parent groups, equality of the emitted terminal
bits is exactly equality of the total bit multiset. -/
theorem same_reading_iff (parent : Path) (priority : List Word) (x y : List (List Bool)) :
    emit parent priority x = emit parent priority y ↔ x.flatten.Perm y.flatten := by
  constructor
  · intro same
    exact (retains parent priority x).symm.trans (same ▸ retains parent priority y)
  · intro p
    let l := legal_order id (x.flatten.map (leaf parent priority))
    let r := legal_order id (y.flatten.map (leaf parent priority))
    have eqn := List.Perm.eq_of_pairwise (fun a b _ _ ab ba => le_antisymm ba ab)
      l.descending r.descending ((l.perm.trans ((p.map _).trans r.perm.symm)).map id)
    exact congrArg (List.filterMap bitOf) (by simpa using eqn)

private def left : List (List Bool) := [[true,true],[false,false]]
private def right : List (List Bool) := [[true,false],[true,false]]

private def grouped (xs : List (List Bool)) : Multiset (Multiset Bool) :=
  ↑(xs.map (fun s => (s : Multiset Bool)))

/-- RR|SS and RS|RS are different even modulo every relabelling of children
and parents. Every shared prefix and earlier priority emits equal Rule 4b bits. -/
theorem cross_parent_obstruction :
    grouped left ≠ grouped right ∧ ∀ parent priority, emit parent priority left = emit parent priority right :=
  ⟨by decide,fun p d => (same_reading_iff p d left right).mpr (by decide)⟩

private def distal (xs : List (Bool × Bool)) : List Bool :=
  (order id (xs.map fun h => leaf (leaf [] [] h.1) [] h.2)).filterMap bitOf

private theorem distal_pair (x y : Bool) : distal [(true,x),(false,y)] = [x,y] := by
  let a := leaf (leaf [] [] true) [] x
  let b := leaf (leaf [] [] false) [] y
  have before : b < a := List.Lex.rel (List.Lex.rel (List.Lex.rel (List.Lex.rel (by decide : 1 < 2))))
  have sorted : order id [a,b] = [a,b] := by
    apply List.mergeSort_of_pairwise
    simp [le_of_lt before]
  change (order id [a,b]).filterMap bitOf = _
  rw [sorted]
  have faithful (p : Path) (v : Bool) : bitOf (leaf p [] v) = some v := bitOf_snoc ..
  simp [a,b,faithful]

/-- If the two parents themselves carry like/unlike bits, the prefix condition
matters. The correlated and anticorrelated paired paths give opposite distal orders. -/
theorem marked_parent_control :
    distal [(true,true),(false,false)] = [true,false] ∧
    distal [(true,false),(false,true)] = [false,true] := ⟨distal_pair true false,distal_pair false true⟩

end TetraStereo.Examples.Rule4bParentGroups
assert_kernel_only TetraStereo.Examples.Rule4bParentGroups.same_reading_iff
assert_kernel_only TetraStereo.Examples.Rule4bParentGroups.cross_parent_obstruction
assert_kernel_only TetraStereo.Examples.Rule4bParentGroups.marked_parent_control
