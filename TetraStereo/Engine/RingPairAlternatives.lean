import TetraStereo.Engine.RingPairSpheres

set_option autoImplicit false
namespace TetraStereo.Engine.RingChemicalPriority.PairSpheres

abbrev Word := List (List Nat)

/-- Bounds on a complete reading for one reference descriptor. -/
structure Interval where
  low : Word
  high : Word
  deriving DecidableEq

def Interval.ofLayers (rows : Layers) : Interval := ⟨rows.map lower,rows.map upper⟩
def Interval.exact (w : Word) : Interval := ⟨w,w⟩
def Interval.Allows (i : Interval) (v : Word) := i.low ≤ v ∧ v ≤ i.high

/-- The alternative is selected separately on each side, after that reference
has ranked the ligand's nodes. Figure 8 of Hanson et al. compares the maxima. -/
def Interval.best (a b : Interval) : Interval := ⟨max a.low b.low,max a.high b.high⟩

theorem Interval.best_allows {a b : Interval} {x y : Word} (ha : a.Allows x) (hb : b.Allows y) :
    (a.best b).Allows (max x y) :=
  ⟨max_le_max ha.1 hb.1,max_le_max ha.2 hb.2⟩

/-- Combine bounds proved from two independent ordering constraints on the
same complete word. -/
def Interval.intersect (a b : Interval) : Interval := ⟨max a.low b.low,min a.high b.high⟩

theorem Interval.intersect_allows {a b : Interval} {w : Word} (ha : a.Allows w) (hb : b.Allows w) :
    (a.intersect b).Allows w := ⟨max_le ha.1 hb.1,le_min ha.2 hb.2⟩

def Interval.compare? (a b : Interval) : Option Ordering :=
  if b.high < a.low then some .gt else if a.high < b.low then some .lt
  else if a.low = a.high ∧ a.high = b.low ∧ b.low = b.high then some .eq else none

theorem Interval.decision {a b : Interval} {x y : Word} {result : Ordering}
    (hx : a.Allows x) (hy : b.Allows y) (h : a.compare? b = some result) :
    match result with | .gt => y < x | .lt => x < y | .eq => x = y := by
  unfold compare? at h
  split at h
  · cases h
    exact lt_of_le_of_lt hy.2 (lt_of_lt_of_le ‹_› hx.1)
  · split at h
    · cases h
      exact lt_of_le_of_lt hx.2 (lt_of_lt_of_le ‹_› hy.1)
    · split at h
      · cases h
        obtain ⟨u,v,w⟩ := ‹a.low = a.high ∧ _›
        exact le_antisymm (hx.2.trans (v ▸ hy.1)) (hy.2.trans ((u.trans (v.trans w)) ▸ hx.1))
      · contradiction

/-- Within the nearest chiral sphere, previously equivalent sites are ranked
like-before-unlike for this reference. All later spheres retain their bounds.
The molecular caller establishes equivalence for a mixed reference population. -/
def rankedRow (row : List Bool) : List Bool :=
  List.replicate (row.count true) true ++ List.replicate (row.count false) false

/-- Lock the lexicographic value of the ranked initial sphere, including
mixed ones; only the subsequent spheres admit unrestricted permutations. -/
def referenceInterval : Layers → Interval
  | [] => ⟨[],[]⟩
  | [] :: rest =>
    let bounds := referenceInterval rest
    ⟨[] :: bounds.low,[] :: bounds.high⟩
  | row@(_ :: _) :: rest =>
    let first := upper row
    ⟨first :: rest.map lower,first :: rest.map upper⟩

/-- Permutations in later spheres cannot escape the interval, once the
nearest sphere has been ranked within its proven equivalence class. -/
inductive ReferenceOrder : Layers → Layers → Prop where
  | empty : ReferenceOrder [] []
  | vacant {xs ys} : ReferenceOrder xs ys → ReferenceOrder ([] :: xs) ([] :: ys)
  | first {b bs xs ys} : List.Forall₂ List.Perm xs ys →
    ReferenceOrder ((b :: bs) :: xs) (rankedRow (b :: bs) :: ys)

theorem referenceInterval_allows {rows actual : Layers} (h : ReferenceOrder rows actual) :
    (referenceInterval rows).Allows (ranks actual) := by
  induction h with
  | empty => exact ⟨le_rfl,le_rfl⟩
  | vacant _ ih => exact ⟨List.cons_le_cons _ ih.1,List.cons_le_cons _ ih.2⟩
  | first hp =>
    obtain ⟨lo,hi⟩ := bounds hp
    constructor
    · simpa [ranks,rankedRow,upper,referenceInterval] using List.cons_le_cons _ lo
    · simpa [ranks,rankedRow,upper,referenceInterval] using List.cons_le_cons _ hi

/-- Keep the independently ranked first occupied sphere while preserving
the lower bound obtained for every later sphere of this same reference. -/
def referenceLower : Layers → Word → Word
  | [] , _ => []
  | row :: rows, lo :: lows => if row.isEmpty then lo :: referenceLower rows lows
      else upper row :: lows
  | rows, [] => (referenceInterval rows).low

private theorem rows_mono {ls rs : Word} (h : List.Forall₂ (· ≤ ·) ls rs) : ls ≤ rs := by
  induction h with
  | nil => exact le_rfl
  | cons head _ rest => exact cons_mono head rest

theorem referenceLower_le {rows actual lows} (hierarchy : ReferenceOrder rows actual)
    (bounds : List.Forall₂ (· ≤ ·) lows (ranks actual)) : referenceLower rows lows ≤ ranks actual := by
  induction hierarchy generalizing lows with
  | empty => cases bounds; exact le_rfl
  | vacant _ ih =>
    cases bounds with
    | cons hd tl => exact cons_mono hd (ih tl)
  | @first b bs xs ys hp =>
    cases bounds with
    | cons hd tl =>
      have later := rows_mono tl
      simpa [referenceLower,rankedRow,ranks,upper] using
        List.cons_le_cons (upper (b :: bs)) later

/-- A four-member reference population and a later mixed pair can both be
fixed even though intersecting their whole-word intervals would leave slack. -/
theorem nearest_four_then_two :
    let rows : Layers := [[true,false,true,false],[false,true]]
    let paired : Interval := ⟨[[0,0,1,1],[1,0]],[[1,1,0,0],[1,0]]⟩
    ((referenceInterval rows).intersect paired).low = [[1,1,0,0],[0,1]] ∧
    referenceLower rows paired.low = [[1,1,0,0],[1,0]] := by decide +kernel

/-- A strictly separated or equal maximum gives the published comparison
for every allowed ordering of the four reference-dependent digraph readings. -/
theorem dual_reference_decision {a b c d wa wb wc wd : Layers} {result : Ordering}
    (ha : ReferenceOrder a wa) (hb : ReferenceOrder b wb)
    (hc : ReferenceOrder c wc) (hd : ReferenceOrder d wd)
    (h : ((referenceInterval a).best (referenceInterval b)).compare?
      ((referenceInterval c).best (referenceInterval d)) = some result) :
    let x := max (ranks wa) (ranks wb)
    let y := max (ranks wc) (ranks wd)
    match result with | .lt => x < y | .gt => y < x | .eq => x = y := by
  have left := Interval.best_allows (referenceInterval_allows ha) (referenceInterval_allows hb)
  have right := Interval.best_allows (referenceInterval_allows hc) (referenceInterval_allows hd)
  cases result <;> exact Interval.decision left right h

/-- Figure 8's reported ranked words, represented as binary lists. These
are source readings; this check exercises the alternative-selection rule. -/
private def bits (w : List Nat) : Interval := Interval.exact [w]

theorem hanson_figure8 :
    ((bits [1,0,1,0,0,0]).best (bits [0,1,1,0,1,1])).compare?
      ((bits [0,1,1,0,0,0]).best (bits [1,0,1,0,1,1])) = some .lt ∧
    ((bits [1,1]).best (bits [0,0])).compare?
      ((bits [0,1]).best (bits [1,1])) = some .eq := by decide +kernel

end TetraStereo.Engine.RingChemicalPriority.PairSpheres
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.PairSpheres.Interval.decision
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.PairSpheres.referenceInterval_allows
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.PairSpheres.hanson_figure8
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.PairSpheres.dual_reference_decision
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.PairSpheres.referenceLower_le
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.PairSpheres.nearest_four_then_two
