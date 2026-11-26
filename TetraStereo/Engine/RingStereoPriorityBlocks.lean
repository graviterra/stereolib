import TetraStereo.Engine.RingFullPathPairs

/-! Population blocks for arbitrary full molecular paths. The separation premise
is on the actual path keys, so it permits arbitrary nonterminal earlier-rule
words and arbitrary common parent paths. Neutral occurrences are retained. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingStereoPriorityBlocks
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)
open RingFullPathPairs (stepKey bitOf)

structure Class where
  parent : Path
  earlier : List Word
  neutral : Nat
  like : Nat
  unlike : Nat
  deriving DecidableEq, Repr

def Class.key (c : Class) (b : Option Bool) : Path := c.parent ++ [stepKey c.earlier b]
def Class.paths (c : Class) : List Path :=
  List.replicate c.neutral (c.key none) ++
  List.replicate c.like (c.key (some true)) ++ List.replicate c.unlike (c.key (some false))
def Class.word (c : Class) : List Bool :=
  List.replicate c.like true ++ List.replicate c.unlike false

def paths (cs : List Class) : List Path := cs.flatMap Class.paths
def word (cs : List Class) : List Bool := cs.flatMap Class.word

@[simp] theorem Class.bit_key (c : Class) (b : Option Bool) : bitOf (c.key b) = b :=
  RingFullPathPairs.bitOf_snoc _ _ _

private theorem filterMap_replicate {α β : Type} (f : α → Option β) (n : Nat) (a : α) :
    (List.replicate n a).filterMap f = (f a).toList.flatMap (List.replicate n) := by
  induction n with
  | zero => cases f a <;> rfl
  | succ n ih => cases h : f a <;> simp_all [List.replicate_succ]

@[simp] theorem Class.emit (c : Class) : c.paths.filterMap bitOf = c.word := by
  simp [Class.paths,Class.word,List.filterMap_append]

@[simp] theorem emit (cs : List Class) : (paths cs).filterMap bitOf = word cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change (c.paths ++ paths cs).filterMap bitOf = c.word ++ word cs
    rw [List.filterMap_append,Class.emit,ih]

private theorem prefix_le {α : Type} [LinearOrder α] (p : List α) {a b : List α}
    (h : a ≤ b) : p ++ a ≤ p ++ b := by
  induction p with
  | nil => exact h
  | cons x xs ih => exact List.cons_le_cons x ih

private theorem singleton_le {α : Type} [LinearOrder α] {a b : α} (h : a ≤ b) : [a] ≤ [b] := by
  rcases lt_or_eq_of_le h with h | rfl
  · exact le_of_lt (List.Lex.rel h)
  · exact le_rfl

theorem Class.key_mono (c : Class) {a b : Option Bool}
    (h : RingFullPathPairs.likeCode a ≤ RingFullPathPairs.likeCode b) : c.key a ≤ c.key b := by
  apply prefix_le
  apply singleton_le
  apply prefix_le
  exact singleton_le (singleton_le (singleton_le h))

theorem Class.sorted (c : Class) : c.paths.Pairwise (· ≥ ·) := by
  have tf : c.key (some false) ≤ c.key (some true) := c.key_mono (by decide)
  have fn : c.key (some false) ≤ c.key none := c.key_mono (by decide)
  have tn : c.key (some true) ≤ c.key none := c.key_mono (by decide)
  simp only [Class.paths,List.pairwise_append]
  simp_all only [List.pairwise_replicate,ge_iff_le,le_refl,implies_true,or_true,
    List.mem_replicate,List.mem_append]
  aesop

/-- The certificate includes the complete actual molecular path comparisons,
not a replacement ordering on atom identifiers or population summaries. -/
def Ordered (cs : List Class) : Prop := (paths cs).Pairwise (· ≥ ·)

/-- Class separation compares every possible final hand on the actual full
path. This is a direct certificate of earlier-rule dominance. -/
def Separated (a b : Class) : Prop := ∀ x y, b.key y ≤ a.key x

theorem ordered_of_separated (cs : List Class) (h : cs.Pairwise Separated) : Ordered cs := by
  induction h with
  | nil => simp [Ordered,paths]
  | @cons c cs all rest ih =>
    change (c.paths ++ paths cs).Pairwise (· ≥ ·)
    refine List.pairwise_append.mpr ⟨c.sorted,ih,?_⟩
    intro x hx y hy
    simp only [Class.paths,List.mem_append,List.mem_replicate] at hx
    obtain ⟨d,hd,hy⟩ := List.mem_flatMap.mp hy
    simp only [Class.paths,List.mem_append,List.mem_replicate] at hy
    have keys := all d hd
    rcases hx with (⟨_,rfl⟩ | ⟨_,rfl⟩) | ⟨_,rfl⟩ <;>
      rcases hy with (⟨_,rfl⟩ | ⟨_,rfl⟩) | ⟨_,rfl⟩ <;> exact keys _ _

/-- Exact reading for any enumeration of occurrences realizing these class
populations. Equal-key freedom in the molecular merge sort is harmless. -/
theorem order_exact (cs : List Class) (sorted : Ordered cs) (raw : List Path)
    (population : raw.Perm (paths cs)) :
    (RingStereoSiblingPass.order id raw).filterMap bitOf = word cs := by
  have legal : RingStereoSiblingPass.Legal id raw (paths cs) :=
    ⟨population.symm,by simpa using sorted⟩
  have same := ((RingStereoSiblingPass.legal_iff id raw (paths cs)).mp legal).2
  have eqn : paths cs = RingStereoSiblingPass.order id raw := by simpa using same
  rw [← eqn,emit]

/-- The same equation applies directly to full visits, including arbitrary
nonterminal cursors and repeated occurrences. -/
theorem visits_exact {α : Type} (key : α → Path) (cs : List Class)
    (raw : List α) (sorted : Ordered cs) (population : (raw.map key).Perm (paths cs)) :
    ((RingStereoSiblingPass.order key raw).map key).filterMap bitOf = word cs := by
  have a := RingStereoSiblingPass.legal_order key raw
  have b : RingStereoSiblingPass.Legal id (raw.map key) ((RingStereoSiblingPass.order key raw).map key) :=
    ⟨a.perm.map key,by simpa using a.descending⟩
  have same := ((RingStereoSiblingPass.legal_iff id _ _).mp b).2
  simp only [List.map_id] at same
  exact (congrArg (List.filterMap bitOf) same).trans (order_exact cs sorted _ population)

/-- Full molecular visits may be descendants of any parent occurrence. The
population premise binds every cursor's actual path, including repeated visits. -/
theorem molecular_exact {i : LocalizedChemicalRing.Input} (cs : List Class)
    (raw : List (RingFullPathPairs.FullVisit i)) (separated : cs.Pairwise Separated)
    (population : (raw.map RingFullPathPairs.FullVisit.path).Perm (paths cs)) :
    ((RingStereoSiblingPass.order RingFullPathPairs.FullVisit.path raw).map
      RingFullPathPairs.FullVisit.path).filterMap bitOf = word cs :=
  visits_exact _ cs raw (ordered_of_separated cs separated) population

@[simp] theorem Class.word_length (c : Class) : c.word.length = c.like + c.unlike := by
  simp [Class.word]

@[simp] theorem Class.word_count (c : Class) : c.word.count true = c.like := by
  simp [Class.word,List.count_replicate]

/-- Equal visible widths preserve the boundaries even when adjacent equal
hands merge in the emitted word. Neutral widths need not agree. -/
theorem word_eq_iff (xs ys : List Class)
    (widths : List.Forall₂ (fun a b : Class => a.like+a.unlike = b.like+b.unlike) xs ys) :
    word xs = word ys ↔ List.Forall₂ (fun a b : Class => a.like = b.like) xs ys := by
  induction widths with
  | nil => simp [word]
  | @cons a b xs ys width widths ih =>
    constructor
    · intro eqn
      have split := List.append_inj eqn (by simpa using width : a.word.length = b.word.length)
      exact .cons (by simpa using congrArg (List.count true) split.1) (ih.mp split.2)
    · intro counts
      cases counts with
      | cons same rest =>
        have unlike : a.unlike = b.unlike := by omega
        change a.word ++ word xs = b.word ++ word ys
        simp only [Class.word,same,unlike,ih.mpr rest]

theorem order_eq_iff (xs ys : List Class) (sx : Ordered xs) (sy : Ordered ys)
    (left right : List Path) (pl : left.Perm (paths xs)) (pr : right.Perm (paths ys))
    (widths : List.Forall₂ (fun a b : Class => a.like+a.unlike = b.like+b.unlike) xs ys) :
    (RingStereoSiblingPass.order id left).filterMap bitOf =
      (RingStereoSiblingPass.order id right).filterMap bitOf ↔
      List.Forall₂ (fun a b : Class => a.like = b.like) xs ys := by
  rw [order_exact xs sx left pl,order_exact ys sy right pr,word_eq_iff xs ys widths]

private theorem compare_prefix (b : Bool) (n : Nat) (xs ys : List Bool) :
    compare (List.replicate n b ++ xs) (List.replicate n b ++ ys) = compare xs ys := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ] using ih

private theorem nat_compare_succ (a b : Nat) : compare (a+1) (b+1) = compare a b := by
  change compareOfLessAndEq (a+1) (b+1) = compareOfLessAndEq a b
  simp [compareOfLessAndEq]

private theorem nat_compare_zero_succ (b : Nat) : compare 0 (b+1) = .lt := by
  change compareOfLessAndEq 0 (b+1) = .lt
  simp [compareOfLessAndEq]

private theorem nat_compare_succ_zero (a : Nat) : compare (a+1) 0 = .gt := by
  change compareOfLessAndEq (a+1) 0 = .gt
  simp [compareOfLessAndEq]

private theorem compare_block (a b u v : Nat) (xs ys : List Bool) (width : a+u=b+v) :
    compare (List.replicate a true ++ List.replicate u false ++ xs)
      (List.replicate b true ++ List.replicate v false ++ ys) =
      (compare a b).then (compare xs ys) := by
  induction a generalizing b with
  | zero =>
    cases b with
    | zero =>
      have uv : u = v := by omega
      simp only [uv,List.replicate_zero,List.nil_append,(show compare (0 : Nat) 0 = .eq from rfl),Ordering.eq_then]
      exact compare_prefix false v xs ys
    | succ b =>
      obtain ⟨u,rfl⟩ : ∃ n, u = n+1 := ⟨u-1,by omega⟩
      simp only [List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append,
        List.compare_cons_cons,nat_compare_zero_succ]
      rfl
  | succ a ih =>
    cases b with
    | zero =>
      obtain ⟨v,rfl⟩ : ∃ n, v = n+1 := ⟨v-1,by omega⟩
      simp only [List.replicate_succ,List.replicate_zero,List.nil_append,List.cons_append,
        List.compare_cons_cons,nat_compare_succ_zero]
      rfl
    | succ b =>
      simpa [List.replicate_succ,nat_compare_succ] using ih b (by omega)

/-- The three-way molecular comparison is exactly lexicographic comparison
of the ordered class-wise like populations. Thus its first differing class
decides both strict directions, with larger like population senior. -/
theorem word_compare (xs ys : List Class)
    (widths : List.Forall₂ (fun a b : Class => a.like+a.unlike = b.like+b.unlike) xs ys) :
    compare (word xs) (word ys) = compare (xs.map Class.like) (ys.map Class.like) := by
  induction widths with
  | nil => rfl
  | @cons a b xs ys width widths ih =>
    change compare (a.word ++ word xs) (b.word ++ word ys) = _
    rw [Class.word,Class.word,
      compare_block _ _ _ _ _ _ width,ih]
    simp only [List.map_cons,List.compare_cons_cons]

theorem molecular_compare {i j : LocalizedChemicalRing.Input} (xs ys : List Class)
    (left : List (RingFullPathPairs.FullVisit i)) (right : List (RingFullPathPairs.FullVisit j))
    (sx : xs.Pairwise Separated) (sy : ys.Pairwise Separated)
    (pl : (left.map RingFullPathPairs.FullVisit.path).Perm (paths xs))
    (pr : (right.map RingFullPathPairs.FullVisit.path).Perm (paths ys))
    (widths : List.Forall₂ (fun a b : Class => a.like+a.unlike = b.like+b.unlike) xs ys) :
    compare (((RingStereoSiblingPass.order RingFullPathPairs.FullVisit.path left).map
        RingFullPathPairs.FullVisit.path).filterMap bitOf)
      (((RingStereoSiblingPass.order RingFullPathPairs.FullVisit.path right).map
        RingFullPathPairs.FullVisit.path).filterMap bitOf) =
      compare (xs.map Class.like) (ys.map Class.like) := by
  rw [molecular_exact xs left sx pl,molecular_exact ys right sy pr,word_compare xs ys widths]

end TetraStereo.Engine.RingStereoPriorityBlocks
assert_kernel_only TetraStereo.Engine.RingStereoPriorityBlocks.order_exact
assert_kernel_only TetraStereo.Engine.RingStereoPriorityBlocks.visits_exact
assert_kernel_only TetraStereo.Engine.RingStereoPriorityBlocks.word_eq_iff
assert_kernel_only TetraStereo.Engine.RingStereoPriorityBlocks.order_eq_iff
assert_kernel_only TetraStereo.Engine.RingStereoPriorityBlocks.molecular_exact
assert_kernel_only TetraStereo.Engine.RingStereoPriorityBlocks.word_compare
assert_kernel_only TetraStereo.Engine.RingStereoPriorityBlocks.molecular_compare
