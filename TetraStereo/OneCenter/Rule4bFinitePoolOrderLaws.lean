import TetraStereo.OneCenter.Rule4bInheritedRankFrontier
import TetraStereo.KernelOnly

/-!
# Finite-pool order laws for the Rule-4b inherited-rank frontier

`TetraStereo.Rule4bInheritedRankFrontier` proves its ranking theorems from `CompareLaws`, whose
`total` field quantifies over *every* cursor of the ambient type.  A runtime pre-Rule-4b comparator
refuses (`none`) on nodes whose canonical key could not be compiled, so that structure can never be
instantiated by the real comparator.  This module removes exactly that global-totality assumption.

The construction is:

* a compiled-key pool is a finite list of cursors together with a compiler and a *per-node receipt*
  `receipt : ∀ c ∈ cursors, compile c = some (keyOf c)`.  A receipt records that one concrete node
  compiled; it says nothing about nodes outside the pool and nothing about any desired ranking;
* the domain of the order laws is the membership subtype `PoolCursor pool = {c // c ∈ pool}`.  On
  this type `total` is only ever asked about pooled, successfully compiled cursors;
* the canonical key comparator is a plain total function `Key → Key → Ordering`.  Its order laws
  (`Std.TransCmp`) are lifted to `CompareLaws` by an explicit orientation swap: the runtime uses
  `gt` for the senior endpoint, the frontier uses `lt`.  The swap is `runtimeSeniorSwap`, proved
  involutive/injective and tie-preserving, so the translation is not a renaming of one direction;
* the frontier's `childClassID_eq_of_eq` / `childClassID_lt_of_lt` are applied on the subtype and
  transported back to the original pool through `childClassID_attach_eq`, which is
  `List.countP_attach`.  Multiplicity is retained because `rankPool` maps without deduplication
  (`rankPool_pool_fst`, `rankPool_length`).

No theorem below assumes a desired pairwise ranking.  The only comparator input is
`ComparesByCompiledKey`, a per-successful-compilation agreement between the pre-Rule-4b comparator
and the canonical key comparator, up to the explicit seniority swap.  Every result is conditional
on that checked bridge plus the standard `Std.TransCmp` laws of the key comparator.
-/

set_option autoImplicit false

namespace TetraStereo.Rule4bInheritedRankFrontier.FinitePool

universe u v w

/-! ## 1. The explicit seniority swap

The runtime canonical comparators write `gt` when the left endpoint is senior; the frontier writes
`lt`.  `runtimeSeniorSwap` is the bridge.  It is an involution, so information is neither lost nor
duplicated by the translation, and it fixes `eq`, so comparator ties survive the orientation
change. -/

/-- Runtime seniority convention (`gt` = left endpoint senior) transported to the frontier
convention (`lt` = left endpoint senior). -/
def runtimeSeniorSwap : Ordering → Ordering
  | .lt => .gt
  | .eq => .eq
  | .gt => .lt

@[simp] theorem runtimeSeniorSwap_lt : runtimeSeniorSwap Ordering.lt = Ordering.gt := rfl

@[simp] theorem runtimeSeniorSwap_eq : runtimeSeniorSwap Ordering.eq = Ordering.eq := rfl

@[simp] theorem runtimeSeniorSwap_gt : runtimeSeniorSwap Ordering.gt = Ordering.lt := rfl

/-- A runtime `gt` (left endpoint senior) becomes a frontier `lt` (left endpoint senior). -/
theorem runtimeSeniorSwap_runtime_senior :
    runtimeSeniorSwap Ordering.gt = Ordering.lt := rfl

/-- A runtime `lt` (left endpoint junior) becomes a frontier `gt`. -/
theorem runtimeSeniorSwap_runtime_junior :
    runtimeSeniorSwap Ordering.lt = Ordering.gt := rfl

/-- The bridge is the ordinary comparison reversal. -/
theorem runtimeSeniorSwap_eq_swap (o : Ordering) :
    runtimeSeniorSwap o = o.swap := by
  cases o <;> rfl

/-- The bridge is involutive. -/
theorem runtimeSeniorSwap_involutive (o : Ordering) :
    runtimeSeniorSwap (runtimeSeniorSwap o) = o := by
  cases o <;> rfl

/-- The bridge is injective: distinct runtime answers remain distinct frontier answers. -/
theorem runtimeSeniorSwap_injective : Function.Injective runtimeSeniorSwap := by
  intro a b h
  cases a <;> cases b <;> simp_all

/-- Comparator ties survive the orientation change. -/
theorem runtimeSeniorSwap_eq_iff (o : Ordering) :
    runtimeSeniorSwap o = Ordering.eq ↔ o = Ordering.eq := by
  cases o <;> simp

/-- Strict seniority is preserved: frontier `lt` means exactly runtime `gt`. -/
theorem runtimeSeniorSwap_lt_iff (o : Ordering) :
    runtimeSeniorSwap o = Ordering.lt ↔ o = Ordering.gt := by
  cases o <;> simp

/-- Strict juniority is preserved: frontier `gt` means exactly runtime `lt`. -/
theorem runtimeSeniorSwap_gt_iff (o : Ordering) :
    runtimeSeniorSwap o = Ordering.gt ↔ o = Ordering.lt := by
  cases o <;> simp

/-! ## 2. From `Std.TransCmp` to `CompareLaws`

`CompareLaws` is the frontier's nine-field presentation of a total preorder on `Option Ordering`.
A key comparator is a plain function, so it is total by construction; the only work is to translate
the `Std.TransCmp` field presentation into the frontier field presentation. -/

/-- A transitive comparator composes with any map: pulling back preserves transitivity. -/
theorem transCmp_comp {α : Type u} {β : Type v} {cmp : β → β → Ordering}
    (f : α → β) [Std.TransCmp cmp] :
    Std.TransCmp (fun a b => cmp (f a) (f b)) where
  eq_swap := fun {a b} => Std.OrientedCmp.eq_swap (cmp := cmp) (a := f a) (b := f b)
  isLE_trans := fun {a b c} ha hb =>
    Std.TransCmp.isLE_trans (cmp := cmp) (a := f a) (b := f b) (c := f c) ha hb

/-- Applying the seniority swap to the result of a transitive comparator leaves a transitive
comparator (it is the opposite comparison). -/
theorem transCmp_swapResult {α : Type u} {cmp : α → α → Ordering} [Std.TransCmp cmp] :
    Std.TransCmp (fun a b => runtimeSeniorSwap (cmp a b)) := by
  have h : (fun a b : α => runtimeSeniorSwap (cmp a b)) = fun a b => cmp b a := by
    funext a b
    rw [runtimeSeniorSwap_eq_swap]
    exact (Std.OrientedCmp.eq_swap (cmp := cmp) (a := b) (b := a)).symm
  rw [h]
  exact Std.TransCmp.opposite

/-- The translation from `Std.TransCmp` to the frontier's `CompareLaws`, for the total
`Option Ordering` embedding `fun a b => some (cmp a b)`. -/
theorem compareLaws_some_of_transCmp {α : Type u} {cmp : α → α → Ordering}
    [Std.TransCmp cmp] :
    CompareLaws (fun a b => some (cmp a b)) where
  total := fun a b => by
    cases cmp a b <;> simp
  refl := fun a => by
    show some (cmp a a) = some Ordering.eq
    rw [Std.ReflCmp.compare_self (cmp := cmp) (a := a)]
  eq_symm := fun {a b} h =>
    congrArg some
      (Std.OrientedCmp.eq_symm (cmp := cmp) (a := a) (b := b) (by simpa using h))
  lt_symm := fun {a b} h =>
    congrArg some
      (Std.OrientedCmp.gt_of_lt (cmp := cmp) (a := a) (b := b) (by simpa using h))
  gt_symm := fun {a b} h =>
    congrArg some
      (Std.OrientedCmp.lt_of_gt (cmp := cmp) (a := a) (b := b) (by simpa using h))
  eq_eq := fun {a b c} h1 h2 =>
    congrArg some
      (Std.TransCmp.eq_trans (cmp := cmp) (a := a) (b := b) (c := c)
        (by simpa using h1) (by simpa using h2))
  eq_lt := fun {a b c} h1 h2 =>
    congrArg some
      (Std.TransCmp.lt_of_eq_of_lt (cmp := cmp) (a := a) (b := b) (c := c)
        (by simpa using h1) (by simpa using h2))
  lt_eq := fun {a b c} h1 h2 =>
    congrArg some
      (Std.TransCmp.lt_of_lt_of_eq (cmp := cmp) (a := a) (b := b) (c := c)
        (by simpa using h1) (by simpa using h2))
  lt_lt := fun {a b c} h1 h2 =>
    congrArg some
      (Std.TransCmp.lt_trans (cmp := cmp) (a := a) (b := b) (c := c)
        (by simpa using h1) (by simpa using h2))

/-- Transport of `CompareLaws` across a pointwise-equal comparison function. -/
theorem compareLaws_congr {α : Type u} {before₁ before₂ : α → α → Option Ordering}
    (laws : CompareLaws before₁) (h : ∀ a b, before₁ a b = before₂ a b) :
    CompareLaws before₂ := by
  have heq : before₂ = before₁ := by
    funext a b
    exact (h a b).symm
  rw [heq]
  exact laws

/-! ## 3. A comparator induced by compiled canonical keys -/

/-- The frontier comparator induced by a key compiler and a canonical key comparator.  The
seniority swap is explicit and is the only place where the runtime convention enters. -/
def keyBefore {α : Type u} {Key : Type w} (keyOf : α → Key)
    (compareKey : Key → Key → Ordering) (a b : α) : Option Ordering :=
  some (runtimeSeniorSwap (compareKey (keyOf a) (keyOf b)))

/-- The key-induced comparator satisfies the frontier's `CompareLaws` whenever the key comparator
is a `Std.TransCmp`.  No property of `Cursor` (totality or otherwise) is used. -/
theorem keyBefore_compareLaws {α : Type u} {Key : Type w} (keyOf : α → Key)
    (compareKey : Key → Key → Ordering) [Std.TransCmp compareKey] :
    CompareLaws (keyBefore keyOf compareKey) := by
  haveI hcomp : Std.TransCmp (fun a b : α => compareKey (keyOf a) (keyOf b)) :=
    transCmp_comp keyOf
  haveI hswap : Std.TransCmp
      (fun a b : α => runtimeSeniorSwap (compareKey (keyOf a) (keyOf b))) :=
    transCmp_swapResult (cmp := fun a b : α => compareKey (keyOf a) (keyOf b))
  exact compareLaws_some_of_transCmp

/-! ## 4. The finite successful-compilation pool

`PoolCursor pool` is the membership subtype of a finite list.  Restricting the cursor type to this
subtype is what removes the global `CompareLaws.total` assumption: the frontier asks for laws only
on the domain it ranks, and every element of this domain is a pooled cursor. -/

variable {Cursor : Type u} {Descriptor : Type v}

/-- The membership subtype of a finite pool. -/
abbrev PoolCursor {α : Type u} (pool : List α) : Type u := { c : α // c ∈ pool }

/-- The frontier specification restricted to a finite pool.  Children are irrelevant to the pool
ranking and are set to `[]`; resolution and comparison are inherited from the original spec. -/
def poolSpec (spec : FrontierSpec Cursor Descriptor) (pool : List Cursor) :
    FrontierSpec (PoolCursor pool) Descriptor where
  children := fun _ => []
  resolve := fun c => spec.resolve c.1
  before := fun a b => spec.before a.1 b.1

@[simp] theorem poolSpec_before (spec : FrontierSpec Cursor Descriptor) (pool : List Cursor)
    (a b : PoolCursor pool) :
    (poolSpec spec pool).before a b = spec.before a.1 b.1 := rfl

@[simp] theorem poolSpec_resolve (spec : FrontierSpec Cursor Descriptor) (pool : List Cursor)
    (c : PoolCursor pool) :
    (poolSpec spec pool).resolve c = spec.resolve c.1 := rfl

/-- `CompareLaws` restricts to a membership subtype.  The `total` field of the result ranges only
over pooled elements, which is exactly the finite domain on which the compiled comparator is
required to answer. -/
theorem compareLaws_subtype {α : Type u} {before : α → α → Option Ordering}
    (laws : CompareLaws before) (pool : List α) :
    CompareLaws (fun a b : PoolCursor pool => before a.1 b.1) where
  total := fun a b => laws.total a.1 b.1
  refl := fun a => laws.refl a.1
  eq_symm := fun {_a _b} h => laws.eq_symm h
  lt_symm := fun {_a _b} h => laws.lt_symm h
  gt_symm := fun {_a _b} h => laws.gt_symm h
  eq_eq := fun {_a _b _c} h1 h2 => laws.eq_eq h1 h2
  eq_lt := fun {_a _b _c} h1 h2 => laws.eq_lt h1 h2
  lt_eq := fun {_a _b _c} h1 h2 => laws.lt_eq h1 h2
  lt_lt := fun {_a _b _c} h1 h2 => laws.lt_lt h1 h2

/-! ## 5. The comparator bridge

`ComparesByCompiledKey` is a per-pair agreement between the pre-Rule-4b comparator and the canonical
key comparator, quantified only over *successful compilations*.  It never states which endpoint is
senior and never mentions the pool ranking. -/

/-- The pre-Rule-4b comparator agrees with the canonical key comparator on every pair of cursors
that both compile, up to the explicit seniority swap. -/
def ComparesByCompiledKey {α : Type u} {Key : Type w}
    (before : α → α → Option Ordering) (compile : α → Option Key)
    (compareKey : Key → Key → Ordering) : Prop :=
  ∀ {a b : α} {ka kb : Key}, compile a = some ka → compile b = some kb →
    before a b = some (runtimeSeniorSwap (compareKey ka kb))

/-- The pool-level key agreement derived from the bridge: only pooled cursors are quantified over,
and their keys exist by construction (`keyOf`). -/
theorem keyAgreesOn_of_comparesByCompiledKey {α : Type u} {Key : Type w}
    {before : α → α → Option Ordering} {compile : α → Option Key}
    {keyOf : α → Key} {compareKey : Key → Key → Ordering} (pool : List α)
    (hbridge : ComparesByCompiledKey before compile compareKey)
    (hreceipt : ∀ c, c ∈ pool → compile c = some (keyOf c)) :
    ∀ a ∈ pool, ∀ b ∈ pool,
      before a b = some (runtimeSeniorSwap (compareKey (keyOf a) (keyOf b))) :=
  fun a ha b hb => hbridge (hreceipt a ha) (hreceipt b hb)

/-- The frontier order laws on the finite pool, derived from the canonical key order laws.

The only inputs are (i) `Std.TransCmp compareKey`, the already established order laws of the
compiled canonical keys, and (ii) `hagree`, the bridge restricted to the pool.  Neither the cursor
type as a whole nor the compiler outside the pool is required to be total. -/
theorem poolSpec_compareLaws_of_keyAgrees
    (spec : FrontierSpec Cursor Descriptor) (pool : List Cursor)
    {Key : Type w} (keyOf : Cursor → Key) (compareKey : Key → Key → Ordering)
    [Std.TransCmp compareKey]
    (hagree : ∀ a ∈ pool, ∀ b ∈ pool,
      spec.before a b = some (runtimeSeniorSwap (compareKey (keyOf a) (keyOf b)))) :
    CompareLaws (poolSpec spec pool).before := by
  have hkey : CompareLaws (keyBefore keyOf compareKey) :=
    keyBefore_compareLaws keyOf compareKey
  have hsub : CompareLaws
      (fun a b : PoolCursor pool => keyBefore keyOf compareKey a.1 b.1) :=
    compareLaws_subtype hkey pool
  refine compareLaws_congr hsub ?_
  intro a b
  exact (hagree a.1 a.2 b.1 b.2).symm

/-! ## 6. Lifting class identifiers back to the original pool

The frontier theorems are applied on `PoolCursor pool` and their conclusions are transported back
to `Cursor` by `childClassID_attach_eq`.  The equation is `List.countP_attach`, so the class
identifier counts exactly the same pooled occurrences on both sides: no recorded occurrence is
dropped and none is duplicated. -/

/-- Class identifiers computed on the attached pool coincide with identifiers computed on the
original pool.  This is the multiplicity-preserving bridge used by both lifting theorems. -/
theorem childClassID_attach_eq (spec : FrontierSpec Cursor Descriptor) (pool : List Cursor)
    (a : Cursor) (ha : a ∈ pool) :
    childClassID (poolSpec spec pool) pool.attach ⟨a, ha⟩ = childClassID spec pool a := by
  unfold childClassID
  have hfun : (fun r : PoolCursor pool =>
        decide ((poolSpec spec pool).before r ⟨a, ha⟩ = some Ordering.lt)) =
      (fun r : PoolCursor pool =>
        decide (spec.before r.1 a = some Ordering.lt)) := by
    funext r
    rfl
  rw [hfun]
  exact List.countP_attach (l := pool)
    (p := fun c : Cursor => decide (spec.before c a = some Ordering.lt))

/-- Equal comparator classes receive equal class identifiers in the original pool.  The proof
runs the frontier's `childClassID_eq_of_eq` on the subtype and rewrites back with
`childClassID_attach_eq`. -/
theorem childClassID_eq_of_pool_compareLaws
    {spec : FrontierSpec Cursor Descriptor} {pool : List Cursor}
    (laws : CompareLaws (poolSpec spec pool).before)
    {a b : Cursor} (ha : a ∈ pool) (hb : b ∈ pool)
    (h : spec.before a b = some Ordering.eq) :
    childClassID spec pool a = childClassID spec pool b := by
  have h' : (poolSpec spec pool).before ⟨a, ha⟩ ⟨b, hb⟩ = some Ordering.eq := h
  have heq := childClassID_eq_of_eq (spec := poolSpec spec pool)
    (reps := pool.attach) laws h'
  rwa [childClassID_attach_eq spec pool a ha,
    childClassID_attach_eq spec pool b hb] at heq

/-- Strict comparator classes receive strictly increasing class identifiers in the original pool.
The frontier's `childClassID_lt_of_lt` is applied on the subtype and transported back; its
membership hypotheses are discharged by `List.mem_attach`. -/
theorem childClassID_lt_of_pool_compareLaws
    {spec : FrontierSpec Cursor Descriptor} {pool : List Cursor}
    (laws : CompareLaws (poolSpec spec pool).before)
    {a b : Cursor} (ha : a ∈ pool) (hb : b ∈ pool)
    (h : spec.before a b = some Ordering.lt) :
    childClassID spec pool a < childClassID spec pool b := by
  have h' : (poolSpec spec pool).before ⟨a, ha⟩ ⟨b, hb⟩ = some Ordering.lt := h
  have hlt := childClassID_lt_of_lt (spec := poolSpec spec pool) (pooled := pool.attach)
    laws (a := ⟨a, ha⟩) (b := ⟨b, hb⟩) h'
    (List.mem_attach pool ⟨a, ha⟩) (List.mem_attach pool ⟨b, hb⟩)
  rwa [childClassID_attach_eq spec pool a ha,
    childClassID_attach_eq spec pool b hb] at hlt

/-- Headline lifting theorem: without any global comparison-totality assumption, key agreement on
a finite pool gives equal class identifiers for comparator-equal pooled cursors. -/
theorem childClassID_eq_of_keyAgrees
    (spec : FrontierSpec Cursor Descriptor) (pool : List Cursor)
    {Key : Type w} (keyOf : Cursor → Key) (compareKey : Key → Key → Ordering)
    [Std.TransCmp compareKey]
    (hagree : ∀ a ∈ pool, ∀ b ∈ pool,
      spec.before a b = some (runtimeSeniorSwap (compareKey (keyOf a) (keyOf b))))
    {a b : Cursor} (ha : a ∈ pool) (hb : b ∈ pool)
    (h : spec.before a b = some Ordering.eq) :
    childClassID spec pool a = childClassID spec pool b :=
  childClassID_eq_of_pool_compareLaws
    (poolSpec_compareLaws_of_keyAgrees spec pool keyOf compareKey hagree) ha hb h

/-- Headline lifting theorem for strict classes: the senior endpoint receives the strictly smaller
identifier in the original pool. -/
theorem childClassID_lt_of_keyAgrees
    (spec : FrontierSpec Cursor Descriptor) (pool : List Cursor)
    {Key : Type w} (keyOf : Cursor → Key) (compareKey : Key → Key → Ordering)
    [Std.TransCmp compareKey]
    (hagree : ∀ a ∈ pool, ∀ b ∈ pool,
      spec.before a b = some (runtimeSeniorSwap (compareKey (keyOf a) (keyOf b))))
    {a b : Cursor} (ha : a ∈ pool) (hb : b ∈ pool)
    (h : spec.before a b = some Ordering.lt) :
    childClassID spec pool a < childClassID spec pool b :=
  childClassID_lt_of_pool_compareLaws
    (poolSpec_compareLaws_of_keyAgrees spec pool keyOf compareKey hagree) ha hb h

/-- Both pooled occurrences of a comparator-equivalent pair appear in the ranked pool (once each,
with the same class identifier).  Multiplicity is the list's, not a set's. -/
theorem rankPool_equal_children_same_rank_of_keyAgrees
    (spec : FrontierSpec Cursor Descriptor) (pool : List Cursor)
    {Key : Type w} (keyOf : Cursor → Key) (compareKey : Key → Key → Ordering)
    [Std.TransCmp compareKey]
    (hagree : ∀ a ∈ pool, ∀ b ∈ pool,
      spec.before a b = some (runtimeSeniorSwap (compareKey (keyOf a) (keyOf b))))
    {ranked : List (Cursor × Nat)} (hrank : rankPool spec pool = some ranked)
    {c₁ c₂ : Cursor} (hc₁ : c₁ ∈ pool) (hc₂ : c₂ ∈ pool)
    (heq : spec.before c₁ c₂ = some Ordering.eq) :
    (c₁, childClassID spec pool c₁) ∈ ranked ∧
      (c₂, childClassID spec pool c₂) ∈ ranked ∧
        childClassID spec pool c₁ = childClassID spec pool c₂ :=
  ⟨rankPool_mem (spec := spec) (pooled := pool) (ranked := ranked) hrank hc₁,
   rankPool_mem (spec := spec) (pooled := pool) (ranked := ranked) hrank hc₂,
   childClassID_eq_of_keyAgrees spec pool keyOf compareKey hagree hc₁ hc₂ heq⟩

/-! ## 7. Pool completeness and successful ranking from compiled keys

The frontier refuses (`rankPool = none`) exactly when some pooled pair is not comparable.  Once the
canonical key comparator supplies an answer for every pair of compiled keys, every pooled pair is
comparable, so the ranking succeeds and is *exactly* the map that records each occurrence together
with its class identifier. -/

/-- A globally lawful comparator makes every pool complete. -/
theorem poolComplete_of_compareLaws {spec : FrontierSpec Cursor Descriptor}
    {pool : List Cursor} (laws : CompareLaws spec.before) :
    PoolComplete spec pool := by
  intro a _ha b _hb
  rcases laws.total a b with h | h | h <;> rw [h] <;> rfl

/-- Pool completeness transported from the membership subtype.  Only comparisons of pooled
cursors are used. -/
theorem poolComplete_of_poolSpec_compareLaws {spec : FrontierSpec Cursor Descriptor}
    {pool : List Cursor} (laws : CompareLaws (poolSpec spec pool).before) :
    PoolComplete spec pool := by
  intro a ha b hb
  have hs : ((poolSpec spec pool).before ⟨a, ha⟩ ⟨b, hb⟩).isSome = true :=
    poolComplete_of_compareLaws (spec := poolSpec spec pool) (pool := pool.attach) laws
      ⟨a, ha⟩ (List.mem_attach pool ⟨a, ha⟩) ⟨b, hb⟩ (List.mem_attach pool ⟨b, hb⟩)
  exact hs

/-- Key agreement makes every pooled pair comparable. -/
theorem poolComplete_of_keyAgrees
    (spec : FrontierSpec Cursor Descriptor) (pool : List Cursor)
    {Key : Type w} (keyOf : Cursor → Key) (compareKey : Key → Key → Ordering)
    [Std.TransCmp compareKey]
    (hagree : ∀ a ∈ pool, ∀ b ∈ pool,
      spec.before a b = some (runtimeSeniorSwap (compareKey (keyOf a) (keyOf b)))) :
    PoolComplete spec pool := by
  intro a ha b hb
  rw [hagree a ha b hb]
  rfl

/-- A complete pool ranks successfully, and the ranked list is exactly the pool mapped to
`(cursor, classID)`.  In particular no occurrence is removed and no class is collapsed. -/
theorem rankPool_eq_some_map_of_poolComplete (spec : FrontierSpec Cursor Descriptor)
    (pool : List Cursor) (h : PoolComplete spec pool) :
    rankPool spec pool = some (pool.map fun c => (c, childClassID spec pool c)) := by
  refine (rankPool_eq_some_iff (spec := spec) (pooled := pool)
    (ranked := (pool.map fun c => (c, childClassID spec pool c)))).2 ⟨?_, rfl⟩
  exact poolComplete_eq_true.mpr h

/-- Headline ranking theorem: from compiled canonical keys, the pool ranking succeeds and equals
the explicit `(cursor, classID)` map.  No desired ranking and no global cursor totality is assumed;
the key comparator is total because it is a plain function on keys. -/
theorem rankPool_eq_some_map_of_keyAgrees
    (spec : FrontierSpec Cursor Descriptor) (pool : List Cursor)
    {Key : Type w} (keyOf : Cursor → Key) (compareKey : Key → Key → Ordering)
    [Std.TransCmp compareKey]
    (hagree : ∀ a ∈ pool, ∀ b ∈ pool,
      spec.before a b = some (runtimeSeniorSwap (compareKey (keyOf a) (keyOf b)))) :
    rankPool spec pool = some (pool.map fun c => (c, childClassID spec pool c)) :=
  rankPool_eq_some_map_of_poolComplete spec pool
    (poolComplete_of_keyAgrees spec pool keyOf compareKey hagree)

/-- Multiplicity: the first projection of a successfully ranked pool is the original pool, in the
same order.  This holds for any successful ranking, with no key-agreement hypothesis. -/
theorem rankPool_pool_fst {spec : FrontierSpec Cursor Descriptor} {pool : List Cursor}
    {ranked : List (Cursor × Nat)} (hrank : rankPool spec pool = some ranked) :
    ranked.map Prod.fst = pool := by
  obtain ⟨_, hm⟩ :=
    (rankPool_eq_some_iff (spec := spec) (pooled := pool) (ranked := ranked)).1 hrank
  rw [hm, List.map_map]
  apply List.map_id''
  intro c
  rfl

/-- Multiplicity and length preservation together. -/
theorem rankPool_multiplicity {spec : FrontierSpec Cursor Descriptor} {pool : List Cursor}
    {ranked : List (Cursor × Nat)} (hrank : rankPool spec pool = some ranked) :
    ranked.map Prod.fst = pool ∧ ranked.length = pool.length :=
  ⟨rankPool_pool_fst hrank, rankPool_length hrank⟩

/-! ## 8. The reusable finite-pool adapter

`CompiledKeyPool` packages the finite cursor pool with a concrete key for every pooled cursor and a
per-node receipt that the compiler produced it.  `FinitePoolAdapter` adds the comparator bridge.
Any next cursor comparator can instantiate this structure; the theorems in this section then give
the pool ranking and class-identifier laws with no global totality assumption. -/

/-- A finite pool of cursors with checked per-node compilation receipts. -/
structure CompiledKeyPool (Cursor : Type u) (Key : Type w) where
  /-- The finite pool.  Only these cursors are ranked. -/
  cursors : List Cursor
  /-- The runtime key compiler.  It may return `none` anywhere outside the pool. -/
  compile : Cursor → Option Key
  /-- The canonical key of each pooled cursor. -/
  keyOf : Cursor → Key
  /-- The canonical key comparator.  It is a plain total function on keys. -/
  compareKey : Key → Key → Ordering
  /-- The key comparator is transitive (supplied by the canonical-key development). -/
  compareKey_transCmp : Std.TransCmp compareKey
  /-- Per-node receipt: this concrete pooled cursor compiled to this concrete key. -/
  receipt : ∀ c, c ∈ cursors → compile c = some (keyOf c)

namespace CompiledKeyPool

variable {Cursor : Type u} {Key : Type w}

/-- The pool-level key agreement obtained from the comparator bridge and the per-node receipts.
This is the precise use of the receipts: they only supply the keys of pooled cursors. -/
theorem keyAgrees (P : CompiledKeyPool Cursor Key)
    {before : Cursor → Cursor → Option Ordering}
    (hbridge : ComparesByCompiledKey before P.compile P.compareKey) :
    ∀ a ∈ P.cursors, ∀ b ∈ P.cursors,
      before a b = some (runtimeSeniorSwap (P.compareKey (P.keyOf a) (P.keyOf b))) :=
  keyAgreesOn_of_comparesByCompiledKey P.cursors hbridge P.receipt

end CompiledKeyPool

/-- A complete finite-pool adapter: an actual frontier specification, a compiled-key pool, and the
one-per-pair comparator bridge.  No ranking datum is stored. -/
structure FinitePoolAdapter (Cursor : Type u) (Descriptor : Type v) (Key : Type w) where
  /-- The frontier specification whose pre-Rule-4b comparator is being certified. -/
  spec : FrontierSpec Cursor Descriptor
  /-- The finite successful-compilation pool. -/
  pool : CompiledKeyPool Cursor Key
  /-- The comparator bridge, checked only on pairs of successful compilations. -/
  bridge : ComparesByCompiledKey spec.before pool.compile pool.compareKey

namespace FinitePoolAdapter

variable {Cursor : Type u} {Descriptor : Type v} {Key : Type w}

/-- The finite-pool order laws derived by the adapter.  This is the theorem the next cursor
comparator instantiates; its `total` field ranges over the pool subtype only. -/
theorem compareLaws (A : FinitePoolAdapter Cursor Descriptor Key) :
    CompareLaws (poolSpec A.spec A.pool.cursors).before := by
  letI := A.pool.compareKey_transCmp
  exact poolSpec_compareLaws_of_keyAgrees A.spec A.pool.cursors A.pool.keyOf
    A.pool.compareKey (CompiledKeyPool.keyAgrees A.pool A.bridge)

/-- Every pooled pair is comparable, so the runtime refusal branch is unreachable on the pool. -/
theorem poolComplete (A : FinitePoolAdapter Cursor Descriptor Key) :
    PoolComplete A.spec A.pool.cursors :=
  poolComplete_of_poolSpec_compareLaws A.compareLaws

/-- The original pool ranks successfully and the result is exactly the `(cursor, classID)` map. -/
theorem rankPool_eq_some (A : FinitePoolAdapter Cursor Descriptor Key) :
    rankPool A.spec A.pool.cursors =
      some (A.pool.cursors.map fun c =>
        (c, childClassID A.spec A.pool.cursors c)) :=
  rankPool_eq_some_map_of_poolComplete A.spec A.pool.cursors A.poolComplete

/-- Every pooled occurrence appears exactly once in the ranked pool. -/
theorem rankPool_entry_mem (A : FinitePoolAdapter Cursor Descriptor Key)
    {ranked : List (Cursor × Nat)}
    (hrank : rankPool A.spec A.pool.cursors = some ranked) {c : Cursor}
    (hc : c ∈ A.pool.cursors) :
    (c, childClassID A.spec A.pool.cursors c) ∈ ranked :=
  rankPool_mem (spec := A.spec) (pooled := A.pool.cursors) (ranked := ranked) hrank hc

/-- Comparator-equal pooled cursors receive equal class identifiers. -/
theorem childClassID_eq (A : FinitePoolAdapter Cursor Descriptor Key)
    {a b : Cursor} (ha : a ∈ A.pool.cursors) (hb : b ∈ A.pool.cursors)
    (h : A.spec.before a b = some Ordering.eq) :
    childClassID A.spec A.pool.cursors a = childClassID A.spec A.pool.cursors b := by
  letI := A.pool.compareKey_transCmp
  exact childClassID_eq_of_keyAgrees A.spec A.pool.cursors A.pool.keyOf
    A.pool.compareKey (CompiledKeyPool.keyAgrees A.pool A.bridge) ha hb h

/-- Strictly senior pooled cursors receive strictly smaller class identifiers. -/
theorem childClassID_lt (A : FinitePoolAdapter Cursor Descriptor Key)
    {a b : Cursor} (ha : a ∈ A.pool.cursors) (hb : b ∈ A.pool.cursors)
    (h : A.spec.before a b = some Ordering.lt) :
    childClassID A.spec A.pool.cursors a < childClassID A.spec A.pool.cursors b := by
  letI := A.pool.compareKey_transCmp
  exact childClassID_lt_of_keyAgrees A.spec A.pool.cursors A.pool.keyOf
    A.pool.compareKey (CompiledKeyPool.keyAgrees A.pool A.bridge) ha hb h

/-- The ranking retains multiplicity: first projection recovers the original pool. -/
theorem rankPool_multiplicity (A : FinitePoolAdapter Cursor Descriptor Key)
    {ranked : List (Cursor × Nat)}
    (hrank : rankPool A.spec A.pool.cursors = some ranked) :
    ranked.map Prod.fst = A.pool.cursors ∧ ranked.length = A.pool.cursors.length :=
  TetraStereo.Rule4bInheritedRankFrontier.FinitePool.rankPool_multiplicity hrank

end FinitePoolAdapter

end TetraStereo.Rule4bInheritedRankFrontier.FinitePool

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.runtimeSeniorSwap_involutive
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.runtimeSeniorSwap_injective
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.transCmp_comp
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.transCmp_swapResult
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.compareLaws_some_of_transCmp
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.compareLaws_congr
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.keyBefore_compareLaws
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.compareLaws_subtype
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.keyAgreesOn_of_comparesByCompiledKey
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.poolSpec_compareLaws_of_keyAgrees
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.childClassID_attach_eq
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.childClassID_eq_of_pool_compareLaws
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.childClassID_lt_of_pool_compareLaws
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.childClassID_eq_of_keyAgrees
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.childClassID_lt_of_keyAgrees
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.rankPool_equal_children_same_rank_of_keyAgrees
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.poolComplete_of_compareLaws
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.poolComplete_of_poolSpec_compareLaws
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.poolComplete_of_keyAgrees
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.rankPool_eq_some_map_of_poolComplete
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.rankPool_eq_some_map_of_keyAgrees
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.rankPool_pool_fst
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.rankPool_multiplicity
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.CompiledKeyPool.keyAgrees
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.FinitePoolAdapter.compareLaws
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.FinitePoolAdapter.poolComplete
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.FinitePoolAdapter.rankPool_eq_some
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.FinitePoolAdapter.rankPool_entry_mem
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.FinitePoolAdapter.childClassID_eq
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.FinitePoolAdapter.childClassID_lt
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.FinitePool.FinitePoolAdapter.rankPool_multiplicity
