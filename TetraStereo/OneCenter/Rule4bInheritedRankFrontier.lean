import Lean
import TetraStereo.KernelOnly




































set_option autoImplicit false

namespace TetraStereo.Rule4bInheritedRankFrontier

universe u v

/-- A cursor together with its inherited rank path.  Smaller paths are senior. -/
structure RankedCursor (Cursor : Type u) where
  /-- Concatenation of the sibling class identifiers from the root to this cursor. -/
  rankPath : List Nat
  /-- The actual cursor at this rank path. -/
  cursor : Cursor

/-- Structural interface of the frontier construction.

* `children` is the actual child relation at the current cut;
* `resolve` is the tri-state evidence resolver: outer `none` is unavailable evidence, inner
  `none` is an independently established non-chiral (or non-bearing) occurrence, and
  `some (some d)` is validated uppercase chiral evidence;
* `before` is a complete pre-Rule-4b comparator on cursors.  It must stop before Rule 4b and
  return `none` only when the comparison cannot be completed.  The convention used throughout
  this module is: `before a b = some Ordering.lt` means that `a` precedes `b`, i.e. `a` is the
  senior endpoint, and smaller rank-path entries are senior. -/
structure FrontierSpec (Cursor : Type u) (Descriptor : Type v) where
  children : Cursor → List Cursor
  resolve : Cursor → Option (Option Descriptor)
  before : Cursor → Cursor → Option Ordering

/-- The selected rank path and the complete uppercase evidence population at that path. -/
structure FrontierChoice (Descriptor : Type v) where
  rankPath : List Nat
  evidence : List Descriptor

variable {Cursor : Type u} {Descriptor : Type v}
variable {spec : FrontierSpec Cursor Descriptor}

/-! ## Structural comparator laws

The correctness statements below never assume the ranking the algorithm is meant to compute.
They only assume that `before` is a lawful total preorder presented as an `Option Ordering`
comparator: it is total on comparable data, reflexive, and `eq`/`lt` compose as a weak order.
-/

/-- Structural laws of a complete total preorder.  `eq` is the induced equivalence and `lt` the
induced strict order; `gt` is the reverse of `lt`. -/
structure CompareLaws {Cursor : Type u}
    (before : Cursor → Cursor → Option Ordering) : Prop where
  /-- Every comparison of the domain of discourse is available. -/
  total : ∀ a b : Cursor,
    before a b = some Ordering.eq ∨
      before a b = some Ordering.lt ∨
        before a b = some Ordering.gt
  refl : ∀ a : Cursor, before a a = some Ordering.eq
  eq_symm : ∀ {a b : Cursor},
    before a b = some Ordering.eq → before b a = some Ordering.eq
  lt_symm : ∀ {a b : Cursor},
    before a b = some Ordering.lt → before b a = some Ordering.gt
  gt_symm : ∀ {a b : Cursor},
    before a b = some Ordering.gt → before b a = some Ordering.lt
  eq_eq : ∀ {a b c : Cursor},
    before a b = some Ordering.eq → before b c = some Ordering.eq →
      before a c = some Ordering.eq
  eq_lt : ∀ {a b c : Cursor},
    before a b = some Ordering.eq → before b c = some Ordering.lt →
      before a c = some Ordering.lt
  lt_eq : ∀ {a b c : Cursor},
    before a b = some Ordering.lt → before b c = some Ordering.eq →
      before a c = some Ordering.lt
  lt_lt : ∀ {a b c : Cursor},
    before a b = some Ordering.lt → before b c = some Ordering.lt →
      before a c = some Ordering.lt

namespace CompareLaws

variable {before : Cursor → Cursor → Option Ordering}

/-- `gt` followed by `eq` is `gt`. -/
theorem gt_eq_trans (laws : CompareLaws before) {a b c : Cursor}
    (hab : before a b = some Ordering.gt) (hbc : before b c = some Ordering.eq) :
    before a c = some Ordering.gt := by
  have hba : before b a = some Ordering.lt := laws.gt_symm hab
  have hcb : before c b = some Ordering.eq := laws.eq_symm hbc
  have hca : before c a = some Ordering.lt := laws.eq_lt hcb hba
  exact laws.lt_symm hca

/-- `gt` followed by `gt` is `gt`. -/
theorem gt_gt_trans (laws : CompareLaws before) {a b c : Cursor}
    (hab : before a b = some Ordering.gt) (hbc : before b c = some Ordering.gt) :
    before a c = some Ordering.gt := by
  have hba : before b a = some Ordering.lt := laws.gt_symm hab
  have hcb : before c b = some Ordering.lt := laws.gt_symm hbc
  exact laws.lt_symm (laws.lt_lt hcb hba)

/-- `eq` followed by `gt` is `gt`. -/
theorem eq_gt_trans (laws : CompareLaws before) {a b c : Cursor}
    (hab : before a b = some Ordering.eq) (hbc : before b c = some Ordering.gt) :
    before a c = some Ordering.gt := by
  have hcb : before c b = some Ordering.lt := laws.gt_symm hbc
  have hba : before b a = some Ordering.eq := laws.eq_symm hab
  exact laws.lt_symm (laws.lt_eq hcb hba)

end CompareLaws

/-! ## Counting helper

The helper below is the only counting fact needed by `childClassID_lt_of_lt`.  It is stated for
booleans so that it applies directly to `List.countP`.
-/

/-- If `p` implies `q` on `l`, and there is a witness in `l` where `p` fails and `q` holds, then
`countP p l < countP q l`. -/
theorem countP_lt_of_imp_of_witness (p q : Cursor → Bool) :
    ∀ (l : List Cursor) (a : Cursor),
      (∀ x ∈ l, p x → q x) → (¬ p a) → q a → a ∈ l →
        List.countP p l < List.countP q l
  | [], a, _himp, _hpa, _hqa, ha => by simp at ha
  | x :: xs, a, himp, hpa, hqa, ha => by
      have hxall : ∀ y ∈ xs, p y → q y :=
        fun y hy => himp y (List.mem_cons_of_mem x hy)
      rcases List.mem_cons.mp ha with rfl | hmem
      · have hle : List.countP p xs ≤ List.countP q xs :=
          List.countP_mono_left (fun y hy hpy => hxall y hy hpy)
        rw [List.countP_cons_of_neg hpa, List.countP_cons_of_pos hqa]
        omega
      · by_cases hpx : p x
        · have hqx : q x := himp x (List.mem_cons_self (a := x) (l := xs)) hpx
          rw [List.countP_cons_of_pos hpx, List.countP_cons_of_pos hqx]
          have ih := countP_lt_of_imp_of_witness p q xs a hxall hpa hqa hmem
          omega
        · rw [List.countP_cons_of_neg hpx]
          by_cases hqx : q x
          · rw [List.countP_cons_of_pos hqx]
            have ih := countP_lt_of_imp_of_witness p q xs a hxall hpa hqa hmem
            omega
          · rw [List.countP_cons_of_neg hqx]
            exact countP_lt_of_imp_of_witness p q xs a hxall hpa hqa hmem

/-! ## Pool-level class identifiers

A child class identifier is the number of pooled occurrences that strictly precede the
occurrence under the pre-Rule-4b comparator.  This is an ordinal rank of the class inside the
pool: it is constant on comparator-equivalent occurrences (so comparator ties are never split by
position) and strictly increases across a strict class boundary.  The actual numeric value is
immaterial: only the induced order of identifiers matters, and paths from unequal parent groups
are compared inside their parent prefix, never by these identifiers.

The numeric value is *not* the literal "zero-based class index" of a sorted scan: if the pool has
classes of sizes `n₀, n₁, n₂, …` in increasing order, the identifiers are
`0, n₀, n₀ + n₁, …` rather than `0, 1, 2, …`.  The two assignments induce exactly the same order
on class identifiers, which is all that rank-path comparison uses.
-/

/-- Number of pooled occurrences strictly preceding (senior to) `c`. -/
def childClassID (spec : FrontierSpec Cursor Descriptor) (pooled : List Cursor)
    (c : Cursor) : Nat :=
  List.countP (fun r => decide (spec.before r c = some Ordering.lt)) pooled

/-- Every ordered pair of the pool is comparable.  This is the completeness side condition under
which a pool is ranked. -/
def PoolComplete (spec : FrontierSpec Cursor Descriptor) (pooled : List Cursor) : Prop :=
  ∀ a ∈ pooled, ∀ b ∈ pooled, (spec.before a b).isSome = true

/-- Executable completeness check for a pool. -/
def poolComplete (spec : FrontierSpec Cursor Descriptor) (pooled : List Cursor) : Bool :=
  pooled.all fun a => pooled.all fun b => (spec.before a b).isSome

theorem poolComplete_eq_true {pooled : List Cursor} :
    poolComplete spec pooled = true ↔ PoolComplete spec pooled := by
  unfold poolComplete PoolComplete
  constructor
  · intro h a ha b hb
    have houter : ∀ x, x ∈ pooled →
        (pooled.all fun y => (spec.before x y).isSome) = true :=
      List.all_eq_true.mp h
    have hinner : ∀ y, y ∈ pooled → (spec.before a y).isSome = true :=
      List.all_eq_true.mp (houter a ha)
    exact hinner b hb
  · intro h
    apply List.all_eq_true.mpr
    intro a ha
    apply List.all_eq_true.mpr
    intro b hb
    exact h a ha b hb

/-- Rank one parent pool.  `none` is returned exactly when some pair in the pool is not
comparable, so an incomplete comparator refuses instead of being silently treated as a tie. -/
def rankPool (spec : FrontierSpec Cursor Descriptor) (pooled : List Cursor) :
    Option (List (Cursor × Nat)) :=
  if poolComplete spec pooled then
    some (pooled.map fun c => (c, childClassID spec pooled c))
  else
    none

/-- Exact characterisation of successful pool ranking. -/
theorem rankPool_eq_some_iff {pooled : List Cursor} {ranked : List (Cursor × Nat)} :
    rankPool spec pooled = some ranked ↔
      poolComplete spec pooled = true ∧
        ranked = pooled.map (fun c => (c, childClassID spec pooled c)) := by
  unfold rankPool
  by_cases h : poolComplete spec pooled = true
  · rw [if_pos h]
    constructor
    · intro hEq
      exact ⟨h, (Option.some_inj.1 hEq).symm⟩
    · rintro ⟨_, hEq⟩
      exact Option.some_inj.2 hEq.symm
  · rw [if_neg h]
    constructor
    · intro hEq
      cases hEq
    · rintro ⟨hp, _⟩
      exact absurd hp h

/-- An unavailable comparison anywhere in the pool refuses the pool. -/
theorem rankPool_eq_none_of_before_eq_none {pooled : List Cursor} {a b : Cursor}
    (ha : a ∈ pooled) (hb : b ∈ pooled) (h : spec.before a b = none) :
    rankPool spec pooled = none := by
  have hnot : ¬ PoolComplete spec pooled := by
    intro hc
    have hs : (spec.before a b).isSome = true := hc a ha b hb
    rw [h] at hs
    simp at hs
  cases hpc : poolComplete spec pooled with
  | false => simp [rankPool, hpc]
  | true => exact absurd (poolComplete_eq_true.mp hpc) hnot

/-- The pool ranking preserves multiplicity: every pooled occurrence contributes exactly one
entry, and no occurrence is removed by class formation. -/
theorem rankPool_length {pooled : List Cursor} {ranked : List (Cursor × Nat)}
    (hrank : rankPool spec pooled = some ranked) :
    ranked.length = pooled.length := by
  obtain ⟨_hpc, hm⟩ :=
    (rankPool_eq_some_iff (spec := spec) (pooled := pooled) (ranked := ranked)).1 hrank
  rw [hm, List.length_map]

/-- Every pooled occurrence appears in the ranked pool with its class identifier. -/
theorem rankPool_mem {pooled : List Cursor} {ranked : List (Cursor × Nat)}
    (hrank : rankPool spec pooled = some ranked) {c : Cursor} (hc : c ∈ pooled) :
    (c, childClassID spec pooled c) ∈ ranked := by
  obtain ⟨_hpc, hm⟩ :=
    (rankPool_eq_some_iff (spec := spec) (pooled := pooled) (ranked := ranked)).1 hrank
  rw [hm]
  exact List.mem_map_of_mem hc

/-- Comparator-equivalent occurrences of one pool receive equal class identifiers. -/
theorem childClassID_eq_of_eq (laws : CompareLaws spec.before)
    {reps : List Cursor} {a b : Cursor}
    (h : spec.before a b = some Ordering.eq) :
    childClassID spec reps a = childClassID spec reps b := by
  unfold childClassID
  apply List.countP_congr
  intro r _
  have hba : spec.before b a = some Ordering.eq := laws.eq_symm h
  constructor
  · intro hra
    exact decide_eq_true_iff.mpr (laws.lt_eq (decide_eq_true_iff.mp hra) h)
  · intro hrb
    exact decide_eq_true_iff.mpr (laws.lt_eq (decide_eq_true_iff.mp hrb) hba)

/-- A strict class boundary strictly increases the identifier: the senior class receives the
smaller identifier.  Both endpoints are required to be members of the pool, matching the
application (they are two pooled children of the same parent group).  The counting witness is
`a` itself: `a` occurs in the pool, `a` is not strictly senior to itself, and `a` strictly
precedes `b`, so the set counted by `a`'s identifier is strictly contained in the set counted by
`b`'s. -/
theorem childClassID_lt_of_lt (laws : CompareLaws spec.before)
    {pooled : List Cursor} {a b : Cursor}
    (h : spec.before a b = some Ordering.lt) (ha : a ∈ pooled) (_hb : b ∈ pooled) :
    childClassID spec pooled a < childClassID spec pooled b := by
  unfold childClassID
  refine countP_lt_of_imp_of_witness
    (fun r => decide (spec.before r a = some Ordering.lt))
    (fun r => decide (spec.before r b = some Ordering.lt)) pooled a ?_ ?_ ?_ ha
  · intro r _ hr
    exact decide_eq_true_iff.mpr (laws.lt_lt (decide_eq_true_iff.mp hr) h)
  · intro hp
    have hlt : spec.before a a = some Ordering.lt := decide_eq_true_iff.mp hp
    rw [laws.refl a] at hlt
    exact absurd hlt (by simp)
  · exact decide_eq_true_iff.mpr h

/-- Equal children of one pool share the same class identifier.  This is the "no positional tie
split" obligation: the identifier does not depend on the position of the child in the pool. -/
theorem rankPool_equal_children_same_rank (laws : CompareLaws spec.before)
    {pooled : List Cursor} {ranked : List (Cursor × Nat)}
    (hrank : rankPool spec pooled = some ranked)
    {c₁ c₂ : Cursor} (hc₁ : c₁ ∈ pooled) (hc₂ : c₂ ∈ pooled)
    (heq : spec.before c₁ c₂ = some Ordering.eq) :
    (c₁, childClassID spec pooled c₁) ∈ ranked ∧
      (c₂, childClassID spec pooled c₂) ∈ ranked ∧
        childClassID spec pooled c₁ = childClassID spec pooled c₂ :=
  ⟨rankPool_mem hrank hc₁, rankPool_mem hrank hc₂,
    childClassID_eq_of_eq laws heq⟩

/-- Appending the shared class identifier to a parent path keeps equivalent children on the same
rank path. -/
theorem childPath_eq_of_comparator_eq (laws : CompareLaws spec.before)
    {pooled : List Cursor} {c₁ c₂ : Cursor}
    (heq : spec.before c₁ c₂ = some Ordering.eq) (parent : List Nat) :
    parent ++ [childClassID spec pooled c₁] = parent ++ [childClassID spec pooled c₂] := by
  rw [childClassID_eq_of_eq laws heq]

/-! ## Parent paths, pooling and descent -/

/-- The distinct parent rank paths of a frontier, in first-occurrence order. -/
def parentPaths : List (RankedCursor Cursor) → List (List Nat)
  | [] => []
  | rc :: rest =>
      rc.rankPath :: (parentPaths rest).filter (fun p => decide (p ≠ rc.rankPath))

/-- All children of frontier occurrences carrying `parent`, pooled **without deduplication**.
Order is irrelevant to the ranking; multiplicity is preserved because `flatMap` never removes an
occurrence. -/
def pooledChildren (spec : FrontierSpec Cursor Descriptor) (parent : List Nat)
    (frontier : List (RankedCursor Cursor)) : List Cursor :=
  frontier.flatMap fun rc =>
    if rc.rankPath = parent then spec.children rc.cursor else []

/-- Membership characterisation of a pooled child. -/
theorem mem_pooledChildren_iff {parent : List Nat}
    {frontier : List (RankedCursor Cursor)} {c : Cursor} :
    c ∈ pooledChildren spec parent frontier ↔
      ∃ rc ∈ frontier, rc.rankPath = parent ∧ c ∈ spec.children rc.cursor := by
  unfold pooledChildren
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨rc, hrc, hc⟩
    refine ⟨rc, hrc, ?_, ?_⟩
    · by_cases hp : rc.rankPath = parent
      · exact hp
      · simp [hp] at hc
    · by_cases hp : rc.rankPath = parent
      · simpa [hp] using hc
      · simp [hp] at hc
  · rintro ⟨rc, hrc, hp, hc⟩
    exact ⟨rc, hrc, by simp [hp, hc]⟩

/-- A child of a frontier occurrence belongs to the pool of that occurrence's parent path. -/
theorem mem_pooledChildren_of_mem_children {parent : List Nat}
    {frontier : List (RankedCursor Cursor)} {rc : RankedCursor Cursor} {c : Cursor}
    (hrc : rc ∈ frontier) (hpath : rc.rankPath = parent)
    (hc : c ∈ spec.children rc.cursor) :
    c ∈ pooledChildren spec parent frontier := by
  rw [mem_pooledChildren_iff]
  exact ⟨rc, hrc, hpath, hc⟩

/-- Descend all equal-parent-path groups of one frontier.  Group order in the output is
immaterial for the selection, which inspects every path; only the class identifiers (and hence
the inherited parent prefixes) determine priority. -/
def regroupGroups (spec : FrontierSpec Cursor Descriptor)
    (frontier : List (RankedCursor Cursor)) :
    List (List Nat) → Option (List (RankedCursor Cursor))
  | [] => some []
  | parent :: parents =>
      match rankPool spec (pooledChildren spec parent frontier) with
      | none => none
      | some ranked =>
          match regroupGroups spec frontier parents with
          | none => none
          | some tail =>
              some ((ranked.map fun entry => ⟨parent ++ [entry.2], entry.1⟩) ++ tail)

/-- Descend one sphere, never comparing or re-ranking children of unequal parent paths. -/
def regroup (spec : FrontierSpec Cursor Descriptor)
    (frontier : List (RankedCursor Cursor)) : Option (List (RankedCursor Cursor)) :=
  regroupGroups spec frontier (parentPaths frontier)

/-- An incomplete pool refuses the descent. -/
theorem regroupGroups_eq_none_of_rankPool_eq_none
    {frontier : List (RankedCursor Cursor)} {parents : List (List Nat)}
    {parent : List Nat} (hparent : parent ∈ parents)
    (hnone : rankPool spec (pooledChildren spec parent frontier) = none) :
    regroupGroups spec frontier parents = none := by
  induction parents with
  | nil => simp at hparent
  | cons p ps ih =>
      simp only [regroupGroups]
      rcases List.mem_cons.mp hparent with rfl | hmem
      · simp [hnone]
      · have ih' : regroupGroups spec frontier ps = none := ih hmem
        cases hr : rankPool spec (pooledChildren spec p frontier) with
        | none => rfl
        | some ranked => simp [ih']

/-- An incomplete pool refuses the whole descent, so failure propagates to the selection. -/
theorem regroup_eq_none_of_rankPool_eq_none
    {frontier : List (RankedCursor Cursor)} {parent : List Nat}
    (hparent : parent ∈ parentPaths frontier)
    (hnone : rankPool spec (pooledChildren spec parent frontier) = none) :
    regroup spec frontier = none := by
  unfold regroup
  exact regroupGroups_eq_none_of_rankPool_eq_none hparent hnone

/-! ## Layer resolution and selection -/

/-- Resolve every occurrence of one sphere.  Any unavailable occurrence refuses the sphere. -/
def classifyLayer (spec : FrontierSpec Cursor Descriptor) :
    List (RankedCursor Cursor) → Option (List (RankedCursor Cursor × Option Descriptor))
  | [] => some []
  | rc :: rest =>
      match spec.resolve rc.cursor with
      | none => none
      | some evidence =>
          match classifyLayer spec rest with
          | none => none
          | some tail => some ((rc, evidence) :: tail)

/-- An unavailable occurrence anywhere on the sphere refuses the sphere. -/
theorem classifyLayer_eq_none_of_resolve_eq_none (spec : FrontierSpec Cursor Descriptor)
    (frontier : List (RankedCursor Cursor)) (rc : RankedCursor Cursor)
    (hmem : rc ∈ frontier) (h : spec.resolve rc.cursor = none) :
    classifyLayer spec frontier = none := by
  induction frontier with
  | nil => simp at hmem
  | cons x xs ih =>
      rw [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · simp [classifyLayer, h]
      · have hx : classifyLayer spec xs = none := ih hmem
        cases hr : spec.resolve x.cursor with
        | none => simp [classifyLayer, hr]
        | some evidence => simp [classifyLayer, hr, hx]

/-- The uppercase evidence of one resolved sphere, with the rank path of its occurrence. -/
def layerCandidates (classified : List (RankedCursor Cursor × Option Descriptor)) :
    List (RankedCursor Cursor × Descriptor) :=
  classified.filterMap fun entry =>
    match entry.2 with
    | none => none
    | some descriptor => some (entry.1, descriptor)

/-- All uppercase descriptors at exactly `path`, preserving multiplicity.  Non-chiral entries
contribute nothing; unavailable entries cannot occur here because `classifyLayer` refused them. -/
def evidenceAtPath (classified : List (RankedCursor Cursor × Option Descriptor))
    (path : List Nat) : List Descriptor :=
  classified.filterMap fun entry =>
    match entry.2 with
    | none => none
    | some descriptor =>
        if entry.1.rankPath = path then some descriptor else none

/-- A matching entry contributes its uppercase descriptor to `evidenceAtPath`. -/
theorem mem_evidenceAtPath_of_entry
    {classified : List (RankedCursor Cursor × Option Descriptor)}
    {entry : RankedCursor Cursor × Option Descriptor} {path : List Nat} {d : Descriptor}
    (hentry : entry ∈ classified) (hpath : entry.1.rankPath = path)
    (hev : entry.2 = some d) :
    d ∈ evidenceAtPath classified path := by
  unfold evidenceAtPath
  rw [List.mem_filterMap]
  exact ⟨entry, hentry, by simp [hev, hpath]⟩

/-- Lexicographically least path of a nonempty path list. -/
def minPath? : List (List Nat) → Option (List Nat)
  | [] => none
  | p :: ps => some (ps.foldl (fun best q => if q < best then q else best) p)

/-- A fold that always returns one of its two arguments can only produce an element of the
initial value together with the folded list. -/
theorem foldl_choice_mem (f : List Nat → List Nat → List Nat)
    (hf : ∀ a b : List Nat, f a b = a ∨ f a b = b) :
    ∀ (init : List Nat) (ps : List (List Nat)),
      ps.foldl f init ∈ init :: ps
  | init, [] => by simp
  | init, q :: qs => by
      simp only [List.foldl_cons]
      have hmem := foldl_choice_mem f hf (f init q) qs
      rcases List.mem_cons.mp hmem with heq | htail
      · rw [heq]
        rcases hf init q with hchoice | hchoice
        · rw [hchoice]
          exact List.mem_cons_self (a := init) (l := q :: qs)
        · rw [hchoice]
          exact List.mem_cons_of_mem init (List.mem_cons_self (a := q) (l := qs))
      · exact List.mem_cons_of_mem init (List.mem_cons_of_mem q htail)

/-- `minPath?` returns a path of its input. -/
theorem minPath?_mem {ps : List (List Nat)} {p : List Nat}
    (h : minPath? ps = some p) : p ∈ ps := by
  cases ps with
  | nil => simp [minPath?] at h
  | cons q qs =>
      simp only [minPath?] at h
      have hp : qs.foldl (fun best q => if q < best then q else best) q = p :=
        Option.some_inj.1 h
      rw [← hp]
      exact foldl_choice_mem (fun best q => if q < best then q else best) (by
        intro a b
        by_cases hlt : b < a
        · exact Or.inr (by simp [hlt])
        · exact Or.inl (by simp [hlt])) q qs

/-- Select the least candidate path of a resolved sphere and collect all uppercase evidence at
exactly that path. -/
def selectLayerChoice? (classified : List (RankedCursor Cursor × Option Descriptor)) :
    Option (FrontierChoice Descriptor) :=
  Option.map (fun path => ⟨path, evidenceAtPath classified path⟩)
    (minPath? ((layerCandidates classified).map fun entry => entry.1.rankPath))

/-- The selected path of a layer is one of the candidate paths. -/
theorem selectLayerChoice?_path_mem
    {classified : List (RankedCursor Cursor × Option Descriptor)}
    {choice : FrontierChoice Descriptor} (h : selectLayerChoice? classified = some choice) :
    choice.rankPath ∈ (layerCandidates classified).map fun entry => entry.1.rankPath := by
  unfold selectLayerChoice? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨path, hpath, hchoice⟩ := h
  rw [← hchoice]
  exact minPath?_mem hpath

/-- The evidence carried by a selected layer is exactly the complete uppercase evidence
population at the selected rank path (multiplicity preserved, nothing added). -/
theorem selectLayerChoice?_evidence
    {classified : List (RankedCursor Cursor × Option Descriptor)}
    {choice : FrontierChoice Descriptor} (h : selectLayerChoice? classified = some choice) :
    choice.evidence = evidenceAtPath classified choice.rankPath := by
  unfold selectLayerChoice? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨path, _hpath, hchoice⟩ := h
  rw [← hchoice]

/-- Breadth-first inherited-rank selection.  An empty frontier is exhausted and contributes no
evidence; a nonempty frontier at zero fuel refuses; otherwise the current sphere is resolved and
either selected (if it carries uppercase evidence) or descended. -/
def selectChoice? (spec : FrontierSpec Cursor Descriptor) :
    Nat → List (RankedCursor Cursor) → Option (FrontierChoice Descriptor)
  | 0, [] => some ⟨[], []⟩
  | 0, _ :: _ => none
  | _ + 1, [] => some ⟨[], []⟩
  | fuel + 1, x :: xs =>
      match classifyLayer spec (x :: xs) with
      | none => none
      | some classified =>
          match layerCandidates classified with
          | [] =>
              match regroup spec (x :: xs) with
              | none => none
              | some next => selectChoice? spec fuel next
          | _ :: _ => selectLayerChoice? classified

/-- Evidence-only view of `selectChoice?`. -/
def selectEvidence? (spec : FrontierSpec Cursor Descriptor) (fuel : Nat)
    (frontier : List (RankedCursor Cursor)) : Option (List Descriptor) :=
  (selectChoice? spec fuel frontier).map fun choice => choice.evidence

/-- A frontier with one ligand cursor at the root rank path. -/
def root (cursor : Cursor) : RankedCursor Cursor := ⟨[], cursor⟩

/-- Selection from a single ligand root. -/
def selectFromRoot? (spec : FrontierSpec Cursor Descriptor) (fuel : Nat)
    (cursor : Cursor) : Option (List Descriptor) :=
  selectEvidence? spec fuel [root cursor]

/-- Unavailable evidence at any occurrence of the current sphere refuses the whole selection. -/
theorem selectChoice?_eq_none_of_mem_resolve_none (spec : FrontierSpec Cursor Descriptor)
    (fuel : Nat) (frontier : List (RankedCursor Cursor)) (rc : RankedCursor Cursor)
    (hmem : rc ∈ frontier) (h : spec.resolve rc.cursor = none) :
    selectChoice? spec fuel frontier = none := by
  induction fuel generalizing frontier rc with
  | zero =>
      cases frontier with
      | nil => simp at hmem
      | cons x xs => rfl
  | succ fuel ih =>
      cases frontier with
      | nil => simp at hmem
      | cons x xs =>
          have hnone : classifyLayer spec (x :: xs) = none :=
            classifyLayer_eq_none_of_resolve_eq_none spec (x :: xs) rc hmem h
          simp [selectChoice?, hnone]

/-- Evidence view of the refusal theorem. -/
theorem selectEvidence?_eq_none_of_mem_resolve_none (spec : FrontierSpec Cursor Descriptor)
    (fuel : Nat) (frontier : List (RankedCursor Cursor)) (rc : RankedCursor Cursor)
    (hmem : rc ∈ frontier) (h : spec.resolve rc.cursor = none) :
    selectEvidence? spec fuel frontier = none := by
  unfold selectEvidence?
  simp [selectChoice?_eq_none_of_mem_resolve_none spec fuel frontier rc hmem h]

/-- The empty frontier is exhausted without evidence, at any fuel. -/
@[simp] theorem selectChoice?_nil (spec : FrontierSpec Cursor Descriptor) (fuel : Nat) :
    selectChoice? spec fuel [] = some ⟨[], []⟩ := by
  cases fuel <;> rfl

/-- Zero fuel with a nonempty frontier refuses. -/
@[simp] theorem selectChoice?_zero_cons (spec : FrontierSpec Cursor Descriptor)
    (rc : RankedCursor Cursor) (rest : List (RankedCursor Cursor)) :
    selectChoice? spec 0 (rc :: rest) = none := rfl

/-- Evidence view of the empty frontier. -/
@[simp] theorem selectEvidence?_nil (spec : FrontierSpec Cursor Descriptor) (fuel : Nat) :
    selectEvidence? spec fuel [] = some [] := by
  unfold selectEvidence?
  simp [selectChoice?_nil]

/-- Evidence view of zero-fuel refusal. -/
@[simp] theorem selectEvidence?_zero_cons (spec : FrontierSpec Cursor Descriptor)
    (rc : RankedCursor Cursor) (rest : List (RankedCursor Cursor)) :
    selectEvidence? spec 0 (rc :: rest) = none := by
  unfold selectEvidence?
  simp [selectChoice?_zero_cons]

/-! ## Inherited parent precedence -/

/-- Auxiliary recursive form of `append_singleton_lt_of_lt_of_length_eq` with all arguments
explicit, so that the recursive call is applied in a fixed argument order. -/
private theorem append_singleton_lt_aux :
    ∀ (a b : List Nat), a.length = b.length → a < b →
      ∀ x y : Nat, a ++ [x] < b ++ [y]
  | [], b, hlen, h, x, y => by
      cases b with
      | nil => exact absurd h (List.not_lt_nil [])
      | cons _ _ =>
          simp only [List.length_nil, List.length_cons] at hlen
          exact absurd hlen (by omega)
  | _ :: _, [], _hlen, h, _x, _y =>
      absurd h (List.not_lt_nil _)
  | a₁ :: as, b₁ :: bs, hlen, h, x, y => by
      have hlen' : as.length = bs.length := by
        simp only [List.length_cons] at hlen
        omega
      rw [List.cons_lt_cons_iff] at h
      simp only [List.cons_append]
      rw [List.cons_lt_cons_iff]
      rcases h with hlt | ⟨heq, htail⟩
      · exact Or.inl hlt
      · subst heq
        exact Or.inr ⟨rfl, append_singleton_lt_aux as bs hlen' htail x y⟩

/-- Extending two equal-length paths preserves their lexicographic order.  This is the formal
content of "inherited different parent path precedence": a child of a senior parent path stays
senior to every child of a junior parent path, whatever class identifiers are appended.

The equal-length hypothesis is the structural invariant of a breadth level: starting from a
single root, every occurrence of one sphere has a path of the same length, because each descent
appends exactly one class identifier.  Without it the statement is false (one parent may be a
proper prefix of another). -/
theorem append_singleton_lt_of_lt_of_length_eq {a b : List Nat}
    (hlen : a.length = b.length) (h : a < b) (x y : Nat) :
    a ++ [x] < b ++ [y] :=
  append_singleton_lt_aux a b hlen h x y

/-- Different parent paths, of equal length, keep their inherited precedence after appending any
child class identifiers. -/
theorem inherited_path_precedence {parentA parentB : List Nat} {classA classB : Nat}
    (hlen : parentA.length = parentB.length) (h : parentA < parentB) :
    parentA ++ [classA] < parentB ++ [classB] :=
  append_singleton_lt_of_lt_of_length_eq hlen h classA classB

/-! ## Two-descriptor majority (Rule-4b instantiation helper)

The structural combinator above is descriptor-agnostic.  P-92.5.2.1(b)/(c) additionally needs the
majority reading of the selected population.  Instantiating `left := RS.R`, `right := RS.S`
reproduces the existing production rule: a strict majority yields the majority descriptor, and an
exact tie yields both descriptors.  An empty population yields no reference.  Descriptors other
than `left` and `right` are not counted by this helper; in the Rule-4b instantiation the
population consists of exactly the two descriptors.
-/

/-- Majority of two distinguished descriptors in a population, preserving the production
tie convention. -/
def majorityReferences {D : Type v} [DecidableEq D]
    (left right : D) (descriptors : List D) : List D :=
  if descriptors.isEmpty then []
  else
    let leftCount := (descriptors.filter fun d => decide (d = left)).length
    let rightCount := (descriptors.filter fun d => decide (d = right)).length
    if rightCount < leftCount then [left]
    else if leftCount < rightCount then [right]
    else [left, right]

/-- The empty population has no reference. -/
@[simp] theorem majorityReferences_nil {D : Type v} [DecidableEq D]
    (left right : D) : majorityReferences left right [] = [] := by
  simp [majorityReferences]

/-- Full Rule-4b reference selection over a ligand root: inherited-rank evidence, then the
two-descriptor majority. -/
def selectReferencesFromRoot? (spec : FrontierSpec Cursor Descriptor) [DecidableEq Descriptor]
    (left right : Descriptor) (fuel : Nat) (cursor : Cursor) : Option (List Descriptor) :=
  (selectFromRoot? spec fuel cursor).map (majorityReferences left right)

end TetraStereo.Rule4bInheritedRankFrontier

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.childClassID_eq_of_eq
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.childClassID_lt_of_lt
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.rankPool_equal_children_same_rank
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.rankPool_eq_some_iff
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.rankPool_length
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.countP_lt_of_imp_of_witness
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.classifyLayer_eq_none_of_resolve_eq_none
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.selectChoice?_eq_none_of_mem_resolve_none
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.selectEvidence?_eq_none_of_mem_resolve_none
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.append_singleton_lt_of_lt_of_length_eq
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.inherited_path_precedence
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.minPath?_mem
assert_kernel_only TetraStereo.Rule4bInheritedRankFrontier.selectLayerChoice?_evidence
