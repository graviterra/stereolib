import Mathlib.Logic.Relation
























set_option autoImplicit false

namespace TetraStereo.Certificate.WeightedDemand

/-- A finite conservative dependency graph. `children cursor` are the ordinary dependencies and
`requests cursor` is a list of reference frames that must be evaluated before `cursor` can be
ranked. Both lists are explicit data, so the graph carries no hidden success assumption. -/
structure Graph (α : Type) where
  children : α → List α
  requests : α → List (List α)

/-- Every cursor that must be ranked before `cursor`: ordinary children plus every reference of
every request. -/
def successors {α : Type} (g : Graph α) (cursor : α) : List α :=
  g.children cursor ++ (g.requests cursor).flatten

/-- Directed edge of the conservative potential-demand graph. -/
def Edge {α : Type} (g : Graph α) (parent child : α) : Prop :=
  child ∈ successors g parent

/-- `cursor` is reachable from one of `roots` through zero or more demand edges. -/
def Reachable {α : Type} (g : Graph α) (roots : List α) (cursor : α) : Prop :=
  ∃ root ∈ roots, Relation.ReflTransGen (Edge g) root cursor

/-- Only the graph reachable from `roots` is required to be acyclic. -/
def Acyclic {α : Type} (g : Graph α) (roots : List α) : Prop :=
  ∀ cursor, Reachable g roots cursor → ¬ Relation.TransGen (Edge g) cursor cursor

/-- Data-only proposed ranks: a list of `(cursor, rank)` pairs. -/
abbrev Table (α : Type) := List (α × Nat)

/-- First-match lookup of a cursor in a rank table. -/
def lookup {α : Type} [DecidableEq α] (table : Table α) (cursor : α) : Option Nat :=
  (table.find? (fun entry => decide (entry.1 = cursor))).map Prod.snd

/-- Rank of a cursor in a table, defaulting to `0` when absent. -/
def height {α : Type} [DecidableEq α] (table : Table α) (cursor : α) : Nat :=
  (lookup table cursor).getD 0

/-- Maximum rank of a list of cursors. -/
def listHeight {α : Type} (h : α → Nat) : List α → Nat
  | [] => 0
  | cursor :: rest => max (h cursor) (listHeight h rest)

/-- A checked assignment of positive ranks to a closed set of vertices. Child edges consume one
fuel step; callback requests consume two, including an empty request whose frame step is still
charged. -/
structure RankCertificate {α : Type} (g : Graph α) where
  vertices : List α
  height : α → Nat
  positive : ∀ cursor ∈ vertices, 0 < height cursor
  children : ∀ cursor ∈ vertices, ∀ child ∈ g.children cursor,
    child ∈ vertices ∧ height child + 1 ≤ height cursor
  callbacks : ∀ cursor ∈ vertices, ∀ request ∈ g.requests cursor,
    (∀ reference ∈ request, reference ∈ vertices) ∧ listHeight height request + 2 ≤ height cursor

/-- The checker-independent validity property: every vertex has positive rank, every child edge is
closed and strictly ranked, and every callback request is closed and ranked at least two above all
its references. -/
def TableValid {α : Type} [DecidableEq α] (g : Graph α) (table : Table α) : Prop :=
  (∀ cursor ∈ table.map Prod.fst, 0 < height table cursor) ∧
  (∀ cursor ∈ table.map Prod.fst, ∀ child ∈ g.children cursor,
    child ∈ table.map Prod.fst ∧ height table child + 1 ≤ height table cursor) ∧
  (∀ cursor ∈ table.map Prod.fst, ∀ request ∈ g.requests cursor,
    (∀ reference ∈ request, reference ∈ table.map Prod.fst) ∧
      listHeight (height table) request + 2 ≤ height table cursor)

instance instDecidableTableValid {α : Type} [DecidableEq α] (g : Graph α) (table : Table α) :
    Decidable (TableValid g table) := by
  unfold TableValid
  infer_instance

/-- The certificate derived from a valid table. -/
def certificateOfValid {α : Type} [DecidableEq α] (g : Graph α) (table : Table α)
    (valid : TableValid g table) : RankCertificate g :=
  { vertices := table.map Prod.fst, height := height table,
    positive := valid.1, children := valid.2.1, callbacks := valid.2.2 }

/-- Executable checker: a table yields a genuine rank certificate exactly when it is valid. -/
def check? {α : Type} [DecidableEq α] (g : Graph α) (table : Table α) :
    Option (RankCertificate g) :=
  if valid : TableValid g table then some (certificateOfValid g table valid) else none

/-- The rank a fresh cursor must receive if all its successors are already completed in `table`. -/
def requiredHeight {α : Type} [DecidableEq α] (g : Graph α) (table : Table α) (cursor : α) : Nat :=
  let childHeight := listHeight (height table) (g.children cursor) + 1
  (g.requests cursor).foldl
    (fun bound request => max bound (listHeight (height table) request + 2)) childHeight

/-- Discovery failures describe this conservative graph, not chemical nonexistence. -/
inductive DiscoveryFailure (α : Type)
  | cycle (cursor : α)
  | traversalLimit
  | invalidRanks
  | missingRoot

/-- Memoized postorder traversal. The active path detects cycles before revisiting descendants;
completed vertices are reused. The separate checker `check?` is the authority for every produced
bound. -/
def discover {α : Type} [DecidableEq α] (g : Graph α) :
    Nat → List α → Table α → α → Except (DiscoveryFailure α) (Table α)
  | 0, _, table, cursor =>
      if (lookup table cursor).isSome then .ok table else .error .traversalLimit
  | remaining + 1, active, table, cursor =>
      if (lookup table cursor).isSome then .ok table
      else if cursor ∈ active then .error (.cycle cursor)
      else do
        let finished ← (successors g cursor).foldlM
          (fun known child => discover g remaining (cursor :: active) known child) table
        pure ((cursor, requiredHeight g finished cursor) :: finished)

/-- A checked graph covers the requested roots, including every reachable dependency. -/
structure Plan {α : Type} (g : Graph α) (roots : List α) where
  ranks : RankCertificate g
  covers : ∀ root ∈ roots, root ∈ ranks.vertices

/-- The computed maximum rank plus one, sufficient for a complete frame evaluation at that budget. -/
def Plan.bound {α : Type} {g : Graph α} {roots : List α} (plan : Plan g roots) : Nat :=
  listHeight plan.ranks.height roots + 1

/-- No graph or ranks are supplied: `traversalBudget` limits the memoized DFS, `check?` is the
authority for every produced rank, and root coverage is rechecked. -/
def prepare {α : Type} [DecidableEq α] (g : Graph α) (traversalBudget : Nat)
    (roots : List α) : Except (DiscoveryFailure α) (Plan g roots) := do
  let table ← roots.foldlM (fun known root => discover g traversalBudget [] known root) []
  let some ranks := check? g table | .error .invalidRanks
  if covers : ∀ root ∈ roots, root ∈ ranks.vertices then
    .ok { ranks, covers }
  else .error .missingRoot

/-! ## Basic table facts -/

theorem lookup_cons {α : Type} [DecidableEq α] (table : Table α) (first cursor : α) (rank : Nat) :
    lookup ((first, rank) :: table) cursor =
      if first = cursor then some rank else lookup table cursor := by
  by_cases same : first = cursor <;> simp [lookup, same]

theorem lookup_isSome_iff {α : Type} [DecidableEq α] (table : Table α) (cursor : α) :
    (lookup table cursor).isSome = true ↔ cursor ∈ table.map Prod.fst := by
  induction table with
  | nil => simp [lookup]
  | cons entry rest ih =>
    rcases entry with ⟨first, rank⟩
    rw [lookup_cons rest first cursor rank]
    by_cases same : first = cursor
    · subst first
      simp
    · simp [same, ih, Ne.symm same]

/-- Completed entries keep both their identity and their first-match rank when new work is added. -/
def TableExtends {α : Type} [DecidableEq α] (before after : Table α) : Prop :=
  ∀ cursor ∈ before.map Prod.fst,
    cursor ∈ after.map Prod.fst ∧ height after cursor = height before cursor

theorem TableExtends.refl {α : Type} [DecidableEq α] (table : Table α) : TableExtends table table :=
  fun _ present => ⟨present, rfl⟩

theorem TableExtends.trans {α : Type} [DecidableEq α] {first second third : Table α}
    (left : TableExtends first second) (right : TableExtends second third) :
    TableExtends first third := by
  intro cursor present
  obtain ⟨middle, heightEq⟩ := left cursor present
  obtain ⟨last, next⟩ := right cursor middle
  exact ⟨last, next.trans heightEq⟩

theorem TableExtends.cons {α : Type} [DecidableEq α] (table : Table α) (cursor : α) (rank : Nat)
    (fresh : cursor ∉ table.map Prod.fst) : TableExtends table ((cursor, rank) :: table) := by
  intro old present
  have different : cursor ≠ old := by rintro rfl; exact fresh present
  refine ⟨by simp [present], ?_⟩
  simp [height, lookup_cons, different]

theorem listHeight_mem {α : Type} (h : α → Nat) (values : List α) (value : α)
    (present : value ∈ values) : h value ≤ listHeight h values := by
  induction values with
  | nil => simp at present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih present) (Nat.le_max_right _ _)

theorem listHeight_congr {α : Type} (left right : α → Nat) (values : List α)
    (agree : ∀ value ∈ values, left value = right value) :
    listHeight left values = listHeight right values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    simp only [listHeight, agree first (by simp),
      ih (fun value present => agree value (by simp [present]))]

/-! ## Required-height bounds -/

private theorem maxFold_ge_start {α : Type} (value : α → Nat) (items : List α) (start : Nat) :
    start ≤ items.foldl (fun bound item => max bound (value item)) start := by
  induction items generalizing start with
  | nil => exact Nat.le_refl _
  | cons first rest ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

private theorem maxFold_ge_member {α : Type} (value : α → Nat) (items : List α) (start : Nat)
    (item : α) (present : item ∈ items) :
    value item ≤ items.foldl (fun bound item => max bound (value item)) start := by
  induction items generalizing start with
  | nil => simp at present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact Nat.le_trans (Nat.le_max_right _ _) (maxFold_ge_start value rest _)
    · exact ih _ present

theorem requiredHeight_children {α : Type} [DecidableEq α] (g : Graph α) (table : Table α)
    (cursor : α) :
    listHeight (height table) (g.children cursor) + 1 ≤ requiredHeight g table cursor :=
  maxFold_ge_start _ _ _

theorem requiredHeight_callback {α : Type} [DecidableEq α] (g : Graph α) (table : Table α)
    (cursor : α) (request : List α) (present : request ∈ g.requests cursor) :
    listHeight (height table) request + 2 ≤ requiredHeight g table cursor :=
  maxFold_ge_member (fun request => listHeight (height table) request + 2) _ _ request present

/-- A completed dependency set permits one fresh vertex to be added without invalidating any
previous rank. This is the invariant maintained by the memoized postorder discovery. -/
theorem tableValid_cons {α : Type} [DecidableEq α] (g : Graph α)
    (table : Table α) (valid : TableValid g table)
    (cursor : α) (fresh : cursor ∉ table.map Prod.fst)
    (covered : ∀ child ∈ successors g cursor, child ∈ table.map Prod.fst) :
    TableValid g ((cursor, requiredHeight g table cursor) :: table) := by
  let finished := (cursor, requiredHeight g table cursor) :: table
  have extension := TableExtends.cons table cursor (requiredHeight g table cursor) fresh
  have newHeight : height finished cursor = requiredHeight g table cursor := by
    simp [finished, height, lookup_cons]
  have childCovered : ∀ child ∈ g.children cursor, child ∈ table.map Prod.fst := by
    intro child present
    exact covered child (by simp [successors, present])
  have callbackCovered : ∀ request ∈ g.requests cursor, ∀ reference ∈ request,
      reference ∈ table.map Prod.fst := by
    intro request requested reference present
    apply covered reference
    simp only [successors, List.mem_append, List.mem_flatten]
    exact Or.inr ⟨request, requested, present⟩
  have congrLists (values : List α) (members : ∀ value ∈ values, value ∈ table.map Prod.fst) :
      listHeight (height finished) values = listHeight (height table) values :=
    listHeight_congr _ _ values (fun value present => (extension value (members value present)).2)
  refine ⟨?_, ?_, ?_⟩
  · intro item member
    simp only [List.map_cons, List.mem_cons] at member
    rcases member with equal | member
    · subst item
      rw [newHeight]
      have bounded := requiredHeight_children g table cursor
      omega
    · rw [(extension item member).2]
      exact valid.1 item member
  · intro item member child present
    simp only [List.map_cons, List.mem_cons] at member
    rcases member with equal | member
    · subst item
      have old := childCovered child present
      refine ⟨(extension child old).1, ?_⟩
      rw [(extension child old).2, newHeight]
      have bounded := requiredHeight_children g table cursor
      have childBound := listHeight_mem (height table) _ child present
      omega
    · obtain ⟨old, bounded⟩ := valid.2.1 item member child present
      refine ⟨(extension child old).1, ?_⟩
      rw [(extension child old).2, (extension item member).2]
      exact bounded
  · intro item member request requested
    simp only [List.map_cons, List.mem_cons] at member
    rcases member with equal | member
    · subst item
      refine ⟨fun reference present => (extension reference (callbackCovered request requested reference present)).1, ?_⟩
      rw [congrLists request (callbackCovered request requested), newHeight]
      exact requiredHeight_callback g table cursor request requested
    · obtain ⟨old, bounded⟩ := valid.2.2 item member request requested
      refine ⟨fun reference present => (extension reference (old reference present)).1, ?_⟩
      rw [congrLists request old, (extension item member).2]
      exact bounded

/-! ## Soundness of checking -/

theorem check?_some_sound {α : Type} [DecidableEq α] (g : Graph α) (table : Table α)
    (certificate : RankCertificate g) (computed : check? g table = some certificate) :
    TableValid g table := by
  unfold check? at computed
  by_cases valid : TableValid g table
  · exact valid
  · rw [dif_neg valid] at computed
    cases computed

theorem check?_of_valid {α : Type} [DecidableEq α] (g : Graph α) (table : Table α)
    (valid : TableValid g table) :
    check? g table = some (certificateOfValid g table valid) := by
  unfold check?
  rw [dif_pos valid]

theorem check?_some_iff_valid {α : Type} [DecidableEq α] (g : Graph α) (table : Table α) :
    (∃ certificate : RankCertificate g, check? g table = some certificate) ↔ TableValid g table := by
  constructor
  · intro ⟨certificate, computed⟩
    exact check?_some_sound g table certificate computed
  · intro valid
    exact ⟨certificateOfValid g table valid, check?_of_valid g table valid⟩

/-- Every certificate returned by `check?` is exactly the table-derived certificate. -/
theorem check?_some_spec {α : Type} [DecidableEq α] (g : Graph α) (table : Table α)
    (certificate : RankCertificate g) (computed : check? g table = some certificate) :
    certificate.vertices = table.map Prod.fst ∧ certificate.height = height table := by
  unfold check? at computed
  by_cases valid : TableValid g table
  · rw [dif_pos valid] at computed
    injection computed with inj
    subst certificate
    exact ⟨rfl, rfl⟩
  · rw [dif_neg valid] at computed
    cases computed

/-! ## Soundness of plans -/

/-- Every edge checked by a rank certificate stays in its vertices and strictly decreases rank.
Callback requests include their extra frame step in the stronger stored inequality. -/
theorem RankCertificate.edge_decreases {α : Type} {g : Graph α}
    (certificate : RankCertificate g) (parent child : α)
    (present : parent ∈ certificate.vertices) (edge : Edge g parent child) :
    child ∈ certificate.vertices ∧ certificate.height child < certificate.height parent := by
  change child ∈ g.children parent ++ (g.requests parent).flatten at edge
  rcases List.mem_append.mp edge with childEdge | callbackEdge
  · obtain ⟨covered, bounded⟩ := certificate.children parent present child childEdge
    exact ⟨covered, by omega⟩
  · obtain ⟨request, requested, reference⟩ := List.mem_flatten.mp callbackEdge
    obtain ⟨covered, bounded⟩ := certificate.callbacks parent present request requested
    have belowMax := listHeight_mem certificate.height request child reference
    exact ⟨covered child reference, by omega⟩

theorem RankCertificate.path_closed {α : Type} {g : Graph α} (certificate : RankCertificate g)
    {parent child : α} (present : parent ∈ certificate.vertices)
    (path : Relation.ReflTransGen (Edge g) parent child) :
    child ∈ certificate.vertices := by
  induction path with
  | refl => exact present
  | tail _ edge ih => exact (certificate.edge_decreases _ _ ih edge).1

theorem RankCertificate.path_decreases {α : Type} {g : Graph α} (certificate : RankCertificate g)
    {parent child : α} (present : parent ∈ certificate.vertices)
    (path : Relation.TransGen (Edge g) parent child) :
    child ∈ certificate.vertices ∧ certificate.height child < certificate.height parent := by
  induction path with
  | single edge => exact certificate.edge_decreases _ _ present edge
  | tail _ edge ih =>
    obtain ⟨covered, smaller⟩ := certificate.edge_decreases _ _ ih.1 edge
    exact ⟨covered, Nat.lt_trans smaller ih.2⟩

/-- The certificate is sufficient to rule out all cycles reachable from the requested roots. -/
theorem Plan.acyclic {α : Type} {g : Graph α} {roots : List α} (plan : Plan g roots) :
    Acyclic g roots := by
  intro cursor reachable cycle
  obtain ⟨root, rootMember, path⟩ := reachable
  have present := plan.ranks.path_closed (plan.covers root rootMember) path
  exact Nat.lt_irrefl _ (plan.ranks.path_decreases present cycle).2

/-- The computed bound is at least the rank of every requested root. -/
theorem Plan.bound_mem {α : Type} {g : Graph α} {roots : List α} (plan : Plan g roots) :
    ∀ root ∈ roots, plan.ranks.height root ≤ plan.bound := by
  intro root member
  exact Nat.le_trans (listHeight_mem plan.ranks.height roots root member) (Nat.le_succ _)

end TetraStereo.Certificate.WeightedDemand
