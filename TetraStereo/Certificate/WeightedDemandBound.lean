import TetraStereo.Certificate.WeightedDemandTotality

set_option autoImplicit false





































namespace TetraStereo.Certificate.WeightedDemand

/-! ## Elementary list and required-height bounds -/

/-- The maximum of `h` over a list is bounded by any pointwise bound. -/
theorem listHeight_le {α : Type} (h : α → Nat) {values : List α} {bound : Nat}
    (bounded : ∀ value ∈ values, h value ≤ bound) :
    listHeight h values ≤ bound := by
  induction values with
  | nil => simp [listHeight]
  | cons first rest ih =>
      simp only [listHeight]
      exact max_le (bounded first (by simp))
        (ih (fun value present => bounded value (by simp [present])))

/-- Folding `max` from a bounded start over pointwise bounded values stays bounded. -/
theorem foldl_max_le {α : Type} (value : α → Nat) (items : List α) (start bound : Nat)
    (startBound : start ≤ bound)
    (members : ∀ item ∈ items, value item ≤ bound) :
    items.foldl (fun acc item => max acc (value item)) start ≤ bound := by
  induction items generalizing start with
  | nil => simpa using startBound
  | cons first rest ih =>
      exact ih (start := max start (value first))
        (max_le startBound (members first (by simp)))
        (fun item present => members item (by simp [present]))

/-- If every successor of `cursor` already has height at most `bound`, then the rank required for
`cursor` is at most `bound + 2`: a child contributes at most `+1` and a callback request at most
`+2` (an empty request still contributes `2`, since `listHeight` of `[]` is `0`). -/
theorem requiredHeight_le {α : Type} [DecidableEq α] (g : Graph α) (table : Table α)
    (cursor : α) {bound : Nat}
    (successorsBounded : ∀ child ∈ successors g cursor, height table child ≤ bound) :
    requiredHeight g table cursor ≤ bound + 2 := by
  have childrenBounded : listHeight (height table) (g.children cursor) ≤ bound :=
    listHeight_le _ (fun child present => successorsBounded child (by simp [successors, present]))
  have callbacksBounded : ∀ request ∈ g.requests cursor,
      listHeight (height table) request + 2 ≤ bound + 2 := by
    intro request present
    have requestBounded : listHeight (height table) request ≤ bound :=
      listHeight_le _ (fun reference refPresent =>
        successorsBounded reference (by
          simp only [successors, List.mem_append, List.mem_flatten]
          exact Or.inr ⟨request, present, refPresent⟩))
    omega
  unfold requiredHeight
  exact foldl_max_le _ _ _ _ (by omega) callbacksBounded

/-- Prepending an entry with a different key does not change the first-match height of a cursor. -/
theorem height_cons_ne {α : Type} [DecidableEq α] (table : Table α) (first cursor : α)
    (rank : Nat) (different : first ≠ cursor) :
    height ((first, rank) :: table) cursor = height table cursor := by
  simp [height, lookup_cons, different]

/-- A fresh head preserves every old height, with the freshness only required on the old keys
themselves.  The weaker `TableExtends.cons` hypothesis is not needed here: an old key can never
coincide with the new head key. -/
theorem TableExtends.cons_of_old {α : Type} [DecidableEq α] {before middle : Table α}
    (extension : TableExtends before middle) (cursor : α) (rank : Nat)
    (different : ∀ old ∈ before.map Prod.fst, old ≠ cursor) :
    TableExtends before ((cursor, rank) :: middle) := by
  intro old present
  obtain ⟨middlePresent, middleHeight⟩ := extension old present
  have ne : cursor ≠ old := fun same => different old present same.symm
  refine ⟨by simp [middlePresent], ?_⟩
  rw [height_cons_ne middle cursor old rank ne, middleHeight]

/-! ## Folding helpers

Discovery threads a table through a `foldlM`.  Each helper below states that a per-step property
composes through the fold.  They are stated for an arbitrary `step`, so the same proof is reused
for the `budget`-indexed induction step of `discover`.
-/

/-- `TableExtends` composes through a `foldlM`. -/
theorem fold_extends {α : Type} [DecidableEq α]
    (step : Table α → α → Except (DiscoveryFailure α) (Table α))
    (items : List α) (table finished : Table α)
    (stepExtends : ∀ (before : Table α) (item : α) (after : Table α),
      step before item = .ok after → TableExtends before after)
    (computed : items.foldlM step table = .ok finished) :
    TableExtends table finished := by
  induction items generalizing table with
  | nil =>
      simp only [List.foldlM_nil] at computed
      change Except.ok table = Except.ok finished at computed
      injection computed with heq
      rw [← heq]
      exact TableExtends.refl table
  | cons first rest ih =>
      cases hstep : step table first with
      | error error => simp [List.foldlM_cons, hstep, bind, Except.bind] at computed
      | ok middle =>
          have restComputed : rest.foldlM step middle = .ok finished := by
            simpa [hstep] using computed
          exact TableExtends.trans (stepExtends table first middle hstep) (ih middle restComputed)

/-- Absence of a fixed cursor is preserved through a `foldlM`. -/
theorem fold_fresh {α : Type} [DecidableEq α]
    (step : Table α → α → Except (DiscoveryFailure α) (Table α))
    (items : List α) (root : α) (table finished : Table α)
    (stepFresh : ∀ (before : Table α) (item : α) (after : Table α),
      step before item = .ok after →
      root ∉ before.map Prod.fst → root ∉ after.map Prod.fst)
    (computed : items.foldlM step table = .ok finished)
    (fresh : root ∉ table.map Prod.fst) :
    root ∉ finished.map Prod.fst := by
  induction items generalizing table with
  | nil =>
      simp only [List.foldlM_nil] at computed
      change Except.ok table = Except.ok finished at computed
      injection computed with heq
      rw [← heq]
      exact fresh
  | cons first rest ih =>
      cases hstep : step table first with
      | error error => simp [List.foldlM_cons, hstep, bind, Except.bind] at computed
      | ok middle =>
          have restComputed : rest.foldlM step middle = .ok finished := by
            simpa [hstep] using computed
          exact ih middle restComputed (stepFresh table first middle hstep fresh)

/-- `List.Nodup` of the key list is preserved through a `foldlM`. -/
theorem fold_nodup {α : Type} [DecidableEq α]
    (step : Table α → α → Except (DiscoveryFailure α) (Table α))
    (items : List α) (table finished : Table α)
    (stepNodup : ∀ (before : Table α) (item : α) (after : Table α),
      step before item = .ok after →
      (before.map Prod.fst).Nodup → (after.map Prod.fst).Nodup)
    (computed : items.foldlM step table = .ok finished)
    (nodup : (table.map Prod.fst).Nodup) :
    (finished.map Prod.fst).Nodup := by
  induction items generalizing table with
  | nil =>
      simp only [List.foldlM_nil] at computed
      change Except.ok table = Except.ok finished at computed
      injection computed with heq
      rw [← heq]
      exact nodup
  | cons first rest ih =>
      cases hstep : step table first with
      | error error => simp [List.foldlM_cons, hstep, bind, Except.bind] at computed
      | ok middle =>
          have restComputed : rest.foldlM step middle = .ok finished := by
            simpa [hstep] using computed
          exact ih middle restComputed (stepNodup table first middle hstep nodup)

/-! ## Structural facts about successful discovery -/

/-- A successful discovery returns a table in which the requested cursor occurs. -/
theorem discover_mem {α : Type} [DecidableEq α] (g : Graph α) :
    ∀ (budget : Nat) (active : List α) (table : Table α) (cursor : α) (finished : Table α),
      discover g budget active table cursor = .ok finished →
      cursor ∈ finished.map Prod.fst := by
  intro budget
  induction budget with
  | zero =>
      intro active table cursor finished computed
      by_cases known : (lookup table cursor).isSome = true
      · have eq : discover g 0 active table cursor = .ok table := by simp [discover, known]
        rw [eq] at computed
        injection computed with heq
        rw [← heq]
        exact (lookup_isSome_iff table cursor).mp known
      · have eq : discover g 0 active table cursor = .error .traversalLimit := by
          simp [discover, known]
        rw [eq] at computed
        cases computed
  | succ budget ih =>
      intro active table cursor finished computed
      by_cases known : (lookup table cursor).isSome = true
      · have eq : discover g (budget + 1) active table cursor = .ok table := by
          simp [discover, known]
        rw [eq] at computed
        injection computed with heq
        rw [← heq]
        exact (lookup_isSome_iff table cursor).mp known
      · by_cases member : cursor ∈ active
        · have eq : discover g (budget + 1) active table cursor = .error (.cycle cursor) := by
            simp [discover, known, member]
          rw [eq] at computed
          cases computed
        · cases hfold : (successors g cursor).foldlM
              (fun known child => discover g budget (cursor :: active) known child) table with
          | error error =>
              have eq : discover g (budget + 1) active table cursor = .error error := by
                simp [discover, known, member, hfold, bind, Except.bind]
              rw [eq] at computed
              cases computed
          | ok middle =>
              have resultEq : discover g (budget + 1) active table cursor =
                  .ok ((cursor, requiredHeight g middle cursor) :: middle) := by
                simp [discover, known, member, hfold, bind, Except.bind]
                rfl
              rw [resultEq] at computed
              injection computed with heq
              rw [← heq]
              simp

/-- A successful discovery never removes or rewrites an existing entry; it only prepends fresh
entries. -/
theorem discover_extends {α : Type} [DecidableEq α] (g : Graph α) :
    ∀ (budget : Nat) (active : List α) (table : Table α) (cursor : α) (finished : Table α),
      discover g budget active table cursor = .ok finished → TableExtends table finished := by
  intro budget
  induction budget with
  | zero =>
      intro active table cursor finished computed
      by_cases known : (lookup table cursor).isSome = true
      · have eq : discover g 0 active table cursor = .ok table := by simp [discover, known]
        rw [eq] at computed
        injection computed with heq
        rw [← heq]
        exact TableExtends.refl table
      · have eq : discover g 0 active table cursor = .error .traversalLimit := by
          simp [discover, known]
        rw [eq] at computed
        cases computed
  | succ budget ih =>
      intro active table cursor finished computed
      by_cases known : (lookup table cursor).isSome = true
      · have eq : discover g (budget + 1) active table cursor = .ok table := by
          simp [discover, known]
        rw [eq] at computed
        injection computed with heq
        rw [← heq]
        exact TableExtends.refl table
      · by_cases member : cursor ∈ active
        · have eq : discover g (budget + 1) active table cursor = .error (.cycle cursor) := by
            simp [discover, known, member]
          rw [eq] at computed
          cases computed
        · cases hfold : (successors g cursor).foldlM
              (fun known child => discover g budget (cursor :: active) known child) table with
          | error error =>
              have eq : discover g (budget + 1) active table cursor = .error error := by
                simp [discover, known, member, hfold, bind, Except.bind]
              rw [eq] at computed
              cases computed
          | ok middle =>
              have foldExtends : TableExtends table middle :=
                fold_extends (fun known child => discover g budget (cursor :: active) known child)
                  (successors g cursor) table middle
                  (fun before item after h => ih (cursor :: active) before item after h) hfold
              have different : ∀ old ∈ table.map Prod.fst, old ≠ cursor := by
                intro old present same
                exact known ((lookup_isSome_iff table cursor).mpr (same ▸ present))
              have resultExtends : TableExtends table
                  ((cursor, requiredHeight g middle cursor) :: middle) :=
                TableExtends.cons_of_old foldExtends cursor (requiredHeight g middle cursor)
                  different
              have resultEq : discover g (budget + 1) active table cursor =
                  .ok ((cursor, requiredHeight g middle cursor) :: middle) := by
                simp [discover, known, member, hfold, bind, Except.bind]
                rfl
              rw [resultEq] at computed
              injection computed with heq
              rw [← heq]
              exact resultExtends

/-- If a cursor is on the active path and absent from the input table, it stays absent from the
output.  This is what rules out duplicate keys when a fold processes several siblings. -/
theorem discover_fresh {α : Type} [DecidableEq α] (g : Graph α) :
    ∀ (budget : Nat) (active : List α) (table : Table α) (cursor : α) (finished : Table α)
      (root : α),
      discover g budget active table cursor = .ok finished →
      root ∈ active → root ∉ table.map Prod.fst → root ∉ finished.map Prod.fst := by
  intro budget
  induction budget with
  | zero =>
      intro active table cursor finished root computed rootActive rootFresh
      by_cases known : (lookup table cursor).isSome = true
      · have eq : discover g 0 active table cursor = .ok table := by simp [discover, known]
        rw [eq] at computed
        injection computed with heq
        rw [← heq]
        exact rootFresh
      · have eq : discover g 0 active table cursor = .error .traversalLimit := by
          simp [discover, known]
        rw [eq] at computed
        cases computed
  | succ budget ih =>
      intro active table cursor finished root computed rootActive rootFresh
      by_cases known : (lookup table cursor).isSome = true
      · have eq : discover g (budget + 1) active table cursor = .ok table := by
          simp [discover, known]
        rw [eq] at computed
        injection computed with heq
        rw [← heq]
        exact rootFresh
      · by_cases member : cursor ∈ active
        · have eq : discover g (budget + 1) active table cursor = .error (.cycle cursor) := by
            simp [discover, known, member]
          rw [eq] at computed
          cases computed
        · cases hfold : (successors g cursor).foldlM
              (fun known child => discover g budget (cursor :: active) known child) table with
          | error error =>
              have eq : discover g (budget + 1) active table cursor = .error error := by
                simp [discover, known, member, hfold, bind, Except.bind]
              rw [eq] at computed
              cases computed
          | ok middle =>
              have middleFresh : root ∉ middle.map Prod.fst :=
                fold_fresh (fun known child => discover g budget (cursor :: active) known child)
                  (successors g cursor) root table middle
                  (fun before item after h fresh =>
                    ih (active := cursor :: active) (table := before) (cursor := item)
                      (finished := after) (root := root) h (by simp [rootActive]) fresh)
                  hfold rootFresh
              have resultEq : discover g (budget + 1) active table cursor =
                  .ok ((cursor, requiredHeight g middle cursor) :: middle) := by
                simp [discover, known, member, hfold, bind, Except.bind]
                rfl
              rw [resultEq] at computed
              injection computed with heq
              rw [← heq]
              intro present
              simp only [List.map_cons, List.mem_cons] at present
              rcases present with same | present
              · exact member (same ▸ rootActive)
              · exact middleFresh present

/-- Successful discovery preserves distinctness of the table keys. -/
theorem discover_nodup {α : Type} [DecidableEq α] (g : Graph α) :
    ∀ (budget : Nat) (active : List α) (table : Table α) (cursor : α) (finished : Table α),
      discover g budget active table cursor = .ok finished →
      (table.map Prod.fst).Nodup → (finished.map Prod.fst).Nodup := by
  intro budget
  induction budget with
  | zero =>
      intro active table cursor finished computed nodup
      by_cases known : (lookup table cursor).isSome = true
      · have eq : discover g 0 active table cursor = .ok table := by simp [discover, known]
        rw [eq] at computed
        injection computed with heq
        rw [← heq]
        exact nodup
      · have eq : discover g 0 active table cursor = .error .traversalLimit := by
          simp [discover, known]
        rw [eq] at computed
        cases computed
  | succ budget ih =>
      intro active table cursor finished computed nodup
      by_cases known : (lookup table cursor).isSome = true
      · have eq : discover g (budget + 1) active table cursor = .ok table := by
          simp [discover, known]
        rw [eq] at computed
        injection computed with heq
        rw [← heq]
        exact nodup
      · by_cases member : cursor ∈ active
        · have eq : discover g (budget + 1) active table cursor = .error (.cycle cursor) := by
            simp [discover, known, member]
          rw [eq] at computed
          cases computed
        · have tableFresh : cursor ∉ table.map Prod.fst := fun present =>
            known ((lookup_isSome_iff table cursor).mpr present)
          cases hfold : (successors g cursor).foldlM
              (fun known child => discover g budget (cursor :: active) known child) table with
          | error error =>
              have eq : discover g (budget + 1) active table cursor = .error error := by
                simp [discover, known, member, hfold, bind, Except.bind]
              rw [eq] at computed
              cases computed
          | ok middle =>
              have middleNodup : (middle.map Prod.fst).Nodup :=
                fold_nodup (fun known child => discover g budget (cursor :: active) known child)
                  (successors g cursor) table middle
                  (fun before item after h beforeNodup =>
                    ih (cursor :: active) before item after h beforeNodup)
                  hfold nodup
              have cursorFreshMiddle : cursor ∉ middle.map Prod.fst :=
                fold_fresh (fun known child => discover g budget (cursor :: active) known child)
                  (successors g cursor) cursor table middle
                  (fun before item after h fresh =>
                    discover_fresh g budget (cursor :: active) before item after cursor h
                      (by simp) fresh)
                  hfold tableFresh
              have resultEq : discover g (budget + 1) active table cursor =
                  .ok ((cursor, requiredHeight g middle cursor) :: middle) := by
                simp [discover, known, member, hfold, bind, Except.bind]
                rfl
              rw [resultEq] at computed
              injection computed with heq
              rw [← heq]
              simp only [List.map_cons]
              exact List.Nodup.cons cursorFreshMiddle middleNodup

/-! ## Height bound through a fold -/

/-- Folding successful `discover` calls at a fixed budget increases the maximum table height by at
most twice the number of newly inserted entries.  Every processed item remains in the final key
list, which is needed to bound `requiredHeight` of the enclosing cursor. -/
theorem fold_discover_height_bound {α : Type} [DecidableEq α] (g : Graph α)
    (budget : Nat) (active : List α) (items : List α) (table finished : Table α)
    (stepHeight : ∀ (before : Table α) (item : α) (after : Table α),
      discover g budget active before item = .ok after →
      before.length ≤ after.length ∧
      ∀ base, (∀ x ∈ before.map Prod.fst, height before x ≤ base) →
        ∀ x ∈ after.map Prod.fst,
          height after x ≤ base + 2 * (after.length - before.length))
    (stepExtends : ∀ (before : Table α) (item : α) (after : Table α),
      discover g budget active before item = .ok after → TableExtends before after)
    (stepMem : ∀ (before : Table α) (item : α) (after : Table α),
      discover g budget active before item = .ok after → item ∈ after.map Prod.fst)
    (computed : items.foldlM (fun known item => discover g budget active known item) table =
      .ok finished) :
    (∀ item ∈ items, item ∈ finished.map Prod.fst) ∧
    table.length ≤ finished.length ∧
    ∀ base, (∀ x ∈ table.map Prod.fst, height table x ≤ base) →
      ∀ x ∈ finished.map Prod.fst,
        height finished x ≤ base + 2 * (finished.length - table.length) := by
  induction items generalizing table with
  | nil =>
      simp only [List.foldlM_nil] at computed
      change Except.ok table = Except.ok finished at computed
      injection computed with heq
      rw [← heq]
      refine ⟨by simp, le_rfl, ?_⟩
      intro base bounded x present
      simpa using bounded x present
  | cons first rest ih =>
      cases hstep : discover g budget active table first with
      | error error => simp [List.foldlM_cons, hstep, bind, Except.bind] at computed
      | ok middle =>
          have restComputed : rest.foldlM
              (fun known item => discover g budget active known item) middle = .ok finished := by
            simpa [hstep] using computed
          obtain ⟨tableLeMiddle, heightMiddle⟩ := stepHeight table first middle hstep
          have firstMem : first ∈ middle.map Prod.fst := stepMem table first middle hstep
          have extendsMiddle : TableExtends table middle := stepExtends table first middle hstep
          obtain ⟨restCovered, middleLeFinished, heightFinished⟩ := ih middle restComputed
          have extendsFinished : TableExtends middle finished :=
            fold_extends (fun known item => discover g budget active known item)
              rest middle finished (fun before item after h => stepExtends before item after h)
              restComputed
          refine ⟨?_, le_trans tableLeMiddle middleLeFinished, ?_⟩
          · intro item present
            rcases List.mem_cons.mp present with same | present
            · rw [same]
              exact (extendsFinished first firstMem).1
            · exact restCovered item present
          · intro base bounded x present
            have middleBounded : ∀ y ∈ middle.map Prod.fst,
                height middle y ≤ base + 2 * (middle.length - table.length) :=
              heightMiddle base bounded
            have bound := heightFinished (base + 2 * (middle.length - table.length))
              middleBounded x present
            omega

/-! ## The main discover bound -/

/-- **Main quantitative discovery theorem.**  Any successful `discover` call inserts exactly
`finished.length - table.length` fresh entries, and every height in its output table is at most
`base + 2 * (finished.length - table.length)` whenever `base` bounds the input table heights.

No acyclicity, no budget side condition and no assumption about the produced heights is used. -/
theorem discover_height_bound {α : Type} [DecidableEq α] (g : Graph α) :
    ∀ (budget : Nat) (active : List α) (table : Table α) (cursor : α) (finished : Table α),
      discover g budget active table cursor = .ok finished →
      table.length ≤ finished.length ∧
      ∀ base, (∀ item ∈ table.map Prod.fst, height table item ≤ base) →
        ∀ item ∈ finished.map Prod.fst,
          height finished item ≤ base + 2 * (finished.length - table.length) := by
  intro budget
  induction budget with
  | zero =>
      intro active table cursor finished computed
      by_cases known : (lookup table cursor).isSome = true
      · have eq : discover g 0 active table cursor = .ok table := by simp [discover, known]
        rw [eq] at computed
        injection computed with heq
        rw [← heq]
        refine ⟨le_rfl, ?_⟩
        intro base bounded item present
        simpa using bounded item present
      · have eq : discover g 0 active table cursor = .error .traversalLimit := by
          simp [discover, known]
        rw [eq] at computed
        cases computed
  | succ budget ih =>
      intro active table cursor finished computed
      by_cases known : (lookup table cursor).isSome = true
      · have eq : discover g (budget + 1) active table cursor = .ok table := by
          simp [discover, known]
        rw [eq] at computed
        injection computed with heq
        rw [← heq]
        refine ⟨le_rfl, ?_⟩
        intro base bounded item present
        simpa using bounded item present
      · by_cases member : cursor ∈ active
        · have eq : discover g (budget + 1) active table cursor = .error (.cycle cursor) := by
            simp [discover, known, member]
          rw [eq] at computed
          cases computed
        · cases hfold : (successors g cursor).foldlM
              (fun known child => discover g budget (cursor :: active) known child) table with
          | error error =>
              have eq : discover g (budget + 1) active table cursor = .error error := by
                simp [discover, known, member, hfold, bind, Except.bind]
              rw [eq] at computed
              cases computed
          | ok middle =>
              have resultEq : discover g (budget + 1) active table cursor =
                  .ok ((cursor, requiredHeight g middle cursor) :: middle) := by
                simp [discover, known, member, hfold, bind, Except.bind]
                rfl
              rw [resultEq] at computed
              injection computed with heq
              rw [← heq]
              obtain ⟨successorsCovered, tableLeMiddle, heightMiddle⟩ :=
                fold_discover_height_bound g budget (cursor :: active) (successors g cursor) table
                  middle
                  (fun before item after h => ih (cursor :: active) before item after h)
                  (fun before item after h =>
                    discover_extends g budget (cursor :: active) before item after h)
                  (fun before item after h =>
                    discover_mem g budget (cursor :: active) before item after h)
                  hfold
              refine ⟨?_, ?_⟩
              · simp only [List.length_cons]
                omega
              · intro base bounded item present
                have middleBounded : ∀ child ∈ successors g cursor,
                    height middle child ≤ base + 2 * (middle.length - table.length) :=
                  fun child childMem =>
                    heightMiddle base bounded child (successorsCovered child childMem)
                have requiredBounded : requiredHeight g middle cursor ≤
                    base + 2 * (middle.length - table.length) + 2 :=
                  requiredHeight_le g middle cursor middleBounded
                have itemBounded : ∀ y ∈ middle.map Prod.fst,
                    height middle y ≤ base + 2 * (middle.length - table.length) :=
                  heightMiddle base bounded
                simp only [List.map_cons, List.mem_cons] at present
                by_cases same : item = cursor
                · subst item
                  have head : height ((cursor, requiredHeight g middle cursor) :: middle) cursor =
                      requiredHeight g middle cursor := by simp [height, lookup_cons]
                  rw [head]
                  simp only [List.length_cons]
                  omega
                · rcases present with equal | present
                  · exact absurd equal same
                  · have ne : cursor ≠ item := fun h => same h.symm
                    have unchanged : height ((cursor, requiredHeight g middle cursor) :: middle)
                        item = height middle item := height_cons_ne middle cursor item _ ne
                    rw [unchanged]
                    have bound := itemBounded item present
                    simp only [List.length_cons]
                    omega

/-! ## Corollaries: budget, finite cardinality and `prepare` -/

/-- Whenever the number of fresh insertions is at most the traversal budget, the bound takes the
simple budget shape `base + 2 * budget`.  The insertion-count side condition is essential; it is
discharged by cardinality in `prepare_bound_of_ok` below. -/
theorem discover_height_bound_budget {α : Type} [DecidableEq α] (g : Graph α)
    (budget : Nat) (active : List α) (table : Table α) (cursor : α) (finished : Table α)
    (computed : discover g budget active table cursor = .ok finished)
    (base : Nat)
    (bounded : ∀ item ∈ table.map Prod.fst, height table item ≤ base)
    (inserted : finished.length - table.length ≤ budget) :
    ∀ item ∈ finished.map Prod.fst, height finished item ≤ base + 2 * budget := by
  have main := (discover_height_bound g budget active table cursor finished computed).2 base bounded
  intro item present
  have bound := main item present
  omega

/-- For a finite vertex type and a table with distinct keys, a successful call inserts at most
`Fintype.card α` entries, so the output heights are at most `base + 2 * Fintype.card α`. -/
theorem discover_height_bound_of_nodup {α : Type} [Fintype α] [DecidableEq α] (g : Graph α)
    (budget : Nat) (active : List α) (table : Table α) (cursor : α) (finished : Table α)
    (computed : discover g budget active table cursor = .ok finished)
    (base : Nat)
    (bounded : ∀ item ∈ table.map Prod.fst, height table item ≤ base)
    (nodup : (table.map Prod.fst).Nodup) :
    ∀ item ∈ finished.map Prod.fst, height finished item ≤ base + 2 * Fintype.card α := by
  have main := (discover_height_bound g budget active table cursor finished computed).2 base bounded
  have finishedNodup := discover_nodup g budget active table cursor finished computed nodup
  have lengthBound : finished.length ≤ Fintype.card α := by
    simpa using List.Nodup.length_le_card finishedNodup
  intro item present
  have bound := main item present
  omega








theorem prepare_bound_of_ok {α : Type} [Fintype α] [DecidableEq α] (g : Graph α)
    (roots : List α) (plan : Plan g roots)
    (computed : prepare g (Fintype.card α + 1) roots = .ok plan) :
    plan.bound ≤ 2 * Fintype.card α + 1 := by
  cases hfold : roots.foldlM
      (fun known root => discover g (Fintype.card α + 1) [] known root) [] with
  | error error =>
      have impossible : prepare g (Fintype.card α + 1) roots = .error error := by
        simp [prepare, hfold, bind, Except.bind]
      rw [impossible] at computed
      cases computed
  | ok table =>
      cases hcheck : check? g table with
      | none =>
          have impossible : prepare g (Fintype.card α + 1) roots = .error .invalidRanks := by
            simp [prepare, hfold, hcheck, bind, Except.bind]
          rw [impossible] at computed
          cases computed
      | some ranks =>
          by_cases covers : ∀ root ∈ roots, root ∈ ranks.vertices
          · have success : prepare g (Fintype.card α + 1) roots =
                .ok { ranks := ranks, covers := covers } := by
              simp only [prepare, hfold, hcheck, bind, Except.bind]
              rw [dif_pos covers]
            rw [success] at computed
            injection computed with heq
            rw [← heq]
            obtain ⟨verticesEq, heightEq⟩ := check?_some_spec g table ranks hcheck
            obtain ⟨rootsCovered, _, heightBound⟩ :=
              fold_discover_height_bound g (Fintype.card α + 1) [] roots [] table
                (fun before item after h =>
                  discover_height_bound g (Fintype.card α + 1) [] before item after h)
                (fun before item after h =>
                  discover_extends g (Fintype.card α + 1) [] before item after h)
                (fun before item after h =>
                  discover_mem g (Fintype.card α + 1) [] before item after h)
                hfold
            have tableNodup : (table.map Prod.fst).Nodup :=
              fold_nodup (fun known root => discover g (Fintype.card α + 1) [] known root)
                roots [] table
                (fun before item after h nodup =>
                  discover_nodup g (Fintype.card α + 1) [] before item after h nodup)
                hfold (by simp)
            have tableLength : table.length ≤ Fintype.card α := by
              have := List.Nodup.length_le_card tableNodup
              simpa using this
            have rootsHeight : ∀ root ∈ roots, height table root ≤ 2 * Fintype.card α := by
              intro root rootMem
              have keyMem : root ∈ table.map Prod.fst := by
                rw [← verticesEq]
                exact covers root rootMem
              have bound := heightBound 0 (by simp) root keyMem
              simp only [List.length_nil, Nat.sub_zero, Nat.zero_add] at bound
              omega
            have listBound : listHeight (height table) roots ≤ 2 * Fintype.card α :=
              listHeight_le _ (fun root rootMem => rootsHeight root rootMem)
            show listHeight ranks.height roots + 1 ≤ 2 * Fintype.card α + 1
            rw [heightEq]
            omega
          · have impossible : prepare g (Fintype.card α + 1) roots = .error .missingRoot := by
              simp only [prepare, hfold, hcheck, bind, Except.bind]
              rw [dif_neg covers]
            rw [impossible] at computed
            cases computed



theorem prepare_bound_of_success {α : Type} [Fintype α] [DecidableEq α] (g : Graph α)
    (roots : List α)
    (success : ∃ plan : Plan g roots, prepare g (Fintype.card α + 1) roots = .ok plan) :
    ∃ plan : Plan g roots, prepare g (Fintype.card α + 1) roots = .ok plan ∧
      plan.bound ≤ 2 * (Fintype.card α + 1) := by
  obtain ⟨plan, computed⟩ := success
  refine ⟨plan, computed, ?_⟩
  have := prepare_bound_of_ok g roots plan computed
  omega




theorem exists_bounded_plan_of_acyclic {α : Type} [Fintype α] [DecidableEq α] (g : Graph α)
    (roots : List α) (acyclic : Acyclic g roots) :
    ∃ plan : Plan g roots, prepare g (Fintype.card α + 1) roots = .ok plan ∧
      plan.bound ≤ 2 * (Fintype.card α + 1) := by
  obtain ⟨plan, computed⟩ := prepare_total_of_acyclic g roots acyclic
  exact ⟨plan, computed, by
    have := prepare_bound_of_ok g roots plan computed
    omega⟩

end TetraStereo.Certificate.WeightedDemand
