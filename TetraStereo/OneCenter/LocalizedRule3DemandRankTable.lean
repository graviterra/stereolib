import TetraStereo.OneCenter.LocalizedRule3DemandRankProducer

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

theorem rule3DemandTableLookup_cons {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (table : input.Rule3DemandRankTable fuel) (first cursor : input.LocalizedRerootCursor fuel) (rank : Nat) :
    rule3DemandTableLookup ((first, rank) :: table) cursor =
      if first = cursor then some rank else rule3DemandTableLookup table cursor := by
  by_cases same : first = cursor <;> simp [rule3DemandTableLookup, same]

theorem rule3DemandTableLookup_isSome_iff {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (table : input.Rule3DemandRankTable fuel) (cursor : input.LocalizedRerootCursor fuel) :
    (rule3DemandTableLookup table cursor).isSome = true ↔ cursor ∈ table.map Prod.fst := by
  induction table with
  | nil => simp [rule3DemandTableLookup]
  | cons entry rest ih =>
    rcases entry with ⟨first, rank⟩
    rw [rule3DemandTableLookup_cons]
    by_cases same : first = cursor
    · subst first; simp
    · simp [same, ih, Ne.symm same]

/-- Completed entries keep both their identity and their first-match rank when new work is added. -/
def Rule3DemandTableExtends {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (before after : input.Rule3DemandRankTable fuel) : Prop :=
  ∀ cursor ∈ before.map Prod.fst,
    cursor ∈ after.map Prod.fst ∧ rule3DemandTableHeight after cursor = rule3DemandTableHeight before cursor

theorem Rule3DemandTableExtends.refl {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (table : input.Rule3DemandRankTable fuel) : Rule3DemandTableExtends table table :=
  fun _ present => ⟨present, rfl⟩

theorem Rule3DemandTableExtends.trans {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {first second third : input.Rule3DemandRankTable fuel}
    (left : Rule3DemandTableExtends first second) (right : Rule3DemandTableExtends second third) :
    Rule3DemandTableExtends first third := by
  intro cursor present
  obtain ⟨middle, height⟩ := left cursor present
  obtain ⟨last, next⟩ := right cursor middle
  exact ⟨last, next.trans height⟩

theorem rule3DemandTableExtends_cons {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (table : input.Rule3DemandRankTable fuel) (cursor : input.LocalizedRerootCursor fuel) (rank : Nat)
    (fresh : cursor ∉ table.map Prod.fst) : Rule3DemandTableExtends table ((cursor, rank) :: table) := by
  intro old present
  have different : cursor ≠ old := by rintro rfl; exact fresh present
  refine ⟨by simp [present], ?_⟩
  simp [rule3DemandTableHeight, rule3DemandTableLookup_cons, different]

theorem rule3CursorListHeight_congr {α : Type} (left right : α → Nat) (values : List α)
    (agree : ∀ value ∈ values, left value = right value) :
    rule3CursorListHeight left values = rule3CursorListHeight right values := by
  induction values with
  | nil => rfl
  | cons first rest ih =>
    simp only [rule3CursorListHeight, agree first (by simp),
      ih (fun value present => agree value (by simp [present]))]

private theorem maxFold_ge_start {α : Type} (value : α → Nat) (items : List α) (start : Nat) :
    start ≤ items.foldl (fun bound item => max bound (value item)) start := by
  induction items generalizing start with
  | nil => exact Nat.le_refl _
  | cons first rest ih => exact (Nat.le_max_left _ _).trans (ih _)

private theorem maxFold_ge_member {α : Type} (value : α → Nat) (items : List α) (start : Nat)
    (item : α) (present : item ∈ items) :
    value item ≤ items.foldl (fun bound item => max bound (value item)) start := by
  induction items generalizing start with
  | nil => simp at present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact (Nat.le_max_right _ _).trans (maxFold_ge_start value rest _)
    · exact ih _ present

theorem rule3DemandRequiredHeight_children (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (table : input.Rule3DemandRankTable fuel) (cursor : input.LocalizedRerootCursor fuel) :
    rule3CursorListHeight (rule3DemandTableHeight table) (input.executableLocalizedRerootChildren cursor) + 1 ≤
      input.rule3DemandRequiredHeight table cursor :=
  maxFold_ge_start _ _ _

theorem rule3DemandRequiredHeight_callback (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (table : input.Rule3DemandRankTable fuel) (cursor : input.LocalizedRerootCursor fuel)
    (request : List (input.LocalizedRerootCursor fuel))
    (present : request ∈ input.rule3NodeCallbackRequests cursor.occurrence) :
    rule3CursorListHeight (rule3DemandTableHeight table) request + 2 ≤
      input.rule3DemandRequiredHeight table cursor :=
  maxFold_ge_member (fun request => rule3CursorListHeight (rule3DemandTableHeight table) request + 2)
    _ _ request present

/-- A completed dependency set permits one fresh vertex to be added without invalidating any
previous rank. This is the invariant maintained by molecular postorder discovery. -/
theorem rule3DemandRankTableValid_cons (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (table : input.Rule3DemandRankTable fuel) (valid : input.Rule3DemandRankTableValid table)
    (cursor : input.LocalizedRerootCursor fuel) (fresh : cursor ∉ table.map Prod.fst)
    (covered : ∀ child ∈ input.rule3DemandSuccessors cursor, child ∈ table.map Prod.fst) :
    input.Rule3DemandRankTableValid ((cursor, input.rule3DemandRequiredHeight table cursor) :: table) := by
  let finished := (cursor, input.rule3DemandRequiredHeight table cursor) :: table
  have extension := rule3DemandTableExtends_cons table cursor (input.rule3DemandRequiredHeight table cursor) fresh
  have newHeight : rule3DemandTableHeight finished cursor = input.rule3DemandRequiredHeight table cursor := by
    simp [finished, rule3DemandTableHeight, rule3DemandTableLookup_cons]
  have childCovered : ∀ child ∈ input.executableLocalizedRerootChildren cursor, child ∈ table.map Prod.fst := by
    intro child present
    exact covered child (by simp [rule3DemandSuccessors, present])
  have callbackCovered : ∀ request ∈ input.rule3NodeCallbackRequests cursor.occurrence,
      ∀ reference ∈ request, reference ∈ table.map Prod.fst := by
    intro request requested reference present
    apply covered reference
    simp only [rule3DemandSuccessors, List.mem_append, List.mem_flatten]
    exact Or.inr ⟨request, requested, present⟩
  have congrLists (values : List (input.LocalizedRerootCursor fuel))
      (members : ∀ value ∈ values, value ∈ table.map Prod.fst) :
      rule3CursorListHeight (rule3DemandTableHeight finished) values =
        rule3CursorListHeight (rule3DemandTableHeight table) values :=
    rule3CursorListHeight_congr _ _ values (fun value present => (extension value (members value present)).2)
  refine ⟨?_, ?_, ?_⟩
  · intro item member
    simp only [List.map_cons, List.mem_cons] at member
    rcases member with equal | member
    · subst item
      rw [newHeight]
      have bounded := input.rule3DemandRequiredHeight_children table cursor
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
      have bounded := input.rule3DemandRequiredHeight_children table cursor
      have childBound := rule3CursorListHeight_mem (rule3DemandTableHeight table) _ child present
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
      exact input.rule3DemandRequiredHeight_callback table cursor request requested
    · obtain ⟨old, bounded⟩ := valid.2.2 item member request requested
      refine ⟨fun reference present => (extension reference (old reference present)).1, ?_⟩
      rw [congrLists request old, (extension item member).2]
      exact bounded

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
