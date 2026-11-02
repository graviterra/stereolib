import TetraStereo.OneCenter.LocalizedExtendedDemandGraph
import TetraStereo.Certificate.WeightedDemandGraph

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput


















































/-! ## The weighted extended demand certificate -/

/-- A finite closed portion of the actual extended computation graph, weighted exactly like the
evaluator.  Child edges consume one fuel step; node-to-frame-to-key request edges consume two.
No successful callback or geometry is assumed. -/
structure ExtendedRule3DemandRankCertificate (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  vertices : List (input.LocalizedRerootCursor fuel)
  height : input.LocalizedRerootCursor fuel → Nat
  positive : ∀ cursor ∈ vertices, 0 < height cursor
  children : ∀ cursor ∈ vertices, ∀ child ∈ input.executableLocalizedRerootChildren cursor,
    child ∈ vertices ∧ height child + 1 ≤ height cursor
  callbacks : ∀ cursor ∈ vertices, ∀ request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence,
    (∀ reference ∈ request, reference ∈ vertices) ∧
      rule3CursorListHeight height request + 2 ≤ height cursor

private theorem extendedDemandMapM_congr_on {α β : Type} (before after : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, before value = after value) →
      values.mapM before = values.mapM after
  | [], _ => rfl
  | value :: values, agree => by
    have head := agree value (by simp)
    have tail := extendedDemandMapM_congr_on before after values
      (fun value present => agree value (by simp [present]))
    simp [head, tail]

/-- A checked weighted extended rank stabilizes the complete recursive key result at every larger
budget.  The induction crosses real endpoint callbacks as well as ordinary child traversal, and
uses the extended demand locality theorem at every node, with the *same* auxiliary view and all
physical exclusions preserved. -/
theorem ExtendedRule3DemandRankCertificate.key_stable
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.ExtendedRule3DemandRankCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) (member : cursor ∈ certificate.vertices)
    (first second : Nat) (firstEnough : certificate.height cursor ≤ first)
    (secondEnough : certificate.height cursor ≤ second)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view first excluded cursor =
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view second excluded cursor := by
  generalize rankEq : certificate.height cursor = rank at firstEnough secondEnough
  induction rank using Nat.strong_induction_on generalizing cursor first second excluded with
  | h rank ih =>
    have positive := certificate.positive cursor member
    cases first with
    | zero => omega
    | succ first =>
      cases second with
      | zero => omega
      | succ second =>
        have callbackEq : input.Rule3CallbackAgreesOn
            (input.rule3ExtendedNodeCallbackRequests cursor.occurrence)
            (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view first)
            (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view second) := by
          intro request requested
          obtain ⟨covered, bounded⟩ := certificate.callbacks cursor member request requested
          cases first with
          | zero => omega
          | succ first =>
            cases second with
            | zero => omega
            | succ second =>
              apply input.extendedRule3Frame_succ_congr_keys target view first second request
              intro cancelled reference present
              have heightBound := rule3CursorListHeight_mem certificate.height request reference present
              apply ih (certificate.height reference) (by omega) reference (covered reference present)
                first second cancelled rfl (by omega) (by omega)
        have nodeEq := input.rule3ExtendedNode_callback_local target cursor.occurrence view _ _
          callbackEq excluded
        have childrenEq : (input.executableLocalizedRerootChildren cursor).mapM
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view first excluded) =
          (input.executableLocalizedRerootChildren cursor).mapM
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view second excluded) := by
          apply extendedDemandMapM_congr_on
          intro child present
          obtain ⟨covered, bounded⟩ := certificate.children cursor member child present
          apply ih (certificate.height child) (by omega) child covered first second
            excluded rfl (by omega) (by omega)
        simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
          executableLocalizedRerootChildren?_eq_some, bind, Option.bind, nodeEq, childrenEq]

/-- The computed maximum rank plus one suffices for a complete two-pass extended frame, with all
its refusal branches preserved.  All frame cursors must belong to the checked closed graph. -/
theorem ExtendedRule3DemandRankCertificate.frame_stable
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.ExtendedRule3DemandRankCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor fuel))
    (covered : ∀ cursor ∈ cursors, cursor ∈ certificate.vertices)
    (first second : Nat)
    (firstEnough : rule3CursorListHeight certificate.height cursors + 1 ≤ first)
    (secondEnough : rule3CursorListHeight certificate.height cursors + 1 ≤ second) :
    input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view first cursors =
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view second cursors := by
  cases first with
  | zero => omega
  | succ first =>
    cases second with
    | zero => omega
    | succ second =>
      apply input.extendedRule3Frame_succ_congr_keys target view first second cursors
      intro excluded cursor present
      have heightBound := rule3CursorListHeight_mem certificate.height cursors cursor present
      exact certificate.key_stable target view cursor (covered cursor present)
        first second (by omega) (by omega) excluded

/-! ## Executable rank tables and their independent checker -/

/-- Data-only proposed ranks for the extended weighted graph.  Cursor identity includes the
incoming cut coordinate.  This is definitionally the same table shape as the pre-extension one,
so the shared lookup and extension lemmas apply unchanged. -/
abbrev ExtendedRule3DemandRankTable (input : CertifiedLocalizedCIPInput) (fuel : Nat) :=
  List (input.LocalizedRerootCursor fuel × Nat)

/-- The checker independently recomputes every extended child and request edge from the molecule.
The callback inequality keeps the additive `+ 2` frame-plus-key weight. -/
def ExtendedRule3DemandRankTableValid (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (table : input.ExtendedRule3DemandRankTable fuel) : Prop :=
  (∀ cursor ∈ table.map Prod.fst, 0 < rule3DemandTableHeight table cursor) ∧
  (∀ cursor ∈ table.map Prod.fst, ∀ child ∈ input.executableLocalizedRerootChildren cursor,
    child ∈ table.map Prod.fst ∧
      rule3DemandTableHeight table child + 1 ≤ rule3DemandTableHeight table cursor) ∧
  (∀ cursor ∈ table.map Prod.fst,
    ∀ request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence,
      (∀ reference ∈ request, reference ∈ table.map Prod.fst) ∧
        rule3CursorListHeight (rule3DemandTableHeight table) request + 2 ≤
          rule3DemandTableHeight table cursor)

instance (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (table : input.ExtendedRule3DemandRankTable fuel) :
    Decidable (input.ExtendedRule3DemandRankTableValid table) := by
  unfold ExtendedRule3DemandRankTableValid
  infer_instance

def checkExtendedRule3DemandRanks? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (table : input.ExtendedRule3DemandRankTable fuel) :
    Option (input.ExtendedRule3DemandRankCertificate fuel) :=
  if valid : input.ExtendedRule3DemandRankTableValid table then
    some
      { vertices := table.map Prod.fst, height := rule3DemandTableHeight table,
        positive := valid.1, children := valid.2.1, callbacks := valid.2.2 }
  else none

/-- Required height of one extended vertex, computed from the already finished dependency table.
Children contribute one step; every listed request contributes its own maximum plus two. -/
def extendedRule3DemandRequiredHeight (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (table : input.ExtendedRule3DemandRankTable fuel)
    (cursor : input.LocalizedRerootCursor fuel) : Nat :=
  let childHeight := rule3CursorListHeight (rule3DemandTableHeight table)
    (input.executableLocalizedRerootChildren cursor) + 1
  (input.rule3ExtendedNodeCallbackRequests cursor.occurrence).foldl
    (fun height request =>
      max height (rule3CursorListHeight (rule3DemandTableHeight table) request + 2)) childHeight

private theorem extendedMaxFold_ge_start {α : Type} (value : α → Nat) (items : List α)
    (start : Nat) :
    start ≤ items.foldl (fun bound item => max bound (value item)) start := by
  induction items generalizing start with
  | nil => exact Nat.le_refl _
  | cons first rest ih => exact (Nat.le_max_left _ _).trans (ih _)

private theorem extendedMaxFold_ge_member {α : Type} (value : α → Nat) (items : List α)
    (start : Nat) (item : α) (present : item ∈ items) :
    value item ≤ items.foldl (fun bound item => max bound (value item)) start := by
  induction items generalizing start with
  | nil => simp at present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact (Nat.le_max_right _ _).trans (extendedMaxFold_ge_start value rest _)
    · exact ih _ present

theorem extendedRule3DemandRequiredHeight_children (input : CertifiedLocalizedCIPInput)
    {fuel : Nat} (table : input.ExtendedRule3DemandRankTable fuel)
    (cursor : input.LocalizedRerootCursor fuel) :
    rule3CursorListHeight (rule3DemandTableHeight table)
        (input.executableLocalizedRerootChildren cursor) + 1 ≤
      input.extendedRule3DemandRequiredHeight table cursor :=
  extendedMaxFold_ge_start _ _ _

theorem extendedRule3DemandRequiredHeight_callback (input : CertifiedLocalizedCIPInput)
    {fuel : Nat} (table : input.ExtendedRule3DemandRankTable fuel)
    (cursor : input.LocalizedRerootCursor fuel)
    (request : List (input.LocalizedRerootCursor fuel))
    (present : request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence) :
    rule3CursorListHeight (rule3DemandTableHeight table) request + 2 ≤
      input.extendedRule3DemandRequiredHeight table cursor :=
  extendedMaxFold_ge_member
    (fun request => rule3CursorListHeight (rule3DemandTableHeight table) request + 2)
    _ _ request present

/-- A completed extended dependency set permits one fresh vertex to be added without invalidating
any previous rank, including the additive request weight on empty lists. -/
theorem extendedRule3DemandRankTableValid_cons (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (table : input.ExtendedRule3DemandRankTable fuel)
    (valid : input.ExtendedRule3DemandRankTableValid table)
    (cursor : input.LocalizedRerootCursor fuel) (fresh : cursor ∉ table.map Prod.fst)
    (covered : ∀ child ∈ input.extendedRule3DemandSuccessors cursor,
      child ∈ table.map Prod.fst) :
    input.ExtendedRule3DemandRankTableValid
      ((cursor, input.extendedRule3DemandRequiredHeight table cursor) :: table) := by
  let finished := (cursor, input.extendedRule3DemandRequiredHeight table cursor) :: table
  have extension := rule3DemandTableExtends_cons table cursor
    (input.extendedRule3DemandRequiredHeight table cursor) fresh
  have newHeight : rule3DemandTableHeight finished cursor =
      input.extendedRule3DemandRequiredHeight table cursor := by
    simp [finished, rule3DemandTableHeight, rule3DemandTableLookup_cons]
  have childCovered : ∀ child ∈ input.executableLocalizedRerootChildren cursor,
      child ∈ table.map Prod.fst := by
    intro child present
    exact covered child (by simp [extendedRule3DemandSuccessors, present])
  have callbackCovered : ∀ request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence,
      ∀ reference ∈ request, reference ∈ table.map Prod.fst := by
    intro request requested reference present
    apply covered reference
    simp only [extendedRule3DemandSuccessors, List.mem_append, List.mem_flatten]
    exact Or.inr ⟨request, requested, present⟩
  have congrLists (values : List (input.LocalizedRerootCursor fuel))
      (members : ∀ value ∈ values, value ∈ table.map Prod.fst) :
      rule3CursorListHeight (rule3DemandTableHeight finished) values =
        rule3CursorListHeight (rule3DemandTableHeight table) values :=
    rule3CursorListHeight_congr _ _ values
      (fun value present => (extension value (members value present)).2)
  refine ⟨?_, ?_, ?_⟩
  · intro item member
    simp only [List.map_cons, List.mem_cons] at member
    rcases member with equal | member
    · subst item
      rw [newHeight]
      have bounded := input.extendedRule3DemandRequiredHeight_children table cursor
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
      have bounded := input.extendedRule3DemandRequiredHeight_children table cursor
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
      refine ⟨fun reference present =>
        (extension reference (callbackCovered request requested reference present)).1, ?_⟩
      rw [congrLists request (callbackCovered request requested), newHeight]
      exact input.extendedRule3DemandRequiredHeight_callback table cursor request requested
    · obtain ⟨old, bounded⟩ := valid.2.2 item member request requested
      refine ⟨fun reference present => (extension reference (old reference present)).1, ?_⟩
      rw [congrLists request old, (extension item member).2]
      exact bounded

/-! ## Executable discovery over the actual extended demand graph -/

/-- Memoized postorder traversal of the extended demand graph.  The active path detects cycles
before revisiting descendants; completed vertices are reused.  The separate checker is the
authority for every produced bound. -/
def discoverExtendedRule3DemandRanks (input : CertifiedLocalizedCIPInput) {fuel : Nat} :
    Nat → List (input.LocalizedRerootCursor fuel) →
      input.ExtendedRule3DemandRankTable fuel →
        input.LocalizedRerootCursor fuel →
          Except (input.Rule3DemandDiscoveryFailure fuel)
            (input.ExtendedRule3DemandRankTable fuel)
  | 0, _, table, cursor =>
      if (rule3DemandTableLookup table cursor).isSome then .ok table else .error .traversalLimit
  | remaining + 1, active, table, cursor =>
      if (rule3DemandTableLookup table cursor).isSome then .ok table
      else if cursor ∈ active then .error (.cycle cursor)
      else do
        let finished ← (input.extendedRule3DemandSuccessors cursor).foldlM
          (fun known child =>
            input.discoverExtendedRule3DemandRanks remaining (cursor :: active) known child) table
        pure ((cursor, input.extendedRule3DemandRequiredHeight finished cursor) :: finished)

/-- A checked extended graph covers the actual requested frame, including every reachable
extended dependency. -/
structure ExtendedRule3DemandPlan (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) where
  ranks : input.ExtendedRule3DemandRankCertificate fuel
  covers : ∀ root ∈ roots, root ∈ ranks.vertices

/-- No graph or ranks are supplied.  The finite occurrence carrier determines the traversal
budget; extended-graph discovery, weighted ranks, edge checking and root coverage are all
executable.  The old `prepareRule3DemandPlan` is never consulted, so newly extended-acyclic
graphs are handled. -/
def prepareExtendedRule3DemandPlan (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) :
    Except (input.Rule3DemandDiscoveryFailure fuel) (input.ExtendedRule3DemandPlan roots) := do
  let occurrenceCount := (input.localizedOccurrenceCarrier fuel).length
  let traversalBudget := occurrenceCount * (occurrenceCount + 1) + 1
  let table ← roots.foldlM (fun known root =>
    input.discoverExtendedRule3DemandRanks traversalBudget [] known root) []
  let some ranks := input.checkExtendedRule3DemandRanks? table | .error .invalidRanks
  if covers : ∀ root ∈ roots, root ∈ ranks.vertices then
    .ok { ranks, covers }
  else .error .missingRoot

def ExtendedRule3DemandPlan.bound {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots) : Nat :=
  rule3CursorListHeight plan.ranks.height roots + 1

def ExtendedRule3DemandPlan.evaluate {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option input.LocalizedRule3CanonicalKeyFrame :=
  input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view plan.bound roots

/-- The input-derived checked bound preserves the full optional extended frame at every larger
budget, including topology ambiguity and every failed recursive key. -/
theorem ExtendedRule3DemandPlan.evaluate_eq_above
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (budget : Nat) (enough : plan.bound ≤ budget) :
    plan.evaluate target view =
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget roots :=
  plan.ranks.frame_stable target view roots plan.covers plan.bound budget
    (Nat.le_refl _) enough

/-- Successful extended evaluation has the existing declarative frame meaning at its computed
budget. -/
theorem ExtendedRule3DemandPlan.evaluate_sound
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedRule3CanonicalKeyFrame)
    (computed : plan.evaluate target view = some frame) :
    input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view plan.bound roots frame :=
  input.buildLocalizedExtendedShortCircuitRule3FrameExec?_sound target view plan.bound roots frame
    computed

/-! ## Totality of extended discovery from extended acyclicity -/

theorem extendedRule3DemandReachable_child (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (cursor child : input.LocalizedRerootCursor fuel)
    (reachable : input.ExtendedRule3DemandReachable roots cursor)
    (edge : input.ExtendedRule3DemandEdge cursor child) :
    input.ExtendedRule3DemandReachable roots child := by
  obtain ⟨root, member, path⟩ := reachable
  exact ⟨root, member, path.tail edge⟩

/-- Fold a total extended discovery step while retaining every previously completed rank and all
requested vertices. -/
theorem extendedRule3DemandFold_total
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (step : input.ExtendedRule3DemandRankTable fuel → input.LocalizedRerootCursor fuel →
      Except (input.Rule3DemandDiscoveryFailure fuel)
        (input.ExtendedRule3DemandRankTable fuel))
    (newVertex : input.LocalizedRerootCursor fuel → Prop)
    (roots : List (input.LocalizedRerootCursor fuel))
    (total : ∀ cursor ∈ roots, ∀ before, input.ExtendedRule3DemandRankTableValid before →
      ∃ after, step before cursor = .ok after ∧
        input.ExtendedRule3DemandRankTableValid after ∧
        Rule3DemandTableExtends before after ∧ cursor ∈ after.map Prod.fst ∧
        (∀ item ∈ after.map Prod.fst, item ∈ before.map Prod.fst ∨ newVertex item))
    (table : input.ExtendedRule3DemandRankTable fuel)
    (valid : input.ExtendedRule3DemandRankTableValid table) :
    ∃ finished, roots.foldlM step table = .ok finished ∧
      input.ExtendedRule3DemandRankTableValid finished ∧
      Rule3DemandTableExtends table finished ∧
      (∀ root ∈ roots, root ∈ finished.map Prod.fst) ∧
      (∀ item ∈ finished.map Prod.fst, item ∈ table.map Prod.fst ∨ newVertex item) := by
  induction roots generalizing table with
  | nil =>
    exact ⟨table, rfl, valid, Rule3DemandTableExtends.refl table, by simp,
      fun _ present => Or.inl present⟩
  | cons first rest ih =>
    obtain ⟨middle, firstDone, middleValid, firstExtension, firstPresent, firstNew⟩ :=
      total first (by simp) table valid
    obtain ⟨finished, restDone, finishedValid, restExtension, restCovered, restNew⟩ :=
      ih (fun cursor present => total cursor (by simp [present])) middle middleValid
    refine ⟨finished, ?_, finishedValid, firstExtension.trans restExtension, ?_, ?_⟩
    · simp [List.foldlM_cons, firstDone, bind, Except.bind, restDone]
    · intro cursor present
      rcases List.mem_cons.mp present with equal | present
      · subst cursor
        exact (restExtension first firstPresent).1
      · exact restCovered cursor present
    · intro cursor present
      rcases restNew cursor present with earlier | new
      · exact firstNew cursor earlier
      · exact Or.inr new

/-- A strictly decreasing structural measure makes the extended memoized DFS succeed.  The
measure is used only in the proof; the runtime still discovers and checks all its own ranks. -/
theorem discoverExtendedRule3DemandRanks_total_of_measure
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (domain : input.LocalizedRerootCursor fuel → Prop)
    (measure : input.LocalizedRerootCursor fuel → Nat)
    (decreases : ∀ cursor, domain cursor →
      ∀ child ∈ input.extendedRule3DemandSuccessors cursor,
        domain child ∧ measure child < measure cursor) :
    ∀ budget active table cursor, input.ExtendedRule3DemandRankTableValid table →
      domain cursor → measure cursor < budget →
      (∀ ancestor ∈ active, measure cursor < measure ancestor) →
      ∃ finished, input.discoverExtendedRule3DemandRanks budget active table cursor = .ok finished ∧
        input.ExtendedRule3DemandRankTableValid finished ∧
        Rule3DemandTableExtends table finished ∧
        cursor ∈ finished.map Prod.fst ∧
        (∀ item ∈ finished.map Prod.fst,
          item ∈ table.map Prod.fst ∨ measure item ≤ measure cursor) := by
  intro budget
  induction budget with
  | zero => intros; omega
  | succ budget ih =>
    intro active table cursor valid inDomain bounded ancestors
    by_cases known : (rule3DemandTableLookup table cursor).isSome = true
    · exact ⟨table, by simp [discoverExtendedRule3DemandRanks, known], valid,
        Rule3DemandTableExtends.refl table,
        (rule3DemandTableLookup_isSome_iff table cursor).mp known,
        fun _ present => Or.inl present⟩
    · have fresh : cursor ∉ table.map Prod.fst := fun present =>
        known ((rule3DemandTableLookup_isSome_iff table cursor).mpr present)
      have inactive : cursor ∉ active := by
        intro present
        have impossible := ancestors cursor present
        omega
      have total : ∀ child ∈ input.extendedRule3DemandSuccessors cursor, ∀ before,
          input.ExtendedRule3DemandRankTableValid before →
          ∃ after,
            input.discoverExtendedRule3DemandRanks budget (cursor :: active) before child =
              .ok after ∧
            input.ExtendedRule3DemandRankTableValid after ∧
            Rule3DemandTableExtends before after ∧
            child ∈ after.map Prod.fst ∧
            (∀ item ∈ after.map Prod.fst,
              item ∈ before.map Prod.fst ∨ measure item < measure cursor) := by
        intro child present before beforeValid
        obtain ⟨childDomain, childBelow⟩ := decreases cursor inDomain child present
        have childAncestors : ∀ ancestor ∈ cursor :: active, measure child < measure ancestor := by
          intro ancestor present
          rcases List.mem_cons.mp present with rfl | present
          · exact childBelow
          · exact childBelow.trans (ancestors ancestor present)
        obtain ⟨after, computed, afterValid, extension, member, added⟩ :=
          ih (cursor :: active) before child beforeValid childDomain (by omega) childAncestors
        refine ⟨after, computed, afterValid, extension, member, ?_⟩
        intro item present
        rcases added item present with old | below
        · exact Or.inl old
        · exact Or.inr (below.trans_lt childBelow)
      obtain ⟨finished, folded, finishedValid, extension, covered, added⟩ :=
        input.extendedRule3DemandFold_total
          (fun before child =>
            input.discoverExtendedRule3DemandRanks budget (cursor :: active) before child)
          (fun item => measure item < measure cursor)
          (input.extendedRule3DemandSuccessors cursor) total table valid
      have stillFresh : cursor ∉ finished.map Prod.fst := by
        intro present
        rcases added cursor present with old | below
        · exact fresh old
        · omega
      let result := (cursor, input.extendedRule3DemandRequiredHeight finished cursor) :: finished
      have newExtension := rule3DemandTableExtends_cons finished cursor
        (input.extendedRule3DemandRequiredHeight finished cursor) stillFresh
      refine ⟨result, ?_,
        input.extendedRule3DemandRankTableValid_cons finished finishedValid cursor stillFresh covered,
        extension.trans newExtension, by simp [result], ?_⟩
      · simp [discoverExtendedRule3DemandRanks, known, inactive, folded, result]
      · intro item present
        simp only [result, List.map_cons, List.mem_cons] at present
        rcases present with rfl | present
        · exact Or.inr (Nat.le_refl _)
        · rcases added item present with old | below
          · exact Or.inl old
          · exact Or.inr below.le

/-- Every requested root is constructed with a checked table when one common structural budget
dominates a decreasing measure on the reachable domain.  No computed rank is assumed. -/
theorem discoverExtendedRule3DemandRoots_total_of_measure
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (domain : input.LocalizedRerootCursor fuel → Prop)
    (measure : input.LocalizedRerootCursor fuel → Nat)
    (decreases : ∀ cursor, domain cursor →
      ∀ child ∈ input.extendedRule3DemandSuccessors cursor,
        domain child ∧ measure child < measure cursor)
    (budget : Nat) (roots : List (input.LocalizedRerootCursor fuel))
    (rootDomain : ∀ root ∈ roots, domain root)
    (bounded : ∀ root ∈ roots, measure root < budget) :
    ∃ table,
      roots.foldlM (fun known root =>
        input.discoverExtendedRule3DemandRanks budget [] known root) [] = .ok table ∧
      input.ExtendedRule3DemandRankTableValid table ∧
      (∀ root ∈ roots, root ∈ table.map Prod.fst) := by
  have total : ∀ root ∈ roots, ∀ before, input.ExtendedRule3DemandRankTableValid before →
      ∃ after, input.discoverExtendedRule3DemandRanks budget [] before root = .ok after ∧
        input.ExtendedRule3DemandRankTableValid after ∧
        Rule3DemandTableExtends before after ∧
        root ∈ after.map Prod.fst ∧
        (∀ item ∈ after.map Prod.fst, item ∈ before.map Prod.fst ∨ True) := by
    intro root present before valid
    obtain ⟨after, computed, afterValid, extension, member, _⟩ :=
      input.discoverExtendedRule3DemandRanks_total_of_measure domain measure decreases budget []
        before root valid (rootDomain root present) (bounded root present) (by simp)
    exact ⟨after, computed, afterValid, extension, member, fun _ _ => Or.inr trivial⟩
  obtain ⟨table, computed, valid, _, covered, _⟩ :=
    input.extendedRule3DemandFold_total _ (fun _ => True) roots total []
      (by simp [ExtendedRule3DemandRankTableValid])
  exact ⟨table, computed, valid, covered⟩





theorem prepareExtendedRule3DemandPlan_total_of_acyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (acyclic : input.ExtendedRule3DemandAcyclic roots) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan := by
  letI := input.localizedRerootCursorFintype fuel
  obtain ⟨measure, measureBound, decreases⟩ :=
    finiteDemandMeasure input.ExtendedRule3DemandEdge (input.ExtendedRule3DemandReachable roots)
      (fun parent reachable child edge =>
        input.extendedRule3DemandReachable_child roots parent child reachable edge) acyclic
  let budget := (input.localizedOccurrenceCarrier fuel).length *
    ((input.localizedOccurrenceCarrier fuel).length + 1) + 1
  obtain ⟨table, computed, valid, covered⟩ :=
    input.discoverExtendedRule3DemandRoots_total_of_measure
      (input.ExtendedRule3DemandReachable roots) measure decreases budget roots
      (fun root present => ⟨root, present, Relation.ReflTransGen.refl⟩)
      (fun root _ => by
        have bounded := measureBound root
        rw [input.localizedRerootCursor_card fuel] at bounded
        dsimp [budget]
        omega)
  let ranks : input.ExtendedRule3DemandRankCertificate fuel :=
    { vertices := table.map Prod.fst, height := rule3DemandTableHeight table,
      positive := valid.1, children := valid.2.1, callbacks := valid.2.2 }
  let plan : input.ExtendedRule3DemandPlan roots := { ranks, covers := covered }
  refine ⟨plan, ?_⟩
  dsimp [budget] at computed
  simp [prepareExtendedRule3DemandPlan, computed, bind, Except.bind,
    checkExtendedRule3DemandRanks?, valid, ranks, plan]
  rw [dif_pos covered]



/-- Every edge checked by an extended rank certificate stays in its vertices and strictly
decreases rank.  Request edges include their extra frame-plus-key step in the stored inequality. -/
theorem ExtendedRule3DemandRankCertificate.edge_decreases
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.ExtendedRule3DemandRankCertificate fuel)
    (parent child : input.LocalizedRerootCursor fuel)
    (present : parent ∈ certificate.vertices) (edge : input.ExtendedRule3DemandEdge parent child) :
    child ∈ certificate.vertices ∧ certificate.height child < certificate.height parent := by
  change child ∈ input.executableLocalizedRerootChildren parent ++
    (input.rule3ExtendedNodeCallbackRequests parent.occurrence).flatten at edge
  rcases List.mem_append.mp edge with childEdge | callbackEdge
  · obtain ⟨covered, bounded⟩ := certificate.children parent present child childEdge
    exact ⟨covered, by omega⟩
  · obtain ⟨request, requested, reference⟩ := List.mem_flatten.mp callbackEdge
    obtain ⟨covered, bounded⟩ := certificate.callbacks parent present request requested
    have belowMax := rule3CursorListHeight_mem certificate.height request child reference
    exact ⟨covered child reference, by omega⟩

theorem ExtendedRule3DemandRankCertificate.path_closed
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.ExtendedRule3DemandRankCertificate fuel)
    {parent child : input.LocalizedRerootCursor fuel}
    (present : parent ∈ certificate.vertices)
    (path : Relation.ReflTransGen input.ExtendedRule3DemandEdge parent child) :
    child ∈ certificate.vertices := by
  induction path with
  | refl => exact present
  | tail _ edge ih => exact (certificate.edge_decreases _ _ ih edge).1

theorem ExtendedRule3DemandRankCertificate.path_decreases
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.ExtendedRule3DemandRankCertificate fuel)
    {parent child : input.LocalizedRerootCursor fuel}
    (present : parent ∈ certificate.vertices)
    (path : Relation.TransGen input.ExtendedRule3DemandEdge parent child) :
    child ∈ certificate.vertices ∧ certificate.height child < certificate.height parent := by
  induction path with
  | single edge => exact certificate.edge_decreases _ _ present edge
  | tail _ edge ih =>
    obtain ⟨covered, smaller⟩ := certificate.edge_decreases _ _ ih.1 edge
    exact ⟨covered, smaller.trans ih.2⟩


theorem ExtendedRule3DemandPlan.acyclic
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots) :
    input.ExtendedRule3DemandAcyclic roots := by
  intro cursor reachable cycle
  obtain ⟨root, rootMember, path⟩ := reachable
  have present := plan.ranks.path_closed (plan.covers root rootMember) path
  exact Nat.lt_irrefl _ (plan.ranks.path_decreases present cycle).2




theorem prepareExtendedRule3DemandPlan_success_iff_acyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) :
    (∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan) ↔
      input.ExtendedRule3DemandAcyclic roots := by
  exact ⟨fun ⟨plan, _⟩ => plan.acyclic,
    input.prepareExtendedRule3DemandPlan_total_of_acyclic roots⟩

/-- Extended-graph rejection has a concrete mathematical cause: a reachable cycle of the actual
extended demand graph.  It does not assert that the molecule has no chemical descriptor. -/
theorem prepareExtendedRule3DemandPlan_error_has_cycle
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (failure : input.Rule3DemandDiscoveryFailure fuel)
    (failed : input.prepareExtendedRule3DemandPlan roots = .error failure) :
    ∃ cursor, input.ExtendedRule3DemandReachable roots cursor ∧
      Relation.TransGen input.ExtendedRule3DemandEdge cursor cursor := by
  classical
  by_contra absent
  have acyclic : input.ExtendedRule3DemandAcyclic roots := by
    intro cursor reachable cycle
    exact absent ⟨cursor, reachable, cycle⟩
  obtain ⟨plan, succeeds⟩ := input.prepareExtendedRule3DemandPlan_total_of_acyclic roots acyclic
  rw [failed] at succeeds
  contradiction



theorem prepareExtendedRule3DemandPlan_constructs_stable_evaluator
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (acyclic : input.ExtendedRule3DemandAcyclic roots) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan ∧
      ∀ (target : input.LocalizedCIPOccurrence fuel)
        (view : input.LocalizedDependencyView target) (budget : Nat),
          plan.bound ≤ budget →
            plan.evaluate target view =
              input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget roots := by
  obtain ⟨plan, succeeds⟩ := input.prepareExtendedRule3DemandPlan_total_of_acyclic roots acyclic
  exact ⟨plan, succeeds, plan.evaluate_eq_above⟩

/-! ## Bridges from existing input-derived acyclicity certificates -/




theorem prepareExtendedRule3DemandPlan_total_of_rule3DemandAcyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (acyclic : input.Rule3DemandAcyclic roots) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan :=
  input.prepareExtendedRule3DemandPlan_total_of_acyclic roots
    (input.extendedRule3DemandAcyclic_of_rule3DemandAcyclic roots acyclic)



theorem prepareExtendedRule3DemandPlan_total_of_rule3DemandPlan
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.Rule3DemandPlan roots) :
    ∃ extendedPlan, input.prepareExtendedRule3DemandPlan roots = .ok extendedPlan :=
  input.prepareExtendedRule3DemandPlan_total_of_rule3DemandAcyclic roots plan.acyclic



theorem prepareExtendedRule3DemandPlan_total_of_noCallbacks
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root)
    (noCallbacks : ∀ occurrence : input.LocalizedCIPOccurrence fuel,
      input.rule3ExtendedNodeCallbackRequests occurrence = []) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan :=
  input.prepareExtendedRule3DemandPlan_total_of_acyclic roots
    (input.extendedRule3DemandAcyclic_of_noCallbacks roots rootValid noCallbacks)



theorem prepareExtendedRule3DemandPlan_total_of_certificate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (ready : input.LocalizedExtendedRule3NoCallbackCertificate fuel)
    (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan :=
  input.prepareExtendedRule3DemandPlan_total_of_acyclic roots
    (input.extendedRule3DemandAcyclic_of_certificate ready roots rootValid)

/-- Consequently the extended constructor is total on the entire no-double-bond-record domain for
every list of valid requested roots. -/
theorem prepareExtendedRule3DemandPlan_total_of_noDoubleRecords
    (input : CertifiedLocalizedCIPInput)
    (noDouble : input.certified.input.molecule.NoLocalizedDoubleBondRecords)
    {fuel : Nat} (roots : List (input.LocalizedRerootCursor fuel))
    (rootValid : ∀ root ∈ roots, input.LocalizedRerootCursorValid root) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan :=
  input.prepareExtendedRule3DemandPlan_total_of_acyclic roots
    (input.extendedRule3DemandAcyclic_of_noDoubleRecords noDouble roots rootValid)

/-! ## Instantiation of the generic weighted demand graph

The generic core `TetraStereo.Certificate.WeightedDemand` parameterizes everything by a
`Graph α` of `children` and `requests`.  The declarations below are the requested concrete
instantiation with the *actual* extended demand data, together with the definitional coincidence
of the generic edges, reachability and acyclicity with the extended graph defined in
`LocalizedExtendedDemandGraph`, and the transport of checked extended plans into generic checked
plans. -/

/-- The actual extended weighted demand graph: executable cut-neighborhood children carry weight
one, and every potential endpoint request of `rule3ExtendedNodeCallbackRequests` carries weight
two.  This is the concrete instantiation of `TetraStereo.Certificate.WeightedDemand.Graph`. -/
def extendedWeightedDemandGraph (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    TetraStereo.Certificate.WeightedDemand.Graph (input.LocalizedRerootCursor fuel) where
  children := fun cursor => input.executableLocalizedRerootChildren cursor
  requests := fun cursor => input.rule3ExtendedNodeCallbackRequests cursor.occurrence

theorem extendedWeightedDemandGraph_successors (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (cursor : input.LocalizedRerootCursor fuel) :
    TetraStereo.Certificate.WeightedDemand.successors
        (input.extendedWeightedDemandGraph fuel) cursor =
      input.extendedRule3DemandSuccessors cursor :=
  rfl

theorem extendedWeightedDemandGraph_edge (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (parent child : input.LocalizedRerootCursor fuel) :
    TetraStereo.Certificate.WeightedDemand.Edge
        (input.extendedWeightedDemandGraph fuel) parent child ↔
      input.ExtendedRule3DemandEdge parent child :=
  Iff.rfl

theorem extendedWeightedDemandGraph_reachable (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (roots : List (input.LocalizedRerootCursor fuel))
    (cursor : input.LocalizedRerootCursor fuel) :
    TetraStereo.Certificate.WeightedDemand.Reachable
        (input.extendedWeightedDemandGraph fuel) roots cursor ↔
      input.ExtendedRule3DemandReachable roots cursor :=
  Iff.rfl

theorem extendedWeightedDemandGraph_acyclic (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    (roots : List (input.LocalizedRerootCursor fuel)) :
    TetraStereo.Certificate.WeightedDemand.Acyclic
        (input.extendedWeightedDemandGraph fuel) roots ↔
      input.ExtendedRule3DemandAcyclic roots :=
  Iff.rfl




theorem prepareExtendedRule3DemandPlan_total_of_weightedAcyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (acyclic : TetraStereo.Certificate.WeightedDemand.Acyclic
      (input.extendedWeightedDemandGraph fuel) roots) :
    ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan :=
  input.prepareExtendedRule3DemandPlan_total_of_acyclic roots
    ((input.extendedWeightedDemandGraph_acyclic fuel roots).mp acyclic)



theorem extendedWeightedDemandGraph_acyclic_of_prepare
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel))
    (succeeds : ∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan) :
    TetraStereo.Certificate.WeightedDemand.Acyclic
      (input.extendedWeightedDemandGraph fuel) roots :=
  (input.extendedWeightedDemandGraph_acyclic fuel roots).mpr
    ((input.prepareExtendedRule3DemandPlan_success_iff_acyclic roots).mp succeeds)

/-- Exact generic domain of the extended constructor. -/
theorem prepareExtendedRule3DemandPlan_total_iff_weightedAcyclic
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) :
    (∃ plan, input.prepareExtendedRule3DemandPlan roots = .ok plan) ↔
      TetraStereo.Certificate.WeightedDemand.Acyclic
        (input.extendedWeightedDemandGraph fuel) roots :=
  (input.prepareExtendedRule3DemandPlan_success_iff_acyclic roots).trans
    (input.extendedWeightedDemandGraph_acyclic fuel roots).symm

/-- The generic list maximum coincides with the localized one used by the extended certificate. -/
theorem weightedListHeight_eq_rule3CursorListHeight {α : Type} (height : α → Nat)
    (values : List α) :
    TetraStereo.Certificate.WeightedDemand.listHeight height values =
      rule3CursorListHeight height values := by
  induction values with
  | nil => rfl
  | cons first rest ih => simp [TetraStereo.Certificate.WeightedDemand.listHeight,
      rule3CursorListHeight, ih]




def ExtendedRule3DemandPlan.toWeightedPlan
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots) :
    TetraStereo.Certificate.WeightedDemand.Plan
      (input.extendedWeightedDemandGraph fuel) roots where
  ranks :=
    { vertices := plan.ranks.vertices
      height := plan.ranks.height
      positive := plan.ranks.positive
      children := plan.ranks.children
      callbacks := by
        intro cursor member request requested
        have requested' : request ∈ input.rule3ExtendedNodeCallbackRequests cursor.occurrence := by
          simpa [extendedWeightedDemandGraph] using requested
        obtain ⟨covered, bounded⟩ := plan.ranks.callbacks cursor member request requested'
        refine ⟨covered, ?_⟩
        rw [weightedListHeight_eq_rule3CursorListHeight]
        exact bounded }
  covers := plan.covers



theorem ExtendedRule3DemandPlan.toWeightedPlan_acyclic
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)}
    (plan : input.ExtendedRule3DemandPlan roots) :
    TetraStereo.Certificate.WeightedDemand.Acyclic
      (input.extendedWeightedDemandGraph fuel) roots :=
  TetraStereo.Certificate.WeightedDemand.Plan.acyclic plan.toWeightedPlan

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
