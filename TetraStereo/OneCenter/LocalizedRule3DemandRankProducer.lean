import TetraStereo.OneCenter.LocalizedRule3DemandRankStability
import TetraStereo.OneCenter.LocalizedOccurrenceFiniteCarrier

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

instance localizedRerootCursorDecidableEq (input : CertifiedLocalizedCIPInput) (fuel : Nat) :
    DecidableEq (input.LocalizedRerootCursor fuel) := fun left right =>
  if occurrence : left.occurrence = right.occurrence then
    if previous : left.previous? = right.previous? then
      isTrue (LocalizedRerootCursor.ext input occurrence previous)
    else isFalse (fun equal => previous (congrArg LocalizedRerootCursor.previous? equal))
  else isFalse (fun equal => occurrence (congrArg LocalizedRerootCursor.occurrence equal))

/-- Data-only proposed ranks. Cursor identity includes the incoming cut coordinate. -/
abbrev Rule3DemandRankTable (input : CertifiedLocalizedCIPInput) (fuel : Nat) :=
  List (input.LocalizedRerootCursor fuel × Nat)

def rule3DemandTableLookup {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (table : input.Rule3DemandRankTable fuel) (cursor : input.LocalizedRerootCursor fuel) : Option Nat :=
  (table.find? (fun entry => decide (entry.1 = cursor))).map Prod.snd

def rule3DemandTableHeight {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (table : input.Rule3DemandRankTable fuel) (cursor : input.LocalizedRerootCursor fuel) : Nat :=
  (rule3DemandTableLookup table cursor).getD 0

/-- The checker independently recomputes every child and callback edge from the molecule. -/
def Rule3DemandRankTableValid (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (table : input.Rule3DemandRankTable fuel) : Prop :=
  (∀ cursor ∈ table.map Prod.fst, 0 < rule3DemandTableHeight table cursor) ∧
  (∀ cursor ∈ table.map Prod.fst, ∀ child ∈ input.executableLocalizedRerootChildren cursor,
    child ∈ table.map Prod.fst ∧ rule3DemandTableHeight table child + 1 ≤ rule3DemandTableHeight table cursor) ∧
  (∀ cursor ∈ table.map Prod.fst, ∀ request ∈ input.rule3NodeCallbackRequests cursor.occurrence,
    (∀ reference ∈ request, reference ∈ table.map Prod.fst) ∧
      rule3CursorListHeight (rule3DemandTableHeight table) request + 2 ≤ rule3DemandTableHeight table cursor)

instance (input : CertifiedLocalizedCIPInput) {fuel : Nat} (table : input.Rule3DemandRankTable fuel) :
    Decidable (input.Rule3DemandRankTableValid table) := by
  unfold Rule3DemandRankTableValid
  infer_instance

def checkRule3DemandRanks? (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (table : input.Rule3DemandRankTable fuel) : Option (input.Rule3DemandRankCertificate fuel) :=
  if valid : input.Rule3DemandRankTableValid table then
    some
      { vertices := table.map Prod.fst, height := rule3DemandTableHeight table,
        positive := valid.1, children := valid.2.1, callbacks := valid.2.2 }
  else none

/-- Reachability discovery uses the same potential requests that the locality proof covers. -/
def rule3DemandSuccessors (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) : List (input.LocalizedRerootCursor fuel) :=
  input.executableLocalizedRerootChildren cursor ++
    (input.rule3NodeCallbackRequests cursor.occurrence).flatten

def rule3DemandRequiredHeight (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (table : input.Rule3DemandRankTable fuel) (cursor : input.LocalizedRerootCursor fuel) : Nat :=
  let childHeight := rule3CursorListHeight (rule3DemandTableHeight table)
    (input.executableLocalizedRerootChildren cursor) + 1
  (input.rule3NodeCallbackRequests cursor.occurrence).foldl
    (fun height request => max height (rule3CursorListHeight (rule3DemandTableHeight table) request + 2)) childHeight

/-- Discovery failures describe this conservative graph, not chemical nonexistence. -/
inductive Rule3DemandDiscoveryFailure (input : CertifiedLocalizedCIPInput) (fuel : Nat)
  | cycle (cursor : input.LocalizedRerootCursor fuel)
  | traversalLimit
  | invalidRanks
  | missingRoot

/-- Memoized postorder traversal. The active path detects cycles before revisiting descendants;
completed vertices are reused. The separate checker is the authority for every produced bound. -/
def discoverRule3DemandRanks (input : CertifiedLocalizedCIPInput) {fuel : Nat} :
    Nat → List (input.LocalizedRerootCursor fuel) → input.Rule3DemandRankTable fuel →
      input.LocalizedRerootCursor fuel →
        Except (input.Rule3DemandDiscoveryFailure fuel) (input.Rule3DemandRankTable fuel)
  | 0, _, table, cursor =>
      if (rule3DemandTableLookup table cursor).isSome then .ok table else .error .traversalLimit
  | remaining + 1, active, table, cursor =>
      if (rule3DemandTableLookup table cursor).isSome then .ok table
      else if cursor ∈ active then .error (.cycle cursor)
      else do
        let finished ← (input.rule3DemandSuccessors cursor).foldlM
          (fun known child => input.discoverRule3DemandRanks remaining (cursor :: active) known child) table
        pure ((cursor, input.rule3DemandRequiredHeight finished cursor) :: finished)

/-- A checked graph covers the actual requested frame, including every reachable dependency. -/
structure Rule3DemandPlan (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) where
  ranks : input.Rule3DemandRankCertificate fuel
  covers : ∀ root ∈ roots, root ∈ ranks.vertices

/-- No graph or ranks are supplied. The finite occurrence carrier determines the traversal
budget; graph discovery, weighted ranks, edge checking and root coverage are all executable. -/
def prepareRule3DemandPlan (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (roots : List (input.LocalizedRerootCursor fuel)) :
    Except (input.Rule3DemandDiscoveryFailure fuel) (input.Rule3DemandPlan roots) := do
  let occurrenceCount := (input.localizedOccurrenceCarrier fuel).length
  let traversalBudget := occurrenceCount * (occurrenceCount + 1) + 1
  let table ← roots.foldlM (fun known root =>
    input.discoverRule3DemandRanks traversalBudget [] known root) []
  let some ranks := input.checkRule3DemandRanks? table | .error .invalidRanks
  if covers : ∀ root ∈ roots, root ∈ ranks.vertices then
    .ok { ranks, covers }
  else .error .missingRoot

def Rule3DemandPlan.bound {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)} (plan : input.Rule3DemandPlan roots) : Nat :=
  rule3CursorListHeight plan.ranks.height roots + 1

def Rule3DemandPlan.evaluate {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)} (plan : input.Rule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option input.LocalizedRule3CanonicalKeyFrame :=
  input.buildLocalizedShortCircuitRule3FrameExec? target view plan.bound roots

/-- The input-derived checked bound preserves the full optional result at every larger budget. -/
theorem Rule3DemandPlan.evaluate_eq_above {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)} (plan : input.Rule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (budget : Nat) (enough : plan.bound ≤ budget) :
    plan.evaluate target view = input.buildLocalizedShortCircuitRule3FrameExec? target view budget roots :=
  plan.ranks.frame_stable target view roots plan.covers plan.bound budget (Nat.le_refl _) enough

/-- Successful evaluation has the existing declarative frame meaning at its computed budget. -/
theorem Rule3DemandPlan.evaluate_sound {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)} (plan : input.Rule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedRule3CanonicalKeyFrame) (computed : plan.evaluate target view = some frame) :
    input.DeclarativeLocalizedShortCircuitRule3Frame target view plan.bound roots frame :=
  input.buildLocalizedShortCircuitRule3FrameExec?_sound target view plan.bound roots frame computed

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
