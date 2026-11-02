import TetraStereo.OneCenter.LocalizedRule3NodeCallbackDemand
import TetraStereo.OneCenter.LocalizedRerootShortCircuitRule3Key

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

def rule3CursorListHeight {α : Type} (height : α → Nat) : List α → Nat
  | [] => 0
  | cursor :: rest => max (height cursor) (rule3CursorListHeight height rest)

theorem rule3CursorListHeight_mem {α : Type} (height : α → Nat) (values : List α)
    (value : α) (present : value ∈ values) : height value ≤ rule3CursorListHeight height values := by
  induction values with
  | nil => simp at present
  | cons first rest ih =>
    rcases List.mem_cons.mp present with rfl | present
    · exact Nat.le_max_left _ _
    · exact (ih present).trans (Nat.le_max_right _ _)

/-- A finite closed portion of the actual computation graph. Child edges consume one fuel step;
node-to-frame-to-key callback edges consume two. No successful callback or geometry is assumed. -/
structure Rule3DemandRankCertificate (input : CertifiedLocalizedCIPInput) (fuel : Nat) where
  vertices : List (input.LocalizedRerootCursor fuel)
  height : input.LocalizedRerootCursor fuel → Nat
  positive : ∀ cursor ∈ vertices, 0 < height cursor
  children : ∀ cursor ∈ vertices, ∀ child ∈ input.executableLocalizedRerootChildren cursor,
    child ∈ vertices ∧ height child + 1 ≤ height cursor
  callbacks : ∀ cursor ∈ vertices, ∀ request ∈ input.rule3NodeCallbackRequests cursor.occurrence,
    (∀ reference ∈ request, reference ∈ vertices) ∧ rule3CursorListHeight height request + 2 ≤ height cursor

private theorem mapM_congr_on {α β : Type} (before after : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, before value = after value) →
      values.mapM before = values.mapM after
  | [], _ => rfl
  | value :: values, agree => by
    have head := agree value (by simp)
    have tail := mapM_congr_on before after values (fun value present => agree value (by simp [present]))
    simp [head, tail]

/-- Equality of both key passes implies equality of the full optional frame, including topology
ambiguity and any failed recursive key. -/
theorem rule3Frame_succ_congr_keys
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (first second : Nat) (cursors : List (input.LocalizedRerootCursor fuel))
    (agree : ∀ excluded cursor, cursor ∈ cursors →
      input.buildLocalizedRerootShortCircuitRule3KeyExec? target view first excluded cursor =
        input.buildLocalizedRerootShortCircuitRule3KeyExec? target view second excluded cursor) :
    input.buildLocalizedShortCircuitRule3FrameExec? target view (first + 1) cursors =
      input.buildLocalizedShortCircuitRule3FrameExec? target view (second + 1) cursors := by
  have mapped : ∀ excluded, cursors.mapM
      (input.buildLocalizedRerootShortCircuitRule3KeyExec? target view first excluded) =
        cursors.mapM (input.buildLocalizedRerootShortCircuitRule3KeyExec? target view second excluded) :=
    fun excluded => mapM_congr_on _ _ cursors (agree excluded)
  simp only [buildLocalizedShortCircuitRule3FrameExec?, mapped]

/-- A checked demand rank stabilizes the complete recursive key result at every larger budget.
The induction crosses real endpoint callbacks as well as ordinary child traversal. -/
theorem Rule3DemandRankCertificate.key_stable
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.Rule3DemandRankCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (cursor : input.LocalizedRerootCursor fuel) (member : cursor ∈ certificate.vertices)
    (first second : Nat) (firstEnough : certificate.height cursor ≤ first)
    (secondEnough : certificate.height cursor ≤ second)
    (excluded : List input.LocalizedRule3PhysicalUnitId) :
    input.buildLocalizedRerootShortCircuitRule3KeyExec? target view first excluded cursor =
      input.buildLocalizedRerootShortCircuitRule3KeyExec? target view second excluded cursor := by
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
        have callbackEq : input.Rule3CallbackAgreesOn (input.rule3NodeCallbackRequests cursor.occurrence)
            (input.buildLocalizedShortCircuitRule3FrameExec? target view first)
            (input.buildLocalizedShortCircuitRule3FrameExec? target view second) := by
          intro request requested
          obtain ⟨covered, bounded⟩ := certificate.callbacks cursor member request requested
          cases first with
          | zero => omega
          | succ first =>
            cases second with
            | zero => omega
            | succ second =>
              apply input.rule3Frame_succ_congr_keys target view first second request
              intro cancelled reference present
              have heightBound := rule3CursorListHeight_mem certificate.height request reference present
              apply ih (certificate.height reference) (by omega) reference (covered reference present)
                first second cancelled rfl (by omega) (by omega)
        have nodeEq := input.rule3Node_callback_local target cursor.occurrence view _ _ callbackEq excluded
        have childrenEq : (input.executableLocalizedRerootChildren cursor).mapM
            (input.buildLocalizedRerootShortCircuitRule3KeyExec? target view first excluded) =
          (input.executableLocalizedRerootChildren cursor).mapM
            (input.buildLocalizedRerootShortCircuitRule3KeyExec? target view second excluded) := by
          apply mapM_congr_on
          intro child present
          obtain ⟨covered, bounded⟩ := certificate.children cursor member child present
          apply ih (certificate.height child) (by omega) child covered first second
            excluded rfl (by omega) (by omega)
        simp only [buildLocalizedRerootShortCircuitRule3KeyExec?,
          executableLocalizedRerootChildren?_eq_some, bind, Option.bind, nodeEq, childrenEq]

/-- The computed maximum rank plus one suffices for a complete two-pass frame, with all its
refusal branches preserved. All frame cursors must belong to the checked closed graph. -/
theorem Rule3DemandRankCertificate.frame_stable
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.Rule3DemandRankCertificate fuel)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (cursors : List (input.LocalizedRerootCursor fuel))
    (covered : ∀ cursor ∈ cursors, cursor ∈ certificate.vertices)
    (first second : Nat)
    (firstEnough : rule3CursorListHeight certificate.height cursors + 1 ≤ first)
    (secondEnough : rule3CursorListHeight certificate.height cursors + 1 ≤ second) :
    input.buildLocalizedShortCircuitRule3FrameExec? target view first cursors =
      input.buildLocalizedShortCircuitRule3FrameExec? target view second cursors := by
  cases first with
  | zero => omega
  | succ first =>
    cases second with
    | zero => omega
    | succ second =>
      apply input.rule3Frame_succ_congr_keys target view first second cursors
      intro excluded cursor present
      have heightBound := rule3CursorListHeight_mem certificate.height cursors cursor present
      exact certificate.key_stable target view cursor (covered cursor present)
        first second (by omega) (by omega) excluded

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
