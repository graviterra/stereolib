import TetraStereo.OneCenter.LocalizedRule3DemandRankProducer
import TetraStereo.OneCenter.LocalizedRerootExtendedShortCircuitRule3Key

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Constitutional shortcuts can remove the eager endpoint request, but cannot add requests. -/
theorem rule3ShortEndpointCallbackRequests_subset
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpoint partner : input.Atom) (cursor : input.LocalizedRerootCursor fuel) :
    ∀ request ∈ input.rule3ShortEndpointCallbackRequests endpoint partner cursor,
      request ∈ input.rule3EndpointCallbackRequests endpoint partner cursor := by
  intro request present
  unfold rule3ShortEndpointCallbackRequests at present
  split at present
  next first second candidates =>
    cases hf : input.localizedRule3ReferenceCursorExec? cursor first with
    | none => simp [hf] at present
    | some firstCursor =>
      cases hs : input.localizedRule3ReferenceCursorExec? cursor second with
      | none => simp [hf, hs] at present
      | some secondCursor =>
        simp only [hf, hs] at present
        split at present <;> simp_all [rule3EndpointCallbackRequests]
        split at present <;> simp_all
  next => simp at present

/-- On a checked odd route, the pre-extension demand list is exactly the eager odd-axis list. -/
theorem rule3NodeCallbackRequests_eq_odd_of_routeCertificate
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel)
    (certificate : input.LocalizedRule3OddRouteCertificate occurrence)
    (routed : input.localizedRule3OddRouteCertificate? occurrence = some certificate) :
    input.rule3NodeCallbackRequests occurrence = input.rule3OddCallbackRequests occurrence := by
  have ordinary := input.ordinaryRoute_none_of_oddRoute occurrence certificate routed
  simp only [rule3NodeCallbackRequests, ordinary]
  unfold localizedRule3OddRouteCertificate? at routed
  split at routed
  next edge =>
    split at routed
    next initial entry =>
      split at routed
      next found => contradiction
      next axis found =>
        split at routed
        next ordinary => contradiction
        next notOrdinary =>
          split at routed
          next odd =>
            simp only [rule3OriginalNodeCallbackRequests, if_pos edge, entry, found,
              if_neg notOrdinary, if_pos odd]
          next => contradiction
    next => contradiction
  next => contradiction

/-- The extended node's actual potential requests are contained in the previous request graph.
The statement is independent of auxiliary view, callback answers, geometry, and exclusions. -/
theorem rule3ExtendedNodeCallbackRequests_subset
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    ∀ request ∈ input.rule3ExtendedNodeCallbackRequests occurrence,
      request ∈ input.rule3NodeCallbackRequests occurrence := by
  intro request present
  unfold rule3ExtendedNodeCallbackRequests at present
  cases routed : input.localizedRule3OddRouteCertificate? occurrence with
  | none => simpa only [routed] using present
  | some certificate =>
    rw [input.rule3NodeCallbackRequests_eq_odd_of_routeCertificate occurrence certificate routed]
    simp only [routed] at present
    unfold rule3ShortOddCallbackRequests at present
    unfold rule3OddCallbackRequests
    cases found : input.localizedRule3OddCumuleneEndpointCursorFrameExec?
        (input.localizedRule3CumulatedTraversalFuel fuel) occurrence with
    | none => simp [found] at present
    | some topology =>
      simp only [found, List.mem_append] at present ⊢
      rcases present with left | right
      · exact Or.inl (input.rule3ShortEndpointCallbackRequests_subset _ _ _ request left)
      · exact Or.inr (input.rule3ShortEndpointCallbackRequests_subset _ _ _ request right)

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
theorem extendedRule3Frame_succ_congr_keys
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (first second : Nat) (cursors : List (input.LocalizedRerootCursor fuel))
    (agree : ∀ excluded cursor, cursor ∈ cursors →
      input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view first excluded cursor =
        input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view second excluded cursor) :
    input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view (first + 1) cursors =
      input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view (second + 1) cursors := by
  have mapped : ∀ excluded, cursors.mapM
      (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view first excluded) =
        cursors.mapM (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view second excluded) :=
    fun excluded => mapM_congr_on _ _ cursors (agree excluded)
  simp only [buildLocalizedExtendedShortCircuitRule3FrameExec?, mapped]

/-- An existing checked demand rank also stabilizes the extended evaluator.
A checked demand rank stabilizes the complete recursive key result at every larger budget.
The induction crosses real endpoint callbacks as well as ordinary child traversal. -/
theorem Rule3DemandRankCertificate.extended_key_stable
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.Rule3DemandRankCertificate fuel)
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
        have callbackEq : input.Rule3CallbackAgreesOn (input.rule3ExtendedNodeCallbackRequests cursor.occurrence)
            (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view first)
            (input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view second) := by
          intro request requested
          obtain ⟨covered, bounded⟩ := certificate.callbacks cursor member request
            (input.rule3ExtendedNodeCallbackRequests_subset cursor.occurrence request requested)
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
        have nodeEq := input.rule3ExtendedNode_callback_local target cursor.occurrence view _ _ callbackEq excluded
        have childrenEq : (input.executableLocalizedRerootChildren cursor).mapM
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view first excluded) =
          (input.executableLocalizedRerootChildren cursor).mapM
            (input.buildLocalizedRerootExtendedShortCircuitRule3KeyExec? target view second excluded) := by
          apply mapM_congr_on
          intro child present
          obtain ⟨covered, bounded⟩ := certificate.children cursor member child present
          apply ih (certificate.height child) (by omega) child covered first second
            excluded rfl (by omega) (by omega)
        simp only [buildLocalizedRerootExtendedShortCircuitRule3KeyExec?,
          executableLocalizedRerootChildren?_eq_some, bind, Option.bind, nodeEq, childrenEq]

/-- The computed maximum rank plus one suffices for a complete two-pass frame, with all its
refusal branches preserved. All frame cursors must belong to the checked closed graph. -/
theorem Rule3DemandRankCertificate.extended_frame_stable
    {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    (certificate : input.Rule3DemandRankCertificate fuel)
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
      exact certificate.extended_key_stable target view cursor (covered cursor present)
        first second (by omega) (by omega) excluded

def Rule3DemandPlan.extended_evaluate {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)} (plan : input.Rule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target) :
    Option input.LocalizedRule3CanonicalKeyFrame :=
  input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view plan.bound roots

/-- The input-derived checked bound preserves the full optional result at every larger budget. -/
theorem Rule3DemandPlan.extended_evaluate_eq_above {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)} (plan : input.Rule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (budget : Nat) (enough : plan.bound ≤ budget) :
    plan.extended_evaluate target view = input.buildLocalizedExtendedShortCircuitRule3FrameExec? target view budget roots :=
  plan.ranks.extended_frame_stable target view roots plan.covers plan.bound budget (Nat.le_refl _) enough

/-- Successful evaluation has the existing declarative frame meaning at its computed budget. -/
theorem Rule3DemandPlan.extended_evaluate_sound {input : CertifiedLocalizedCIPInput} {fuel : Nat}
    {roots : List (input.LocalizedRerootCursor fuel)} (plan : input.Rule3DemandPlan roots)
    (target : input.LocalizedCIPOccurrence fuel) (view : input.LocalizedDependencyView target)
    (frame : input.LocalizedRule3CanonicalKeyFrame) (computed : plan.extended_evaluate target view = some frame) :
    input.DeclarativeLocalizedExtendedShortCircuitRule3Frame target view plan.bound roots frame :=
  input.buildLocalizedExtendedShortCircuitRule3FrameExec?_sound target view plan.bound roots frame computed

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
