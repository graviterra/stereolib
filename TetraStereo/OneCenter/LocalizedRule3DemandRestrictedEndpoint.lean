import TetraStereo.OneCenter.LocalizedParametricRule3Endpoint
import TetraStereo.OneCenter.LocalizedRule3EndpointCallbackDemand
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
















































































namespace TetraStereo.OneCenter

universe u

/-- The bind of a `some` value in the `Option` monad is definitionally the applied continuation.
This is the same private helper used by `LocalizedParametricRule3Endpoint`; it is repeated here
because that one is module-private. -/
private theorem option_some_bind_apply
    {α β : Type u} (value : α) (continuation : α → Option β) :
    (some value : Option α) >>= continuation = continuation value :=
  rfl

namespace CertifiedLocalizedCIPInput

/-! ## Demand-sensitive read support -/

/-- The request-local reader premise.  Two arbitrary total label readers agree on every cursor
executable-reachable from a cursor occurring in one of the retained request pairs.  The retained
requests themselves are computed by the input-derived callback-demand analysis, so structurally
suppressed references — a missing candidate pair, a refused reference selection, and, for the short
selector, a strict root decision or a strict complete constitutional decision — contribute no
request and therefore no read obligation.  The request lists do not inspect callback results; a
refused or malformed callback is outside this premise's discriminations. -/
def LocalizedRerootReadersAgreeOnRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (requests : List (List (input.LocalizedRerootCursor carrierFuel))) : Prop :=
  ∀ cursors ∈ requests, ∀ cursor ∈ cursors,
    input.LocalizedRerootReadersAgreeOnReachable read1 read2 cursor

/-- **Request-local endpoint congruence.**  The two parametric occurrence-local Rule-3 endpoint
compilers are exactly equal, with full `Option` agreement, as soon as the two frame callbacks agree
at the *requested* reference pairs of `rule3EndpointCallbackRequests` and the two readers agree on
the executable-reachable support of the cursors occurring in those requests.  When the candidate
pair or either reference selection fails, the request list is empty and the parametric computation
fails closed without any read; the equality in that branch needs no pair-specific instance of the
premises.

The callback is demanded before the two compound through-Rule-5 builds and the two-key shape still
gates both of them.  The request list is callback-independent: a refused or malformed callback is
covered by the theorem but does not by itself discharge the request-local reader premise. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_actualRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOfOne rule3FrameOfTwo :
      List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (callbackAgree : input.Rule3CallbackAgreesOn
      (input.rule3EndpointCallbackRequests endpoint partner endpointCursor)
      rule3FrameOfOne rule3FrameOfTwo)
    (readersAgree : input.LocalizedRerootReadersAgreeOnRequests read1 read2
      (input.rule3EndpointCallbackRequests endpoint partner endpointCursor)) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target view read1 rule3FrameOfOne endpoint partner endpointCursor =
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target view read2 rule3FrameOfTwo endpoint partner endpointCursor := by
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
  split
  · rename_i first second candidates
    cases firstComputed : input.localizedRule3ReferenceCursorExec? endpointCursor first with
    | none => simp
    | some firstCursor =>
      cases secondComputed : input.localizedRule3ReferenceCursorExec? endpointCursor second with
      | none => simp
      | some secondCursor =>
        have member : [firstCursor, secondCursor] ∈
            input.rule3EndpointCallbackRequests endpoint partner endpointCursor := by
          simp [rule3EndpointCallbackRequests, candidates, firstComputed, secondComputed]
        have requested := callbackAgree [firstCursor, secondCursor] member
        have firstReaders : input.LocalizedRerootReadersAgreeOnReachable read1 read2 firstCursor :=
          readersAgree [firstCursor, secondCursor] member firstCursor (by simp)
        have secondReaders : input.LocalizedRerootReadersAgreeOnReachable read1 read2 secondCursor :=
          readersAgree [firstCursor, secondCursor] member secondCursor (by simp)
        simp only [option_some_bind_apply]
        rw [requested]
        generalize callbackResult : rule3FrameOfTwo [firstCursor, secondCursor] = result
        cases result with
        | none => rfl
        | some rule3Frame =>
            simp only [option_some_bind_apply]
            generalize keysResult : rule3Frame.keys = keys
            cases keys with
            | nil => rfl
            | cons firstRule3 rest =>
                cases rest with
                | nil => rfl
                | cons secondRule3 rest =>
                    cases rest with
                    | cons thirdRule3 rest => rfl
                    | nil =>
                        simp only [
                          input.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_of_readersAgreeOnReachable
                            read1 read2 firstCursor firstReaders,
                          input.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_of_readersAgreeOnReachable
                            read1 read2 secondCursor secondReaders]
  · rfl

/-! ## Demand-sensitive selector congruence -/

/-- **Request-local selector congruence.**  The two parametric short-circuit endpoint selectors are
exactly equal, including every fail-closed `none`, from callback agreement only on
`rule3ShortEndpointCallbackRequests` and reader agreement only on the cursors occurring in those
retained requests.  The request list is input-derived and callback-independent; the strict branches
still remove the obligations entirely, but a refused or malformed callback does not.

The proof follows the executable branch structure.  A strict atomic-root outcome (`gt`/`lt`) and a
strict complete-constitutional outcome (`some .gt`/`some .lt`) are decided before any callback or
read and are discharged with no premise.  In the two fallback branches — constitutional `none` and
constitutional `some .eq` — the short request list is exactly the full endpoint request list, so
the retained pair is the actual selected pair and the branch is closed by the demand-sensitive
endpoint congruence. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_actualRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOfOne rule3FrameOfTwo :
      List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (callbackAgree : input.Rule3CallbackAgreesOn
      (input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor)
      rule3FrameOfOne rule3FrameOfTwo)
    (readersAgree : input.LocalizedRerootReadersAgreeOnRequests read1 read2
      (input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor)) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read1 rule3FrameOfOne endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read2 rule3FrameOfTwo endpoint partner endpointCursor := by
  unfold localizedRule3ShortCircuitEndpointPriorityWithRead?
  split
  · rename_i first second candidates
    cases firstComputed : input.localizedRule3ReferenceCursorExec? endpointCursor first with
    | none => simp
    | some firstCursor =>
      cases secondComputed : input.localizedRule3ReferenceCursorExec? endpointCursor second with
      | none => simp
      | some secondCursor =>
        simp only [bind, Option.bind_some]
        cases root : input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor with
        | gt => rfl
        | lt => rfl
        | eq =>
            cases constitutional : input.compareLocalizedConstitutionalCursors?
                firstCursor secondCursor with
            | some order =>
                cases order with
                | gt => rfl
                | lt => rfl
                | eq =>
                    have deferred :
                        input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor =
                          input.rule3EndpointCallbackRequests endpoint partner endpointCursor := by
                      simp [rule3ShortEndpointCallbackRequests, rule3EndpointCallbackRequests,
                        candidates, firstComputed, secondComputed, root, constitutional]
                    have endpointCallback : input.Rule3CallbackAgreesOn
                        (input.rule3EndpointCallbackRequests endpoint partner endpointCursor)
                        rule3FrameOfOne rule3FrameOfTwo := by
                      intro cursors member
                      exact callbackAgree cursors (by rw [deferred]; exact member)
                    have endpointReaders : input.LocalizedRerootReadersAgreeOnRequests
                        read1 read2
                        (input.rule3EndpointCallbackRequests endpoint partner endpointCursor) := by
                      intro cursors member cursor cursorMember
                      exact readersAgree cursors (by rw [deferred]; exact member) cursor cursorMember
                    simp only [
                      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_actualRequests
                        target view read1 read2 rule3FrameOfOne rule3FrameOfTwo endpoint partner
                        endpointCursor endpointCallback endpointReaders]
            | none =>
                have deferred :
                    input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor =
                      input.rule3EndpointCallbackRequests endpoint partner endpointCursor := by
                  simp [rule3ShortEndpointCallbackRequests, rule3EndpointCallbackRequests,
                    candidates, firstComputed, secondComputed, root, constitutional]
                have endpointCallback : input.Rule3CallbackAgreesOn
                    (input.rule3EndpointCallbackRequests endpoint partner endpointCursor)
                    rule3FrameOfOne rule3FrameOfTwo := by
                  intro cursors member
                  exact callbackAgree cursors (by rw [deferred]; exact member)
                have endpointReaders : input.LocalizedRerootReadersAgreeOnRequests
                    read1 read2
                    (input.rule3EndpointCallbackRequests endpoint partner endpointCursor) := by
                  intro cursors member cursor cursorMember
                  exact readersAgree cursors (by rw [deferred]; exact member) cursor cursorMember
                simp only [
                  input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_actualRequests
                    target view read1 read2 rule3FrameOfOne rule3FrameOfTwo endpoint partner
                    endpointCursor endpointCallback endpointReaders]
  · rfl

/-! ## Specialization to the actual executable for the restricted reader -/

/-- The actual executable endpoint compiler is the parametric endpoint compiler under the shipped
restricted dependency reader.  Consequently any reader that agrees with the restricted reader only
on the actual endpoint request cursors produces exactly the executable endpoint. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_of_actualRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (readersAgree : input.LocalizedRerootReadersAgreeOnRequests read
      (fun cursor => input.localizedDependencyLabel target view cursor)
      (input.rule3EndpointCallbackRequests endpoint partner endpointCursor)) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target view read rule3FrameOf endpoint partner endpointCursor =
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
        target view rule3FrameOf endpoint partner endpointCursor := by
  rw [input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_actualRequests
    target view read (fun cursor => input.localizedDependencyLabel target view cursor)
    rule3FrameOf rule3FrameOf endpoint partner endpointCursor
    (by intro cursors _member; rfl) readersAgree]
  exact
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_of_localizedDependencyLabel
      target view rule3FrameOf endpoint partner endpointCursor

/-- The actual executable short-circuit selector is the parametric selector under the shipped
restricted dependency reader.  Any reader agreeing with the restricted reader only on the actual
short-selector request cursors therefore produces exactly the executable selector, in every
branch. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_localizedRule3ShortCircuitEndpointPriorityExec?_of_actualRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (readersAgree : input.LocalizedRerootReadersAgreeOnRequests read
      (fun cursor => input.localizedDependencyLabel target view cursor)
      (input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor)) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read rule3FrameOf endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityExec?
        target view rule3FrameOf endpoint partner endpointCursor := by
  rw [input.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_actualRequests
    target view read (fun cursor => input.localizedDependencyLabel target view cursor)
    rule3FrameOf rule3FrameOf endpoint partner endpointCursor
    (by intro cursors _member; rfl) readersAgree]
  exact
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_localizedRule3ShortCircuitEndpointPriorityExec?_of_localizedDependencyLabel
      target view rule3FrameOf endpoint partner endpointCursor

/-! ## Explicit branch split at the actual retained pair

The four strict branches are decided before either the callback or a label read is demanded.  The
lemmas below record the corresponding *congruence* form: the two selectors agree with no premise at
all on the readers or on the callbacks, once the actual candidate pair, the two actual selected
cursor references and the strict comparison outcome are fixed.  They are the strict-branch halves
of the selector split; the fallback lemmas are the two remaining branches. -/

theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_root_gt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOfOne rule3FrameOfTwo :
      List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (strict : input.compareLocalizedRerootCursorConstitutionalRoot
      firstCursor secondCursor = Ordering.gt) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read1 rule3FrameOfOne endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read2 rule3FrameOfTwo endpoint partner endpointCursor := by
  rw [input.localizedRule3ShortCircuitEndpointPriorityWithRead?_strict_gt
        target view read1 rule3FrameOfOne endpoint partner first second endpointCursor
        candidates firstCursor secondCursor firstSelected secondSelected strict,
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?_strict_gt
        target view read2 rule3FrameOfTwo endpoint partner first second endpointCursor
        candidates firstCursor secondCursor firstSelected secondSelected strict]

theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_root_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOfOne rule3FrameOfTwo :
      List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (strict : input.compareLocalizedRerootCursorConstitutionalRoot
      firstCursor secondCursor = Ordering.lt) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read1 rule3FrameOfOne endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read2 rule3FrameOfTwo endpoint partner endpointCursor := by
  rw [input.localizedRule3ShortCircuitEndpointPriorityWithRead?_strict_lt
        target view read1 rule3FrameOfOne endpoint partner first second endpointCursor
        candidates firstCursor secondCursor firstSelected secondSelected strict,
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?_strict_lt
        target view read2 rule3FrameOfTwo endpoint partner first second endpointCursor
        candidates firstCursor secondCursor firstSelected secondSelected strict]

theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_constitutional_gt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOfOne rule3FrameOfTwo :
      List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (tied : input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor = .eq)
    (strict : input.compareLocalizedConstitutionalCursors?
      firstCursor secondCursor = some Ordering.gt) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read1 rule3FrameOfOne endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read2 rule3FrameOfTwo endpoint partner endpointCursor := by
  rw [input.localizedRule3ShortCircuitEndpointPriorityWithRead?_constitutional_gt
        target view read1 rule3FrameOfOne endpoint partner first second endpointCursor
        candidates firstCursor secondCursor firstSelected secondSelected tied strict,
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?_constitutional_gt
        target view read2 rule3FrameOfTwo endpoint partner first second endpointCursor
        candidates firstCursor secondCursor firstSelected secondSelected tied strict]

theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_constitutional_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOfOne rule3FrameOfTwo :
      List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (tied : input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor = .eq)
    (strict : input.compareLocalizedConstitutionalCursors?
      firstCursor secondCursor = some Ordering.lt) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read1 rule3FrameOfOne endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read2 rule3FrameOfTwo endpoint partner endpointCursor := by
  rw [input.localizedRule3ShortCircuitEndpointPriorityWithRead?_constitutional_lt
        target view read1 rule3FrameOfOne endpoint partner first second endpointCursor
        candidates firstCursor secondCursor firstSelected secondSelected tied strict,
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?_constitutional_lt
        target view read2 rule3FrameOfTwo endpoint partner first second endpointCursor
        candidates firstCursor secondCursor firstSelected secondSelected tied strict]

/-- **Fallback congruence, constitutional refusal (`none`).**  On the fully tied atomic-root
branch with a refused complete constitutional comparison, the two selectors agree as soon as the
callbacks agree at the actual retained pair and the readers agree on the executable-reachable
support of the two actual selected references.  This is exactly the existing full endpoint
congruence at that pair; no other branch is inspected. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_fallback_congr_of_none
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOfOne rule3FrameOfTwo :
      List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (tied : input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor = .eq)
    (constitutional : input.compareLocalizedConstitutionalCursors?
      firstCursor secondCursor = none)
    (callbackAgree : rule3FrameOfOne [firstCursor, secondCursor] =
      rule3FrameOfTwo [firstCursor, secondCursor])
    (readersAgreeFirst : input.LocalizedRerootReadersAgreeOnReachable
      read1 read2 firstCursor)
    (readersAgreeSecond : input.LocalizedRerootReadersAgreeOnReachable
      read1 read2 secondCursor) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read1 rule3FrameOfOne endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read2 rule3FrameOfTwo endpoint partner endpointCursor := by
  unfold localizedRule3ShortCircuitEndpointPriorityWithRead?
  rw [candidates]
  dsimp only
  simp only [firstSelected, option_some_bind_apply, secondSelected, option_some_bind_apply]
  rw [tied, constitutional]
  dsimp only
  simp only [
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_readersAgreeOnReachable
      target view read1 read2 rule3FrameOfOne rule3FrameOfTwo endpoint partner first second
      endpointCursor firstCursor secondCursor candidates firstSelected secondSelected
      callbackAgree readersAgreeFirst readersAgreeSecond]

/-- **Fallback congruence, complete constitutional tie (`some .eq`).**  The same reduction at the
actual retained pair when the complete constitutional comparison ties instead of refusing. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_fallback_congr_of_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOfOne rule3FrameOfTwo :
      List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (tied : input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor = .eq)
    (constitutional : input.compareLocalizedConstitutionalCursors?
      firstCursor secondCursor = some Ordering.eq)
    (callbackAgree : rule3FrameOfOne [firstCursor, secondCursor] =
      rule3FrameOfTwo [firstCursor, secondCursor])
    (readersAgreeFirst : input.LocalizedRerootReadersAgreeOnReachable
      read1 read2 firstCursor)
    (readersAgreeSecond : input.LocalizedRerootReadersAgreeOnReachable
      read1 read2 secondCursor) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read1 rule3FrameOfOne endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read2 rule3FrameOfTwo endpoint partner endpointCursor := by
  unfold localizedRule3ShortCircuitEndpointPriorityWithRead?
  rw [candidates]
  dsimp only
  simp only [firstSelected, option_some_bind_apply, secondSelected, option_some_bind_apply]
  rw [tied, constitutional]
  dsimp only
  simp only [
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_readersAgreeOnReachable
      target view read1 read2 rule3FrameOfOne rule3FrameOfTwo endpoint partner first second
      endpointCursor firstCursor secondCursor candidates firstSelected secondSelected
      callbackAgree readersAgreeFirst readersAgreeSecond]

/-- **Fallback congruence.**  Both fallback outcomes — a refused complete constitutional
comparison and an exact complete constitutional tie — with the actual candidate pair, the actual
selected cursors, the callback equality at that retained pair and the existing full endpoint
congruence as the only inputs. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_fallback_congr
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOfOne rule3FrameOfTwo :
      List (input.LocalizedRerootCursor carrierFuel) →
        Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (tied : input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor = .eq)
    (fallback : input.compareLocalizedConstitutionalCursors? firstCursor secondCursor = none ∨
      input.compareLocalizedConstitutionalCursors? firstCursor secondCursor =
        some Ordering.eq)
    (callbackAgree : rule3FrameOfOne [firstCursor, secondCursor] =
      rule3FrameOfTwo [firstCursor, secondCursor])
    (readersAgreeFirst : input.LocalizedRerootReadersAgreeOnReachable
      read1 read2 firstCursor)
    (readersAgreeSecond : input.LocalizedRerootReadersAgreeOnReachable
      read1 read2 secondCursor) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read1 rule3FrameOfOne endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read2 rule3FrameOfTwo endpoint partner endpointCursor := by
  rcases fallback with refused | tiedConstitutional
  · exact
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?_fallback_congr_of_none
        target view read1 read2 rule3FrameOfOne rule3FrameOfTwo endpoint partner first second
        endpointCursor firstCursor secondCursor candidates firstSelected secondSelected tied
        refused callbackAgree readersAgreeFirst readersAgreeSecond
  · exact
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?_fallback_congr_of_eq
        target view read1 read2 rule3FrameOfOne rule3FrameOfTwo endpoint partner first second
        endpointCursor firstCursor secondCursor candidates firstSelected secondSelected tied
        tiedConstitutional callbackAgree readersAgreeFirst readersAgreeSecond









/-- Locality of every cursor occurring in a finite list of retained request pairs, relative to one
common starting cursor. -/
def Rule3RequestsReachableFrom
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first : input.LocalizedRerootCursor carrierFuel)
    (requests : List (List (input.LocalizedRerootCursor carrierFuel))) : Prop :=
  ∀ cursors ∈ requests, ∀ cursor ∈ cursors,
    Relation.ReflTransGen (E input) first cursor

/-- **Whole-state read support from outward locality.**  If every cursor occurring in the retained
requests is executable-reachable from an outward cursor of the target, then the unrestricted
whole-state reader agrees with the restricted dependency reader on the demand-sensitive read
support of those requests.  Each reached cursor is outward by `outward_reachable_cursor`, hence a
strict depth dependency of the target, and `localizedDependencyLabel_eq_state_of_dependency`
identifies the two reads. -/
theorem LocalizedRerootReadersAgreeOnRequests_of_outwardReachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (first : input.LocalizedRerootCursor carrierFuel)
    (firstOutward : input.OutwardRerootCursor target first)
    (requests : List (List (input.LocalizedRerootCursor carrierFuel)))
    (locality : input.Rule3RequestsReachableFrom first requests) :
    input.LocalizedRerootReadersAgreeOnRequests
      (fun cursor => state cursor.occurrence)
      (fun cursor => input.localizedDependencyLabel target
        (input.localizedDependencyView state target) cursor)
      requests := by
  intro cursors member cursor cursorMember child reachable
  have requestReachable : Relation.ReflTransGen (E input) first cursor :=
    locality cursors member cursor cursorMember
  have childReachable : Relation.ReflTransGen (E input) first child :=
    requestReachable.trans reachable
  have outward : input.OutwardRerootCursor target child :=
    input.outward_reachable_cursor target first child firstOutward childReachable
  exact
    (input.localizedDependencyLabel_eq_state_of_dependency target state child
      outward.2.1).symm

/-- **Whole-state endpoint agreement.**  Under outward locality of the actual endpoint request
cursors, the endpoint compiled from the whole auxiliary state equals the endpoint compiled from the
restricted dependency view, with the same Rule-3 callback and full `Option` agreement. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_wholeState_eq_restricted_of_outwardRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (first : input.LocalizedRerootCursor carrierFuel)
    (firstOutward : input.OutwardRerootCursor target first)
    (locality : input.Rule3RequestsReachableFrom first
      (input.rule3EndpointCallbackRequests endpoint partner endpointCursor)) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target view (fun cursor => state cursor.occurrence) rule3FrameOf endpoint partner
        endpointCursor =
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target view
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor)
        rule3FrameOf endpoint partner endpointCursor :=
  input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_actualRequests
    target view
    (fun cursor => state cursor.occurrence)
    (fun cursor => input.localizedDependencyLabel target
      (input.localizedDependencyView state target) cursor)
    rule3FrameOf rule3FrameOf endpoint partner endpointCursor
    (by intro cursors _member; rfl)
    (input.LocalizedRerootReadersAgreeOnRequests_of_outwardReachable
      target state first firstOutward _ locality)

/-- **Whole-state endpoint agreement against the actual executable.**  Under the same outward
locality the whole-state parametric endpoint is exactly the executable endpoint, which is the
restricted dependency build. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_wholeState_eq_Exec?_of_outwardRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (first : input.LocalizedRerootCursor carrierFuel)
    (firstOutward : input.OutwardRerootCursor target first)
    (locality : input.Rule3RequestsReachableFrom first
      (input.rule3EndpointCallbackRequests endpoint partner endpointCursor)) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target (input.localizedDependencyView state target)
        (fun cursor => state cursor.occurrence) rule3FrameOf endpoint partner endpointCursor =
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
        target (input.localizedDependencyView state target) rule3FrameOf endpoint partner
        endpointCursor := by
  rw [input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_wholeState_eq_restricted_of_outwardRequests
    target (input.localizedDependencyView state target) state rule3FrameOf endpoint partner
    endpointCursor first firstOutward locality]
  exact
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_of_localizedDependencyLabel
      target (input.localizedDependencyView state target) rule3FrameOf endpoint partner endpointCursor

/-- **Whole-state selector agreement.**  Under outward locality of the actual short-selector
request cursors, the selector over the whole auxiliary state equals the selector over the
restricted dependency view, with the same Rule-3 callback and full `Option` agreement. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_restricted_of_outwardRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (first : input.LocalizedRerootCursor carrierFuel)
    (firstOutward : input.OutwardRerootCursor target first)
    (locality : input.Rule3RequestsReachableFrom first
      (input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor)) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view (fun cursor => state cursor.occurrence) rule3FrameOf endpoint partner
        endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor)
        rule3FrameOf endpoint partner endpointCursor :=
  input.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_actualRequests
    target view
    (fun cursor => state cursor.occurrence)
    (fun cursor => input.localizedDependencyLabel target
      (input.localizedDependencyView state target) cursor)
    rule3FrameOf rule3FrameOf endpoint partner endpointCursor
    (by intro cursors _member; rfl)
    (input.LocalizedRerootReadersAgreeOnRequests_of_outwardReachable
      target state first firstOutward _ locality)

/-- **Whole-state selector agreement against the actual executable.**  Under outward locality the
whole-state parametric selector is exactly the executable short-circuit selector. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_outwardRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (first : input.LocalizedRerootCursor carrierFuel)
    (firstOutward : input.OutwardRerootCursor target first)
    (locality : input.Rule3RequestsReachableFrom first
      (input.rule3ShortEndpointCallbackRequests endpoint partner endpointCursor)) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target (input.localizedDependencyView state target)
        (fun cursor => state cursor.occurrence) rule3FrameOf endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityExec?
        target (input.localizedDependencyView state target) rule3FrameOf endpoint partner
        endpointCursor := by
  rw [input.localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_restricted_of_outwardRequests
    target (input.localizedDependencyView state target) state rule3FrameOf endpoint partner
    endpointCursor first firstOutward locality]
  exact
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_localizedRule3ShortCircuitEndpointPriorityExec?_of_localizedDependencyLabel
      target (input.localizedDependencyView state target) rule3FrameOf endpoint partner endpointCursor

/-! ## Parametric spatial wrapper

This is the executable occurrence wrapper with both endpoint selectors replaced by their parametric
forms.  The physical topology recovery, the two endpoint arguments, the callback-first order and
the geometry unit are the executable ones verbatim; the physical occurrence and the descriptor
target remain separate parameters. -/

noncomputable def localizedRule3ShortCircuitSpatialUnitWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    Option (input.LocalizedRule3ShortCircuitSpatialResult carrierFuel) := do
  let topology ← input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence
  let leftEndpoint ← input.localizedRule3ShortCircuitEndpointPriorityWithRead?
    target view read rule3FrameOf topology.left topology.right topology.leftCursor
  let rightEndpoint ← input.localizedRule3ShortCircuitEndpointPriorityWithRead?
    target view read rule3FrameOf topology.right topology.left topology.rightCursor
  let unit ← input.localizedRule3ShortCircuitSpatialUnit?
    topology.left topology.right leftEndpoint rightEndpoint
  some { topology, leftEndpoint, rightEndpoint, unit }

/-- The parametric spatial wrapper specialized to the shipped restricted dependency reader is
exactly the executable spatial wrapper, including every fail-closed `none` and the shared geometry
unit. -/
theorem localizedRule3ShortCircuitSpatialUnitWithRead?_eq_localizedRule3ShortCircuitSpatialUnitWithExec?_of_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame) :
    input.localizedRule3ShortCircuitSpatialUnitWithRead? target occurrence view
        (fun cursor => input.localizedDependencyLabel target view cursor) rule3FrameOf =
      input.localizedRule3ShortCircuitSpatialUnitWithExec?
        target occurrence view rule3FrameOf := by
  unfold localizedRule3ShortCircuitSpatialUnitWithRead?
    localizedRule3ShortCircuitSpatialUnitWithExec?
  simp only [
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_localizedRule3ShortCircuitEndpointPriorityExec?_of_localizedDependencyLabel]

/-- **Request-local spatial agreement.**  The two parametric spatial wrappers are exactly equal as
soon as the two callbacks agree on the retained spatial requests and the two readers agree on the
executable-reachable support of every cursor occurring in them.  The topology recovery and the
geometry unit are shared, so the equality is decided entirely by the two endpoint selectors. -/
theorem localizedRule3ShortCircuitSpatialUnitWithRead?_congr_of_actualRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read1 read2 : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (before after : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (callbackAgree : input.Rule3CallbackAgreesOn
      (input.rule3ShortSpatialCallbackRequests occurrence) before after)
    (readersAgree : input.LocalizedRerootReadersAgreeOnRequests read1 read2
      (input.rule3ShortSpatialCallbackRequests occurrence)) :
    input.localizedRule3ShortCircuitSpatialUnitWithRead?
        target occurrence view read1 before =
      input.localizedRule3ShortCircuitSpatialUnitWithRead?
        target occurrence view read2 after := by
  unfold localizedRule3ShortCircuitSpatialUnitWithRead?
  cases found : input.localizedRule3PhysicalEndpointCursorFrameExec? occurrence with
  | none => simp
  | some topology =>
      have leftCallback : input.Rule3CallbackAgreesOn
          (input.rule3ShortEndpointCallbackRequests topology.left topology.right
            topology.leftCursor) before after := by
        intro cursors member
        exact callbackAgree cursors
          (by simp [rule3ShortSpatialCallbackRequests, found, member])
      have leftReaders : input.LocalizedRerootReadersAgreeOnRequests read1 read2
          (input.rule3ShortEndpointCallbackRequests topology.left topology.right
            topology.leftCursor) := by
        intro cursors member cursor cursorMember
        exact readersAgree cursors
          (by simp [rule3ShortSpatialCallbackRequests, found, member]) cursor cursorMember
      have rightCallback : input.Rule3CallbackAgreesOn
          (input.rule3ShortEndpointCallbackRequests topology.right topology.left
            topology.rightCursor) before after := by
        intro cursors member
        exact callbackAgree cursors
          (by simp [rule3ShortSpatialCallbackRequests, found, member])
      have rightReaders : input.LocalizedRerootReadersAgreeOnRequests read1 read2
          (input.rule3ShortEndpointCallbackRequests topology.right topology.left
            topology.rightCursor) := by
        intro cursors member cursor cursorMember
        exact readersAgree cursors
          (by simp [rule3ShortSpatialCallbackRequests, found, member]) cursor cursorMember
      simp only [option_some_bind_apply,
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_actualRequests
          target view read1 read2 before after topology.left topology.right
          topology.leftCursor leftCallback leftReaders,
        input.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_actualRequests
          target view read1 read2 before after topology.right topology.left
          topology.rightCursor rightCallback rightReaders]

/-- The actual executable spatial wrapper is the parametric wrapper under the shipped restricted
dependency reader.  A reader that agrees with the restricted reader only on the actual spatial
request cursors therefore produces exactly the executable spatial result. -/
theorem localizedRule3ShortCircuitSpatialUnitWithRead?_eq_localizedRule3ShortCircuitSpatialUnitWithExec?_of_actualRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (readersAgree : input.LocalizedRerootReadersAgreeOnRequests read
      (fun cursor => input.localizedDependencyLabel target view cursor)
      (input.rule3ShortSpatialCallbackRequests occurrence)) :
    input.localizedRule3ShortCircuitSpatialUnitWithRead?
        target occurrence view read rule3FrameOf =
      input.localizedRule3ShortCircuitSpatialUnitWithExec?
        target occurrence view rule3FrameOf := by
  rw [input.localizedRule3ShortCircuitSpatialUnitWithRead?_congr_of_actualRequests
    target occurrence view read (fun cursor => input.localizedDependencyLabel target view cursor)
    rule3FrameOf rule3FrameOf (by intro cursors _member; rfl) readersAgree]
  exact
    input.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_localizedRule3ShortCircuitSpatialUnitWithExec?_of_localizedDependencyLabel
      target occurrence view rule3FrameOf

/-- **Whole-state spatial agreement.**  Under outward locality of the retained spatial request
cursors, the whole-state parametric spatial wrapper equals the restricted one with the same Rule-3
callback.  The physical occurrence is not identified with the original descriptor target. -/
theorem localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_restricted_of_outwardRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (first : input.LocalizedRerootCursor carrierFuel)
    (firstOutward : input.OutwardRerootCursor target first)
    (locality : input.Rule3RequestsReachableFrom first
      (input.rule3ShortSpatialCallbackRequests occurrence)) :
    input.localizedRule3ShortCircuitSpatialUnitWithRead?
        target occurrence view (fun cursor => state cursor.occurrence) rule3FrameOf =
      input.localizedRule3ShortCircuitSpatialUnitWithRead?
        target occurrence view
        (fun cursor => input.localizedDependencyLabel target
          (input.localizedDependencyView state target) cursor)
        rule3FrameOf :=
  input.localizedRule3ShortCircuitSpatialUnitWithRead?_congr_of_actualRequests
    target occurrence view
    (fun cursor => state cursor.occurrence)
    (fun cursor => input.localizedDependencyLabel target
      (input.localizedDependencyView state target) cursor)
    rule3FrameOf rule3FrameOf
    (by intro cursors _member; rfl)
    (input.LocalizedRerootReadersAgreeOnRequests_of_outwardReachable
      target state first firstOutward _ locality)

/-- **Whole-state spatial agreement against the actual executable.**  Under outward locality the
whole-state parametric spatial wrapper is exactly the executable spatial wrapper. -/
theorem localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_Exec?_of_outwardRequests
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (state : input.LocalizedAuxiliaryState carrierFuel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (first : input.LocalizedRerootCursor carrierFuel)
    (firstOutward : input.OutwardRerootCursor target first)
    (locality : input.Rule3RequestsReachableFrom first
      (input.rule3ShortSpatialCallbackRequests occurrence)) :
    input.localizedRule3ShortCircuitSpatialUnitWithRead?
        target occurrence (input.localizedDependencyView state target)
        (fun cursor => state cursor.occurrence) rule3FrameOf =
      input.localizedRule3ShortCircuitSpatialUnitWithExec?
        target occurrence (input.localizedDependencyView state target) rule3FrameOf := by
  rw [input.localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_restricted_of_outwardRequests
    target occurrence (input.localizedDependencyView state target) state rule3FrameOf
    first firstOutward locality]
  exact
    input.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_localizedRule3ShortCircuitSpatialUnitWithExec?_of_localizedDependencyLabel
      target occurrence (input.localizedDependencyView state target) rule3FrameOf

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootReadersAgreeOnRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_actualRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_actualRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_of_actualRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_localizedRule3ShortCircuitEndpointPriorityExec?_of_actualRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_root_gt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_root_lt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_constitutional_gt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_constitutional_lt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_fallback_congr_of_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_fallback_congr_of_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_fallback_congr
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.Rule3RequestsReachableFrom
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedRerootReadersAgreeOnRequests_of_outwardReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_wholeState_eq_restricted_of_outwardRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_wholeState_eq_Exec?_of_outwardRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_restricted_of_outwardRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_wholeState_eq_Exec?_of_outwardRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_localizedRule3ShortCircuitSpatialUnitWithExec?_of_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithRead?_congr_of_actualRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithRead?_eq_localizedRule3ShortCircuitSpatialUnitWithExec?_of_actualRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_restricted_of_outwardRequests
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitSpatialUnitWithRead?_wholeState_eq_Exec?_of_outwardRequests
