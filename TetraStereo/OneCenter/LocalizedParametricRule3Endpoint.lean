import TetraStereo.OneCenter.LocalizedRule3ShortCircuitExecutable
import TetraStereo.OneCenter.LocalizedCompoundReachableReadCongruence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter

/-! ## The `Option` bind used by the executable `do` blocks is definitional

The `>>=` produced by a `do`-block is `Bind.bind` with the `Option` instance rather than the
primitive `Option.bind`; the two are definitionally equal, so the following helper is proved by
`rfl`, exactly as in `LocalizedRule3ShortCircuitExecutable`. -/

universe u

private theorem option_some_bind_apply
    {α β : Type u} (value : α) (continuation : α → Option β) :
    (some value : Option α) >>= continuation = continuation value :=
  rfl

/-!
# Parametric occurrence-local Rule-3 endpoint compilation over an arbitrary label reader

`LocalizedRule3ShortCircuitExecutable` compiles an occurrence-local double-bond endpoint from the
two executable reference cursors, one shared Rule-3 frame callback and two compound through-Rule-5
keys built under the *shipped restricted dependency reader*
`fun cursor => localizedDependencyLabel target view cursor`.  The present module exposes the label
source of those two compound builds as an explicit parameter, leaving every other operational
ingredient of the executable compiler untouched:

* the reference-cursor selection is exactly `localizedRule3ReferenceCursorExec?` (the executable
  cut-neighborhood expansion, the physical reference filter and the singleton check);
* the geometry is exactly the actual `endpointCursor`, the actual candidate pair
  `localizedRule3ExplicitSubstituents endpoint partner` and the actual occurrence reroot budget
  `localizedOccurrenceRerootEvaluationFuel carrierFuel`;
* the `Option` order is preserved verbatim, and in particular it is **callback-first**: the shared
  Rule-3 frame callback `rule3FrameOf [firstCursor, secondCursor]` is demanded before either
  Rules-4a--5 build, and its two-key shape gates both of them, so a refused callback or a refused
  key shape returns `none` without performing any label read.

The resulting compiler `buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?` therefore
interpolates between the shipped executable endpoint and any total label source, without adding a
solver, an evaluator or a new production path.

## Main results

* `buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_of_localizedDependencyLabel`
  — **unconditional specialization.**  Specializing the callback to the shipped restricted
  dependency reader reproduces `buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?` at *every*
  target, view, Rule-3 callback, endpoint, partner and cursor.  No chemistry hypothesis and no
  `DecidableEq` on atoms is used; the equality is a full `Option` equality, so the fail-closed
  branch agrees as well.
* `buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_of_selected` — the pinned-computation
  form: once the actual candidate pair and the two actual selected reference cursors are fixed,
  the compiler is exactly the callback-first `Option` program on those cursors.
* `buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_readersAgreeOnReachable` —
  **endpoint congruence.**  Given callback equality at the *actual selected reference pair*
  `[firstCursor, secondCursor]`, and agreement of the two readers on the *actual executable reroot
  reachable support* of each of the two selected references, the two parametric endpoints are
  exactly equal.  The key equality is derived, not assumed: it is the GREEN
  `LocalizedCompoundReachableReadCongruence`
  `buildLocalizedRerootCompoundRule45KeyWithRead?_eq_of_readersAgreeOnReachable` applied at each
  selected cursor.
* `buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_of_readersAgreeOnReachable`
  — the executable endpoint equals the parametric endpoint for *any* reader that agrees with the
  restricted dependency reader on those two actual supports.
* `localizedRule3ShortCircuitEndpointPriorityWithRead?` and its unconditional specialization, its
  four strict-branch non-eagerness lemmas (both strict atomic-root branches `Ordering.gt`/`.lt` and
  both strict complete constitutional branches `some .gt`/`some .lt`) and its congruence and
  executable corollary — the same parameterization for the short-circuit endpoint selector, with
  every branch of the executable selector retained verbatim, so the strict branches still decide
  without demanding the callback or any label read.

## What is deliberately not assumed

The congruence theorem says nothing about the *geometry* of the selected references: in particular
it does **not** assume that outward selected references stay deeper than the endpoint (the opposite
endpoint may leave the subtree).  Its only support premise is the honest unbounded executable
reachability relation `Relation.ReflTransGen (E input) selectedCursor ·` supplied separately for
each of the two actually selected cursors.

## Scope

This module concerns the existing original-root observer (the candidate supported by the Hanson
2018 original-root reading) exactly as already deployed in the imported endpoint layers.  It does
not adopt, restate or claim the 2013 normative reading, and it does not import any raw owner-context
Rule-3 source.  It proves runtime congruence and exact specialization only; it makes no source
policy claim.
-/

namespace CertifiedLocalizedCIPInput

/-! ## The parametric endpoint compiler -/

/-- Parametric form of the executable occurrence-local Rule-3 endpoint compiler.  Only the label
source of the two compound through-Rule-5 builds is generalized to an arbitrary total callback
`read`; the reference-cursor selection, the candidate pair, the occurrence reroot budget, the
Rule-3 frame callback and the full `Option`/callback-first order are the executable ones
verbatim. -/
noncomputable def buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    Option (input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel) :=
  match input.localizedRule3ExplicitSubstituents endpoint partner with
  | [first, second] => do
      let firstCursor ← input.localizedRule3ReferenceCursorExec? endpointCursor first
      let secondCursor ← input.localizedRule3ReferenceCursorExec? endpointCursor second
      let fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
      let rule3Frame ← rule3FrameOf [firstCursor, secondCursor]
      match rule3Frame.keys with
      | [firstRule3, secondRule3] => do
          let firstRule45 ← input.buildLocalizedRerootCompoundRule45KeyWithRead?
            read fuel firstCursor
          let secondRule45 ← input.buildLocalizedRerootCompoundRule45KeyWithRead?
            read fuel secondCursor
          some
            { firstCursor
              secondCursor
              rule3Frame
              endpointFrame :=
                { first
                  second
                  firstKey := { rule3 := firstRule3, rule45 := firstRule45 }
                  secondKey := { rule3 := secondRule3, rule45 := secondRule45 } } }
      | _ => none
  | _ => none

/-! ## Unconditional specialization to the shipped restricted reader -/

/-- **Unconditional specialization.**  With the callback specialized to the shipped restricted
dependency reader, the parametric endpoint is exactly the executable endpoint, at every argument
and with full `Option` agreement.  The proof rewrites only the two compound through-Rule-5 builds:
the parametric builder recovers the restricted production builder
(`buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel`) and that builder is
extensionally the executable one
(`buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?`).  No
hypothesis on the input, the callback or the candidate pair is used. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_of_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target view (fun cursor => input.localizedDependencyLabel target view cursor)
        rule3FrameOf endpoint partner endpointCursor =
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
        target view rule3FrameOf endpoint partner endpointCursor := by
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
    buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
  simp only [
    input.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_localizedDependencyLabel target view,
    input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?]
  rfl

/-! ## Pinned-computation form -/

/-- **Pinned-computation rule.**  Once the actual candidate pair and the two actual selected
reference cursors are fixed, the parametric endpoint is exactly the callback-first `Option`
program on those cursors: the shared Rule-3 callback is demanded before either compound key, and
its two-key shape gates both.  This is a computation rule for the definition, not an extra
hypothesis. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_of_selected
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target view read rule3FrameOf endpoint partner endpointCursor =
      (do
        let fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
        let rule3Frame ← rule3FrameOf [firstCursor, secondCursor]
        match rule3Frame.keys with
        | [firstRule3, secondRule3] => do
            let firstRule45 ← input.buildLocalizedRerootCompoundRule45KeyWithRead?
              read fuel firstCursor
            let secondRule45 ← input.buildLocalizedRerootCompoundRule45KeyWithRead?
              read fuel secondCursor
            some
              { firstCursor
                secondCursor
                rule3Frame
                endpointFrame :=
                  { first
                    second
                    firstKey := { rule3 := firstRule3, rule45 := firstRule45 }
                    secondKey := { rule3 := secondRule3, rule45 := secondRule45 } } }
        | _ => none) := by
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
  rw [candidates]
  dsimp only
  rw [firstSelected, option_some_bind_apply, secondSelected, option_some_bind_apply]

end CertifiedLocalizedCIPInput

namespace CertifiedLocalizedCIPInput

/-! ## Endpoint congruence from callback equality and read support -/

/-- **Endpoint congruence.**  Fix the actual candidate pair and the two actual selected reference
cursors of `endpointCursor`.  If the two Rule-3 frame callbacks agree at exactly that selected
reference pair, and the two label readers agree on every executable-reroot cursor reachable from
each of the two selected cursors, then the two parametric endpoints are exactly equal, including
the fail-closed `none` outcome.

The compound key equalities are *derived* per selected cursor by the GREEN read-support congruence
`buildLocalizedRerootCompoundRule45KeyWithRead?_eq_of_readersAgreeOnReachable`; no key equality,
comparison outcome or compiled frame is assumed.  Nothing is assumed about the geometry of the
selected references (they need not stay deeper than the endpoint). -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_readersAgreeOnReachable
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
    (callbackAgree : rule3FrameOfOne [firstCursor, secondCursor] =
      rule3FrameOfTwo [firstCursor, secondCursor])
    (readersAgreeFirst : input.LocalizedRerootReadersAgreeOnReachable
      read1 read2 firstCursor)
    (readersAgreeSecond : input.LocalizedRerootReadersAgreeOnReachable
      read1 read2 secondCursor) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target view read1 rule3FrameOfOne endpoint partner endpointCursor =
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target view read2 rule3FrameOfTwo endpoint partner endpointCursor := by
  have leftReduced :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_of_selected
      target view read1 rule3FrameOfOne endpoint partner first second endpointCursor
      firstCursor secondCursor candidates firstSelected secondSelected
  have rightReduced :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_of_selected
      target view read2 rule3FrameOfTwo endpoint partner first second endpointCursor
      firstCursor secondCursor candidates firstSelected secondSelected
  rw [leftReduced, rightReduced]
  rw [callbackAgree]
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
                      read1 read2 firstCursor readersAgreeFirst,
                    input.buildLocalizedRerootCompoundRule45KeyWithRead?_eq_of_readersAgreeOnReachable
                      read1 read2 secondCursor readersAgreeSecond]

/-- **Executable endpoint as a parametric endpoint.**  For any total label reader that agrees with
the shipped restricted dependency reader on the actual executable reachable support of each of the
two selected references, the executable endpoint equals the parametric endpoint built under that
reader.  This is the form consumed by a whole-state reader whose outward agreement has already
been established on the same support. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_of_readersAgreeOnReachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (readersAgreeFirst : input.LocalizedRerootReadersAgreeOnReachable
      (fun cursor => input.localizedDependencyLabel target view cursor) read firstCursor)
    (readersAgreeSecond : input.LocalizedRerootReadersAgreeOnReachable
      (fun cursor => input.localizedDependencyLabel target view cursor) read secondCursor) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
        target view read rule3FrameOf endpoint partner endpointCursor =
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
        target view rule3FrameOf endpoint partner endpointCursor := by
  have congruence :=
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_readersAgreeOnReachable
      target view
      (fun cursor => input.localizedDependencyLabel target view cursor) read
      rule3FrameOf rule3FrameOf endpoint partner first second endpointCursor firstCursor
      secondCursor candidates firstSelected secondSelected rfl
      readersAgreeFirst readersAgreeSecond
  rw [← congruence]
  exact
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_of_localizedDependencyLabel
      target view rule3FrameOf endpoint partner endpointCursor

/-! ## The short-circuit endpoint selector over an arbitrary reader -/

/-- Parametric form of the executable short-circuit endpoint selector.  The candidate list, the two
canonical cursor selections, the plain root comparator and the complete constitutional comparator
are the executable ones verbatim, and both strict root branches and both strict constitutional
branches are retained unchanged; only the deferred complete endpoint compiler is replaced by its
parametric form.  Consequently the label reader `read` is demanded only in the completely tied
branch, after both comparisons have failed to decide. -/
noncomputable def localizedRule3ShortCircuitEndpointPriorityWithRead?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRule3ShortCircuitEndpointResult :=
  match input.localizedRule3ExplicitSubstituents endpoint partner with
  | [first, second] => do
      let firstCursor ← input.localizedRule3ReferenceCursorExec? endpointCursor first
      let secondCursor ← input.localizedRule3ReferenceCursorExec? endpointCursor second
      match input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor with
      | Ordering.gt => some { priority := .senior first, firstCandidate := first }
      | Ordering.lt => some { priority := .senior second, firstCandidate := first }
      | Ordering.eq =>
          match input.compareLocalizedConstitutionalCursors? firstCursor secondCursor with
          | some .gt => some { priority := .senior first, firstCandidate := first }
          | some .lt => some { priority := .senior second, firstCandidate := first }
          | _ => do
              let frame ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
                target view read rule3FrameOf endpoint partner endpointCursor
              some { priority := input.localizedRule3EndpointPriority frame.endpointFrame,
                     firstCandidate := first }
  | _ => none

/-- **Unconditional specialization of the selector.**  With the reader specialized to the shipped
restricted dependency reader, the parametric selector is exactly the executable short-circuit
selector, including the four strict branches and every fail-closed answer. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_localizedRule3ShortCircuitEndpointPriorityExec?_of_localizedDependencyLabel
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view (fun cursor => input.localizedDependencyLabel target view cursor)
        rule3FrameOf endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityExec?
        target view rule3FrameOf endpoint partner endpointCursor := by
  unfold localizedRule3ShortCircuitEndpointPriorityWithRead?
    localizedRule3ShortCircuitEndpointPriorityExec?
  simp only [
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_of_localizedDependencyLabel
      target view rule3FrameOf endpoint partner endpointCursor]
  rfl

/-! ### The two strict atomic-root branches are retained -/

/-- A strict `gt` root outcome returns the senior-first result for *every* reader and *every*
Rule-3 frame callback: the strict branch never demands either the callback or a label read. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_strict_gt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (firstComputed : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondComputed : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (strict : input.compareLocalizedRerootCursorConstitutionalRoot
      firstCursor secondCursor = Ordering.gt) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read rule3FrameOf endpoint partner endpointCursor =
      some { priority := .senior first, firstCandidate := first } := by
  unfold localizedRule3ShortCircuitEndpointPriorityWithRead?
  rw [candidates]
  dsimp only
  rw [firstComputed, option_some_bind_apply, secondComputed, option_some_bind_apply, strict]

/-- A strict `lt` root outcome returns the second-candidate senior result for *every* reader and
*every* Rule-3 frame callback, again without demanding the deferred compilation. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_strict_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (firstComputed : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondComputed : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (strict : input.compareLocalizedRerootCursorConstitutionalRoot
      firstCursor secondCursor = Ordering.lt) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read rule3FrameOf endpoint partner endpointCursor =
      some { priority := .senior second, firstCandidate := first } := by
  unfold localizedRule3ShortCircuitEndpointPriorityWithRead?
  rw [candidates]
  dsimp only
  rw [firstComputed, option_some_bind_apply, secondComputed, option_some_bind_apply, strict]

/-! ### The two strict complete-constitutional branches are retained -/

/-- A strict `gt` complete constitutional comparison selects the senior reference for *every*
reader and *every* Rule-3 frame callback, even when the two atomic roots tie. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_constitutional_gt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (firstComputed : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondComputed : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (tied : input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor = .eq)
    (strict : input.compareLocalizedConstitutionalCursors?
      firstCursor secondCursor = some Ordering.gt) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read rule3FrameOf endpoint partner endpointCursor =
      some { priority := .senior first, firstCandidate := first } := by
  unfold localizedRule3ShortCircuitEndpointPriorityWithRead?
  rw [candidates]
  dsimp only
  rw [firstComputed, option_some_bind_apply, secondComputed, option_some_bind_apply, tied]
  simp [strict]

/-- A strict `lt` complete constitutional comparison selects the senior reference for *every*
reader and *every* Rule-3 frame callback, even when the two atomic roots tie. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_constitutional_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (firstComputed : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondComputed : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (tied : input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor = .eq)
    (strict : input.compareLocalizedConstitutionalCursors?
      firstCursor secondCursor = some Ordering.lt) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read rule3FrameOf endpoint partner endpointCursor =
      some { priority := .senior second, firstCandidate := first } := by
  unfold localizedRule3ShortCircuitEndpointPriorityWithRead?
  rw [candidates]
  dsimp only
  rw [firstComputed, option_some_bind_apply, secondComputed, option_some_bind_apply, tied]
  simp [strict]

/-! ### Selector congruence -/

/-- **Selector congruence.**  Callback equality at the actual selected reference pair and reader
agreement on the executable reroot reachable support of each of the two actual selected references
make the two parametric short-circuit selectors exactly equal, in every branch.  The decided strict
branches are equal because the reader is not demanded there at all; the fully tied branch reduces to
the endpoint congruence. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_readersAgreeOnReachable
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
  generalize rootComparison :
    input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor = rootOrdering
  cases rootOrdering with
  | gt => rfl
  | lt => rfl
  | eq =>
      generalize constitutionalComparison :
        input.compareLocalizedConstitutionalCursors? firstCursor secondCursor =
          constitutionalOrdering
      cases constitutionalOrdering with
      | none =>
          simp only [
            input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_readersAgreeOnReachable
              target view read1 read2 rule3FrameOfOne rule3FrameOfTwo endpoint partner first
              second endpointCursor firstCursor secondCursor candidates firstSelected
              secondSelected callbackAgree readersAgreeFirst readersAgreeSecond]
      | some ordering =>
          cases ordering with
          | lt => rfl
          | eq =>
              simp only [
                input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_readersAgreeOnReachable
                  target view read1 read2 rule3FrameOfOne rule3FrameOfTwo endpoint partner first
                  second endpointCursor firstCursor secondCursor candidates firstSelected
                  secondSelected callbackAgree readersAgreeFirst readersAgreeSecond]
          | gt => rfl

/-- **Executable selector as a parametric selector.**  For any reader agreeing with the shipped
restricted dependency reader on the executable reroot reachable support of each of the two actual
selected references, the executable short-circuit selector equals the parametric selector. -/
theorem localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_localizedRule3ShortCircuitEndpointPriorityExec?_of_readersAgreeOnReachable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (read : input.LocalizedRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner first second : input.Atom)
    (endpointCursor firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (candidates : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor first = some firstCursor)
    (secondSelected : input.localizedRule3ReferenceCursorExec?
      endpointCursor second = some secondCursor)
    (readersAgreeFirst : input.LocalizedRerootReadersAgreeOnReachable
      (fun cursor => input.localizedDependencyLabel target view cursor) read firstCursor)
    (readersAgreeSecond : input.LocalizedRerootReadersAgreeOnReachable
      (fun cursor => input.localizedDependencyLabel target view cursor) read secondCursor) :
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?
        target view read rule3FrameOf endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityExec?
        target view rule3FrameOf endpoint partner endpointCursor := by
  have congruence :=
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_readersAgreeOnReachable
      target view
      (fun cursor => input.localizedDependencyLabel target view cursor) read
      rule3FrameOf rule3FrameOf endpoint partner first second endpointCursor firstCursor
      secondCursor candidates firstSelected secondSelected rfl
      readersAgreeFirst readersAgreeSecond
  rw [← congruence]
  exact
    input.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_localizedRule3ShortCircuitEndpointPriorityExec?_of_localizedDependencyLabel
      target view rule3FrameOf endpoint partner endpointCursor

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The guarded declarations are the parametric endpoint compiler, its unconditional specialization to
the shipped restricted dependency reader, the pinned-computation rule, the endpoint congruence from
callback equality together with read support on the two actual selected references, the
executable-versus-parametric corollary for a reader agreeing with the restricted reader on that
support, and the parametric short-circuit selector with its unconditional specialization, its four
strict-branch non-eagerness lemmas (both strict atomic-root branches and both strict complete
constitutional branches) and its congruence and corollary.  `assert_kernel_only` permits exactly
`propext`, `Classical.choice` and `Quot.sound`, and rejects `sorryAx`, project axioms and
native/compiler trust. -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_of_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_of_selected
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRule3OccurrenceEndpointKeyFrameWithRead?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_localizedRule3ShortCircuitEndpointPriorityExec?_of_localizedDependencyLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_strict_gt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_strict_lt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_constitutional_gt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_constitutional_lt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_congr_of_readersAgreeOnReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule3ShortCircuitEndpointPriorityWithRead?_eq_localizedRule3ShortCircuitEndpointPriorityExec?_of_readersAgreeOnReachable
