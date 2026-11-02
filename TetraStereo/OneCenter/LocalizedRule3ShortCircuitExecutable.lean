import TetraStereo.OneCenter.LocalizedRule3ShortCircuitEndpoint
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable
import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Executable

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Executable occurrence-local Rule-3 reference, endpoint and short-circuit compilers

`LocalizedRule3OccurrenceReferenceCursor` defines the fail-closed occurrence-local reference lookup
`localizedRule3ReferenceCursor?`, whose only non-executable ingredient is the optional cut-neighborhood
expansion `localizedRerootChildren?`; `LocalizedRerootChildrenExecutable` proves that expansion
extensionally equal to the total `executableLocalizedRerootChildren?`.
`LocalizedRule3ParameterizedEndpoint` then compiles a descriptor-bearing endpoint from two such
reference cursors and the compound Rules-4b--5 key compiler `buildLocalizedRerootCompoundRule45Key?`,
whose executable twin is provided by `LocalizedRerootCompoundRule45Executable`.  Finally
`LocalizedRule3ShortCircuitEndpoint` decides a strict first-sphere root difference before compiling
the complete frame.

This module supplies the three plain executable twins

* `localizedRule3ReferenceCursorExec?`, replacing the cursor reader `localizedRerootChildren?` by
  `executableLocalizedRerootChildren?`;
* `buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?`, replacing additionally the cursor reader
  and the two compound Rule-4a--5 sub-compilers by their executable twins; and
* `localizedRule3ShortCircuitEndpointPriorityExec?`, replacing the cursor reader and the deferred
  complete compiler by the corresponding executable twins.

All three keep the original parameters, the original match structure and the original fail-closed
`none` answers verbatim, and all three are proved extensionally equal to their originals at *every*
argument as `Option` equalities, using only the previously established equalities
`localizedRerootChildren?_eq_some_executable` and
`buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?`.  No chemistry
hypothesis, no `DecidableEq` on atoms, and no other input is required: the equalities hold
unconditionally, and the fail-closed branches on both sides agree.

The strict branch of the short-circuit twin is *not* eager: the complete endpoint compiler is invoked
only inside the `Ordering.eq` branch of the root comparison, exactly as in the original definition.
`localizedRule3ShortCircuitEndpointPriorityExec?_strict_gt` (and its `lt` twin) record this formally:
a strict root outcome produces the corresponding senior-first result with no hypothesis whatsoever on
the Rule-3 frame callback `rule3FrameOf`, i.e. the deferred frame is never demanded on a decided strict
case.
-/

namespace CertifiedLocalizedCIPInput

/-- Executable twin of `localizedRule3ReferenceCursor?`.  The only change is the replacement of the
fail-closed optional expansion `localizedRerootChildren?` by the total executable reader
`executableLocalizedRerootChildren?`; the candidate filter and the singleton check are untouched. -/
def localizedRule3ReferenceCursorExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom) : Option (input.LocalizedRerootCursor fuel) := do
  let children ← input.executableLocalizedRerootChildren? endpointCursor
  match input.localizedRule3ReferenceCursorCandidates children reference with
  | [cursor] => some cursor
  | _ => none

/-- The executable reference lookup returns exactly the original optional lookup at every cursor and
reference, including every `none` answer.  Only the upstream equality between the optional and the
total executable cut-neighborhood expansion is used. -/
theorem localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (endpointCursor : input.LocalizedRerootCursor fuel)
    (reference : input.Atom) :
    input.localizedRule3ReferenceCursor? endpointCursor reference =
      input.localizedRule3ReferenceCursorExec? endpointCursor reference := by
  unfold localizedRule3ReferenceCursor? localizedRule3ReferenceCursorExec?
  simp only [input.localizedRerootChildren?_eq_some_executable,
    input.executableLocalizedRerootChildren?_eq_some]
  rfl

/-- Executable twin of `buildLocalizedRule3OccurrenceEndpointKeyFrameWith?`.  Every call to the
occurrence-local reference lookup and every call to the compound Rules-4b--5 compiler is replaced by
its executable twin; the explicit Rule-3 frame callback `rule3FrameOf`, the candidate list, the key
projection and the two-key check are preserved verbatim. -/
def buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
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
          let firstRule45 ← input.buildLocalizedRerootCompoundRule45KeyExec?
            target view fuel firstCursor
          let secondRule45 ← input.buildLocalizedRerootCompoundRule45KeyExec?
            target view fuel secondCursor
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

/-- The executable endpoint compiler returns exactly the original parameterized endpoint compiler at
every target, view, callback, endpoint, partner and cursor.  Only the two upstream equalities for the
reference reader and for the compound Rules-4a--5 compiler are used, so the equality is unconditional
and the fail-closed answers agree. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
        target view rule3FrameOf endpoint partner endpointCursor =
      input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
        target view rule3FrameOf endpoint partner endpointCursor := by
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
    buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
  simp only [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?,
    input.buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?]
  rfl

/-- Executable twin of `localizedRule3ShortCircuitEndpointPriority?`.  The candidate list, the two
canonical cursor selections and the plain root comparator are unchanged; only the cursor reader and
the deferred complete endpoint compiler are replaced by their executable twins.  The complete compiler
is still reached *only* in the `Ordering.eq` branch, so a strict `gt`/`lt` root outcome returns
without ever demanding the deferred frame. -/
def localizedRule3ShortCircuitEndpointPriorityExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
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
              let frame ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?
                target view rule3FrameOf endpoint partner endpointCursor
              some { priority := input.localizedRule3EndpointPriority frame.endpointFrame,
                     firstCandidate := first }
  | _ => none

/-- The executable short-circuit endpoint selector returns exactly the original at every target, view,
callback, endpoint, partner and cursor, including every `none` answer.  Only the two lower equalities
are used, so no chemistry input is required and the deferred branch agrees on both sides. -/
theorem localizedRule3ShortCircuitEndpointPriority?_eq_localizedRule3ShortCircuitEndpointPriorityExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    input.localizedRule3ShortCircuitEndpointPriority?
        target view rule3FrameOf endpoint partner endpointCursor =
      input.localizedRule3ShortCircuitEndpointPriorityExec?
        target view rule3FrameOf endpoint partner endpointCursor := by
  unfold localizedRule3ShortCircuitEndpointPriority?
    localizedRule3ShortCircuitEndpointPriorityExec?
  simp only [input.localizedRule3ReferenceCursor?_eq_localizedRule3ReferenceCursorExec?,
    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_eq_buildLocalizedRule3OccurrenceEndpointKeyFrameWithExec?]
  rfl

universe u

/-- The bind of a `some` value in the `Option` monad is definitionally the applied continuation.
The statement uses the `>>=` notation actually produced by `do`-blocks, whose head is `Bind.bind` with
the `Option` instance rather than the primitive `Option.bind`; the two are definitionally equal, so
this is proved by `rfl`. -/
private theorem option_some_bind_apply
    {α β : Type u} (value : α) (continuation : α → Option β) :
    (some value : Option α) >>= continuation = continuation value :=
  rfl

/-- Non-eagerness of the strict branch, stated for the executable twin: whenever the endpoint has the
exact candidate pair and both canonical cursors are found, a strict `gt` root outcome returns the
senior-first result *for every* Rule-3 frame callback `rule3FrameOf`.  No hypothesis constrains the
callback, so the deferred complete compilation is never demanded on a decided strict case. -/
theorem localizedRule3ShortCircuitEndpointPriorityExec?_strict_gt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
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
    input.localizedRule3ShortCircuitEndpointPriorityExec?
        target view rule3FrameOf endpoint partner endpointCursor =
      some { priority := .senior first, firstCandidate := first } := by
  unfold localizedRule3ShortCircuitEndpointPriorityExec?
  rw [candidates]
  dsimp only
  rw [firstComputed, option_some_bind_apply, secondComputed, option_some_bind_apply, strict]

/-- Symmetric non-eagerness of the strict branch: a strict `lt` root outcome returns the
second-candidate senior result, again for *every* Rule-3 frame callback, so no deferred compilation is
demanded when the first sphere already decides the comparison. -/
theorem localizedRule3ShortCircuitEndpointPriorityExec?_strict_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
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
    input.localizedRule3ShortCircuitEndpointPriorityExec?
        target view rule3FrameOf endpoint partner endpointCursor =
      some { priority := .senior second, firstCandidate := first } := by
  unfold localizedRule3ShortCircuitEndpointPriorityExec?
  rw [candidates]
  dsimp only
  rw [firstComputed, option_some_bind_apply, secondComputed, option_some_bind_apply, strict]

/-- A strict complete constitutional comparison selects the senior reference without invoking
the stereo callback, even when the two atomic roots tie. -/
theorem localizedRule3ShortCircuitEndpointPriorityExec?_constitutional_gt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
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
    input.localizedRule3ShortCircuitEndpointPriorityExec?
        target view rule3FrameOf endpoint partner endpointCursor =
      some { priority := .senior first, firstCandidate := first } := by
  unfold localizedRule3ShortCircuitEndpointPriorityExec?
  rw [candidates]
  dsimp only
  rw [firstComputed, option_some_bind_apply, secondComputed, option_some_bind_apply, tied]
  simp [strict]

/-- A strict complete constitutional comparison selects the senior reference without invoking
the stereo callback, even when the two atomic roots tie. -/
theorem localizedRule3ShortCircuitEndpointPriorityExec?_constitutional_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
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
    input.localizedRule3ShortCircuitEndpointPriorityExec?
        target view rule3FrameOf endpoint partner endpointCursor =
      some { priority := .senior second, firstCandidate := first } := by
  unfold localizedRule3ShortCircuitEndpointPriorityExec?
  rw [candidates]
  dsimp only
  rw [firstComputed, option_some_bind_apply, secondComputed, option_some_bind_apply, tied]
  simp [strict]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
