import TetraStereo.OneCenter.LocalizedRule3EndpointConstitutionalPriority
import TetraStereo.OneCenter.LocalizedRule3ParameterizedEndpoint
import TetraStereo.OneCenter.LocalizedConstitutionalExecutable

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-! Endpoint priority first checks strict atomic roots, then complete constitutional keys at the
proved structural budget. Constitutional ties and failed attempts retain the full stereo callback.
The independent relation records pure constitutional derivations, never a fabricated stereo frame. -/

namespace CertifiedLocalizedCIPInput

/-- The short-circuit endpoint result: a priority plus the inert first-candidate witness. -/
structure LocalizedRule3ShortCircuitEndpointResult
    (input : CertifiedLocalizedCIPInput) where
  priority : input.LocalizedRule3EndpointPriority
  firstCandidate : input.Atom
  deriving DecidableEq, Repr



noncomputable def localizedRule3ShortCircuitEndpointPriority?
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
      let firstCursor ← input.localizedRule3ReferenceCursor? endpointCursor first
      let secondCursor ← input.localizedRule3ReferenceCursor? endpointCursor second
      match input.compareLocalizedRerootCursorConstitutionalRoot firstCursor secondCursor with
      | Ordering.gt => some { priority := .senior first, firstCandidate := first }
      | Ordering.lt => some { priority := .senior second, firstCandidate := first }
      | Ordering.eq =>
          match input.compareLocalizedConstitutionalCursors? firstCursor secondCursor with
          | some .gt => some { priority := .senior first, firstCandidate := first }
          | some .lt => some { priority := .senior second, firstCandidate := first }
          | _ => do
              let frame ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                target view rule3FrameOf endpoint partner endpointCursor
              some { priority := input.localizedRule3EndpointPriority frame.endpointFrame,
                     firstCandidate := first }
  | _ => none

/-- Computational sub-results recovered from a successful parameterized endpoint compilation.  These
are the exact candidate pair, the two canonical cursor selections, and the shared Rule-3 frame
boundary; the Rules-4a--5 sub-compilations are intentionally not exported. -/
structure LocalizedRule3OccurrenceEndpointKeyFrameComputations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel) where
  candidates : input.localizedRule3ExplicitSubstituents endpoint partner =
    [frame.endpointFrame.first, frame.endpointFrame.second]
  firstCursor : input.localizedRule3ReferenceCursor? endpointCursor
    frame.endpointFrame.first = some frame.firstCursor
  secondCursor : input.localizedRule3ReferenceCursor? endpointCursor
    frame.endpointFrame.second = some frame.secondCursor
  rule3Frame : rule3FrameOf [frame.firstCursor, frame.secondCursor] = some frame.rule3Frame
  keys : frame.rule3Frame.keys =
    [frame.endpointFrame.firstKey.rule3, frame.endpointFrame.secondKey.rule3]

/-- A successful parameterized endpoint compilation reveals exactly its candidate pair, its two
canonical cursor selections, and its shared Rule-3 frame boundary. -/
theorem buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_computations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (computed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view rule3FrameOf endpoint partner endpointCursor = some frame) :
    input.LocalizedRule3OccurrenceEndpointKeyFrameComputations
      target view rule3FrameOf endpoint partner endpointCursor frame := by
  unfold buildLocalizedRule3OccurrenceEndpointKeyFrameWith? at computed
  generalize candidatesIdentity :
      input.localizedRule3ExplicitSubstituents endpoint partner = candidates at computed
  cases candidates with
  | nil => simp at computed
  | cons first rest =>
      cases rest with
      | nil => simp at computed
      | cons second tail =>
          cases tail with
          | cons third more => simp at computed
          | nil =>
              cases firstCursorComputed :
                  input.localizedRule3ReferenceCursor? endpointCursor first with
              | none => simp [firstCursorComputed] at computed
              | some firstCursor =>
                  cases secondCursorComputed :
                      input.localizedRule3ReferenceCursor? endpointCursor second with
                  | none =>
                      simp [firstCursorComputed, secondCursorComputed] at computed
                  | some secondCursor =>
                      let fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
                      cases rule3FrameComputed :
                          rule3FrameOf [firstCursor, secondCursor] with
                      | none =>
                          simp [firstCursorComputed, secondCursorComputed,
                            rule3FrameComputed] at computed
                      | some rule3Frame =>
                          generalize keysIdentity : rule3Frame.keys = keys at computed
                          cases keys with
                          | nil =>
                              simp [firstCursorComputed, secondCursorComputed,
                                rule3FrameComputed, keysIdentity] at computed
                          | cons firstRule3 keyTail =>
                              cases keyTail with
                              | nil =>
                                  simp [firstCursorComputed, secondCursorComputed,
                                    rule3FrameComputed, keysIdentity] at computed
                              | cons secondRule3 keyRest =>
                                  cases keyRest with
                                  | cons thirdRule3 more =>
                                      simp [firstCursorComputed, secondCursorComputed,
                                        rule3FrameComputed, keysIdentity] at computed
                                  | nil =>
                                      cases firstRule45Computed :
                                          input.buildLocalizedRerootCompoundRule45Key?
                                            target view fuel firstCursor with
                                      | none =>
                                          simp [firstCursorComputed, secondCursorComputed,
                                            rule3FrameComputed, keysIdentity,
                                            firstRule45Computed, fuel] at computed
                                      | some firstRule45 =>
                                          cases secondRule45Computed :
                                              input.buildLocalizedRerootCompoundRule45Key?
                                                target view fuel secondCursor with
                                          | none =>
                                              simp [firstCursorComputed,
                                                secondCursorComputed,
                                                rule3FrameComputed, keysIdentity,
                                                secondRule45Computed, fuel] at computed
                                          | some secondRule45 =>
                                              simp [firstCursorComputed,
                                                secondCursorComputed,
                                                rule3FrameComputed, keysIdentity,
                                                firstRule45Computed,
                                                secondRule45Computed, fuel] at computed
                                              subst frame
                                              exact
                                                { candidates := candidatesIdentity
                                                  firstCursor := firstCursorComputed
                                                  secondCursor := secondCursorComputed
                                                  rule3Frame := rule3FrameComputed
                                                  keys := keysIdentity }

/-- Independent fresh root observation on two actual cursors, as a strict endpoint reading. -/
inductive DeclarativeLocalizedRule3RootObservation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.Atom)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel) :
    input.LocalizedRule3EndpointPriority → Prop where
  | firstSenior
      (strict : input.compareLocalizedRerootCursorConstitutionalRoot
        firstCursor secondCursor = Ordering.gt) :
      input.DeclarativeLocalizedRule3RootObservation
        first second firstCursor secondCursor (.senior first)
  | secondSenior
      (strict : input.compareLocalizedRerootCursorConstitutionalRoot
        firstCursor secondCursor = Ordering.lt) :
      input.DeclarativeLocalizedRule3RootObservation
        first second firstCursor secondCursor (.senior second)

/-- Independent endpoint meaning: a strict root, a strict independently derived complete
constitutional comparison, or the deferred full parameterized frame. -/
inductive DeclarativeLocalizedRule3ShortCircuitEndpointResult
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel) :
    input.LocalizedRule3ShortCircuitEndpointResult → Prop where
  | rootRule1aStrict {first second firstCursor secondCursor priority}
      (actualPair : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
      (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
        endpointCursor firstCursor first)
      (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
        endpointCursor secondCursor second)
      (fresh : input.DeclarativeLocalizedRule3RootObservation
        first second firstCursor secondCursor priority) :
      input.DeclarativeLocalizedRule3ShortCircuitEndpointResult target view
        Rule3FrameMeaning endpoint partner endpointCursor
        { priority := priority, firstCandidate := first }
  | constitutionalStrict {first second firstCursor secondCursor priority firstKey secondKey fuel}
      (actualPair : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
      (firstReference : input.CanonicalLocalizedRule3ReferenceCursor endpointCursor firstCursor first)
      (secondReference : input.CanonicalLocalizedRule3ReferenceCursor endpointCursor secondCursor second)
      (firstDerived : input.DeclarativeLocalizedRerootRuleMajorKey fuel firstCursor firstKey)
      (secondDerived : input.DeclarativeLocalizedRerootRuleMajorKey fuel secondCursor secondKey)
      (strict : (OfficialRuleMajorKey.compare firstKey secondKey = .gt ∧ priority = .senior first) ∨
        (OfficialRuleMajorKey.compare firstKey secondKey = .lt ∧ priority = .senior second)) :
      input.DeclarativeLocalizedRule3ShortCircuitEndpointResult target view
        Rule3FrameMeaning endpoint partner endpointCursor
        { priority := priority, firstCandidate := first }
  | fullKey (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
      (derived : input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
        target view Rule3FrameMeaning endpoint partner endpointCursor frame)
      (deferred : input.compareLocalizedRerootCursorConstitutionalRoot
        frame.firstCursor frame.secondCursor = Ordering.eq) :
      input.DeclarativeLocalizedRule3ShortCircuitEndpointResult target view
        Rule3FrameMeaning endpoint partner endpointCursor
        { priority := input.localizedRule3EndpointPriority frame.endpointFrame,
          firstCandidate := frame.endpointFrame.first }

/-- Every successful short-circuit compilation has its independent relational witness.  Soundness
needs only the shared Rule-3 frame meaning; the unused lower-rule frames are never required. -/
theorem localizedRule3ShortCircuitEndpointPriority?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (rule3FrameSound : ∀ cursors frame,
      rule3FrameOf cursors = some frame → Rule3FrameMeaning cursors frame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (result : input.LocalizedRule3ShortCircuitEndpointResult)
    (computed : input.localizedRule3ShortCircuitEndpointPriority?
      target view rule3FrameOf endpoint partner endpointCursor = some result) :
    input.DeclarativeLocalizedRule3ShortCircuitEndpointResult
      target view Rule3FrameMeaning endpoint partner endpointCursor result := by
  unfold localizedRule3ShortCircuitEndpointPriority? at computed
  generalize candidatesIdentity :
      input.localizedRule3ExplicitSubstituents endpoint partner = candidates at computed
  cases candidates with
  | nil => simp at computed
  | cons first rest =>
      cases rest with
      | nil => simp at computed
      | cons second tail =>
          cases tail with
          | cons third more => simp at computed
          | nil =>
              cases firstCursorComputed :
                  input.localizedRule3ReferenceCursor? endpointCursor first with
              | none => simp [firstCursorComputed] at computed
              | some firstCursor =>
                  cases secondCursorComputed :
                      input.localizedRule3ReferenceCursor? endpointCursor second with
                  | none =>
                      simp [firstCursorComputed, secondCursorComputed] at computed
                  | some secondCursor =>
                      generalize rootComparison :
                          input.compareLocalizedRerootCursorConstitutionalRoot
                            firstCursor secondCursor = outcome at computed
                      cases outcome with
                      | gt =>
                          simp [firstCursorComputed, secondCursorComputed,
                            rootComparison] at computed
                          subst result
                          exact
                            DeclarativeLocalizedRule3ShortCircuitEndpointResult.rootRule1aStrict
                              candidatesIdentity
                              ((input.localizedRule3ReferenceCursor?_eq_some_iff
                                endpointCursor firstCursor first).mp firstCursorComputed)
                              ((input.localizedRule3ReferenceCursor?_eq_some_iff
                                endpointCursor secondCursor second).mp secondCursorComputed)
                              (DeclarativeLocalizedRule3RootObservation.firstSenior
                                rootComparison)
                      | lt =>
                          simp [firstCursorComputed, secondCursorComputed,
                            rootComparison] at computed
                          subst result
                          exact
                            DeclarativeLocalizedRule3ShortCircuitEndpointResult.rootRule1aStrict
                              candidatesIdentity
                              ((input.localizedRule3ReferenceCursor?_eq_some_iff
                                endpointCursor firstCursor first).mp firstCursorComputed)
                              ((input.localizedRule3ReferenceCursor?_eq_some_iff
                                endpointCursor secondCursor second).mp secondCursorComputed)
                              (DeclarativeLocalizedRule3RootObservation.secondSenior
                                rootComparison)
                      | eq =>
                          have fullSound (result : input.LocalizedRule3ShortCircuitEndpointResult)
                              (computed : (do
                                let frame ← input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                                  target view rule3FrameOf endpoint partner endpointCursor
                                some { priority := input.localizedRule3EndpointPriority frame.endpointFrame,
                                       firstCandidate := first }) = some result) :
                              input.DeclarativeLocalizedRule3ShortCircuitEndpointResult target view
                                Rule3FrameMeaning endpoint partner endpointCursor result := by
                              cases frameComputed :
                                  input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
                                    target view rule3FrameOf endpoint partner endpointCursor with
                              | none =>
                                  simp [frameComputed] at computed
                              | some frame =>
                                  simp [frameComputed] at computed
                                  subst result
                                  have derived :=
                                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_sound
                                      target view rule3FrameOf Rule3FrameMeaning rule3FrameSound
                                      endpoint partner endpointCursor frame frameComputed
                                  have comps :=
                                    input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_computations
                                      target view rule3FrameOf endpoint partner endpointCursor
                                      frame frameComputed
                                  have firstEq : frame.endpointFrame.first = first := by
                                    have listsEq :
                                        [frame.endpointFrame.first, frame.endpointFrame.second] =
                                          [first, second] := by
                                      rw [← comps.candidates, candidatesIdentity]
                                    exact (List.cons.inj listsEq).1
                                  have secondEq : frame.endpointFrame.second = second := by
                                    have listsEq :
                                        [frame.endpointFrame.first, frame.endpointFrame.second] =
                                          [first, second] := by
                                      rw [← comps.candidates, candidatesIdentity]
                                    exact (List.cons.inj (List.cons.inj listsEq).2).1
                                  have firstCursorEq : frame.firstCursor = firstCursor := by
                                    have comp :
                                        input.localizedRule3ReferenceCursor? endpointCursor first =
                                          some frame.firstCursor := by
                                      simpa [firstEq] using comps.firstCursor
                                    exact Option.some.inj (comp.symm.trans firstCursorComputed)
                                  have secondCursorEq : frame.secondCursor = secondCursor := by
                                    have comp :
                                        input.localizedRule3ReferenceCursor? endpointCursor second =
                                          some frame.secondCursor := by
                                      simpa [secondEq] using comps.secondCursor
                                    exact Option.some.inj (comp.symm.trans secondCursorComputed)
                                  have deferred :
                                      input.compareLocalizedRerootCursorConstitutionalRoot
                                        frame.firstCursor frame.secondCursor = Ordering.eq := by
                                    rw [firstCursorEq, secondCursorEq]
                                    exact rootComparison
                                  rw [← firstEq]
                                  exact
                                    DeclarativeLocalizedRule3ShortCircuitEndpointResult.fullKey
                                      frame derived deferred
                          cases constitutionalComputed :
                              input.compareLocalizedConstitutionalCursors? firstCursor secondCursor with
                          | none =>
                              apply fullSound result
                              simpa [firstCursorComputed, secondCursorComputed,
                                rootComparison, constitutionalComputed] using computed
                          | some order =>
                              cases order with
                              | eq =>
                                  apply fullSound result
                                  simpa [firstCursorComputed, secondCursorComputed,
                                    rootComparison, constitutionalComputed] using computed
                              | gt =>
                                  simp [firstCursorComputed, secondCursorComputed,
                                    rootComparison, constitutionalComputed] at computed
                                  subst result
                                  obtain ⟨firstKey, secondKey, left, right, strict⟩ :=
                                    input.compareLocalizedConstitutionalCursors?_computations
                                      firstCursor secondCursor .gt constitutionalComputed
                                  exact .constitutionalStrict candidatesIdentity
                                    ((input.localizedRule3ReferenceCursor?_eq_some_iff
                                      endpointCursor firstCursor first).mp firstCursorComputed)
                                    ((input.localizedRule3ReferenceCursor?_eq_some_iff
                                      endpointCursor secondCursor second).mp secondCursorComputed)
                                    (input.buildLocalizedRerootRuleMajorKeyExec?_sound _ _ _ left)
                                    (input.buildLocalizedRerootRuleMajorKeyExec?_sound _ _ _ right)
                                    (Or.inl ⟨strict, rfl⟩)
                              | lt =>
                                  simp [firstCursorComputed, secondCursorComputed,
                                    rootComparison, constitutionalComputed] at computed
                                  subst result
                                  obtain ⟨firstKey, secondKey, left, right, strict⟩ :=
                                    input.compareLocalizedConstitutionalCursors?_computations
                                      firstCursor secondCursor .lt constitutionalComputed
                                  exact .constitutionalStrict candidatesIdentity
                                    ((input.localizedRule3ReferenceCursor?_eq_some_iff
                                      endpointCursor firstCursor first).mp firstCursorComputed)
                                    ((input.localizedRule3ReferenceCursor?_eq_some_iff
                                      endpointCursor secondCursor second).mp secondCursorComputed)
                                    (input.buildLocalizedRerootRuleMajorKeyExec?_sound _ _ _ left)
                                    (input.buildLocalizedRerootRuleMajorKeyExec?_sound _ _ _ right)
                                    (Or.inr ⟨strict, rfl⟩)

/-- A callback's rebuilt endpoint keys agree with every successful pure constitutional comparison.
First-sphere coherence alone is insufficient for a deeper or isotope shortcut. -/
def LocalizedRule3EndpointConstitutionalExact
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel) : Prop :=
  ∀ order, input.compareLocalizedConstitutionalCursors?
      frame.firstCursor frame.secondCursor = some order →
    OfficialRuleMajorKey.compare frame.endpointFrame.firstKey.rule3.constitutional
      frame.endpointFrame.secondKey.rule3.constitutional = order

/-- The short-circuit compiler is conservative over the complete parameterized compiler whenever
the compiled frame has exact root and complete constitutional comparisons: it returns exactly the complete priority together with the
same first candidate, and never invents a different key frame. -/
theorem localizedRule3ShortCircuitEndpointPriority?_eq_of_compiled
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (rule3FrameOf : List (input.LocalizedRerootCursor carrierFuel) →
      Option input.LocalizedRule3CanonicalKeyFrame)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (exactPair : LocalizedRule3EndpointKeyFrame.FirstSphereRootExact
      frame.endpointFrame frame.firstCursor frame.secondCursor)
    (exactConstitutional : input.LocalizedRule3EndpointConstitutionalExact frame)
    (computed : input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?
      target view rule3FrameOf endpoint partner endpointCursor = some frame) :
    input.localizedRule3ShortCircuitEndpointPriority?
      target view rule3FrameOf endpoint partner endpointCursor =
      some { priority := input.localizedRule3EndpointPriority frame.endpointFrame,
             firstCandidate := frame.endpointFrame.first } := by
  have comps := input.buildLocalizedRule3OccurrenceEndpointKeyFrameWith?_computations
    target view rule3FrameOf endpoint partner endpointCursor frame computed
  unfold localizedRule3ShortCircuitEndpointPriority?
  rw [comps.candidates]
  simp [comps.firstCursor, comps.secondCursor]
  generalize rootComparison : input.compareLocalizedRerootCursorConstitutionalRoot
    frame.firstCursor frame.secondCursor = outcome
  cases outcome with
  | gt =>
      have higher : input.localizedRerootCursorRootAtomicNumber frame.secondCursor <
          input.localizedRerootCursorRootAtomicNumber frame.firstCursor := by
        have compared : compare
            (input.localizedRerootCursorRootAtomicNumber frame.firstCursor)
            (input.localizedRerootCursorRootAtomicNumber frame.secondCursor) =
            Ordering.gt := by
          simpa [compareLocalizedRerootCursorConstitutionalRoot] using rootComparison
        exact compare_gt_iff_gt.mp compared
      have priorityEq := input.localizedRule3EndpointPriority_of_cursor_root_gt
        frame.endpointFrame frame.firstCursor frame.secondCursor exactPair higher
      simp [priorityEq]
  | lt =>
      have lower : input.localizedRerootCursorRootAtomicNumber frame.firstCursor <
          input.localizedRerootCursorRootAtomicNumber frame.secondCursor := by
        have compared : compare
            (input.localizedRerootCursorRootAtomicNumber frame.firstCursor)
            (input.localizedRerootCursorRootAtomicNumber frame.secondCursor) =
            Ordering.lt := by
          simpa [compareLocalizedRerootCursorConstitutionalRoot] using rootComparison
        exact compare_lt_iff_lt.mp compared
      have priorityEq := input.localizedRule3EndpointPriority_of_cursor_root_lt
        frame.endpointFrame frame.firstCursor frame.secondCursor exactPair lower
      simp [priorityEq]
  | eq =>
      cases compared : input.compareLocalizedConstitutionalCursors?
          frame.firstCursor frame.secondCursor with
      | none => simp [computed]
      | some order =>
          have exactOrder := exactConstitutional order compared
          cases order with
          | eq => simp [computed]
          | gt =>
              have priority := input.localizedRule3EndpointPriority_of_constitutional_gt
                frame.endpointFrame exactOrder
              simp [priority]
          | lt =>
              have priority := input.localizedRule3EndpointPriority_of_constitutional_lt
                frame.endpointFrame exactOrder
              simp [priority]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
