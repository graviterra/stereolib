import TetraStereo.OneCenter.LocalizedConstitutionalRule3Coherence
import TetraStereo.OneCenter.LocalizedRule3ShortCircuitEndpoint
import TetraStereo.OneCenter.LocalizedRerootExtendedShortCircuitRule3Key

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Declarative Rule-3 priority agreement

This module packages the chemically justified first-sphere and complete-constitutional shortcuts as
purely declarative statements.  The point is *not* to prove that an eager full Rules-3a--5 payload
always exists, but to prove that a strict constitutional prefix decides the endpoint uniformly for
every compatible independently derived full endpoint frame, whatever arbitrary lower Rule-3
observation or Rules-4a--5 payload that frame carries.

Four results are established:

1. `extendedRule3Key_constitutional_derived`: every independent extended short-circuit Rule-3 key
   contains an independent pure constitutional derivation of its `constitutional` projection.  This
   is the structural analogue of the descriptor-bearing and short-circuit projections; it needs no
   executable success.

2. `declarative_constitutional_rule1a_head`: a pure constitutional derivation at a cursor retains
   the cursor's atomic number as the singleton first sphere of Rule 1a.

3. `localizedRule3EndpointPriority_of_declarative_constitutional_gt/lt`: two independently derived
   pure constitutional keys at a full endpoint frame's two cursors (at possibly different fuels)
   strictly comparing `.gt`/`.lt` implies that the actual full endpoint priority selects the
   corresponding senior reference.

4. `DeclarativeLocalizedRule3StrictEndpointEvidence` packages a strict decision together with the
   exact candidate pair and canonical reference selections, and
   `localizedRule3EndpointPriority_eq_of_strict_evidence` shows that every compatible independently
   derived full endpoint frame agrees with that decision, including the first-candidate identity.
-/

namespace CertifiedLocalizedCIPInput

/-! ## 1. Constitutional projection of extended short-circuit keys -/

/-- The demand-driven extended short-circuit successor has the same constitutional projection
property as the original and short-circuit successors: each independent full-key derivation carries
an independent pure Rules-1a--2 derivation of its constitutional component. -/
theorem extendedRule3Key_constitutional_derived
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel excluded cursor key,
      input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
        target view fuel excluded cursor key →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key.constitutional := by
  intro fuel
  induction fuel with
  | zero =>
      intro excluded cursor key meaning
      obtain ⟨children, frame, empty, _, rfl⟩ := meaning
      exact .terminal frame empty
  | succ fuel ih =>
      intro excluded cursor key meaning
      obtain ⟨children, observation, frame, _, terminal | branch⟩ := meaning
      · obtain ⟨empty, rfl⟩ := terminal
        exact .terminal frame empty
      · obtain ⟨childKeys, sorted, nonempty, derivations, ranking, descending, rfl⟩ := branch
        exact .branch frame nonempty
          (projected_rule3_constitutional_key_list input _ (ih excluded)
            children childKeys derivations)
          (ranking.map (·.constitutional)) (input.rule3_descending_constitutional sorted descending)

/-! ## 2. Pure Rule-1a head of a constitutional derivation -/

/-- Every independent pure constitutional derivation retains the addressed cursor's atomic number
as the singleton first sphere of Rule 1a, in both the terminal and the assembled branch cases. -/
theorem declarative_constitutional_rule1a_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ (fuel : Nat) (key : OfficialRuleMajorKey input.Atom),
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key →
      key.rule1a.head? =
        some [([], input.localizedRerootCursorRootAtomicNumber cursor)] := by
  intro fuel key derived
  cases derived with
  | terminal frame empty =>
      simp [localizedRerootCursorRootAtomicNumber]
  | branch frame nonempty childDerivations ranking descending =>
      simp [OfficialRuleMajorKey.assemble, localizedRerootCursorRootAtomicNumber]

/-! ## 3. Strict constitutional priority agreement -/

/-- A full endpoint frame whose two constitutional projections are independently derived at its
cursors agrees with any other independent pure constitutional comparison at those cursors, even at
different fuels: a strict pure `.gt` selects the first endpoint reference. -/
theorem localizedRule3EndpointPriority_of_declarative_constitutional_gt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (firstConstitutionalFuel secondConstitutionalFuel leftFuel rightFuel : Nat)
    {left right : OfficialRuleMajorKey input.Atom}
    (firstConstitutionalDerived : input.DeclarativeLocalizedRerootRuleMajorKey
      firstConstitutionalFuel frame.firstCursor frame.endpointFrame.firstKey.rule3.constitutional)
    (secondConstitutionalDerived : input.DeclarativeLocalizedRerootRuleMajorKey
      secondConstitutionalFuel frame.secondCursor frame.endpointFrame.secondKey.rule3.constitutional)
    (leftDerived : input.DeclarativeLocalizedRerootRuleMajorKey leftFuel frame.firstCursor left)
    (rightDerived : input.DeclarativeLocalizedRerootRuleMajorKey rightFuel frame.secondCursor right)
    (strict : OfficialRuleMajorKey.compare left right = Ordering.gt) :
    input.localizedRule3EndpointPriority frame.endpointFrame = .senior frame.endpointFrame.first := by
  have leftObservable : constitutionalObservable left =
      constitutionalObservable frame.endpointFrame.firstKey.rule3.constitutional :=
    input.declarative_constitutional_observable_unique leftFuel firstConstitutionalFuel
      frame.firstCursor left frame.endpointFrame.firstKey.rule3.constitutional
      leftDerived firstConstitutionalDerived
  have rightObservable : constitutionalObservable right =
      constitutionalObservable frame.endpointFrame.secondKey.rule3.constitutional :=
    input.declarative_constitutional_observable_unique rightFuel secondConstitutionalFuel
      frame.secondCursor right frame.endpointFrame.secondKey.rule3.constitutional
      rightDerived secondConstitutionalDerived
  have constitutionalStrict : OfficialRuleMajorKey.compare
      frame.endpointFrame.firstKey.rule3.constitutional
      frame.endpointFrame.secondKey.rule3.constitutional = Ordering.gt :=
    (ruleMajor_compare_congr left right
      frame.endpointFrame.firstKey.rule3.constitutional
      frame.endpointFrame.secondKey.rule3.constitutional
      leftObservable rightObservable).symm.trans strict
  exact input.localizedRule3EndpointPriority_of_constitutional_gt
    frame.endpointFrame constitutionalStrict

/-- The symmetric strict constitutional case: a strict pure `.lt` selects the second endpoint
reference. -/
theorem localizedRule3EndpointPriority_of_declarative_constitutional_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (firstConstitutionalFuel secondConstitutionalFuel leftFuel rightFuel : Nat)
    {left right : OfficialRuleMajorKey input.Atom}
    (firstConstitutionalDerived : input.DeclarativeLocalizedRerootRuleMajorKey
      firstConstitutionalFuel frame.firstCursor frame.endpointFrame.firstKey.rule3.constitutional)
    (secondConstitutionalDerived : input.DeclarativeLocalizedRerootRuleMajorKey
      secondConstitutionalFuel frame.secondCursor frame.endpointFrame.secondKey.rule3.constitutional)
    (leftDerived : input.DeclarativeLocalizedRerootRuleMajorKey leftFuel frame.firstCursor left)
    (rightDerived : input.DeclarativeLocalizedRerootRuleMajorKey rightFuel frame.secondCursor right)
    (strict : OfficialRuleMajorKey.compare left right = Ordering.lt) :
    input.localizedRule3EndpointPriority frame.endpointFrame = .senior frame.endpointFrame.second := by
  have leftObservable : constitutionalObservable left =
      constitutionalObservable frame.endpointFrame.firstKey.rule3.constitutional :=
    input.declarative_constitutional_observable_unique leftFuel firstConstitutionalFuel
      frame.firstCursor left frame.endpointFrame.firstKey.rule3.constitutional
      leftDerived firstConstitutionalDerived
  have rightObservable : constitutionalObservable right =
      constitutionalObservable frame.endpointFrame.secondKey.rule3.constitutional :=
    input.declarative_constitutional_observable_unique rightFuel secondConstitutionalFuel
      frame.secondCursor right frame.endpointFrame.secondKey.rule3.constitutional
      rightDerived secondConstitutionalDerived
  have constitutionalStrict : OfficialRuleMajorKey.compare
      frame.endpointFrame.firstKey.rule3.constitutional
      frame.endpointFrame.secondKey.rule3.constitutional = Ordering.lt :=
    (ruleMajor_compare_congr left right
      frame.endpointFrame.firstKey.rule3.constitutional
      frame.endpointFrame.secondKey.rule3.constitutional
      leftObservable rightObservable).symm.trans strict
  exact input.localizedRule3EndpointPriority_of_constitutional_lt
    frame.endpointFrame constitutionalStrict

/-! ## 4. Packaged strict evidence and agreement with every compatible full frame -/

/-- A canonical reference cursor is unique among cut-neighborhood candidates carrying the requested
physical atom, so any other independent reference selection for the same atom is the same cursor. -/
theorem referenceCursor_eq_of_canonical_of_declarative
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (endpointCursor cursor canonicalCursor : input.LocalizedRerootCursor carrierFuel)
    (reference : input.Atom)
    (canonical : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor canonicalCursor reference)
    (declarative : input.DeclarativeLocalizedRule3ReferenceCursor
      endpointCursor cursor reference) :
    cursor = canonicalCursor := by
  rcases canonical with ⟨children, childrenComputed, exactChildren, canonicalPresent,
    canonicalCurrent, canonicalPhysical, canonicalPrevious, unique⟩
  rcases declarative with ⟨children', childrenComputed', exactChildren', present,
    current, physical, previous⟩
  have childrenEq : children = children' :=
    Option.some.inj (childrenComputed.symm.trans childrenComputed')
  subst children'
  exact unique cursor present current physical

/-- A full endpoint frame is compatible with a strict evidence package when it selects the same
candidate pair and the same two cursors. -/
def LocalizedRule3EndpointFrameCompatible
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (first second : input.Atom)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  frame.endpointFrame.first = first ∧
  frame.endpointFrame.second = second ∧
  frame.firstCursor = firstCursor ∧
  frame.secondCursor = secondCursor

/-- An independently derived full endpoint frame inherits the candidate pair and cursor selections
of a strict evidence package: the explicit-substituent list and the canonical reference selections
pin the frame's identities. -/
theorem LocalizedRule3EndpointFrameCompatible_of_evidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    {first second : input.Atom}
    {firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel}
    (actualPair : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor firstCursor first)
    (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor secondCursor second)
    {frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel}
    (frameDerived : input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning endpoint partner endpointCursor frame) :
    input.LocalizedRule3EndpointFrameCompatible frame first second firstCursor secondCursor := by
  have candidatesEq : [frame.endpointFrame.first, frame.endpointFrame.second] = [first, second] :=
    frameDerived.1.symm.trans actualPair
  have firstEq : frame.endpointFrame.first = first := (List.cons.inj candidatesEq).1
  have secondEq : frame.endpointFrame.second = second :=
    (List.cons.inj (List.cons.inj candidatesEq).2).1
  have firstDeclRef : input.DeclarativeLocalizedRule3ReferenceCursor
      endpointCursor frame.firstCursor frame.endpointFrame.first := frameDerived.2.1
  have firstCursorEq : frame.firstCursor = firstCursor := by
    rw [firstEq] at firstDeclRef
    exact input.referenceCursor_eq_of_canonical_of_declarative
      endpointCursor frame.firstCursor firstCursor first firstReference firstDeclRef
  have secondDeclRef : input.DeclarativeLocalizedRule3ReferenceCursor
      endpointCursor frame.secondCursor frame.endpointFrame.second := frameDerived.2.2.1
  have secondCursorEq : frame.secondCursor = secondCursor := by
    rw [secondEq] at secondDeclRef
    exact input.referenceCursor_eq_of_canonical_of_declarative
      endpointCursor frame.secondCursor secondCursor second secondReference secondDeclRef
  exact ⟨firstEq, secondEq, firstCursorEq, secondCursorEq⟩

/-- Strict endpoint evidence: an exact candidate pair with canonical reference selections and either
a fresh first-sphere root decision or an independent pure constitutional strict comparison.  This is
the chemically justified shortcut that never inspects lower Rule-3 observations or Rules-4a--5. -/
inductive DeclarativeLocalizedRule3StrictEndpointEvidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    (first second : input.Atom)
    (firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel)
    (priority : input.LocalizedRule3EndpointPriority) : Prop where
  | rootRule1aStrict
      (actualPair : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
      (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
        endpointCursor firstCursor first)
      (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
        endpointCursor secondCursor second)
      (fresh : input.DeclarativeLocalizedRule3RootObservation
        first second firstCursor secondCursor priority) :
      input.DeclarativeLocalizedRule3StrictEndpointEvidence
        endpoint partner endpointCursor first second firstCursor secondCursor priority
  | constitutionalStrict {firstKey secondKey : OfficialRuleMajorKey input.Atom}
      {firstFuel secondFuel : Nat}
      (actualPair : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
      (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
        endpointCursor firstCursor first)
      (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
        endpointCursor secondCursor second)
      (firstDerived : input.DeclarativeLocalizedRerootRuleMajorKey
        firstFuel firstCursor firstKey)
      (secondDerived : input.DeclarativeLocalizedRerootRuleMajorKey
        secondFuel secondCursor secondKey)
      (strict : (OfficialRuleMajorKey.compare firstKey secondKey = Ordering.gt ∧
          priority = .senior first) ∨
        (OfficialRuleMajorKey.compare firstKey secondKey = Ordering.lt ∧
          priority = .senior second)) :
      input.DeclarativeLocalizedRule3StrictEndpointEvidence
        endpoint partner endpointCursor first second firstCursor secondCursor priority

/-- Every compatible independently derived full endpoint frame agrees with a strict evidence
package: its complete endpoint priority is the packaged priority and its first candidate is the
packaged first candidate.  This makes the strict prefix decision independent of any arbitrary
lower Rule-3 observation or Rules-4a--5 payload. -/
theorem localizedRule3EndpointPriority_eq_of_strict_evidence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (Rule3FrameMeaning : input.LocalizedRule3FrameMeaning carrierFuel)
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    {first second : input.Atom}
    {firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel}
    {priority : input.LocalizedRule3EndpointPriority}
    (evidence : input.DeclarativeLocalizedRule3StrictEndpointEvidence
      endpoint partner endpointCursor first second firstCursor secondCursor priority)
    {frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel}
    (frameDerived : input.DeclarativeLocalizedRule3OccurrenceEndpointKeyFrameWith
      target view Rule3FrameMeaning endpoint partner endpointCursor frame)
    {firstConstitutionalFuel secondConstitutionalFuel : Nat}
    (firstConstitutionalDerived : input.DeclarativeLocalizedRerootRuleMajorKey
      firstConstitutionalFuel frame.firstCursor frame.endpointFrame.firstKey.rule3.constitutional)
    (secondConstitutionalDerived : input.DeclarativeLocalizedRerootRuleMajorKey
      secondConstitutionalFuel frame.secondCursor frame.endpointFrame.secondKey.rule3.constitutional) :
    input.localizedRule3EndpointPriority frame.endpointFrame = priority ∧
      frame.endpointFrame.first = first := by
  cases evidence with
  | rootRule1aStrict actualPair firstReference secondReference fresh =>
      have compatible : input.LocalizedRule3EndpointFrameCompatible
          frame first second firstCursor secondCursor :=
        input.LocalizedRule3EndpointFrameCompatible_of_evidence
          target view Rule3FrameMeaning endpoint partner endpointCursor
          actualPair firstReference secondReference frameDerived
      rcases compatible with ⟨firstEq, secondEq, firstCursorEq, secondCursorEq⟩
      cases fresh with
      | firstSenior strict =>
          have firstHead : frame.endpointFrame.firstKey.rule3.constitutional.rule1a.head? =
              some [([], input.localizedRerootCursorRootAtomicNumber firstCursor)] := by
            have head := input.declarative_constitutional_rule1a_head
              frame.firstCursor firstConstitutionalFuel
              frame.endpointFrame.firstKey.rule3.constitutional firstConstitutionalDerived
            simpa [firstCursorEq] using head
          have secondHead : frame.endpointFrame.secondKey.rule3.constitutional.rule1a.head? =
              some [([], input.localizedRerootCursorRootAtomicNumber secondCursor)] := by
            have head := input.declarative_constitutional_rule1a_head
              frame.secondCursor secondConstitutionalFuel
              frame.endpointFrame.secondKey.rule3.constitutional secondConstitutionalDerived
            simpa [secondCursorEq] using head
          have exactPair : LocalizedRule3EndpointKeyFrame.FirstSphereRootExact
              frame.endpointFrame firstCursor secondCursor := ⟨firstHead, secondHead⟩
          have higher : input.localizedRerootCursorRootAtomicNumber secondCursor <
              input.localizedRerootCursorRootAtomicNumber firstCursor := by
            have compared : compare (input.localizedRerootCursorRootAtomicNumber firstCursor)
                (input.localizedRerootCursorRootAtomicNumber secondCursor) = Ordering.gt := by
              simpa [compareLocalizedRerootCursorConstitutionalRoot] using strict
            exact compare_gt_iff_gt.mp compared
          have priorityEq := input.localizedRule3EndpointPriority_of_cursor_root_gt
            frame.endpointFrame firstCursor secondCursor exactPair higher
          exact ⟨by simpa [firstEq] using priorityEq, firstEq⟩
      | secondSenior strict =>
          have firstHead : frame.endpointFrame.firstKey.rule3.constitutional.rule1a.head? =
              some [([], input.localizedRerootCursorRootAtomicNumber firstCursor)] := by
            have head := input.declarative_constitutional_rule1a_head
              frame.firstCursor firstConstitutionalFuel
              frame.endpointFrame.firstKey.rule3.constitutional firstConstitutionalDerived
            simpa [firstCursorEq] using head
          have secondHead : frame.endpointFrame.secondKey.rule3.constitutional.rule1a.head? =
              some [([], input.localizedRerootCursorRootAtomicNumber secondCursor)] := by
            have head := input.declarative_constitutional_rule1a_head
              frame.secondCursor secondConstitutionalFuel
              frame.endpointFrame.secondKey.rule3.constitutional secondConstitutionalDerived
            simpa [secondCursorEq] using head
          have exactPair : LocalizedRule3EndpointKeyFrame.FirstSphereRootExact
              frame.endpointFrame firstCursor secondCursor := ⟨firstHead, secondHead⟩
          have lower : input.localizedRerootCursorRootAtomicNumber firstCursor <
              input.localizedRerootCursorRootAtomicNumber secondCursor := by
            have compared : compare (input.localizedRerootCursorRootAtomicNumber firstCursor)
                (input.localizedRerootCursorRootAtomicNumber secondCursor) = Ordering.lt := by
              simpa [compareLocalizedRerootCursorConstitutionalRoot] using strict
            exact compare_lt_iff_lt.mp compared
          have priorityEq := input.localizedRule3EndpointPriority_of_cursor_root_lt
            frame.endpointFrame firstCursor secondCursor exactPair lower
          exact ⟨by simpa [secondEq] using priorityEq, firstEq⟩
  | @constitutionalStrict firstKey secondKey firstFuel secondFuel actualPair firstReference
      secondReference firstDerived secondDerived strict =>
      have compatible : input.LocalizedRule3EndpointFrameCompatible
          frame first second firstCursor secondCursor :=
        input.LocalizedRule3EndpointFrameCompatible_of_evidence
          target view Rule3FrameMeaning endpoint partner endpointCursor
          actualPair firstReference secondReference frameDerived
      rcases compatible with ⟨firstEq, secondEq, firstCursorEq, secondCursorEq⟩
      have leftDerivedAt : input.DeclarativeLocalizedRerootRuleMajorKey
          firstFuel frame.firstCursor firstKey := by
        rwa [firstCursorEq]
      have rightDerivedAt : input.DeclarativeLocalizedRerootRuleMajorKey
          secondFuel frame.secondCursor secondKey := by
        rwa [secondCursorEq]
      rcases strict with h | h
      · have priorityEq :=
          input.localizedRule3EndpointPriority_of_declarative_constitutional_gt
            frame firstConstitutionalFuel secondConstitutionalFuel firstFuel secondFuel
            firstConstitutionalDerived secondConstitutionalDerived
            leftDerivedAt rightDerivedAt h.1
        have priorityEqFirst : input.localizedRule3EndpointPriority frame.endpointFrame =
            .senior first := by
          simpa [firstEq] using priorityEq
        exact ⟨priorityEqFirst.trans h.2.symm, firstEq⟩
      · have priorityEq :=
          input.localizedRule3EndpointPriority_of_declarative_constitutional_lt
            frame firstConstitutionalFuel secondConstitutionalFuel firstFuel secondFuel
            firstConstitutionalDerived secondConstitutionalDerived
            leftDerivedAt rightDerivedAt h.1
        have priorityEqSecond : input.localizedRule3EndpointPriority frame.endpointFrame =
            .senior second := by
          simpa [secondEq] using priorityEq
        exact ⟨priorityEqSecond.trans h.2.symm, firstEq⟩

/-! ## Compatibility of the three full-key builders via their projections -/

/-- The descriptor-bearing full-key builder discharges a full endpoint frame's two independent
constitutional projections. -/
theorem constitutional_derived_of_descriptorBearing
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (firstDerived : input.DeclarativeLocalizedRerootDescriptorBearingRule3Key
      target view fuel excluded frame.firstCursor frame.endpointFrame.firstKey.rule3)
    (secondDerived : input.DeclarativeLocalizedRerootDescriptorBearingRule3Key
      target view fuel excluded frame.secondCursor frame.endpointFrame.secondKey.rule3) :
    input.DeclarativeLocalizedRerootRuleMajorKey fuel frame.firstCursor
      frame.endpointFrame.firstKey.rule3.constitutional ∧
    input.DeclarativeLocalizedRerootRuleMajorKey fuel frame.secondCursor
      frame.endpointFrame.secondKey.rule3.constitutional := by
  exact ⟨
    input.descriptorRule3Key_constitutional_derived target view fuel excluded
      frame.firstCursor frame.endpointFrame.firstKey.rule3 firstDerived,
    input.descriptorRule3Key_constitutional_derived target view fuel excluded
      frame.secondCursor frame.endpointFrame.secondKey.rule3 secondDerived⟩

/-- The short-circuit full-key builder discharges a full endpoint frame's two independent
constitutional projections. -/
theorem constitutional_derived_of_shortCircuit
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (firstDerived : input.DeclarativeLocalizedRerootShortCircuitRule3Key
      target view fuel excluded frame.firstCursor frame.endpointFrame.firstKey.rule3)
    (secondDerived : input.DeclarativeLocalizedRerootShortCircuitRule3Key
      target view fuel excluded frame.secondCursor frame.endpointFrame.secondKey.rule3) :
    input.DeclarativeLocalizedRerootRuleMajorKey fuel frame.firstCursor
      frame.endpointFrame.firstKey.rule3.constitutional ∧
    input.DeclarativeLocalizedRerootRuleMajorKey fuel frame.secondCursor
      frame.endpointFrame.secondKey.rule3.constitutional := by
  exact ⟨
    input.shortCircuitRule3Key_constitutional_derived target view fuel excluded
      frame.firstCursor frame.endpointFrame.firstKey.rule3 firstDerived,
    input.shortCircuitRule3Key_constitutional_derived target view fuel excluded
      frame.secondCursor frame.endpointFrame.secondKey.rule3 secondDerived⟩

/-- The extended short-circuit full-key builder discharges a full endpoint frame's two independent
constitutional projections. -/
theorem constitutional_derived_of_extendedShortCircuit
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (excluded : List input.LocalizedRule3PhysicalUnitId)
    (frame : input.LocalizedRule3OccurrenceEndpointKeyFrame carrierFuel)
    (firstDerived : input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
      target view fuel excluded frame.firstCursor frame.endpointFrame.firstKey.rule3)
    (secondDerived : input.DeclarativeLocalizedRerootExtendedShortCircuitRule3Key
      target view fuel excluded frame.secondCursor frame.endpointFrame.secondKey.rule3) :
    input.DeclarativeLocalizedRerootRuleMajorKey fuel frame.firstCursor
      frame.endpointFrame.firstKey.rule3.constitutional ∧
    input.DeclarativeLocalizedRerootRuleMajorKey fuel frame.secondCursor
      frame.endpointFrame.secondKey.rule3.constitutional := by
  exact ⟨
    input.extendedRule3Key_constitutional_derived target view fuel excluded
      frame.firstCursor frame.endpointFrame.firstKey.rule3 firstDerived,
    input.extendedRule3Key_constitutional_derived target view fuel excluded
      frame.secondCursor frame.endpointFrame.secondKey.rule3 secondDerived⟩

/-! ## Connection to the existing short-circuit result relation -/

/-- The root-strict constructor of the short-circuit result relation is a packaged strict
evidence. -/
theorem strictEndpointEvidence_of_shortCircuit_rootRule1aStrict
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    {first second : input.Atom}
    {firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel}
    {priority : input.LocalizedRule3EndpointPriority}
    (actualPair : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor firstCursor first)
    (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor secondCursor second)
    (fresh : input.DeclarativeLocalizedRule3RootObservation
      first second firstCursor secondCursor priority) :
    input.DeclarativeLocalizedRule3StrictEndpointEvidence
      endpoint partner endpointCursor first second firstCursor secondCursor priority :=
  DeclarativeLocalizedRule3StrictEndpointEvidence.rootRule1aStrict
    actualPair firstReference secondReference fresh

/-- The constitutional-strict constructor of the short-circuit result relation is a packaged strict
evidence. -/
theorem strictEndpointEvidence_of_shortCircuit_constitutionalStrict
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (endpoint partner : input.Atom)
    (endpointCursor : input.LocalizedRerootCursor carrierFuel)
    {first second : input.Atom}
    {firstCursor secondCursor : input.LocalizedRerootCursor carrierFuel}
    {priority : input.LocalizedRule3EndpointPriority}
    {firstKey secondKey : OfficialRuleMajorKey input.Atom}
    {firstFuel secondFuel : Nat}
    (actualPair : input.localizedRule3ExplicitSubstituents endpoint partner = [first, second])
    (firstReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor firstCursor first)
    (secondReference : input.CanonicalLocalizedRule3ReferenceCursor
      endpointCursor secondCursor second)
    (firstDerived : input.DeclarativeLocalizedRerootRuleMajorKey
      firstFuel firstCursor firstKey)
    (secondDerived : input.DeclarativeLocalizedRerootRuleMajorKey
      secondFuel secondCursor secondKey)
    (strict : (OfficialRuleMajorKey.compare firstKey secondKey = Ordering.gt ∧
        priority = .senior first) ∨
      (OfficialRuleMajorKey.compare firstKey secondKey = Ordering.lt ∧
        priority = .senior second)) :
    input.DeclarativeLocalizedRule3StrictEndpointEvidence
      endpoint partner endpointCursor first second firstCursor secondCursor priority :=
  DeclarativeLocalizedRule3StrictEndpointEvidence.constitutionalStrict
    actualPair firstReference secondReference firstDerived secondDerived strict

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
