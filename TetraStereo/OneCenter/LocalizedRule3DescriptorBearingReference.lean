import TetraStereo.OneCenter.LocalizedOccurrenceRule3Through5Descriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Descriptor-bearing Rule-3 endpoint references

The first localized spatial implementation selected an alkene reference only when Rules 1a--2
were already strict.  That is sound on its stated subdomain, but a constitutional tie is not in
general an unresolved endpoint: occurrence-local Rules 3--5 may separate descriptor-bearing or
cyclic branches, while a complete tie proves that the endpoint is nonstereogenic.

This module makes that distinction explicit.  It is deliberately factored at the compiled-key
boundary.  A later occurrence-path module must construct each candidate key from the exact
reroot cursor and discharge the abstract `KeyMeaning` premise below.  No atom-global descriptor
lookup is accepted here.
-/

namespace CertifiedLocalizedCIPInput

/-- The two physical endpoint candidates together with their complete occurrence-local
Rules-1a--5 keys. -/
structure LocalizedRule3EndpointKeyFrame
    (input : CertifiedLocalizedCIPInput) where
  first : input.Atom
  second : input.Atom
  firstKey : input.LocalizedOccurrenceRule3Through5Key
  secondKey : input.LocalizedOccurrenceRule3Through5Key

/-- Compile the exact two explicit non-partner candidates with a caller-supplied occurrence-local
key builder.  Candidate enumeration remains molecule-backed and canonical. -/
noncomputable def buildLocalizedRule3EndpointKeyFrame?
    (input : CertifiedLocalizedCIPInput) (endpoint partner : input.Atom)
    (keyOf : input.Atom → Option input.LocalizedOccurrenceRule3Through5Key) :
    Option input.LocalizedRule3EndpointKeyFrame :=
  match input.localizedRule3ExplicitSubstituents endpoint partner with
  | [first, second] => do
      let firstKey ← keyOf first
      let secondKey ← keyOf second
      some { first, second, firstKey, secondKey }
  | _ => none

/-- Independent endpoint-frame meaning, parameterized by the concrete occurrence-local key
derivation that the next layer must supply. -/
def DeclarativeLocalizedRule3EndpointKeyFrame
    (input : CertifiedLocalizedCIPInput) (endpoint partner : input.Atom)
    (KeyMeaning : input.Atom → input.LocalizedOccurrenceRule3Through5Key → Prop)
    (frame : input.LocalizedRule3EndpointKeyFrame) : Prop :=
  input.localizedRule3ExplicitSubstituents endpoint partner =
      [frame.first, frame.second] ∧
    KeyMeaning frame.first frame.firstKey ∧
    KeyMeaning frame.second frame.secondKey

/-- A successful endpoint compilation contains exactly the molecular candidates and inherits the
independent meaning of both supplied keys. -/
theorem buildLocalizedRule3EndpointKeyFrame?_sound
    (input : CertifiedLocalizedCIPInput) (endpoint partner : input.Atom)
    (keyOf : input.Atom → Option input.LocalizedOccurrenceRule3Through5Key)
    (KeyMeaning : input.Atom → input.LocalizedOccurrenceRule3Through5Key → Prop)
    (keySound : ∀ reference key, keyOf reference = some key → KeyMeaning reference key)
    (frame : input.LocalizedRule3EndpointKeyFrame)
    (computed : input.buildLocalizedRule3EndpointKeyFrame?
      endpoint partner keyOf = some frame) :
    input.DeclarativeLocalizedRule3EndpointKeyFrame
      endpoint partner KeyMeaning frame := by
  unfold buildLocalizedRule3EndpointKeyFrame? at computed
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
              cases firstComputed : keyOf first with
              | none => simp [firstComputed] at computed
              | some firstKey =>
                  cases secondComputed : keyOf second with
                  | none => simp [firstComputed, secondComputed] at computed
                  | some secondKey =>
                      simp [firstComputed, secondComputed] at computed
                      subst frame
                      exact ⟨candidatesIdentity,
                        keySound first firstKey firstComputed,
                        keySound second secondKey secondComputed⟩

/-- Complete endpoint priority has two strict reference outcomes and one proved terminal tie. -/
inductive LocalizedRule3EndpointPriority
    (input : CertifiedLocalizedCIPInput) where
  | senior (reference : input.Atom)
  | nonstereogenic
  deriving DecidableEq, Repr

/-- Select by the complete unary Rules-1a--5 ordering.  Equality is chemical
nonstereogenicity—not computational failure—because both complete keys are already present. -/
def localizedRule3EndpointPriority
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame) :
    input.LocalizedRule3EndpointPriority :=
  match input.compareLocalizedOccurrenceRule3Through5Keys
      frame.firstKey frame.secondKey with
  | .gt => .senior frame.first
  | .lt => .senior frame.second
  | .eq => .nonstereogenic

/-- Independent relational reading of the complete endpoint comparison. -/
inductive DeclarativeLocalizedRule3EndpointPriority
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame) :
    input.LocalizedRule3EndpointPriority → Prop
  | firstSenior
      (strict : input.compareLocalizedOccurrenceRule3Through5Keys
        frame.firstKey frame.secondKey = Ordering.gt) :
      input.DeclarativeLocalizedRule3EndpointPriority frame (.senior frame.first)
  | secondSenior
      (strict : input.compareLocalizedOccurrenceRule3Through5Keys
        frame.firstKey frame.secondKey = Ordering.lt) :
      input.DeclarativeLocalizedRule3EndpointPriority frame (.senior frame.second)
  | nonstereogenic
      (tied : input.compareLocalizedOccurrenceRule3Through5Keys
        frame.firstKey frame.secondKey = Ordering.eq) :
      input.DeclarativeLocalizedRule3EndpointPriority frame (.nonstereogenic)

/-- The executable endpoint decision is exactly the relational complete comparison. -/
theorem localizedRule3EndpointPriority_eq_iff
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame)
    (priority : input.LocalizedRule3EndpointPriority) :
    input.localizedRule3EndpointPriority frame = priority ↔
      input.DeclarativeLocalizedRule3EndpointPriority frame priority := by
  unfold localizedRule3EndpointPriority
  generalize compared : input.compareLocalizedOccurrenceRule3Through5Keys
    frame.firstKey frame.secondKey = outcome
  cases outcome with
  | lt =>
      constructor
      · intro computed
        subst priority
        exact DeclarativeLocalizedRule3EndpointPriority.secondSenior compared
      · intro derived
        cases derived with
        | firstSenior strict => rw [compared] at strict; contradiction
        | secondSenior _ => rfl
        | nonstereogenic tied => rw [compared] at tied; contradiction
  | eq =>
      constructor
      · intro computed
        subst priority
        exact DeclarativeLocalizedRule3EndpointPriority.nonstereogenic compared
      · intro derived
        cases derived with
        | firstSenior strict => rw [compared] at strict; contradiction
        | secondSenior strict => rw [compared] at strict; contradiction
        | nonstereogenic _ => rfl
  | gt =>
      constructor
      · intro computed
        subst priority
        exact DeclarativeLocalizedRule3EndpointPriority.firstSenior compared
      · intro derived
        cases derived with
        | firstSenior _ => rfl
        | secondSenior strict => rw [compared] at strict; contradiction
        | nonstereogenic tied => rw [compared] at tied; contradiction

/-- Every computed endpoint decision has its independent complete-comparison witness. -/
theorem localizedRule3EndpointPriority_sound
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame) :
    input.DeclarativeLocalizedRule3EndpointPriority frame
      (input.localizedRule3EndpointPriority frame) :=
  (input.localizedRule3EndpointPriority_eq_iff frame _).mp rfl

/-- A complete Rules-1a--5 tie is exactly the nonstereogenic endpoint outcome. -/
theorem localizedRule3EndpointPriority_eq_nonstereogenic_iff
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame) :
    input.localizedRule3EndpointPriority frame = .nonstereogenic ↔
      input.compareLocalizedOccurrenceRule3Through5Keys
        frame.firstKey frame.secondKey = Ordering.eq := by
  unfold localizedRule3EndpointPriority
  cases input.compareLocalizedOccurrenceRule3Through5Keys
      frame.firstKey frame.secondKey <;> simp

/-- The new complete selector is conservative over the old strict constitutional subdomain. -/
theorem localizedRule3EndpointPriority_of_constitutional_gt
    (input : CertifiedLocalizedCIPInput)
    (frame : input.LocalizedRule3EndpointKeyFrame)
    (strict : OfficialRuleMajorKey.compare
      frame.firstKey.rule3.constitutional
      frame.secondKey.rule3.constitutional = Ordering.gt) :
    input.localizedRule3EndpointPriority frame = .senior frame.first := by
  have rule3Strict : input.compareLocalizedRerootRecursiveRule3SpatialKeys
      frame.firstKey.rule3 frame.secondKey.rule3 = Ordering.gt :=
    input.compareLocalizedRerootRecursiveRule3SpatialKeys_of_constitutional_gt
      frame.firstKey.rule3 frame.secondKey.rule3 strict
  simp [localizedRule3EndpointPriority,
    compareLocalizedOccurrenceRule3Through5Keys, compareLex, Ordering.byKey,
    rule3Strict]

/-- Retained endpoint decisions and final Rule-3 geometry.  Nonstereogenic units intentionally
retain both complete endpoint decisions even though no senior-reference coordinates are needed. -/
structure LocalizedRule3DescriptorBearingSpatialUnitResult
    (input : CertifiedLocalizedCIPInput) where
  leftPriority : input.LocalizedRule3EndpointPriority
  rightPriority : input.LocalizedRule3EndpointPriority
  geometry : OfficialRule3Geometry
  deriving DecidableEq, Repr

/-- Resolve a physical double bond from complete endpoint keys.  A proved tie at either endpoint
returns `nonstereogenic`; only two strict endpoints reach exact rational spatial classification. -/
noncomputable def localizedRule3DescriptorBearingSpatialUnit?
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame) :
    Option input.LocalizedRule3DescriptorBearingSpatialUnitResult :=
  if input.moleculeGraph.bond left right = 2 then
    let leftPriority := input.localizedRule3EndpointPriority leftFrame
    let rightPriority := input.localizedRule3EndpointPriority rightFrame
    match leftPriority, rightPriority with
    | .nonstereogenic, _ | _, .nonstereogenic =>
        some { leftPriority, rightPriority, geometry := .nonstereogenic }
    | .senior leftReference, .senior rightReference => do
        let leftPoint ← input.spatialPointAt? left
        let rightPoint ← input.spatialPointAt? right
        let leftReferencePoint ← input.spatialPointAt? leftReference
        let rightReferencePoint ← input.spatialPointAt? rightReference
        let geometry ← rule3GeometryOfSpatialReferences? leftPoint rightPoint
          leftReferencePoint rightReferencePoint
        some { leftPriority, rightPriority, geometry }
  else none

/-- Independent complete-key and exact-spatial meaning of the descriptor-bearing unit result. -/
def DeclarativeLocalizedRule3DescriptorBearingSpatialUnit
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (LeftKeyMeaning RightKeyMeaning :
      input.Atom → input.LocalizedOccurrenceRule3Through5Key → Prop)
    (result : input.LocalizedRule3DescriptorBearingSpatialUnitResult) : Prop :=
  input.DeclarativeLocalizedRule3EndpointKeyFrame
      left right LeftKeyMeaning leftFrame ∧
    input.DeclarativeLocalizedRule3EndpointKeyFrame
      right left RightKeyMeaning rightFrame ∧
    input.moleculeGraph.bond left right = 2 ∧
    input.DeclarativeLocalizedRule3EndpointPriority
      leftFrame result.leftPriority ∧
    input.DeclarativeLocalizedRule3EndpointPriority
      rightFrame result.rightPriority ∧
    match result.leftPriority, result.rightPriority with
    | .nonstereogenic, _ | _, .nonstereogenic =>
        result.geometry = OfficialRule3Geometry.nonstereogenic
    | .senior leftReference, .senior rightReference =>
        ∃ leftPoint rightPoint leftReferencePoint rightReferencePoint,
          input.SemanticSpatialPointAt left leftPoint ∧
          input.SemanticSpatialPointAt right rightPoint ∧
          input.SemanticSpatialPointAt leftReference leftReferencePoint ∧
          input.SemanticSpatialPointAt rightReference rightReferencePoint ∧
          RationalRule3SpatialGeometry leftPoint rightPoint
            leftReferencePoint rightReferencePoint result.geometry

/-- On independently valid endpoint frames, executable success is exactly complete endpoint
priority plus the independent rational spatial relation. -/
theorem localizedRule3DescriptorBearingSpatialUnit?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (LeftKeyMeaning RightKeyMeaning :
      input.Atom → input.LocalizedOccurrenceRule3Through5Key → Prop)
    (leftValid : input.DeclarativeLocalizedRule3EndpointKeyFrame
      left right LeftKeyMeaning leftFrame)
    (rightValid : input.DeclarativeLocalizedRule3EndpointKeyFrame
      right left RightKeyMeaning rightFrame)
    (result : input.LocalizedRule3DescriptorBearingSpatialUnitResult) :
    input.localizedRule3DescriptorBearingSpatialUnit?
        left right leftFrame rightFrame = some result ↔
      input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnit
        left right leftFrame rightFrame LeftKeyMeaning RightKeyMeaning result := by
  constructor
  · intro computed
    unfold localizedRule3DescriptorBearingSpatialUnit? at computed
    by_cases doubleBond : input.moleculeGraph.bond left right = 2
    · rw [if_pos doubleBond] at computed
      generalize leftPriorityIdentity :
          input.localizedRule3EndpointPriority leftFrame = leftPriority at computed
      generalize rightPriorityIdentity :
          input.localizedRule3EndpointPriority rightFrame = rightPriority at computed
      cases leftPriority with
      | nonstereogenic =>
          simp at computed
          subst result
          exact ⟨leftValid, rightValid, doubleBond,
            (input.localizedRule3EndpointPriority_eq_iff leftFrame _).mp
              leftPriorityIdentity,
            (input.localizedRule3EndpointPriority_eq_iff rightFrame _).mp
              rightPriorityIdentity, rfl⟩
      | senior leftReference =>
          cases rightPriority with
          | nonstereogenic =>
              simp at computed
              subst result
              exact ⟨leftValid, rightValid, doubleBond,
                (input.localizedRule3EndpointPriority_eq_iff leftFrame _).mp
                  leftPriorityIdentity,
                (input.localizedRule3EndpointPriority_eq_iff rightFrame _).mp
                  rightPriorityIdentity, rfl⟩
          | senior rightReference =>
              cases leftPointComputed : input.spatialPointAt? left with
              | none => simp [leftPointComputed] at computed
              | some leftPoint =>
                  cases rightPointComputed : input.spatialPointAt? right with
                  | none => simp [leftPointComputed, rightPointComputed] at computed
                  | some rightPoint =>
                      cases leftReferencePointComputed :
                          input.spatialPointAt? leftReference with
                      | none =>
                          simp [leftPointComputed, rightPointComputed,
                            leftReferencePointComputed] at computed
                      | some leftReferencePoint =>
                          cases rightReferencePointComputed :
                              input.spatialPointAt? rightReference with
                          | none =>
                              simp [leftPointComputed, rightPointComputed,
                                leftReferencePointComputed,
                                rightReferencePointComputed] at computed
                          | some rightReferencePoint =>
                              cases geometryComputed : rule3GeometryOfSpatialReferences?
                                  leftPoint rightPoint leftReferencePoint
                                  rightReferencePoint with
                              | none =>
                                  simp [leftPointComputed, rightPointComputed,
                                    leftReferencePointComputed,
                                    rightReferencePointComputed,
                                    geometryComputed] at computed
                              | some geometry =>
                                  simp [leftPointComputed, rightPointComputed,
                                    leftReferencePointComputed,
                                    rightReferencePointComputed,
                                    geometryComputed] at computed
                                  subst result
                                  exact ⟨leftValid, rightValid, doubleBond,
                                    (input.localizedRule3EndpointPriority_eq_iff
                                      leftFrame _).mp leftPriorityIdentity,
                                    (input.localizedRule3EndpointPriority_eq_iff
                                      rightFrame _).mp rightPriorityIdentity,
                                    ⟨leftPoint, rightPoint, leftReferencePoint,
                                      rightReferencePoint,
                                      (input.spatialPointAt?_eq_some_iff
                                        left leftPoint).mp leftPointComputed,
                                      (input.spatialPointAt?_eq_some_iff
                                        right rightPoint).mp rightPointComputed,
                                      (input.spatialPointAt?_eq_some_iff
                                        leftReference leftReferencePoint).mp
                                          leftReferencePointComputed,
                                      (input.spatialPointAt?_eq_some_iff
                                        rightReference rightReferencePoint).mp
                                          rightReferencePointComputed,
                                      (rule3GeometryOfSpatialReferences?_eq_some_iff
                                        leftPoint rightPoint leftReferencePoint
                                        rightReferencePoint geometry).mp
                                          geometryComputed⟩⟩
    · simp [doubleBond] at computed
  · rintro ⟨_leftValid, _rightValid, doubleBond,
      leftDerived, rightDerived, meaning⟩
    cases result with
    | mk leftPriority rightPriority geometry =>
        have leftComputed :=
          (input.localizedRule3EndpointPriority_eq_iff
            leftFrame leftPriority).mpr leftDerived
        have rightComputed :=
          (input.localizedRule3EndpointPriority_eq_iff
            rightFrame rightPriority).mpr rightDerived
        unfold localizedRule3DescriptorBearingSpatialUnit?
        rw [if_pos doubleBond, leftComputed, rightComputed]
        cases leftPriority with
        | nonstereogenic =>
            simp at meaning
            subst geometry
            rfl
        | senior leftReference =>
            cases rightPriority with
            | nonstereogenic =>
                simp at meaning
                subst geometry
                rfl
            | senior rightReference =>
                simp only
                rcases meaning with ⟨leftPoint, rightPoint, leftReferencePoint,
                  rightReferencePoint, leftSemantic, rightSemantic,
                  leftReferenceSemantic, rightReferenceSemantic, spatial⟩
                simp [(input.spatialPointAt?_eq_some_iff left leftPoint).mpr leftSemantic,
                  (input.spatialPointAt?_eq_some_iff right rightPoint).mpr rightSemantic,
                  (input.spatialPointAt?_eq_some_iff
                    leftReference leftReferencePoint).mpr leftReferenceSemantic,
                  (input.spatialPointAt?_eq_some_iff
                    rightReference rightReferencePoint).mpr rightReferenceSemantic,
                  (rule3GeometryOfSpatialReferences?_eq_some_iff
                    leftPoint rightPoint leftReferencePoint
                    rightReferencePoint geometry).mpr spatial]

/-- Positive unit computation is sound with respect to complete endpoint keys and exact spatial
semantics. -/
theorem localizedRule3DescriptorBearingSpatialUnit?_sound
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (LeftKeyMeaning RightKeyMeaning :
      input.Atom → input.LocalizedOccurrenceRule3Through5Key → Prop)
    (leftValid : input.DeclarativeLocalizedRule3EndpointKeyFrame
      left right LeftKeyMeaning leftFrame)
    (rightValid : input.DeclarativeLocalizedRule3EndpointKeyFrame
      right left RightKeyMeaning rightFrame)
    (result : input.LocalizedRule3DescriptorBearingSpatialUnitResult)
    (computed : input.localizedRule3DescriptorBearingSpatialUnit?
      left right leftFrame rightFrame = some result) :
    input.DeclarativeLocalizedRule3DescriptorBearingSpatialUnit
      left right leftFrame rightFrame LeftKeyMeaning RightKeyMeaning result :=
  (input.localizedRule3DescriptorBearingSpatialUnit?_eq_some_iff
    left right leftFrame rightFrame LeftKeyMeaning RightKeyMeaning
    leftValid rightValid result).mp computed

/-- Once the left endpoint has a proved complete tie, the physical double bond is returned as
nonstereogenic without demanding irrelevant coordinate evidence. -/
theorem localizedRule3DescriptorBearingSpatialUnit?_of_left_nonstereogenic
    (input : CertifiedLocalizedCIPInput) (left right : input.Atom)
    (leftFrame rightFrame : input.LocalizedRule3EndpointKeyFrame)
    (doubleBond : input.moleculeGraph.bond left right = 2)
    (leftTied : input.localizedRule3EndpointPriority leftFrame = .nonstereogenic) :
    input.localizedRule3DescriptorBearingSpatialUnit?
        left right leftFrame rightFrame =
      some
        { leftPriority := .nonstereogenic
          rightPriority := input.localizedRule3EndpointPriority rightFrame
          geometry := .nonstereogenic } := by
  simp [localizedRule3DescriptorBearingSpatialUnit?, doubleBond, leftTied]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
