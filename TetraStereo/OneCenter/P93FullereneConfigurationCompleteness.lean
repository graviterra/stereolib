import TetraStereo.OneCenter.P93CyclicConfiguration

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP93.Cyclic

/-!
# Exact P-93.5.6 fullerene classification and descriptor obligations

`P93CyclicConfiguration` states the four fullerene chirality classes independently, but did not
yet prove that the complete four-way relation is functional or give an executable classifier.
This module closes that mathematical boundary and then compiles the class-dependent descriptor
requirements.  The five Boolean substitution tests remain explicit chemical/perception evidence;
no molecular graph is declared to be a fullerene merely because it can carry those Booleans.
-/

instance (test : FullereneSubstitutionTest) (chiralityType : FullereneChiralityType) :
    Decidable (FullereneTypeMatches test chiralityType) := by
  cases chiralityType <;> unfold FullereneTypeMatches <;> infer_instance

/-- Exhaustive finite vocabulary of the four P-93.5.6 fullerene chirality classes. -/
def allFullereneChiralityTypes : List FullereneChiralityType :=
  [.inherentlyChiralParent, .inherentlyChiralSubstitutionPattern,
    .noninherentlyChiralSubstitutionPattern, .chiralSubstituentsOnly]

@[simp] theorem mem_allFullereneChiralityTypes
    (chiralityType : FullereneChiralityType) :
    chiralityType ∈ allFullereneChiralityTypes := by
  cases chiralityType <;> simp [allFullereneChiralityTypes]

theorem allFullereneChiralityTypes_nodup : allFullereneChiralityTypes.Nodup := by
  simp [allFullereneChiralityTypes]

/-- The four independent P-93.5.6 class predicates are mutually exclusive. -/
theorem fullereneTypeMatches_subsingleton
    (test : FullereneSubstitutionTest) {left right : FullereneChiralityType}
    (leftMatches : FullereneTypeMatches test left)
    (rightMatches : FullereneTypeMatches test right) :
    left = right := by
  cases left <;> cases right <;>
    simp_all [FullereneTypeMatches]

/-- Type 4 is reached only at the third substitution-test step, where the original derivative is
itself chiral.  Merely containing chiral substituents is insufficient because enantiomorphic
substructures can cancel in an achiral derivative. -/
theorem fullerene_chiralSubstituentsOnly_requires_originalDerivativeChiral
    (test : FullereneSubstitutionTest)
    (matched : FullereneTypeMatches test .chiralSubstituentsOnly) :
    test.originalDerivativeChiral = true :=
  matched.2.1

/-- Executable exact classifier for the four independent fullerene chirality classes. -/
def fullereneChiralityType? (test : FullereneSubstitutionTest) :
    Option FullereneChiralityType :=
  allFullereneChiralityTypes.find? fun chiralityType =>
    decide (FullereneTypeMatches test chiralityType)

/-- Classification succeeds exactly for the independently stated P-93.5.6 class relation. -/
@[simp] theorem fullereneChiralityType?_eq_some_iff
    (test : FullereneSubstitutionTest) (chiralityType : FullereneChiralityType) :
    fullereneChiralityType? test = some chiralityType ↔
      FullereneTypeMatches test chiralityType := by
  constructor
  · intro computed
    have observed :
        allFullereneChiralityTypes.find? (fun candidate =>
          decide (FullereneTypeMatches test candidate)) = some chiralityType := by
      simpa [fullereneChiralityType?] using computed
    exact of_decide_eq_true
      (List.find?_some
        (p := fun candidate => decide (FullereneTypeMatches test candidate)) observed)
  · intro derived
    cases computed : fullereneChiralityType? test with
    | none =>
        have observed :
            allFullereneChiralityTypes.find? (fun candidate =>
              decide (FullereneTypeMatches test candidate)) = none := by
          simpa [fullereneChiralityType?] using computed
        have rejects := List.find?_eq_none.mp observed chiralityType
          (mem_allFullereneChiralityTypes chiralityType)
        exact False.elim (rejects (decide_eq_true derived))
    | some actual =>
        have actualObserved :
            allFullereneChiralityTypes.find? (fun candidate =>
              decide (FullereneTypeMatches test candidate)) = some actual := by
          simpa [fullereneChiralityType?] using computed
        have actualMatches : FullereneTypeMatches test actual :=
          of_decide_eq_true
            (List.find?_some
              (p := fun candidate => decide (FullereneTypeMatches test candidate))
              actualObserved)
        exact congrArg some
          (fullereneTypeMatches_subsingleton test actualMatches derived)

/-- Explicit chemical-data pattern for which none of the four P-93.5.6 classes applies. -/
def FullereneChiralityClassificationRefusal
    (test : FullereneSubstitutionTest) : Prop :=
  test.parentChiral = false ∧
    test.allSubstituentsReplacedByAchiralTChiral = false ∧
    ((test.substitutionPatternWithActualIdentitiesChiral = true ∧
        test.originalDerivativeChiral = false) ∨
      (test.substitutionPatternWithActualIdentitiesChiral = false ∧
        (test.originalDerivativeChiral = false ∨
          test.hasChiralSubstituent = false)))

/-- The classifier's `none` result has an exhaustive, field-level meaning. -/
theorem fullereneChiralityType?_eq_none_iff_refusal
    (test : FullereneSubstitutionTest) :
    fullereneChiralityType? test = none ↔
      FullereneChiralityClassificationRefusal test := by
  cases test with
  | mk parent original replaced actual hasChiral =>
      cases parent <;> cases original <;> cases replaced <;>
        cases actual <;> cases hasChiral <;>
        simp [fullereneChiralityType?, allFullereneChiralityTypes,
          FullereneTypeMatches, FullereneChiralityClassificationRefusal]

/-- Evidence needed to materialize the descriptor kinds required by the classified fullerene.
The numbering kind and turn jointly determine the P-93.5.6 `f,xC/A` cage descriptor; substituent
completeness means that all required substituent CIP descriptors have already been supplied by
their own independent rules. -/
structure FullereneDescriptorEvidence where
  cageNumberingKind : Option FullereneNumberingKind
  cageTurn : Option ThreeLocantTurn
  everyChiralSubstituentHasCIP : Bool
  deriving DecidableEq, Repr

/-- Typed descriptor payload emitted for one P-93.5.6 requirement. -/
inductive FullereneDescriptorPayload where
  | cageHandedness
      (numberingKind : FullereneNumberingKind)
      (descriptor : FullereneHandedness)
  | substituentCIPComplete
  deriving DecidableEq, Repr

def FullereneDescriptorPayload.requirement :
    FullereneDescriptorPayload → FullereneDescriptorRequirement
  | .cageHandedness _ _ => .cageHandedness
  | .substituentCIPComplete => .substituentCIP

/-- Independent exact meaning of the payload list for a classified fullerene. -/
def FullereneDescriptorPayloadJudgment
    (chiralityType : FullereneChiralityType)
    (evidence : FullereneDescriptorEvidence)
    (payloads : List FullereneDescriptorPayload) : Prop :=
  match chiralityType with
  | .inherentlyChiralParent
  | .inherentlyChiralSubstitutionPattern
  | .noninherentlyChiralSubstitutionPattern =>
      ∃ numberingKind turn,
        evidence.cageNumberingKind = some numberingKind ∧
          evidence.cageTurn = some turn ∧
          payloads = [.cageHandedness numberingKind (fullereneHandedness turn)]
  | .chiralSubstituentsOnly =>
      evidence.everyChiralSubstituentHasCIP = true ∧
        payloads = [.substituentCIPComplete]

/-- Compile the class-dependent P-93.5.6 descriptor obligation. -/
def fullereneDescriptorPayloads?
    (chiralityType : FullereneChiralityType)
    (evidence : FullereneDescriptorEvidence) :
    Option (List FullereneDescriptorPayload) :=
  match chiralityType with
  | .inherentlyChiralParent
  | .inherentlyChiralSubstitutionPattern
  | .noninherentlyChiralSubstitutionPattern =>
      do
        let numberingKind ← evidence.cageNumberingKind
        let turn ← evidence.cageTurn
        pure [.cageHandedness numberingKind (fullereneHandedness turn)]
  | .chiralSubstituentsOnly =>
      if evidence.everyChiralSubstituentHasCIP then
        some [.substituentCIPComplete]
      else none

/-- Descriptor materialization is exact against the independent class-specific judgment. -/
@[simp] theorem fullereneDescriptorPayloads?_eq_some_iff
    (chiralityType : FullereneChiralityType)
    (evidence : FullereneDescriptorEvidence)
    (payloads : List FullereneDescriptorPayload) :
    fullereneDescriptorPayloads? chiralityType evidence = some payloads ↔
      FullereneDescriptorPayloadJudgment chiralityType evidence payloads := by
  rcases evidence with ⟨numberingKind, turn, substituentCIP⟩
  cases chiralityType <;>
    cases numberingKind <;>
    cases turn <;>
    cases substituentCIP <;>
    simp [fullereneDescriptorPayloads?, FullereneDescriptorPayloadJudgment, eq_comm]

/-- Explicit negative meaning of missing class-dependent descriptor evidence. -/
def FullereneDescriptorEvidenceRefusal
    (chiralityType : FullereneChiralityType)
    (evidence : FullereneDescriptorEvidence) : Prop :=
  match chiralityType with
  | .inherentlyChiralParent
  | .inherentlyChiralSubstitutionPattern
  | .noninherentlyChiralSubstitutionPattern =>
      evidence.cageNumberingKind = none ∨ evidence.cageTurn = none
  | .chiralSubstituentsOnly => evidence.everyChiralSubstituentHasCIP = false

/-- Descriptor materialization refuses exactly when its required evidence is absent. -/
theorem fullereneDescriptorPayloads?_eq_none_iff_refusal
    (chiralityType : FullereneChiralityType)
    (evidence : FullereneDescriptorEvidence) :
    fullereneDescriptorPayloads? chiralityType evidence = none ↔
      FullereneDescriptorEvidenceRefusal chiralityType evidence := by
  rcases evidence with ⟨numberingKind, turn, substituentCIP⟩
  cases chiralityType <;> cases numberingKind <;>
    cases turn <;>
    cases substituentCIP <;>
    simp [fullereneDescriptorPayloads?, FullereneDescriptorEvidenceRefusal]

/-- Every independently judged payload list contains exactly the descriptor kinds mandated by
P-93.5.6 for its chirality class. -/
theorem FullereneDescriptorPayloadJudgment.requirements_exact
    (chiralityType : FullereneChiralityType)
    (evidence : FullereneDescriptorEvidence)
    (payloads : List FullereneDescriptorPayload)
    (judged : FullereneDescriptorPayloadJudgment chiralityType evidence payloads) :
    payloads.map FullereneDescriptorPayload.requirement =
      RequiredFullereneDescriptorKinds chiralityType := by
  cases chiralityType with
  | inherentlyChiralParent =>
      rcases judged with ⟨numberingKind, turn, _, _, rfl⟩
      rfl
  | inherentlyChiralSubstitutionPattern =>
      rcases judged with ⟨numberingKind, turn, _, _, rfl⟩
      rfl
  | noninherentlyChiralSubstitutionPattern =>
      rcases judged with ⟨numberingKind, turn, _, _, rfl⟩
      rfl
  | chiralSubstituentsOnly =>
      rcases judged with ⟨_, rfl⟩
      rfl

/-- Every cage-handedness payload retains the numbering convention required by the `f,xC/A`
descriptor, rather than emitting an unqualified `C/A` value. -/
theorem FullereneDescriptorPayloadJudgment.cage_numbering_retained
    (chiralityType : FullereneChiralityType)
    (evidence : FullereneDescriptorEvidence)
    (payloads : List FullereneDescriptorPayload)
    (requiresCageHandedness : chiralityType ≠ .chiralSubstituentsOnly)
    (judged : FullereneDescriptorPayloadJudgment chiralityType evidence payloads) :
    ∃ numberingKind turn,
      evidence.cageNumberingKind = some numberingKind ∧
        evidence.cageTurn = some turn ∧
        payloads =
          [.cageHandedness numberingKind (fullereneHandedness turn)] := by
  cases chiralityType with
  | inherentlyChiralParent => exact judged
  | inherentlyChiralSubstitutionPattern => exact judged
  | noninherentlyChiralSubstitutionPattern => exact judged
  | chiralSubstituentsOnly => exact False.elim (requiresCageHandedness rfl)

/-- One caller-identified fullerene cage and the independent P-93.5.6 evidence used to classify
it. `unit` is an opaque physical-cage identity at this layer; graph-level fullerene perception is
a separate upstream obligation. -/
structure FullereneConfigurationInput where
  unit : List Nat
  substitutionTest : FullereneSubstitutionTest
  descriptorEvidence : FullereneDescriptorEvidence

/-- Complete P-93.5.6 result for one identified fullerene cage. -/
structure FullereneConfigurationAssignment where
  unit : List Nat
  chiralityType : FullereneChiralityType
  payloads : List FullereneDescriptorPayload
  deriving DecidableEq, Repr

/-- Independent complete meaning of one fullerene configuration assignment. -/
def FullereneConfigurationAssignmentJudgment
    (input : FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) : Prop :=
  ∃ chiralityType payloads,
    FullereneTypeMatches input.substitutionTest chiralityType ∧
      FullereneDescriptorPayloadJudgment
        chiralityType input.descriptorEvidence payloads ∧
      assignment =
        { unit := input.unit
          chiralityType
          payloads }

/-- Total executable P-93.5.6 classifier/materializer for one identified cage. -/
def fullereneConfigurationAssignment?
    (input : FullereneConfigurationInput) :
    Option FullereneConfigurationAssignment := do
  let chiralityType ← fullereneChiralityType? input.substitutionTest
  let payloads ← fullereneDescriptorPayloads?
    chiralityType input.descriptorEvidence
  some { unit := input.unit, chiralityType, payloads }

/-- End-to-end local success is exactly the independent class and descriptor-requirement
judgment. -/
theorem fullereneConfigurationAssignment?_eq_some_iff
    (input : FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment) :
    fullereneConfigurationAssignment? input = some assignment ↔
      FullereneConfigurationAssignmentJudgment input assignment := by
  constructor
  · intro computed
    unfold fullereneConfigurationAssignment? at computed
    cases typeComputed : fullereneChiralityType? input.substitutionTest with
    | none => simp [typeComputed] at computed
    | some chiralityType =>
        cases payloadsComputed : fullereneDescriptorPayloads?
            chiralityType input.descriptorEvidence with
        | none => simp [typeComputed, payloadsComputed] at computed
        | some payloads =>
            simp [typeComputed, payloadsComputed] at computed
            subst assignment
            exact ⟨chiralityType, payloads,
              (fullereneChiralityType?_eq_some_iff
                input.substitutionTest chiralityType).mp typeComputed,
              (fullereneDescriptorPayloads?_eq_some_iff
                chiralityType input.descriptorEvidence payloads).mp payloadsComputed,
              rfl⟩
  · rintro ⟨chiralityType, payloads, typeMatches, payloadsJudged, rfl⟩
    have typeComputed :=
      (fullereneChiralityType?_eq_some_iff
        input.substitutionTest chiralityType).mpr typeMatches
    have payloadsComputed :=
      (fullereneDescriptorPayloads?_eq_some_iff
        chiralityType input.descriptorEvidence payloads).mpr payloadsJudged
    simp [fullereneConfigurationAssignment?, typeComputed, payloadsComputed]

/-- Exact local refusal: either the supplied substitution test matches no P-93.5.6 class, or its
unique class lacks the descriptor evidence that class requires. -/
def FullereneConfigurationRefusal (input : FullereneConfigurationInput) : Prop :=
  FullereneChiralityClassificationRefusal input.substitutionTest ∨
    ∃ chiralityType,
      FullereneTypeMatches input.substitutionTest chiralityType ∧
        FullereneDescriptorEvidenceRefusal
          chiralityType input.descriptorEvidence

/-- The local analyzer returns `none` exactly for the exhaustive independent refusal. -/
theorem fullereneConfigurationAssignment?_eq_none_iff_refusal
    (input : FullereneConfigurationInput) :
    fullereneConfigurationAssignment? input = none ↔
      FullereneConfigurationRefusal input := by
  constructor
  · intro refused
    unfold fullereneConfigurationAssignment? at refused
    cases typeComputed : fullereneChiralityType? input.substitutionTest with
    | none =>
        exact .inl
          ((fullereneChiralityType?_eq_none_iff_refusal
            input.substitutionTest).mp typeComputed)
    | some chiralityType =>
        have typeMatches :=
          (fullereneChiralityType?_eq_some_iff
            input.substitutionTest chiralityType).mp typeComputed
        cases payloadsComputed : fullereneDescriptorPayloads?
            chiralityType input.descriptorEvidence with
        | none =>
            exact .inr ⟨chiralityType, typeMatches,
              (fullereneDescriptorPayloads?_eq_none_iff_refusal
                chiralityType input.descriptorEvidence).mp payloadsComputed⟩
        | some payloads => simp [typeComputed, payloadsComputed] at refused
  · intro refusal
    rcases refusal with classificationRefusal | ⟨chiralityType, typeMatches, evidenceRefusal⟩
    · have typeNone :=
        (fullereneChiralityType?_eq_none_iff_refusal
          input.substitutionTest).mpr classificationRefusal
      simp [fullereneConfigurationAssignment?, typeNone]
    · have typeComputed :=
        (fullereneChiralityType?_eq_some_iff
          input.substitutionTest chiralityType).mpr typeMatches
      have payloadsNone :=
        (fullereneDescriptorPayloads?_eq_none_iff_refusal
          chiralityType input.descriptorEvidence).mpr evidenceRefusal
      simp [fullereneConfigurationAssignment?, typeComputed, payloadsNone]

/-- Positive readiness is existence of the complete independent assignment judgment. -/
def FullereneConfigurationReady (input : FullereneConfigurationInput) : Prop :=
  ∃ assignment, FullereneConfigurationAssignmentJudgment input assignment

theorem fullereneConfigurationAssignment?_isSome_iff_ready
    (input : FullereneConfigurationInput) :
    (fullereneConfigurationAssignment? input).isSome = true ↔
      FullereneConfigurationReady input := by
  rw [Option.isSome_iff_exists]
  exact exists_congr fun assignment =>
    fullereneConfigurationAssignment?_eq_some_iff input assignment


theorem fullereneConfigurationReady_iff_not_refusal
    (input : FullereneConfigurationInput) :
    FullereneConfigurationReady input ↔ ¬ FullereneConfigurationRefusal input := by
  rw [← fullereneConfigurationAssignment?_isSome_iff_ready]
  rw [← fullereneConfigurationAssignment?_eq_none_iff_refusal]
  exact Option.isSome_iff_ne_none

/-- A fixed fullerene input has at most one independently valid assignment. -/
theorem fullereneConfigurationAssignmentJudgment_subsingleton
    (input : FullereneConfigurationInput)
    {left right : FullereneConfigurationAssignment}
    (leftJudged : FullereneConfigurationAssignmentJudgment input left)
    (rightJudged : FullereneConfigurationAssignmentJudgment input right) :
    left = right := by
  have leftComputed :=
    (fullereneConfigurationAssignment?_eq_some_iff input left).mpr leftJudged
  have rightComputed :=
    (fullereneConfigurationAssignment?_eq_some_iff input right).mpr rightJudged
  rw [leftComputed] at rightComputed
  exact Option.some.inj rightComputed

/-- A complete local assignment contains exactly the descriptor kinds required by its classified
P-93.5.6 fullerene chirality type. -/
theorem FullereneConfigurationAssignmentJudgment.requirements_exact
    (input : FullereneConfigurationInput)
    (assignment : FullereneConfigurationAssignment)
    (judged : FullereneConfigurationAssignmentJudgment input assignment) :
    assignment.payloads.map FullereneDescriptorPayload.requirement =
      RequiredFullereneDescriptorKinds assignment.chiralityType := by
  rcases judged with ⟨chiralityType, payloads, _typeMatches, payloadsJudged, rfl⟩
  exact payloadsJudged.requirements_exact chiralityType input.descriptorEvidence payloads

end BlueBookP93.Cyclic
end TetraStereo.OneCenter
