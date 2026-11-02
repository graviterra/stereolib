import TetraStereo.OneCenter.AuthoritativeSemanticMancudeRule3VirtualEndpointExact
import TetraStereo.OneCenter.AuthoritativeSemanticOrdinaryDoubleBondExactReadinessCompleteness

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Whole-family exactness with virtual endpoint completions

The format-neutral molecule does not encode a serialization policy for omitted atoms.  Therefore
an absent endpoint position cannot be inferred soundly from connectivity alone: it may be implicit
hydrogen, a lone pair, or an intentionally absent position in a charged/radical state.  This module
takes the finite completion decision as explicit chemical evidence and threads it through the
actual ordinary-double-bond analyzer.

The result is exact at every remaining software boundary.  Per-bond success and refusal, family
membership, unique retained-bond occurrence, literal count one, and the whole-family dichotomy are
all equivalent to the virtual-aware canonical relation.
-/

/-- Evidence provider for the two nonpartner positions at every directed endpoint.  `none` means
that the chemical completion is unavailable and the analyzer must refuse rather than guess. -/
abbrev AromaticCanonicalRule3EndpointCompletionMap
    (source : AuthoritativeChemicalInput) :=
  (endpoint partner : source.AromaticCanonicalAtom) →
    Option AromaticCanonicalRule3EndpointCompletion

/-- Both endpoint completions accept the represented references retained in an assignment. -/
def CanonicalAromaticCanonicalOrdinaryDoubleBondVirtualEndpointAcceptance
    (source : AuthoritativeChemicalInput)
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) : Prop :=
  ∃ leftCompletion rightCompletion,
    completionAt assignment.bond.left assignment.bond.right = some leftCompletion ∧
    completionAt assignment.bond.right assignment.bond.left = some rightCompletion ∧
    source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
      assignment.bond.left assignment.bond.right assignment.leftReference leftCompletion ∧
    source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
      assignment.bond.right assignment.bond.left assignment.rightReference rightCompletion

noncomputable def aromaticCanonicalOrdinaryDoubleBondVirtualEndpointAccepted?
    (source : AuthoritativeChemicalInput)
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) : Bool :=
  match completionAt assignment.bond.left assignment.bond.right,
      completionAt assignment.bond.right assignment.bond.left with
  | some leftCompletion, some rightCompletion =>
      source.aromaticCanonicalRule3EndpointReferenceAccepted?
          assignment.bond.left assignment.bond.right assignment.leftReference leftCompletion &&
        source.aromaticCanonicalRule3EndpointReferenceAccepted?
          assignment.bond.right assignment.bond.left assignment.rightReference rightCompletion
  | _, _ => false

@[simp] theorem aromaticCanonicalOrdinaryDoubleBondVirtualEndpointAccepted?_eq_true_iff
    (source : AuthoritativeChemicalInput)
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    source.aromaticCanonicalOrdinaryDoubleBondVirtualEndpointAccepted?
        completionAt assignment = true ↔
      source.CanonicalAromaticCanonicalOrdinaryDoubleBondVirtualEndpointAcceptance
        completionAt assignment := by
  unfold aromaticCanonicalOrdinaryDoubleBondVirtualEndpointAccepted?
    CanonicalAromaticCanonicalOrdinaryDoubleBondVirtualEndpointAcceptance
  cases leftObserved : completionAt assignment.bond.left assignment.bond.right with
  | none => simp
  | some leftCompletion =>
      cases rightObserved : completionAt assignment.bond.right assignment.bond.left with
      | none => simp
      | some rightCompletion =>
          simp

/-- Canonical ordinary-double-bond meaning strengthened by exact completion of both endpoint
ligand frames. -/
def AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalSpatialJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) : Prop :=
  source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment
      carrierFuel bond leftView rightView assignment ∧
    source.CanonicalAromaticCanonicalOrdinaryDoubleBondVirtualEndpointAcceptance
      completionAt assignment

/-- The actual per-bond analyzer followed by the virtual endpoint guard. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) :
    Option source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment := do
  let assignment ← source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
    carrierFuel bond leftView rightView
  if source.aromaticCanonicalOrdinaryDoubleBondVirtualEndpointAccepted?
      completionAt assignment then
    some assignment
  else
    none

/-- Per-bond virtual-aware emission is exactly the strengthened canonical judgment. -/
theorem aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?
        carrierFuel completionAt bond leftView rightView = some assignment ↔
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalSpatialJudgment
        carrierFuel completionAt bond leftView rightView assignment := by
  constructor
  · intro computed
    unfold aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?
      at computed
    cases baseComputed : source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?
        carrierFuel bond leftView rightView with
    | none => simp [baseComputed] at computed
    | some observed =>
        cases accepted : source.aromaticCanonicalOrdinaryDoubleBondVirtualEndpointAccepted?
            completionAt observed <;>
          simp [baseComputed, accepted] at computed
        subst assignment
        exact ⟨
          (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_canonical
            carrierFuel bond leftView rightView observed).mp baseComputed,
          (source.aromaticCanonicalOrdinaryDoubleBondVirtualEndpointAccepted?_eq_true_iff
            completionAt observed).mp accepted⟩
  · rintro ⟨baseDerived, acceptedDerived⟩
    have baseComputed :=
      (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_canonical
        carrierFuel bond leftView rightView assignment).mpr baseDerived
    have accepted :=
      (source.aromaticCanonicalOrdinaryDoubleBondVirtualEndpointAccepted?_eq_true_iff
        completionAt assignment).mpr acceptedDerived
    simp [aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?,
      baseComputed, accepted]

/-- Minimal virtual-aware per-bond readiness. -/
def AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) : Prop :=
  ∃ assignment,
    source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalSpatialJudgment
      carrierFuel completionAt bond leftView rightView assignment

theorem aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?_isSome_iff_readiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) :
    (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?
      carrierFuel completionAt bond leftView rightView).isSome = true ↔
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalReadiness
        carrierFuel completionAt bond leftView rightView := by
  rw [Option.isSome_iff_exists]
  exact exists_congr fun assignment =>
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?_eq_some_iff_canonical
      carrierFuel completionAt bond leftView rightView assignment

theorem aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?_eq_none_iff_not_ready
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) :
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?
        carrierFuel completionAt bond leftView rightView = none ↔
      ¬ source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalReadiness
        carrierFuel completionAt bond leftView rightView := by
  cases computed :
      source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?
        carrierFuel completionAt bond leftView rightView with
  | none =>
      simp only [true_iff]
      rintro ⟨assignment, derived⟩
      have positive :=
        (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?_eq_some_iff_canonical
          carrierFuel completionAt bond leftView rightView assignment).mpr derived
      rw [computed] at positive
      contradiction
  | some assignment =>
      simp only [reduceCtorEq, false_iff]
      intro notReady
      exact notReady ⟨assignment,
        (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?_eq_some_iff_canonical
          carrierFuel completionAt bond leftView rightView assignment).mp computed⟩

/-- Whole-family analyzer: retain exactly the base assignments accepted by the explicit endpoint
completion evidence. -/
noncomputable def analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap) :
    List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment :=
  (source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial carrierFuel viewAt).filter
    (source.aromaticCanonicalOrdinaryDoubleBondVirtualEndpointAccepted? completionAt)

theorem mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈ source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints
        carrierFuel viewAt completionAt ↔
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalSpatialJudgment
          carrierFuel completionAt bond (viewAt bond.left) (viewAt bond.right) assignment := by
  rw [analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints,
    List.mem_filter,
    source.aromaticCanonicalOrdinaryDoubleBondVirtualEndpointAccepted?_eq_true_iff,
    source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff_canonical]
  constructor
  · rintro ⟨⟨bond, canonical⟩, accepted⟩
    exact ⟨bond, canonical, accepted⟩
  · rintro ⟨bond, canonical, accepted⟩
    exact ⟨⟨bond, canonical⟩, accepted⟩

/-- Every whole-family result is equivalently produced by the virtual-aware per-bond evaluator. -/
theorem mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_perBond
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈ source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints
        carrierFuel viewAt completionAt ↔
      ∃ bond,
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?
          carrierFuel completionAt bond (viewAt bond.left) (viewAt bond.right) =
            some assignment := by
  rw [source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_canonical]
  exact exists_congr fun bond =>
    (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?_eq_some_iff_canonical
      carrierFuel completionAt bond (viewAt bond.left) (viewAt bond.right) assignment).symm

theorem analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_nodup
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap) :
    (source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints
      carrierFuel viewAt completionAt).Nodup := by
  exact (source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_nodup
    carrierFuel viewAt).filter _

/-- Existence of a retained whole-family assignment for one bond is exactly virtual readiness. -/
theorem exists_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_readiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    (∃ assignment,
        assignment ∈
          source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints
            carrierFuel viewAt completionAt ∧
        assignment.bond = bond) ↔
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalReadiness
        carrierFuel completionAt bond (viewAt bond.left) (viewAt bond.right) := by
  constructor
  · rintro ⟨assignment, present, assignmentBond⟩
    obtain ⟨origin, canonical, accepted⟩ :=
      (source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_canonical
        carrierFuel viewAt completionAt assignment).mp present
    have originIdentity : origin = bond := canonical.sound.1.symm.trans assignmentBond
    subst origin
    exact ⟨assignment, canonical, accepted⟩
  · rintro ⟨assignment, canonical, accepted⟩
    refine ⟨assignment, ?_, canonical.sound.1⟩
    exact
      (source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_canonical
        carrierFuel viewAt completionAt assignment).mpr ⟨bond, canonical, accepted⟩

/-- Virtual readiness is equivalent to unique retained-bond occurrence. -/
theorem existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_readiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    (∃! assignment,
        assignment ∈
          source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints
            carrierFuel viewAt completionAt ∧
        assignment.bond = bond) ↔
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalReadiness
        carrierFuel completionAt bond (viewAt bond.left) (viewAt bond.right) := by
  constructor
  · rintro ⟨assignment, property, _unique⟩
    exact
      (source.exists_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_readiness
        carrierFuel viewAt completionAt bond).mp ⟨assignment, property⟩
  · intro ready
    obtain ⟨assignment, assignmentPresent, assignmentBond⟩ :=
      (source.exists_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_readiness
        carrierFuel viewAt completionAt bond).mpr ready
    have baseReady :
        source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalReadiness
          carrierFuel bond (viewAt bond.left) (viewAt bond.right) := by
      obtain ⟨witness, canonical, _accepted⟩ := ready
      exact ⟨witness, canonical⟩
    obtain ⟨baseAssignment, baseProperty, baseUnique⟩ :=
      (source.existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial_iff_readiness
        carrierFuel viewAt bond).mpr baseReady
    refine ⟨assignment, ⟨assignmentPresent, assignmentBond⟩, ?_⟩
    intro other ⟨otherPresent, otherBond⟩
    have assignmentBasePresent :
        assignment ∈ source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
          carrierFuel viewAt := by
      exact (List.mem_filter.mp assignmentPresent).1
    have otherBasePresent :
        other ∈ source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatial
          carrierFuel viewAt := by
      exact (List.mem_filter.mp otherPresent).1
    have assignmentEq : assignment = baseAssignment :=
      baseUnique assignment ⟨assignmentBasePresent, assignmentBond⟩
    have otherEq : other = baseAssignment :=
      baseUnique other ⟨otherBasePresent, otherBond⟩
    exact otherEq.trans assignmentEq.symm

/-- Literal count one in the virtual-aware family list is equivalent to virtual readiness. -/
theorem exists_count_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_eq_one_iff_readiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    (∃ assignment,
        assignment.bond = bond ∧
          (source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints
            carrierFuel viewAt completionAt).count assignment = 1) ↔
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalReadiness
        carrierFuel completionAt bond (viewAt bond.left) (viewAt bond.right) := by
  constructor
  · rintro ⟨assignment, assignmentBond, countOne⟩
    apply
      (source.exists_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_readiness
        carrierFuel viewAt completionAt bond).mp
    refine ⟨assignment, ?_, assignmentBond⟩
    exact List.count_pos_iff.mp (by omega)
  · intro ready
    obtain ⟨assignment, property, _unique⟩ :=
      (source.existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_readiness
        carrierFuel viewAt completionAt bond).mpr ready
    refine ⟨assignment, property.2, ?_⟩
    rw [(source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_nodup
      carrierFuel viewAt completionAt).count]
    simp [property.1]

/-- Every canonical individual bond is exhaustively classified as one virtual-aware count-one
success or an exact virtual-aware refusal. -/
theorem every_aromaticCanonicalOrdinaryDoubleBond_virtual_exact_readiness_or_refusal
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (completionAt : source.AromaticCanonicalRule3EndpointCompletionMap) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      (source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalReadiness
          carrierFuel completionAt bond (viewAt bond.left) (viewAt bond.right) ∧
        ∃! assignment,
          assignment ∈
            source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints
              carrierFuel viewAt completionAt ∧
          assignment.bond = bond) ∨
      (¬ source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalReadiness
          carrierFuel completionAt bond (viewAt bond.left) (viewAt bond.right) ∧
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?
          carrierFuel completionAt bond (viewAt bond.left) (viewAt bond.right) = none) := by
  intro bond _owner
  by_cases ready :
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalReadiness
        carrierFuel completionAt bond (viewAt bond.left) (viewAt bond.right)
  · exact Or.inl ⟨ready,
      (source.existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_readiness
        carrierFuel viewAt completionAt bond).mpr ready⟩
  · exact Or.inr ⟨ready,
      (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?_eq_none_iff_not_ready
        carrierFuel completionAt bond (viewAt bond.left) (viewAt bond.right)).mpr ready⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
