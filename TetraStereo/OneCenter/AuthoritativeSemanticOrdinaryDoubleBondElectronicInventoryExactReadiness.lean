import TetraStereo.OneCenter.AuthoritativeChemicalInputEndpointElectronicInventory

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

/-!
# Whole-family ordinary-double-bond exactness from electronic inventories

This module compiles the independent two-position electronic inventory into the already exact
virtual-endpoint analyzer.  The positive judgment mentions only the base canonical spatial
judgment, the inventory-to-completion relation, and endpoint reference acceptance.  The negative
judgment is exhaustive: base-analysis failure, a vacancy/radical at either endpoint, or failure of
reference acceptance after the unique supported endpoint completions.
-/

/-- A vacancy or an unpaired-electron position prevents a closed-shell virtual completion. -/
def AromaticCanonicalRule3EndpointElectronicInventoryRefusal
    (inventory : AromaticCanonicalRule3EndpointElectronicInventory) : Prop :=
  inventory.vacancies ≠ 0 ∨ inventory.unpairedElectronPositions ≠ 0

/-- With the inventory-generated completion map, virtual acceptance is exactly support by both
independent endpoint inventories followed by acceptance of the retained references. -/
theorem canonicalOrdinaryDoubleBondVirtualEndpointAcceptance_electronicInventory_iff
    (source : AuthoritativeChemicalInput)
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    source.CanonicalAromaticCanonicalOrdinaryDoubleBondVirtualEndpointAcceptance
        (source.electronicInventoryCompletionMap inventories) assignment ↔
      ∃ leftCompletion rightCompletion,
        AromaticCanonicalRule3EndpointElectronicInventorySupports
          (inventories.inventory assignment.bond.left assignment.bond.right) leftCompletion ∧
        AromaticCanonicalRule3EndpointElectronicInventorySupports
          (inventories.inventory assignment.bond.right assignment.bond.left) rightCompletion ∧
        source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
          assignment.bond.left assignment.bond.right assignment.leftReference leftCompletion ∧
        source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
          assignment.bond.right assignment.bond.left assignment.rightReference rightCompletion := by
  unfold CanonicalAromaticCanonicalOrdinaryDoubleBondVirtualEndpointAcceptance
  constructor
  · rintro ⟨leftCompletion, rightCompletion, leftComputed, rightComputed,
      leftAccepted, rightAccepted⟩
    exact ⟨leftCompletion, rightCompletion,
      (source.electronicInventoryCompletionMap_eq_some_iff inventories
        assignment.bond.left assignment.bond.right leftCompletion).mp leftComputed,
      (source.electronicInventoryCompletionMap_eq_some_iff inventories
        assignment.bond.right assignment.bond.left rightCompletion).mp rightComputed,
      leftAccepted, rightAccepted⟩
  · rintro ⟨leftCompletion, rightCompletion, leftSupported, rightSupported,
      leftAccepted, rightAccepted⟩
    exact ⟨leftCompletion, rightCompletion,
      (source.electronicInventoryCompletionMap_eq_some_iff inventories
        assignment.bond.left assignment.bond.right leftCompletion).mpr leftSupported,
      (source.electronicInventoryCompletionMap_eq_some_iff inventories
        assignment.bond.right assignment.bond.left rightCompletion).mpr rightSupported,
      leftAccepted, rightAccepted⟩

/-- Independent positive judgment for an ordinary-double-bond result driven by endpoint electronic
inventories. -/
def AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) : Prop :=
  source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment
      carrierFuel bond leftView rightView assignment ∧
    ∃ leftCompletion rightCompletion,
      AromaticCanonicalRule3EndpointElectronicInventorySupports
        (inventories.inventory bond.left bond.right) leftCompletion ∧
      AromaticCanonicalRule3EndpointElectronicInventorySupports
        (inventories.inventory bond.right bond.left) rightCompletion ∧
      source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
        bond.left bond.right assignment.leftReference leftCompletion ∧
      source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
        bond.right bond.left assignment.rightReference rightCompletion

theorem automaticVirtualCanonicalSpatialJudgment_electronicInventory_iff
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    source.AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalSpatialJudgment
        carrierFuel (source.electronicInventoryCompletionMap inventories)
        bond leftView rightView assignment ↔
      source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
        carrierFuel inventories bond leftView rightView assignment := by
  unfold AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalSpatialJudgment
    AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
  rw [source.canonicalOrdinaryDoubleBondVirtualEndpointAcceptance_electronicInventory_iff]
  constructor
  · rintro ⟨baseCanonical, endpointJudgment⟩
    have assignmentBond : assignment.bond = bond := baseCanonical.sound.1
    exact ⟨baseCanonical, by simpa [assignmentBond] using endpointJudgment⟩
  · rintro ⟨baseCanonical, endpointJudgment⟩
    have assignmentBond : assignment.bond = bond := baseCanonical.sound.1
    exact ⟨baseCanonical, by simpa [assignmentBond] using endpointJudgment⟩

/-- Actual per-bond analyzer specialized to the inventory-generated completion map. -/
noncomputable def aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) :
    Option source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment :=
  source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?
    carrierFuel (source.electronicInventoryCompletionMap inventories) bond leftView rightView

/-- Per-bond emission is exactly the independent inventory judgment. -/
theorem aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?_eq_some_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
        carrierFuel inventories bond leftView rightView = some assignment ↔
      source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
        carrierFuel inventories bond leftView rightView assignment := by
  unfold aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
  exact
    (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithVirtualEndpoints?_eq_some_iff_canonical
      carrierFuel (source.electronicInventoryCompletionMap inventories)
      bond leftView rightView assignment).trans
        (source.automaticVirtualCanonicalSpatialJudgment_electronicInventory_iff
          carrierFuel inventories bond leftView rightView assignment)

/-- Minimal exact readiness for the inventory-specialized analyzer. -/
def AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) : Prop :=
  ∃ assignment,
    source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
      carrierFuel inventories bond leftView rightView assignment

theorem aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?_isSome_iff_readiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) :
    (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
      carrierFuel inventories bond leftView rightView).isSome = true ↔
      source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
        carrierFuel inventories bond leftView rightView := by
  rw [Option.isSome_iff_exists]
  exact exists_congr fun assignment =>
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?_eq_some_iff_canonical
      carrierFuel inventories bond leftView rightView assignment

theorem aromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment_subsingleton
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right))
    {left right : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment}
    (leftCanonical :
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment
        carrierFuel bond leftView rightView left)
    (rightCanonical :
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment
        carrierFuel bond leftView rightView right) :
    left = right := by
  have leftComputed :=
    (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_canonical
      carrierFuel bond leftView rightView left).mpr leftCanonical
  have rightComputed :=
    (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignment?_eq_some_iff_canonical
      carrierFuel bond leftView rightView right).mpr rightCanonical
  exact Option.some.inj (leftComputed.symm.trans rightComputed)

/-- Explicit exhaustive refusal predicate.  No virtual-completion `Option` occurs in it. -/
def AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalRefusal
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) : Prop :=
  (¬ source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalReadiness
      carrierFuel bond leftView rightView) ∨
    ∃ assignment,
      source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment
          carrierFuel bond leftView rightView assignment ∧
        (AromaticCanonicalRule3EndpointElectronicInventoryRefusal
            (inventories.inventory bond.left bond.right) ∨
          AromaticCanonicalRule3EndpointElectronicInventoryRefusal
            (inventories.inventory bond.right bond.left) ∨
          ∃ leftCompletion rightCompletion,
            AromaticCanonicalRule3EndpointElectronicInventorySupports
              (inventories.inventory bond.left bond.right) leftCompletion ∧
            AromaticCanonicalRule3EndpointElectronicInventorySupports
              (inventories.inventory bond.right bond.left) rightCompletion ∧
            (¬ source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
                bond.left bond.right assignment.leftReference leftCompletion ∨
              ¬ source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
                bond.right bond.left assignment.rightReference rightCompletion))

/-- Failure of inventory readiness is exactly the explicit exhaustive refusal predicate. -/
theorem not_electronicInventoryCanonicalReadiness_iff_refusal
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) :
    (¬ source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
        carrierFuel inventories bond leftView rightView) ↔
      source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalRefusal
        carrierFuel inventories bond leftView rightView := by
  constructor
  · intro notReady
    by_cases baseReady :
        source.AromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalReadiness
          carrierFuel bond leftView rightView
    · rcases baseReady with ⟨assignment, baseCanonical⟩
      refine Or.inr ⟨assignment, baseCanonical, ?_⟩
      have leftDirected :
          source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint bond.left bond.right :=
        ⟨bond, baseCanonical.1, Or.inl ⟨rfl, rfl⟩⟩
      have rightDirected :
          source.AromaticCanonicalIndividualDoubleBondDirectedEndpoint bond.right bond.left :=
        ⟨bond, baseCanonical.1, Or.inr ⟨rfl, rfl⟩⟩
      by_cases leftRefusal :
          AromaticCanonicalRule3EndpointElectronicInventoryRefusal
            (inventories.inventory bond.left bond.right)
      · exact Or.inl leftRefusal
      by_cases rightRefusal :
          AromaticCanonicalRule3EndpointElectronicInventoryRefusal
            (inventories.inventory bond.right bond.left)
      · exact Or.inr (Or.inl rightRefusal)
      have leftClosed :
          (inventories.inventory bond.left bond.right).vacancies = 0 ∧
            (inventories.inventory bond.left bond.right).unpairedElectronPositions = 0 := by
        unfold AromaticCanonicalRule3EndpointElectronicInventoryRefusal at leftRefusal
        push_neg at leftRefusal
        exact leftRefusal
      have rightClosed :
          (inventories.inventory bond.right bond.left).vacancies = 0 ∧
            (inventories.inventory bond.right bond.left).unpairedElectronPositions = 0 := by
        unfold AromaticCanonicalRule3EndpointElectronicInventoryRefusal at rightRefusal
        push_neg at rightRefusal
        exact rightRefusal
      obtain ⟨leftCompletion, leftSupported⟩ :=
        source.exists_electronicInventorySupports_of_no_refusal bond.left bond.right
          (inventories.inventory bond.left bond.right)
          (inventories.canonical bond.left bond.right leftDirected)
          leftClosed.1 leftClosed.2
      obtain ⟨rightCompletion, rightSupported⟩ :=
        source.exists_electronicInventorySupports_of_no_refusal bond.right bond.left
          (inventories.inventory bond.right bond.left)
          (inventories.canonical bond.right bond.left rightDirected)
          rightClosed.1 rightClosed.2
      by_cases leftAccepted :
          source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
            bond.left bond.right assignment.leftReference leftCompletion
      · by_cases rightAccepted :
            source.CanonicalAromaticCanonicalRule3EndpointReferenceAcceptance
              bond.right bond.left assignment.rightReference rightCompletion
        · exact False.elim (notReady ⟨assignment, baseCanonical, leftCompletion,
            rightCompletion, leftSupported, rightSupported, leftAccepted, rightAccepted⟩)
        · exact Or.inr (Or.inr ⟨leftCompletion, rightCompletion,
            leftSupported, rightSupported, Or.inr rightAccepted⟩)
      · exact Or.inr (Or.inr ⟨leftCompletion, rightCompletion,
          leftSupported, rightSupported, Or.inl leftAccepted⟩)
    · exact Or.inl baseReady
  · intro refusal ready
    rcases ready with ⟨readyAssignment, readyBase, readyLeftCompletion,
      readyRightCompletion, readyLeftSupported, readyRightSupported,
      readyLeftAccepted, readyRightAccepted⟩
    rcases refusal with baseRefusal | ⟨refusalAssignment, refusalBase, endpointRefusal⟩
    · exact baseRefusal ⟨readyAssignment, readyBase⟩
    · have assignmentEqual :=
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticCanonicalSpatialJudgment_subsingleton
          carrierFuel bond leftView rightView refusalBase readyBase
      subst refusalAssignment
      rcases endpointRefusal with leftRefusal | rightRefusal | acceptanceRefusal
      · unfold AromaticCanonicalRule3EndpointElectronicInventoryRefusal at leftRefusal
        rcases leftRefusal with vacancy | radical
        · exact vacancy readyLeftSupported.1
        · exact radical readyLeftSupported.2.1
      · unfold AromaticCanonicalRule3EndpointElectronicInventoryRefusal at rightRefusal
        rcases rightRefusal with vacancy | radical
        · exact vacancy readyRightSupported.1
        · exact radical readyRightSupported.2.1
      · rcases acceptanceRefusal with ⟨refusalLeftCompletion, refusalRightCompletion,
          refusalLeftSupported, refusalRightSupported, leftRejected | rightRejected⟩
        · have completionEqual := electronicInventorySupports_subsingleton
            (inventories.inventory bond.left bond.right)
            refusalLeftSupported readyLeftSupported
          subst refusalLeftCompletion
          exact leftRejected readyLeftAccepted
        · have completionEqual := electronicInventorySupports_subsingleton
            (inventories.inventory bond.right bond.left)
            refusalRightSupported readyRightSupported
          subst refusalRightCompletion
          exact rightRejected readyRightAccepted

/-- Per-bond refusal has precisely the explicit electronic-inventory classification. -/
theorem aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?_eq_none_iff_refusal
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (leftView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.left))
    (rightView : source.AromaticCanonicalDependencyView
      (source.aromaticCanonicalRootOccurrence carrierFuel bond.right)) :
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
        carrierFuel inventories bond leftView rightView = none ↔
      source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalRefusal
        carrierFuel inventories bond leftView rightView := by
  rw [Option.eq_none_iff_forall_not_mem]
  simp only [Option.mem_def,
    source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?_eq_some_iff_canonical]
  rw [← not_exists]
  change (¬ source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
    carrierFuel inventories bond leftView rightView) ↔ _
  exact source.not_electronicInventoryCanonicalReadiness_iff_refusal
    carrierFuel inventories bond leftView rightView

/-- Whole-family analyzer specialized to inventory-generated endpoint completions. -/
noncomputable def analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource) :
    List source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment :=
  source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints
    carrierFuel viewAt (source.electronicInventoryCompletionMap inventories)

theorem mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_iff_canonical
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) :
    assignment ∈
        source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
          carrierFuel viewAt inventories ↔
      ∃ bond,
        source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
          carrierFuel inventories bond (viewAt bond.left) (viewAt bond.right) assignment := by
  unfold analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
  rw [source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_canonical]
  exact exists_congr fun bond =>
    source.automaticVirtualCanonicalSpatialJudgment_electronicInventory_iff
      carrierFuel inventories bond (viewAt bond.left) (viewAt bond.right) assignment

theorem analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_nodup
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource) :
    (source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
      carrierFuel viewAt inventories).Nodup := by
  unfold analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
  exact source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_nodup
    carrierFuel viewAt (source.electronicInventoryCompletionMap inventories)

theorem existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_iff_readiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    (∃! assignment,
        assignment ∈
          source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
            carrierFuel viewAt inventories ∧
        assignment.bond = bond) ↔
      source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
        carrierFuel inventories bond (viewAt bond.left) (viewAt bond.right) := by
  unfold analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
  rw [source.existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_iff_readiness]
  unfold AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalReadiness
    AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
  exact exists_congr fun assignment =>
    source.automaticVirtualCanonicalSpatialJudgment_electronicInventory_iff
      carrierFuel inventories bond (viewAt bond.left) (viewAt bond.right) assignment

theorem exists_count_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_eq_one_iff_readiness
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    (∃ assignment,
        assignment.bond = bond ∧
          (source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
            carrierFuel viewAt inventories).count assignment = 1) ↔
      source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
        carrierFuel inventories bond (viewAt bond.left) (viewAt bond.right) := by
  unfold analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
  rw [source.exists_count_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithVirtualEndpoints_eq_one_iff_readiness]
  unfold AromaticCanonicalOrdinaryDoubleBondAutomaticVirtualCanonicalReadiness
    AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
  exact exists_congr fun assignment =>
    source.automaticVirtualCanonicalSpatialJudgment_electronicInventory_iff
      carrierFuel inventories bond (viewAt bond.left) (viewAt bond.right) assignment

/-- Every canonical individual ordinary double bond has exactly one successful family outcome or
one exhaustive explicit refusal classification. -/
theorem every_aromaticCanonicalOrdinaryDoubleBond_electronicInventory_exact_success_or_refusal
    (source : AuthoritativeChemicalInput) (carrierFuel : Nat)
    (viewAt : (atom : source.AromaticCanonicalAtom) →
      source.AromaticCanonicalDependencyView
        (source.aromaticCanonicalRootOccurrence carrierFuel atom))
    (inventories : source.AromaticCanonicalRule3EndpointElectronicInventorySource) :
    ∀ bond ∈ source.aromaticCanonicalIndividualDoubleBondCarriers,
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
          carrierFuel inventories bond (viewAt bond.left) (viewAt bond.right) ∧
        ∃! assignment,
          assignment ∈
            source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
              carrierFuel viewAt inventories ∧
          assignment.bond = bond) ∨
      (source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalRefusal
          carrierFuel inventories bond (viewAt bond.left) (viewAt bond.right) ∧
        source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?
          carrierFuel inventories bond (viewAt bond.left) (viewAt bond.right) = none) := by
  intro bond _owner
  by_cases ready :
      source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
        carrierFuel inventories bond (viewAt bond.left) (viewAt bond.right)
  · exact Or.inl ⟨ready,
      (source.existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_iff_readiness
        carrierFuel viewAt inventories bond).mpr ready⟩
  · have refusal :=
      (source.not_electronicInventoryCanonicalReadiness_iff_refusal
        carrierFuel inventories bond (viewAt bond.left) (viewAt bond.right)).mp ready
    exact Or.inr ⟨refusal,
      (source.aromaticCanonicalOrdinaryDoubleBondAutomaticSpatialAssignmentWithElectronicInventory?_eq_none_iff_refusal
        carrierFuel inventories bond (viewAt bond.left) (viewAt bond.right)).mpr refusal⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
