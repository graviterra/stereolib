import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6FuelCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6RSPseudoTotality

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RawMolecule
open Rule6FourWayFamilySemantics
open Rule6ReferenceFamilySemantics
open AuthoritativeCIPRule6P92Enumeration
open DeclarativeCIP.ProductionOccurrenceRules456

namespace LocalizedTetrahedralRSPseudoDescriptor

/-- Forget only the typographic uppercase/lowercase distinction while retaining handedness. -/
def eraseCase : LocalizedTetrahedralRSPseudoDescriptor → RS
  | .chiral descriptor => descriptor
  | .pseudoasymmetric .r => .R
  | .pseudoasymmetric .s => .S

@[simp] theorem eraseCase_classifyTetrahedralRSPseudo
    (descriptor : RS) (pseudoComparisons : Nat) :
    (classifyTetrahedralRSPseudo descriptor pseudoComparisons).eraseCase = descriptor := by
  by_cases exactlyOne : pseudoComparisons = 1
  · subst pseudoComparisons
    cases descriptor <;> rfl
  · simp [classifyTetrahedralRSPseudo, exactlyOne, eraseCase]

end LocalizedTetrahedralRSPseudoDescriptor

namespace AuthoritativeChemicalInput

@[simp] theorem eraseCase_classifiedRule6RankingDescriptor
    (parity : TetrahedralInputParity) (ranking : Rule6TrackedRanking) :
    (classifiedRule6RankingDescriptor parity ranking).eraseCase =
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven ranking.positions) := by
  simp [classifiedRule6RankingDescriptor]

@[simp] theorem eraseCase_classifiedFourWayRule6Descriptor
    (parity : TetrahedralInputParity) (second : Rule6TrackedRanking) :
    (classifiedFourWayRule6Descriptor parity second).eraseCase =
      if second.unique then
        RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven second.positions)
      else
        RS.swap (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven second.positions)) := by
  simp [classifiedFourWayRule6Descriptor]

/-- The rich dependent four-way judgment is exactly the old judgment plus the retained
uppercase/lowercase classification. -/
theorem authoritativeFourWayDescriptorJudgment_iff_exists_rspseudo_erasing_to
    (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (sorted : List Nat) (descriptor : RS) :
    AuthoritativeFourWayDescriptorJudgment backend parity sorted descriptor ↔
      ∃ richDescriptor,
        AuthoritativeFourWayRSPseudoJudgment backend parity sorted richDescriptor ∧
          richDescriptor.eraseCase = descriptor := by
  constructor
  · rintro ⟨firstReference, first, second, firstReferenceEq, firstEq, secondEq,
      coherent, descriptorEq⟩
    refine ⟨classifiedFourWayRule6Descriptor parity second,
      ⟨firstReference, first, second, firstReferenceEq, firstEq, secondEq,
        coherent, rfl⟩, ?_⟩
    simpa using descriptorEq
  · rintro ⟨richDescriptor,
      ⟨firstReference, first, second, firstReferenceEq, firstEq, secondEq,
        coherent, richDescriptorEq⟩,
      erasedEq⟩
    refine ⟨firstReference, first, second, firstReferenceEq, firstEq, secondEq,
      coherent, ?_⟩
    rw [← erasedEq, richDescriptorEq]
    exact (eraseCase_classifiedFourWayRule6Descriptor parity second).symm

/-- The rich two-group reference-family judgment is a conservative extension of the common
`R/S` family judgment. -/
theorem commonRule6Descriptor_iff_exists_rspseudo_erasing_to
    (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat) (descriptor : RS) :
    CommonRule6Descriptor backend parity references descriptor ↔
      ∃ richDescriptor,
        Rule6FamilyRSPseudoJudgment backend parity references richDescriptor ∧
          richDescriptor.eraseCase = descriptor := by
  constructor
  · intro common
    have emitted : rule6FamilyDescriptorWithBackend? backend parity references =
        some descriptor :=
      (rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor
        backend parity references descriptor).mpr common
    cases rankingEq : rankProductionRule6EquivalentReferencesWithBackend?
        backend parity references with
    | none => simp [rule6FamilyDescriptorWithBackend?, rankingEq] at emitted
    | some ranking =>
        have certificate :=
          (rankProductionRule6EquivalentReferencesWithBackend?_iff_certificate
            backend parity references ranking).mp rankingEq
        refine ⟨classifiedRule6RankingDescriptor parity ranking,
          ⟨ranking, certificate, rfl⟩, ?_⟩
        have descriptorEq :
            RawMolecule.descriptorOfParity parity
                (RawMolecule.permutationIsEven ranking.positions) = descriptor := by
          simpa [rule6FamilyDescriptorWithBackend?, rankingEq] using emitted
        simpa using descriptorEq
  · rintro ⟨richDescriptor, ⟨ranking, certificate, richDescriptorEq⟩, erasedEq⟩
    rcases certificate with ⟨certificate⟩
    have referencesNonempty : references ≠ [] := by
      intro referencesEq
      simpa [referencesEq] using certificate.reference_head
    have baseEq :
        RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven ranking.positions) = descriptor := by
      calc
        RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven ranking.positions) =
            richDescriptor.eraseCase := by
              rw [richDescriptorEq]
              exact (eraseCase_classifiedRule6RankingDescriptor parity ranking).symm
        _ = descriptor := erasedEq
    refine ⟨referencesNonempty, ?_⟩
    intro reference member
    simpa [baseEq] using certificate.all_references reference member

/-- The three-group quotient reversal is preserved exactly by case erasure. -/
theorem commonSwappedRule6Descriptor_iff_exists_threeGroupRSPseudo_erasing_to
    (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat) (descriptor : RS) :
    CommonRule6Descriptor backend parity references (RS.swap descriptor) ↔
      ∃ richDescriptor,
        Rule6ThreeGroupRSPseudoJudgment backend parity references richDescriptor ∧
          richDescriptor.eraseCase = descriptor := by
  constructor
  · intro common
    have emitted : rule6FamilyDescriptorWithBackend? backend parity references =
        some (RS.swap descriptor) :=
      (rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor
        backend parity references (RS.swap descriptor)).mpr common
    cases rankingEq : rankProductionRule6EquivalentReferencesWithBackend?
        backend parity references with
    | none => simp [rule6FamilyDescriptorWithBackend?, rankingEq] at emitted
    | some ranking =>
        have certificate :=
          (rankProductionRule6EquivalentReferencesWithBackend?_iff_certificate
            backend parity references ranking).mp rankingEq
        refine ⟨.chiral (RS.swap (RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven ranking.positions))),
          ⟨ranking, certificate, rfl⟩, ?_⟩
        have baseEq :
            RawMolecule.descriptorOfParity parity
                (RawMolecule.permutationIsEven ranking.positions) = RS.swap descriptor := by
          simpa [rule6FamilyDescriptorWithBackend?, rankingEq] using emitted
        simp [LocalizedTetrahedralRSPseudoDescriptor.eraseCase, baseEq,
          rs_swap_involutive]
  · rintro ⟨richDescriptor, ⟨ranking, certificate, richDescriptorEq⟩, erasedEq⟩
    rcases certificate with ⟨certificate⟩
    have referencesNonempty : references ≠ [] := by
      intro referencesEq
      simpa [referencesEq] using certificate.reference_head
    have swappedBaseEq :
        RS.swap (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven ranking.positions)) = descriptor := by
      calc
        RS.swap (RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven ranking.positions)) =
            richDescriptor.eraseCase := by
              rw [richDescriptorEq]
              rfl
        _ = descriptor := erasedEq
    have baseEq :
        RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven ranking.positions) = RS.swap descriptor := by
      calc
        RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven ranking.positions) =
            RS.swap (RS.swap (RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven ranking.positions))) :=
                (rs_swap_involutive _).symm
        _ = RS.swap descriptor := congrArg RS.swap swappedBaseEq
    refine ⟨referencesNonempty, ?_⟩
    intro reference member
    simpa [baseEq] using certificate.all_references reference member

/-- Exact P-92 branch conservation: adding uppercase/lowercase information changes no success
case and erases to exactly the old handedness result. -/
theorem aromaticCanonicalRule3Through6BranchDescriptorJudgment_iff_exists_rspseudo_erasing_to
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (parity : TetrahedralInputParity) (descriptor : RS) :
    source.AromaticCanonicalRule3Through6BranchDescriptorJudgment
        target view fuel roots partition parity descriptor ↔
      ∃ richDescriptor,
        source.AromaticCanonicalRule3Through6RSPseudoBranchJudgment
          target view fuel roots partition parity richDescriptor ∧
        richDescriptor.eraseCase = descriptor := by
  let backend := source.aromaticCanonicalRule3Through6RankingBackendForFrame
    partition.frame.rule3Frame target view fuel roots
  let sorted := partition.sortedPositions
  let adjacent := partition.adjacentOptions
  let groupCount := rule6GroupCount adjacent
  unfold AromaticCanonicalRule3Through6BranchDescriptorJudgment
    AromaticCanonicalRule3Through6RSPseudoBranchJudgment
  dsimp only
  change
    ((groupCount = 1 ∧
        AuthoritativeFourWayDescriptorJudgment backend parity sorted descriptor) ∨
      (groupCount = 2 ∧
        CommonRule6Descriptor backend parity
          (rule6EquivalentReferencePositions sorted adjacent) descriptor) ∨
      (groupCount = 3 ∧
        CommonRule6Descriptor backend parity
          (rule6ThreeGroupReferencePositions sorted) (RS.swap descriptor))) ↔
    ∃ richDescriptor,
      ((groupCount = 1 ∧
          AuthoritativeFourWayRSPseudoJudgment backend parity sorted richDescriptor) ∨
        (groupCount = 2 ∧
          Rule6FamilyRSPseudoJudgment backend parity
            (rule6EquivalentReferencePositions sorted adjacent) richDescriptor) ∨
        (groupCount = 3 ∧
          Rule6ThreeGroupRSPseudoJudgment backend parity
            (rule6ThreeGroupReferencePositions sorted) richDescriptor)) ∧
      richDescriptor.eraseCase = descriptor
  constructor
  · rintro (one | two | three)
    · obtain ⟨richDescriptor, richJudgment, erasedEq⟩ :=
        (authoritativeFourWayDescriptorJudgment_iff_exists_rspseudo_erasing_to
          backend parity sorted descriptor).mp one.2
      exact ⟨richDescriptor, Or.inl ⟨one.1, richJudgment⟩, erasedEq⟩
    · obtain ⟨richDescriptor, richJudgment, erasedEq⟩ :=
        (commonRule6Descriptor_iff_exists_rspseudo_erasing_to backend parity
          (rule6EquivalentReferencePositions sorted adjacent) descriptor).mp two.2
      exact ⟨richDescriptor, Or.inr (Or.inl ⟨two.1, richJudgment⟩), erasedEq⟩
    · obtain ⟨richDescriptor, richJudgment, erasedEq⟩ :=
        (commonSwappedRule6Descriptor_iff_exists_threeGroupRSPseudo_erasing_to
          backend parity (rule6ThreeGroupReferencePositions sorted) descriptor).mp three.2
      exact ⟨richDescriptor, Or.inr (Or.inr ⟨three.1, richJudgment⟩), erasedEq⟩
  · rintro ⟨richDescriptor, one | two | three, erasedEq⟩
    · exact Or.inl ⟨one.1,
        (authoritativeFourWayDescriptorJudgment_iff_exists_rspseudo_erasing_to
          backend parity sorted descriptor).mpr
            ⟨richDescriptor, one.2, erasedEq⟩⟩
    · exact Or.inr (Or.inl ⟨two.1,
        (commonRule6Descriptor_iff_exists_rspseudo_erasing_to backend parity
          (rule6EquivalentReferencePositions sorted adjacent) descriptor).mpr
            ⟨richDescriptor, two.2, erasedEq⟩⟩)
    · exact Or.inr (Or.inr ⟨three.1,
        (commonSwappedRule6Descriptor_iff_exists_threeGroupRSPseudo_erasing_to
          backend parity (rule6ThreeGroupReferencePositions sorted) descriptor).mpr
            ⟨richDescriptor, three.2, erasedEq⟩⟩)

/-- The one-shot rich executable judgment has exactly the old success domain and conservatively
extends its result. -/
theorem aromaticCanonicalRule3Through6ExecutableDescriptorJudgment_iff_exists_rspseudo_erasing_to
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) (descriptor : RS) :
    source.AromaticCanonicalRule3Through6ExecutableDescriptorJudgment
        center target view fuel roots parity descriptor ↔
      ∃ richDescriptor,
        source.AromaticCanonicalRule3Through6RSPseudoExecutableJudgment
          center target view fuel roots parity richDescriptor ∧
        richDescriptor.eraseCase = descriptor := by
  constructor
  · rintro ⟨rootsLength, partition, partitionComputed, applicable, branchJudgment⟩
    obtain ⟨richDescriptor, richBranchJudgment, erasedEq⟩ :=
      (source.aromaticCanonicalRule3Through6BranchDescriptorJudgment_iff_exists_rspseudo_erasing_to
        target view fuel roots partition parity descriptor).mp branchJudgment
    exact ⟨richDescriptor,
      ⟨rootsLength, partition, partitionComputed, applicable, richBranchJudgment⟩,
      erasedEq⟩
  · rintro ⟨richDescriptor,
      ⟨rootsLength, partition, partitionComputed, applicable, richBranchJudgment⟩,
      erasedEq⟩
    exact ⟨rootsLength, partition, partitionComputed, applicable,
      (source.aromaticCanonicalRule3Through6BranchDescriptorJudgment_iff_exists_rspseudo_erasing_to
        target view fuel roots partition parity descriptor).mpr
          ⟨richDescriptor, richBranchJudgment, erasedEq⟩⟩

/-- Whole-molecule execution also preserves exactly the old success domain and handedness. -/
theorem aromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment_iff_exists_rspseudo_erasing_to
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : RS) :
    source.AromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment
        semantics ruleFuel center descriptor ↔
      ∃ richDescriptor,
        source.AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
          semantics ruleFuel center richDescriptor ∧
        richDescriptor.eraseCase = descriptor := by
  unfold AromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment
    AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
  dsimp only
  constructor
  · rintro ⟨roots, parity, rootsComputed, parityComputed, executable⟩
    obtain ⟨richDescriptor, richExecutable, erasedEq⟩ :=
      (source.aromaticCanonicalRule3Through6ExecutableDescriptorJudgment_iff_exists_rspseudo_erasing_to
        center.1 _ _ ruleFuel roots parity descriptor).mp executable
    exact ⟨richDescriptor,
      ⟨roots, parity, rootsComputed, parityComputed, richExecutable⟩, erasedEq⟩
  · rintro ⟨richDescriptor,
      ⟨roots, parity, rootsComputed, parityComputed, richExecutable⟩,
      erasedEq⟩
    exact ⟨roots, parity, rootsComputed, parityComputed,
      (source.aromaticCanonicalRule3Through6ExecutableDescriptorJudgment_iff_exists_rspseudo_erasing_to
        center.1 _ _ ruleFuel roots parity descriptor).mpr
          ⟨richDescriptor, richExecutable, erasedEq⟩⟩

/-- Direct executable-output conservation theorem. -/
theorem aromaticCanonicalScheduledRule3Through6Descriptor?_eq_some_iff_exists_rspseudo_erasing_to
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : RS) :
    source.aromaticCanonicalScheduledRule3Through6Descriptor?
        semantics ruleFuel center = some descriptor ↔
      ∃ richDescriptor,
        source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
            semantics ruleFuel center = some richDescriptor ∧
          richDescriptor.eraseCase = descriptor := by
  rw [source.aromaticCanonicalScheduledRule3Through6Descriptor?_eq_some_iff_executableJudgment]
  constructor
  · intro executable
    obtain ⟨richDescriptor, richExecutable, erasedEq⟩ :=
      (source.aromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment_iff_exists_rspseudo_erasing_to
        semantics ruleFuel center descriptor).mp executable
    exact ⟨richDescriptor,
      (source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_some_iff
        semantics ruleFuel center richDescriptor).mpr richExecutable,
      erasedEq⟩
  · rintro ⟨richDescriptor, richComputed, erasedEq⟩
    apply (source.aromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment_iff_exists_rspseudo_erasing_to
      semantics ruleFuel center descriptor).mpr
    exact ⟨richDescriptor,
      (source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_some_iff
        semantics ruleFuel center richDescriptor).mp richComputed,
      erasedEq⟩

/-- Retaining descriptor case introduces no new readiness premise. -/
theorem aromaticCanonicalScheduledRule3Through6Ready_iff_rspseudoReady
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    source.AromaticCanonicalScheduledRule3Through6Ready semantics ruleFuel center ↔
      source.AromaticCanonicalScheduledRule3Through6RSPseudoReady
        semantics ruleFuel center := by
  unfold AromaticCanonicalScheduledRule3Through6Ready
    AromaticCanonicalScheduledRule3Through6RSPseudoReady
  constructor
  · rintro ⟨descriptor, executable⟩
    obtain ⟨richDescriptor, richExecutable, _⟩ :=
      (source.aromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment_iff_exists_rspseudo_erasing_to
        semantics ruleFuel center descriptor).mp executable
    exact ⟨richDescriptor, richExecutable⟩
  · rintro ⟨richDescriptor, richExecutable⟩
    let descriptor := richDescriptor.eraseCase
    exact ⟨descriptor,
      (source.aromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment_iff_exists_rspseudo_erasing_to
        semantics ruleFuel center descriptor).mpr
          ⟨richDescriptor, richExecutable, rfl⟩⟩

/-- The previously established chemical evidence is sufficient for the full `R/S/r/s` endpoint;
no new chemical premise is required merely to retain case. -/
theorem aromaticCanonicalScheduledRule3Through6RSPseudoReady_of_chemicallyReadyAtBound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalScheduledRule3Through6ChemicallyReadyAtBound
      semantics center) :
    source.AromaticCanonicalScheduledRule3Through6RSPseudoReady
      semantics (2 * (carrierFuel + 1)) center := by
  obtain ⟨descriptor, computed⟩ :=
    source.exists_aromaticCanonicalScheduledRule3Through6Descriptor?_at_bound
      semantics center ready
  have oldReady : source.AromaticCanonicalScheduledRule3Through6Ready
      semantics (2 * (carrierFuel + 1)) center :=
    (source.aromaticCanonicalScheduledRule3Through6Ready_iff_exists_descriptor
      semantics (2 * (carrierFuel + 1)) center).mpr ⟨descriptor, computed⟩
  exact (source.aromaticCanonicalScheduledRule3Through6Ready_iff_rspseudoReady
    semantics (2 * (carrierFuel + 1)) center).mp oldReady

/-- Chemical readiness yields a computed rich descriptor together with its exact independent
executable judgment. -/
theorem exists_aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor_and_judgment_at_bound
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalScheduledRule3Through6ChemicallyReadyAtBound
      semantics center) :
    ∃ descriptor,
      source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
          semantics (2 * (carrierFuel + 1)) center = some descriptor ∧
        source.AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
          semantics (2 * (carrierFuel + 1)) center descriptor := by
  have richReady :=
    source.aromaticCanonicalScheduledRule3Through6RSPseudoReady_of_chemicallyReadyAtBound
      semantics center ready
  rcases richReady with ⟨descriptor, judged⟩
  exact ⟨descriptor,
    (source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_some_iff
      semantics (2 * (carrierFuel + 1)) center descriptor).mpr judged,
    judged⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
