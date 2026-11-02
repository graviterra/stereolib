import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6Totality

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open RawMolecule
open Rule6FourWayFamilySemantics
open Rule6ReferenceFamilySemantics
open AuthoritativeCIPRule6P92Enumeration
open DeclarativeCIP.ProductionOccurrenceRules456

/-!
# Exact uppercase/lowercase preservation for the source Rules 1a--6 endpoint

The molecule-level Rules 1a--6 endpoint previously projected its answer to bare `RS`.  That is
enough for handedness, but it erases the P-92 fact that exactly one enantiomorphic comparison
makes a tetrahedral descriptor lowercase.  This module carries the selected production
ranking's `pseudoComparisons` count through the same one-, two-, and three-group dispatch and
proves an exact declarative boundary for the richer `R/S/r/s` result.
-/

/-- The local descriptor contributed by one strict promoted ranking. -/
def classifiedRule6RankingDescriptor
    (parity : TetrahedralInputParity) (ranking : Rule6TrackedRanking) :
    LocalizedTetrahedralRSPseudoDescriptor :=
  classifyTetrahedralRSPseudo
    (RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven ranking.positions))
    ranking.pseudoComparisons

/-- Four-way classification uses the quotient-aware second-ranking descriptor, exactly as the
P-92 dependent-reference carrier does. -/
def classifiedFourWayRule6Descriptor
    (parity : TetrahedralInputParity) (second : Rule6TrackedRanking) :
    LocalizedTetrahedralRSPseudoDescriptor :=
  classifyTetrahedralRSPseudo
    (if second.unique then
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven second.positions)
    else
      RS.swap (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven second.positions)))
    second.pseudoComparisons

/-- Pure four-way evaluator retaining uppercase/lowercase classification. -/
def evaluateFourWayRSPseudo?
    (parity : TetrahedralInputParity) (first second : Rule6TrackedRanking) :
    Option LocalizedTetrahedralRSPseudoDescriptor := do
  let _agreement ← evaluateFourWayCarrier? parity first second
  some (classifiedFourWayRule6Descriptor parity second)

/-- The richer four-way evaluator has exactly the same three coherence obligations as the
existing P-92 carrier and no additional failure branch. -/
theorem evaluateFourWayRSPseudo?_eq_some_iff
    (parity : TetrahedralInputParity) (first second : Rule6TrackedRanking)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    evaluateFourWayRSPseudo? parity first second = some descriptor ↔
      FourWayCarrierCoherent parity first second ∧
        descriptor = classifiedFourWayRule6Descriptor parity second := by
  unfold evaluateFourWayRSPseudo? evaluateFourWayCarrier? FourWayCarrierCoherent
  by_cases different : first.positions ≠ second.positions
  · by_cases sameDescriptor :
        RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven first.positions) =
          RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven second.positions)
    · by_cases sameUnique : first.unique = second.unique
      · simp [different, sameDescriptor, sameUnique]
        exact eq_comm
      · simp [different, sameDescriptor, sameUnique]
    · simp [different, sameDescriptor]
  · simp [different]

/-- Dependent four-way execution with its selected second-ranking case retained. -/
def authoritativeOccurrenceRule6FourWayRSPseudo?
    (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (sorted : List Nat) :
    Option LocalizedTetrahedralRSPseudoDescriptor := do
  let firstReference ← sorted[0]?
  let first ← backend firstReference
  let second ← backend (first.positions[1]?.getD 0)
  evaluateFourWayRSPseudo? parity first second

/-- Independent meaning of the richer dependent four-way result. -/
def AuthoritativeFourWayRSPseudoJudgment
    (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (sorted : List Nat)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) : Prop :=
  ∃ firstReference first second,
    sorted[0]? = some firstReference ∧
      backend firstReference = some first ∧
      backend (first.positions[1]?.getD 0) = some second ∧
      FourWayCarrierCoherent parity first second ∧
      descriptor = classifiedFourWayRule6Descriptor parity second

theorem authoritativeOccurrenceRule6FourWayRSPseudo?_eq_some_iff
    (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (sorted : List Nat)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    authoritativeOccurrenceRule6FourWayRSPseudo? backend parity sorted = some descriptor ↔
      AuthoritativeFourWayRSPseudoJudgment backend parity sorted descriptor := by
  unfold AuthoritativeFourWayRSPseudoJudgment
  constructor
  · intro computed
    unfold authoritativeOccurrenceRule6FourWayRSPseudo? at computed
    cases firstReferenceEq : sorted[0]? with
    | none => simp [firstReferenceEq] at computed
    | some firstReference =>
        cases firstEq : backend firstReference with
        | none => simp [firstReferenceEq, firstEq] at computed
        | some first =>
            cases secondEq : backend (first.positions[1]?.getD 0) with
            | none => simp [firstReferenceEq, firstEq, secondEq] at computed
            | some second =>
                have evaluated :
                    evaluateFourWayRSPseudo? parity first second = some descriptor := by
                  simpa [firstReferenceEq, firstEq, secondEq] using computed
                exact ⟨firstReference, first, second, rfl, firstEq, secondEq,
                  (evaluateFourWayRSPseudo?_eq_some_iff parity first second descriptor).mp
                    evaluated⟩
  · rintro ⟨firstReference, first, second, firstReferenceEq, firstEq, secondEq,
      coherent, descriptorEq⟩
    have evaluated :
        evaluateFourWayRSPseudo? parity first second = some descriptor :=
      (evaluateFourWayRSPseudo?_eq_some_iff parity first second descriptor).mpr
        ⟨coherent, descriptorEq⟩
    unfold authoritativeOccurrenceRule6FourWayRSPseudo?
    simpa [firstReferenceEq, firstEq, secondEq] using evaluated

/-- Equivalent-reference execution retaining the pseudo-comparison count of the prescribed
head reference. -/
def rule6FamilyRSPseudo?
    (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat) :
    Option LocalizedTetrahedralRSPseudoDescriptor := do
  let ranking ← rankProductionRule6EquivalentReferencesWithBackend?
    backend parity references
  some (classifiedRule6RankingDescriptor parity ranking)

/-- Exact certificate boundary for the richer equivalent-reference result. -/
def Rule6FamilyRSPseudoJudgment
    (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) : Prop :=
  ∃ ranking,
    Nonempty (ProductionRule6BackendEquivalentReferencesCertificate
      backend parity references ranking) ∧
    descriptor = classifiedRule6RankingDescriptor parity ranking

theorem rule6FamilyRSPseudo?_eq_some_iff
    (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    rule6FamilyRSPseudo? backend parity references = some descriptor ↔
      Rule6FamilyRSPseudoJudgment backend parity references descriptor := by
  unfold rule6FamilyRSPseudo? Rule6FamilyRSPseudoJudgment
  cases rankingEq : rankProductionRule6EquivalentReferencesWithBackend?
      backend parity references with
  | none =>
      constructor
      · simp
      · rintro ⟨ranking, certificate, _⟩
        have computed :=
          (rankProductionRule6EquivalentReferencesWithBackend?_iff_certificate
            backend parity references ranking).mpr certificate
        rw [rankingEq] at computed
        contradiction
  | some ranking =>
      constructor
      · intro computed
        have descriptorEq : descriptor = classifiedRule6RankingDescriptor parity ranking := by
          simpa [rankingEq] using computed.symm
        exact ⟨ranking,
          (rankProductionRule6EquivalentReferencesWithBackend?_iff_certificate
            backend parity references ranking).mp rankingEq,
          descriptorEq⟩
      · rintro ⟨otherRanking, certificate, descriptorEq⟩
        have otherComputed :=
          (rankProductionRule6EquivalentReferencesWithBackend?_iff_certificate
            backend parity references otherRanking).mpr certificate
        have rankingIdentity : otherRanking = ranking :=
          Option.some.inj (otherComputed.symm.trans rankingEq)
        subst otherRanking
        simpa [rankingEq] using descriptorEq.symm

/-- The three-group branch is always uppercase, while retaining the quotient reversal. -/
def rule6ThreeGroupRSPseudo?
    (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat) :
    Option LocalizedTetrahedralRSPseudoDescriptor := do
  let ranking ← rankProductionRule6EquivalentReferencesWithBackend?
    backend parity references
  some (.chiral (RS.swap (RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven ranking.positions))))

def Rule6ThreeGroupRSPseudoJudgment
    (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) : Prop :=
  ∃ ranking,
    Nonempty (ProductionRule6BackendEquivalentReferencesCertificate
      backend parity references ranking) ∧
    descriptor = .chiral (RS.swap (RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven ranking.positions)))

theorem rule6ThreeGroupRSPseudo?_eq_some_iff
    (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (references : List Nat)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    rule6ThreeGroupRSPseudo? backend parity references = some descriptor ↔
      Rule6ThreeGroupRSPseudoJudgment backend parity references descriptor := by
  unfold rule6ThreeGroupRSPseudo? Rule6ThreeGroupRSPseudoJudgment
  cases rankingEq : rankProductionRule6EquivalentReferencesWithBackend?
      backend parity references with
  | none =>
      constructor
      · simp
      · rintro ⟨ranking, certificate, _⟩
        have computed :=
          (rankProductionRule6EquivalentReferencesWithBackend?_iff_certificate
            backend parity references ranking).mpr certificate
        rw [rankingEq] at computed
        contradiction
  | some ranking =>
      constructor
      · intro computed
        have descriptorEq : descriptor = .chiral (RS.swap
            (RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven ranking.positions))) := by
          simpa [rankingEq] using computed.symm
        exact ⟨ranking,
          (rankProductionRule6EquivalentReferencesWithBackend?_iff_certificate
            backend parity references ranking).mp rankingEq,
          descriptorEq⟩
      · rintro ⟨otherRanking, certificate, descriptorEq⟩
        have otherComputed :=
          (rankProductionRule6EquivalentReferencesWithBackend?_iff_certificate
            backend parity references otherRanking).mpr certificate
        have rankingIdentity : otherRanking = ranking :=
          Option.some.inj (otherComputed.symm.trans rankingEq)
        subst otherRanking
        simpa [rankingEq] using descriptorEq.symm

/-! ## Exact source dispatch and molecule endpoint -/

/-- The same P-92 1/2/3-group dispatch as the established `RS` endpoint, now retaining the
uppercase/lowercase case selected by the authoritative promoted ranking. -/
noncomputable def aromaticCanonicalRule3Through6RSPseudoForPartition?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (parity : TetrahedralInputParity) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  let backend := source.aromaticCanonicalRule3Through6RankingBackendForFrame
    partition.frame.rule3Frame target view fuel roots
  let sorted := partition.sortedPositions
  let adjacent := partition.adjacentOptions
  let groupCount := rule6GroupCount adjacent
  if groupCount = 1 then
    authoritativeOccurrenceRule6FourWayRSPseudo? backend parity sorted
  else if groupCount = 2 then
    rule6FamilyRSPseudo? backend parity
      (rule6EquivalentReferencePositions sorted adjacent)
  else if groupCount = 3 then
    rule6ThreeGroupRSPseudo? backend parity
      (rule6ThreeGroupReferencePositions sorted)
  else none

/-- Independent case-by-case meaning of the richer P-92 dispatch. -/
def AromaticCanonicalRule3Through6RSPseudoBranchJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (parity : TetrahedralInputParity)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) : Prop :=
  let backend := source.aromaticCanonicalRule3Through6RankingBackendForFrame
    partition.frame.rule3Frame target view fuel roots
  let sorted := partition.sortedPositions
  let adjacent := partition.adjacentOptions
  let groupCount := rule6GroupCount adjacent
  (groupCount = 1 ∧
      AuthoritativeFourWayRSPseudoJudgment backend parity sorted descriptor) ∨
    (groupCount = 2 ∧
      Rule6FamilyRSPseudoJudgment backend parity
        (rule6EquivalentReferencePositions sorted adjacent) descriptor) ∨
    (groupCount = 3 ∧
      Rule6ThreeGroupRSPseudoJudgment backend parity
        (rule6ThreeGroupReferencePositions sorted) descriptor)

theorem aromaticCanonicalRule3Through6RSPseudoForPartition?_eq_some_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (parity : TetrahedralInputParity)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    source.aromaticCanonicalRule3Through6RSPseudoForPartition?
        target view fuel roots partition parity = some descriptor ↔
      source.AromaticCanonicalRule3Through6RSPseudoBranchJudgment
        target view fuel roots partition parity descriptor := by
  let backend := source.aromaticCanonicalRule3Through6RankingBackendForFrame
    partition.frame.rule3Frame target view fuel roots
  let sorted := partition.sortedPositions
  let adjacent := partition.adjacentOptions
  let groupCount := rule6GroupCount adjacent
  unfold aromaticCanonicalRule3Through6RSPseudoForPartition?
    AromaticCanonicalRule3Through6RSPseudoBranchJudgment
  dsimp only
  change
    (if groupCount = 1 then
        authoritativeOccurrenceRule6FourWayRSPseudo? backend parity sorted
      else if groupCount = 2 then
        rule6FamilyRSPseudo? backend parity
          (rule6EquivalentReferencePositions sorted adjacent)
      else if groupCount = 3 then
        rule6ThreeGroupRSPseudo? backend parity
          (rule6ThreeGroupReferencePositions sorted)
      else none) = some descriptor ↔
      (groupCount = 1 ∧
          AuthoritativeFourWayRSPseudoJudgment backend parity sorted descriptor) ∨
        (groupCount = 2 ∧
          Rule6FamilyRSPseudoJudgment backend parity
            (rule6EquivalentReferencePositions sorted adjacent) descriptor) ∨
        (groupCount = 3 ∧
          Rule6ThreeGroupRSPseudoJudgment backend parity
            (rule6ThreeGroupReferencePositions sorted) descriptor)
  by_cases groupOne : groupCount = 1
  · rw [if_pos groupOne,
      authoritativeOccurrenceRule6FourWayRSPseudo?_eq_some_iff]
    simp [groupOne]
  · rw [if_neg groupOne]
    by_cases groupTwo : groupCount = 2
    · rw [if_pos groupTwo, rule6FamilyRSPseudo?_eq_some_iff]
      simp [groupTwo]
    · rw [if_neg groupTwo]
      by_cases groupThree : groupCount = 3
      · rw [if_pos groupThree, rule6ThreeGroupRSPseudo?_eq_some_iff]
        simp [groupThree]
      · rw [if_neg groupThree]
        simp [groupOne, groupTwo, groupThree]

/-- Topology-checked rich result for one already constructed initial partition. -/
noncomputable def aromaticCanonicalRule3Through6RSPseudoForPartitionChecked?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (parity : TetrahedralInputParity) :
    Option LocalizedTetrahedralRSPseudoDescriptor :=
  if _noOdd : source.aromaticCanonicalRule6HasOddConstitutionAutomorphism?
      center roots rootsLength partition = false then
    source.aromaticCanonicalRule3Through6RSPseudoForPartition?
      target view fuel roots partition parity
  else none

theorem aromaticCanonicalRule3Through6RSPseudoForPartitionChecked?_eq_some_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (rootsLength : roots.length = 4)
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (parity : TetrahedralInputParity)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    source.aromaticCanonicalRule3Through6RSPseudoForPartitionChecked?
        center target view fuel roots rootsLength partition parity = some descriptor ↔
      source.AromaticCanonicalRule6TopologyAdmissible
          center roots rootsLength partition ∧
        source.AromaticCanonicalRule3Through6RSPseudoBranchJudgment
          target view fuel roots partition parity descriptor := by
  unfold aromaticCanonicalRule3Through6RSPseudoForPartitionChecked?
  by_cases noOdd : source.aromaticCanonicalRule6HasOddConstitutionAutomorphism?
      center roots rootsLength partition = false
  · rw [dif_pos noOdd,
      source.aromaticCanonicalRule3Through6RSPseudoForPartition?_eq_some_iff]
    exact (and_iff_right
      ((source.aromaticCanonicalRule6HasOddConstitutionAutomorphism?_eq_false_iff_admissible
        center roots rootsLength partition).mp noOdd)).symm
  · have notApplicable : ¬ source.AromaticCanonicalRule6TopologyAdmissible
        center roots rootsLength partition := by
      intro applicable
      exact noOdd
        ((source.aromaticCanonicalRule6HasOddConstitutionAutomorphism?_eq_false_iff_admissible
          center roots rootsLength partition).mpr applicable)
    simp [dif_neg noOdd, notApplicable]

/-- One-shot source endpoint retaining the final uppercase/lowercase classification. -/
noncomputable def aromaticCanonicalRule3Through6RSPseudoDescriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity) :
    Option LocalizedTetrahedralRSPseudoDescriptor := do
  if rootsLength : roots.length = 4 then
    let partition ← source.buildAromaticCanonicalRule3Through5InitialPartition?
      target view fuel roots
    source.aromaticCanonicalRule3Through6RSPseudoForPartitionChecked?
      center target view fuel roots rootsLength partition parity
  else none

/-- Exact non-wrapper meaning of one rich Rules 1a--6 result. -/
def AromaticCanonicalRule3Through6RSPseudoExecutableJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) : Prop :=
  ∃ (rootsLength : roots.length = 4)
      (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel),
    source.buildAromaticCanonicalRule3Through5InitialPartition?
        target view fuel roots = some partition ∧
      source.AromaticCanonicalRule6TopologyAdmissible
        center roots rootsLength partition ∧
      source.AromaticCanonicalRule3Through6RSPseudoBranchJudgment
        target view fuel roots partition parity descriptor

theorem aromaticCanonicalRule3Through6RSPseudoDescriptor?_eq_some_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (center : source.AromaticCanonicalAtom)
    (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target)
    (fuel : Nat)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (parity : TetrahedralInputParity)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    source.aromaticCanonicalRule3Through6RSPseudoDescriptor?
        center target view fuel roots parity = some descriptor ↔
      source.AromaticCanonicalRule3Through6RSPseudoExecutableJudgment
        center target view fuel roots parity descriptor := by
  unfold aromaticCanonicalRule3Through6RSPseudoDescriptor?
    AromaticCanonicalRule3Through6RSPseudoExecutableJudgment
  constructor
  · intro computed
    by_cases rootsLength : roots.length = 4
    · cases partitionComputed :
          source.buildAromaticCanonicalRule3Through5InitialPartition?
            target view fuel roots with
      | none => simp [rootsLength, partitionComputed] at computed
      | some partition =>
          have checked :
              source.aromaticCanonicalRule3Through6RSPseudoForPartitionChecked?
                  center target view fuel roots rootsLength partition parity =
                some descriptor := by
            simpa [rootsLength, partitionComputed] using computed
          exact ⟨rootsLength, partition, rfl,
            (source.aromaticCanonicalRule3Through6RSPseudoForPartitionChecked?_eq_some_iff
              center target view fuel roots rootsLength partition parity descriptor).mp checked⟩
    · simp [rootsLength] at computed
  · rintro ⟨rootsLength, partition, partitionComputed, applicable, judged⟩
    have checked :
        source.aromaticCanonicalRule3Through6RSPseudoForPartitionChecked?
            center target view fuel roots rootsLength partition parity = some descriptor :=
      (source.aromaticCanonicalRule3Through6RSPseudoForPartitionChecked?_eq_some_iff
        center target view fuel roots rootsLength partition parity descriptor).mpr
          ⟨applicable, judged⟩
    simpa [rootsLength, partitionComputed] using checked

/-- Fully molecule-attached rich result: canonical roots, exact rational parity, scheduled
dependency labels, and complete P-92 dispatch are all internal. -/
noncomputable def aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    Option LocalizedTetrahedralRSPseudoDescriptor := do
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let roots ← source.aromaticCanonicalOccurrenceLigandFrame? target
  let parity ← source.aromaticCanonicalRerootFrameParity? roots
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  source.aromaticCanonicalRule3Through6RSPseudoDescriptor? center.1 target
    (source.aromaticCanonicalDependencyView state target) ruleFuel roots parity

def AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) : Prop :=
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  ∃ roots parity,
    source.aromaticCanonicalOccurrenceLigandFrame? target = some roots ∧
      source.aromaticCanonicalRerootFrameParity? roots = some parity ∧
      source.AromaticCanonicalRule3Through6RSPseudoExecutableJudgment center.1 target
        (source.aromaticCanonicalDependencyView state target)
        ruleFuel roots parity descriptor

theorem aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_some_iff
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter)
    (descriptor : LocalizedTetrahedralRSPseudoDescriptor) :
    source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
        semantics ruleFuel center = some descriptor ↔
      source.AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
        semantics ruleFuel center descriptor := by
  unfold aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
    AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
  let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
  let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
  constructor
  · intro computed
    cases rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame? target with
    | none => simp [target, rootsComputed] at computed
    | some roots =>
        cases parityComputed : source.aromaticCanonicalRerootFrameParity? roots with
        | none => simp [target, rootsComputed, parityComputed] at computed
        | some parity =>
            have finalComputed :
                source.aromaticCanonicalRule3Through6RSPseudoDescriptor? center.1 target
                    (source.aromaticCanonicalDependencyView state target)
                    ruleFuel roots parity = some descriptor := by
              simpa [target, rootsComputed, parityComputed, state] using computed
            exact ⟨roots, parity, rootsComputed, parityComputed,
              (source.aromaticCanonicalRule3Through6RSPseudoDescriptor?_eq_some_iff
                center.1 target (source.aromaticCanonicalDependencyView state target)
                ruleFuel roots parity descriptor).mp finalComputed⟩
  · rintro ⟨roots, parity, rootsComputed, parityComputed, finalJudgment⟩
    have finalComputed :
        source.aromaticCanonicalRule3Through6RSPseudoDescriptor? center.1 target
            (source.aromaticCanonicalDependencyView state target)
            ruleFuel roots parity = some descriptor :=
      (source.aromaticCanonicalRule3Through6RSPseudoDescriptor?_eq_some_iff
        center.1 target (source.aromaticCanonicalDependencyView state target)
        ruleFuel roots parity descriptor).mpr finalJudgment
    simpa [target, rootsComputed, parityComputed, state] using finalComputed

/-- Descriptor-independent readiness of the complete rich molecule endpoint. -/
def AromaticCanonicalScheduledRule3Through6RSPseudoReady
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) : Prop :=
  ∃ descriptor,
    source.AromaticCanonicalScheduledRule3Through6RSPseudoExecutableJudgment
      semantics ruleFuel center descriptor

theorem aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_isSome_iff_ready
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    (source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
        semantics ruleFuel center).isSome = true ↔
      source.AromaticCanonicalScheduledRule3Through6RSPseudoReady
        semantics ruleFuel center := by
  rw [Option.isSome_iff_exists]
  unfold AromaticCanonicalScheduledRule3Through6RSPseudoReady
  exact exists_congr fun descriptor =>
    source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_some_iff
      semantics ruleFuel center descriptor

theorem aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_eq_none_iff_not_ready
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (semantics : source.AromaticCanonicalRuleSemantics carrierFuel)
    (ruleFuel : Nat) (center : source.AromaticCanonicalTetrahedralCenter) :
    source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
        semantics ruleFuel center = none ↔
      ¬ source.AromaticCanonicalScheduledRule3Through6RSPseudoReady
        semantics ruleFuel center := by
  rw [← source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?_isSome_iff_ready]
  cases source.aromaticCanonicalScheduledRule3Through6RSPseudoDescriptor?
      semantics ruleFuel center <;> simp

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
