import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.OneCenter.DeclarativeCIPRule6

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

/-!
# Production Rule-6 consistency certificates

This module states and proves what the executable equivalent-reference check actually establishes:
all checked references produce a unique ranking with the same final `R/S` descriptor.  It does not
claim that their rankings or pairwise comparisons are identical.
-/

theorem option_allM_eq_some_true_iff {α : Type*} (values : List α)
    (predicate : α → Option Bool) :
    values.allM predicate = some true ↔
      ∀ value, value ∈ values → predicate value = some true := by
  induction values with
  | nil => simp [List.allM]
  | cons value values ih =>
      simp only [List.allM]
      cases hvalue : predicate value with
      | none => simp [hvalue]
      | some decision =>
          cases decision <;> simp [hvalue, ih]

/-! ## Exact shape of the two-group reference enumeration -/

/-- Reference class selected syntactically by edge 1 of a candidate two-group partition.

The three disjuncts are respectively `a|bbb`, `aa|bb`, and `aaa|b`.  They deliberately describe
the complete enumerated group, independently of the executable list constructor.  A production
caller must separately certify that the candidate partition is a valid Rules-1--5 equivalence
partition before interpreting this enumeration as semantic admissibility. -/
def TwoGroupEnumeratedReferencePosition (sorted : List ℕ)
    (adjacent : List (Option Ordering)) (position : ℕ) : Prop :=
  (adjacent.getD 0 none = some Ordering.gt ∧
    (position = sorted.getD 1 0 ∨ position = sorted.getD 2 0 ∨
      position = sorted.getD 3 0)) ∨
  (adjacent.getD 0 none ≠ some Ordering.gt ∧
    adjacent.getD 1 none = some Ordering.gt ∧
    (position = sorted.getD 1 0 ∨ position = sorted.getD 0 0)) ∨
  (adjacent.getD 0 none ≠ some Ordering.gt ∧
    adjacent.getD 1 none ≠ some Ordering.gt ∧
    (position = sorted.getD 1 0 ∨ position = sorted.getD 2 0 ∨
      position = sorted.getD 0 0))

/-- `rule6EquivalentReferencePositions` enumerates exactly the class selected by its three
candidate boundary shapes. -/
theorem mem_rule6EquivalentReferencePositions_iff_enumerated
    (sorted : List ℕ) (adjacent : List (Option Ordering)) (position : ℕ) :
    position ∈ rule6EquivalentReferencePositions sorted adjacent ↔
      TwoGroupEnumeratedReferencePosition sorted adjacent position := by
  unfold rule6EquivalentReferencePositions TwoGroupEnumeratedReferencePosition
  by_cases hfirst : adjacent[0]?.getD none = some Ordering.gt
  · simp [hfirst]
  · by_cases hsecond : adjacent[1]?.getD none = some Ordering.gt
    · simp [hfirst, hsecond]
    · simp [hfirst, hsecond]

/-- Proof-relevant certificate for the production equivalent-reference check. -/
def Rule6EquivalentReferencesCertificate
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (parity : TetrahedralInputParity)
    (ligands sorted references : List ℕ) (first : Rule6TrackedRanking) : Prop :=
  first.unique = true ∧
    ∃ firstReferencePosition,
      references.head? = some firstReferencePosition ∧
      rankBranchPositionsThroughRule6Tracked? result mol state fuel center
        (ligands.getD firstReferencePosition 0) ligands sorted = some first ∧
      ∀ referencePosition, referencePosition ∈ references.tail →
        ∃ ranking,
          rankBranchPositionsThroughRule6Tracked? result mol state fuel center
            (ligands.getD referencePosition 0) ligands sorted = some ranking ∧
          ranking.unique = true ∧
          RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven ranking.positions) =
            RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven first.positions)

/-- Successful production consistency checking certifies descriptor agreement for every reference
it checked. -/
theorem rankRule6EquivalentReferences?_sound
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (parity : TetrahedralInputParity)
    (ligands sorted references : List ℕ) (first : Rule6TrackedRanking)
    (accepted : rankRule6EquivalentReferences? result mol state fuel center parity
      ligands sorted references = some first) :
    Rule6EquivalentReferencesCertificate result mol state fuel center parity
      ligands sorted references first := by
  unfold rankRule6EquivalentReferences? at accepted
  cases hhead : references.head? with
  | none => simp [hhead] at accepted
  | some firstReferencePosition =>
      cases hfirst : rankBranchPositionsThroughRule6Tracked? result mol state fuel center
          (ligands.getD firstReferencePosition 0) ligands sorted with
      | none =>
          change rankBranchPositionsThroughRule6Tracked? result mol state fuel center
            (ligands[firstReferencePosition]?.getD 0) ligands sorted = none at hfirst
          simp [hhead, hfirst] at accepted
      | some firstRanking =>
          change rankBranchPositionsThroughRule6Tracked? result mol state fuel center
            (ligands[firstReferencePosition]?.getD 0) ligands sorted = some firstRanking at hfirst
          cases hunique : firstRanking.unique with
          | false => simp [hhead, hfirst, hunique] at accepted
          | true =>
              let descriptor := RawMolecule.descriptorOfParity parity
                (RawMolecule.permutationIsEven firstRanking.positions)
              let checkReference := fun (referencePosition : ℕ) =>
                (rankBranchPositionsThroughRule6Tracked? result mol state fuel center
                  (ligands[referencePosition]?.getD 0) ligands sorted).bind fun ranking =>
                    some (ranking.unique &&
                      RawMolecule.descriptorOfParity parity
                        (RawMolecule.permutationIsEven ranking.positions) == descriptor)
              cases hconsistent : references.tail.allM checkReference with
              | none => simp [hhead, hfirst, hunique, descriptor, checkReference,
                  hconsistent] at accepted
              | some consistent =>
                  cases consistent with
                  | false => simp [hhead, hfirst, hunique, descriptor, checkReference,
                      hconsistent] at accepted
                  | true =>
                      have hfirstEq : firstRanking = first := by
                        simpa [hhead, hfirst, hunique, descriptor, checkReference,
                          hconsistent] using accepted
                      subst firstRanking
                      refine ⟨hunique, firstReferencePosition, hhead, hfirst, ?_⟩
                      intro referencePosition hreference
                      have hchecked :=
                        (option_allM_eq_some_true_iff
                          references.tail checkReference).1 hconsistent
                            referencePosition hreference
                      cases hranking : rankBranchPositionsThroughRule6Tracked? result mol state
                          fuel center (ligands.getD referencePosition 0) ligands sorted with
                      | none =>
                          change rankBranchPositionsThroughRule6Tracked? result mol state fuel center
                            (ligands[referencePosition]?.getD 0) ligands sorted = none at hranking
                          simp [checkReference, hranking] at hchecked
                      | some ranking =>
                          change rankBranchPositionsThroughRule6Tracked? result mol state fuel center
                            (ligands[referencePosition]?.getD 0) ligands sorted = some ranking
                              at hranking
                          have hchecked' :
                              some (ranking.unique &&
                                RawMolecule.descriptorOfParity parity
                                    (RawMolecule.permutationIsEven ranking.positions) == descriptor) =
                                some true := by
                            simpa [checkReference, hranking] using hchecked
                          have hbool : (ranking.unique &&
                              RawMolecule.descriptorOfParity parity
                                  (RawMolecule.permutationIsEven ranking.positions) == descriptor) =
                                true :=
                            Option.some.inj hchecked'
                          have hand : ranking.unique = true ∧
                              RawMolecule.descriptorOfParity parity
                                  (RawMolecule.permutationIsEven ranking.positions) = descriptor := by
                            simpa using hbool
                          refine ⟨ranking, rfl, hand.1, ?_⟩
                          simpa [descriptor] using hand.2

/-- A production Rule-6 ranking backend.  The argument is a ligand position in the promoted
reference class, not an atom number.  Raw-descriptor and root-relative occurrence evaluation
instantiate this same interface with their respective state-sensitive ranking computations. -/
abbrev ProductionRule6RankingBackend := ℕ → Option Rule6TrackedRanking

/-- Descriptor produced by one checked reference position through an arbitrary production
Rule-6 ranking backend.  This is the shared descriptor-level judgment: state representation is
deliberately absent from the proposition once its ranking backend has been supplied. -/
def ProductionRule6BackendDescriptorJudgment
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (referencePosition : ℕ) (descriptor : RS) : Prop :=
  ∃ ranking,
    backend referencePosition = some ranking ∧
    ranking.unique = true ∧
    RawMolecule.descriptorOfParity parity
      (RawMolecule.permutationIsEven ranking.positions) = descriptor

/-- Proof-relevant form of the shared backend-parametric descriptor judgment. -/
structure ProductionRule6BackendDescriptorCertificate
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (referencePosition : ℕ) (descriptor : RS) where
  ranking : Rule6TrackedRanking
  accepted : backend referencePosition = some ranking
  unique : ranking.unique = true
  descriptor_eq : RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven ranking.positions) = descriptor

theorem productionRule6BackendDescriptorJudgment_iff_certificate
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (referencePosition : ℕ) (descriptor : RS) :
    ProductionRule6BackendDescriptorJudgment backend parity referencePosition descriptor ↔
      Nonempty (ProductionRule6BackendDescriptorCertificate backend parity referencePosition
        descriptor) := by
  constructor
  · rintro ⟨ranking, accepted, unique, descriptorEq⟩
    exact ⟨⟨ranking, accepted, unique, descriptorEq⟩⟩
  · rintro ⟨⟨ranking, accepted, unique, descriptorEq⟩⟩
    exact ⟨ranking, accepted, unique, descriptorEq⟩

theorem productionRule6BackendDescriptorJudgment_functional
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (referencePosition : ℕ) {first second : RS}
    (hfirst : ProductionRule6BackendDescriptorJudgment backend parity referencePosition first)
    (hsecond : ProductionRule6BackendDescriptorJudgment backend parity referencePosition second) :
    first = second := by
  rcases hfirst with ⟨firstRanking, hfirstRanking, _, hfirstValue⟩
  rcases hsecond with ⟨secondRanking, hsecondRanking, _, hsecondValue⟩
  have hranking : firstRanking = secondRanking :=
    Option.some.inj (hfirstRanking.symm.trans hsecondRanking)
  subst secondRanking
  exact hfirstValue.symm.trans hsecondValue

/-! ## Backend-parametric equivalent-reference certificate -/

/-- Run the production all-equivalent-reference check through an arbitrary Rule-6 ranking
backend.  Raw-descriptor and root-relative occurrence ranking use this same semantic algorithm;
only their backend functions differ. -/
def rankProductionRule6EquivalentReferencesWithBackend?
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List ℕ) : Option Rule6TrackedRanking := do
  let firstReferencePosition ← references.head?
  let first ← backend firstReferencePosition
  if !first.unique then none else
  let descriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven first.positions)
  let consistent ← references.tail.allM fun referencePosition => do
    let ranking ← backend referencePosition
    some (ranking.unique &&
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven ranking.positions) == descriptor)
  if consistent then some first else none

/-- Proof-relevant meaning of a successful all-equivalent-reference check.  Crucially, the last
field exposes the shared production descriptor judgment for every listed reference, rather than
only for the first reference returned by the executable checker. -/
structure ProductionRule6BackendEquivalentReferencesCertificate
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List ℕ) (first : Rule6TrackedRanking) where
  firstReferencePosition : ℕ
  reference_head : references.head? = some firstReferencePosition
  first_ranking : backend firstReferencePosition = some first
  first_unique : first.unique = true
  all_references : ∀ referencePosition, referencePosition ∈ references →
    ProductionRule6BackendDescriptorJudgment backend parity referencePosition
      (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven first.positions))

/-- Successful backend-parametric consistency checking certifies the common production descriptor
judgment at every equivalent reference. -/
theorem rankProductionRule6EquivalentReferencesWithBackend?_sound
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List ℕ) (first : Rule6TrackedRanking)
    (accepted : rankProductionRule6EquivalentReferencesWithBackend? backend parity references =
      some first) :
    Nonempty
      (ProductionRule6BackendEquivalentReferencesCertificate backend parity references first) := by
  unfold rankProductionRule6EquivalentReferencesWithBackend? at accepted
  cases headEq : references.head? with
  | none => simp [headEq] at accepted
  | some firstReferencePosition =>
      cases firstEq : backend firstReferencePosition with
      | none => simp [headEq, firstEq] at accepted
      | some firstRanking =>
          cases uniqueEq : firstRanking.unique with
          | false => simp [headEq, firstEq, uniqueEq] at accepted
          | true =>
              let descriptor := RawMolecule.descriptorOfParity parity
                (RawMolecule.permutationIsEven firstRanking.positions)
              let checkReference := fun referencePosition => do
                let ranking ← backend referencePosition
                some (ranking.unique &&
                  RawMolecule.descriptorOfParity parity
                    (RawMolecule.permutationIsEven ranking.positions) == descriptor)
              simp [Option.bind, headEq, firstEq, uniqueEq] at accepted
              change (references.tail.allM checkReference).bind
                (fun consistent => if consistent then some firstRanking else none) = some first
                at accepted
              cases consistentEq : references.tail.allM checkReference with
              | none =>
                  simp [consistentEq] at accepted
              | some consistent =>
                  cases consistent with
                  | false =>
                      simp [consistentEq] at accepted
                  | true =>
                      have firstRankingEq : firstRanking = first := by
                        simpa [consistentEq] using accepted
                      subst firstRanking
                      refine ⟨
                        { firstReferencePosition := firstReferencePosition
                          reference_head := headEq
                          first_ranking := firstEq
                          first_unique := uniqueEq
                          all_references := ?_ }⟩
                      intro referencePosition referenceMember
                      cases references with
                      | nil => simp at headEq
                      | cons head tail =>
                          simp only [List.head?_cons, Option.some.injEq] at headEq
                          subst head
                          simp only [List.mem_cons] at referenceMember
                          rcases referenceMember with rfl | tailMember
                          · exact ⟨first, firstEq, uniqueEq, rfl⟩
                          · have checked :=
                              (option_allM_eq_some_true_iff tail checkReference).1 consistentEq
                                referencePosition tailMember
                            cases rankingEq : backend referencePosition with
                            | none => simp [checkReference, rankingEq] at checked
                            | some ranking =>
                                have checkedSome :
                                    some (ranking.unique &&
                                      RawMolecule.descriptorOfParity parity
                                          (RawMolecule.permutationIsEven ranking.positions) ==
                                        RawMolecule.descriptorOfParity parity
                                          (RawMolecule.permutationIsEven first.positions)) =
                                      some true := by
                                  simpa [checkReference, descriptor, rankingEq] using checked
                                have checked' :
                                    (ranking.unique &&
                                      RawMolecule.descriptorOfParity parity
                                          (RawMolecule.permutationIsEven ranking.positions) ==
                                        RawMolecule.descriptorOfParity parity
                                          (RawMolecule.permutationIsEven first.positions)) = true := by
                                  exact Option.some.inj checkedSome
                                have parts : ranking.unique = true ∧
                                    RawMolecule.descriptorOfParity parity
                                        (RawMolecule.permutationIsEven ranking.positions) =
                                      RawMolecule.descriptorOfParity parity
                                        (RawMolecule.permutationIsEven first.positions) := by
                                  simpa using checked'
                                exact ⟨ranking, rankingEq, parts.1, parts.2⟩

/-- The all-reference certificate is complete: its per-reference shared production judgments
reconstruct the executable consistency check. -/
theorem rankProductionRule6EquivalentReferencesWithBackend?_complete
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List ℕ) (first : Rule6TrackedRanking)
    (certificate : ProductionRule6BackendEquivalentReferencesCertificate backend parity
      references first) :
    rankProductionRule6EquivalentReferencesWithBackend? backend parity references = some first := by
  let descriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven first.positions)
  let checkReference := fun referencePosition => do
    let ranking ← backend referencePosition
    some (ranking.unique &&
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven ranking.positions) == descriptor)
  have consistent : references.tail.allM checkReference = some true := by
    apply (option_allM_eq_some_true_iff references.tail checkReference).2
    intro referencePosition tailMember
    rcases certificate.all_references referencePosition (List.mem_of_mem_tail tailMember) with
      ⟨ranking, rankingEq, uniqueEq, descriptorEq⟩
    simp [checkReference, rankingEq, uniqueEq, descriptor, descriptorEq]
  unfold rankProductionRule6EquivalentReferencesWithBackend?
  simp [Option.bind, certificate.reference_head, certificate.first_ranking,
    certificate.first_unique]
  change (references.tail.allM checkReference).bind
    (fun consistent => if consistent then some first else none) = some first
  rw [consistent]
  rfl

theorem rankProductionRule6EquivalentReferencesWithBackend?_iff_certificate
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (references : List ℕ) (first : Rule6TrackedRanking) :
    rankProductionRule6EquivalentReferencesWithBackend? backend parity references = some first ↔
      Nonempty
        (ProductionRule6BackendEquivalentReferencesCertificate backend parity references first) := by
  constructor
  · exact rankProductionRule6EquivalentReferencesWithBackend?_sound backend parity references first
  · rintro ⟨certificate⟩
    exact rankProductionRule6EquivalentReferencesWithBackend?_complete backend parity references
      first certificate

/-- The proof-relevant certificate specialized to the complete reference list returned by the
candidate two-group boundary enumeration.  Semantic admissibility requires a separately certified
partition, supplied by the occurrence-level integration. -/
abbrev ProductionRule6BackendAllEnumeratedReferencesCertificate
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (sorted : List ℕ) (adjacent : List (Option Ordering)) (first : Rule6TrackedRanking) :=
  ProductionRule6BackendEquivalentReferencesCertificate backend parity
    (rule6EquivalentReferencePositions sorted adjacent) first

theorem rankProductionRule6AllEnumeratedReferencesWithBackend?_sound
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (sorted : List ℕ) (adjacent : List (Option Ordering)) (first : Rule6TrackedRanking)
    (accepted : rankProductionRule6EquivalentReferencesWithBackend? backend parity
      (rule6EquivalentReferencePositions sorted adjacent) = some first) :
    Nonempty
      (ProductionRule6BackendAllEnumeratedReferencesCertificate backend parity sorted adjacent
        first) :=
  rankProductionRule6EquivalentReferencesWithBackend?_sound backend parity
    (rule6EquivalentReferencePositions sorted adjacent) first accepted

theorem rankProductionRule6AllEnumeratedReferencesWithBackend?_complete
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (sorted : List ℕ) (adjacent : List (Option Ordering)) (first : Rule6TrackedRanking)
    (certificate : ProductionRule6BackendAllEnumeratedReferencesCertificate backend parity
      sorted adjacent first) :
    rankProductionRule6EquivalentReferencesWithBackend? backend parity
      (rule6EquivalentReferencePositions sorted adjacent) = some first :=
  rankProductionRule6EquivalentReferencesWithBackend?_complete backend parity
    (rule6EquivalentReferencePositions sorted adjacent) first certificate

theorem rankProductionRule6AllEnumeratedReferencesWithBackend?_iff_certificate
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (sorted : List ℕ) (adjacent : List (Option Ordering)) (first : Rule6TrackedRanking) :
    rankProductionRule6EquivalentReferencesWithBackend? backend parity
        (rule6EquivalentReferencePositions sorted adjacent) = some first ↔
      Nonempty
        (ProductionRule6BackendAllEnumeratedReferencesCertificate backend parity sorted adjacent
          first) :=
  rankProductionRule6EquivalentReferencesWithBackend?_iff_certificate backend parity
    (rule6EquivalentReferencePositions sorted adjacent) first

namespace ProductionRule6BackendEquivalentReferencesCertificate

/-- When the supplied reference list is the exact candidate two-group enumeration, the certificate
licenses the common descriptor at every enumerated reference. -/
theorem enumerated_reference
    {backend : ProductionRule6RankingBackend} {parity : TetrahedralInputParity}
    {references sorted : List ℕ} {adjacent : List (Option Ordering)}
    {first : Rule6TrackedRanking}
    (certificate : ProductionRule6BackendEquivalentReferencesCertificate backend parity
      references first)
    (references_eq : references = rule6EquivalentReferencePositions sorted adjacent)
    (referencePosition : ℕ)
    (enumerated : TwoGroupEnumeratedReferencePosition sorted adjacent referencePosition) :
    ProductionRule6BackendDescriptorJudgment backend parity referencePosition
      (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven first.positions)) := by
  apply certificate.all_references referencePosition
  rw [references_eq, mem_rule6EquivalentReferencePositions_iff_enumerated]
  exact enumerated

end ProductionRule6BackendEquivalentReferencesCertificate

namespace ProductionRule6BackendAllEnumeratedReferencesCertificate

/-- Every reference in the complete candidate two-group enumeration carries the same production
descriptor judgment. -/
theorem enumerated_reference
    {backend : ProductionRule6RankingBackend} {parity : TetrahedralInputParity}
    {sorted : List ℕ} {adjacent : List (Option Ordering)} {first : Rule6TrackedRanking}
    (certificate : ProductionRule6BackendAllEnumeratedReferencesCertificate backend parity
      sorted adjacent first)
    (referencePosition : ℕ)
    (enumerated : TwoGroupEnumeratedReferencePosition sorted adjacent referencePosition) :
    ProductionRule6BackendDescriptorJudgment backend parity referencePosition
      (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven first.positions)) := by
  apply certificate.all_references referencePosition
  rw [mem_rule6EquivalentReferencePositions_iff_enumerated]
  exact enumerated

end ProductionRule6BackendAllEnumeratedReferencesCertificate

/-- Legacy raw-descriptor-state ranking as an instance of the shared production backend. -/
def rawProductionRule6RankingBackend
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (ligands sorted : List ℕ) :
    ProductionRule6RankingBackend :=
  fun referencePosition =>
    rankBranchPositionsThroughRule6Tracked? result mol state fuel center
      (ligands.getD referencePosition 0) ligands sorted

/-- Existing raw-state API, now defined as the exact specialization of the shared
backend-parametric production judgment. -/
def ProductionRule6DescriptorJudgment
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (parity : TetrahedralInputParity)
    (ligands sorted : List ℕ) (referencePosition : ℕ) (descriptor : RS) : Prop :=
  ProductionRule6BackendDescriptorJudgment
    (rawProductionRule6RankingBackend result mol state fuel center ligands sorted)
    parity referencePosition descriptor

/-- Certificate form of the existing raw-state descriptor API. -/
theorem productionRule6DescriptorJudgment_iff_certificate
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (parity : TetrahedralInputParity)
    (ligands sorted : List ℕ) (referencePosition : ℕ) (descriptor : RS) :
    ProductionRule6DescriptorJudgment result mol state fuel center parity ligands sorted
        referencePosition descriptor ↔
      Nonempty (ProductionRule6BackendDescriptorCertificate
        (rawProductionRule6RankingBackend result mol state fuel center ligands sorted)
        parity referencePosition descriptor) :=
  productionRule6BackendDescriptorJudgment_iff_certificate _ _ _ _

theorem productionRule6DescriptorJudgment_functional
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (parity : TetrahedralInputParity)
    (ligands sorted : List ℕ) (referencePosition : ℕ) {first second : RS}
    (hfirst : ProductionRule6DescriptorJudgment result mol state fuel center parity
      ligands sorted referencePosition first)
    (hsecond : ProductionRule6DescriptorJudgment result mol state fuel center parity
      ligands sorted referencePosition second) :
    first = second :=
  productionRule6BackendDescriptorJudgment_functional
    (rawProductionRule6RankingBackend result mol state fuel center ligands sorted)
    parity referencePosition hfirst hsecond

namespace Rule6EquivalentReferencesCertificate

/-- Every member of a certified reference list has a unique ranking carrying the returned first
ranking's descriptor. -/
theorem reference_agrees
    {result : ChemistryNormalizationResult} {mol : RawMolecule}
    {state : RawDescriptorState} {fuel center : ℕ} {parity : TetrahedralInputParity}
    {ligands sorted references : List ℕ} {first : Rule6TrackedRanking}
    (certificate : Rule6EquivalentReferencesCertificate result mol state fuel center parity
      ligands sorted references first)
    (referencePosition : ℕ) (hreference : referencePosition ∈ references) :
    ProductionRule6DescriptorJudgment result mol state fuel center parity ligands sorted
      referencePosition
      (RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven first.positions)) := by
  rcases certificate with ⟨hunique, firstReferencePosition, hhead, hfirst, hall⟩
  cases references with
  | nil => simp at hhead
  | cons head tail =>
      simp only [List.head?_cons, Option.some.injEq] at hhead
      subst head
      simp only [List.mem_cons] at hreference
      rcases hreference with rfl | htail
      · exact ⟨first, hfirst, hunique, rfl⟩
      · exact hall referencePosition htail

end Rule6EquivalentReferencesCertificate

/-- What the production check genuinely proves: any two checked reference positions license the
same final descriptor, without requiring identical rankings. -/
theorem rankRule6EquivalentReferences?_descriptor_independent
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (parity : TetrahedralInputParity)
    (ligands sorted references : List ℕ) (first : Rule6TrackedRanking)
    (accepted : rankRule6EquivalentReferences? result mol state fuel center parity
      ligands sorted references = some first)
    {reference₁ reference₂ : ℕ} (href₁ : reference₁ ∈ references)
    (href₂ : reference₂ ∈ references) {descriptor₁ descriptor₂ : RS}
    (hdescriptor₁ : ProductionRule6DescriptorJudgment result mol state fuel center parity
      ligands sorted reference₁ descriptor₁)
    (hdescriptor₂ : ProductionRule6DescriptorJudgment result mol state fuel center parity
      ligands sorted reference₂ descriptor₂) :
    descriptor₁ = descriptor₂ := by
  have certificate := rankRule6EquivalentReferences?_sound result mol state fuel center parity
    ligands sorted references first accepted
  have hcommon₁ := certificate.reference_agrees reference₁ href₁
  have hcommon₂ := certificate.reference_agrees reference₂ href₂
  rcases hdescriptor₁ with ⟨ranking₁, hranking₁, _, hvalue₁⟩
  rcases hdescriptor₂ with ⟨ranking₂, hranking₂, _, hvalue₂⟩
  rcases hcommon₁ with ⟨commonRanking₁, hcommonRanking₁, _, hcommonValue₁⟩
  rcases hcommon₂ with ⟨commonRanking₂, hcommonRanking₂, _, hcommonValue₂⟩
  have hrankingEq₁ : ranking₁ = commonRanking₁ :=
    Option.some.inj (hranking₁.symm.trans hcommonRanking₁)
  have hrankingEq₂ : ranking₂ = commonRanking₂ :=
    Option.some.inj (hranking₂.symm.trans hcommonRanking₂)
  subst commonRanking₁
  subst commonRanking₂
  exact hvalue₁.symm.trans (hcommonValue₁.trans (hcommonValue₂.symm.trans hvalue₂))

/-! ## Four-way S4 promotion certificate -/

/-- Semantic facts certified by the special two-promotion S4 helper. -/
def Rule6FourWayAgreementCertificate (parity : TetrahedralInputParity)
    (agreement : Rule6FourWayAgreement) : Prop :=
  agreement.firstRanking.positions ≠ agreement.secondRanking.positions ∧
    RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven agreement.firstRanking.positions) =
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven agreement.secondRanking.positions) ∧
    agreement.firstRanking.unique = agreement.secondRanking.unique ∧
    agreement.descriptor =
      if agreement.secondRanking.unique then
        RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven agreement.secondRanking.positions)
      else
        RS.swap (RawMolecule.descriptorOfParity parity
          (RawMolecule.permutationIsEven agreement.secondRanking.positions))

/-- Successful four-way processing exposes the different carrier orders, common molecular-root
descriptor, matching uniqueness status, and exact parity-quotient output. -/
theorem rankRule6FourWayReferences?_sound
    (result : ChemistryNormalizationResult) (mol : RawMolecule)
    (state : RawDescriptorState) (fuel center : ℕ) (parity : TetrahedralInputParity)
    (ligands sorted : List ℕ) (agreement : Rule6FourWayAgreement)
    (accepted : rankRule6FourWayReferences? result mol state fuel center parity
      ligands sorted = some agreement) :
    Rule6FourWayAgreementCertificate parity agreement := by
  unfold rankRule6FourWayReferences? at accepted
  cases hfirstPosition : sorted[0]? with
  | none => simp [hfirstPosition] at accepted
  | some firstPosition =>
      cases hfirst : rankBranchPositionsThroughRule6Tracked? result mol state fuel center
          (ligands.getD firstPosition 0) ligands sorted with
      | none =>
          change rankBranchPositionsThroughRule6Tracked? result mol state fuel center
            (ligands[firstPosition]?.getD 0) ligands sorted = none at hfirst
          simp [hfirstPosition, hfirst] at accepted
      | some firstRanking =>
          change rankBranchPositionsThroughRule6Tracked? result mol state fuel center
            (ligands[firstPosition]?.getD 0) ligands sorted = some firstRanking at hfirst
          let secondReference := ligands.getD (firstRanking.positions.getD 1 0) 0
          cases hsecond : rankBranchPositionsThroughRule6Tracked? result mol state fuel center
              secondReference ligands firstRanking.positions with
          | none =>
              change rankBranchPositionsThroughRule6Tracked? result mol state fuel center
                (ligands[firstRanking.positions[1]?.getD 0]?.getD 0)
                  ligands firstRanking.positions = none at hsecond
              simp [hfirstPosition, hfirst, hsecond] at accepted
          | some secondRanking =>
              change rankBranchPositionsThroughRule6Tracked? result mol state fuel center
                (ligands[firstRanking.positions[1]?.getD 0]?.getD 0)
                  ligands firstRanking.positions = some secondRanking at hsecond
              let firstDescriptor := RawMolecule.descriptorOfParity parity
                (RawMolecule.permutationIsEven firstRanking.positions)
              let secondDescriptor := RawMolecule.descriptorOfParity parity
                (RawMolecule.permutationIsEven secondRanking.positions)
              by_cases hdifferent : firstRanking.positions ≠ secondRanking.positions
              · by_cases hdescriptor : firstDescriptor = secondDescriptor
                · by_cases hunique : firstRanking.unique = secondRanking.unique
                  · have hagreement :
                        ({ firstRanking := firstRanking
                           secondRanking := secondRanking
                           descriptor := if secondRanking.unique then secondDescriptor
                             else RS.swap secondDescriptor } : Rule6FourWayAgreement) = agreement := by
                      have haccepted :
                          some ({ firstRanking := firstRanking
                                  secondRanking := secondRanking
                                  descriptor := if secondRanking.unique then secondDescriptor
                                    else RS.swap secondDescriptor } : Rule6FourWayAgreement) =
                            some agreement := by
                        simpa [hfirstPosition, hfirst, hsecond, firstDescriptor,
                          secondDescriptor, hdifferent, hdescriptor, hunique] using accepted
                      exact Option.some.inj haccepted
                    subst agreement
                    exact ⟨hdifferent, hdescriptor, hunique, rfl⟩
                  · simp [hfirstPosition, hfirst, hsecond,
                      firstDescriptor, secondDescriptor, hdifferent, hdescriptor, hunique]
                      at accepted
                · simp [hfirstPosition, hfirst, hsecond,
                    firstDescriptor, secondDescriptor, hdifferent, hdescriptor] at accepted
              · simp [hfirstPosition, hfirst, hsecond, hdifferent] at accepted

end OneCenter
end TetraStereo
