import TetraStereo.OneCenter.CIPAuthoritativeRule6ReferenceFamily
import TetraStereo.OneCenter.Rule6FourWayFamilyCore

set_option autoImplicit false

namespace TetraStereo.OneCenter.AuthoritativeCIPRule6P92Enumeration

open RawMolecule
open DeclarativeCIP.ProductionOccurrenceRules456
open AuthoritativeCIPOccurrenceCompleteness
open AuthoritativeCIPMoleculeCursorRanking
open AuthoritativeCIPRule6ReferenceFamily
open Rule6ReferenceFamilySemantics
open Rule6FourWayFamilySemantics

/-!
# Exact P-92 Rule-6 reference enumeration over the uncapped occurrence comparator

The production carrier enumerates *positions* in the four-ligand frame.  The authoritative
occurrence comparator consumes the atom chosen as the Rule-4b/Rule-5 reference.  The adapter below
is the missing typed bridge: a reference position is mapped through the actual ligand list before
the uncapped comparator is run.
-/

/-- Interpret a P-92 reference position as its ligand atom, then run the uncapped authoritative
occurrence ranking. -/
def authoritativeOccurrenceRule6PositionRankingBackend (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (roots : List CanonicalRerootCursor)
    (ligands : List Nat) : ProductionRule6RankingBackend :=
  fun referencePosition =>
    authoritativeOccurrenceRule6RankingBackend mol state fuel roots
      (ligands.getD referencePosition 0)

/-- The position adapter preserves the proved carrier permutation invariant. -/
theorem authoritativeOccurrenceRule6PositionRankingBackend_positions_perm
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands : List Nat)
    (referencePosition : Nat) (ranking : Rule6TrackedRanking)
    (computed : authoritativeOccurrenceRule6PositionRankingBackend mol state fuel roots ligands
      referencePosition = some ranking) :
    ranking.positions.Perm (List.range roots.length) := by
  exact rankOccurrenceLigandsThroughRule6UnrestrictedAuthoritative?_positions_perm
    mol state (ligands.getD referencePosition 0) fuel roots ranking computed

/-- Chemical applicability makes every P-92 reference position executable after position-to-atom
interpretation.  The theorem is deliberately total on `Nat`: exact-family membership is handled
by the branch-specific enumeration theorems below. -/
theorem authoritativeOccurrenceRule6PositionRankingBackend_total_of_chemical_applicability
    {mol : RawMolecule} {state : OccurrenceAuxState} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : AuthoritativeCIPMancudeTotality.LocalizedMancudeKekuleAdmissible mol)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated : CanonicalCenterTreeNode mol center occurrence)
    (ligands : List Nat) :
    ∀ referencePosition,
      ∃ ranking,
        authoritativeOccurrenceRule6PositionRankingBackend mol state
            (2 * mol.atomCount + 1) (occurrenceLigandCursors mol occurrence) ligands
            referencePosition = some ranking := by
  intro referencePosition
  exact authoritativeOccurrenceRule6RankingBackend_total_of_chemical_applicability
    centerBound wellFormed unique valence kekule occurrenceGenerated
      (ligands.getD referencePosition 0)

/-- Descriptor projection for any P-92 position family. -/
def authoritativeOccurrenceRule6PositionFamilyDescriptor? (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (roots : List CanonicalRerootCursor)
    (ligands : List Nat) (parity : TetrahedralInputParity)
    (references : List Nat) : Option RS :=
  rule6FamilyDescriptorWithBackend?
    (authoritativeOccurrenceRule6PositionRankingBackend mol state fuel roots ligands)
    parity references

/-- Position-family descriptor emission is exactly common strict-reference semantics. -/
theorem authoritativeOccurrenceRule6PositionFamilyDescriptor?_eq_some_iff_commonDescriptor
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands : List Nat)
    (parity : TetrahedralInputParity) (references : List Nat) (descriptor : RS) :
    authoritativeOccurrenceRule6PositionFamilyDescriptor? mol state fuel roots ligands parity
        references = some descriptor ↔
      CommonRule6Descriptor
        (authoritativeOccurrenceRule6PositionRankingBackend mol state fuel roots ligands)
        parity references descriptor := by
  exact rule6FamilyDescriptorWithBackend?_eq_some_iff_commonDescriptor
    (authoritativeOccurrenceRule6PositionRankingBackend mol state fuel roots ligands)
    parity references descriptor

/-! ## Exact two-group family -/

/-- P-92's exact two-group descriptor calculation: all positions enumerated by the rank-one
equivalence-class selector must agree. -/
def authoritativeOccurrenceRule6TwoGroupDescriptor? (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (roots : List CanonicalRerootCursor)
    (ligands sorted : List Nat) (adjacent : List (Option Ordering))
    (parity : TetrahedralInputParity) : Option RS :=
  authoritativeOccurrenceRule6PositionFamilyDescriptor? mol state fuel roots ligands parity
    (rule6EquivalentReferencePositions sorted adjacent)

/-- The executable two-group branch emits exactly the common descriptor of the independently
specified complete rank-one reference class. -/
theorem authoritativeOccurrenceRule6TwoGroupDescriptor?_eq_some_iff_commonDescriptor
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (adjacent : List (Option Ordering)) (parity : TetrahedralInputParity) (descriptor : RS) :
    authoritativeOccurrenceRule6TwoGroupDescriptor? mol state fuel roots ligands sorted adjacent
        parity = some descriptor ↔
      CommonRule6Descriptor
        (authoritativeOccurrenceRule6PositionRankingBackend mol state fuel roots ligands)
        parity (rule6EquivalentReferencePositions sorted adjacent) descriptor := by
  exact authoritativeOccurrenceRule6PositionFamilyDescriptor?_eq_some_iff_commonDescriptor
    mol state fuel roots ligands parity
      (rule6EquivalentReferencePositions sorted adjacent) descriptor

/-- The shape-level two-group selector is never empty. -/
theorem rule6EquivalentReferencePositions_ne_nil
    (sorted : List Nat) (adjacent : List (Option Ordering)) :
    rule6EquivalentReferencePositions sorted adjacent ≠ [] := by
  unfold rule6EquivalentReferencePositions
  by_cases first : adjacent[0]?.getD none = some Ordering.gt
  · simp [first]
  · by_cases second : adjacent[1]?.getD none = some Ordering.gt
    · simp [first, second]
    · simp [first, second]

/-- On chemically applicable input, the exact two-group branch can refuse only because a listed
ranking is non-strict or because two strict reference choices disagree on the descriptor. -/
theorem authoritativeOccurrenceRule6TwoGroupDescriptor?_eq_none_iff_failureWitness
    {mol : RawMolecule} {state : OccurrenceAuxState} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : AuthoritativeCIPMancudeTotality.LocalizedMancudeKekuleAdmissible mol)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated : CanonicalCenterTreeNode mol center occurrence)
    (ligands sorted : List Nat) (adjacent : List (Option Ordering))
    (parity : TetrahedralInputParity) :
    authoritativeOccurrenceRule6TwoGroupDescriptor? mol state (2 * mol.atomCount + 1)
        (occurrenceLigandCursors mol occurrence) ligands sorted adjacent parity = none ↔
      HasNonStrictRule6Reference
          (authoritativeOccurrenceRule6PositionRankingBackend mol state
            (2 * mol.atomCount + 1) (occurrenceLigandCursors mol occurrence) ligands)
          (rule6EquivalentReferencePositions sorted adjacent) ∨
        HasRule6ReferenceDescriptorConflict
          (authoritativeOccurrenceRule6PositionRankingBackend mol state
            (2 * mol.atomCount + 1) (occurrenceLigandCursors mol occurrence) ligands)
          parity (rule6EquivalentReferencePositions sorted adjacent) := by
  apply rule6FamilyDescriptorWithBackend?_eq_none_iff_failureWitness
  · exact rule6EquivalentReferencePositions_ne_nil sorted adjacent
  · intro referencePosition _member
    exact authoritativeOccurrenceRule6PositionRankingBackend_total_of_chemical_applicability
      centerBound wellFormed unique valence kekule occurrenceGenerated ligands referencePosition

/-! ## Exact three-group singleton family -/

/-- The three-group branch uses the ligand at sorted rank one as its sole reference. -/
def rule6ThreeGroupReferencePositions (sorted : List Nat) : List Nat :=
  [sorted[1]?.getD 0]

/-- The three-group branch reverses the descriptor obtained from its one strict promoted
reference, exactly as prescribed by the P-92 carrier construction. -/
def authoritativeOccurrenceRule6ThreeGroupDescriptor? (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : Nat) (roots : List CanonicalRerootCursor)
    (ligands sorted : List Nat) (parity : TetrahedralInputParity) : Option RS := do
  let descriptor ← authoritativeOccurrenceRule6PositionFamilyDescriptor?
    mol state fuel roots ligands parity (rule6ThreeGroupReferencePositions sorted)
  some (RS.swap descriptor)

@[simp] theorem rs_swap_involutive (descriptor : RS) :
    RS.swap (RS.swap descriptor) = descriptor := by
  cases descriptor <;> rfl

/-- Three-group emission is exactly the swapped common descriptor of its prescribed singleton
reference family. -/
theorem authoritativeOccurrenceRule6ThreeGroupDescriptor?_eq_some_iff_swappedCommonDescriptor
    (mol : RawMolecule) (state : OccurrenceAuxState) (fuel : Nat)
    (roots : List CanonicalRerootCursor) (ligands sorted : List Nat)
    (parity : TetrahedralInputParity) (descriptor : RS) :
    authoritativeOccurrenceRule6ThreeGroupDescriptor? mol state fuel roots ligands sorted parity =
        some descriptor ↔
      CommonRule6Descriptor
        (authoritativeOccurrenceRule6PositionRankingBackend mol state fuel roots ligands)
        parity (rule6ThreeGroupReferencePositions sorted) (RS.swap descriptor) := by
  unfold authoritativeOccurrenceRule6ThreeGroupDescriptor?
  cases familyEq : authoritativeOccurrenceRule6PositionFamilyDescriptor?
      mol state fuel roots ligands parity (rule6ThreeGroupReferencePositions sorted) with
  | none =>
      have noCommon :=
        (authoritativeOccurrenceRule6PositionFamilyDescriptor?_eq_some_iff_commonDescriptor
          mol state fuel roots ligands parity (rule6ThreeGroupReferencePositions sorted)
            (RS.swap descriptor)).not.mp
          (by simp [familyEq])
      simp [noCommon]
  | some base =>
      have commonBase :=
        (authoritativeOccurrenceRule6PositionFamilyDescriptor?_eq_some_iff_commonDescriptor
          mol state fuel roots ligands parity (rule6ThreeGroupReferencePositions sorted) base).mp
          familyEq
      constructor
      · intro emitted
        have baseEq : base = RS.swap descriptor := by
          have swappedEq : RS.swap base = descriptor := by simpa [familyEq] using emitted
          calc
            base = RS.swap (RS.swap base) := (rs_swap_involutive base).symm
            _ = RS.swap descriptor := congrArg RS.swap swappedEq
        simpa [baseEq] using commonBase
      · intro commonSwapped
        have descriptorsEqual : base = RS.swap descriptor :=
          commonRule6Descriptor_functional
            (authoritativeOccurrenceRule6PositionRankingBackend mol state fuel roots ligands)
            parity (rule6ThreeGroupReferencePositions sorted) commonBase commonSwapped
        simp [descriptorsEqual]

/-! ## Exact dependent four-way family -/

/-- Run the two dependent four-way promotions through the position-adapted authoritative backend.
The second reference is rank one of the first promoted order, matching the production carrier. -/
def authoritativeOccurrenceRule6FourWayAgreement? (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (sorted : List Nat) : Option Rule6FourWayAgreement := do
  let firstReference ← sorted[0]?
  let first ← backend firstReference
  let secondReference := first.positions[1]?.getD 0
  let second ← backend secondReference
  evaluateFourWayCarrier? parity first second

/-- Final descriptor projection of the exact dependent four-way carrier. -/
def authoritativeOccurrenceRule6FourWayDescriptor? (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (sorted : List Nat) : Option RS := do
  let agreement ← authoritativeOccurrenceRule6FourWayAgreement? backend parity sorted
  some agreement.descriptor

/-- Independent meaning of a successful dependent four-way descriptor: both prescribed rankings
exist, satisfy the three carrier-coherence equations, and produce the specified quotient-aware
descriptor. -/
def AuthoritativeFourWayDescriptorJudgment (backend : ProductionRule6RankingBackend)
    (parity : TetrahedralInputParity) (sorted : List Nat) (descriptor : RS) : Prop :=
  ∃ firstReference first second,
    sorted[0]? = some firstReference ∧
      backend firstReference = some first ∧
      backend (first.positions[1]?.getD 0) = some second ∧
      FourWayCarrierCoherent parity first second ∧
      (if second.unique then
          RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven second.positions)
        else
          RS.swap (RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven second.positions))) = descriptor

theorem evaluateFourWayCarrier_descriptor_eq_some_iff
    (parity : TetrahedralInputParity) (first second : Rule6TrackedRanking)
    (descriptor : RS) :
    (do
        let agreement ← evaluateFourWayCarrier? parity first second
        some agreement.descriptor) = some descriptor ↔
      FourWayCarrierCoherent parity first second ∧
        (if second.unique then
            RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven second.positions)
          else
            RS.swap (RawMolecule.descriptorOfParity parity
              (RawMolecule.permutationIsEven second.positions))) = descriptor := by
  unfold evaluateFourWayCarrier? FourWayCarrierCoherent
  by_cases different : first.positions ≠ second.positions
  · by_cases sameDescriptor :
        RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven first.positions) =
          RawMolecule.descriptorOfParity parity
            (RawMolecule.permutationIsEven second.positions)
    · by_cases sameUnique : first.unique = second.unique
      · simp [different, sameDescriptor, sameUnique]
      · simp [different, sameDescriptor, sameUnique]
    · simp [different, sameDescriptor]
  · simp [different]

/-- Four-way descriptor emission is equivalent to the independent dependent-reference judgment. -/
theorem authoritativeOccurrenceRule6FourWayDescriptor?_eq_some_iff_judgment
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (sorted : List Nat) (descriptor : RS) :
    authoritativeOccurrenceRule6FourWayDescriptor? backend parity sorted = some descriptor ↔
      AuthoritativeFourWayDescriptorJudgment backend parity sorted descriptor := by
  cases firstReferenceEq : sorted[0]? with
  | none =>
      simp [authoritativeOccurrenceRule6FourWayDescriptor?,
        authoritativeOccurrenceRule6FourWayAgreement?, firstReferenceEq,
        AuthoritativeFourWayDescriptorJudgment]
  | some firstReference =>
      cases firstEq : backend firstReference with
      | none =>
          simp [authoritativeOccurrenceRule6FourWayDescriptor?,
            authoritativeOccurrenceRule6FourWayAgreement?, firstReferenceEq, firstEq,
            AuthoritativeFourWayDescriptorJudgment]
      | some first =>
          cases secondEq : backend (first.positions[1]?.getD 0) with
          | none =>
              simp [authoritativeOccurrenceRule6FourWayDescriptor?,
                authoritativeOccurrenceRule6FourWayAgreement?, firstReferenceEq, firstEq, secondEq,
                AuthoritativeFourWayDescriptorJudgment]
          | some second =>
              have reduced :
                  authoritativeOccurrenceRule6FourWayDescriptor? backend parity sorted =
                    (do
                      let agreement ← evaluateFourWayCarrier? parity first second
                      some agreement.descriptor) := by
                simp [authoritativeOccurrenceRule6FourWayDescriptor?,
                  authoritativeOccurrenceRule6FourWayAgreement?, firstReferenceEq, firstEq,
                  secondEq]
              rw [reduced, evaluateFourWayCarrier_descriptor_eq_some_iff]
              simp only [AuthoritativeFourWayDescriptorJudgment]
              constructor
              · intro semantic
                exact ⟨firstReference, first, second, firstReferenceEq, firstEq, secondEq,
                  semantic⟩
              · rintro ⟨specifiedReference, specifiedFirst, specifiedSecond,
                  specifiedReferenceEq, specifiedFirstEq, specifiedSecondEq, semantic⟩
                have referenceIdentity : specifiedReference = firstReference :=
                  Option.some.inj (specifiedReferenceEq.symm.trans firstReferenceEq)
                subst specifiedReference
                have firstIdentity : specifiedFirst = first :=
                  Option.some.inj (specifiedFirstEq.symm.trans firstEq)
                subst specifiedFirst
                have secondIdentity : specifiedSecond = second :=
                  Option.some.inj (specifiedSecondEq.symm.trans secondEq)
                subst specifiedSecond
                exact semantic

/-- If the initial order has a first position and the adapted backend is total, both dependent
four-way rankings exist and refusal is exactly one of the three carrier-coherence failures. -/
theorem authoritativeOccurrenceRule6FourWay_failureClassification_exists
    (backend : ProductionRule6RankingBackend) (parity : TetrahedralInputParity)
    (sorted : List Nat) (firstPresent : ∃ firstReference, sorted[0]? = some firstReference)
    (rankingTotal : ∀ reference, ∃ ranking, backend reference = some ranking) :
    ∃ firstReference first second,
      sorted[0]? = some firstReference ∧
      backend firstReference = some first ∧
      backend (first.positions[1]?.getD 0) = some second ∧
      (authoritativeOccurrenceRule6FourWayDescriptor? backend parity sorted = none ↔
        HasFourWayCarrierFailure parity first second) := by
  rcases firstPresent with ⟨firstReference, firstReferenceEq⟩
  rcases rankingTotal firstReference with ⟨first, firstEq⟩
  rcases rankingTotal (first.positions[1]?.getD 0) with ⟨second, secondEq⟩
  refine ⟨firstReference, first, second, firstReferenceEq, firstEq, secondEq, ?_⟩
  constructor
  · intro descriptorNone
    have evaluatedNone : evaluateFourWayCarrier? parity first second = none := by
      cases evaluatedEq : evaluateFourWayCarrier? parity first second with
      | none => rfl
      | some agreement =>
          simp [authoritativeOccurrenceRule6FourWayDescriptor?,
            authoritativeOccurrenceRule6FourWayAgreement?, firstReferenceEq, firstEq, secondEq,
            evaluatedEq] at descriptorNone
    exact (evaluateFourWayCarrier?_eq_none_iff_failure parity first second).mp evaluatedNone
  · intro failure
    have evaluatedNone :=
      (evaluateFourWayCarrier?_eq_none_iff_failure parity first second).mpr failure
    simp [authoritativeOccurrenceRule6FourWayDescriptor?,
      authoritativeOccurrenceRule6FourWayAgreement?, firstReferenceEq, firstEq, secondEq,
      evaluatedNone]

/-- Chemical applicability discharges every operational premise of the dependent four-way
carrier; only its explicit semantic coherence conditions can still refuse a descriptor. -/
theorem authoritativeOccurrenceRule6FourWay_failureClassification_of_chemical_applicability
    {mol : RawMolecule} {state : OccurrenceAuxState} {center : Nat}
    (centerBound : center < mol.atomCount) (wellFormed : mol.WellFormed)
    (unique : mol.BondRecordsUnique) (valence : mol.ValenceOK)
    (kekule : AuthoritativeCIPMancudeTotality.LocalizedMancudeKekuleAdmissible mol)
    {occurrence : CanonicalBranchNode}
    (occurrenceGenerated : CanonicalCenterTreeNode mol center occurrence)
    (ligands sorted : List Nat) (parity : TetrahedralInputParity)
    (firstPresent : ∃ firstReference, sorted[0]? = some firstReference) :
    ∃ firstReference first second,
      sorted[0]? = some firstReference ∧
      authoritativeOccurrenceRule6PositionRankingBackend mol state
          (2 * mol.atomCount + 1) (occurrenceLigandCursors mol occurrence) ligands
          firstReference = some first ∧
      authoritativeOccurrenceRule6PositionRankingBackend mol state
          (2 * mol.atomCount + 1) (occurrenceLigandCursors mol occurrence) ligands
          (first.positions[1]?.getD 0) = some second ∧
      (authoritativeOccurrenceRule6FourWayDescriptor?
          (authoritativeOccurrenceRule6PositionRankingBackend mol state
            (2 * mol.atomCount + 1) (occurrenceLigandCursors mol occurrence) ligands)
          parity sorted = none ↔ HasFourWayCarrierFailure parity first second) := by
  apply authoritativeOccurrenceRule6FourWay_failureClassification_exists
  · exact firstPresent
  · intro reference
    exact authoritativeOccurrenceRule6PositionRankingBackend_total_of_chemical_applicability
      centerBound wellFormed unique valence kekule occurrenceGenerated ligands reference

end TetraStereo.OneCenter.AuthoritativeCIPRule6P92Enumeration
