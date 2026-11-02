import TetraStereo.OneCenter.ProductionRule6Certificate

set_option autoImplicit false

namespace TetraStereo.OneCenter.Rule6FourWayFamilySemantics

/-!
# Exact semantics of the four-way Rule-6 carrier

The four-way production branch runs two dependent promoted rankings and then checks three facts.
This module separates those facts from the control flow.  Once the two rankings exist, success is
exactly coherence of their carrier orders, descriptors, and uniqueness status; failure is exactly
one of the three corresponding explicit witnesses.
-/

open RawMolecule

/-- The three semantic agreement conditions required by the four-way carrier. -/
def FourWayCarrierCoherent (parity : TetrahedralInputParity)
    (first second : Rule6TrackedRanking) : Prop :=
  first.positions ≠ second.positions ∧
    RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven first.positions) =
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven second.positions) ∧
    first.unique = second.unique

/-- Every possible semantic reason for rejecting two completed four-way rankings. -/
def HasFourWayCarrierFailure (parity : TetrahedralInputParity)
    (first second : Rule6TrackedRanking) : Prop :=
  first.positions = second.positions ∨
    RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven first.positions) ≠
      RawMolecule.descriptorOfParity parity
        (RawMolecule.permutationIsEven second.positions) ∨
    first.unique ≠ second.unique

/-- Coherence failure has exactly the three explicit witness forms above. -/
theorem not_fourWayCarrierCoherent_iff_failure
    (parity : TetrahedralInputParity) (first second : Rule6TrackedRanking) :
    ¬ FourWayCarrierCoherent parity first second ↔
      HasFourWayCarrierFailure parity first second := by
  unfold FourWayCarrierCoherent HasFourWayCarrierFailure
  tauto

/-- Pure evaluation of the three four-way agreement conditions after both rankings exist. -/
def evaluateFourWayCarrier? (parity : TetrahedralInputParity)
    (first second : Rule6TrackedRanking) : Option Rule6FourWayAgreement :=
  let firstDescriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven first.positions)
  let secondDescriptor := RawMolecule.descriptorOfParity parity
    (RawMolecule.permutationIsEven second.positions)
  if first.positions != second.positions && firstDescriptor == secondDescriptor &&
      first.unique == second.unique then
    some
      { firstRanking := first
        secondRanking := second
        descriptor := if second.unique then secondDescriptor else RS.swap secondDescriptor }
  else none

/-- The pure evaluator fails exactly when the semantic coherence proposition fails. -/
theorem evaluateFourWayCarrier?_eq_none_iff_not_coherent
    (parity : TetrahedralInputParity) (first second : Rule6TrackedRanking) :
    evaluateFourWayCarrier? parity first second = none ↔
      ¬ FourWayCarrierCoherent parity first second := by
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

/-- Equivalent explicit-witness form of pure four-way failure. -/
theorem evaluateFourWayCarrier?_eq_none_iff_failure
    (parity : TetrahedralInputParity) (first second : Rule6TrackedRanking) :
    evaluateFourWayCarrier? parity first second = none ↔
      HasFourWayCarrierFailure parity first second :=
  (evaluateFourWayCarrier?_eq_none_iff_not_coherent parity first second).trans
    (not_fourWayCarrierCoherent_iff_failure parity first second)

end TetraStereo.OneCenter.Rule6FourWayFamilySemantics
