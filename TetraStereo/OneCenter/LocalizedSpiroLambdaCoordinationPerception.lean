import TetraStereo.OneCenter.LocalizedSpiroCenterPerception
import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace BlueBookP93.Cyclic

/-- The three nonstandard-valence spiro coordination cases named in P-93.5.3.4. -/
def IsLambdaSpiroCoordination : SpiroCenterCoordination → Prop
  | .lambda4 | .lambda5 | .lambda6 => True
  | .tetrahedral => False

instance (coordination : SpiroCenterCoordination) :
    Decidable (IsLambdaSpiroCoordination coordination) := by
  cases coordination <;> simp [IsLambdaSpiroCoordination] <;> exact inferInstance

/-- Exact finite router from a bonding/coordination number to the P-93 lambda case. -/
def lambdaSpiroCoordinationOfNumber? (number : Nat) : Option SpiroCenterCoordination :=
  if number = 4 then some .lambda4
  else if number = 5 then some .lambda5
  else if number = 6 then some .lambda6
  else none

theorem lambdaSpiroCoordinationOfNumber?_eq_some_iff
    (number : Nat) (coordination : SpiroCenterCoordination) :
    lambdaSpiroCoordinationOfNumber? number = some coordination ↔
      IsLambdaSpiroCoordination coordination ∧
        coordination.number = number := by
  by_cases h4 : number = 4
  · subst number
    cases coordination <;> simp [lambdaSpiroCoordinationOfNumber?,
      IsLambdaSpiroCoordination, SpiroCenterCoordination.number]
  by_cases h5 : number = 5
  · subst number
    cases coordination <;> simp [lambdaSpiroCoordinationOfNumber?, h4,
      IsLambdaSpiroCoordination, SpiroCenterCoordination.number]
  by_cases h6 : number = 6
  · subst number
    cases coordination <;> simp [lambdaSpiroCoordinationOfNumber?, h4, h5,
      IsLambdaSpiroCoordination, SpiroCenterCoordination.number]
  cases coordination <;> simp [lambdaSpiroCoordinationOfNumber?, h4, h5, h6,
    IsLambdaSpiroCoordination, SpiroCenterCoordination.number, eq_comm]

theorem lambdaSpiroCoordinationOfNumber?_eq_none_iff (number : Nat) :
    lambdaSpiroCoordinationOfNumber? number = none ↔
      number ≠ 4 ∧ number ≠ 5 ∧ number ≠ 6 := by
  by_cases h4 : number = 4
  · simp [lambdaSpiroCoordinationOfNumber?, h4]
  by_cases h5 : number = 5
  · simp [lambdaSpiroCoordinationOfNumber?, h5]
  by_cases h6 : number = 6
  · simp [lambdaSpiroCoordinationOfNumber?, h6]
  simp [lambdaSpiroCoordinationOfNumber?, h4, h5, h6]

end BlueBookP93.Cyclic

namespace CertifiedLocalizedCIPInput

open BlueBookP93.Cyclic

/-- Sum of all positive localized pair-bond orders incident to one center.  On the current
localized graph this is the representation-independent bonding-number witness needed to keep a
mere neighbor count from masquerading as a lambda superscript. -/
noncomputable def localizedCenterIncidentBondOrderSum
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) : Nat :=
  ∑ neighbor ∈ input.moleculeGraph.neighborFinset center,
    input.moleculeGraph.bond center neighbor

/-- Public source-level carrier for a P-93 lambda-4, lambda-5, or lambda-6 spiro atom. -/
structure LocalizedLambdaSpiroCenter
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) where
  carrier : input.LocalizedSpiroCenter center
  coordination : SpiroCenterCoordination
  deriving DecidableEq

/-- Independent chemical/topological meaning of the lambda-spiro carrier.

The exhaustive two-cycle carrier supplies the spiro topology.  The atom must be a heteroatom,
the exact number of distinct positive-bond neighbors must be 4, 5, or 6, and the incident
pair-bond order sum must equal the same number.  The final equality rules out silently treating a
multiple bond as one lambda coordination site. -/
def DeclarativeLocalizedLambdaSpiroCenter
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (candidate : input.LocalizedLambdaSpiroCenter center) : Prop :=
  input.DeclarativeLocalizedSpiroCenter center candidate.carrier ∧
    (input.certified.input.molecule.atoms.get center).element.atomicNumber ≠ 6 ∧
    IsLambdaSpiroCoordination candidate.coordination ∧
    (input.moleculeGraph.neighborFinset center).card = candidate.coordination.number ∧
    input.localizedCenterIncidentBondOrderSum center = candidate.coordination.number

/-- Exhaustive source-level detector for the represented lambda-spiro domain. -/
noncomputable def localizedLambdaSpiroCenterAt?
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) :
    Option (input.LocalizedLambdaSpiroCenter center) := do
  let carrier ← input.localizedSpiroCenterAt? center
  if (input.certified.input.molecule.atoms.get center).element.atomicNumber ≠ 6 then
    let number := (input.moleculeGraph.neighborFinset center).card
    let coordination ← lambdaSpiroCoordinationOfNumber? number
    if input.localizedCenterIncidentBondOrderSum center = number then
      some { carrier, coordination }
    else none
  else none

/-- Perception succeeds exactly for the independent topology, heteroatom, coordination-number,
and bonding-number predicate. -/
theorem localizedLambdaSpiroCenterAt?_eq_some_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (candidate : input.LocalizedLambdaSpiroCenter center) :
    input.localizedLambdaSpiroCenterAt? center = some candidate ↔
      input.DeclarativeLocalizedLambdaSpiroCenter center candidate := by
  classical
  unfold localizedLambdaSpiroCenterAt?
  cases carrierEq : input.localizedSpiroCenterAt? center with
  | none =>
      constructor
      · simp
      · intro judged
        have carrierSome :=
          (input.localizedSpiroCenterAt?_eq_some_iff center candidate.carrier).mpr judged.1
        rw [carrierEq] at carrierSome
        contradiction
  | some carrier =>
      by_cases hetero :
          (input.certified.input.molecule.atoms.get center).element.atomicNumber ≠ 6
      · let number := (input.moleculeGraph.neighborFinset center).card
        cases coordinationEq : lambdaSpiroCoordinationOfNumber? number with
        | none =>
            constructor
            · simp [number, coordinationEq]
            · intro judged
              have numberEq : candidate.coordination.number = number := by
                simpa [number] using judged.2.2.2.1.symm
              have coordinationSome :=
                (lambdaSpiroCoordinationOfNumber?_eq_some_iff
                  number candidate.coordination).mpr ⟨judged.2.2.1, numberEq⟩
              rw [coordinationEq] at coordinationSome
              contradiction
        | some coordination =>
            by_cases bonding : input.localizedCenterIncidentBondOrderSum center = number
            · constructor
              · intro computed
                have candidateEq :
                    candidate = ({ carrier, coordination } :
                      input.LocalizedLambdaSpiroCenter center) := by
                  have facts :
                      (input.certified.input.molecule.atoms.get center).element.atomicNumber ≠ 6 ∧
                        candidate = ({ carrier, coordination } :
                          input.LocalizedLambdaSpiroCenter center) := by
                    simpa [carrierEq, number, coordinationEq, bonding] using computed.symm
                  exact facts.2
                subst candidate
                have carrierJudged :=
                  (input.localizedSpiroCenterAt?_eq_some_iff center carrier).mp carrierEq
                have coordinationFacts :=
                  (lambdaSpiroCoordinationOfNumber?_eq_some_iff number coordination).mp
                    coordinationEq
                exact ⟨carrierJudged, hetero, coordinationFacts.1,
                  by simpa [number] using coordinationFacts.2.symm,
                  bonding.trans coordinationFacts.2.symm⟩
              · intro judged
                have carrierSome :=
                  (input.localizedSpiroCenterAt?_eq_some_iff center candidate.carrier).mpr
                    judged.1
                rw [carrierEq] at carrierSome
                have carrierIdentity : candidate.carrier = carrier :=
                  (Option.some.inj carrierSome).symm
                have coordinationSome :=
                  (lambdaSpiroCoordinationOfNumber?_eq_some_iff
                    number candidate.coordination).mpr
                    ⟨judged.2.2.1, by simpa [number] using judged.2.2.2.1.symm⟩
                rw [coordinationEq] at coordinationSome
                have coordinationIdentity : candidate.coordination = coordination :=
                  (Option.some.inj coordinationSome).symm
                have candidateEq :
                    candidate = ({ carrier, coordination } :
                      input.LocalizedLambdaSpiroCenter center) := by
                  cases candidate with
                  | mk candidateCarrier candidateCoordination =>
                      simp only at carrierIdentity coordinationIdentity ⊢
                      subst candidateCarrier
                      subst candidateCoordination
                      rfl
                subst candidate
                simp [number, coordinationEq, bonding]
                exact hetero
            · constructor
              · simp [number, coordinationEq, bonding]
              · intro judged
                apply False.elim
                apply bonding
                exact judged.2.2.2.2.trans (by
                  simpa [number] using judged.2.2.2.1.symm)
      · constructor
        · intro computed
          simp at computed
          exact False.elim (hetero computed.1)
        · intro judged
          exact False.elim (hetero judged.2.1)

/-- Absence is exact: no independently valid lambda-spiro carrier exists at the atom. -/
theorem localizedLambdaSpiroCenterAt?_eq_none_iff
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) :
    input.localizedLambdaSpiroCenterAt? center = none ↔
      ∀ candidate, ¬input.DeclarativeLocalizedLambdaSpiroCenter center candidate := by
  constructor
  · intro none candidate judged
    have someEq :=
      (input.localizedLambdaSpiroCenterAt?_eq_some_iff center candidate).mpr judged
    rw [none] at someEq
    contradiction
  · intro absent
    cases computed : input.localizedLambdaSpiroCenterAt? center with
    | none => rfl
    | some candidate =>
        exact False.elim (absent candidate
          ((input.localizedLambdaSpiroCenterAt?_eq_some_iff center candidate).mp computed))

/-- The detector's independently valid result is unique. -/
theorem declarativeLocalizedLambdaSpiroCenter_subsingleton
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    {left right : input.LocalizedLambdaSpiroCenter center}
    (leftJudged : input.DeclarativeLocalizedLambdaSpiroCenter center left)
    (rightJudged : input.DeclarativeLocalizedLambdaSpiroCenter center right) :
    left = right := by
  have carrierEq := input.declarativeLocalizedSpiroCenter_subsingleton center
    leftJudged.1 rightJudged.1
  have numberEq : left.coordination.number = right.coordination.number :=
    leftJudged.2.2.2.1.symm.trans rightJudged.2.2.2.1
  have leftLambda := leftJudged.2.2.1
  have rightLambda := rightJudged.2.2.1
  cases left with
  | mk leftCarrier leftCoordination =>
      cases right with
      | mk rightCarrier rightCoordination =>
          simp only at carrierEq numberEq leftLambda rightLambda ⊢
          have coordinationEq : leftCoordination = rightCoordination := by
            cases leftCoordination <;> cases rightCoordination <;>
              simp [SpiroCenterCoordination.number, IsLambdaSpiroCoordination] at leftLambda rightLambda numberEq ⊢
          cases carrierEq
          cases coordinationEq
          rfl

/-- The two rings always contribute four donors.  Lambda-4 has no additional donor, lambda-5 has
one, and lambda-6 has two; the theorem states all three cases uniformly. -/
theorem DeclarativeLocalizedLambdaSpiroCenter.exists_ring_pair_and_external_donors
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (candidate : input.LocalizedLambdaSpiroCenter center)
    (judged : input.DeclarativeLocalizedLambdaSpiroCenter center candidate) :
    ∃ first second,
      first ≠ second ∧
      candidate.carrier.rings = {first, second} ∧
      (input.localizedCycleNeighbors first center ∪
          input.localizedCycleNeighbors second center).card = 4 ∧
      (input.moleculeGraph.neighborFinset center \
        (input.localizedCycleNeighbors first center ∪
          input.localizedCycleNeighbors second center)).card =
        candidate.coordination.number - 4 := by
  obtain ⟨first, second, distinct, ringsEq, branchCard⟩ :=
    judged.1.four_ring_branch_starts input center candidate.carrier
  have subset :
      input.localizedCycleNeighbors first center ∪
          input.localizedCycleNeighbors second center ⊆
        input.moleculeGraph.neighborFinset center := by
    intro atom present
    rcases Finset.mem_union.mp present with firstPresent | secondPresent
    · apply (input.moleculeGraph.mem_neighborFinset center atom).mpr
      exact (input.mem_localizedCycleNeighbors_iff first center atom).mp firstPresent |>.2
    · apply (input.moleculeGraph.mem_neighborFinset center atom).mpr
      exact (input.mem_localizedCycleNeighbors_iff second center atom).mp secondPresent |>.2
  refine ⟨first, second, distinct, ringsEq, branchCard, ?_⟩
  rw [Finset.card_sdiff_of_subset subset, judged.2.2.2.1, branchCard]

/-- Deterministic complete donor list used by later coordinate and IR-9 stages. -/
noncomputable def localizedLambdaSpiroDonors
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) : List input.Atom :=
  (input.moleculeGraph.neighborFinset center).toList

theorem localizedLambdaSpiroDonors_nodup
    (input : CertifiedLocalizedCIPInput) (center : input.Atom) :
    (input.localizedLambdaSpiroDonors center).Nodup :=
  (input.moleculeGraph.neighborFinset center).nodup_toList

theorem DeclarativeLocalizedLambdaSpiroCenter.donor_length
    (input : CertifiedLocalizedCIPInput) (center : input.Atom)
    (candidate : input.LocalizedLambdaSpiroCenter center)
    (judged : input.DeclarativeLocalizedLambdaSpiroCenter center candidate) :
    (input.localizedLambdaSpiroDonors center).length = candidate.coordination.number := by
  simpa [localizedLambdaSpiroDonors] using judged.2.2.2.1

@[simp] theorem mem_localizedLambdaSpiroDonors_iff
    (input : CertifiedLocalizedCIPInput) (center donor : input.Atom) :
    donor ∈ input.localizedLambdaSpiroDonors center ↔
      input.moleculeGraph.Adj center donor := by
  simp [localizedLambdaSpiroDonors, MoleculeGraph.mem_neighborFinset]

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
