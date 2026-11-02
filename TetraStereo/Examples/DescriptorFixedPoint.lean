import TetraStereo.OneCenter.DescriptorFixedPoint
import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo
namespace Examples
namespace DescriptorFixedPoint

open OneCenter











/-- A one-carbon molecule with no stereochemical annotation. -/
def nonstereogenicCarbon : RawMolecule where
  atoms := [AtomSpec.aliphatic Element.C]
  bonds := []

def nonstereogenicCarbonResult : ChemistryNormalizationResult :=
  normalizeRawMolecule nonstereogenicCarbon

/-- An unsupported provisional fact.  Its positive evidence size sends it through the production
recomputation branch rather than treating it as a final Rules-1--3 seed. -/
def unsupportedProvisionalFact : RawDescriptorFact where
  atom := 0
  descriptor := RS.R
  uppercase := false
  evidenceSize := 1

def unsupportedInitialState : RawDescriptorState :=
  [unsupportedProvisionalFact]

/-- View a raw descriptor list as the set of facts it asserts. -/
def assertedFacts (state : RawDescriptorState) : Set RawDescriptorFact :=
  { fact | fact ∈ state }

/-- The production pass retracts the unsupported provisional fact. -/
theorem unsupportedProvisionalFact_is_retracted :
    runRawDescriptorDiscoveryPass nonstereogenicCarbonResult
        nonstereogenicCarbonResult.parsed 100 2 unsupportedInitialState = [] := by
  decide

/-- Therefore the production pass is not inflationary on unrestricted `RawDescriptorState`.
This is the exact failed premise of `DescriptorClosureOperator`. -/
theorem rawDescriptorDiscoveryPass_not_inflationary :
    ¬ assertedFacts unsupportedInitialState ⊆
      assertedFacts
        (runRawDescriptorDiscoveryPass nonstereogenicCarbonResult
          nonstereogenicCarbonResult.parsed 100 2 unsupportedInitialState) := by
  intro included
  have initialMember : unsupportedProvisionalFact ∈ assertedFacts unsupportedInitialState := by
    simp [assertedFacts, unsupportedInitialState]
  have retained := included initialMember
  rw [unsupportedProvisionalFact_is_retracted] at retained
  simp [assertedFacts] at retained

/-- Retraction is not itself an oscillation: after removing the unsupported candidate, another
pass leaves the empty state unchanged. -/
theorem retractedState_is_fixed :
    runRawDescriptorDiscoveryPass nonstereogenicCarbonResult
        nonstereogenicCarbonResult.parsed 100 2
        (runRawDescriptorDiscoveryPass nonstereogenicCarbonResult
          nonstereogenicCarbonResult.parsed 100 2 unsupportedInitialState) =
      runRawDescriptorDiscoveryPass nonstereogenicCarbonResult
          nonstereogenicCarbonResult.parsed 100 2 unsupportedInitialState := by
  decide

/-- Exhausting the iteration budget is represented distinctly from stabilization. -/
theorem zeroBudget_is_not_stabilized :
    (discoverRawDescriptorsFromCertified nonstereogenicCarbonResult
      nonstereogenicCarbonResult.parsed 100 2 0 unsupportedInitialState).stabilized = false := by
  rfl

/-- With sufficient budget, the same provisional state is retracted and the certified iterator
records the resulting literal fixed point. -/
theorem unsupportedCandidate_certified_retraction :
    discoverRawDescriptorsFromCertified nonstereogenicCarbonResult
        nonstereogenicCarbonResult.parsed 100 2 2 unsupportedInitialState =
      { state := [], stabilized := true } := by
  decide

/-- The stabilization gate exposes the retracted state as its accepted result. -/
theorem unsupportedCandidate_stabilization_gate :
    stabilizedRawDescriptorState? nonstereogenicCarbonResult
        nonstereogenicCarbonResult.parsed 100 2 2 unsupportedInitialState = some [] := by
  decide

/-- Even though this orbit begins with a retraction, its accepted closure is the unique reachable
fixed point.  This is a closed kernel-checked instance of the production uniqueness theorem. -/
theorem unsupportedCandidate_has_unique_reachable_fixedPoint :
    ∃! candidate,
      IsReachableRawDescriptorFixedPoint nonstereogenicCarbonResult
        nonstereogenicCarbonResult.parsed 100 2 unsupportedInitialState candidate :=
  stabilizedRawDescriptorState_existsUnique_reachable_fixedPoint nonstereogenicCarbonResult
    nonstereogenicCarbonResult.parsed 100 2 2 unsupportedInitialState []
    unsupportedCandidate_stabilization_gate

/-- The production API exposes the general certification boundary proved by the chemistry engine. -/
theorem productionDescriptorBoundary_is_certified
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (fuel : ℕ) :
    ∃ source,
      discoverRawDescriptors result mol fuel =
          normalizeTwoCyclicRule6AnchorCarrier mol fuel source ∧
      IsCertifiedRawDescriptorSource result mol fuel source :=
  discoverRawDescriptors_certified result mol fuel

/-- The strengthened production API exposes uniqueness provenance for the source underlying every
reported descriptor list. -/
theorem productionDescriptorBoundary_is_unique
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (fuel : ℕ) :
    ∃ source,
      discoverRawDescriptors result mol fuel =
          normalizeTwoCyclicRule6AnchorCarrier mol fuel source ∧
        IsUniqueRawDescriptorSource result mol fuel source :=
  discoverRawDescriptors_unique result mol fuel

end DescriptorFixedPoint
end Examples
end TetraStereo
