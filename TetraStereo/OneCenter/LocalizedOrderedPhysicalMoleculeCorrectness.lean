import TetraStereo.OneCenter.LocalizedOrderedPhysicalMoleculeTotality
import TetraStereo.OneCenter.LocalizedActualOrderedRootOwnMap
import TetraStereo.OneCenter.LocalizedRigidFinalDeclarativeDescriptor
import TetraStereo.OneCenter.LocalizedTerminalTwinDeclarativeRefusal
import TetraStereo.OneCenter.DeclarativeCIPFinalTetrahedralOutcome
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# General whole-molecule final-report correctness

The callable ordered report is characterized by an independent eight-rule assignment
relation using its own generated auxiliary descriptor map. This theorem covers every
detected centre of an arbitrary-size molecule in `OrderedTreePhysicalDomain`.
Missing entries mean absence of any declarative descriptor judgment, not an assumed
runtime failure. This is a theorem about all final molecular centres; it does not
assert `CIPSpec` at every auxiliary occurrence or cover rings.
-/

namespace TetraStereo.OneCenter
open CertifiedLocalizedCIPInput DeclarativeCIP
open Rule4aTableBridge.ActualCentrePhysicalSetup

noncomputable section
namespace OrderedTreePhysicalDomain
variable {input : LocalizedUniversalReference.Input}
  {cfg : input.certified.detectedMultiCenterMolecule.Configuration}
  {root : input.certified.detectedMultiCenterMolecule.Center}
  (domain : OrderedTreePhysicalDomain input cfg root)
include domain

/-- At the distinguished centre the actual ordered state has a unique independent assignment,
with all auxiliary readings taken from that same ordered evaluator. -/
theorem root_own_assignment :
    ∃ label : LocalizedAuxiliaryLabel,
      input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
          (ActualReaderPhysicalBranchInverse.topTarget input root) = some label ∧
      FinalTetrahedralAssignment (geoProblem (input := input))
        (actualOrderedReferenceDescriptorMap input) (input.certified.topUnit domain.rootCenter) label ∧
      ∀ other, FinalTetrahedralAssignment (geoProblem (input := input))
        (actualOrderedReferenceDescriptorMap input) (input.certified.topUnit domain.rootCenter) other →
          other = label := by
  obtain ⟨rs, state, judgment, unique⟩ :=
    domain.setup.orderedReferenceState_top_descriptorJudgment_ownMap
      domain.rootDistinct domain.rootCoordinates
  let label := classifyTetrahedralRSPseudo rs
    (finalRule5PairCount (geoProblem (input := input)) (actualOrderedReferenceDescriptorMap input)
      (input.certified.topUnit domain.rootCenter))
  have assigned : FinalTetrahedralAssignment (geoProblem (input := input))
      (actualOrderedReferenceDescriptorMap input) (input.certified.topUnit domain.rootCenter) label :=
    ⟨rs, judgment, rfl⟩
  have uniqueLabel := finalTetrahedralAssignment_existsUnique (geoProblem (input := input))
    (actualOrderedReferenceDescriptorMap input) (input.certified.topUnit domain.rootCenter)
    rs judgment unique
  refine ⟨label, ?_, assigned, fun other h => uniqueLabel.unique h assigned⟩
  exact (orderedReferenceStateAt_eq_pipelineState input
    (ActualReaderPhysicalBranchInverse.topTarget input root)).trans state

/-- Every actual final occurrence has exactly the independent optional eight-rule outcome.
Neither evaluator success nor comparison strictness is a hypothesis. -/
theorem final_outcome_iff (center : input.certified.TetrahedralCenter)
    (outcome : Option LocalizedAuxiliaryLabel) :
    input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
        (input.certified.localizedFinalOccurrenceExecutable
          (LocalizedUniversalReference.carrierFuel input) center) = outcome ↔
      FinalTetrahedralOutcome (geoProblem (input := input))
        (actualOrderedReferenceDescriptorMap input) (input.certified.topUnit center) outcome := by
  classical
  by_cases atRoot : (⟨center.1, center.2⟩ :
      input.certified.detectedMultiCenterMolecule.Center) = root
  · have centerEq : center = domain.rootCenter := Subtype.ext (congrArg Subtype.val atRoot)
    rw [centerEq, input.certified.localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence]
    obtain ⟨label, state, assigned, unique⟩ := domain.root_own_assignment
    change input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
      (ActualReaderPhysicalBranchInverse.topTarget input root) = outcome ↔ _
    rw [state]
    have specification := finalOutcome_iff_some_of_unique_assignment
      (geoProblem (input := input)) (actualOrderedReferenceDescriptorMap input)
      (input.certified.topUnit domain.rootCenter) label assigned unique outcome
    exact ⟨fun equality => specification.mpr equality.symm,
      fun correct => (specification.mp correct).symm⟩
  · rcases domain.centers.centerCase ⟨center.1, center.2⟩ atRoot with twin | calibrated
    · have state := domain.terminalTwin_final_none center twin
      have absent := terminalTwin_top_no_descriptorJudgment input domain.singleBonded
        domain.acyclic center twin (actualOrderedReferenceDescriptorMap input)
      rw [state]
      have specification := finalOutcome_iff_none_of_no_judgment
        (geoProblem (input := input)) (actualOrderedReferenceDescriptorMap input)
        (input.certified.topUnit center) absent outcome
      exact ⟨fun equality => specification.mpr equality.symm,
        fun correct => (specification.mp correct).symm⟩
    · obtain ⟨rs, state, assigned, _count, unique⟩ :=
        orderedTop_finalTetrahedralAssignment_of_physicalCalibratedCenter input
          domain.singleBonded domain.acyclic domain.constantCharge cfg
          ⟨center.1, center.2⟩ calibrated (actualOrderedReferenceDescriptorMap input)
      rw [input.certified.localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence]
      change input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
        (ActualReaderPhysicalBranchInverse.topTarget input ⟨center.1, center.2⟩) = outcome ↔ _
      rw [state]
      have specification := finalOutcome_iff_some_of_unique_assignment
        (geoProblem (input := input)) (actualOrderedReferenceDescriptorMap input)
        (input.certified.topUnit center) (.chiral rs) assigned unique outcome
      exact ⟨fun equality => specification.mpr equality.symm,
        fun correct => (specification.mp correct).symm⟩

/-- Independent failure of a complete descriptor ranking is exactly the supported physical
terminal-twin symmetry; it is not caused by an execution bound or a missing comparison proof. -/
theorem independent_refusal_iff_terminalTwin (center : input.certified.TetrahedralCenter) :
    (¬ ∃ descriptor, (geoProblem (input := input)).DescriptorJudgment
      (actualOrderedReferenceDescriptorMap input) (input.certified.topUnit center) descriptor) ↔
      ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule ⟨center.1, center.2⟩ :=
  (domain.final_outcome_iff center none).symm.trans (domain.final_none_iff_terminalTwin center)

/-- The actual executable report includes precisely the detected centres' independent outcomes. -/
theorem mem_report_iff (atom : Nat) (outcome : Option LocalizedAuxiliaryLabel) :
    (atom, outcome) ∈ LocalizedOrderedReference.analyze input ↔
      ∃ center : input.certified.TetrahedralCenter, center.1.1 = atom ∧
        FinalTetrahedralOutcome (geoProblem (input := input))
          (actualOrderedReferenceDescriptorMap input) (input.certified.topUnit center) outcome := by
  rw [LocalizedOrderedReference.mem_analyze_iff]
  constructor
  · rintro ⟨center, index, state⟩
    exact ⟨center, index, (domain.final_outcome_iff center outcome).mp state⟩
  · rintro ⟨center, index, correct⟩
    exact ⟨center, index, (domain.final_outcome_iff center outcome).mpr correct⟩

/-- Every detected centre has a unique independent optional outcome and appears in the report.
A terminal-twin centre's unique outcome is `none`; every other centre has a descriptor. -/
theorem final_outcome_existsUnique (center : input.certified.TetrahedralCenter) :
    ∃! outcome, FinalTetrahedralOutcome (geoProblem (input := input))
      (actualOrderedReferenceDescriptorMap input) (input.certified.topUnit center) outcome := by
  let result := input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input)
    (input.certified.localizedFinalOccurrenceExecutable
      (LocalizedUniversalReference.carrierFuel input) center)
  refine ⟨result, (domain.final_outcome_iff center result).mp rfl, ?_⟩
  intro other correct
  exact ((domain.final_outcome_iff center other).mpr correct).symm

/-- The generated auxiliary map itself satisfies the independent final-outcome relation at
every top molecular unit. This is restricted to final units, rather than all auxiliary contexts. -/
theorem ownMap_top_satisfies (center : input.certified.TetrahedralCenter) :
    FinalTetrahedralOutcome (geoProblem (input := input))
      (actualOrderedReferenceDescriptorMap input) (input.certified.topUnit center)
      ((actualOrderedReferenceDescriptorMap input (input.certified.topUnit center)).bind
        Descriptor.toLocalizedLabel) := by
  let c : input.certified.detectedMultiCenterMolecule.Center := ⟨center.1, center.2⟩
  have unitEq : input.certified.molecularFrameUnit
      (ActualReaderPhysicalBranchInverse.topTarget input c).1 =
        (input.certified.topUnit center).1 := by
    unfold molecularFrameUnit
    rw [ActualReaderPhysicalBranchInverse.topTarget_root,
      ActualReaderPhysicalBranchInverse.topTarget_node]
    rfl
  have readback := actualOrderedReferenceDescriptorMap_readback input domain.singleBonded
    domain.acyclic (input.certified.topUnit center)
    (ActualReaderPhysicalBranchInverse.topTarget input c) unitEq
  apply (domain.final_outcome_iff center _).mp
  rw [input.certified.localizedFinalOccurrenceExecutable_eq_localizedFinalOccurrence, readback]
  exact orderedReferenceStateAt_eq_pipelineState input
    (ActualReaderPhysicalBranchInverse.topTarget input c)

/-- General report endpoint: actual inventory, no duplicate centres, and exact independent
semantics of every present or absent assignment. -/
theorem complete_report :
    (LocalizedOrderedReference.analyze input).map Prod.fst =
        input.certified.canonicalTetrahedralCenters.map (fun center => center.1.1) ∧
    ((LocalizedOrderedReference.analyze input).map Prod.fst).Nodup ∧
    (LocalizedOrderedReference.analyze input).length = input.certified.tetrahedralCenterSet.card ∧
    ∀ atom outcome, (atom, outcome) ∈ LocalizedOrderedReference.analyze input ↔
      ∃ center : input.certified.TetrahedralCenter, center.1.1 = atom ∧
        FinalTetrahedralOutcome (geoProblem (input := input))
          (actualOrderedReferenceDescriptorMap input) (input.certified.topUnit center) outcome :=
  ⟨LocalizedOrderedReference.analyze_center_indices input,
    LocalizedOrderedReference.analyze_indices_nodup input,
    LocalizedOrderedReference.analyze_length input, domain.mem_report_iff⟩

end OrderedTreePhysicalDomain
end
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.root_own_assignment
assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.final_outcome_iff
assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.independent_refusal_iff_terminalTwin
assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.mem_report_iff
assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.final_outcome_existsUnique
assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.ownMap_top_satisfies
assert_kernel_only TetraStereo.OneCenter.OrderedTreePhysicalDomain.complete_report
