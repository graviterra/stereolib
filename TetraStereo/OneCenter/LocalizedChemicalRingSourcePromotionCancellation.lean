import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedPromotionCancellation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Fail-closed promotion cancellation stated on independent molecular source keys.
The source operator distinguishes missing frame/readback data from a completed nonunique
promotion. On the physical auxiliary branch domain, every solution of the independent source
equations satisfies this cancellation prescription exactly, on both geometry sides and every
accumulated reference context. Actual population transport and refusal reconstruction discharge
the cancellation-versus-consensus premise. Published applicability and the status of auxiliary
recalculation are not inferred from this aggregation result.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionCancellation

open CertifiedLocalizedCIPInput
open DeclarativeCIP.ProductionOccurrenceRules456
open LocalizedChemicalRingJointPreparedSourceStep
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence
open LocalizedChemicalRingJointPreparedSourceQueries (SourceQuery)
open LocalizedChemicalRingJointPreparedSourceQueryMap (generated_map_eq_sourceQueryMap)
open LocalizedChemicalRingJointPreparedPromotionOutcomes
open LocalizedChemicalRingJointPreparedPromotionCancellation (actualAggregate_eq_step_of_tied)
open LocalizedChemicalRingJointPreparedExecution (keys step)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData observedGeometry referenceAt rank)
open LocalizedChemicalRingSelectedRefusalWitness (TiedRootBranch)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedGenericMarkedRecalculation (Geometry mirror structuralDepth caseFromMirror?)
open LocalizedMarkedRetainedMolecularSelection (retainedCarrierFuel)
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (single : input.moleculeGraph.SimpleBonded)

/-- A single promotion on the independent source frame, with operational failure kept distinct. -/
def sourcePromotionOutcome (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) (slot : Fin 4) : PromotionOutcome :=
  match frameAtom? input frame slot with
  | none => .operationalFailure
  | some reference =>
    if Function.Injective (sourceKeysAt input single family target frame geom
        (references ++ [reference])) then
      match sourceFallback input single family target frame geom references slot with
      | none => .operationalFailure
      | some descriptor => .descriptor descriptor
    else .unresolved

def sourcePromotionOutcomes (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) : List PromotionOutcome :=
  (sourceSelectedSlots (sourceKeysAt input single family target frame geom references)).map
    (sourcePromotionOutcome input single family target frame geom references)

/-- Strict geometric reading, or fail-closed cancellation of all selected source promotions. -/
def sourceCancellationStep (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) : Option (Option RS) :=
  if Function.Injective (sourceKeysAt input single family target frame geom references) then
    (sourceReading input geom frame (sourceKeysAt input single family target frame geom references)).map some
  else promotionAggregate (sourcePromotionOutcomes input single family target frame geom references)

def sourceCancellationDescriptor (family : DescriptorFamily input)
    (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
    (frame : input.LocalizedOccurrenceFourLigandFrame (retainedCarrierFuel input))
    (geom : Geometry) (references : List input.Atom) :
    Option (Option LocalizedTetrahedralRSPseudoDescriptor) := do
  let first ← sourceCancellationStep input single family target frame geom references
  let second ← sourceCancellationStep input single family target frame (mirror geom) references
  pure (caseFromMirror? first second)

variable (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)

include agreement admissible supported in
theorem sourcePromotionOutcome_eq_actual
    (center : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol center node) (depth : Nat)
    (references : List input.Atom) (reflected : Bool) (slot : Fin 4) :
    sourcePromotionOutcome input single (generatedFamily input mol depth node)
      data.target data.frame (observedGeometry input reflected) references slot =
      promotionOutcomeAt input mol single center node data depth references reflected slot := by
  unfold sourcePromotionOutcome
  rw [frameAtom_eq_referenceAt input mol center node data slot]
  dsimp only
  have injectivity := keys_injective_iff input mol single center node data depth
    (observedGeometry input reflected) (references ++ [referenceAt input mol center node data slot])
  have reading := fallback_eq_source input mol single center node data depth agreement admissible
    supported (observedGeometry input reflected) references slot
  unfold promotionOutcomeAt
  by_cases injective : Function.Injective (keys input mol single center node data depth
      (observedGeometry input reflected) (references ++ [referenceAt input mol center node data slot]))
  · rw [if_pos injective, if_pos (injectivity.mp injective), ← reading]
    rfl
  · rw [if_neg injective, if_neg (fun h => injective (injectivity.mpr h))]

include agreement admissible supported in
theorem sourcePromotionOutcomes_eq_actual
    (center : input.detectedMultiCenterMolecule.Center) (node : RawMolecule.CanonicalBranchNode)
    (data : OccurrenceData input mol center node) (depth : Nat)
    (references : List input.Atom) (reflected : Bool) :
    sourcePromotionOutcomes input single (generatedFamily input mol depth node)
      data.target data.frame (observedGeometry input reflected) references =
      actualOutcomes input mol single center node data depth references reflected := by
  unfold sourcePromotionOutcomes actualOutcomes
  rw [selectedSlots_source_eq input mol single center node data depth]
  apply List.map_congr_left
  intro slot _
  exact sourcePromotionOutcome_eq_actual input single mol agreement admissible supported
    center node data depth references reflected slot

include agreement admissible supported in
/-- The independent solution supplies exactly the actually generated family at each query. -/
theorem sourceModel_family_eq_generated {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol) :
    profileFamily input mol candidate query =
      generatedFamily input mol (structuralDepth mol query.1) query.1 := by
  rw [sourceModel_eq_actual input mol agreement admissible supported single model]
  have endpoints : LocalizedGenericMarkedRecalculation.WellFormedBonds mol := fun bond member =>
    ⟨(admissible.1.1 bond member).1, (admissible.1.1 bond member).2.1⟩
  funext geom references
  exact (generated_map_eq_sourceQueryMap input mol endpoints geom references query).symm

variable (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported charge calibrated in
/-- Source cancellation equals the original independent raw prescription, with no strictness,
obstruction, population-balance or desired-label premise. Both source branches are covered. -/
theorem sourceCancellationStep_eq_sourceStep {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (center : input.detectedMultiCenterMolecule.Center) (current : query.1.atom = center.1.val)
    (data : OccurrenceData input mol center query.1) (branch : TiedRootBranch input data.target)
    (boundary references : List input.Atom)
    (history : data.target.1.node.history.reverse = boundary ++ [center.1])
    (outside : center.1 ∉ boundary) (reflected : Bool) :
    sourceCancellationStep input single (profileFamily input mol candidate query)
      data.target data.frame (observedGeometry input reflected) references =
      some (sourceStep input single (profileFamily input mol candidate query)
        data.target data.frame (observedGeometry input reflected) references) := by
  rw [sourceModel_family_eq_generated input single mol agreement admissible supported model query]
  rw [← step_eq_source input mol single center query.1 data (structuralDepth mol query.1)
    agreement admissible supported (observedGeometry input reflected) references]
  unfold sourceCancellationStep
  have injectivity := keys_injective_iff input mol single center query.1 data
    (structuralDepth mol query.1) (observedGeometry input reflected) references
  by_cases injective : Function.Injective (keys input mol single center query.1 data
      (structuralDepth mol query.1) (observedGeometry input reflected) references)
  · rw [if_pos (injectivity.mp injective), sourceReading_eq_enumeration,
      LocalizedChemicalRingJointPreparedExecution.step_eq input mol agreement admissible supported
        single center query.1 data, if_pos injective]
    obtain ⟨descriptor, read⟩ := LocalizedChemicalRingInheritedRefusalCases.readback_some input cfg center
      (calibrated center) reflected (rank input mol center query.1 data
        (keys input mol single center query.1 data (structuralDepth mol query.1)
          (observedGeometry input reflected) references))
    rw [read]
    rfl
  · rw [if_neg (fun h => injective (injectivity.mpr h)),
      sourcePromotionOutcomes_eq_actual input single mol agreement admissible supported]
    exact actualAggregate_eq_step_of_tied input mol agreement admissible supported single charge cfg
      calibrated center query.1 data query.2.1 query.2.2.1 current branch boundary references history
      outside reflected injective

include agreement admissible supported charge calibrated in
/-- The unique independent recursive meaning satisfies fail-closed cancellation on both
geometry sides at every physical auxiliary query in scope, with the exact same descriptor. -/
theorem sourceModel_cancellation_equation {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (query : SourceQuery input mol)
    (center : input.detectedMultiCenterMolecule.Center) (current : query.1.atom = center.1.val)
    (data : OccurrenceData input mol center query.1) (branch : TiedRootBranch input data.target)
    (boundary references : List input.Atom)
    (history : data.target.1.node.history.reverse = boundary ++ [center.1])
    (outside : center.1 ∉ boundary) :
    sourceCancellationDescriptor input single (profileFamily input mol candidate query)
      data.target data.frame (inputGeometry input) references =
      some (candidate (inputGeometry input) references query) := by
  have first := sourceCancellationStep_eq_sourceStep input single mol agreement admissible supported
    charge cfg calibrated model query center current data branch boundary references history outside false
  have second := sourceCancellationStep_eq_sourceStep input single mol agreement admissible supported
    charge cfg calibrated model query center current data branch boundary references history outside true
  change sourceCancellationStep input single (profileFamily input mol candidate query)
    data.target data.frame (inputGeometry input) references = _ at first
  change sourceCancellationStep input single (profileFamily input mol candidate query)
    data.target data.frame (mirror (inputGeometry input)) references = _ at second
  unfold sourceCancellationDescriptor
  rw [first, second]
  exact congrArg some (model (inputGeometry input) references query center data)

end
end TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionCancellation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionCancellation.sourcePromotionOutcome_eq_actual
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionCancellation.sourcePromotionOutcomes_eq_actual
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionCancellation.sourceModel_family_eq_generated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionCancellation.sourceCancellationStep_eq_sourceStep
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionCancellation.sourceModel_cancellation_equation

assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingSourcePromotionCancellation.sourceCancellationDescriptor
  [TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueryMap.actualQueryProfile,
   TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.generated,
   TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedDescriptor?]
