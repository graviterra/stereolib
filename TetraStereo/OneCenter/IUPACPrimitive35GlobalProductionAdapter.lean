import TetraStereo.OneCenter.IUPACGlobalCompilerAssembly
import TetraStereo.OneCenter.IUPACPrimitive35Interpreter

set_option autoImplicit false

/-!
# Concrete primitive-35 production adapter for the global compiler

This module lifts the named `Primitive35AuthorityRow.ProductionJudges` implementation into the
global operation-projected corpus.  The reviewed reference is used only to transport the dependent
observation type and as the target of the existing production refinement theorem; it never defines
production.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

theorem Primitive35AuthorityRow.provision_mem_primitive35
    (row : Primitive35AuthorityRow) :
    row.provision ∈ primitive35Provisions := by
  cases row <;> try decide
  case p92Rule45 family => cases family <;> decide

theorem Primitive35AuthorityRow.descriptorAssignmentBearing
    (row : Primitive35AuthorityRow) :
    DescriptorAssignmentBearing row.provision := by
  apply descriptorBearingOfReviewedMember row.provision
  rw [List.mem_toFinset, descriptorBearingReviewedSemanticsSlice_exact]
  simp [reviewed81DescriptorBearingProvisions, row.provision_mem_primitive35]

theorem globalReviewedSemantics_primitive35_exact
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Primitive35AuthorityRow) :
    global.reviewed.row row.provision = row.semantics := by
  rw [global.descriptorBearing_exact row.descriptorAssignmentBearing]
  exact descriptorBearingReviewedSemantics_primitive35_exact policies row

/-- The global operation projection retains the exact primitive source reference. -/
theorem primitive35GlobalReference_eq
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Primitive35AuthorityRow) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision = row.reference := by
  change ((globalDescriptorAssignmentProjection global.toFrozenCorpus).reference
    row.provision).toReference = row.reference
  rw [DescriptorAssignmentProjection.descriptorBearing_exact
    (globalDescriptorAssignmentProjection global.toFrozenCorpus)
      row.provision row.descriptorAssignmentBearing]
  change (global.reviewed.row row.provision).reference = row.reference
  rw [globalReviewedSemantics_primitive35_exact global row]
  rfl

theorem primitive35GlobalReference_eq_of_member
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ primitive35Provisions) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference provision =
      (primitive35AuthorityRowOf provision member).reference := by
  let row := primitive35AuthorityRowOf provision member
  have rowProvision : row.provision = provision :=
    primitive35AuthorityRowOf_provision provision member
  calc
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference provision =
        (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
          row.provision := congrArg
            ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference)
            rowProvision.symm
    _ = row.reference := primitive35GlobalReference_eq global row
    _ = (primitive35AuthorityRowOf provision member).reference := rfl

/-- Named primitive production on the global observation type.  The only cast is forced by the
equality between the global source reference and the already reviewed primitive reference. -/
noncomputable def Primitive35AuthorityRow.GlobalProductionJudges
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Primitive35AuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision).Observation) : Prop :=
  row.ProductionJudges source
    (cast (congrArg ProvisionReference.Observation
      (primitive35GlobalReference_eq global row)) observation)

private theorem Primitive35AuthorityRow.productionJudges_congr
    (left right : Primitive35AuthorityRow)
    (provisionEq : left.provision = right.provision)
    (source : AuthoritativeChemicalInput)
    {leftObservation : left.reference.Observation}
    {rightObservation : right.reference.Observation}
    (observationEq : HEq leftObservation rightObservation) :
    left.ProductionJudges source leftObservation ↔
      right.ProductionJudges source rightObservation := by
  have rowEq : left = right := Primitive35AuthorityRow.provision_injective provisionEq
  subst right
  have observationEq' : leftObservation = rightObservation := eq_of_heq observationEq
  subst rightObservation
  rfl

/-- Concrete total interpreter whose primitive branch is real production.  The `False` branch is
an explicit extension point for the independently implemented next-54 and remaining-71 adapters;
no correctness claim is made for that branch here. -/
noncomputable def primitive35GlobalInterpreter
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative) :
    ProvisionInterpreter
      (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus where
  Produces := fun provision source observation =>
    if member : provision ∈ primitive35Provisions then
      let row := primitive35AuthorityRowOf provision member
      let referenceEq := primitive35GlobalReference_eq_of_member global provision member
      row.ProductionJudges source
        (cast (congrArg ProvisionReference.Observation referenceEq) observation)
    else False

@[simp] theorem primitive35GlobalInterpreter_exact
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Primitive35AuthorityRow)
    (source : AuthoritativeChemicalInput)
    (observation : ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision).Observation) :
    (primitive35GlobalInterpreter global).Produces row.provision source observation ↔
      row.GlobalProductionJudges global source observation := by
  have member := row.provision_mem_primitive35
  simp only [primitive35GlobalInterpreter]
  rw [dif_pos member]
  change (primitive35AuthorityRowOf row.provision member).ProductionJudges source
      (cast (congrArg ProvisionReference.Observation
        (primitive35GlobalReference_eq_of_member global row.provision member)) observation) ↔
    row.ProductionJudges source
      (cast (congrArg ProvisionReference.Observation
        (primitive35GlobalReference_eq global row)) observation)
  apply Primitive35AuthorityRow.productionJudges_congr
    (primitive35AuthorityRowOf row.provision member) row
    (primitive35AuthorityRowOf_provision row.provision member) source
  exact (cast_heq _ observation).trans (cast_heq _ observation).symm

/-- One existing concrete refinement family now discharges the primitive-35 field of the global
positive production boundary. -/
theorem primitive35GlobalProduction_correct
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Primitive35AuthorityRow) :
    ProvisionCorrect (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus
      (primitive35GlobalInterpreter global) row.provision := by
  intro source _admitted observation
  let referenceEq := primitive35GlobalReference_eq global row
  let rowObservation : row.reference.Observation :=
    cast (congrArg ProvisionReference.Observation referenceEq) observation
  have exactJudgment := row.production_eq_reference source rowObservation
  have applicableTransport := ProvisionReference.applicable_congr referenceEq source
  have judgmentTransport :=
    ProvisionReference.judges_cast_congr referenceEq source observation
  rw [primitive35GlobalInterpreter_exact global row source observation]
  change row.ProductionJudges source rowObservation ↔
    ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision).Applicable source ∧
      ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
        row.provision).Judges source observation
  constructor
  · intro produced
    have rowJudged := exactJudgment.mp produced
    exact ⟨applicableTransport.mpr
        (row.reference_applicable_of_judged source rowObservation rowJudged),
      judgmentTransport.mpr rowJudged⟩
  · rintro ⟨_applicable, judged⟩
    exact exactJudgment.mpr (judgmentTransport.mp judged)

/-- The global compiler receives the whole Rules-4b/5 family through the single dependent family
adapter.  Every family member is a typed projection of `primitive35GlobalProduction_correct`; no
row-specific global correctness proof is authored here. -/
theorem rule45PrimitiveFamily_globalProduction_correct
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (family : Rule45CanonicalProvisionFamily) :
    ProvisionCorrect (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus
      (primitive35GlobalInterpreter global) family.provision := by
  simpa using primitive35GlobalProduction_correct global (.p92Rule45 family)

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35GlobalReference_eq
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35GlobalInterpreter_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.primitive35GlobalProduction_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.rule45PrimitiveFamily_globalProduction_correct
