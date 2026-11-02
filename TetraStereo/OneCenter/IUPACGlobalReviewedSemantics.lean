import TetraStereo.OneCenter.IUPACDescriptorBearingReviewedSemantics
import TetraStereo.OneCenter.IUPACGlobalNegativeClosure

set_option autoImplicit false

/-!
# Exact global reviewed-semantics join

This module joins the independently reviewed 152-row descriptor-bearing table to an explicit
reviewed source table for the 2,300-row descriptor-assignment-negative region.  The negative
input remains source-owned: it cannot be replaced by the empty operational projection used to
prove descriptor assignment inapplicable.

The result is one total 2,452-row reviewed table and its literally induced frozen corpus.  Both
branches are selected by the exhaustive descriptor-assignment partition, and branch-equality
theorems make the absence of a fallback observable.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-- Candidate source-meaning program supplied at the operationally negative trust boundary.
Authority presence is source-owned: present rules carry a nonvacuous admitted judgment, while
genuinely absent rules carry admitted-domain inapplicability. The operation index is always
`sourceMeaning`, never `descriptorAssignment`, so neither branch can be confused with the empty
operational projection. This structure alone does not prove transcription faithfulness; the
canonical frozen program still has to be generated and sealed from audited source data. -/
structure GlobalNonDescriptorSourceReferenceProgram where
  sourceSuppliesRule : (provision : IUPACNormativeProvision) →
    provision ∈ globalNonDescriptorProvisions.toFinset → Bool
  reference : (provision : IUPACNormativeProvision) →
    provision ∈ globalNonDescriptorProvisions.toFinset →
      OperationProvisionReference .sourceMeaning
  sourcePresent_nonvacuous : ∀ (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset),
      sourceSuppliesRule provision member = true →
      ∃ input, ∃ observation : ((reference provision member).toReference).Observation,
        AuthoritativeChemicalInput.StructurallyWellFormed input ∧
          ((reference provision member).toReference).Applicable input ∧
            ((reference provision member).toReference).Judges input observation
  sourceAbsent_inapplicable : ∀ (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset),
      sourceSuppliesRule provision member = false →
        ∀ input, AuthoritativeChemicalInput.StructurallyWellFormed input →
          ¬((reference provision member).toReference).Applicable input

namespace GlobalNonDescriptorSourceReferenceProgram

theorem reference_ne_nonDescriptorAssignment
    (program : GlobalNonDescriptorSourceReferenceProgram)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset)
    (sourcePresent : program.sourceSuppliesRule provision member = true) :
    (program.reference provision member).toReference ≠
      nonDescriptorAssignmentReference.toReference := by
  intro erased
  rcases program.sourcePresent_nonvacuous provision member sourcePresent with
    ⟨input, observation, _admitted, applicable, _judges⟩
  have emptyApplicable :
      nonDescriptorAssignmentReference.toReference.Applicable input := by
    rw [← erased]
    exact applicable
  simp [nonDescriptorAssignmentReference] at emptyApplicable

end GlobalNonDescriptorSourceReferenceProgram

/-- The remaining source-transcription boundary for the 2,300 operationally negative rows.
Every reviewed row copies both authority presence and its reference from the separately typed
source program even though its descriptor-assignment projection is empty. -/
structure GlobalNonDescriptorReviewedSemantics where
  sourceProgram : GlobalNonDescriptorSourceReferenceProgram
  reviewed : ReviewedProvisionBatch globalNonDescriptorProvisions.toFinset
  admitted_exact : ∀ input : AuthoritativeChemicalInput,
    reviewed.ChemicallyAdmitted input ↔
      AuthoritativeChemicalInput.StructurallyWellFormed input
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ globalNonDescriptorProvisions.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision
  source_presence_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ globalNonDescriptorProvisions.toFinset),
      (reviewed.row provision member).sourceSuppliesRule =
        sourceProgram.sourceSuppliesRule provision member
  reference_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ globalNonDescriptorProvisions.toFinset),
      (reviewed.row provision member).reference =
        (sourceProgram.reference provision member).toReference

namespace GlobalNonDescriptorSourceReferenceProgram







def toReviewedSemantics
    (program : GlobalNonDescriptorSourceReferenceProgram)
    (sourceAudited : ∀ (provision : IUPACNormativeProvision)
      (_member : provision ∈ globalNonDescriptorProvisions.toFinset),
        IUPACNormativeSource.ProvisionAuditComplete provision.source) :
    GlobalNonDescriptorReviewedSemantics where
  sourceProgram := program
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        { kind := globalProvisionKind provision
          sourceSuppliesRule := program.sourceSuppliesRule provision member
          reference := (program.reference provision member).toReference }
      sourceAudited := fun {provision} member => sourceAudited provision member }
  admitted_exact := by
    intro input
    rfl
  classifier_exact := by
    intro provision member
    rfl
  source_presence_exact := by
    intro provision member
    rfl
  reference_exact := by
    intro provision member
    rfl

@[simp] theorem toReviewedSemantics_sourceProgram
    (program : GlobalNonDescriptorSourceReferenceProgram)
    (sourceAudited : ∀ (provision : IUPACNormativeProvision)
      (_member : provision ∈ globalNonDescriptorProvisions.toFinset),
        IUPACNormativeSource.ProvisionAuditComplete provision.source) :
    (program.toReviewedSemantics sourceAudited).sourceProgram = program :=
  rfl

@[simp] theorem toReviewedSemantics_admitted
    (program : GlobalNonDescriptorSourceReferenceProgram)
    (sourceAudited : ∀ (provision : IUPACNormativeProvision)
      (_member : provision ∈ globalNonDescriptorProvisions.toFinset),
        IUPACNormativeSource.ProvisionAuditComplete provision.source)
    (input : AuthoritativeChemicalInput) :
    (program.toReviewedSemantics sourceAudited).reviewed.ChemicallyAdmitted input ↔
      AuthoritativeChemicalInput.StructurallyWellFormed input :=
  Iff.rfl

@[simp] theorem toReviewedSemantics_row_kind
    (program : GlobalNonDescriptorSourceReferenceProgram)
    (sourceAudited : ∀ (provision : IUPACNormativeProvision)
      (_member : provision ∈ globalNonDescriptorProvisions.toFinset),
        IUPACNormativeSource.ProvisionAuditComplete provision.source)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    ((program.toReviewedSemantics sourceAudited).reviewed.row provision member).kind =
      globalProvisionKind provision :=
  rfl

@[simp] theorem toReviewedSemantics_row_sourceSuppliesRule
    (program : GlobalNonDescriptorSourceReferenceProgram)
    (sourceAudited : ∀ (provision : IUPACNormativeProvision)
      (_member : provision ∈ globalNonDescriptorProvisions.toFinset),
        IUPACNormativeSource.ProvisionAuditComplete provision.source)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    ((program.toReviewedSemantics sourceAudited).reviewed.row provision member).sourceSuppliesRule =
      program.sourceSuppliesRule provision member :=
  rfl

@[simp] theorem toReviewedSemantics_row_reference
    (program : GlobalNonDescriptorSourceReferenceProgram)
    (sourceAudited : ∀ (provision : IUPACNormativeProvision)
      (_member : provision ∈ globalNonDescriptorProvisions.toFinset),
        IUPACNormativeSource.ProvisionAuditComplete provision.source)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    ((program.toReviewedSemantics sourceAudited).reviewed.row provision member).reference =
      (program.reference provision member).toReference :=
  rfl

end GlobalNonDescriptorSourceReferenceProgram

theorem GlobalNonDescriptorReviewedSemantics.reviewedReference_ne_nonDescriptorAssignment
    (negative : GlobalNonDescriptorReviewedSemantics)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset)
    (sourcePresent : (negative.reviewed.row provision member).sourceSuppliesRule = true) :
    (negative.reviewed.row provision member).reference ≠
      nonDescriptorAssignmentReference.toReference := by
  intro erased
  exact negative.sourceProgram.reference_ne_nonDescriptorAssignment provision member
    ((negative.source_presence_exact member).symm.trans sourcePresent)
    ((negative.reference_exact member).symm.trans erased)

theorem descriptorBearingReviewedMember
    (provision : IUPACNormativeProvision)
    (bearing : DescriptorAssignmentBearing provision) :
    provision ∈ descriptorBearingReviewedSemanticsSlice.toFinset := by
  rw [descriptorBearingReviewedSemanticsScope_exact]
  simpa using (mem_descriptorAssignmentBearingProvisions_iff provision).2 bearing

theorem globalNonDescriptorReviewedMember
    (provision : IUPACNormativeProvision)
    (negative : ¬DescriptorAssignmentBearing provision) :
    provision ∈ globalNonDescriptorProvisions.toFinset := by
  simpa [globalNonDescriptorProvisions] using
    (mem_descriptorAssignmentNegativeProvisions_iff provision).2 negative

/-- Exact sum of the positive reviewed program and the negative reviewed source program. -/
noncomputable def assembledGlobalReviewedTable
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ReviewedProvisionSemanticsTable := by
  classical
  exact
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision =>
        if bearing : DescriptorAssignmentBearing provision then
          (descriptorBearingReviewedSemantics policies).reviewed.row provision
            (descriptorBearingReviewedMember provision bearing)
        else
          negative.reviewed.row provision
            (globalNonDescriptorReviewedMember provision bearing) }

@[simp] theorem assembledGlobalReviewedTable_descriptorBearing_exact
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (provision : IUPACNormativeProvision)
    (bearing : DescriptorAssignmentBearing provision) :
    (assembledGlobalReviewedTable policies negative).row provision =
      (descriptorBearingReviewedSemantics policies).reviewed.row provision
        (descriptorBearingReviewedMember provision bearing) := by
  simp [assembledGlobalReviewedTable, bearing]

@[simp] theorem assembledGlobalReviewedTable_nonDescriptor_exact
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (provision : IUPACNormativeProvision)
    (nonDescriptor : ¬DescriptorAssignmentBearing provision) :
    (assembledGlobalReviewedTable policies negative).row provision =
      negative.reviewed.row provision
        (globalNonDescriptorReviewedMember provision nonDescriptor) := by
  simp [assembledGlobalReviewedTable, nonDescriptor]




structure GlobalReviewedSemantics
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) where
  reviewed : ReviewedProvisionSemanticsTable
  descriptorBearing_exact : ∀ {provision : IUPACNormativeProvision}
    (bearing : DescriptorAssignmentBearing provision),
      reviewed.row provision =
        (descriptorBearingReviewedSemantics policies).reviewed.row provision
          (descriptorBearingReviewedMember provision bearing)
  nonDescriptor_exact : ∀ {provision : IUPACNormativeProvision}
    (nonDescriptor : ¬DescriptorAssignmentBearing provision),
      reviewed.row provision =
        negative.reviewed.row provision
          (globalNonDescriptorReviewedMember provision nonDescriptor)
  classifier_exact : ∀ provision,
    (reviewed.row provision).kind = globalProvisionKind provision
  source_audited : ∀ provision : IUPACNormativeProvision,
    IUPACNormativeSource.ProvisionAuditComplete provision.source

noncomputable def assembleGlobalReviewedSemantics
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    GlobalReviewedSemantics policies negative where
  reviewed := assembledGlobalReviewedTable policies negative
  descriptorBearing_exact := by
    intro provision bearing
    exact assembledGlobalReviewedTable_descriptorBearing_exact
      policies negative provision bearing
  nonDescriptor_exact := by
    intro provision nonDescriptor
    exact assembledGlobalReviewedTable_nonDescriptor_exact
      policies negative provision nonDescriptor
  classifier_exact := by
    intro provision
    by_cases bearing : DescriptorAssignmentBearing provision
    · rw [assembledGlobalReviewedTable_descriptorBearing_exact
        policies negative provision bearing]
      exact (descriptorBearingReviewedSemantics policies).classifier_exact
        (descriptorBearingReviewedMember provision bearing)
    · rw [assembledGlobalReviewedTable_nonDescriptor_exact
        policies negative provision bearing]
      exact negative.classifier_exact
        (globalNonDescriptorReviewedMember provision bearing)
  source_audited := by
    intro provision
    by_cases bearing : DescriptorAssignmentBearing provision
    · exact (descriptorBearingReviewedSemantics policies).reviewed.sourceAudited
        (descriptorBearingReviewedMember provision bearing)
    · exact negative.reviewed.sourceAudited
        (globalNonDescriptorReviewedMember provision bearing)

namespace GlobalReviewedSemantics

/-- Every descriptor-bearing reviewed row is an authority-present rule.  This follows from the
positive reviewed-family construction rather than from a global all-rows assumption. -/
theorem descriptorBearing_source_present
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (bearing : DescriptorAssignmentBearing provision) :
    (global.reviewed.row provision).sourceSuppliesRule = true := by
  rw [global.descriptorBearing_exact bearing]
  rfl

theorem nonDescriptorReference_ne_operationalEmpty
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (nonDescriptor : ¬DescriptorAssignmentBearing provision)
    (sourcePresent : (global.reviewed.row provision).sourceSuppliesRule = true) :
    (global.reviewed.row provision).reference ≠
      nonDescriptorAssignmentReference.toReference := by
  rw [global.nonDescriptor_exact nonDescriptor]
  exact negative.reviewedReference_ne_nonDescriptorAssignment provision
    (globalNonDescriptorReviewedMember provision nonDescriptor) (by
      simpa only [global.nonDescriptor_exact nonDescriptor] using sourcePresent)

/-- The source corpus induced literally by the reviewed table, before any operation projection. -/
noncomputable def toFrozenCorpus
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative) : FrozenProvisionCorpus where
  ChemicallyAdmitted := global.reviewed.ChemicallyAdmitted
  kind := fun provision => (global.reviewed.row provision).kind
  SourceSuppliesRule := fun provision =>
    (global.reviewed.row provision).sourceSuppliesRule = true
  reference := fun provision => (global.reviewed.row provision).reference

theorem corpusFaithful
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative) :
    ReviewedCorpusFaithful global.reviewed global.toFrozenCorpus where
  admitted_exact := by
    intro input
    rfl
  exact := by
    intro provision
    exact ⟨rfl, Iff.rfl, rfl⟩

end GlobalReviewedSemantics

@[simp] theorem globalReviewedPartitionCount :
    descriptorBearingReviewedSemanticsSlice.length +
      globalNonDescriptorProvisions.length = 2452 := by
  simp

theorem globalReviewedPartition_exact (provision : IUPACNormativeProvision) :
    (provision ∈ descriptorBearingReviewedSemanticsSlice.toFinset ∨
      provision ∈ globalNonDescriptorProvisions.toFinset) ∧
    ¬(provision ∈ descriptorBearingReviewedSemanticsSlice.toFinset ∧
      provision ∈ globalNonDescriptorProvisions.toFinset) := by
  by_cases bearing : DescriptorAssignmentBearing provision
  · refine ⟨Or.inl (descriptorBearingReviewedMember provision bearing), ?_⟩
    intro overlap
    have negative : ¬DescriptorAssignmentBearing provision :=
      (mem_globalNonDescriptorProvisions_iff provision).1 (by simpa using overlap.2)
    exact negative bearing
  · refine ⟨Or.inr (globalNonDescriptorReviewedMember provision bearing), ?_⟩
    intro overlap
    have positiveFinset : provision ∈ descriptorAssignmentBearingProvisions.toFinset := by
      rw [← descriptorBearingReviewedSemanticsScope_exact]
      exact overlap.1
    have positiveList : provision ∈ descriptorAssignmentBearingProvisions := by
      simpa using positiveFinset
    have positive : DescriptorAssignmentBearing provision :=
      (mem_descriptorAssignmentBearingProvisions_iff provision).1 positiveList
    exact bearing positive

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSourceReferenceProgram.toReviewedSemantics
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSourceReferenceProgram.toReviewedSemantics_admitted
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSourceReferenceProgram.toReviewedSemantics_row_kind
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSourceReferenceProgram.toReviewedSemantics_row_sourceSuppliesRule
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSourceReferenceProgram.toReviewedSemantics_row_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalReviewedPartitionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalReviewedPartition_exact
