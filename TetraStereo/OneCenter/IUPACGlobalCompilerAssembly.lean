import TetraStereo.OneCenter.IUPACGlobalReviewedSemantics

set_option autoImplicit false

/-!
# Exhaustive global compiler assembly

The exact 152/2,300 provision partition is lifted from reviewed source semantics to compiler
specifications.  Two scoped compilers over the same descriptor-assignment corpus become one total
2,452-row compiler; their scoped seven-family correctness theorems become the global seven-family
theorem.  Dispositions are fixed en masse: descriptor-bearing rows are conformant, while negative
rows become `notApplicable` or `sourceAbsent` according to audited source presence.

This module deliberately stops at the exact compiler/correctness assembly boundary.  The genuine
root `CompleteIUPACAuthorityCertificate` must be assembled only from named concrete production
adapters for primitive35, next54, and remaining71; it is not exposed through an arbitrary
interpreter parameter.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

theorem descriptorBearingOfReviewedMember
    (provision : IUPACNormativeProvision)
    (member : provision ∈ descriptorBearingReviewedSemanticsSlice.toFinset) :
    DescriptorAssignmentBearing provision := by
  have classified : provision ∈ descriptorAssignmentBearingProvisions.toFinset := by
    rw [← descriptorBearingReviewedSemanticsScope_exact]
    exact member
  exact (mem_descriptorAssignmentBearingProvisions_iff provision).1 (by
    simpa using classified)

theorem nonDescriptorOfReviewedMember
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    ¬DescriptorAssignmentBearing provision := by
  exact (mem_globalNonDescriptorProvisions_iff provision).1 (by simpa using member)

/-- The two exact compiler pieces over one shared operation-projected corpus. -/
structure GlobalProvisionCompilerPieces (sourceCorpus : FrozenProvisionCorpus) where
  descriptorBearing : ScopedProvisionCompiler
    (globalDescriptorAssignmentProjection sourceCorpus).toCorpus
    descriptorBearingReviewedSemanticsSlice.toFinset
  nonDescriptor : ScopedProvisionCompiler
    (globalDescriptorAssignmentProjection sourceCorpus).toCorpus
    globalNonDescriptorProvisions.toFinset

namespace GlobalProvisionCompilerPieces

/-- Exhaustive compiler join.  The dependent membership proofs are obtained from the same exact
partition used by the reviewed source table. -/
noncomputable def toCompiler
    {sourceCorpus : FrozenProvisionCorpus}
    (pieces : GlobalProvisionCompilerPieces sourceCorpus) :
    ProvisionCompiler (globalDescriptorAssignmentProjection sourceCorpus).toCorpus := by
  classical
  exact
    { spec := fun provision =>
        if bearing : DescriptorAssignmentBearing provision then
          pieces.descriptorBearing.spec provision
            (descriptorBearingReviewedMember provision bearing)
        else
          pieces.nonDescriptor.spec provision
            (globalNonDescriptorReviewedMember provision bearing) }

@[simp] theorem toCompiler_descriptorBearing_exact
    {sourceCorpus : FrozenProvisionCorpus}
    (pieces : GlobalProvisionCompilerPieces sourceCorpus)
    (provision : IUPACNormativeProvision)
    (bearing : DescriptorAssignmentBearing provision) :
    pieces.toCompiler.spec provision =
      pieces.descriptorBearing.spec provision
        (descriptorBearingReviewedMember provision bearing) := by
  simp [toCompiler, bearing]

@[simp] theorem toCompiler_nonDescriptor_exact
    {sourceCorpus : FrozenProvisionCorpus}
    (pieces : GlobalProvisionCompilerPieces sourceCorpus)
    (provision : IUPACNormativeProvision)
    (nonDescriptor : ¬DescriptorAssignmentBearing provision) :
    pieces.toCompiler.spec provision =
      pieces.nonDescriptor.spec provision
        (globalNonDescriptorReviewedMember provision nonDescriptor) := by
  simp [toCompiler, nonDescriptor]

end GlobalProvisionCompilerPieces

/-- Scoped correctness for both exact sides of the global compiler partition. -/
structure GlobalProvisionCompilerPiecesCorrect
    {sourceCorpus : FrozenProvisionCorpus}
    (pieces : GlobalProvisionCompilerPieces sourceCorpus)
    (interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus) : Prop where
  descriptorBearing : ScopedProvisionCompilerCorrect pieces.descriptorBearing interpreter
  nonDescriptor : ScopedProvisionCompilerCorrect pieces.nonDescriptor interpreter

namespace GlobalProvisionCompilerPiecesCorrect

theorem every_provision_correct
    {sourceCorpus : FrozenProvisionCorpus}
    {pieces : GlobalProvisionCompilerPieces sourceCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (correct : GlobalProvisionCompilerPiecesCorrect pieces interpreter)
    (provision : IUPACNormativeProvision) :
    ProvisionCorrect (globalDescriptorAssignmentProjection sourceCorpus).toCorpus
      interpreter provision := by
  by_cases bearing : DescriptorAssignmentBearing provision
  · exact correct.descriptorBearing.every_provision_correct provision
      (descriptorBearingReviewedMember provision bearing)
  · exact correct.nonDescriptor.every_provision_correct provision
      (globalNonDescriptorReviewedMember provision bearing)

/-- The global seven-family theorem is a projection of the two scoped seven-family theorems, not
a fresh row-wise correctness proof. -/
def toCompilerCorrect
    {sourceCorpus : FrozenProvisionCorpus}
    {pieces : GlobalProvisionCompilerPieces sourceCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (correct : GlobalProvisionCompilerPiecesCorrect pieces interpreter) :
    ProvisionCompilerCorrect pieces.toCompiler interpreter where
  sequenceRule_correct := by
    intro provision _kind
    exact correct.every_provision_correct provision
  perception_correct := by
    intro provision _kind
    exact correct.every_provision_correct provision
  spatialDescriptor_correct := by
    intro provision _kind
    exact correct.every_provision_correct provision
  depiction_correct := by
    intro provision _kind
    exact correct.every_provision_correct provision
  nomenclature_correct := by
    intro provision _kind
    exact correct.every_provision_correct provision
  authorityData_correct := by
    intro provision _kind
    exact correct.every_provision_correct provision
  sourceOnly_correct := by
    intro provision _kind
    exact correct.every_provision_correct provision

end GlobalProvisionCompilerPiecesCorrect

/-- Exact disposition theorem for the two compiler pieces. -/
structure GlobalProvisionDispositionPartition
    {sourceCorpus : FrozenProvisionCorpus}
    (pieces : GlobalProvisionCompilerPieces sourceCorpus) : Prop where
  descriptorBearing_conformant : ∀ (provision : IUPACNormativeProvision)
    (member : provision ∈ descriptorBearingReviewedSemanticsSlice.toFinset),
      (pieces.descriptorBearing.spec provision member).disposition.IsConformant
  nonDescriptor_terminal : ∀ (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset),
      (pieces.nonDescriptor.spec provision member).disposition.IsNotApplicable ∨
        (pieces.nonDescriptor.spec provision member).disposition.IsSourceAbsent

namespace GlobalProvisionDispositionPartition

theorem isConformant_iff_descriptorBearing
    {sourceCorpus : FrozenProvisionCorpus}
    {pieces : GlobalProvisionCompilerPieces sourceCorpus}
    (partition : GlobalProvisionDispositionPartition pieces)
    (provision : IUPACNormativeProvision) :
    (pieces.toCompiler.spec provision).disposition.IsConformant ↔
      DescriptorAssignmentBearing provision := by
  by_cases bearing : DescriptorAssignmentBearing provision
  · rw [pieces.toCompiler_descriptorBearing_exact provision bearing]
    exact ⟨fun _conformant => bearing,
      fun _bearing => partition.descriptorBearing_conformant provision
        (descriptorBearingReviewedMember provision bearing)⟩
  · rw [pieces.toCompiler_nonDescriptor_exact provision bearing]
    constructor
    · intro conformant
      rcases partition.nonDescriptor_terminal provision
          (globalNonDescriptorReviewedMember provision bearing) with
        notApplicable | sourceAbsent
      · exact False.elim
          (ProvisionDisposition.not_conformant_of_notApplicable notApplicable conformant)
      · exact False.elim
          (ProvisionDisposition.not_conformant_of_sourceAbsent sourceAbsent conformant)
    · intro impossible
      exact False.elim (bearing impossible)

theorem terminal_of_nonDescriptor
    {sourceCorpus : FrozenProvisionCorpus}
    {pieces : GlobalProvisionCompilerPieces sourceCorpus}
    (partition : GlobalProvisionDispositionPartition pieces)
    (provision : IUPACNormativeProvision)
    (nonDescriptor : ¬DescriptorAssignmentBearing provision) :
    (pieces.toCompiler.spec provision).disposition.IsNotApplicable ∨
      (pieces.toCompiler.spec provision).disposition.IsSourceAbsent := by
  rw [pieces.toCompiler_nonDescriptor_exact provision nonDescriptor]
  exact partition.nonDescriptor_terminal provision
    (globalNonDescriptorReviewedMember provision nonDescriptor)

end GlobalProvisionDispositionPartition

/-! ## Generated negative compiler and interpreter branch -/



noncomputable def generatedGlobalNonDescriptorCompiler
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative) :
    ScopedProvisionCompiler
      (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus
      globalNonDescriptorProvisions.toFinset where
  spec := fun provision member =>
    { sourceAudited := global.source_audited provision
      disposition := if sourcePresent :
          (global.reviewed.row provision).sourceSuppliesRule = true then
        .notApplicable sourcePresent (by
            intro input _admitted
            exact globalDescriptorAssignmentProjection_inapplicable global.toFrozenCorpus
              (by simpa using member) input)
      else
        .sourceAbsent sourcePresent (by
            intro input _admitted
            exact globalDescriptorAssignmentProjection_inapplicable global.toFrozenCorpus
              (by simpa using member) input) }

theorem generatedGlobalNonDescriptorCompiler_terminal
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    ProvisionDisposition.IsNotApplicable
        ((generatedGlobalNonDescriptorCompiler global).spec provision member).disposition ∨
      ProvisionDisposition.IsSourceAbsent
        ((generatedGlobalNonDescriptorCompiler global).spec provision member).disposition := by
  by_cases sourcePresent :
      (global.reviewed.row provision).sourceSuppliesRule = true <;>
    simp [generatedGlobalNonDescriptorCompiler, sourcePresent,
      ProvisionDisposition.IsNotApplicable, ProvisionDisposition.IsSourceAbsent]

/-- The generated negative compiler chooses `notApplicable` exactly when the frozen source corpus
contains the whole provision. -/
theorem generatedGlobalNonDescriptorCompiler_notApplicable_iff_sourcePresent
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    ProvisionDisposition.IsNotApplicable
        ((generatedGlobalNonDescriptorCompiler global).spec provision member).disposition ↔
      global.toFrozenCorpus.SourceSuppliesRule provision := by
  change ProvisionDisposition.IsNotApplicable
      ((generatedGlobalNonDescriptorCompiler global).spec provision member).disposition ↔
    (global.reviewed.row provision).sourceSuppliesRule = true
  by_cases sourcePresent :
      (global.reviewed.row provision).sourceSuppliesRule = true <;>
    simp [generatedGlobalNonDescriptorCompiler, sourcePresent,
      ProvisionDisposition.IsNotApplicable]

/-- The complementary generated branch is `sourceAbsent` exactly when the frozen source corpus
does not contain the whole provision. -/
theorem generatedGlobalNonDescriptorCompiler_sourceAbsent_iff_sourceAbsent
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    ProvisionDisposition.IsSourceAbsent
        ((generatedGlobalNonDescriptorCompiler global).spec provision member).disposition ↔
      ¬global.toFrozenCorpus.SourceSuppliesRule provision := by
  change ProvisionDisposition.IsSourceAbsent
      ((generatedGlobalNonDescriptorCompiler global).spec provision member).disposition ↔
    ¬(global.reviewed.row provision).sourceSuppliesRule = true
  by_cases sourcePresent :
      (global.reviewed.row provision).sourceSuppliesRule = true <;>
    simp [generatedGlobalNonDescriptorCompiler, sourcePresent,
      ProvisionDisposition.IsSourceAbsent]

/-- One family-level witness theorem for the exact 152-row reviewed source program.  This is the
only data needed to generate every positive compiler disposition; it is deliberately stated over
the independently reviewed references, not over production output. -/
structure DescriptorBearingReviewedNonvacuity
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative) : Prop where
  nonvacuous : ∀ (provision : IUPACNormativeProvision)
    (_member : provision ∈ descriptorBearingReviewedSemanticsSlice.toFinset),
      ∃ input, ∃ observation : (global.reviewed.row provision).reference.Observation,
        global.reviewed.ChemicallyAdmitted input ∧
          (global.reviewed.row provision).reference.Applicable input ∧
            (global.reviewed.row provision).reference.Judges input observation

/-- The source-reference witness boundary is proved once per strategic reviewed family, not once
per manifest provision. -/
structure DescriptorBearingReviewedNonvacuityFamilies
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative) : Prop where
  primitive35 : ∀ row : Primitive35AuthorityRow,
    ∃ input, ∃ observation : (global.reviewed.row row.provision).reference.Observation,
      global.reviewed.ChemicallyAdmitted input ∧
        (global.reviewed.row row.provision).reference.Applicable input ∧
          (global.reviewed.row row.provision).reference.Judges input observation
  next54 : ∀ row : Next54DescriptorBearingReviewedRow,
    ∃ input, ∃ observation : (global.reviewed.row row.provision).reference.Observation,
      global.reviewed.ChemicallyAdmitted input ∧
        (global.reviewed.row row.provision).reference.Applicable input ∧
          (global.reviewed.row row.provision).reference.Judges input observation
  remaining71 : ∀ row : Remaining71ReviewedRow,
    ∃ input, ∃ observation : (global.reviewed.row row.provision).reference.Observation,
      global.reviewed.ChemicallyAdmitted input ∧
        (global.reviewed.row row.provision).reference.Applicable input ∧
          (global.reviewed.row row.provision).reference.Judges input observation

namespace DescriptorBearingReviewedNonvacuityFamilies

noncomputable def toReviewedNonvacuity
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    {global : GlobalReviewedSemantics policies negative}
    (families : DescriptorBearingReviewedNonvacuityFamilies global) :
    DescriptorBearingReviewedNonvacuity global where
  nonvacuous := by
    intro provision member
    have listMember : provision ∈ descriptorBearingReviewedSemanticsSlice := by
      simpa using member
    obtain ⟨row, _rowMember, rfl⟩ :=
      exists_descriptorBearingReviewedRow listMember
    cases row with
    | primitive35 child => exact families.primitive35 child
    | next54 child => exact families.next54 child
    | remaining71 child => exact families.remaining71 child

end DescriptorBearingReviewedNonvacuityFamilies

/-- Generate all 152 audited conformant specifications from the reviewed source witnesses. -/
noncomputable def generatedGlobalDescriptorBearingCompiler
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (witnesses : DescriptorBearingReviewedNonvacuity global) :
    ScopedProvisionCompiler
      (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus
      descriptorBearingReviewedSemanticsSlice.toFinset where
  spec := fun provision member =>
    { sourceAudited := global.source_audited provision
      disposition := .conformant (by
          change (global.reviewed.row provision).sourceSuppliesRule = true
          exact global.descriptorBearing_source_present provision
            (descriptorBearingOfReviewedMember provision member)) (by
          have bearing := descriptorBearingOfReviewedMember provision member
          change ∃ input, ∃ observation,
            global.toFrozenCorpus.ChemicallyAdmitted input ∧
              (((globalDescriptorAssignmentProjection global.toFrozenCorpus).reference
                provision).toReference).Applicable input ∧
              (((globalDescriptorAssignmentProjection global.toFrozenCorpus).reference
                provision).toReference).Judges input observation
          rw [DescriptorAssignmentProjection.descriptorBearing_exact
            (globalDescriptorAssignmentProjection global.toFrozenCorpus) provision bearing]
          exact witnesses.nonvacuous provision member) }

@[simp] theorem generatedGlobalDescriptorBearingCompiler_conformant
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (witnesses : DescriptorBearingReviewedNonvacuity global)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ descriptorBearingReviewedSemanticsSlice.toFinset) :
    ProvisionDisposition.IsConformant
      ((generatedGlobalDescriptorBearingCompiler global witnesses).spec provision member).disposition := by
  simp [generatedGlobalDescriptorBearingCompiler, ProvisionDisposition.IsConformant]

/-- Preserve the positive production interpreter exactly and generate an empty production branch
for every non-descriptor provision. -/
noncomputable def generatedGlobalDescriptorAssignmentInterpreter
    {sourceCorpus : FrozenProvisionCorpus}
    (positive : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus) :
    ProvisionInterpreter (globalDescriptorAssignmentProjection sourceCorpus).toCorpus := by
  classical
  exact
    { Produces := fun provision input observation =>
        if DescriptorAssignmentBearing provision then
          positive.Produces provision input observation
        else
          False }

/-- Positive correctness transfers literally through the generated interpreter branch. -/
theorem generatedInterpreter_descriptorBearing_correct
    {sourceCorpus : FrozenProvisionCorpus}
    {compiler : ScopedProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus
      descriptorBearingReviewedSemanticsSlice.toFinset}
    {positive : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (correct : ScopedProvisionCompilerCorrect compiler positive)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ descriptorBearingReviewedSemanticsSlice.toFinset) :
    ProvisionCorrect (globalDescriptorAssignmentProjection sourceCorpus).toCorpus
      (generatedGlobalDescriptorAssignmentInterpreter positive) provision := by
  have bearing := descriptorBearingOfReviewedMember provision member
  have exactPositive := correct.every_provision_correct provision member
  intro input admitted observation
  simpa [generatedGlobalDescriptorAssignmentInterpreter, bearing] using
    exactPositive input admitted observation

/-- The generated negative production branch is correct because both production and the exact
operation-projected reference applicability are empty. -/
theorem generatedInterpreter_nonDescriptor_correct
    {sourceCorpus : FrozenProvisionCorpus}
    (positive : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    ProvisionCorrect (globalDescriptorAssignmentProjection sourceCorpus).toCorpus
      (generatedGlobalDescriptorAssignmentInterpreter positive) provision := by
  have nonDescriptor := nonDescriptorOfReviewedMember provision member
  intro input _admitted observation
  constructor
  · intro produced
    simp [generatedGlobalDescriptorAssignmentInterpreter, nonDescriptor] at produced
  · intro expected
    have inapplicable := globalDescriptorAssignmentProjection_inapplicable sourceCorpus
      (by simpa using member) input
    exact False.elim (inapplicable expected.1)

/-- Generate all 2,300 negative family-correctness obligations at once. -/
def generatedGlobalNonDescriptorCorrect
    {sourceCorpus : FrozenProvisionCorpus}
    (compiler : ScopedProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus
      globalNonDescriptorProvisions.toFinset)
    (positive : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus) :
    ScopedProvisionCompilerCorrect compiler
      (generatedGlobalDescriptorAssignmentInterpreter positive) where
  sequenceRule_correct := by
    intro provision member _kind
    exact generatedInterpreter_nonDescriptor_correct positive provision member
  perception_correct := by
    intro provision member _kind
    exact generatedInterpreter_nonDescriptor_correct positive provision member
  spatialDescriptor_correct := by
    intro provision member _kind
    exact generatedInterpreter_nonDescriptor_correct positive provision member
  depiction_correct := by
    intro provision member _kind
    exact generatedInterpreter_nonDescriptor_correct positive provision member
  nomenclature_correct := by
    intro provision member _kind
    exact generatedInterpreter_nonDescriptor_correct positive provision member
  authorityData_correct := by
    intro provision member _kind
    exact generatedInterpreter_nonDescriptor_correct positive provision member
  sourceOnly_correct := by
    intro provision member _kind
    exact generatedInterpreter_nonDescriptor_correct positive provision member

/-- Transfer the positive scoped correctness certificate to the generated global interpreter. -/
def generatedGlobalDescriptorBearingCorrect
    {sourceCorpus : FrozenProvisionCorpus}
    (compiler : ScopedProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus
      descriptorBearingReviewedSemanticsSlice.toFinset)
    (positive : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus)
    (correct : ScopedProvisionCompilerCorrect compiler positive) :
    ScopedProvisionCompilerCorrect compiler
      (generatedGlobalDescriptorAssignmentInterpreter positive) where
  sequenceRule_correct := by
    intro provision member _kind
    exact generatedInterpreter_descriptorBearing_correct correct provision member
  perception_correct := by
    intro provision member _kind
    exact generatedInterpreter_descriptorBearing_correct correct provision member
  spatialDescriptor_correct := by
    intro provision member _kind
    exact generatedInterpreter_descriptorBearing_correct correct provision member
  depiction_correct := by
    intro provision member _kind
    exact generatedInterpreter_descriptorBearing_correct correct provision member
  nomenclature_correct := by
    intro provision member _kind
    exact generatedInterpreter_descriptorBearing_correct correct provision member
  authorityData_correct := by
    intro provision member _kind
    exact generatedInterpreter_descriptorBearing_correct correct provision member
  sourceOnly_correct := by
    intro provision member _kind
    exact generatedInterpreter_descriptorBearing_correct correct provision member

/-- Assemble the exact global compiler pieces from only the positive scoped compiler; the entire
negative half is generated from the global reviewed source table. -/
noncomputable def generatedGlobalProvisionCompilerPieces
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (positive : ScopedProvisionCompiler
      (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus
      descriptorBearingReviewedSemanticsSlice.toFinset) :
    GlobalProvisionCompilerPieces global.toFrozenCorpus where
  descriptorBearing := positive
  nonDescriptor := generatedGlobalNonDescriptorCompiler global

/-- The generated pieces inherit positive correctness and synthesize negative correctness. -/
noncomputable def generatedGlobalProvisionCompilerPiecesCorrect
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (positiveCompiler : ScopedProvisionCompiler
      (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus
      descriptorBearingReviewedSemanticsSlice.toFinset)
    (positiveInterpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus)
    (positiveCorrect : ScopedProvisionCompilerCorrect
      positiveCompiler positiveInterpreter) :
    GlobalProvisionCompilerPiecesCorrect
      (generatedGlobalProvisionCompilerPieces global positiveCompiler)
      (generatedGlobalDescriptorAssignmentInterpreter positiveInterpreter) where
  descriptorBearing := generatedGlobalDescriptorBearingCorrect
    positiveCompiler positiveInterpreter positiveCorrect
  nonDescriptor := generatedGlobalNonDescriptorCorrect
    (generatedGlobalNonDescriptorCompiler global) positiveInterpreter

/-- The exact disposition partition now needs only positive conformance evidence. -/
noncomputable def generatedGlobalProvisionDispositionPartition
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (positiveCompiler : ScopedProvisionCompiler
      (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus
      descriptorBearingReviewedSemanticsSlice.toFinset)
    (positiveConformant : ∀ (provision : IUPACNormativeProvision)
      (member : provision ∈ descriptorBearingReviewedSemanticsSlice.toFinset),
        (positiveCompiler.spec provision member).disposition.IsConformant) :
    GlobalProvisionDispositionPartition
      (generatedGlobalProvisionCompilerPieces global positiveCompiler) where
  descriptorBearing_conformant := positiveConformant
  nonDescriptor_terminal := by
    intro provision member
    exact generatedGlobalNonDescriptorCompiler_terminal global provision member

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalProvisionCompilerPieces.toCompiler
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalProvisionCompilerPiecesCorrect.toCompilerCorrect
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalProvisionDispositionPartition.isConformant_iff_descriptorBearing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.generatedGlobalNonDescriptorCompiler_notApplicable_iff_sourcePresent
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.generatedGlobalNonDescriptorCompiler_sourceAbsent_iff_sourceAbsent
