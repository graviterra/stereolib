import TetraStereo.OneCenter.IUPACGlobalProvisionClassification

set_option autoImplicit false

/-!
# Global non-descriptor operation projection

The global operation partition identifies 2,300 provisions outside descriptor assignment:
depiction, nomenclature, source scope, and 171 Appendix-3 retained-parent structures.  This module
defines that exact partition and the typed descriptor-assignment projection that gives those rows
empty operational applicability.  Compiler generation and the seven-family proof live in
`IUPACGlobalCompilerAssembly`.

This operation projection does not rewrite the independent source meanings and does not classify
any row as source-absent.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

def globalNonDescriptorProvisions : List IUPACNormativeProvision :=
  descriptorAssignmentNegativeProvisions

set_option maxRecDepth 16384 in
@[simp] theorem globalNonDescriptorProvisionCount :
    globalNonDescriptorProvisions.length = 2300 := by
  exact descriptorAssignmentNegativeProvisionCount

theorem globalNonDescriptorProvisions_nodup :
    globalNonDescriptorProvisions.Nodup :=
  descriptorAssignmentNegativeProvisions_nodup

theorem mem_globalNonDescriptorProvisions_iff
    (provision : IUPACNormativeProvision) :
    provision ∈ globalNonDescriptorProvisions ↔
      ¬DescriptorAssignmentBearing provision := by
  exact mem_descriptorAssignmentNegativeProvisions_iff provision

/-! ## Typed source-to-operation projection -/

/-- Provision meanings are source-owned; production comparisons are operation-specific.  The
phantom operation index prevents a descriptor-assignment projection from being confused with the
sole source reference reviewed for the provision. -/
inductive ProvisionSemanticOperation where
  | sourceMeaning
  | descriptorAssignment

structure OperationProvisionReference (operation : ProvisionSemanticOperation) where
  toReference : ProvisionReference

/-- Empty applicability only at the `descriptorAssignment` operation.  This does not replace or
weaken the source-owned provision reference. -/
def nonDescriptorAssignmentReference :
    OperationProvisionReference .descriptorAssignment where
  toReference :=
    { Observation := PUnit
      Applicable := fun _input => False
      Judges := fun _input _observation => False }

/-- A total descriptor-assignment projection from a source-faithful corpus.  Negative rows project
to empty applicability; descriptor-bearing rows retain their exact source reference. -/
structure DescriptorAssignmentProjection (sourceCorpus : FrozenProvisionCorpus) where
  reference : (provision : IUPACNormativeProvision) →
    OperationProvisionReference .descriptorAssignment
  nonDescriptor_exact : ∀ (provision : IUPACNormativeProvision),
    ¬DescriptorAssignmentBearing provision →
      reference provision = nonDescriptorAssignmentReference
  descriptorBearing_exact : ∀ (provision : IUPACNormativeProvision),
    DescriptorAssignmentBearing provision →
      (reference provision).toReference = sourceCorpus.reference provision

namespace DescriptorAssignmentProjection

/-- The operation-specific corpus inherits admission, kind, and source ownership verbatim; only
the operation reference is projected. -/
def toCorpus {sourceCorpus : FrozenProvisionCorpus}
    (projection : DescriptorAssignmentProjection sourceCorpus) : FrozenProvisionCorpus where
  ChemicallyAdmitted := sourceCorpus.ChemicallyAdmitted
  kind := sourceCorpus.kind
  SourceSuppliesRule := sourceCorpus.SourceSuppliesRule
  reference := fun provision => (projection.reference provision).toReference

end DescriptorAssignmentProjection

/-- Canonical total projection fixed by the global kind classifier. -/
noncomputable def globalDescriptorAssignmentProjection
    (sourceCorpus : FrozenProvisionCorpus) : DescriptorAssignmentProjection sourceCorpus := by
  classical
  exact
    { reference := fun provision =>
        if DescriptorAssignmentBearing provision then
          ⟨sourceCorpus.reference provision⟩
        else
          nonDescriptorAssignmentReference
      nonDescriptor_exact := by
        intro provision nonDescriptor
        simp [nonDescriptor]
      descriptorBearing_exact := by
        intro provision bearing
        simp [bearing] }

theorem globalDescriptorAssignmentProjection_inapplicable
    (sourceCorpus : FrozenProvisionCorpus)
    {provision : IUPACNormativeProvision}
    (member : provision ∈ globalNonDescriptorProvisions) :
    ∀ input,
      ¬((globalDescriptorAssignmentProjection sourceCorpus).toCorpus.reference provision).Applicable
        input := by
  intro input
  have nonDescriptor := (mem_globalNonDescriptorProvisions_iff provision).1 member
  change ¬((globalDescriptorAssignmentProjection sourceCorpus).reference provision).toReference.Applicable
    input
  rw [(globalDescriptorAssignmentProjection sourceCorpus).nonDescriptor_exact
    provision nonDescriptor]
  simp [nonDescriptorAssignmentReference]

theorem ProvisionDisposition.not_conformant_of_notApplicable
    {corpus : FrozenProvisionCorpus}
    {provision : IUPACNormativeProvision}
    {disposition : ProvisionDisposition corpus provision}
    (notApplicable : disposition.IsNotApplicable) :
    ¬disposition.IsConformant := by
  cases disposition <;>
    simp [ProvisionDisposition.IsNotApplicable,
      ProvisionDisposition.IsConformant] at notApplicable ⊢

theorem ProvisionDisposition.not_conformant_of_sourceAbsent
    {corpus : FrozenProvisionCorpus}
    {provision : IUPACNormativeProvision}
    {disposition : ProvisionDisposition corpus provision}
    (sourceAbsent : disposition.IsSourceAbsent) :
    ¬disposition.IsConformant := by
  cases disposition <;>
    simp [ProvisionDisposition.IsSourceAbsent,
      ProvisionDisposition.IsConformant] at sourceAbsent ⊢

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalNonDescriptorProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.globalNonDescriptorProvisions_nodup
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.mem_globalNonDescriptorProvisions_iff
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionDisposition.not_conformant_of_notApplicable
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.ProvisionDisposition.not_conformant_of_sourceAbsent
