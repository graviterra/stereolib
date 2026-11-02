import TetraStereo.OneCenter.IUPACGlobalReviewedSemantics
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Proof-carrying source manifest for the global non-descriptor partition

This module gives the 2,300 operationally non-descriptor rows one finite, no-fallback source
program interface.  It does not provide any row data: a manifest entry must carry an independent
source-meaning reference and a concrete admitted judgment, and the manifest must cover the exact
canonical provision list.  The materializer therefore cannot manufacture an absent row or replace
source meaning by the empty descriptor-assignment projection.

Completed source audits remain a separate proof-carrying input to reviewed-semantics assembly.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-- One independently transcribed source meaning in the non-descriptor manifest. -/
structure GlobalNonDescriptorSourceMeaningEntry where
  provision : IUPACNormativeProvision
  reference : OperationProvisionReference .sourceMeaning
  admittedJudgment :
    ∃ input, ∃ observation : reference.toReference.Observation,
      AuthoritativeChemicalInput.StructurallyWellFormed input ∧
        reference.toReference.Applicable input ∧
          reference.toReference.Judges input observation

/-- A composable, exact source-meaning batch.  Unlike the final canonical manifest, a batch may
cover any explicitly named list of rows drawn from the 2,300-row non-descriptor partition; it need
not itself be duplicate-free or canonically ordered.  Every row already carries its real
source-meaning reference and an admitted judgment; `scope` only prevents a batch from smuggling in
a descriptor-bearing provision.

The provision list is an index rather than stored metadata.  Consequently append is literal list
append and eventual promotion to the canonical manifest requires an exact equation with the full
canonical list—there is no union, fallback, or row synthesis step. -/
structure GlobalNonDescriptorSourceMeaningBatch
    (provisions : List IUPACNormativeProvision) where
  entries : List GlobalNonDescriptorSourceMeaningEntry
  provisions_exact :
    entries.map GlobalNonDescriptorSourceMeaningEntry.provision = provisions
  scope : ∀ provision ∈ provisions, provision ∈ globalNonDescriptorProvisions

namespace GlobalNonDescriptorSourceMeaningBatch

@[simp] theorem entries_length
    {provisions : List IUPACNormativeProvision}
    (batch : GlobalNonDescriptorSourceMeaningBatch provisions) :
    batch.entries.length = provisions.length := by
  simpa using congrArg List.length batch.provisions_exact

/-- Empty identity batch for source-ordered assembly. -/
def empty : GlobalNonDescriptorSourceMeaningBatch [] where
  entries := []
  provisions_exact := rfl
  scope := by simp

/-- Source-order-preserving composition.  The result still contains every proof-carrying entry;
the operation cannot merge equal rows or fill a missing row. -/
def append
    {leftProvisions rightProvisions : List IUPACNormativeProvision}
    (left : GlobalNonDescriptorSourceMeaningBatch leftProvisions)
    (right : GlobalNonDescriptorSourceMeaningBatch rightProvisions) :
    GlobalNonDescriptorSourceMeaningBatch (leftProvisions ++ rightProvisions) where
  entries := left.entries ++ right.entries
  provisions_exact := by
    rw [List.map_append, left.provisions_exact, right.provisions_exact]
  scope := by
    intro provision member
    rcases List.mem_append.mp member with leftMember | rightMember
    · exact left.scope provision leftMember
    · exact right.scope provision rightMember

@[simp] theorem append_entries
    {leftProvisions rightProvisions : List IUPACNormativeProvision}
    (left : GlobalNonDescriptorSourceMeaningBatch leftProvisions)
    (right : GlobalNonDescriptorSourceMeaningBatch rightProvisions) :
    (left.append right).entries = left.entries ++ right.entries :=
  rfl

end GlobalNonDescriptorSourceMeaningBatch

/-- A finite source manifest whose provision column is definitionally the exact canonical
2,300-row partition.  Exact list equality records both coverage and order; canonical list
`Nodup` rules out duplicate or fallback entries. -/
structure GlobalNonDescriptorCanonicalSourceManifest where
  entries : List GlobalNonDescriptorSourceMeaningEntry
  provisions_exact :
    entries.map GlobalNonDescriptorSourceMeaningEntry.provision =
      globalNonDescriptorProvisions

namespace GlobalNonDescriptorSourceMeaningBatch

/-- The only promotion path from composable batches to the canonical manifest.  Its type requires
literal coverage of the complete canonical 2,300-row list. -/
def toCanonical
    (batch : GlobalNonDescriptorSourceMeaningBatch globalNonDescriptorProvisions) :
    GlobalNonDescriptorCanonicalSourceManifest where
  entries := batch.entries
  provisions_exact := batch.provisions_exact

end GlobalNonDescriptorSourceMeaningBatch

namespace GlobalNonDescriptorCanonicalSourceManifest

theorem entryProvisions_nodup
    (manifest : GlobalNonDescriptorCanonicalSourceManifest) :
    (manifest.entries.map GlobalNonDescriptorSourceMeaningEntry.provision).Nodup := by
  rw [manifest.provisions_exact]
  exact globalNonDescriptorProvisions_nodup

theorem entry_exists_exact
    (manifest : GlobalNonDescriptorCanonicalSourceManifest)
    (provision : IUPACNormativeProvision) :
    provision ∈ globalNonDescriptorProvisions ↔
      ∃ entry ∈ manifest.entries, entry.provision = provision := by
  rw [← manifest.provisions_exact, List.mem_map]

theorem entry_unique
    (manifest : GlobalNonDescriptorCanonicalSourceManifest)
    {left right : GlobalNonDescriptorSourceMeaningEntry}
    (leftMember : left ∈ manifest.entries)
    (rightMember : right ∈ manifest.entries)
    (sameProvision : left.provision = right.provision) :
    left = right := by
  exact List.inj_on_of_nodup_map manifest.entryProvisions_nodup
    leftMember rightMember sameProvision

/-- The unique manifest entry for a canonical non-descriptor provision. -/
noncomputable def entryFor
    (manifest : GlobalNonDescriptorCanonicalSourceManifest)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    GlobalNonDescriptorSourceMeaningEntry := by
  classical
  exact Classical.choose
    ((manifest.entry_exists_exact provision).1 (by simpa using member))

theorem entryFor_mem
    (manifest : GlobalNonDescriptorCanonicalSourceManifest)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    manifest.entryFor provision member ∈ manifest.entries := by
  classical
  exact (Classical.choose_spec
    ((manifest.entry_exists_exact provision).1 (by simpa using member))).1

@[simp] theorem entryFor_provision
    (manifest : GlobalNonDescriptorCanonicalSourceManifest)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    (manifest.entryFor provision member).provision = provision := by
  classical
  exact (Classical.choose_spec
    ((manifest.entry_exists_exact provision).1 (by simpa using member))).2

/-- Materialize the exact manifest as a total source-present program.  There is no default row:
every lookup is obtained from `entry_exists_exact`, and every nonvacuity proof is stored in that
exact entry. -/
noncomputable def toSourceReferenceProgram
    (manifest : GlobalNonDescriptorCanonicalSourceManifest) :
    GlobalNonDescriptorSourceReferenceProgram where
  sourceSuppliesRule := fun _provision _member => true
  reference := fun provision member => (manifest.entryFor provision member).reference
  sourcePresent_nonvacuous := by
    intro provision member _sourcePresent
    exact (manifest.entryFor provision member).admittedJudgment
  sourceAbsent_inapplicable := by
    intro provision member sourceAbsent
    simp at sourceAbsent

@[simp] theorem toSourceReferenceProgram_sourceSuppliesRule
    (manifest : GlobalNonDescriptorCanonicalSourceManifest)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    manifest.toSourceReferenceProgram.sourceSuppliesRule provision member = true :=
  rfl

@[simp] theorem toSourceReferenceProgram_reference
    (manifest : GlobalNonDescriptorCanonicalSourceManifest)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    manifest.toSourceReferenceProgram.reference provision member =
      (manifest.entryFor provision member).reference :=
  rfl

theorem toSourceReferenceProgram_reference_nonvacuous
    (manifest : GlobalNonDescriptorCanonicalSourceManifest)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    ∃ input, ∃ observation :
        (manifest.toSourceReferenceProgram.reference provision member).toReference.Observation,
      AuthoritativeChemicalInput.StructurallyWellFormed input ∧
        (manifest.toSourceReferenceProgram.reference provision member).toReference.Applicable input ∧
          (manifest.toSourceReferenceProgram.reference provision member).toReference.Judges
            input observation :=
  (manifest.entryFor provision member).admittedJudgment




structure CompletedSourceAudits where
  complete : ∀ (provision : IUPACNormativeProvision)
    (_member : provision ∈ globalNonDescriptorProvisions.toFinset),
      IUPACNormativeSource.ProvisionAuditComplete provision.source

/-- Assemble reviewed semantics only after both independent proof-carrying inputs exist. -/
noncomputable def toReviewedSemantics
    (manifest : GlobalNonDescriptorCanonicalSourceManifest)
    (audits : CompletedSourceAudits) :
    GlobalNonDescriptorReviewedSemantics :=
  manifest.toSourceReferenceProgram.toReviewedSemantics audits.complete

@[simp] theorem toReviewedSemantics_sourcePresent
    (manifest : GlobalNonDescriptorCanonicalSourceManifest)
    (audits : CompletedSourceAudits)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    ((manifest.toReviewedSemantics audits).reviewed.row provision member).sourceSuppliesRule =
      true :=
  rfl

@[simp] theorem toReviewedSemantics_reference_exact
    (manifest : GlobalNonDescriptorCanonicalSourceManifest)
    (audits : CompletedSourceAudits)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset) :
    ((manifest.toReviewedSemantics audits).reviewed.row provision member).reference =
      (manifest.entryFor provision member).reference.toReference :=
  rfl

end GlobalNonDescriptorCanonicalSourceManifest
end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCanonicalSourceManifest.entryProvisions_nodup
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCanonicalSourceManifest.entry_exists_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCanonicalSourceManifest.entryFor_provision
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCanonicalSourceManifest.toSourceReferenceProgram_reference_nonvacuous
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCanonicalSourceManifest.toReviewedSemantics_sourcePresent
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSourceMeaningBatch.append
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorSourceMeaningBatch.toCanonical
