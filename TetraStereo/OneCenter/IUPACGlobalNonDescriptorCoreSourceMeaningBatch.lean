import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCoreAuxiliarySourceEntries
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorGraphicalSourceMeaningBatch

set_option autoImplicit false

/-!
# Exact 92-row core-negative source-meaning batch

This module composes the eight P-90/P-91 rows, all 82 graphical rows, and the two IR-9 rows in
their literal canonical source order.  The resulting batch is exactly the complete
descriptor-assignment-negative portion of the 244-row core manifest.  Every entry retains the
independent source relation and concrete admitted judgment carried by its owning batch.

This is not the final 2,300-row manifest: the 2,208 parameterized-source rows remain a separate
source-transcription boundary, and `GlobalNonDescriptorSourceMeaningBatch.toCanonical` cannot be
invoked here.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

namespace GlobalNonDescriptorCoreSourceMeaning

open GlobalNonDescriptorCoreAuxiliarySourceRow

/-- Canonical core-negative order: P-90, P-91, graphical ST-0--ST-6, then IR-9. -/
def provisions : List IUPACNormativeProvision :=
  leadingProvisions ++ sourceProvisions .graphicalRepresentation2006 ++ trailingProvisions

/-- Literal proof-carrying composition; no row is selected, merged, or synthesized here. -/
def batch : GlobalNonDescriptorSourceMeaningBatch provisions :=
  (leadingBatch.append GlobalNonDescriptorGraphicalSourceMeaning.batch).append trailingBatch

@[simp] theorem batch_entries :
    batch.entries = leadingEntries ++
      GlobalNonDescriptorGraphicalSourceMeaning.entries ++ trailingEntries :=
  rfl

/-- Strategic exactness theorem: this batch closes every operation-negative row in the frozen
244-row core, not merely a hand-selected source sample. -/
theorem provisions_eq_core_negative :
    provisions = coreProvisions.filter (fun provision => !descriptorAssignmentBearing? provision) :=
  by decide

@[simp] theorem provision_count : provisions.length = 92 := by
  simp [provisions, leadingProvisions, trailingProvisions]

@[simp] theorem entry_count : batch.entries.length = 92 := by
  rw [batch.entries_length, provision_count]

theorem provisions_nodup : provisions.Nodup := by
  decide

/-- The exact provision map inherited from the dependent batch index. -/
theorem entry_provisions_exact :
    batch.entries.map GlobalNonDescriptorSourceMeaningEntry.provision = provisions :=
  batch.provisions_exact



theorem source_audit_complete
    (provision : IUPACNormativeProvision) (member : provision ∈ provisions) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  simp only [provisions, List.mem_append] at member
  rcases member with (leadingMember | graphicalMember) | trailingMember
  · rw [← GlobalNonDescriptorCoreAuxiliarySourceRow.leading_entry_provisions_exact]
      at leadingMember
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp leadingMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp entryMember
    exact GlobalNonDescriptorCoreAuxiliarySourceRow.source_audit_complete row
  · have sourceExact : provision.source = .graphicalRepresentation2006 :=
      (mem_sourceProvisions_iff provision .graphicalRepresentation2006).1 graphicalMember
    rw [sourceExact]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · rw [← GlobalNonDescriptorCoreAuxiliarySourceRow.trailing_entry_provisions_exact]
      at trailingMember
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp trailingMember
    obtain ⟨row, _rowMember, rfl⟩ := List.mem_map.mp entryMember
    exact GlobalNonDescriptorCoreAuxiliarySourceRow.source_audit_complete row

/-- Each exact row has an independently typed source-meaning reference and a concrete admitted
judgment.  This is a projection of stored proof data, not a new nonvacuity assumption. -/
theorem every_entry_nonvacuous
    (entry : GlobalNonDescriptorSourceMeaningEntry) (_member : entry ∈ batch.entries) :
    ∃ input, ∃ observation : entry.reference.toReference.Observation,
      input.StructurallyWellFormed ∧
        entry.reference.toReference.Applicable input ∧
          entry.reference.toReference.Judges input observation :=
  entry.admittedJudgment

end GlobalNonDescriptorCoreSourceMeaning

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCoreSourceMeaning.provisions_eq_core_negative
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCoreSourceMeaning.entry_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCoreSourceMeaning.source_audit_complete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.GlobalNonDescriptorCoreSourceMeaning.every_entry_nonvacuous
