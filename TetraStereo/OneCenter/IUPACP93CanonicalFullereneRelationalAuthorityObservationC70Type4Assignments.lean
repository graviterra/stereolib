import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalAuthorityObservationC70Type4Physical

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Assignment certificates for the relational P-93 C70 type-4 observation. -/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

theorem iupacP93CanonicalFullereneC70Type4AssignmentAudited
    (assignment : P93RelationalFullereneSubstituentCIPAssignment)
    (assignmentPresent : assignment ∈
      iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments) :
    iupacP93RelationalFullereneAuditedAssignment
      iupacP93CanonicalFullereneC70Type4AuthoritySource
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC70Type4RelationalInput
      assignment.owner assignment.unit assignment.citation assignment.descriptor := by
  refine ⟨iupacP93CanonicalFullereneC70Type4AuthorityAuditRow, ?_, ?_,
    assignment, ?_, rfl, rfl, rfl, rfl⟩
  · simp [iupacP93CanonicalFullereneRelationalAuthorityAuditRows]
  · exact ⟨⟨rfl, rfl⟩, by
      simp [iupacP93CanonicalFullereneC70Type4AuthorityAuditRow]⟩
  · simpa [iupacP93CanonicalFullereneC70Type4AuthorityAuditRow] using assignmentPresent

theorem iupacP93CanonicalFullereneC70Type4OwnerZeroExact
    (valid : 0 < iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends.length) :
    iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends.get ⟨0, valid⟩ =
      iupacP93CanonicalFullereneC70Type4Assembly.compiledPlacedAddend 0
        iupacP93CanonicalFullereneC70Type4FirstPlacement.toPlaced := by
  simp [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.1]

theorem iupacP93CanonicalFullereneC70Type4OwnerOneExact
    (valid : 1 < iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends.length) :
    iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends.get ⟨1, valid⟩ =
      iupacP93CanonicalFullereneC70Type4Assembly.compiledPlacedAddend 1
        iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced := by
  simp [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.1]

theorem iupacP93CanonicalFullereneC70Type4AssignmentsValid :
    ∀ assignment ∈ iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments,
      assignment.ValidFor iupacP93CanonicalFullereneRelationalAuthorityPolicy
        iupacP93CanonicalFullereneC70Type4AuthoritySource
        iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
        iupacP93CanonicalFullereneC70Type4RelationalInput := by
  intro assignment assignmentPresent
  have audited := iupacP93CanonicalFullereneC70Type4AssignmentAudited
    assignment assignmentPresent
  have eligible :
      iupacP93CanonicalFullereneRelationalAuthorityPolicy.SubstituentUnitInAddendEligible
        iupacP93CanonicalFullereneC70Type4AuthoritySource
        iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
        iupacP93CanonicalFullereneC70Type4RelationalInput assignment.owner assignment.unit :=
    ⟨assignment.citation, assignment.descriptor, audited⟩
  have citationAuthorized :
      iupacP93CanonicalFullereneRelationalAuthorityPolicy.SubstituentCitationAuthorized
        iupacP93CanonicalFullereneC70Type4AuthoritySource
        iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
        iupacP93CanonicalFullereneC70Type4RelationalInput assignment.owner
        assignment.citation assignment.unit :=
    ⟨assignment.descriptor, audited⟩
  have descriptorAuthorized :
      iupacP93CanonicalFullereneRelationalAuthorityPolicy.SubstituentDescriptorAuthorized
        iupacP93CanonicalFullereneC70Type4AuthoritySource
        iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
        iupacP93CanonicalFullereneC70Type4RelationalInput assignment.owner assignment.unit
        assignment.descriptor :=
    ⟨assignment.citation, audited⟩
  simp only [iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments,
    iupacP93CanonicalFullereneC70Type4LocalCIPAudit,
    IUPACP93RelationalFullereneLocalCenterAudit.compile, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at assignmentPresent
  rcases assignmentPresent with rfl | rfl | rfl | rfl
  · refine ⟨?_, ?_, iupacP93CanonicalFullereneC70Type4Center74PhysicalValid,
      eligible, trivial, by simp [P93AuthorityCitationToken.Valid,
        iupacP93RelationalFullereneOneCitation], citationAuthorized, descriptorAuthorized⟩
    · change _ ∈ iupacP93CanonicalFullereneC70Type4Assembly.compiledChiralAddends
      rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.1]
      exact List.mem_toFinset.mpr (List.get_mem _ _)
    · simp only [P93RelationalFullereneSubstituentAtomCarrier, Finset.singleton_subset_iff]
      rw [iupacP93CanonicalFullereneC70Type4OwnerZeroExact]
      change 74 ∈ Finset.Ico 70 97
      decide
  · refine ⟨?_, ?_, iupacP93CanonicalFullereneC70Type4Center87PhysicalValid,
      eligible, trivial, by simp [P93AuthorityCitationToken.Valid,
        iupacP93RelationalFullereneOneCitation], citationAuthorized, descriptorAuthorized⟩
    · change _ ∈ iupacP93CanonicalFullereneC70Type4Assembly.compiledChiralAddends
      rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.1]
      exact List.mem_toFinset.mpr (List.get_mem _ _)
    · simp only [P93RelationalFullereneSubstituentAtomCarrier, Finset.singleton_subset_iff]
      rw [iupacP93CanonicalFullereneC70Type4OwnerZeroExact]
      change 87 ∈ Finset.Ico 70 97
      decide
  · refine ⟨?_, ?_, iupacP93CanonicalFullereneC70Type4Center101PhysicalValid,
      eligible, trivial, by simp [P93AuthorityCitationToken.Valid,
        iupacP93RelationalFullereneOneCitation], citationAuthorized, descriptorAuthorized⟩
    · change _ ∈ iupacP93CanonicalFullereneC70Type4Assembly.compiledChiralAddends
      rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.1]
      exact List.mem_toFinset.mpr (List.get_mem _ _)
    · simp only [P93RelationalFullereneSubstituentAtomCarrier, Finset.singleton_subset_iff]
      rw [iupacP93CanonicalFullereneC70Type4OwnerOneExact]
      change 101 ∈ Finset.Ico 97 124
      decide
  · refine ⟨?_, ?_, iupacP93CanonicalFullereneC70Type4Center114PhysicalValid,
      eligible, trivial, by simp [P93AuthorityCitationToken.Valid,
        iupacP93RelationalFullereneOneCitation], citationAuthorized, descriptorAuthorized⟩
    · change _ ∈ iupacP93CanonicalFullereneC70Type4Assembly.compiledChiralAddends
      rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.1]
      exact List.mem_toFinset.mpr (List.get_mem _ _)
    · simp only [P93RelationalFullereneSubstituentAtomCarrier, Finset.singleton_subset_iff]
      rw [iupacP93CanonicalFullereneC70Type4OwnerOneExact]
      change 114 ∈ Finset.Ico 97 124
      decide



end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
