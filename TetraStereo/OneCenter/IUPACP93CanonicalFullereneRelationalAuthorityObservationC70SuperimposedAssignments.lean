import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalAuthorityObservationC70SuperimposedPhysical

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Assignment and corpus certificates for the relational P-93 C70 superimposed observation. -/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

theorem iupacP93CanonicalFullereneC70SuperimposedAssignmentAudited
    (assignment : P93RelationalFullereneSubstituentCIPAssignment)
    (assignmentPresent : assignment ∈
      iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments) :
    iupacP93RelationalFullereneAuditedAssignment
      iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
      iupacP93CanonicalFullereneC70SuperimposedMolecule
      iupacP93CanonicalFullereneC70SuperimposedRelationalInput
      assignment.owner assignment.unit assignment.citation assignment.descriptor := by
  refine ⟨iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow, ?_, ?_,
    assignment, ?_, rfl, rfl, rfl, rfl⟩
  · simp [iupacP93CanonicalFullereneRelationalAuthorityAuditRows]
  · exact ⟨⟨rfl, rfl⟩, by
      simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow]⟩
  · simpa [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow] using
      assignmentPresent

theorem iupacP93CanonicalFullereneC70SuperimposedOwnerZeroExact
    (valid : 0 < iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends.length) :
    iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends.get ⟨0, valid⟩ =
      iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledPlacedAddend 0
        iupacP93CanonicalFullereneC70SuperimposedFirstPlacement.toPlaced := by
  simp [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.2]

theorem iupacP93CanonicalFullereneC70SuperimposedOwnerOneExact
    (valid : 1 < iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends.length) :
    iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends.get ⟨1, valid⟩ =
      iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledPlacedAddend 1
        iupacP93CanonicalFullereneC70SuperimposedSecondPlacement.toPlaced := by
  simp [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.2]

theorem iupacP93CanonicalFullereneC70SuperimposedAssignmentsValid :
    ∀ assignment ∈ iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments,
      assignment.ValidFor iupacP93CanonicalFullereneRelationalAuthorityPolicy
        iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
        iupacP93CanonicalFullereneC70SuperimposedMolecule
        iupacP93CanonicalFullereneC70SuperimposedRelationalInput := by
  intro assignment assignmentPresent
  have audited := iupacP93CanonicalFullereneC70SuperimposedAssignmentAudited
    assignment assignmentPresent
  have eligible :
      iupacP93CanonicalFullereneRelationalAuthorityPolicy.SubstituentUnitInAddendEligible
        iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
        iupacP93CanonicalFullereneC70SuperimposedMolecule
        iupacP93CanonicalFullereneC70SuperimposedRelationalInput assignment.owner assignment.unit :=
    ⟨assignment.citation, assignment.descriptor, audited⟩
  have citationAuthorized :
      iupacP93CanonicalFullereneRelationalAuthorityPolicy.SubstituentCitationAuthorized
        iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
        iupacP93CanonicalFullereneC70SuperimposedMolecule
        iupacP93CanonicalFullereneC70SuperimposedRelationalInput assignment.owner
        assignment.citation assignment.unit :=
    ⟨assignment.descriptor, audited⟩
  have descriptorAuthorized :
      iupacP93CanonicalFullereneRelationalAuthorityPolicy.SubstituentDescriptorAuthorized
        iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
        iupacP93CanonicalFullereneC70SuperimposedMolecule
        iupacP93CanonicalFullereneC70SuperimposedRelationalInput assignment.owner assignment.unit
        assignment.descriptor :=
    ⟨assignment.citation, audited⟩
  simp only [iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments,
    iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit,
    IUPACP93RelationalFullereneLocalCenterAudit.compile, List.map_cons, List.map_nil,
    List.mem_cons, List.not_mem_nil, or_false] at assignmentPresent
  rcases assignmentPresent with rfl | rfl | rfl | rfl
  · refine ⟨?_, ?_, iupacP93CanonicalFullereneC70SuperimposedCenter74PhysicalValid,
      eligible, trivial, by simp [P93AuthorityCitationToken.Valid,
        iupacP93RelationalFullereneOneCitation], citationAuthorized, descriptorAuthorized⟩
    · change _ ∈ iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledChiralAddends
      rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.2]
      exact List.mem_toFinset.mpr (List.get_mem _ _)
    · simp only [P93RelationalFullereneSubstituentAtomCarrier, Finset.singleton_subset_iff]
      rw [iupacP93CanonicalFullereneC70SuperimposedOwnerZeroExact]
      change 74 ∈ Finset.Ico 70 97
      decide
  · refine ⟨?_, ?_, iupacP93CanonicalFullereneC70SuperimposedCenter87PhysicalValid,
      eligible, trivial, by simp [P93AuthorityCitationToken.Valid,
        iupacP93RelationalFullereneOneCitation], citationAuthorized, descriptorAuthorized⟩
    · change _ ∈ iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledChiralAddends
      rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.2]
      exact List.mem_toFinset.mpr (List.get_mem _ _)
    · simp only [P93RelationalFullereneSubstituentAtomCarrier, Finset.singleton_subset_iff]
      rw [iupacP93CanonicalFullereneC70SuperimposedOwnerZeroExact]
      change 87 ∈ Finset.Ico 70 97
      decide
  · refine ⟨?_, ?_, iupacP93CanonicalFullereneC70SuperimposedCenter101PhysicalValid,
      eligible, trivial, by simp [P93AuthorityCitationToken.Valid,
        iupacP93RelationalFullereneOneCitation], citationAuthorized, descriptorAuthorized⟩
    · change _ ∈ iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledChiralAddends
      rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.2]
      exact List.mem_toFinset.mpr (List.get_mem _ _)
    · simp only [P93RelationalFullereneSubstituentAtomCarrier, Finset.singleton_subset_iff]
      rw [iupacP93CanonicalFullereneC70SuperimposedOwnerOneExact]
      change 101 ∈ Finset.Ico 97 124
      decide
  · refine ⟨?_, ?_, iupacP93CanonicalFullereneC70SuperimposedCenter114PhysicalValid,
      eligible, trivial, by simp [P93AuthorityCitationToken.Valid,
        iupacP93RelationalFullereneOneCitation], citationAuthorized, descriptorAuthorized⟩
    · change _ ∈ iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledChiralAddends
      rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.2]
      exact List.mem_toFinset.mpr (List.get_mem _ _)
    · simp only [P93RelationalFullereneSubstituentAtomCarrier, Finset.singleton_subset_iff]
      rw [iupacP93CanonicalFullereneC70SuperimposedOwnerOneExact]
      change 114 ∈ Finset.Ico 97 124
      decide

theorem iupacP93CanonicalFullereneC70SuperimposedAuditRow_eq
    (row : IUPACP93RelationalFullereneAuthorityAuditRow)
    (rowPresent : row ∈ iupacP93CanonicalFullereneRelationalAuthorityAuditRows)
    (rowMatches : row.MatchesSymmetryInput
      iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
      iupacP93CanonicalFullereneC70SuperimposedMolecule
      iupacP93CanonicalFullereneC70SuperimposedRelationalInput) :
    row = iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow := by
  simp only [iupacP93CanonicalFullereneRelationalAuthorityAuditRows,
    iupacP93CanonicalFullereneRelationalSourceAudit_rows,
    List.mem_cons, List.not_mem_nil, or_false] at rowPresent
  rcases rowPresent with rfl | rfl | rfl | rfl | rfl
  · exfalso
    exact (by decide :
      iupacP93CanonicalFullereneC70SuperimposedMolecule.atomCount ≠
        iupacP93CanonicalFullereneC76Type1Molecule.atomCount)
      (congrArg RawMolecule.atomCount rowMatches.1.2)
  · exfalso
    exact (by decide :
      iupacP93CanonicalFullereneC70SuperimposedMolecule.atomCount ≠
        iupacP93CanonicalFullereneC60Type2Molecule.atomCount)
      (congrArg RawMolecule.atomCount rowMatches.1.2)
  · exfalso
    exact (by decide :
      iupacP93CanonicalFullereneC70SuperimposedMolecule.atomCount ≠
        iupacP93CanonicalFullereneC60Type3Molecule.atomCount)
      (congrArg RawMolecule.atomCount rowMatches.1.2)
  · exfalso
    exact iupacP93CanonicalFullereneC70Type4Molecule_ne_superimposed rowMatches.1.2.symm
  · rfl

theorem iupacP93CanonicalFullereneC70SuperimposedSubstituentCorpusComplete :
    P93RelationalFullereneSubstituentCIPAssignmentsComplete
      iupacP93CanonicalFullereneRelationalAuthorityPolicy
      iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
      iupacP93CanonicalFullereneC70SuperimposedMolecule
      iupacP93CanonicalFullereneC70SuperimposedRelationalInput
      iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments := by
  refine ⟨?_, iupacP93CanonicalFullereneC70SuperimposedAssignmentsValid, ?_, ?_⟩
  · simp [iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments,
      iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit,
      IUPACP93RelationalFullereneLocalCenterAudit.compile]
  · intro owner ownerChiral
    change owner ∈
      iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledChiralAddends at ownerChiral
    rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.2,
      iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.2] at ownerChiral
    simp at ownerChiral
    rcases ownerChiral with rfl | rfl
    · refine ⟨(iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit.get
        ⟨0, by decide⟩).compile, ?_, rfl⟩
      simp [iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments,
        iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit]
    · refine ⟨(iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit.get
        ⟨2, by decide⟩).compile, ?_, rfl⟩
      simp [iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments,
        iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit]
  · intro owner ownerChiral unit eligible
    change ∃ citation descriptor,
      iupacP93RelationalFullereneAuditedAssignment
        iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
        iupacP93CanonicalFullereneC70SuperimposedMolecule
        iupacP93CanonicalFullereneC70SuperimposedRelationalInput owner unit citation descriptor
        at eligible
    obtain ⟨citation, descriptor, row, rowPresent, rowMatches, assignment,
      assignmentPresent, ownerEq, unitEq, _citationEq, _descriptorEq⟩ := eligible
    have rowEq := iupacP93CanonicalFullereneC70SuperimposedAuditRow_eq
      row rowPresent rowMatches
    subst row
    exact ⟨assignment, by
      simpa [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow] using
        assignmentPresent,
      ownerEq, unitEq⟩


end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
