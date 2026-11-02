import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalAuthorityObservationC70Type4Assignments

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Final validity certificate for the relational P-93 C70 type-4 observation. -/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

private theorem iupacP93CanonicalFullereneC70Type4AuditRow_eq
    (row : IUPACP93RelationalFullereneAuthorityAuditRow)
    (rowPresent : row ∈ iupacP93CanonicalFullereneRelationalAuthorityAuditRows)
    (rowMatches : row.MatchesSymmetryInput
      iupacP93CanonicalFullereneC70Type4AuthoritySource
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC70Type4RelationalInput) :
    row = iupacP93CanonicalFullereneC70Type4AuthorityAuditRow := by
  simp only [iupacP93CanonicalFullereneRelationalAuthorityAuditRows,
    iupacP93CanonicalFullereneRelationalSourceAudit_rows,
    List.mem_cons, List.not_mem_nil, or_false] at rowPresent
  rcases rowPresent with rfl | rfl | rfl | rfl | rfl
  · exfalso
    exact (by decide :
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.atomCount ≠
        iupacP93CanonicalFullereneC76Type1Molecule.atomCount)
      (congrArg RawMolecule.atomCount rowMatches.1.2)
  · exfalso
    exact (by decide :
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.atomCount ≠
        iupacP93CanonicalFullereneC60Type2Molecule.atomCount)
      (congrArg RawMolecule.atomCount rowMatches.1.2)
  · exfalso
    exact (by decide :
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.atomCount ≠
        iupacP93CanonicalFullereneC60Type3Molecule.atomCount)
      (congrArg RawMolecule.atomCount rowMatches.1.2)
  · rfl
  · exfalso
    exact iupacP93CanonicalFullereneC70Type4Molecule_ne_superimposed rowMatches.1.2

private theorem iupacP93CanonicalFullereneC70Type4SubstituentCorpusComplete :
    P93RelationalFullereneSubstituentCIPAssignmentsComplete
      iupacP93CanonicalFullereneRelationalAuthorityPolicy
      iupacP93CanonicalFullereneC70Type4AuthoritySource
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC70Type4RelationalInput
      iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments := by
  refine ⟨?_, iupacP93CanonicalFullereneC70Type4AssignmentsValid, ?_, ?_⟩
  · simp [iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments,
      iupacP93CanonicalFullereneC70Type4LocalCIPAudit,
      IUPACP93RelationalFullereneLocalCenterAudit.compile]
  · intro owner ownerChiral
    change owner ∈ iupacP93CanonicalFullereneC70Type4Assembly.compiledChiralAddends at ownerChiral
    rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.1,
      iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.1] at ownerChiral
    simp at ownerChiral
    rcases ownerChiral with rfl | rfl
    · refine ⟨(iupacP93CanonicalFullereneC70Type4LocalCIPAudit.get ⟨0, by decide⟩).compile,
        ?_, rfl⟩
      simp [iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments,
        iupacP93CanonicalFullereneC70Type4LocalCIPAudit]
    · refine ⟨(iupacP93CanonicalFullereneC70Type4LocalCIPAudit.get ⟨2, by decide⟩).compile,
        ?_, rfl⟩
      simp [iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments,
        iupacP93CanonicalFullereneC70Type4LocalCIPAudit]
  · intro owner ownerChiral unit eligible
    change ∃ citation descriptor,
      iupacP93RelationalFullereneAuditedAssignment
        iupacP93CanonicalFullereneC70Type4AuthoritySource
        iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
        iupacP93CanonicalFullereneC70Type4RelationalInput owner unit citation descriptor at eligible
    obtain ⟨citation, descriptor, row, rowPresent, rowMatches, assignment,
      assignmentPresent, ownerEq, unitEq, _citationEq, _descriptorEq⟩ := eligible
    have rowEq := iupacP93CanonicalFullereneC70Type4AuditRow_eq row rowPresent rowMatches
    subst row
    exact ⟨assignment, by
      simpa [iupacP93CanonicalFullereneC70Type4AuthorityAuditRow] using assignmentPresent,
      ownerEq, unitEq⟩

theorem iupacP93CanonicalFullereneC70Type4AuthorityObservation_valid :
    iupacP93CanonicalFullereneC70Type4AuthorityObservation.ValidFor
      iupacP93CanonicalFullereneRelationalAuthorityPolicy
      iupacP93CanonicalFullereneC70Type4AuthoritySource := by
  refine
    { structureAgreement := iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.1
      moleculeObserved := ?_
      inputObserved := ?_
      inputJudged := iupacP93CanonicalFullereneC70Type4RelationalInput_judged
      originalDerivativeChiralityObserved := ?_
      chiralAddendsObserved := ?_
      localAssignmentJudged := iupacP93CanonicalFullereneC70Type4LocalAssignment_judged
      typeFour := rfl
      cipPayloadPresent := by simp [iupacP93CanonicalFullereneC70Type4AuthorityObservation,
        iupacP93CanonicalFullereneC70Type4LocalAssignment]
      numberingAbsent := rfl
      turnAbsent := rfl
      chiralAddendsNonempty := ?_
      substituentCorpusComplete := iupacP93CanonicalFullereneC70Type4SubstituentCorpusComplete }
  · refine ⟨iupacP93CanonicalFullereneC70Type4AuthorityAuditRow, ?_, ?_⟩
    · simp
    · exact ⟨rfl, rfl⟩
  · refine ⟨iupacP93CanonicalFullereneC70Type4AuthorityAuditRow, ?_, ?_, rfl⟩
    · simp
    · exact ⟨⟨rfl, rfl⟩, by
        simp [iupacP93CanonicalFullereneC70Type4AuthorityAuditRow,
          iupacP93CanonicalFullereneC70Type4AuthorityObservation]⟩
  · refine ⟨iupacP93CanonicalFullereneC70Type4AuthorityAuditRow, ?_, ?_, rfl⟩
    · simp
    · exact ⟨⟨rfl, rfl⟩, by
        simp [iupacP93CanonicalFullereneC70Type4AuthorityAuditRow,
          iupacP93CanonicalFullereneC70Type4AuthorityObservation]⟩
  · refine ⟨iupacP93CanonicalFullereneC70Type4AuthorityAuditRow, ?_, ?_, rfl⟩
    · simp
    · exact ⟨⟨rfl, rfl⟩, by
        simp [iupacP93CanonicalFullereneC70Type4AuthorityAuditRow,
          iupacP93CanonicalFullereneC70Type4AuthorityObservation]⟩
  · change iupacP93CanonicalFullereneC70Type4Assembly.compiledChiralAddends.Nonempty
    rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.1,
      iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.1]
    simp

end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
