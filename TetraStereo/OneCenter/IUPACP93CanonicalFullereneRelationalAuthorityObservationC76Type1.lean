import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalAuthorityObservationFoundation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Bounded validity proof for the relational P-93 C76 type-1 observation. -/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

private theorem iupacP93CanonicalFullereneC76Type1SubstituentCorpusComplete :
    P93RelationalFullereneSubstituentCIPAssignmentsComplete
      iupacP93CanonicalFullereneRelationalAuthorityPolicy
      iupacP93CanonicalFullereneC76Type1AuthoritySource
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC76Type1RelationalInput [] := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · simp
  · intro owner ownerChiral
    change owner ∈ iupacP93CanonicalFullereneC76Type1Assembly.compiledChiralAddends at ownerChiral
    rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.1] at ownerChiral
    simp at ownerChiral
  · intro owner ownerChiral
    change owner ∈ iupacP93CanonicalFullereneC76Type1Assembly.compiledChiralAddends at ownerChiral
    rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.1] at ownerChiral
    simp at ownerChiral

theorem iupacP93CanonicalFullereneC76Type1AuthorityObservation_valid :
    iupacP93CanonicalFullereneC76Type1AuthorityObservation.ValidFor
      iupacP93CanonicalFullereneRelationalAuthorityPolicy
      iupacP93CanonicalFullereneC76Type1AuthoritySource := by
  refine { baseValid := ?_, handedClass := ?_, payloadPresent := ?_, printedObserved := ?_ }
  · refine
      { structureAgreement := iupacP93CanonicalFullereneAuthoritySources_all_agree.1
        moleculeObserved := ?_
        inputsNonempty := by simp [iupacP93CanonicalFullereneC76Type1AuthorityObservation]
        inputFamilyObserved := ?_
        inputsObserved := ?_
        inputsExteriorFaceSenseObserved := ?_
        inputsOriginalDerivativeChiralityObserved := ?_
        inputsChiralAddendsObserved := ?_
        selectedInputPresent := by simp [iupacP93CanonicalFullereneC76Type1AuthorityObservation]
        selectedInputJudged := iupacP93CanonicalFullereneC76Type1RelationalSourceInput_judged
        exteriorFaceSenseObserved := ?_
        originalDerivativeChiralityObserved := ?_
        chiralAddendsObserved := ?_
        addendsExact := rfl
        chiralAddendsExact := rfl
        localAssignmentJudged := iupacP93CanonicalFullereneC76Type1LocalAssignment_judged
        assignmentComplete := iupacP93CanonicalFullereneC76Type1AuthorityAssignment_judged
        substituentCorpusComplete :=
          iupacP93CanonicalFullereneC76Type1SubstituentCorpusComplete }
    · refine ⟨iupacP93CanonicalFullereneC76Type1AuthorityAuditRow, ?_, ?_⟩
      · simp
      · exact ⟨rfl, rfl⟩
    · refine ⟨iupacP93CanonicalFullereneC76Type1AuthorityAuditRow, ?_, ?_, rfl, ?_⟩
      · simp
      · exact ⟨rfl, rfl⟩
      · simp [iupacP93CanonicalFullereneC76Type1AuthorityObservation,
          iupacP93CanonicalFullereneC76Type1AuthorityAuditRow]
    · intro input inputPresent
      simp only [iupacP93CanonicalFullereneC76Type1AuthorityObservation,
        List.mem_singleton] at inputPresent
      subst input
      refine ⟨iupacP93CanonicalFullereneC76Type1AuthorityAuditRow, ?_, ?_, rfl⟩
      · simp
      · exact ⟨⟨rfl, rfl⟩, iupacP93CanonicalFullereneC76Type1RelationalSourceInput, by
          simp [iupacP93CanonicalFullereneC76Type1AuthorityAuditRow], by
          simp [iupacP93CanonicalFullereneC76Type1AuthorityAuditRow]⟩
    · intro input inputPresent
      simp only [iupacP93CanonicalFullereneC76Type1AuthorityObservation,
        List.mem_singleton] at inputPresent
      subst input
      refine ⟨iupacP93CanonicalFullereneC76Type1AuthorityAuditRow, ?_, ?_, rfl, ?_⟩
      · simp
      · exact ⟨rfl, rfl⟩
      · exact ⟨_, rfl, by
          simp [iupacP93CanonicalFullereneC76Type1AuthorityAuditRow]⟩
    · intro input inputPresent
      simp only [iupacP93CanonicalFullereneC76Type1AuthorityObservation,
        List.mem_singleton] at inputPresent
      subst input
      refine ⟨iupacP93CanonicalFullereneC76Type1AuthorityAuditRow, ?_, ?_, rfl⟩
      · simp
      · exact ⟨⟨rfl, rfl⟩, by
          simp [iupacP93CanonicalFullereneC76Type1AuthorityAuditRow,
            iupacP93CanonicalFullereneC76Type1RelationalSourceInput]⟩
    · intro input inputPresent
      simp only [iupacP93CanonicalFullereneC76Type1AuthorityObservation,
        List.mem_singleton] at inputPresent
      subst input
      refine ⟨iupacP93CanonicalFullereneC76Type1AuthorityAuditRow, ?_, ?_, rfl⟩
      · simp
      · exact ⟨⟨rfl, rfl⟩, by
          simp [iupacP93CanonicalFullereneC76Type1AuthorityAuditRow,
            iupacP93CanonicalFullereneC76Type1RelationalSourceInput]⟩
    · refine ⟨iupacP93CanonicalFullereneC76Type1AuthorityAuditRow, ?_, ?_, rfl, ?_⟩
      · simp
      · exact ⟨rfl, rfl⟩
      · exact ⟨_, rfl, by
          simp [iupacP93CanonicalFullereneC76Type1AuthorityAuditRow,
            iupacP93CanonicalFullereneC76Type1AuthorityObservation]⟩
    · refine ⟨iupacP93CanonicalFullereneC76Type1AuthorityAuditRow, ?_, ?_, rfl⟩
      · simp
      · exact ⟨⟨rfl, rfl⟩, by
          simp [iupacP93CanonicalFullereneC76Type1AuthorityAuditRow,
            iupacP93CanonicalFullereneC76Type1AuthorityObservation,
            iupacP93CanonicalFullereneC76Type1RelationalSourceInput]⟩
    · refine ⟨iupacP93CanonicalFullereneC76Type1AuthorityAuditRow, ?_, ?_, rfl⟩
      · simp
      · exact ⟨⟨rfl, rfl⟩, by
          simp [iupacP93CanonicalFullereneC76Type1AuthorityAuditRow,
            iupacP93CanonicalFullereneC76Type1AuthorityObservation,
            iupacP93CanonicalFullereneC76Type1RelationalSourceInput]⟩
  · left
    rfl
  · simp [iupacP93CanonicalFullereneC76Type1AuthorityObservation,
      iupacP93CanonicalFullereneC76Type1LocalAssignment]
  · refine ⟨iupacP93CanonicalFullereneC76Type1AuthorityAuditRow, ?_, ?_, rfl, ?_⟩
    · simp
    · exact ⟨rfl, rfl⟩
    · exact ⟨_, rfl, by
        simp [iupacP93CanonicalFullereneC76Type1AuthorityAuditRow,
          iupacP93CanonicalFullereneC76Type1AuthorityObservation]⟩


end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
