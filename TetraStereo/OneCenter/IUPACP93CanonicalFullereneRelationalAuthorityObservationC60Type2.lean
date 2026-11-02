import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalAuthorityObservationFoundation

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Bounded validity proof for the relational P-93 C60 type-2 observation. -/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

private theorem iupacP93CanonicalFullereneC60Type2SubstituentCorpusComplete :
    P93RelationalFullereneSubstituentCIPAssignmentsComplete
      iupacP93CanonicalFullereneRelationalAuthorityPolicy
      iupacP93CanonicalFullereneC60Type2AuthoritySource
      iupacP93CanonicalFullereneC60Type2Molecule
      iupacP93CanonicalFullereneC60Type2RelationalInput [] := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · intro owner ownerChiral
    change owner ∈ iupacP93CanonicalFullereneC60Type2Assembly.compiledChiralAddends at ownerChiral
    rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.1] at ownerChiral
    simp at ownerChiral
  · intro owner ownerChiral
    change owner ∈ iupacP93CanonicalFullereneC60Type2Assembly.compiledChiralAddends at ownerChiral
    rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.1] at ownerChiral
    simp at ownerChiral

theorem iupacP93CanonicalFullereneC60Type2AuthorityObservation_valid :
    iupacP93CanonicalFullereneC60Type2AuthorityObservation.ValidFor
      iupacP93CanonicalFullereneRelationalAuthorityPolicy
      iupacP93CanonicalFullereneC60Type2AuthoritySource := by
  refine { baseValid := ?_, handedClass := ?_, payloadPresent := ?_, printedObserved := ?_ }
  · refine
      { structureAgreement := iupacP93CanonicalFullereneAuthoritySources_all_agree.2.1
        moleculeObserved := ?_
        inputsNonempty := by simp [iupacP93CanonicalFullereneC60Type2AuthorityObservation]
        inputFamilyObserved := ?_
        inputsObserved := ?_
        inputsExteriorFaceSenseObserved := ?_
        inputsOriginalDerivativeChiralityObserved := ?_
        inputsChiralAddendsObserved := ?_
        selectedInputPresent := by simp [iupacP93CanonicalFullereneC60Type2AuthorityObservation]
        selectedInputJudged := iupacP93CanonicalFullereneC60Type2RelationalSourceInput_judged
        exteriorFaceSenseObserved := ?_
        originalDerivativeChiralityObserved := ?_
        chiralAddendsObserved := ?_
        addendsExact := rfl
        chiralAddendsExact := rfl
        localAssignmentJudged := iupacP93CanonicalFullereneC60Type2LocalAssignment_judged
        assignmentComplete := iupacP93CanonicalFullereneC60Type2AuthorityAssignment_judged
        substituentCorpusComplete :=
          iupacP93CanonicalFullereneC60Type2SubstituentCorpusComplete }
    · refine ⟨iupacP93CanonicalFullereneC60Type2AuthorityAuditRow, ?_, ?_⟩
      · simp
      · exact ⟨rfl, rfl⟩
    · refine ⟨iupacP93CanonicalFullereneC60Type2AuthorityAuditRow, ?_, ?_, rfl, ?_⟩
      · simp
      · exact ⟨rfl, rfl⟩
      · simp [iupacP93CanonicalFullereneC60Type2AuthorityObservation,
          iupacP93CanonicalFullereneC60Type2AuthorityAuditRow]
    · intro input inputPresent
      simp only [iupacP93CanonicalFullereneC60Type2AuthorityObservation,
        List.mem_singleton] at inputPresent
      subst input
      refine ⟨iupacP93CanonicalFullereneC60Type2AuthorityAuditRow, ?_, ?_, rfl⟩
      · simp
      · exact ⟨⟨rfl, rfl⟩, iupacP93CanonicalFullereneC60Type2RelationalSourceInput, by
          simp [iupacP93CanonicalFullereneC60Type2AuthorityAuditRow], by
          simp [iupacP93CanonicalFullereneC60Type2AuthorityAuditRow]⟩
    · intro input inputPresent
      simp only [iupacP93CanonicalFullereneC60Type2AuthorityObservation,
        List.mem_singleton] at inputPresent
      subst input
      refine ⟨iupacP93CanonicalFullereneC60Type2AuthorityAuditRow, ?_, ?_, rfl, ?_⟩
      · simp
      · exact ⟨rfl, rfl⟩
      · exact ⟨_, rfl, by simp [iupacP93CanonicalFullereneC60Type2AuthorityAuditRow]⟩
    · intro input inputPresent
      simp only [iupacP93CanonicalFullereneC60Type2AuthorityObservation,
        List.mem_singleton] at inputPresent
      subst input
      refine ⟨iupacP93CanonicalFullereneC60Type2AuthorityAuditRow, ?_, ?_, rfl⟩
      · simp
      · exact ⟨⟨rfl, rfl⟩, by simp [iupacP93CanonicalFullereneC60Type2AuthorityAuditRow,
          iupacP93CanonicalFullereneC60Type2RelationalSourceInput]⟩
    · intro input inputPresent
      simp only [iupacP93CanonicalFullereneC60Type2AuthorityObservation,
        List.mem_singleton] at inputPresent
      subst input
      refine ⟨iupacP93CanonicalFullereneC60Type2AuthorityAuditRow, ?_, ?_, rfl⟩
      · simp
      · exact ⟨⟨rfl, rfl⟩, by simp [iupacP93CanonicalFullereneC60Type2AuthorityAuditRow,
          iupacP93CanonicalFullereneC60Type2RelationalSourceInput]⟩
    · refine ⟨iupacP93CanonicalFullereneC60Type2AuthorityAuditRow, ?_, ?_, rfl, ?_⟩
      · simp
      · exact ⟨rfl, rfl⟩
      · exact ⟨_, rfl, by simp [iupacP93CanonicalFullereneC60Type2AuthorityAuditRow,
          iupacP93CanonicalFullereneC60Type2AuthorityObservation]⟩
    · refine ⟨iupacP93CanonicalFullereneC60Type2AuthorityAuditRow, ?_, ?_, rfl⟩
      · simp
      · exact ⟨⟨rfl, rfl⟩, by simp [iupacP93CanonicalFullereneC60Type2AuthorityAuditRow,
          iupacP93CanonicalFullereneC60Type2AuthorityObservation,
          iupacP93CanonicalFullereneC60Type2RelationalSourceInput]⟩
    · refine ⟨iupacP93CanonicalFullereneC60Type2AuthorityAuditRow, ?_, ?_, rfl⟩
      · simp
      · exact ⟨⟨rfl, rfl⟩, by simp [iupacP93CanonicalFullereneC60Type2AuthorityAuditRow,
          iupacP93CanonicalFullereneC60Type2AuthorityObservation,
          iupacP93CanonicalFullereneC60Type2RelationalSourceInput]⟩
  · simp [iupacP93CanonicalFullereneC60Type2AuthorityObservation,
      iupacP93CanonicalFullereneC60Type2LocalAssignment]
  · simp [iupacP93CanonicalFullereneC60Type2AuthorityObservation,
      iupacP93CanonicalFullereneC60Type2LocalAssignment]
  · refine ⟨iupacP93CanonicalFullereneC60Type2AuthorityAuditRow, ?_, ?_, rfl, ?_⟩
    · simp
    · exact ⟨rfl, rfl⟩
    · exact ⟨_, rfl, by simp [iupacP93CanonicalFullereneC60Type2AuthorityAuditRow,
        iupacP93CanonicalFullereneC60Type2AuthorityObservation]⟩


end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
