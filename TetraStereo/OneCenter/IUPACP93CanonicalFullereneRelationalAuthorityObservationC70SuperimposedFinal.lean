import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalAuthorityObservationC70SuperimposedAssignments

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Final validity certificate for the relational P-93 C70 superimposed observation. -/

namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

theorem iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation_valid :
    iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation.ValidFor
      iupacP93CanonicalFullereneRelationalAuthorityPolicy
      iupacP93CanonicalFullereneC70SuperimposedAuthoritySource := by
  refine
    { handedValid := ?_
      substitutionPatternClass := by
        simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation,
          iupacP93CanonicalFullereneC70SuperimposedLocalAssignment]
      chiralAddendsNonempty := ?_
      complete := ⟨rfl, rfl⟩ }
  · refine { baseValid := ?_, handedClass := ?_, payloadPresent := ?_, printedObserved := ?_ }
    · refine
        { structureAgreement := iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.2
          moleculeObserved := ?_
          inputsNonempty := by
            simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation]
          inputFamilyObserved := ?_
          inputsObserved := ?_
          inputsExteriorFaceSenseObserved := ?_
          inputsOriginalDerivativeChiralityObserved := ?_
          inputsChiralAddendsObserved := ?_
          selectedInputPresent := by
            simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation]
          selectedInputJudged :=
            iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput_judged
          exteriorFaceSenseObserved := ?_
          originalDerivativeChiralityObserved := ?_
          chiralAddendsObserved := ?_
          addendsExact := rfl
          chiralAddendsExact := rfl
          localAssignmentJudged :=
            iupacP93CanonicalFullereneC70SuperimposedLocalAssignment_judged
          assignmentComplete :=
            iupacP93CanonicalFullereneC70SuperimposedAuthorityAssignment_judged
          substituentCorpusComplete :=
            iupacP93CanonicalFullereneC70SuperimposedSubstituentCorpusComplete }
      · refine ⟨iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow, ?_, ?_⟩
        · simp
        · exact ⟨rfl, rfl⟩
      · refine ⟨iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
          ?_, ?_, rfl, ?_⟩
        · simp
        · exact ⟨rfl, rfl⟩
        · simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation,
            iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow]
      · intro input inputPresent
        simp only [iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation,
          List.mem_singleton] at inputPresent
        subst input
        refine ⟨iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow, ?_, ?_, rfl⟩
        · simp
        · exact ⟨⟨rfl, rfl⟩,
            iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput, by
              simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow], by
              simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow]⟩
      · intro input inputPresent
        simp only [iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation,
          List.mem_singleton] at inputPresent
        subst input
        refine ⟨iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
          ?_, ?_, rfl, ?_⟩
        · simp
        · exact ⟨rfl, rfl⟩
        · exact ⟨_, rfl, by
            simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow]⟩
      · intro input inputPresent
        simp only [iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation,
          List.mem_singleton] at inputPresent
        subst input
        refine ⟨iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow, ?_, ?_, rfl⟩
        · simp
        · exact ⟨⟨rfl, rfl⟩, by
            simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
              iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput]⟩
      · intro input inputPresent
        simp only [iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation,
          List.mem_singleton] at inputPresent
        subst input
        refine ⟨iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow, ?_, ?_, rfl⟩
        · simp
        · exact ⟨⟨rfl, rfl⟩, by
            simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
              iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput]⟩
      · refine ⟨iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
          ?_, ?_, rfl, ?_⟩
        · simp
        · exact ⟨rfl, rfl⟩
        · exact ⟨_, rfl, by
            simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
              iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation]⟩
      · refine ⟨iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow, ?_, ?_, rfl⟩
        · simp
        · exact ⟨⟨rfl, rfl⟩, by
            simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
              iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation,
              iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput]⟩
      · refine ⟨iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow, ?_, ?_, rfl⟩
        · simp
        · exact ⟨⟨rfl, rfl⟩, by
            simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
              iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation,
              iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput]⟩
    · simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation,
        iupacP93CanonicalFullereneC70SuperimposedLocalAssignment]
    · simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation,
        iupacP93CanonicalFullereneC70SuperimposedLocalAssignment]
    · refine ⟨iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
        ?_, ?_, rfl, ?_⟩
      · simp
      · exact ⟨rfl, rfl⟩
      · exact ⟨_, rfl, by
          simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
            iupacP93CanonicalFullereneC70SuperimposedAuthorityObservation]⟩
  · change iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledChiralAddends.Nonempty
    rw [iupacP93CanonicalFullereneDerivativeCompiledChiralAddends_exact.2.2.2.2,
      iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.2]
    simp

end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
