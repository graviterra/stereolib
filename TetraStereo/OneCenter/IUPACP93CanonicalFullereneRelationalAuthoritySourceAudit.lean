import TetraStereo.OneCenter.IUPACP93CanonicalFullereneRelationalAuthoritySources
import TetraStereo.OneCenter.IUPACP93RelationalFullereneSourceAuditSchema
import TetraStereo.OneCenter.IUPACP93RelationalFullereneCIPMaterializer

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0










namespace TetraStereo.OneCenter
namespace P93CanonicalProgramFullerene

open BlueBookP93.Cyclic

noncomputable section

def iupacP93BlueBookP9Sha256 : String :=
  "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"

def iupacP93RelationalFullereneLocator
    (page : Nat) (provision : String) :
    IUPACP93RelationalFullereneBibliographicLocator where
  work := "Nomenclature of Organic Chemistry: IUPAC Recommendations and Preferred Names 2013"
  part := "Blue Book P-9"
  artifactSha256 := iupacP93BlueBookP9Sha256
  pdfPage := page
  provision := provision

def iupacP93RelationalFullereneOneCitation : P93AuthorityCitationToken :=
  { components := [{ value := 1 }] }

/-! ## Executable finite CIP audits -/

def iupacP93CanonicalFullereneC70Type4LocalCIPAudit :
    List (IUPACP93RelationalFullereneLocalCenterAudit
      iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends) :=
  [ { ownerIndex := ⟨0, by decide⟩, externalOffset := 70, localCenter := 4,
      citation := iupacP93RelationalFullereneOneCitation, descriptor := .S }
  , { ownerIndex := ⟨0, by decide⟩, externalOffset := 70, localCenter := 17,
      citation := iupacP93RelationalFullereneOneCitation, descriptor := .S }
  , { ownerIndex := ⟨1, by decide⟩, externalOffset := 97, localCenter := 4,
      citation := iupacP93RelationalFullereneOneCitation, descriptor := .S }
  , { ownerIndex := ⟨1, by decide⟩, externalOffset := 97, localCenter := 17,
      citation := iupacP93RelationalFullereneOneCitation, descriptor := .S }
  ]

def iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit :
    List (IUPACP93RelationalFullereneLocalCenterAudit
      iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends) :=
  [ { ownerIndex := ⟨0, by decide⟩, externalOffset := 70, localCenter := 4,
      citation := iupacP93RelationalFullereneOneCitation, descriptor := .S }
  , { ownerIndex := ⟨0, by decide⟩, externalOffset := 70, localCenter := 17,
      citation := iupacP93RelationalFullereneOneCitation, descriptor := .S }
  , { ownerIndex := ⟨1, by decide⟩, externalOffset := 97, localCenter := 4,
      citation := iupacP93RelationalFullereneOneCitation, descriptor := .S }
  , { ownerIndex := ⟨1, by decide⟩, externalOffset := 97, localCenter := 17,
      citation := iupacP93RelationalFullereneOneCitation, descriptor := .S }
  ]

/-- The generic materializer consumes already-global facts.  This projection is definitionally
the same assignment as the local-center compiler, while retaining the source-audited local
offset and center as the primary record. -/
def iupacP93RelationalFullereneLocalCenterAuditToAuditedCIPFact
    {owners : List MolecularFullereneAddend}
    (audit : IUPACP93RelationalFullereneLocalCenterAudit owners) :
    P93RelationalFullereneAuditedCIPFact owners where
  ownerIndex := audit.ownerIndex
  unit := .center (audit.externalOffset + audit.localCenter)
  citation := audit.citation
  descriptor := .center audit.descriptor

@[simp] theorem iupacP93RelationalFullereneLocalCenterAudit_compileFact
    {owners : List MolecularFullereneAddend}
    (audit : IUPACP93RelationalFullereneLocalCenterAudit owners) :
    (iupacP93RelationalFullereneLocalCenterAuditToAuditedCIPFact audit).compile =
      audit.compile := rfl

def iupacP93CanonicalFullereneC70Type4AuditedCIPFacts :
    List (P93RelationalFullereneAuditedCIPFact
      iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends) :=
  iupacP93CanonicalFullereneC70Type4LocalCIPAudit.map
    iupacP93RelationalFullereneLocalCenterAuditToAuditedCIPFact

def iupacP93CanonicalFullereneC70SuperimposedAuditedCIPFacts :
    List (P93RelationalFullereneAuditedCIPFact
      iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends) :=
  iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit.map
    iupacP93RelationalFullereneLocalCenterAuditToAuditedCIPFact

def iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments :
    List P93RelationalFullereneSubstituentCIPAssignment :=
  iupacP93CanonicalFullereneC70Type4LocalCIPAudit.map
    IUPACP93RelationalFullereneLocalCenterAudit.compile

def iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments :
    List P93RelationalFullereneSubstituentCIPAssignment :=
  iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit.map
    IUPACP93RelationalFullereneLocalCenterAudit.compile

theorem iupacP93CanonicalFullereneC70WholeAddendCIPAssignments_materialized :
    iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments =
        materializeP93RelationalFullereneCIPAssignments
          iupacP93CanonicalFullereneC70Type4AuditedCIPFacts ∧
      iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments =
        materializeP93RelationalFullereneCIPAssignments
          iupacP93CanonicalFullereneC70SuperimposedAuditedCIPFacts := by
  constructor <;>
    simp [iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments,
      iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments,
      iupacP93CanonicalFullereneC70Type4AuditedCIPFacts,
      iupacP93CanonicalFullereneC70SuperimposedAuditedCIPFacts,
      materializeP93RelationalFullereneCIPAssignments, List.map_map]

theorem iupacP93CanonicalFullereneC70WholeAddendCIPAssignmentCounts :
    iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments.length = 4 ∧
      iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments.length = 4 := by
  decide



def iupacP93CanonicalFullereneC76Type1AuthorityAuditRow :
    IUPACP93RelationalFullereneAuthorityAuditRow where
  releaseRow := .inherentParent
  bibliography := iupacP93RelationalFullereneLocator 80 "P-93.5.6.2, example II"
  source := iupacP93CanonicalFullereneC76Type1AuthoritySource
  molecule := iupacP93CanonicalFullereneC76Type1Molecule
  spatial? := none
  sourceInputs := [iupacP93CanonicalFullereneC76Type1RelationalSourceInput]
  selectedSourceInput? := some iupacP93CanonicalFullereneC76Type1RelationalSourceInput
  symmetryInput := iupacP93CanonicalFullereneC76Type1RelationalInput
  isType4 := false
  exteriorSense? := some .clockwiseFromOutside
  originalDerivativeChiral := true
  chiralAddends := ∅
  printedCageHandedness? := some (.systematic, .C)
  substituentAssignments := []

def iupacP93CanonicalFullereneC60Type2AuthorityAuditRow :
    IUPACP93RelationalFullereneAuthorityAuditRow where
  releaseRow := .inherentSubstitution
  bibliography := iupacP93RelationalFullereneLocator 81 "P-93.5.6.3"
  source := iupacP93CanonicalFullereneC60Type2AuthoritySource
  molecule := iupacP93CanonicalFullereneC60Type2Molecule
  spatial? := none
  sourceInputs := [iupacP93CanonicalFullereneC60Type2RelationalSourceInput]
  selectedSourceInput? := some iupacP93CanonicalFullereneC60Type2RelationalSourceInput
  symmetryInput := iupacP93CanonicalFullereneC60Type2RelationalInput
  isType4 := false
  exteriorSense? := some .clockwiseFromOutside
  originalDerivativeChiral := true
  chiralAddends := ∅
  printedCageHandedness? := some (.systematic, .C)
  substituentAssignments := []

def iupacP93CanonicalFullereneC60Type3AuthorityAuditRow :
    IUPACP93RelationalFullereneAuthorityAuditRow where
  releaseRow := .noninherentSubstitution
  bibliography := iupacP93RelationalFullereneLocator 81 "P-93.5.6.4"
  source := iupacP93CanonicalFullereneC60Type3AuthoritySource
  molecule := iupacP93CanonicalFullereneC60Type3Molecule
  spatial? := none
  sourceInputs := [iupacP93CanonicalFullereneC60Type3RelationalSourceInput]
  selectedSourceInput? := some iupacP93CanonicalFullereneC60Type3RelationalSourceInput
  symmetryInput := iupacP93CanonicalFullereneC60Type3RelationalInput
  isType4 := false
  exteriorSense? := some .clockwiseFromOutside
  originalDerivativeChiral := true
  chiralAddends := ∅
  printedCageHandedness? := some (.systematic, .C)
  substituentAssignments := []

def iupacP93CanonicalFullereneC70Type4AuthorityAuditRow :
    IUPACP93RelationalFullereneAuthorityAuditRow where
  releaseRow := .chiralSubstituents
  bibliography := iupacP93RelationalFullereneLocator 82 "P-93.5.6.5, Type 4"
  source := iupacP93CanonicalFullereneC70Type4AuthoritySource
  molecule := iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
  spatial? := none
  sourceInputs := []
  selectedSourceInput? := none
  symmetryInput := iupacP93CanonicalFullereneC70Type4RelationalInput
  isType4 := true
  exteriorSense? := none
  originalDerivativeChiral := true
  chiralAddends := iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends.toFinset
  printedCageHandedness? := none
  substituentAssignments := iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments

def iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow :
    IUPACP93RelationalFullereneAuthorityAuditRow where
  releaseRow := .superimposed
  bibliography := iupacP93RelationalFullereneLocator 83 "P-93.5.6.6, superimposition"
  source := iupacP93CanonicalFullereneC70SuperimposedAuthoritySource
  molecule := iupacP93CanonicalFullereneC70SuperimposedMolecule
  spatial? := none
  sourceInputs := [iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput]
  selectedSourceInput? := some iupacP93CanonicalFullereneC70SuperimposedRelationalSourceInput
  symmetryInput := iupacP93CanonicalFullereneC70SuperimposedRelationalInput
  isType4 := false
  exteriorSense? := some .clockwiseFromOutside
  originalDerivativeChiral := true
  chiralAddends :=
    iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends.toFinset
  printedCageHandedness? := some (.systematic, .C)
  substituentAssignments :=
    iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments

def iupacP93CanonicalFullereneRelationalAuthorityAuditRow :
    P93RelationalFullereneReleaseRow → IUPACP93RelationalFullereneAuthorityAuditRow
  | .inherentParent => iupacP93CanonicalFullereneC76Type1AuthorityAuditRow
  | .inherentSubstitution => iupacP93CanonicalFullereneC60Type2AuthorityAuditRow
  | .noninherentSubstitution => iupacP93CanonicalFullereneC60Type3AuthorityAuditRow
  | .chiralSubstituents => iupacP93CanonicalFullereneC70Type4AuthorityAuditRow
  | .superimposed => iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow

private theorem iupacP93RelationalFullereneLocator_valid
    (page : Nat) (provision : String) (pagePositive : 0 < page)
    (provisionPresent : provision ≠ "") :
    (iupacP93RelationalFullereneLocator page provision).ValidFor := by
  refine ⟨?_, ?_, ?_, ?_, pagePositive, provisionPresent⟩
  · simp [iupacP93RelationalFullereneLocator]
  · simp [iupacP93RelationalFullereneLocator]
  · change
      "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450".length = 64
    decide
  · change
      "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450".toList.all
        IUPACP93RelationalFullereneSha256Char = true
    decide

private theorem iupacP93CanonicalFullereneC70Type4OwnerZeroExact
    (valid : 0 < iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends.length) :
    iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends.get ⟨0, valid⟩ =
      iupacP93CanonicalFullereneC70Type4Assembly.compiledPlacedAddend 0
        iupacP93CanonicalFullereneC70Type4FirstPlacement.toPlaced := by
  simp [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.1]

private theorem iupacP93CanonicalFullereneC70Type4OwnerOneExact
    (valid : 1 < iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends.length) :
    iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends.get ⟨1, valid⟩ =
      iupacP93CanonicalFullereneC70Type4Assembly.compiledPlacedAddend 1
        iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced := by
  simp [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.1]

private theorem iupacP93CanonicalFullereneC70SuperimposedOwnerZeroExact
    (valid : 0 < iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends.length) :
    iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends.get ⟨0, valid⟩ =
      iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledPlacedAddend 0
        iupacP93CanonicalFullereneC70SuperimposedFirstPlacement.toPlaced := by
  simp [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.2]

private theorem iupacP93CanonicalFullereneC70SuperimposedOwnerOneExact
    (valid : 1 < iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends.length) :
    iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends.get ⟨1, valid⟩ =
      iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledPlacedAddend 1
        iupacP93CanonicalFullereneC70SuperimposedSecondPlacement.toPlaced := by
  simp [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.2]

private theorem iupacP93CanonicalFullereneC76Type1AuthorityAuditRow_valid :
    iupacP93CanonicalFullereneC76Type1AuthorityAuditRow.ValidFor
      iupacP93CanonicalFullereneC76Type1AuthoritySource := by
  refine
    { sourceExact := rfl
      bibliographyValid := iupacP93RelationalFullereneLocator_valid 80 _ (by decide) (by decide)
      sourceStructurallyWellFormed :=
        iupacP93CanonicalFullereneAuthoritySources_all_structurallyWellFormed.1
      structureAgreement := iupacP93CanonicalFullereneAuthoritySources_all_agree.1
      type4IndexExact := by decide
      type4Shape := by decide
      orientedShape := by simp [iupacP93CanonicalFullereneC76Type1AuthorityAuditRow]
      sourceInputsSymmetryExact := by
        intro input inputPresent
        simp only [iupacP93CanonicalFullereneC76Type1AuthorityAuditRow,
          List.mem_singleton] at inputPresent
        subst input
        rfl
      substituentPairsNodup := by decide
      substituentAssignmentsSourceShaped := by
        simp [iupacP93CanonicalFullereneC76Type1AuthorityAuditRow]
      chiralOwnersCovered := by simp [iupacP93CanonicalFullereneC76Type1AuthorityAuditRow]
      chiralAddendsPresent := by decide
      cipAssignmentsPresent := by decide }

private theorem iupacP93CanonicalFullereneC60Type2AuthorityAuditRow_valid :
    iupacP93CanonicalFullereneC60Type2AuthorityAuditRow.ValidFor
      iupacP93CanonicalFullereneC60Type2AuthoritySource := by
  refine
    { sourceExact := rfl
      bibliographyValid := iupacP93RelationalFullereneLocator_valid 81 _ (by decide) (by decide)
      sourceStructurallyWellFormed :=
        iupacP93CanonicalFullereneAuthoritySources_all_structurallyWellFormed.2.1
      structureAgreement := iupacP93CanonicalFullereneAuthoritySources_all_agree.2.1
      type4IndexExact := by decide
      type4Shape := by decide
      orientedShape := by simp [iupacP93CanonicalFullereneC60Type2AuthorityAuditRow]
      sourceInputsSymmetryExact := by
        intro input inputPresent
        simp only [iupacP93CanonicalFullereneC60Type2AuthorityAuditRow,
          List.mem_singleton] at inputPresent
        subst input
        rfl
      substituentPairsNodup := by decide
      substituentAssignmentsSourceShaped := by
        simp [iupacP93CanonicalFullereneC60Type2AuthorityAuditRow]
      chiralOwnersCovered := by simp [iupacP93CanonicalFullereneC60Type2AuthorityAuditRow]
      chiralAddendsPresent := by decide
      cipAssignmentsPresent := by decide }

private theorem iupacP93CanonicalFullereneC60Type3AuthorityAuditRow_valid :
    iupacP93CanonicalFullereneC60Type3AuthorityAuditRow.ValidFor
      iupacP93CanonicalFullereneC60Type3AuthoritySource := by
  refine
    { sourceExact := rfl
      bibliographyValid := iupacP93RelationalFullereneLocator_valid 81 _ (by decide) (by decide)
      sourceStructurallyWellFormed :=
        iupacP93CanonicalFullereneAuthoritySources_all_structurallyWellFormed.2.2.1
      structureAgreement := iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.1
      type4IndexExact := by decide
      type4Shape := by decide
      orientedShape := by simp [iupacP93CanonicalFullereneC60Type3AuthorityAuditRow]
      sourceInputsSymmetryExact := by
        intro input inputPresent
        simp only [iupacP93CanonicalFullereneC60Type3AuthorityAuditRow,
          List.mem_singleton] at inputPresent
        subst input
        rfl
      substituentPairsNodup := by decide
      substituentAssignmentsSourceShaped := by
        simp [iupacP93CanonicalFullereneC60Type3AuthorityAuditRow]
      chiralOwnersCovered := by simp [iupacP93CanonicalFullereneC60Type3AuthorityAuditRow]
      chiralAddendsPresent := by decide
      cipAssignmentsPresent := by decide }

private theorem iupacP93CanonicalFullereneC70Type4AuthorityAuditRow_valid :
    iupacP93CanonicalFullereneC70Type4AuthorityAuditRow.ValidFor
      iupacP93CanonicalFullereneC70Type4AuthoritySource := by
  refine
    { sourceExact := rfl
      bibliographyValid := iupacP93RelationalFullereneLocator_valid 82 _ (by decide) (by decide)
      sourceStructurallyWellFormed :=
        iupacP93CanonicalFullereneAuthoritySources_all_structurallyWellFormed.2.2.2.1
      structureAgreement := iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.1
      type4IndexExact := by decide
      type4Shape := by simp [iupacP93CanonicalFullereneC70Type4AuthorityAuditRow]
      orientedShape := by
        intro falseEq
        simp [iupacP93CanonicalFullereneC70Type4AuthorityAuditRow] at falseEq
      sourceInputsSymmetryExact := by simp [iupacP93CanonicalFullereneC70Type4AuthorityAuditRow]
      substituentPairsNodup :=
        by
          change ((iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments.map
            fun assignment => (assignment.owner, assignment.unit))).Nodup
          rw [iupacP93CanonicalFullereneC70WholeAddendCIPAssignments_materialized.1]
          exact materializeP93RelationalFullereneCIPAssignments_pairNodup
            iupacP93CanonicalFullereneC70Type4RelationalEvidence.addendsNodup (by decide)
      substituentAssignmentsSourceShaped := by
        intro assignment assignmentPresent
        simp only [iupacP93CanonicalFullereneC70Type4AuthorityAuditRow,
          iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments,
          iupacP93CanonicalFullereneC70Type4LocalCIPAudit,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
          at assignmentPresent
        rcases assignmentPresent with rfl | rfl | rfl | rfl
        · refine ⟨List.mem_toFinset.mpr (List.get_mem _ _), ?_, by
              simp [IUPACP93RelationalFullereneLocalCenterAudit.compile,
                P93AuthorityCitationToken.Valid,
                iupacP93RelationalFullereneOneCitation], trivial⟩
          simp only [IUPACP93RelationalFullereneLocalCenterAudit.compile,
            P93RelationalFullereneSubstituentAtomCarrier,
            Finset.singleton_subset_iff]
          rw [iupacP93CanonicalFullereneC70Type4OwnerZeroExact]
          change 74 ∈ Finset.Ico 70 97
          decide
        · refine ⟨List.mem_toFinset.mpr (List.get_mem _ _), ?_, by
              simp [IUPACP93RelationalFullereneLocalCenterAudit.compile,
                P93AuthorityCitationToken.Valid,
                iupacP93RelationalFullereneOneCitation], trivial⟩
          simp only [IUPACP93RelationalFullereneLocalCenterAudit.compile,
            P93RelationalFullereneSubstituentAtomCarrier,
            Finset.singleton_subset_iff]
          rw [iupacP93CanonicalFullereneC70Type4OwnerZeroExact]
          change 87 ∈ Finset.Ico 70 97
          decide
        · refine ⟨List.mem_toFinset.mpr (List.get_mem _ _), ?_, by
              simp [IUPACP93RelationalFullereneLocalCenterAudit.compile,
                P93AuthorityCitationToken.Valid,
                iupacP93RelationalFullereneOneCitation], trivial⟩
          simp only [IUPACP93RelationalFullereneLocalCenterAudit.compile,
            P93RelationalFullereneSubstituentAtomCarrier,
            Finset.singleton_subset_iff]
          rw [iupacP93CanonicalFullereneC70Type4OwnerOneExact]
          change 101 ∈ Finset.Ico 97 124
          decide
        · refine ⟨List.mem_toFinset.mpr (List.get_mem _ _), ?_, by
              simp [IUPACP93RelationalFullereneLocalCenterAudit.compile,
                P93AuthorityCitationToken.Valid,
                iupacP93RelationalFullereneOneCitation], trivial⟩
          simp only [IUPACP93RelationalFullereneLocalCenterAudit.compile,
            P93RelationalFullereneSubstituentAtomCarrier,
            Finset.singleton_subset_iff]
          rw [iupacP93CanonicalFullereneC70Type4OwnerOneExact]
          change 114 ∈ Finset.Ico 97 124
          decide
      chiralOwnersCovered := by
        intro owner ownerChiral
        change owner ∈ iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends.toFinset
          at ownerChiral
        rw [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.1]
          at ownerChiral
        simp at ownerChiral
        rcases ownerChiral with rfl | rfl
        · refine ⟨(iupacP93CanonicalFullereneC70Type4LocalCIPAudit.get
              ⟨0, by decide⟩).compile, ?_, rfl⟩
          simp [iupacP93CanonicalFullereneC70Type4AuthorityAuditRow,
            iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments,
            iupacP93CanonicalFullereneC70Type4LocalCIPAudit]
        · refine ⟨(iupacP93CanonicalFullereneC70Type4LocalCIPAudit.get
              ⟨2, by decide⟩).compile, ?_, rfl⟩
          simp [iupacP93CanonicalFullereneC70Type4AuthorityAuditRow,
            iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments,
            iupacP93CanonicalFullereneC70Type4LocalCIPAudit]
      chiralAddendsPresent := by
        intro _
        change iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends.toFinset.Nonempty
        rw [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.1]
        simp
      cipAssignmentsPresent := by
        intro _
        simp [iupacP93CanonicalFullereneC70Type4AuthorityAuditRow,
          iupacP93CanonicalFullereneC70Type4WholeAddendCIPAssignments,
          iupacP93CanonicalFullereneC70Type4LocalCIPAudit] }

private theorem iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow_valid :
    iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow.ValidFor
      iupacP93CanonicalFullereneC70SuperimposedAuthoritySource := by
  refine
    { sourceExact := rfl
      bibliographyValid := iupacP93RelationalFullereneLocator_valid 83 _ (by decide) (by decide)
      sourceStructurallyWellFormed :=
        iupacP93CanonicalFullereneAuthoritySources_all_structurallyWellFormed.2.2.2.2
      structureAgreement := iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.2
      type4IndexExact := by decide
      type4Shape := by decide
      orientedShape := by simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow]
      sourceInputsSymmetryExact := by
        intro input inputPresent
        simp only [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
          List.mem_singleton] at inputPresent
        subst input
        rfl
      substituentPairsNodup :=
        by
          change ((iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments.map
            fun assignment => (assignment.owner, assignment.unit))).Nodup
          rw [iupacP93CanonicalFullereneC70WholeAddendCIPAssignments_materialized.2]
          exact materializeP93RelationalFullereneCIPAssignments_pairNodup
            iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence.addendsNodup (by decide)
      substituentAssignmentsSourceShaped := by
        intro assignment assignmentPresent
        simp only [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
          iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments,
          iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit,
          List.map_cons, List.map_nil, List.mem_cons, List.not_mem_nil, or_false]
          at assignmentPresent
        rcases assignmentPresent with rfl | rfl | rfl | rfl
        · refine ⟨List.mem_toFinset.mpr (List.get_mem _ _), ?_, by
              simp [IUPACP93RelationalFullereneLocalCenterAudit.compile,
                P93AuthorityCitationToken.Valid,
                iupacP93RelationalFullereneOneCitation], trivial⟩
          simp only [IUPACP93RelationalFullereneLocalCenterAudit.compile,
            P93RelationalFullereneSubstituentAtomCarrier,
            Finset.singleton_subset_iff]
          rw [iupacP93CanonicalFullereneC70SuperimposedOwnerZeroExact]
          change 74 ∈ Finset.Ico 70 97
          decide
        · refine ⟨List.mem_toFinset.mpr (List.get_mem _ _), ?_, by
              simp [IUPACP93RelationalFullereneLocalCenterAudit.compile,
                P93AuthorityCitationToken.Valid,
                iupacP93RelationalFullereneOneCitation], trivial⟩
          simp only [IUPACP93RelationalFullereneLocalCenterAudit.compile,
            P93RelationalFullereneSubstituentAtomCarrier,
            Finset.singleton_subset_iff]
          rw [iupacP93CanonicalFullereneC70SuperimposedOwnerZeroExact]
          change 87 ∈ Finset.Ico 70 97
          decide
        · refine ⟨List.mem_toFinset.mpr (List.get_mem _ _), ?_, by
              simp [IUPACP93RelationalFullereneLocalCenterAudit.compile,
                P93AuthorityCitationToken.Valid,
                iupacP93RelationalFullereneOneCitation], trivial⟩
          simp only [IUPACP93RelationalFullereneLocalCenterAudit.compile,
            P93RelationalFullereneSubstituentAtomCarrier,
            Finset.singleton_subset_iff]
          rw [iupacP93CanonicalFullereneC70SuperimposedOwnerOneExact]
          change 101 ∈ Finset.Ico 97 124
          decide
        · refine ⟨List.mem_toFinset.mpr (List.get_mem _ _), ?_, by
              simp [IUPACP93RelationalFullereneLocalCenterAudit.compile,
                P93AuthorityCitationToken.Valid,
                iupacP93RelationalFullereneOneCitation], trivial⟩
          simp only [IUPACP93RelationalFullereneLocalCenterAudit.compile,
            P93RelationalFullereneSubstituentAtomCarrier,
            Finset.singleton_subset_iff]
          rw [iupacP93CanonicalFullereneC70SuperimposedOwnerOneExact]
          change 114 ∈ Finset.Ico 97 124
          decide
      chiralOwnersCovered := by
        intro owner ownerChiral
        change owner ∈
          iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends.toFinset
          at ownerChiral
        rw [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.2]
          at ownerChiral
        simp at ownerChiral
        rcases ownerChiral with rfl | rfl
        · refine ⟨(iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit.get
              ⟨0, by decide⟩).compile, ?_, rfl⟩
          simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
            iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments,
            iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit]
        · refine ⟨(iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit.get
              ⟨2, by decide⟩).compile, ?_, rfl⟩
          simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
            iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments,
            iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit]
      chiralAddendsPresent := by
        intro _
        change iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends.toFinset.Nonempty
        rw [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.2]
        simp
      cipAssignmentsPresent := by
        intro _
        simp [iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow,
          iupacP93CanonicalFullereneC70SuperimposedWholeAddendCIPAssignments,
          iupacP93CanonicalFullereneC70SuperimposedLocalCIPAudit] }

private theorem iupacP93CanonicalFullereneRelationalAuthorityAuditRow_valid
    (releaseRow : P93RelationalFullereneReleaseRow) :
    (iupacP93CanonicalFullereneRelationalAuthorityAuditRow releaseRow).ValidFor
      (iupacP93CanonicalFullereneRelationalAuthorityAuditRow releaseRow).source := by
  cases releaseRow
  · exact iupacP93CanonicalFullereneC76Type1AuthorityAuditRow_valid
  · exact iupacP93CanonicalFullereneC60Type2AuthorityAuditRow_valid
  · exact iupacP93CanonicalFullereneC60Type3AuthorityAuditRow_valid
  · exact iupacP93CanonicalFullereneC70Type4AuthorityAuditRow_valid
  · exact iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow_valid

def iupacP93CanonicalFullereneRelationalAuthorityPhysicalPolicy :
    P93AuthorityPhysicalObservationPolicy where
  HelixIdentified _ _ _ := False
  PlanarRestrictionAndAsymmetryObserved _ _ _ := False
  PolyhedralQualitativeFrameObserved _ _ _ _ _ := False

private theorem authoritySource_ne_of_rawAtomCount_ne
    (firstMolecule secondMolecule : RawMolecule)
    (firstCarrier secondCarrier : Finset Nat)
    (firstSource secondSource : AuthoritativeChemicalInput)
    (firstAgreement : firstMolecule.MolecularFullereneTopologyRepresentationAgreement
      firstCarrier none firstSource)
    (secondAgreement : secondMolecule.MolecularFullereneTopologyRepresentationAgreement
      secondCarrier none secondSource)
    (countsDifferent : firstMolecule.atomCount ≠ secondMolecule.atomCount) :
    firstSource ≠ secondSource := by
  intro sourcesEqual
  have firstCount := firstMolecule.toMolecularFullereneTopologySemanticMolecule?_atomCount
    firstCarrier firstSource.molecule firstAgreement.1
  have secondCount := secondMolecule.toMolecularFullereneTopologySemanticMolecule?_atomCount
    secondCarrier secondSource.molecule secondAgreement.1
  apply countsDifferent
  calc
    firstMolecule.atomCount = firstSource.molecule.atomCount := firstCount.symm
    _ = secondSource.molecule.atomCount := congrArg (fun source => source.molecule.atomCount) sourcesEqual
    _ = secondMolecule.atomCount := secondCount

private theorem authoritySource_ne_of_rawBondOrder_disagreement
    (firstMolecule secondMolecule : RawMolecule)
    (firstCarrier secondCarrier : Finset Nat)
    (firstSource secondSource : AuthoritativeChemicalInput)
    (firstAgreement : firstMolecule.MolecularFullereneTopologyRepresentationAgreement
      firstCarrier none firstSource)
    (secondAgreement : secondMolecule.MolecularFullereneTopologyRepresentationAgreement
      secondCarrier none secondSource)
    (left right : Nat) (distinct : left ≠ right)
    (firstPositive : 0 < firstMolecule.bondOrder left right)
    (secondZero : secondMolecule.bondOrder left right = 0) :
    firstSource ≠ secondSource := by
  intro sourcesEqual
  obtain ⟨firstBond, firstBondPresent, firstConnects⟩ :=
    (firstMolecule.bondOrder_pos_iff_exists_bond distinct).mp firstPositive
  have firstInteractionPresent :
      firstBond.toMolecularFullereneTopologyInteraction firstCarrier ∈
        firstSource.molecule.interactions := by
    rw [(firstMolecule.toMolecularFullereneTopologySemanticMolecule?_exact
      firstCarrier firstSource.molecule firstAgreement.1).2]
    exact List.mem_map.mpr ⟨firstBond, firstBondPresent, rfl⟩
  have secondInteractionPresent :
      firstBond.toMolecularFullereneTopologyInteraction firstCarrier ∈
        secondSource.molecule.interactions := by
    simpa [sourcesEqual] using firstInteractionPresent
  rw [(secondMolecule.toMolecularFullereneTopologySemanticMolecule?_exact
    secondCarrier secondSource.molecule secondAgreement.1).2] at secondInteractionPresent
  obtain ⟨secondBond, secondBondPresent, interactionsEqual⟩ :=
    List.mem_map.mp secondInteractionPresent
  have endpointsEqual :
      [secondBond.source, secondBond.target] = [firstBond.source, firstBond.target] := by
    have := congrArg SemanticInteraction.participants interactionsEqual
    simpa using this
  have sourceEqual : secondBond.source = firstBond.source := (List.cons.inj endpointsEqual).1
  have targetEqual : secondBond.target = firstBond.target :=
    (List.cons.inj (List.cons.inj endpointsEqual).2).1
  have secondConnects : secondBond.connects left right = true := by
    simp only [RawBond.connects, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
      at firstConnects ⊢
    rcases firstConnects with ⟨firstSource, firstTarget⟩ | ⟨firstSource, firstTarget⟩
    · exact Or.inl ⟨sourceEqual.trans firstSource, targetEqual.trans firstTarget⟩
    · exact Or.inr ⟨sourceEqual.trans firstSource, targetEqual.trans firstTarget⟩
  have secondPositive : 0 < secondMolecule.bondOrder left right :=
    (secondMolecule.bondOrder_pos_iff_exists_bond distinct).mpr
      ⟨secondBond, secondBondPresent, secondConnects⟩
  exact Nat.ne_of_gt secondPositive secondZero

private theorem iupacP93CanonicalFullereneC70Type4SecondPlacement_attachmentSites :
    iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced.attachmentSites = {15, 34} := by
  simpa [iupacP93CanonicalFullereneC70Type4SecondPlacement] using
    (compileIUPACP93PrintedFullereneAddendPlacement_attachmentSites
      (core := iupacP93CanonicalFullereneC70Transcription.cageMolecule)
      (carrier := iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier)
      rfl { kind := .cyclopropanoBisCarboxylatePhenylbutyl, attachmentSites := {15, 34} }
      (iupacP93CanonicalFullereneC70Type4Placements_audited.2.2.1 _ (by
        simp [iupacP93CanonicalFullereneC70Type4Placements])) (by decide))

private theorem iupacP93CanonicalFullereneC70SuperimposedPlacement_attachmentSites :
    iupacP93CanonicalFullereneC70SuperimposedFirstPlacement.toPlaced.attachmentSites = {7, 24} ∧
      iupacP93CanonicalFullereneC70SuperimposedSecondPlacement.toPlaced.attachmentSites =
        {32, 33} := by
  exact ⟨
    by simpa [iupacP93CanonicalFullereneC70SuperimposedFirstPlacement] using
      (compileIUPACP93PrintedFullereneAddendPlacement_attachmentSites
        (core := iupacP93CanonicalFullereneC70Transcription.cageMolecule)
        (carrier := iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier)
        rfl { kind := .cyclopropanoBisCarboxylatePhenylbutyl, attachmentSites := {7, 24} }
        (iupacP93CanonicalFullereneC70SuperimposedPlacements_audited.2.2.1 _ (by
          simp [iupacP93CanonicalFullereneC70SuperimposedPlacements])) (by decide)),
    by simpa [iupacP93CanonicalFullereneC70SuperimposedSecondPlacement] using
      (compileIUPACP93PrintedFullereneAddendPlacement_attachmentSites
        (core := iupacP93CanonicalFullereneC70Transcription.cageMolecule)
        (carrier := iupacP93CanonicalFullereneC70Transcription.numberedPackage.carrier)
        rfl { kind := .cyclopropanoBisCarboxylatePhenylbutyl, attachmentSites := {32, 33} }
        (iupacP93CanonicalFullereneC70SuperimposedPlacements_audited.2.2.1 _ (by
          simp [iupacP93CanonicalFullereneC70SuperimposedPlacements])) (by decide))⟩

private theorem iupacP93CanonicalFullereneC70Type4AttachmentBond_positive :
    0 < iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble.bondOrder 15 97 := by
  have port : (15, 97) ∈
      (iupacP93CanonicalFullereneC70Type4Assembly.compiledPlacedAddend 1
        iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced).attachmentPorts := by
    have sitePresent : 15 ∈
        iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced.attachmentSites := by
      rw [iupacP93CanonicalFullereneC70Type4SecondPlacement_attachmentSites]
      simp
    obtain ⟨portIndex, _, siteEq⟩ := Finset.mem_image.mp sitePresent
    simp only [MolecularFullereneAddendTemplateAssembly.compiledPlacedAddend]
    refine Finset.mem_image.mpr ⟨portIndex, Finset.mem_univ _, ?_⟩
    apply Prod.ext
    · exact siteEq
    · have portRoot :=
        iupacP93CanonicalFullereneCyclopropanoBisCarboxylatePhenylbutylTemplate_constitution
          |>.2.2.2.2.2 portIndex |>.1
      have portRoot' :
          ((iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced.template.port
            portIndex).externalAtom : Nat) = 0 := by
        simpa [iupacP93CanonicalFullereneC70Type4SecondPlacement] using portRoot
      simp only [molecularFullereneRemapLocalAtom]
      rw [portRoot']
      change 70 + 27 = 97
      decide
  exact (MolecularFullereneAddend.validFor_port_exact
      (iupacP93CanonicalFullereneC70Type4RelationalEvidence.addendsValid
        (iupacP93CanonicalFullereneC70Type4Assembly.compiledPlacedAddend 1
          iupacP93CanonicalFullereneC70Type4SecondPlacement.toPlaced) (by
            change _ ∈ iupacP93CanonicalFullereneC70Type4Assembly.compiledAddends
            rw [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.1]
            simp))
      15 97).1 port |>.2.2

private theorem iupacP93CanonicalFullereneC70SuperimposedAttachmentBond_zero :
    iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder 15 97 = 0 := by
  by_contra nonzero
  have positive : 0 < iupacP93CanonicalFullereneC70SuperimposedMolecule.bondOrder 15 97 :=
    Nat.pos_of_ne_zero nonzero
  obtain ⟨addend, addendPresent, port⟩ :=
    (iupacP93CanonicalFullereneC70SuperimposedRelationalEvidence.attachmentPortsPartition
      15 97 (by decide) (by decide) (by decide)).1 positive
  change addend ∈ iupacP93CanonicalFullereneC70SuperimposedAssembly.compiledAddends at addendPresent
  rw [iupacP93CanonicalFullereneDerivativeCompiledAddends_exact.2.2.2.2] at addendPresent
  simp only [List.mem_cons, List.not_mem_nil, or_false] at addendPresent
  rcases addendPresent with rfl | rfl
  · simp only [MolecularFullereneAddendTemplateAssembly.compiledPlacedAddend] at port
    obtain ⟨portIndex, _, portEq⟩ := Finset.mem_image.mp port
    have siteEq := congrArg Prod.fst portEq
    have sitePresent' : 15 ∈
        iupacP93CanonicalFullereneC70SuperimposedFirstPlacement.toPlaced.attachmentSites := by
      refine Finset.mem_image.mpr ⟨portIndex, Finset.mem_univ _, ?_⟩
      simpa using siteEq
    rw [iupacP93CanonicalFullereneC70SuperimposedPlacement_attachmentSites.1] at sitePresent'
    simp at sitePresent'
  · simp only [MolecularFullereneAddendTemplateAssembly.compiledPlacedAddend] at port
    obtain ⟨portIndex, _, portEq⟩ := Finset.mem_image.mp port
    have siteEq := congrArg Prod.fst portEq
    have sitePresent' : 15 ∈
        iupacP93CanonicalFullereneC70SuperimposedSecondPlacement.toPlaced.attachmentSites := by
      refine Finset.mem_image.mpr ⟨portIndex, Finset.mem_univ _, ?_⟩
      simpa using siteEq
    rw [iupacP93CanonicalFullereneC70SuperimposedPlacement_attachmentSites.2] at sitePresent'
    simp at sitePresent'

def iupacP93CanonicalFullereneRelationalSourceAudit :
    P93RelationalFullereneSourceAudit where
  row := iupacP93CanonicalFullereneRelationalAuthorityAuditRow
  releaseRowExact := by intro releaseRow; cases releaseRow <;> rfl
  valid := iupacP93CanonicalFullereneRelationalAuthorityAuditRow_valid
  sourcesNodup := by
    have type1_type2 := authoritySource_ne_of_rawAtomCount_ne
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC60Type2Molecule _ _ _ _
      iupacP93CanonicalFullereneAuthoritySources_all_agree.1
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.1 (by decide)
    have type1_type3 := authoritySource_ne_of_rawAtomCount_ne
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC60Type3Molecule _ _ _ _
      iupacP93CanonicalFullereneAuthoritySources_all_agree.1
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.1 (by decide)
    have type1_type4 := authoritySource_ne_of_rawAtomCount_ne
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble _ _ _ _
      iupacP93CanonicalFullereneAuthoritySources_all_agree.1
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.1 (by decide)
    have type1_super := authoritySource_ne_of_rawAtomCount_ne
      iupacP93CanonicalFullereneC76Type1Molecule
      iupacP93CanonicalFullereneC70SuperimposedMolecule _ _ _ _
      iupacP93CanonicalFullereneAuthoritySources_all_agree.1
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.2 (by decide)
    have type2_type3 := authoritySource_ne_of_rawAtomCount_ne
      iupacP93CanonicalFullereneC60Type2Molecule
      iupacP93CanonicalFullereneC60Type3Molecule _ _ _ _
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.1
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.1 (by decide)
    have type2_type4 := authoritySource_ne_of_rawAtomCount_ne
      iupacP93CanonicalFullereneC60Type2Molecule
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble _ _ _ _
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.1
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.1 (by decide)
    have type2_super := authoritySource_ne_of_rawAtomCount_ne
      iupacP93CanonicalFullereneC60Type2Molecule
      iupacP93CanonicalFullereneC70SuperimposedMolecule _ _ _ _
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.1
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.2 (by decide)
    have type3_type4 := authoritySource_ne_of_rawAtomCount_ne
      iupacP93CanonicalFullereneC60Type3Molecule
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble _ _ _ _
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.1
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.1 (by decide)
    have type3_super := authoritySource_ne_of_rawAtomCount_ne
      iupacP93CanonicalFullereneC60Type3Molecule
      iupacP93CanonicalFullereneC70SuperimposedMolecule _ _ _ _
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.1
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.2 (by decide)
    have type4_super := authoritySource_ne_of_rawBondOrder_disagreement
      iupacP93CanonicalFullereneC70Type4Assembly.compileExtension.assemble
      iupacP93CanonicalFullereneC70SuperimposedMolecule _ _ _ _
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.1
      iupacP93CanonicalFullereneAuthoritySources_all_agree.2.2.2.2
      15 97 (by decide) iupacP93CanonicalFullereneC70Type4AttachmentBond_positive
      iupacP93CanonicalFullereneC70SuperimposedAttachmentBond_zero
    change List.Nodup
      [iupacP93CanonicalFullereneC76Type1AuthoritySource,
       iupacP93CanonicalFullereneC60Type2AuthoritySource,
       iupacP93CanonicalFullereneC60Type3AuthoritySource,
       iupacP93CanonicalFullereneC70Type4AuthoritySource,
       iupacP93CanonicalFullereneC70SuperimposedAuthoritySource]
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false]
    refine ⟨?_, ?_, ?_, type4_super, by simp⟩
    · rintro (equal | equal | equal | equal)
      · exact type1_type2 equal
      · exact type1_type3 equal
      · exact type1_type4 equal
      · exact type1_super equal
    · rintro (equal | equal | equal)
      · exact type2_type3 equal
      · exact type2_type4 equal
      · exact type2_super equal
    · rintro (equal | equal)
      · exact type3_type4 equal
      · exact type3_super equal
  physicalObservation := iupacP93CanonicalFullereneRelationalAuthorityPhysicalPolicy

def iupacP93CanonicalFullereneRelationalAuthorityAuditRows :
    List IUPACP93RelationalFullereneAuthorityAuditRow :=
  iupacP93CanonicalFullereneRelationalSourceAudit.rows

@[simp] theorem iupacP93CanonicalFullereneRelationalSourceAudit_rows :
    iupacP93CanonicalFullereneRelationalSourceAudit.rows =
      [ iupacP93CanonicalFullereneC76Type1AuthorityAuditRow
      , iupacP93CanonicalFullereneC60Type2AuthorityAuditRow
      , iupacP93CanonicalFullereneC60Type3AuthorityAuditRow
      , iupacP93CanonicalFullereneC70Type4AuthorityAuditRow
      , iupacP93CanonicalFullereneC70SuperimposedAuthorityAuditRow ] := rfl

theorem iupacP93CanonicalFullereneRelationalAuthorityAuditRows_length :
    iupacP93CanonicalFullereneRelationalAuthorityAuditRows.length = 5 := by
  exact iupacP93CanonicalFullereneRelationalSourceAudit.rows_length

def iupacP93RelationalFullereneAuditedAssignment
    (source : AuthoritativeChemicalInput) (molecule : RawMolecule)
    (input : RelationalSymmetryDerivedMolecularFullereneConfigurationInput molecule)
    (owner : MolecularFullereneAddend)
    (unit : P93FullereneSubstituentStereogenicUnit)
    (citation : P93AuthorityCitationToken)
    (descriptor : P93FullereneSubstituentCIPDescriptor) : Prop :=
  IUPACP93RelationalFullereneAuthorityAuditRow.AuditedAssignment
    iupacP93CanonicalFullereneRelationalAuthorityAuditRows source molecule input owner unit
      citation descriptor

def iupacP93CanonicalFullereneRelationalAuthorityPolicy :
    P93RelationalFullereneAuthorityPolicy :=
  iupacP93CanonicalFullereneRelationalSourceAudit.policy

end
end P93CanonicalProgramFullerene
end TetraStereo.OneCenter
