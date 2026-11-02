import TetraStereo.OneCenter.IUPACNext54P92FoundationalProductionAdapter
import TetraStereo.OneCenter.IUPACP92FamilyProductionCompleteness
import TetraStereo.OneCenter.IUPACNext54P93ResidualProductionAdapter
import TetraStereo.OneCenter.IUPACNext54IR9ProductionAdapter

set_option autoImplicit false

/-!
# One global-corpus production adapter for the 46 descriptor-bearing next-54 rows

The interpreter in this module is a fixed four-way join of the existing P-92 foundational,
P-92 digraph/Rule-1a, residual P-93, and residual IR-9 production families.  It is indexed by the
exact 46-row production partition and transported explicitly to the global descriptor-assignment
corpus.  It never uses a reviewed judgment as production and has no caller-selected relation.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

noncomputable section

private theorem next54ReviewedSubbatch_unique
    {provision : IUPACNormativeProvision}
    (left right : Next54ReviewedSubbatch provision) :
    left = right := by
  have allNodup := next54ReviewedSubbatchProvisions_nodup
  simp only [next54ReviewedSubbatchProvisions] at allNodup
  have ir9Split := List.nodup_append.mp allNodup
  have p93Split := List.nodup_append.mp ir9Split.1
  have digraphSplit := List.nodup_append.mp p93Split.1
  have foundationalSplit := List.nodup_append.mp digraphSplit.1
  have ir9Separated := ir9Split.2.2
  have foundationalSeparated := foundationalSplit.2.2
  have digraphSeparated := digraphSplit.2.2
  have p93Separated := p93Split.2.2
  cases left with
  | p91 leftMember =>
      cases right with
      | p91 _ => congr
      | p92Foundational rightMember =>
          exact False.elim (foundationalSeparated provision leftMember provision
            rightMember rfl)
      | p92DigraphRule1a rightMember =>
          exact False.elim (digraphSeparated provision (by simp [leftMember]) provision
            (by simp [rightMember]) rfl)
      | p93Residual rightMember =>
          exact False.elim (p93Separated provision (by simp [leftMember]) provision
            (by simp [rightMember]) rfl)
      | ir9Residual rightMember =>
          exact False.elim (ir9Separated provision (by simp [leftMember]) provision
            rightMember rfl)
  | p92Foundational leftMember =>
      cases right with
      | p91 rightMember =>
          exact False.elim (foundationalSeparated provision rightMember provision
            leftMember rfl)
      | p92Foundational _ => congr
      | p92DigraphRule1a rightMember =>
          exact False.elim (digraphSeparated provision (by simp [leftMember]) provision
            rightMember rfl)
      | p93Residual rightMember =>
          exact False.elim (p93Separated provision (by simp [leftMember]) provision
            rightMember rfl)
      | ir9Residual rightMember =>
          exact False.elim (ir9Separated provision (by simp [leftMember]) provision
            rightMember rfl)
  | p92DigraphRule1a leftMember =>
      cases right with
      | p91 rightMember =>
          exact False.elim (digraphSeparated provision (by simp [rightMember]) provision
            leftMember rfl)
      | p92Foundational rightMember =>
          exact False.elim (digraphSeparated provision (by simp [rightMember]) provision
            leftMember rfl)
      | p92DigraphRule1a _ => congr
      | p93Residual rightMember =>
          exact False.elim (p93Separated provision (by simp [leftMember]) provision
            rightMember rfl)
      | ir9Residual rightMember =>
          exact False.elim (ir9Separated provision (by simp [leftMember]) provision
            rightMember rfl)
  | p93Residual leftMember =>
      cases right with
      | p91 rightMember =>
          exact False.elim (p93Separated provision (by simp [rightMember]) provision
            leftMember rfl)
      | p92Foundational rightMember =>
          exact False.elim (p93Separated provision (by simp [rightMember]) provision
            leftMember rfl)
      | p92DigraphRule1a rightMember =>
          exact False.elim (p93Separated provision (by simp [rightMember]) provision
            leftMember rfl)
      | p93Residual _ => congr
      | ir9Residual rightMember =>
          exact False.elim (ir9Separated provision (by simp [leftMember]) provision
            rightMember rfl)
  | ir9Residual leftMember =>
      cases right with
      | p91 rightMember =>
          exact False.elim (ir9Separated provision (by simp [rightMember]) provision
            leftMember rfl)
      | p92Foundational rightMember =>
          exact False.elim (ir9Separated provision (by simp [rightMember]) provision
            leftMember rfl)
      | p92DigraphRule1a rightMember =>
          exact False.elim (ir9Separated provision (by simp [rightMember]) provision
            leftMember rfl)
      | p93Residual rightMember =>
          exact False.elim (ir9Separated provision (by simp [rightMember]) provision
            leftMember rfl)
      | ir9Residual _ => congr

namespace Next54P92DigraphRule1aAuthorityRow

theorem provision_mem (row : Next54P92DigraphRule1aAuthorityRow) :
    row.provision ∈ next54P92DigraphRule1aProvisions := by
  cases row <;> simp [provision, next54P92DigraphRule1aProvisions,
    p92DigraphAndRule1aSemanticsSlice]

private theorem provision_injective : Function.Injective provision := by
  intro left right equal
  cases left <;> cases right <;> simp_all [provision]

private theorem authorityRowOf_eq (row : Next54P92DigraphRule1aAuthorityRow) :
    next54P92DigraphRule1aAuthorityRowOf row.provision row.provision_mem = row := by
  apply provision_injective
  exact next54P92DigraphRule1aAuthorityRowOf_provision row.provision row.provision_mem

end Next54P92DigraphRule1aAuthorityRow

private theorem next54ReviewedSemantics_foundational_exact
    (row : Next54P92FoundationalAuthorityRow) :
    next54ReviewedSemantics.reviewed.row row.provision
        (by simpa using next54P92Foundational_mem_next54 row.provision_mem) =
      row.semantics := by
  let next54Member := next54P92Foundational_mem_next54 row.provision_mem
  change next54ReviewedRow row.provision next54Member = row.semantics
  unfold next54ReviewedRow
  have partitionEq :
      next54ReviewedSubbatchOf row.provision next54Member =
        .p92Foundational row.provision_mem :=
    next54ReviewedSubbatch_unique _ _
  rw [partitionEq]
  change (next54P92FoundationalAuthorityRowOf row.provision _).semantics = row.semantics
  rw [row.authorityRowOf_eq]

private theorem next54ReviewedSemantics_digraph_exact
    (row : Next54P92DigraphRule1aAuthorityRow) :
    next54ReviewedSemantics.reviewed.row row.provision
        (by simpa using next54P92DigraphRule1a_mem_next54 row.provision_mem) =
      row.semantics := by
  let next54Member := next54P92DigraphRule1a_mem_next54 row.provision_mem
  change next54ReviewedRow row.provision next54Member = row.semantics
  unfold next54ReviewedRow
  have partitionEq :
      next54ReviewedSubbatchOf row.provision next54Member =
        .p92DigraphRule1a row.provision_mem :=
    next54ReviewedSubbatch_unique _ _
  rw [partitionEq]
  change (next54P92DigraphRule1aAuthorityRowOf row.provision _).semantics = row.semantics
  rw [row.authorityRowOf_eq]

private theorem next54ReviewedSemantics_p93_exact
    (row : Next54P93ResidualAuthorityRow) :
    next54ReviewedSemantics.reviewed.row row.provision
        (by simpa using next54P93Residual_mem_next54 row.provision_mem) =
      row.semantics := by
  let next54Member := next54P93Residual_mem_next54 row.provision_mem
  change next54ReviewedRow row.provision next54Member = row.semantics
  unfold next54ReviewedRow
  have partitionEq :
      next54ReviewedSubbatchOf row.provision next54Member =
        .p93Residual row.provision_mem :=
    next54ReviewedSubbatch_unique _ _
  rw [partitionEq]
  exact next54P93ResidualReviewedSemantics_row_exact row

private theorem next54DescriptorBearingReviewedRow_mem
    (row : Next54DescriptorBearingReviewedRow) :
    DescriptorBearingReviewedRow.next54 row ∈ DescriptorBearingReviewedRow.all := by
  simp [DescriptorBearingReviewedRow.all, DescriptorBearingReviewedRow.next54Rows,
    Next54DescriptorBearingReviewedRow.all]

private theorem descriptorBearingReviewedSemantics_next54_exact
    (policies : DescriptorBearingReviewedPolicies)
    (row : Next54DescriptorBearingReviewedRow) :
    (descriptorBearingReviewedSemantics policies).reviewed.row row.provision (by
      rw [List.mem_toFinset]
      change row.provision ∈
        DescriptorBearingReviewedRow.all.map DescriptorBearingReviewedRow.provision
      exact List.mem_map.mpr ⟨DescriptorBearingReviewedRow.next54 row,
        next54DescriptorBearingReviewedRow_mem row, rfl⟩) =
      DescriptorBearingReviewedRow.semantics policies (.next54 row) := by
  change DescriptorBearingReviewedRow.semantics policies
      (descriptorBearingReviewedRowOf
        (DescriptorBearingReviewedRow.next54 row).provision _) =
    DescriptorBearingReviewedRow.semantics policies (.next54 row)
  rw [descriptorBearingReviewedRowOf_eq (.next54 row)
    (next54DescriptorBearingReviewedRow_mem row)]

set_option maxRecDepth 16384 in
private theorem next54GlobalReference_eq
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Next54DescriptorBearingReviewedRow) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision = row.reference := by
  have descriptorMember : row.provision ∈ descriptorBearingReviewedSemanticsSlice := by
    change row.provision ∈
      DescriptorBearingReviewedRow.all.map DescriptorBearingReviewedRow.provision
    exact List.mem_map.mpr ⟨DescriptorBearingReviewedRow.next54 row,
      next54DescriptorBearingReviewedRow_mem row, rfl⟩
  have bearing := descriptorBearingOfReviewedMember row.provision descriptorMember
  change ((globalDescriptorAssignmentProjection global.toFrozenCorpus).reference
    row.provision).toReference = row.reference
  rw [DescriptorAssignmentProjection.descriptorBearing_exact
    (globalDescriptorAssignmentProjection global.toFrozenCorpus) row.provision bearing]
  change (global.reviewed.row row.provision).reference = row.reference
  rw [global.descriptorBearing_exact bearing]
  rw [descriptorBearingReviewedSemantics_next54_exact policies row]
  rfl

namespace Next54ProductionFamilyRow

def reference : Next54ProductionFamilyRow → ProvisionReference
  | .p92Foundational child => child.reference
  | .p92DigraphRule1a child => child.reference
  | .p93Residual child => child.reference
  | .ir9Residual child => child.reference

noncomputable def reviewedRow (row : Next54ProductionFamilyRow) :
    Next54DescriptorBearingReviewedRow :=
  ⟨row.provision, by
    have member : row.provision ∈ (all.map provision).toFinset := by
      simpa using List.mem_map.mpr ⟨row, row.mem_all, rfl⟩
    rw [all_provisions_exact] at member
    simpa using member⟩

@[simp] theorem reviewedRow_provision (row : Next54ProductionFamilyRow) :
    row.reviewedRow.provision = row.provision := rfl

private theorem eq_of_mem_of_mem_of_map_nodup
    {Row Provision : Type}
    (project : Row → Provision)
    {rows : List Row} {left right : Row}
    (mappedNodup : (rows.map project).Nodup)
    (leftMember : left ∈ rows) (rightMember : right ∈ rows)
    (sameProvision : project left = project right) : left = right := by
  induction rows with
  | nil => simp at leftMember
  | cons head tail inductionHypothesis =>
      simp only [List.map_cons, List.nodup_cons] at mappedNodup
      rcases mappedNodup with ⟨headNotInTail, tailNodup⟩
      simp only [List.mem_cons] at leftMember rightMember
      rcases leftMember with rfl | leftTail
      · rcases rightMember with rfl | rightTail
        · rfl
        · exact False.elim (headNotInTail (by
            rw [sameProvision]
            exact List.mem_map_of_mem rightTail))
      · rcases rightMember with rfl | rightTail
        · exact False.elim (headNotInTail (by
            rw [← sameProvision]
            exact List.mem_map_of_mem leftTail))
        · exact inductionHypothesis tailNodup leftTail rightTail

theorem provision_injective : Function.Injective provision := by
  intro left right sameProvision
  exact eq_of_mem_of_mem_of_map_nodup provision all_provisions_nodup
    left.mem_all right.mem_all sameProvision

theorem familyRowOf_reviewedRow_eq (row : Next54ProductionFamilyRow) :
    familyRowOf row.reviewedRow = row := by
  apply provision_injective
  exact familyRowOf_provision row.reviewedRow

private theorem reviewedRow_reference_eq (row : Next54ProductionFamilyRow) :
    row.reviewedRow.reference = row.reference := by
  cases row with
  | p92Foundational child =>
      change (next54ReviewedSemantics.reviewed.row child.provision _).reference =
        child.reference
      rw [next54ReviewedSemantics_foundational_exact child]
      rfl
  | p92DigraphRule1a child =>
      change (next54ReviewedSemantics.reviewed.row child.provision _).reference =
        child.reference
      rw [next54ReviewedSemantics_digraph_exact child]
      rfl
  | p93Residual child =>
      change (next54ReviewedSemantics.reviewed.row child.provision _).reference =
        child.reference
      rw [next54ReviewedSemantics_p93_exact child]
      rfl
  | ir9Residual child =>
      change (next54ReviewedSemantics.reviewed.row child.provision _).reference =
        child.reference
      have next54Member : child.toAuthorityRow.provision ∈ next54Provisions.toFinset := by
        cases child <;> decide
      have ir9Member : child.toAuthorityRow.provision ∈
          next54IR9ResidualProvisions.toFinset := by
        cases child <;> decide
      have exactRow := next54ReviewedSemantics_ir9_exact child.toAuthorityRow
        next54Member ir9Member
      simpa only [Next54DescriptorBearingIR9Row.provision,
        Next54DescriptorBearingIR9Row.reference] using
          congrArg ReviewedProvisionSemantics.reference exactRow

theorem globalReference_eq
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Next54ProductionFamilyRow) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision = row.reference := by
  rw [← row.reviewedRow_reference_eq]
  exact next54GlobalReference_eq global row.reviewedRow

set_option maxRecDepth 16384 in
/-- The assembled reviewed table retains the exact independent reference selected by the
four-family next-54 partition.  This is the direct bridge used to generate reviewed nonvacuity;
it does not pass through, or depend on, the production interpreter. -/
theorem globalReviewedReference_eq
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Next54ProductionFamilyRow) :
    (global.reviewed.row row.provision).reference = row.reference := by
  have descriptorMember : row.provision ∈ descriptorBearingReviewedSemanticsSlice := by
    change row.provision ∈
      DescriptorBearingReviewedRow.all.map DescriptorBearingReviewedRow.provision
    exact List.mem_map.mpr ⟨DescriptorBearingReviewedRow.next54 row.reviewedRow,
      next54DescriptorBearingReviewedRow_mem row.reviewedRow, rfl⟩
  have bearing := descriptorBearingOfReviewedMember row.provision descriptorMember
  rw [global.descriptorBearing_exact bearing]
  change ((descriptorBearingReviewedSemantics policies).reviewed.row
      row.reviewedRow.provision _).reference = row.reference
  rw [descriptorBearingReviewedSemantics_next54_exact policies row.reviewedRow]
  exact row.reviewedRow_reference_eq

/-- The already fixed production relation selected by the exact four-family row. -/
def ProductionJudges :
    (row : Next54ProductionFamilyRow) → AuthoritativeChemicalInput →
      row.reference.Observation → Prop
  | .p92Foundational child, source, observation =>
      child.ProductionJudges source observation
  | .p92DigraphRule1a child, source, observation =>
      Next54P92Produces child source observation
  | .p93Residual child, _source, observation =>
      child.ProductionJudges observation
  | .ir9Residual child, _source, observation =>
      child.ProductionJudges observation

private theorem productionJudges_congr
    (left right : Next54ProductionFamilyRow)
    (rowEq : left = right)
    (source : AuthoritativeChemicalInput)
    {leftObservation : left.reference.Observation}
    {rightObservation : right.reference.Observation}
    (observationEq : HEq leftObservation rightObservation) :
    left.ProductionJudges source leftObservation ↔
      right.ProductionJudges source rightObservation := by
  cases rowEq
  cases observationEq
  rfl

/-- Constructive row-local readiness.  Every P-92, P-93 residual, and IR-9 residual family is
theorem-derived; no caller-supplied P-92 realization remains. -/
inductive ProductionReady : Next54ProductionFamilyRow → Prop where
  | p92Foundational (child : Next54P92FoundationalAuthorityRow) :
      ProductionReady (.p92Foundational child)
  | digraphRule1a (child : Next54P92DigraphRule1aAuthorityRow) :
      ProductionReady (.p92DigraphRule1a child)
  | p93Residual (child : Next54P93ResidualAuthorityRow) :
      ProductionReady (.p93Residual child)
  | ir9Residual (child : Next54DescriptorBearingIR9Row) :
      ProductionReady (.ir9Residual child)

private theorem foundational_production_iff_reference
    (child : Next54P92FoundationalAuthorityRow)
    (correct : ProvisionCorrect p92FoundationalFrozenCorpus
      p92FoundationalInterpreter child.provision)
    (source : AuthoritativeChemicalInput)
    (wellFormed : AuthoritativeChemicalInput.StructurallyWellFormed source)
    (observation : child.reference.Observation) :
    child.ProductionJudges source observation ↔
      child.reference.Applicable source ∧ child.reference.Judges source observation := by
  let referenceEq := p92FoundationalFrozenCorpus_reference_eq child
  let frozenObservation :
      (p92FoundationalFrozenCorpus.reference child.provision).Observation :=
    cast (congrArg ProvisionReference.Observation referenceEq.symm) observation
  have exactAt := correct source wellFormed frozenObservation
  rw [p92FoundationalInterpreter_exact child source frozenObservation] at exactAt
  rw [ProvisionReference.applicable_congr referenceEq source] at exactAt
  rw [ProvisionReference.judges_cast_congr
    referenceEq source frozenObservation] at exactAt
  simpa [frozenObservation] using exactAt

theorem production_iff_reference_of_ready
    (row : Next54ProductionFamilyRow)
    (ready : row.ProductionReady)
    (source : AuthoritativeChemicalInput)
    (wellFormed : AuthoritativeChemicalInput.StructurallyWellFormed source)
    (observation : row.reference.Observation) :
    row.ProductionJudges source observation ↔
      row.reference.Applicable source ∧ row.reference.Judges source observation := by
  cases ready with
  | p92Foundational child =>
      exact foundational_production_iff_reference child
        (p92FoundationalInterpreter_correct child) source wellFormed observation
  | digraphRule1a child =>
      constructor
      · exact Next54P92Produces.applicable_and_judged
      · rintro ⟨_applicable, judged⟩
        exact next54P92_reverse_realization child source observation judged
  | p93Residual child =>
      have judgedExact := child.production_eq_reference source observation
      constructor
      · intro produced
        exact ⟨child.reference_applicable source, judgedExact.mp produced⟩
      · rintro ⟨_applicable, judged⟩
        exact judgedExact.mpr judged
  | ir9Residual child =>
      have judgedExact := child.production_eq_reference source observation
      constructor
      · intro produced
        exact ⟨child.reference_applicable source, judgedExact.mp produced⟩
      · rintro ⟨_applicable, judged⟩
        exact judgedExact.mpr judged

end Next54ProductionFamilyRow

/-! ## Fixed global-corpus join -/

noncomputable abbrev Next54GlobalProductionCorpus
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) : FrozenProvisionCorpus :=
  (globalDescriptorAssignmentProjection
    (assembleGlobalReviewedSemantics policies negative).toFrozenCorpus).toCorpus

private noncomputable def next54GlobalFamilyRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54DescriptorBearingProvisions) :
    Next54ProductionFamilyRow :=
  Next54ProductionFamilyRow.familyRowOf ⟨provision, member⟩

private theorem next54GlobalFamilyRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54DescriptorBearingProvisions) :
    (next54GlobalFamilyRowOf provision member).provision = provision :=
  Next54ProductionFamilyRow.familyRowOf_provision ⟨provision, member⟩

private theorem next54GlobalFamilyRowOf_eq
    (row : Next54ProductionFamilyRow) :
    next54GlobalFamilyRowOf row.provision row.reviewedRow.2 = row := by
  exact row.familyRowOf_reviewedRow_eq

private theorem next54GlobalReference_eq_of_member
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54DescriptorBearingProvisions) :
    (Next54GlobalProductionCorpus policies negative).reference provision =
      (next54GlobalFamilyRowOf provision member).reference := by
  let row := next54GlobalFamilyRowOf provision member
  have rowProvision : row.provision = provision :=
    next54GlobalFamilyRowOf_provision provision member
  calc
    (Next54GlobalProductionCorpus policies negative).reference provision =
        (Next54GlobalProductionCorpus policies negative).reference row.provision :=
      congrArg (Next54GlobalProductionCorpus policies negative).reference rowProvision.symm
    _ = row.reference := Next54ProductionFamilyRow.globalReference_eq
      (assembleGlobalReviewedSemantics policies negative) row

/-- The generic residual P-93 adapter instantiated against this exact assembled global corpus. -/
noncomputable def next54P93GlobalReferenceFaithful
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ProvisionBatchReferenceFaithful next54P93ResidualReviewedSemantics.reviewed
      (Next54GlobalProductionCorpus policies negative) where
  admitted_exact := by
    intro input
    rfl
  exact := by
    intro provision member
    let row := next54P93ResidualAuthorityRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      next54P93ResidualAuthorityRowOf_provision provision (by simpa using member)
    have next54Member : provision ∈ next54Provisions.toFinset := by
      simpa using next54P93Residual_mem_next54 (by simpa using member)
    have next54Exact := next54ReviewedSemantics_p93_exact row
    have localExact := next54P93ResidualReviewedSemantics_row_exact row
    have kindExact :
        (Next54GlobalProductionCorpus policies negative).kind provision =
          (next54P93ResidualReviewedSemantics.reviewed.row provision member).kind := by
      change ((assembleGlobalReviewedSemantics policies negative).reviewed.row
        provision).kind = _
      calc
        ((assembleGlobalReviewedSemantics policies negative).reviewed.row provision).kind =
            globalProvisionKind provision :=
          (assembleGlobalReviewedSemantics policies negative).classifier_exact provision
        _ = (next54ReviewedSemantics.reviewed.row provision next54Member).kind :=
          globalProvisionKind_eq_next54Reviewed next54Member
        _ = row.semantics.kind := by
          simpa [rowProvision] using congrArg ReviewedProvisionSemantics.kind next54Exact
        _ = (next54P93ResidualReviewedSemantics.reviewed.row provision member).kind := by
          simpa [rowProvision] using
            (congrArg ReviewedProvisionSemantics.kind localExact).symm
    have sourceExact :
        (Next54GlobalProductionCorpus policies negative).SourceSuppliesRule provision ↔
          (next54P93ResidualReviewedSemantics.reviewed.row provision member).sourceSuppliesRule =
            true := by
      have globalSource :
          (Next54GlobalProductionCorpus policies negative).SourceSuppliesRule provision := by
        change ((assembleGlobalReviewedSemantics policies negative).reviewed.row
          provision).sourceSuppliesRule = true
        have rowBearing : DescriptorAssignmentBearing row.provision := by
          cases row <;> rfl
        have bearing : DescriptorAssignmentBearing provision := by
          simpa [rowProvision] using rowBearing
        exact (assembleGlobalReviewedSemantics policies negative).descriptorBearing_source_present
          provision bearing
      have localSource :
          (next54P93ResidualReviewedSemantics.reviewed.row provision member).sourceSuppliesRule =
            true := by
        simpa [rowProvision] using
          congrArg ReviewedProvisionSemantics.sourceSuppliesRule localExact
      exact iff_of_true globalSource localSource
    have referenceExact :
        (Next54GlobalProductionCorpus policies negative).reference provision =
          (next54P93ResidualReviewedSemantics.reviewed.row provision member).reference := by
      calc
        (Next54GlobalProductionCorpus policies negative).reference provision =
            (Next54GlobalProductionCorpus policies negative).reference row.provision :=
          congrArg (Next54GlobalProductionCorpus policies negative).reference
            rowProvision.symm
        _ = row.reference := Next54ProductionFamilyRow.globalReference_eq
          (assembleGlobalReviewedSemantics policies negative) (.p93Residual row)
        _ = (next54P93ResidualReviewedSemantics.reviewed.row provision member).reference := by
          simpa [rowProvision] using
            (congrArg ReviewedProvisionSemantics.reference localExact).symm
    exact ⟨kindExact, sourceExact, referenceExact⟩

theorem next54P93GlobalProduction_correct
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54P93PolyhedralResidualProvisions) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54P93ResidualProductionInterpreter
        (next54P93GlobalReferenceFaithful policies negative)) provision :=
  next54P93ResidualProductionInterpreter_provisionCorrect
    (next54P93GlobalReferenceFaithful policies negative) provision member

/-- The single fixed interpreter for exactly the 46 descriptor-bearing next-54 rows.  The false
branch is only its out-of-scope totalization. -/
noncomputable def next54GlobalProductionInterpreter
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ProvisionInterpreter (Next54GlobalProductionCorpus policies negative) where
  Produces := fun provision source observation =>
    if member : provision ∈ next54DescriptorBearingProvisions then
      let row := next54GlobalFamilyRowOf provision member
      let referenceEq := next54GlobalReference_eq_of_member
        policies negative provision member
      row.ProductionJudges source
        (cast (congrArg ProvisionReference.Observation referenceEq) observation)
    else False

@[simp] theorem next54GlobalProductionInterpreter_exact
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54DescriptorBearingProvisions)
    (source : AuthoritativeChemicalInput)
    (observation : ((Next54GlobalProductionCorpus policies negative).reference
      provision).Observation) :
    (next54GlobalProductionInterpreter policies negative).Produces
        provision source observation ↔
      let row := next54GlobalFamilyRowOf provision member
      row.ProductionJudges source
        (cast (congrArg ProvisionReference.Observation
          (next54GlobalReference_eq_of_member policies negative provision member)) observation) := by
  simp only [next54GlobalProductionInterpreter, dif_pos member]

@[simp] theorem next54GlobalProductionInterpreter_exact_row
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (row : Next54ProductionFamilyRow)
    (source : AuthoritativeChemicalInput)
    (observation : ((Next54GlobalProductionCorpus policies negative).reference
      row.provision).Observation) :
    (next54GlobalProductionInterpreter policies negative).Produces
        row.provision source observation ↔
      row.ProductionJudges source
        (cast (congrArg ProvisionReference.Observation
          (row.globalReference_eq
            (assembleGlobalReviewedSemantics policies negative))) observation) := by
  rw [next54GlobalProductionInterpreter_exact policies negative row.provision
    row.reviewedRow.2 source observation]
  change (next54GlobalFamilyRowOf row.provision row.reviewedRow.2).ProductionJudges source
      (cast _ observation) ↔ row.ProductionJudges source (cast _ observation)
  apply Next54ProductionFamilyRow.productionJudges_congr
    (next54GlobalFamilyRowOf row.provision row.reviewedRow.2) row
    (next54GlobalFamilyRowOf_eq row)
  exact (cast_heq _ observation).trans (cast_heq _ observation).symm

/-- Row-local correctness for the joined interpreter.  This theorem makes the P-93 and IR-9
branches usable without constructing any unrelated P-92 obligation. -/
theorem next54GlobalProduction_correct_of_ready
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (row : Next54ProductionFamilyRow)
    (ready : row.ProductionReady) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54GlobalProductionInterpreter policies negative) row.provision := by
  intro source admitted observation
  let referenceEq := row.globalReference_eq
    (assembleGlobalReviewedSemantics policies negative)
  let rowObservation : row.reference.Observation :=
    cast (congrArg ProvisionReference.Observation referenceEq) observation
  have wellFormed : AuthoritativeChemicalInput.StructurallyWellFormed source := admitted
  have localExact := row.production_iff_reference_of_ready
    ready source wellFormed rowObservation
  have applicableTransport := ProvisionReference.applicable_congr referenceEq source
  have judgmentTransport := ProvisionReference.judges_cast_congr referenceEq source observation
  rw [next54GlobalProductionInterpreter_exact_row policies negative row source observation]
  change row.ProductionJudges source rowObservation ↔
    ((Next54GlobalProductionCorpus policies negative).reference row.provision).Applicable source ∧
      ((Next54GlobalProductionCorpus policies negative).reference row.provision).Judges
        source observation
  constructor
  · intro produced
    have expected := localExact.mp produced
    exact ⟨applicableTransport.mpr expected.1, judgmentTransport.mpr expected.2⟩
  · rintro ⟨applicable, judged⟩
    exact localExact.mpr
      ⟨applicableTransport.mp applicable, judgmentTransport.mp judged⟩

theorem next54GlobalJoinedP93Production_correct
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (row : Next54P93ResidualAuthorityRow) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54GlobalProductionInterpreter policies negative) row.provision :=
  next54GlobalProduction_correct_of_ready policies negative (.p93Residual row)
    (.p93Residual row)

theorem next54GlobalJoinedIR9Production_correct
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (row : Next54DescriptorBearingIR9Row) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54GlobalProductionInterpreter policies negative) row.provision :=
  next54GlobalProduction_correct_of_ready policies negative (.ir9Residual row)
    (.ir9Residual row)

/-- One joined-corpus theorem closes every foundational P-92 row. -/
theorem next54GlobalJoinedP92Foundational_correct
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (row : Next54P92FoundationalAuthorityRow) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54GlobalProductionInterpreter policies negative) row.provision :=
  next54GlobalProduction_correct_of_ready policies negative (.p92Foundational row)
    (.p92Foundational row)

theorem next54GlobalJoinedP92BondingNumberScope_correct
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54GlobalProductionInterpreter policies negative)
      Next54P92FoundationalAuthorityRow.bondingNumberScope.provision :=
  next54GlobalProduction_correct_of_ready policies negative
    (.p92Foundational .bondingNumberScope) (.p92Foundational .bondingNumberScope)

theorem next54GlobalJoinedP92HelicityRule_correct
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54GlobalProductionInterpreter policies negative)
      Next54P92FoundationalAuthorityRow.helicityRule.provision :=
  next54GlobalProduction_correct_of_ready policies negative
    (.p92Foundational .helicityRule) (.p92Foundational .helicityRule)

theorem next54GlobalJoinedP92HelicityAxis_correct
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54GlobalProductionInterpreter policies negative)
      Next54P92FoundationalAuthorityRow.helicityAxis.provision :=
  next54GlobalProduction_correct_of_ready policies negative
    (.p92Foundational .helicityAxis) (.p92Foundational .helicityAxis)

theorem next54GlobalJoinedP92HelicityPlane_correct
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54GlobalProductionInterpreter policies negative)
      Next54P92FoundationalAuthorityRow.helicityPlane.provision :=
  next54GlobalProduction_correct_of_ready policies negative
    (.p92Foundational .helicityPlane) (.p92Foundational .helicityPlane)

theorem next54GlobalJoinedP92RSMPDescriptorCorrespondence_correct
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54GlobalProductionInterpreter policies negative)
      Next54P92FoundationalAuthorityRow.rsmpDescriptorCorrespondence.provision :=
  next54GlobalProduction_correct_of_ready policies negative
    (.p92Foundational .rsmpDescriptorCorrespondence)
      (.p92Foundational .rsmpDescriptorCorrespondence)

theorem next54GlobalJoinedP92SequenceRulePropertyClasses_correct
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54GlobalProductionInterpreter policies negative)
      Next54P92FoundationalAuthorityRow.sequenceRulePropertyClasses.provision :=
  next54GlobalProduction_correct_of_ready policies negative
    (.p92Foundational .sequenceRulePropertyClasses)
      (.p92Foundational .sequenceRulePropertyClasses)

theorem next54GlobalJoinedP92SequenceRuleReflectionBehavior_correct
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54GlobalProductionInterpreter policies negative)
      Next54P92FoundationalAuthorityRow.sequenceRuleReflectionBehavior.provision :=
  next54GlobalProduction_correct_of_ready policies negative
    (.p92Foundational .sequenceRuleReflectionBehavior)
      (.p92Foundational .sequenceRuleReflectionBehavior)

theorem next54GlobalJoinedP92SequenceRuleHierarchy_correct
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54GlobalProductionInterpreter policies negative)
      Next54P92FoundationalAuthorityRow.sequenceRuleHierarchy.provision :=
  next54GlobalProduction_correct_of_ready policies negative
    (.p92Foundational .sequenceRuleHierarchy) (.p92Foundational .sequenceRuleHierarchy)

/-- The eleven digraph/Rule-1a rows close unconditionally through fixed executable semantic
hierarchy, mancude, duplicate-fiber, and saturated-ring programs. -/
theorem next54GlobalJoinedP92DigraphRule1a_correct
    (policies : DescriptorBearingReviewedPolicies)
    (negative : GlobalNonDescriptorReviewedSemantics)
    (row : Next54P92DigraphRule1aAuthorityRow) :
    ProvisionCorrect (Next54GlobalProductionCorpus policies negative)
      (next54GlobalProductionInterpreter policies negative) row.provision :=
  next54GlobalProduction_correct_of_ready policies negative (.p92DigraphRule1a row)
    (.digraphRule1a row)

end

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54ReviewedSubbatch_unique
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54ProductionFamilyRow.globalReference_eq
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.Next54ProductionFamilyRow.globalReviewedReference_eq
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54P93GlobalProduction_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54GlobalProductionInterpreter_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54GlobalProduction_correct_of_ready
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54GlobalJoinedP93Production_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54GlobalJoinedIR9Production_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54GlobalJoinedP92Foundational_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54GlobalJoinedP92BondingNumberScope_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54GlobalJoinedP92SequenceRuleHierarchy_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54GlobalJoinedP92DigraphRule1a_correct
