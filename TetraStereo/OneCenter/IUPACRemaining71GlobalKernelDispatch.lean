import TetraStereo.OneCenter.IUPACRemaining71P93DescriptorKernel
import TetraStereo.OneCenter.IUPACRemaining71P94AuthorityProductionAdapter

set_option autoImplicit false

/-!
# Mixed kernel dispatch for the remaining 71-row inventory

This joins production relations for the 56 P-93 rows with the twelve P-94
normalization/conformation rows and the three generated authority-data lookups.  Dispatch is fixed
by the exact 56/12/3 remaining-71 inventory.

The P-93 branch now proves provision correctness for thirteen rows through one closed-family sum:
six fullerene rows, three acyclic rows (two executable evaluators and one finite descriptor
relation), and four spiro source/core rows.  The spiro result is not transport from the deeper
`SpiroConfiguration` analyzer.  The other forty-three rows remain open, including the four
noncarbon representation factorizations that still carry opaque descriptor authorization.  The
P-94 rows retain their conditional row correctness under fixed-normalization totality, while the
three authority-data rows retain unconditional row correctness.  The caller-selected policy
boundary remains explicit; this module does not claim the final assumption-free 71-row adapter.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-! ## Exact global-reference recovery for the P-94 and authority-data rows -/

namespace Remaining71P94AuthorityRow

def toDescriptorBearingReviewedRow
    (row : Remaining71P94AuthorityRow) : DescriptorBearingReviewedRow :=
  .remaining71 (.p94 row)

theorem toDescriptorBearingReviewedRow_mem_all
    (row : Remaining71P94AuthorityRow) :
    row.toDescriptorBearingReviewedRow ∈ DescriptorBearingReviewedRow.all := by
  cases row <;>
    simp [toDescriptorBearingReviewedRow, DescriptorBearingReviewedRow.all,
      DescriptorBearingReviewedRow.remaining71Rows, Remaining71ReviewedRow.all,
      Remaining71ReviewedRow.p94Rows, Remaining71P94AuthorityRow.all]

theorem descriptorAssignmentBearing (row : Remaining71P94AuthorityRow) :
    DescriptorAssignmentBearing row.provision := by
  apply descriptorBearingOfReviewedMember row.provision
  rw [List.mem_toFinset]
  change row.provision ∈
    DescriptorBearingReviewedRow.all.map DescriptorBearingReviewedRow.provision
  exact List.mem_map.mpr
    ⟨row.toDescriptorBearingReviewedRow,
      row.toDescriptorBearingReviewedRow_mem_all, rfl⟩

end Remaining71P94AuthorityRow

namespace Remaining71AuthorityDataRow

def toDescriptorBearingReviewedRow
    (row : Remaining71AuthorityDataRow) : DescriptorBearingReviewedRow :=
  .remaining71 (.authorityData row)

theorem toDescriptorBearingReviewedRow_mem_all
    (row : Remaining71AuthorityDataRow) :
    row.toDescriptorBearingReviewedRow ∈ DescriptorBearingReviewedRow.all := by
  cases row <;>
    simp [toDescriptorBearingReviewedRow, DescriptorBearingReviewedRow.all,
      DescriptorBearingReviewedRow.remaining71Rows, Remaining71ReviewedRow.all,
      Remaining71ReviewedRow.authorityDataRows, Remaining71AuthorityDataRow.all]

theorem descriptorAssignmentBearing (row : Remaining71AuthorityDataRow) :
    DescriptorAssignmentBearing row.provision := by
  apply descriptorBearingOfReviewedMember row.provision
  rw [List.mem_toFinset]
  change row.provision ∈
    DescriptorBearingReviewedRow.all.map DescriptorBearingReviewedRow.provision
  exact List.mem_map.mpr
    ⟨row.toDescriptorBearingReviewedRow,
      row.toDescriptorBearingReviewedRow_mem_all, rfl⟩

end Remaining71AuthorityDataRow

theorem descriptorBearingReviewedSemantics_remaining71P94_exact
    (policies : DescriptorBearingReviewedPolicies)
    (row : Remaining71P94AuthorityRow) :
    (descriptorBearingReviewedSemantics policies).reviewed.row row.provision
        (descriptorBearingReviewedMember row.provision row.descriptorAssignmentBearing) =
      row.semantics policies.remaining71.p94 := by
  change DescriptorBearingReviewedRow.semantics policies
      (descriptorBearingReviewedRowOf row.toDescriptorBearingReviewedRow.provision _) =
    row.semantics policies.remaining71.p94
  rw [descriptorBearingReviewedRowOf_eq row.toDescriptorBearingReviewedRow
    row.toDescriptorBearingReviewedRow_mem_all]
  rfl

theorem descriptorBearingReviewedSemantics_remaining71AuthorityData_exact
    (policies : DescriptorBearingReviewedPolicies)
    (row : Remaining71AuthorityDataRow) :
    (descriptorBearingReviewedSemantics policies).reviewed.row row.provision
        (descriptorBearingReviewedMember row.provision row.descriptorAssignmentBearing) =
      row.semantics := by
  change DescriptorBearingReviewedRow.semantics policies
      (descriptorBearingReviewedRowOf row.toDescriptorBearingReviewedRow.provision _) =
    row.semantics
  rw [descriptorBearingReviewedRowOf_eq row.toDescriptorBearingReviewedRow
    row.toDescriptorBearingReviewedRow_mem_all]
  rfl

theorem globalReviewedSemantics_remaining71P94_exact
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Remaining71P94AuthorityRow) :
    global.reviewed.row row.provision = row.semantics policies.remaining71.p94 := by
  rw [global.descriptorBearing_exact row.descriptorAssignmentBearing]
  exact descriptorBearingReviewedSemantics_remaining71P94_exact policies row

theorem globalReviewedSemantics_remaining71AuthorityData_exact
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Remaining71AuthorityDataRow) :
    global.reviewed.row row.provision = row.semantics := by
  rw [global.descriptorBearing_exact row.descriptorAssignmentBearing]
  exact descriptorBearingReviewedSemantics_remaining71AuthorityData_exact policies row

theorem remaining71P93ClosedGlobalReference_eq
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Remaining71P93ClosedProductionRow) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision = row.reference policies.remaining71 := by
  simpa using remaining71P93GlobalReference_eq global
    (Remaining71P93DescriptorKernelRow.ofClosedProduction row)

theorem remaining71P93ClosedGlobalReference_eq_of_member
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ Remaining71P93ClosedProductionRow.provisions) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference provision =
      (Remaining71P93ClosedProductionRow.rowOf provision member).reference
        policies.remaining71 := by
  let row := Remaining71P93ClosedProductionRow.rowOf provision member
  have rowProvision : row.provision = provision :=
    Remaining71P93ClosedProductionRow.rowOf_provision provision member
  calc
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference provision =
        (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
          row.provision := congrArg
            ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference)
            rowProvision.symm
    _ = row.reference policies.remaining71 :=
      remaining71P93ClosedGlobalReference_eq global row
    _ = (Remaining71P93ClosedProductionRow.rowOf provision member).reference
        policies.remaining71 := rfl

theorem remaining71P94GlobalReference_eq
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Remaining71P94AuthorityRow) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision = row.reference policies.remaining71.p94 := by
  change ((globalDescriptorAssignmentProjection global.toFrozenCorpus).reference
    row.provision).toReference = row.reference policies.remaining71.p94
  rw [DescriptorAssignmentProjection.descriptorBearing_exact
    (globalDescriptorAssignmentProjection global.toFrozenCorpus)
      row.provision row.descriptorAssignmentBearing]
  change (global.reviewed.row row.provision).reference =
    row.reference policies.remaining71.p94
  rw [globalReviewedSemantics_remaining71P94_exact global row]
  rfl

theorem remaining71AuthorityDataGlobalReference_eq
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (row : Remaining71AuthorityDataRow) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      row.provision = row.reference := by
  change ((globalDescriptorAssignmentProjection global.toFrozenCorpus).reference
    row.provision).toReference = row.reference
  rw [DescriptorAssignmentProjection.descriptorBearing_exact
    (globalDescriptorAssignmentProjection global.toFrozenCorpus)
      row.provision row.descriptorAssignmentBearing]
  change (global.reviewed.row row.provision).reference = row.reference
  rw [globalReviewedSemantics_remaining71AuthorityData_exact global row]
  rfl

theorem remaining71P94GlobalReference_eq_of_member
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p94ReviewedSemanticsSlice) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference provision =
      (remaining71P94AuthorityRowOf provision member).reference policies.remaining71.p94 := by
  let row := remaining71P94AuthorityRowOf provision member
  have rowProvision : row.provision = provision :=
    remaining71P94AuthorityRowOf_provision provision member
  calc
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference provision =
        (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
          row.provision := congrArg
            ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference)
            rowProvision.symm
    _ = row.reference policies.remaining71.p94 := remaining71P94GlobalReference_eq global row
    _ = (remaining71P94AuthorityRowOf provision member).reference
        policies.remaining71.p94 := rfl

theorem remaining71AuthorityDataGlobalReference_eq_of_member
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ authorityDataReviewedSemanticsSlice) :
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference provision =
      (remaining71AuthorityDataRowOf provision member).reference := by
  let row := remaining71AuthorityDataRowOf provision member
  have rowProvision : row.provision = provision :=
    remaining71AuthorityDataRowOf_provision provision member
  calc
    (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference provision =
        (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
          row.provision := congrArg
            ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference)
            rowProvision.symm
    _ = row.reference := remaining71AuthorityDataGlobalReference_eq global row
    _ = (remaining71AuthorityDataRowOf provision member).reference := rfl

/-! ## Exact 56/12/3 inventory partition -/

def remaining71GlobalKernelDispatchScope : List IUPACNormativeProvision :=
  Remaining71P93DescriptorKernelRow.provisions ++
    p94ReviewedSemanticsSlice ++ authorityDataReviewedSemanticsSlice

@[simp] theorem remaining71GlobalKernelDispatchInventory_lengths :
    Remaining71P93DescriptorKernelRow.provisions.length = 56 ∧
      p94ReviewedSemanticsSlice.length = 12 ∧
      authorityDataReviewedSemanticsSlice.length = 3 := by
  exact ⟨Remaining71P93DescriptorKernelRow.provisions_length,
    p94ReviewedSemanticsSlice_length, authorityDataReviewedSemanticsSlice_length⟩

@[simp] theorem remaining71GlobalKernelDispatchScope_length :
    remaining71GlobalKernelDispatchScope.length = 71 := by
  simp only [remaining71GlobalKernelDispatchScope, List.length_append,
    Remaining71P93DescriptorKernelRow.provisions_length,
    p94ReviewedSemanticsSlice_length, authorityDataReviewedSemanticsSlice_length]

@[simp] theorem remaining71GlobalKernelDispatchScope_exact :
    remaining71GlobalKernelDispatchScope = remaining71DescriptorBearingProvisions := by
  simp [remaining71GlobalKernelDispatchScope,
    Remaining71P93DescriptorKernelRow.provisions_exact,
    remaining71DescriptorBearingProvisions, remainingP93DescriptorProvisions]

theorem p93ClosedProductionProvisions_subset_p93DescriptorProvisions
    {provision : IUPACNormativeProvision}
    (member : provision ∈ Remaining71P93ClosedProductionRow.provisions) :
    provision ∈ Remaining71P93DescriptorKernelRow.provisions := by
  have everyClosedRow : Remaining71P93ClosedProductionRow.provisions.Forall
      (fun row => row ∈ Remaining71P93DescriptorKernelRow.provisions) := by
    decide
  exact (List.forall_iff_forall_mem.mp everyClosedRow) provision member

theorem p93DescriptorProvisions_subset_closedProductionProvisions
    {provision : IUPACNormativeProvision}
    (member : provision ∈ Remaining71P93DescriptorKernelRow.provisions) :
    provision ∈ Remaining71P93ClosedProductionRow.provisions := by
  have everyDescriptorRow : Remaining71P93DescriptorKernelRow.provisions.Forall
      (fun row => row ∈ Remaining71P93ClosedProductionRow.provisions) := by
    decide
  exact (List.forall_iff_forall_mem.mp everyDescriptorRow) provision member

theorem remaining71P93_disjoint_p94Authority :
    List.Disjoint Remaining71P93DescriptorKernelRow.provisions
      (p94ReviewedSemanticsSlice ++ authorityDataReviewedSemanticsSlice) := by
  apply List.disjoint_of_nodup_append
  simpa [Remaining71P93DescriptorKernelRow.provisions_exact,
    remaining71DescriptorBearingProvisions, remainingP93DescriptorProvisions] using
      remaining71DescriptorBearingProvisions_nodup

theorem remaining71P94_disjoint_authorityData :
    List.Disjoint p94ReviewedSemanticsSlice authorityDataReviewedSemanticsSlice := by
  have allNodup :
      (Remaining71P93DescriptorKernelRow.provisions ++
        (p94ReviewedSemanticsSlice ++ authorityDataReviewedSemanticsSlice)).Nodup := by
    simpa [Remaining71P93DescriptorKernelRow.provisions_exact,
      remaining71DescriptorBearingProvisions, remainingP93DescriptorProvisions] using
        remaining71DescriptorBearingProvisions_nodup
  exact List.disjoint_of_nodup_append (List.Nodup.of_append_right allNodup)

/-! ## Mixed dispatcher: closed P-93 families, residual kernels, P-94, and authority rows -/

/-- A fixed dispatcher over the exact remaining-71 inventory.  The leading family branch installs
one complete thirteen-row production sum; the residual P-93 branch retains the partial kernel. -/
noncomputable def remaining71GlobalKernelDispatchInterpreter
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative) :
    ProvisionInterpreter
      (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus where
  Produces := fun provision source observation =>
    if closedMember : provision ∈ Remaining71P93ClosedProductionRow.provisions then
      let row := Remaining71P93ClosedProductionRow.rowOf provision closedMember
      let referenceEq := remaining71P93ClosedGlobalReference_eq_of_member
        global provision closedMember
      row.ProductionJudges policies.remaining71 source
        (cast (congrArg ProvisionReference.Observation referenceEq) observation)
    else if _p93Member : provision ∈ Remaining71P93DescriptorKernelRow.provisions then
      (remaining71P93DescriptorKernelInterpreter global).Produces provision source observation
    else if p94Member : provision ∈ p94ReviewedSemanticsSlice then
      let row := remaining71P94AuthorityRowOf provision p94Member
      let referenceEq := remaining71P94GlobalReference_eq_of_member
        global provision p94Member
      row.ProductionJudges policies.remaining71.p94 source
        (cast (congrArg ProvisionReference.Observation referenceEq) observation)
    else if authorityMember : provision ∈ authorityDataReviewedSemanticsSlice then
      let row := remaining71AuthorityDataRowOf provision authorityMember
      let referenceEq := remaining71AuthorityDataGlobalReference_eq_of_member
        global provision authorityMember
      row.ProductionJudges
        (cast (congrArg ProvisionReference.Observation referenceEq) observation)
    else False

@[simp] theorem remaining71GlobalKernelDispatchInterpreter_p93_descriptorKernel_exact
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (closedAbsent : provision ∉ Remaining71P93ClosedProductionRow.provisions)
    (member : provision ∈ Remaining71P93DescriptorKernelRow.provisions)
    (source : AuthoritativeChemicalInput)
    (observation : ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      provision).Observation) :
    (remaining71GlobalKernelDispatchInterpreter global).Produces provision source observation ↔
      (Remaining71P93DescriptorKernelRow.rowOf provision member).DescriptorKernelJudges
        policies.remaining71 source
        (cast (congrArg ProvisionReference.Observation
          (remaining71P93GlobalReference_eq_of_member global provision member)) observation) := by
  rw [show
    (remaining71GlobalKernelDispatchInterpreter global).Produces provision source observation ↔
      (remaining71P93DescriptorKernelInterpreter global).Produces
        provision source observation by
      simp only [remaining71GlobalKernelDispatchInterpreter, dif_neg closedAbsent,
        dif_pos member]]
  exact remaining71P93DescriptorKernelInterpreter_exact
    global provision member source observation

@[simp] theorem remaining71GlobalKernelDispatchInterpreter_p93_closed_exact
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ Remaining71P93ClosedProductionRow.provisions)
    (source : AuthoritativeChemicalInput)
    (observation : ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      provision).Observation) :
    (remaining71GlobalKernelDispatchInterpreter global).Produces provision source observation ↔
      (Remaining71P93ClosedProductionRow.rowOf provision member).ProductionJudges
        policies.remaining71 source
        (cast (congrArg ProvisionReference.Observation
          (remaining71P93ClosedGlobalReference_eq_of_member
            global provision member)) observation) := by
  simp only [remaining71GlobalKernelDispatchInterpreter, dif_pos member]

/-- All thirteen proved P-93 provisions are correct for the installed global dispatcher through
one sum theorem.  This removes their provision-correctness assumptions while remaining uniform in
the still-explicit reviewed policies. -/
theorem remaining71GlobalKernelDispatchInterpreter_p93_closed_correct
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ Remaining71P93ClosedProductionRow.provisions) :
    ProvisionCorrect (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus
      (remaining71GlobalKernelDispatchInterpreter global) provision := by
  let row := Remaining71P93ClosedProductionRow.rowOf provision member
  let referenceEq :
      (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
          provision =
        row.reference policies.remaining71 :=
    remaining71P93ClosedGlobalReference_eq_of_member global provision member
  exact ProvisionCorrect.of_transported_judgment
    (fun source observation =>
      row.ProductionJudges policies.remaining71 source observation)
    referenceEq
    (remaining71GlobalKernelDispatchInterpreter_p93_closed_exact
      global provision member)
    (row.production_eq_reference policies.remaining71)
    (row.reference_applicable_of_judged policies.remaining71)

@[simp] theorem remaining71GlobalKernelDispatchInterpreter_p94_exact
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (p93Absent : provision ∉ Remaining71P93DescriptorKernelRow.provisions)
    (member : provision ∈ p94ReviewedSemanticsSlice)
    (source : AuthoritativeChemicalInput)
    (observation : ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      provision).Observation) :
    (remaining71GlobalKernelDispatchInterpreter global).Produces provision source observation ↔
      (remaining71P94AuthorityRowOf provision member).ProductionJudges
        policies.remaining71.p94 source
        (cast (congrArg ProvisionReference.Observation
          (remaining71P94GlobalReference_eq_of_member global provision member)) observation) := by
  have closedAbsent : provision ∉ Remaining71P93ClosedProductionRow.provisions := by
    intro closed
    exact p93Absent (p93ClosedProductionProvisions_subset_p93DescriptorProvisions closed)
  simp only [remaining71GlobalKernelDispatchInterpreter, dif_neg closedAbsent,
    dif_neg p93Absent, dif_pos member]

@[simp] theorem remaining71GlobalKernelDispatchInterpreter_authority_exact
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (p93Absent : provision ∉ Remaining71P93DescriptorKernelRow.provisions)
    (p94Absent : provision ∉ p94ReviewedSemanticsSlice)
    (member : provision ∈ authorityDataReviewedSemanticsSlice)
    (source : AuthoritativeChemicalInput)
    (observation : ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      provision).Observation) :
    (remaining71GlobalKernelDispatchInterpreter global).Produces provision source observation ↔
      (remaining71AuthorityDataRowOf provision member).ProductionJudges
        (cast (congrArg ProvisionReference.Observation
          (remaining71AuthorityDataGlobalReference_eq_of_member global provision member))
            observation) := by
  have closedAbsent : provision ∉ Remaining71P93ClosedProductionRow.provisions := by
    intro closed
    exact p93Absent (p93ClosedProductionProvisions_subset_p93DescriptorProvisions closed)
  simp only [remaining71GlobalKernelDispatchInterpreter, dif_neg closedAbsent,
    dif_neg p93Absent, dif_neg p94Absent, dif_pos member]

/-! ## Family correctness for closed P-93, P-94, and authority-data rows -/

theorem remaining71GlobalKernelDispatchInterpreter_p94_correct
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ p94ReviewedSemanticsSlice)
    (p93Absent : provision ∉ Remaining71P93DescriptorKernelRow.provisions) :
    ProvisionCorrect (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus
      (remaining71GlobalKernelDispatchInterpreter global) provision := by
  intro source _admitted observation
  let row := remaining71P94AuthorityRowOf provision member
  let referenceEq := remaining71P94GlobalReference_eq_of_member global provision member
  let rowObservation : (row.reference policies.remaining71.p94).Observation :=
    cast (congrArg ProvisionReference.Observation referenceEq) observation
  have judgment := row.production_eq_reference source rowObservation
  have applicableTransport := ProvisionReference.applicable_congr referenceEq source
  have judgmentTransport := ProvisionReference.judges_cast_congr referenceEq source observation
  rw [remaining71GlobalKernelDispatchInterpreter_p94_exact
    global provision p93Absent member source observation]
  change row.ProductionJudges policies.remaining71.p94 source rowObservation ↔
    ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      provision).Applicable source ∧
      ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
        provision).Judges source observation
  constructor
  · intro produced
    have judged := judgment.mp produced
    exact ⟨applicableTransport.mpr
      (row.reference_applicable_of_judged source rowObservation judged),
        judgmentTransport.mpr judged⟩
  · rintro ⟨_applicable, judged⟩
    exact judgment.mpr (judgmentTransport.mp judged)

theorem remaining71GlobalKernelDispatchInterpreter_authority_correct
    {policies : DescriptorBearingReviewedPolicies}
    {negative : GlobalNonDescriptorReviewedSemantics}
    (global : GlobalReviewedSemantics policies negative)
    (provision : IUPACNormativeProvision)
    (member : provision ∈ authorityDataReviewedSemanticsSlice)
    (p93Absent : provision ∉ Remaining71P93DescriptorKernelRow.provisions)
    (p94Absent : provision ∉ p94ReviewedSemanticsSlice) :
    ProvisionCorrect (globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus
      (remaining71GlobalKernelDispatchInterpreter global) provision := by
  intro source _admitted observation
  let row := remaining71AuthorityDataRowOf provision member
  let referenceEq := remaining71AuthorityDataGlobalReference_eq_of_member
    global provision member
  let rowObservation : row.reference.Observation :=
    cast (congrArg ProvisionReference.Observation referenceEq) observation
  have judgment := row.production_eq_reference source rowObservation
  have applicable := row.reference_applicable source
  have applicableTransport := ProvisionReference.applicable_congr referenceEq source
  have judgmentTransport := ProvisionReference.judges_cast_congr referenceEq source observation
  rw [remaining71GlobalKernelDispatchInterpreter_authority_exact
    global provision p93Absent p94Absent member source observation]
  change row.ProductionJudges rowObservation ↔
    ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
      provision).Applicable source ∧
      ((globalDescriptorAssignmentProjection global.toFrozenCorpus).toCorpus.reference
        provision).Judges source observation
  constructor
  · intro produced
    exact ⟨applicableTransport.mpr applicable,
      judgmentTransport.mpr (judgment.mp produced)⟩
  · rintro ⟨_applicable, judged⟩
    exact judgment.mpr (judgmentTransport.mp judged)

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71GlobalKernelDispatchInventory_lengths
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71GlobalKernelDispatchScope_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71GlobalKernelDispatchScope_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P93ClosedGlobalReference_eq
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71P94GlobalReference_eq
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71AuthorityDataGlobalReference_eq
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71GlobalKernelDispatchInterpreter_p93_descriptorKernel_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71GlobalKernelDispatchInterpreter_p93_closed_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71GlobalKernelDispatchInterpreter_p93_closed_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71GlobalKernelDispatchInterpreter_p94_correct
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.remaining71GlobalKernelDispatchInterpreter_authority_correct
