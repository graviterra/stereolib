import TetraStereo.OneCenter.IUPACRemaining71ReviewedSemantics
import TetraStereo.OneCenter.IUPACPrimitive35ReviewedSemantics
import TetraStereo.OneCenter.IUPACNext54ReviewedSemantics

set_option autoImplicit false

/-!
# Exact reviewed compiler for all 152 descriptor-bearing provisions

This module combines the reviewed 35-row primitive compiler, the descriptor-bearing 46-row
restriction of the reviewed next-54 compiler, and the reviewed remaining-71 compiler.  References
are inherited literally from those programs; the sum compiler does not define another authority
relation and has no fallback branch.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

abbrev Next54DescriptorBearingReviewedRow :=
  { provision : IUPACNormativeProvision //
    provision ∈ next54DescriptorBearingProvisions }

namespace Next54DescriptorBearingReviewedRow

def all : List Next54DescriptorBearingReviewedRow :=
  next54DescriptorBearingProvisions.attach

def provision (row : Next54DescriptorBearingReviewedRow) : IUPACNormativeProvision :=
  row.1

@[simp] theorem all_length : all.length = 46 := by
  simp [all]

theorem member_next54Provisions (row : Next54DescriptorBearingReviewedRow) :
    row.provision ∈ next54Provisions := by
  have everyRowIncluded : next54DescriptorBearingProvisions.Forall (fun provision =>
      provision ∈ next54Provisions) := by
    decide
  exact (List.forall_iff_forall_mem.mp everyRowIncluded) row.provision row.2

noncomputable def reference
    (row : Next54DescriptorBearingReviewedRow) : ProvisionReference :=
  (next54ReviewedSemantics.reviewed.row row.provision
    (by simpa using row.member_next54Provisions)).reference

noncomputable def kind
    (row : Next54DescriptorBearingReviewedRow) : ProvisionKind :=
  (next54ReviewedSemantics.reviewed.row row.provision
    (by simpa using row.member_next54Provisions)).kind

end Next54DescriptorBearingReviewedRow

structure DescriptorBearingReviewedPolicies where
  remaining71 : Remaining71ReviewedPolicies

inductive DescriptorBearingReviewedRow where
  | primitive35 (row : Primitive35AuthorityRow)
  | next54 (row : Next54DescriptorBearingReviewedRow)
  | remaining71 (row : Remaining71ReviewedRow)
  deriving DecidableEq, Repr

namespace DescriptorBearingReviewedRow

def primitive35Rows : List DescriptorBearingReviewedRow :=
  Primitive35AuthorityRow.all.map .primitive35

def next54Rows : List DescriptorBearingReviewedRow :=
  Next54DescriptorBearingReviewedRow.all.map .next54

def remaining71Rows : List DescriptorBearingReviewedRow :=
  Remaining71ReviewedRow.all.map .remaining71

def all : List DescriptorBearingReviewedRow :=
  primitive35Rows ++ next54Rows ++ remaining71Rows

def provision : DescriptorBearingReviewedRow → IUPACNormativeProvision
  | .primitive35 row => row.provision
  | .next54 row => row.provision
  | .remaining71 row => row.provision

noncomputable def kind : DescriptorBearingReviewedRow → ProvisionKind
  | .primitive35 row => row.kind
  | .next54 row => row.kind
  | .remaining71 row => row.kind

noncomputable def reference
    (policies : DescriptorBearingReviewedPolicies) :
    DescriptorBearingReviewedRow → ProvisionReference
  | .primitive35 row => row.reference
  | .next54 row => row.reference
  | .remaining71 row => row.reference policies.remaining71

noncomputable def semantics
    (policies : DescriptorBearingReviewedPolicies)
    (row : DescriptorBearingReviewedRow) : ReviewedProvisionSemantics where
  kind := row.kind
  sourceSuppliesRule := true
  reference := row.reference policies

@[simp] theorem all_length : all.length = 152 := by
  simp [all, primitive35Rows, next54Rows, remaining71Rows]

@[simp] theorem all_provisions_exact :
    all.map provision =
      primitive35Provisions ++ next54DescriptorBearingProvisions ++
        remaining71DescriptorBearingProvisions := by
  have primitive35Exact :
      primitive35Rows.map provision = primitive35Provisions := by
    simpa only [primitive35Rows, List.map_map, Function.comp_def, provision] using
      Primitive35AuthorityRow.all_provisions_exact
  have next54Exact :
      next54Rows.map provision = next54DescriptorBearingProvisions := by
    simp only [next54Rows, List.map_map, Function.comp_def, provision,
      Next54DescriptorBearingReviewedRow.all,
      Next54DescriptorBearingReviewedRow.provision]
    rfl
  have remaining71Exact :
      remaining71Rows.map provision = remaining71DescriptorBearingProvisions := by
    simpa only [remaining71Rows, List.map_map, Function.comp_def, provision] using
      Remaining71ReviewedRow.all_provisions_exact
  simp only [all, List.map_append]
  rw [primitive35Exact, next54Exact, remaining71Exact]

@[simp] theorem classifier_exact (row : DescriptorBearingReviewedRow) :
    globalProvisionKind row.provision = row.kind := by
  cases row with
  | primitive35 child =>
      have classified := Primitive35AuthorityRow.classifier_exact child
      simp [provision, kind, globalProvisionKind, classified]
  | next54 child =>
      exact globalProvisionKind_eq_next54Reviewed
        (by simpa using child.member_next54Provisions)
  | remaining71 child =>
      exact Remaining71ReviewedRow.classifier_exact child

end DescriptorBearingReviewedRow

def descriptorBearingReviewedSemanticsSlice : List IUPACNormativeProvision :=
  DescriptorBearingReviewedRow.all.map DescriptorBearingReviewedRow.provision

@[simp] theorem descriptorBearingReviewedSemanticsSlice_length :
    descriptorBearingReviewedSemanticsSlice.length = 152 := by
  simp [descriptorBearingReviewedSemanticsSlice]

@[simp] theorem descriptorBearingReviewedSemanticsSlice_exact :
    descriptorBearingReviewedSemanticsSlice =
      reviewed81DescriptorBearingProvisions ++ remaining71DescriptorBearingProvisions := by
  rw [descriptorBearingReviewedSemanticsSlice,
    DescriptorBearingReviewedRow.all_provisions_exact]
  rfl

theorem descriptorBearingReviewedSemanticsSlice_nodup :
    descriptorBearingReviewedSemanticsSlice.Nodup := by
  rw [descriptorBearingReviewedSemanticsSlice_exact]
  exact reviewed81DescriptorBearingProvisions_nodup.append
    remaining71DescriptorBearingProvisions_nodup reviewed81_disjoint_remaining71

@[simp] theorem descriptorBearingReviewedSemanticsScope_exact :
    descriptorBearingReviewedSemanticsSlice.toFinset =
      descriptorAssignmentBearingProvisions.toFinset := by
  rw [descriptorBearingReviewedSemanticsSlice_exact]
  exact reviewed81_union_remaining71_exact

set_option maxRecDepth 16384 in
theorem descriptorBearing_sourceAuditComplete
    {provision : IUPACNormativeProvision}
    (member : provision ∈ descriptorBearingReviewedSemanticsSlice) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  have sourceNotIncomplete :
      provision.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources := by
    have everySourceClosed : descriptorBearingReviewedSemanticsSlice.Forall (fun row =>
        row.source ∉ IUPACNormativeSource.currentIncompleteProvisionAuditSources) := by
      decide
    exact (List.forall_iff_forall_mem.mp everySourceClosed) provision member
  apply Classical.byContradiction
  intro auditIncomplete
  exact sourceNotIncomplete
    ((IUPACNormativeSource.mem_currentIncompleteProvisionAuditSources_iff
      provision.source).2 auditIncomplete)

theorem exists_descriptorBearingReviewedRow
    {provision : IUPACNormativeProvision}
    (member : provision ∈ descriptorBearingReviewedSemanticsSlice) :
    ∃ row, row ∈ DescriptorBearingReviewedRow.all ∧ row.provision = provision := by
  change provision ∈
    DescriptorBearingReviewedRow.all.map DescriptorBearingReviewedRow.provision at member
  simpa only [List.mem_map] using member

noncomputable def descriptorBearingReviewedRowOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ descriptorBearingReviewedSemanticsSlice) :
    DescriptorBearingReviewedRow :=
  Classical.choose (exists_descriptorBearingReviewedRow member)

theorem descriptorBearingReviewedRowOf_provision
    (provision : IUPACNormativeProvision)
    (member : provision ∈ descriptorBearingReviewedSemanticsSlice) :
    (descriptorBearingReviewedRowOf provision member).provision = provision :=
  (Classical.choose_spec (exists_descriptorBearingReviewedRow member)).2

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

theorem descriptorBearingReviewedRowOf_eq
    (row : DescriptorBearingReviewedRow)
    (rowMember : row ∈ DescriptorBearingReviewedRow.all) :
    descriptorBearingReviewedRowOf row.provision (by
      change row.provision ∈
        DescriptorBearingReviewedRow.all.map DescriptorBearingReviewedRow.provision
      exact List.mem_map.mpr ⟨row, rowMember, rfl⟩) = row := by
  let member : row.provision ∈ descriptorBearingReviewedSemanticsSlice := by
    change row.provision ∈
      DescriptorBearingReviewedRow.all.map DescriptorBearingReviewedRow.provision
    exact List.mem_map.mpr ⟨row, rowMember, rfl⟩
  let selected := descriptorBearingReviewedRowOf row.provision member
  have selectedMember : selected ∈ DescriptorBearingReviewedRow.all :=
    (Classical.choose_spec (exists_descriptorBearingReviewedRow member)).1
  have selectedProvision : selected.provision = row.provision :=
    descriptorBearingReviewedRowOf_provision row.provision member
  exact eq_of_mem_of_mem_of_map_nodup DescriptorBearingReviewedRow.provision
    descriptorBearingReviewedSemanticsSlice_nodup selectedMember rowMember selectedProvision

theorem primitive35_mem_descriptorBearingReviewedRows
    (row : Primitive35AuthorityRow) :
    DescriptorBearingReviewedRow.primitive35 row ∈ DescriptorBearingReviewedRow.all := by
  have primitiveMember : row ∈ Primitive35AuthorityRow.all := by
    cases row <;> decide +revert
  simp [DescriptorBearingReviewedRow.all, DescriptorBearingReviewedRow.primitive35Rows,
    primitiveMember]

structure DescriptorBearingReviewedSemanticsTable where
  reviewed : ReviewedProvisionBatch descriptorBearingReviewedSemanticsSlice.toFinset
  classifier_exact : ∀ {provision : IUPACNormativeProvision}
    (member : provision ∈ descriptorBearingReviewedSemanticsSlice.toFinset),
      (reviewed.row provision member).kind = globalProvisionKind provision

noncomputable def descriptorBearingReviewedSemantics
    (policies : DescriptorBearingReviewedPolicies) :
    DescriptorBearingReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        DescriptorBearingReviewedRow.semantics policies
          (descriptorBearingReviewedRowOf provision (by simpa using member))
      sourceAudited := by
        intro provision member
        exact descriptorBearing_sourceAuditComplete (by simpa using member) }
  classifier_exact := by
    intro provision member
    let row := descriptorBearingReviewedRowOf provision (by simpa using member)
    have rowProvision : row.provision = provision :=
      descriptorBearingReviewedRowOf_provision provision (by simpa using member)
    have classified := DescriptorBearingReviewedRow.classifier_exact row
    change row.kind = globalProvisionKind provision
    simpa [rowProvision] using classified.symm

@[simp] theorem descriptorBearingReviewedSemantics_primitive35_exact
    (policies : DescriptorBearingReviewedPolicies)
    (row : Primitive35AuthorityRow) :
    (descriptorBearingReviewedSemantics policies).reviewed.row row.provision (by
      rw [List.mem_toFinset]
      change row.provision ∈
        DescriptorBearingReviewedRow.all.map DescriptorBearingReviewedRow.provision
      exact List.mem_map.mpr ⟨DescriptorBearingReviewedRow.primitive35 row,
        primitive35_mem_descriptorBearingReviewedRows row, rfl⟩) = row.semantics := by
  change DescriptorBearingReviewedRow.semantics policies
      (descriptorBearingReviewedRowOf
        (DescriptorBearingReviewedRow.primitive35 row).provision _) = row.semantics
  rw [descriptorBearingReviewedRowOf_eq (.primitive35 row)
    (primitive35_mem_descriptorBearingReviewedRows row)]
  rfl

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.DescriptorBearingReviewedRow.all_length
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.DescriptorBearingReviewedRow.all_provisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.descriptorBearingReviewedSemanticsScope_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.descriptorBearing_sourceAuditComplete
