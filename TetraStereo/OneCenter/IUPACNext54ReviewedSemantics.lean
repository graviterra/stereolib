import TetraStereo.OneCenter.IUPACNext54P91ReviewedSemantics
import TetraStereo.OneCenter.IUPACNext54P92FoundationalReviewedSemantics
import TetraStereo.OneCenter.IUPACNext54P92DigraphRule1aReviewedSemantics
import TetraStereo.OneCenter.IUPACNext54P93ResidualReviewedSemantics
import TetraStereo.OneCenter.IUPACNext54IR9ReviewedSemantics

set_option autoImplicit false

/-!
# One exact reviewed compiler table for the complete next-54 work unit

The five independently reviewed semantic sub-batches are assembled here into the single
classifier-bound `Next54ReviewedSemanticsTable` required by the provision compiler.  Selection is
by a proof-relevant exhaustive partition of the frozen 54-row inventory; there is no fallback row,
default reference, or caller-selected semantic family.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

noncomputable section

def next54ReviewedSubbatchProvisions : List IUPACNormativeProvision :=
  next54P91Provisions ++
    next54P92FoundationalProvisions ++
      next54P92DigraphRule1aProvisions ++
        next54P93PolyhedralResidualProvisions ++
          next54IR9ResidualProvisions

@[simp] theorem next54ReviewedSubbatchProvisionCount :
    next54ReviewedSubbatchProvisions.length = 54 := by
  rfl

theorem next54ReviewedSubbatchProvisions_exact :
    next54ReviewedSubbatchProvisions = next54Provisions := by
  simp [next54ReviewedSubbatchProvisions, next54Provisions, next54BlueBookProvisions,
    next54P92ResidualProvisions, next54P92FoundationalProvisions,
    next54P92DigraphRule1aProvisions, List.append_assoc]

theorem next54ReviewedSubbatchProvisions_nodup :
    next54ReviewedSubbatchProvisions.Nodup := by
  rw [next54ReviewedSubbatchProvisions_exact]
  exact next54Provisions_nodup

/-- Proof-relevant ownership of one next-54 row.  Exhaustivity comes from the exact frozen list;
disjointness comes from `next54Provisions_nodup`. -/
inductive Next54ReviewedSubbatch (provision : IUPACNormativeProvision) where
  | p91 (member : provision ∈ next54P91Provisions)
  | p92Foundational (member : provision ∈ next54P92FoundationalProvisions)
  | p92DigraphRule1a (member : provision ∈ next54P92DigraphRule1aProvisions)
  | p93Residual (member : provision ∈ next54P93PolyhedralResidualProvisions)
  | ir9Residual (member : provision ∈ next54IR9ResidualProvisions)

theorem exists_next54ReviewedSubbatch
    {provision : IUPACNormativeProvision}
    (member : provision ∈ next54Provisions) :
    ∃ _partition : Next54ReviewedSubbatch provision, True := by
  rw [← next54ReviewedSubbatchProvisions_exact] at member
  simp only [next54ReviewedSubbatchProvisions, List.mem_append] at member
  rcases member with member | ir9Member
  · rcases member with member | p93Member
    · rcases member with member | digraphMember
      · rcases member with p91Member | foundationalMember
        · exact ⟨.p91 p91Member, trivial⟩
        · exact ⟨.p92Foundational foundationalMember, trivial⟩
      · exact ⟨.p92DigraphRule1a digraphMember, trivial⟩
    · exact ⟨.p93Residual p93Member, trivial⟩
  · exact ⟨.ir9Residual ir9Member, trivial⟩

noncomputable def next54ReviewedSubbatchOf
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54Provisions) :
    Next54ReviewedSubbatch provision :=
  Classical.choose (exists_next54ReviewedSubbatch member)

/-- The reviewed dependent semantics selected by the exact five-way partition. -/
noncomputable def next54ReviewedRow
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54Provisions) : ReviewedProvisionSemantics :=
  match next54ReviewedSubbatchOf provision member with
  | .p91 subMember =>
      next54P91ReviewedSemantics.reviewed.row provision (by simpa using subMember)
  | .p92Foundational subMember =>
      next54P92FoundationalReviewedSemantics.reviewed.row provision
        (by simpa using subMember)
  | .p92DigraphRule1a subMember =>
      next54P92DigraphRule1aReviewedSemantics.reviewed.row provision
        (by simpa using subMember)
  | .p93Residual subMember =>
      next54P93ResidualReviewedSemantics.reviewed.row provision
        (by simpa using subMember)
  | .ir9Residual subMember =>
      next54IR9ReviewedSemantics.reviewed.row provision (by simpa using subMember)

theorem next54ReviewedRow_sourceAudited
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54Provisions) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source := by
  cases partitionEq : next54ReviewedSubbatchOf provision member with
  | p91 subMember => exact next54P91_sourceAuditComplete subMember
  | p92Foundational subMember =>
      exact next54P92Foundational_sourceAuditComplete subMember
  | p92DigraphRule1a subMember =>
      exact next54P92DigraphRule1a_sourceAuditComplete subMember
  | p93Residual subMember => exact next54P93Residual_sourceAuditComplete subMember
  | ir9Residual subMember => exact next54IR9_sourceAuditComplete subMember

theorem next54ReviewedRow_classifier_exact
    (provision : IUPACNormativeProvision)
    (member : provision ∈ next54Provisions) :
    (next54ReviewedRow provision member).kind = next54Kind provision member := by
  unfold next54ReviewedRow
  generalize partitionEq : next54ReviewedSubbatchOf provision member = partition
  cases partition with
  | p91 subMember =>
      simpa using next54P91ReviewedSemantics.classifier_exact
        (provision := provision) (by simpa using subMember)
  | p92Foundational subMember =>
      simpa using next54P92FoundationalReviewedSemantics.classifier_exact
        (provision := provision) (by simpa using subMember)
  | p92DigraphRule1a subMember =>
      simpa using next54P92DigraphRule1aReviewedSemantics.classifier_exact
        (provision := provision) (by simpa using subMember)
  | p93Residual subMember =>
      simpa using next54P93ResidualReviewedSemantics.classifier_exact
        (provision := provision) (by simpa using subMember)
  | ir9Residual subMember =>
      simpa using next54IR9ReviewedSemantics.classifier_exact
        (provision := provision) (by simpa using subMember)

/-- The concrete, exact, classifier-bound reviewed semantics for all 54 second-batch provisions. -/
noncomputable def next54ReviewedSemantics : Next54ReviewedSemanticsTable where
  reviewed :=
    { ChemicallyAdmitted := AuthoritativeChemicalInput.StructurallyWellFormed
      row := fun provision member =>
        next54ReviewedRow provision (by simpa using member)
      sourceAudited := by
        intro provision member
        exact next54ReviewedRow_sourceAudited provision (by simpa using member) }
  classifier_exact := by
    intro provision member
    exact next54ReviewedRow_classifier_exact provision (by simpa using member)

end


end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54ReviewedSubbatchProvisionCount
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54ReviewedSubbatchProvisions_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54ReviewedSubbatchProvisions_nodup
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.exists_next54ReviewedSubbatch
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54ReviewedRow_sourceAudited
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54ReviewedRow_classifier_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.next54ReviewedSemantics
