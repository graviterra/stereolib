import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence
import TetraStereo.OneCenter.LocalizedGenericMarkedRecalculationCage
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192

/-! The same 15-atom cage input inhabits CURRENT's independent source-model interface.
This supplies the intake adapter; it does not assume or prove a result comparison with the
older replacing-reference cage evaluator. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCageInput

open LocalizedHiddenParityMarkedProbe
open LocalizedRecursiveAuxiliaryObservationSeparation
open LocalizedRecursiveAuxiliaryPhysicalCompletion
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceModelExistence

variable (P : List CartesianPoint3) (len : P.length = 15)

/-- Explicit empty parser diagram channel. The older certified family omitted this channel;
Raw structure agreement requires it to be present even when it contains no stereomarks. -/
def sourceWithDiagram : AuthoritativeChemicalInput :=
  { sourceWith P with diagram? := some cageRaw.toDiagramConfiguration }

theorem sourceWithDiagram_wellFormed (length : P.length = 15) :
    (sourceWithDiagram P).StructurallyWellFormed := by
  have original := sourceWith_wellFormed P length
  refine ⟨original.1, original.2.1, ?_⟩
  change True ∧ true = true ∧ true = true
  decide

def certified : CertifiedLocalizedCIPInput where
  certified := ⟨sourceWithDiagram P, sourceWithDiagram_wellFormed P len⟩
  graphReady := (certifiedWith P len).graphReady

/-- Adding the empty diagram changes neither the molecular graph nor the spatial evidence. -/
theorem graph_preserved : (certified P len).moleculeGraph = (certifiedWith P len).moleculeGraph := rfl

theorem spatial_preserved : (certified P len).certified.input.spatial? =
    (certifiedWith P len).certified.input.spatial? := rfl

theorem structure_agreement :
    cageRaw.AuthoritativeStructureAgreement (certified P len).certified.input := by
  constructor <;> rfl

theorem admissible : cageRaw.StereochemicalAdmissible :=
  cageRaw.stereochemicalAdmissible?_eq_true_iff.mp (by decide +kernel)

theorem supported : ∀ bond ∈ cageRaw.bonds, bond.kind.IsLocalizedCovalent := by
  have all : cageRaw.bonds.all (fun bond => decide (bond.kind = .single)) = true := by
    decide +kernel
  intro bond member
  have kind : bond.kind = .single := of_decide_eq_true ((List.all_eq_true.mp all) bond member)
  rw [kind]
  exact ⟨1, rfl⟩

noncomputable section

/-- CURRENT's unique independent profile is inhabited on exactly the same graph and geometry
as the independent frozen/regenerated consensus comparison, with an explicit empty parser
diagram channel. Its output is not supplied. -/
theorem unique_current_source_model :
    ∃! candidate : Profile (certified P len) cageRaw,
      SourceModel (certified P len) cageRaw (simpleBondedWith P len) candidate :=
  existsUnique_sourceModel (certified P len) cageRaw (structure_agreement P len)
    admissible supported (simpleBondedWith P len)

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCageInput

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCageInput.structure_agreement
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCageInput.admissible
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCageInput.supported
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCageInput.unique_current_source_model

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCageInput.sourceWithDiagram

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCageInput.sourceWithDiagram_wellFormed

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCageInput.certified

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCageInput.graph_preserved

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicyCageInput.spatial_preserved
