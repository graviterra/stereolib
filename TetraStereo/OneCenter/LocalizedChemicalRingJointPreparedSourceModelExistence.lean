import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModel
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual recursively generated profile is the unique independent source model.
Every generated map is derived from that same profile at strict molecular descendants. The
independent one-step equation then identifies the actual optional descriptor with its source
meaning, for all contexts, geometries and reached detected queries. The report is its exact
final-query projection, including refusals. This closes implementation/specification agreement
for the explicit accumulated-context profile, not its normative chemical-policy status.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence

open CertifiedLocalizedCIPInput
open LocalizedGenericMarkedRecalculation (Geometry WellFormedBonds structuralDepth)
open LocalizedChemicalRingPreparedContextRecursion (preparedAssignCenter?)
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingJointPreparedSourceQueries
open LocalizedChemicalRingJointPreparedSourceQueryMap
open LocalizedChemicalRingJointPreparedSourceStep
open LocalizedChemicalRingJointPreparedSourceModel

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)

include agreement admissible supported in
/-- The actual generated profile satisfies the independent equations at every molecular query,
every ordered reference context and every geometry; both successful labels and refusals agree. -/
theorem actualQueryProfile_sourceModel :
    SourceModel input mol single (actualQueryProfile input mol) := by
  intro geom references query center data
  have endpoints : WellFormedBonds mol := fun bond member =>
    ⟨(admissible.1.1 bond member).1, (admissible.1.1 bond member).2.1⟩
  have familyEq : generatedFamily input mol (structuralDepth mol query.1) query.1 =
      profileFamily input mol (actualQueryProfile input mol) query := by
    funext g context
    exact generated_map_eq_sourceQueryMap input mol endpoints g context query
  rw [← familyEq]
  exact (preparedDescriptor_eq_sourceDescriptor input mol single center query.1 data
    (structuralDepth mol query.1) agreement admissible supported geom references).symm

include agreement admissible supported in
/-- Existence and uniqueness of the full geometry/context-indexed source model are derived.
There is no acyclicity, auxiliary-label correspondence or presumed descriptor premise. -/
theorem existsUnique_sourceModel :
    ∃! candidate : Profile input mol, SourceModel input mol single candidate :=
  ⟨actualQueryProfile input mol,
    actualQueryProfile_sourceModel input mol agreement admissible supported single,
    fun _candidate model => sourceModel_unique input mol agreement admissible supported single
      model (actualQueryProfile_sourceModel input mol agreement admissible supported single)⟩

include agreement admissible supported in
/-- Any independently defined source model is exactly the actual generated profile. -/
theorem sourceModel_eq_actual {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) :
    candidate = actualQueryProfile input mol :=
  sourceModel_unique input mol agreement admissible supported single model
    (actualQueryProfile_sourceModel input mol agreement admissible supported single)

/-- The final molecular query of an actual detected center. -/
def finalQuery (center : input.detectedMultiCenterMolecule.Center) : SourceQuery input mol :=
  ⟨canonicalCenterRoot center.1.val, final_query_eligible input mol agreement center⟩

include admissible supported in
/-- Actual final assignment reads any source model at the corresponding molecular root. -/
theorem assignCenter_eq_sourceModel {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (geom : Geometry)
    (center : input.detectedMultiCenterMolecule.Center) :
    preparedAssignCenter? mol (jointOperations input mol) geom center.1.val =
      candidate geom [] (finalQuery input mol agreement center) := by
  rw [sourceModel_eq_actual input mol agreement admissible supported single model]
  rfl

include admissible supported in
/-- The complete detected-center report is the final projection of the unique source model.
Every candidate is retained, including an independently derived refusal. -/
theorem mem_analyze_iff_sourceModel {candidate : Profile input mol}
    (model : SourceModel input mol single candidate) (atom : Nat)
    (outcome : Option LocalizedAuxiliaryLabel) :
    (atom, outcome) ∈ LocalizedChemicalRingJointPreparedReport.analyze input mol ↔
      ∃ center : input.detectedMultiCenterMolecule.Center, center.1.val = atom ∧
        candidate (inputGeometry input) [] (finalQuery input mol agreement center) = outcome := by
  rw [LocalizedChemicalRingJointPreparedReport.mem_analyze_iff]
  apply exists_congr
  intro center
  rw [assignCenter_eq_sourceModel input mol agreement admissible supported single model]

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence.actualQueryProfile_sourceModel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence.existsUnique_sourceModel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence.sourceModel_eq_actual
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence.assignCenter_eq_sourceModel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence.mem_analyze_iff_sourceModel
