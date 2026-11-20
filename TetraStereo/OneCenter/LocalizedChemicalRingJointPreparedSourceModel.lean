import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStep
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueryMap
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Independent source equations for the accumulated-context molecular profile.
These are concrete equations on source cuts, candidate labels, all eligible reference choices
and independently read geometries. The source-query and candidate-map definitions exclude the
actual evaluator. Their locality and actual molecular descent derive uniqueness; no dependency
well-foundedness, successful sort, label match or desired descriptor is a hypothesis.
Existence and agreement with the actual evaluator are a separate integration theorem.
This is the explicit accumulated-context profile, not a claim of normative Rule-6 approval.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModel

open CertifiedLocalizedCIPInput
open LocalizedGenericMarkedRecalculation (Geometry WellFormedBonds)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedChemicalRingJointPreparedSourceQueries
open LocalizedChemicalRingJointPreparedSourceQueryMap
open LocalizedChemicalRingJointPreparedSourceStep

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)

/-- One optional molecular descriptor for every geometry, full ordered context and source query. -/
abbrev Profile := Geometry → List input.Atom → SourceQuery input mol →
  Option LocalizedTetrahedralRSPseudoDescriptor

/-- The complete context/geometry candidate reader family at a source query. -/
def profileFamily (candidate : Profile input mol) (query : SourceQuery input mol) :
    DescriptorFamily input :=
  fun geom references => sourceQueryMap input mol query (candidate geom references)

/-- Independent source equations at every real detected molecular query and every source frame.
Frame existence is derived in `sourceQuery_data_exists`, so these equations are not vacuous.
No actual generated profile or runtime descriptor occurs in this definition. -/
def SourceModel (single : input.moleculeGraph.SimpleBonded) (candidate : Profile input mol) : Prop :=
  ∀ (geom : Geometry) (references : List input.Atom) (query : SourceQuery input mol)
    (center : input.detectedMultiCenterMolecule.Center)
    (data : OccurrenceData input mol center query.1),
    sourceDescriptor input single (profileFamily input mol candidate query)
      data.target data.frame geom references = candidate geom references query

/-- A query's entire family of source maps depends only on strictly deeper queries, even
when local comparisons ask for another geometry or an extended reference context. -/
theorem profileFamily_local (query : SourceQuery input mol) (first second : Profile input mol)
    (agree : ∀ geom references inner, StrictDescendant mol query.1 inner.1 →
      first geom references inner = second geom references inner) :
    profileFamily input mol first query = profileFamily input mol second query := by
  funext geom references
  exact sourceQueryMap_local input mol query _ _ (agree geom references)

/-- Uniqueness follows from actual molecular strict descent and the source-map locality.
Both successful descriptors and refusals are determined; no existence of a desired answer
or auxiliary correspondence is assumed. -/
theorem sourceModel_unique
    (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
    (admissible : mol.StereochemicalAdmissible)
    (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
    (single : input.moleculeGraph.SimpleBonded)
    {first second : Profile input mol}
    (firstModel : SourceModel input mol single first)
    (secondModel : SourceModel input mol single second) : first = second := by
  let Call := (Geometry × List input.Atom) × SourceQuery input mol
  have endpoints : WellFormedBonds mol := fun bond member =>
    ⟨(admissible.1.1 bond member).1, (admissible.1.1 bond member).2.1⟩
  have wf : WellFounded (fun (inner outer : Call) =>
      StrictDescendant mol outer.2.1 inner.2.1) :=
    sourceQueryDependency_wellFounded input mol endpoints
  have equal : ∀ call : Call,
      first call.1.1 call.1.2 call.2 = second call.1.1 call.1.2 call.2 := by
    intro call
    apply wf.induction call
    intro call ih
    obtain ⟨center, _current, ⟨data⟩⟩ :=
      sourceQuery_data_exists input mol agreement admissible supported single call.2
    have families : profileFamily input mol first call.2 = profileFamily input mol second call.2 :=
      profileFamily_local input mol call.2 first second
        (fun geom references inner path => ih ((geom, references), inner) path)
    rw [← firstModel call.1.1 call.1.2 call.2 center data,
      ← secondModel call.1.1 call.1.2 call.2 center data, families]
  funext geom references query
  exact equal ((geom, references), query)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModel

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModel.profileFamily_local
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModel.sourceModel_unique

assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModel.SourceModel
  [TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueryMap.actualQueryProfile,
   TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.generated,
   TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedDescriptor?,
   TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames,
   TetraStereo.OneCenter.LocalizedChemicalRingJointMarkerKey.buildJoint?]
