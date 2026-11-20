import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueries
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Candidate maps on the exact molecular detected-query domain.
All supported reads are in this domain, so values at other raw nodes have no effect. This
provides the concrete state-to-reader adapter for the independent context-indexed model,
including locality and the actual generated-state realization without supplied label matches.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueryMap

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedGenericMarkedRecalculation (Geometry WellFormedBonds structuralDepth)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open LocalizedMarkedRetainedStateReader (rawStateDescriptorMap)
open LocalizedChemicalRingJointPreparedSourceStateReadback
open LocalizedChemicalRingJointPreparedSourceProfileMap
open LocalizedChemicalRingJointPreparedSourceQueries
open LocalizedChemicalRingJointPreparedStructuralProfile (stableProfile)
open LocalizedChemicalRingJointPreparedExecution (generated)

noncomputable section
open scoped Classical

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)

/-- Extend a candidate on molecular detected queries by absence elsewhere. -/
def extendQueryProfile
    (candidate : SourceQuery input mol → Option LocalizedTetrahedralRSPseudoDescriptor)
    (node : RawMolecule.CanonicalBranchNode) : Option LocalizedTetrahedralRSPseudoDescriptor :=
  if eligible : QueryEligible input mol node then candidate ⟨node, eligible⟩ else none

/-- The independent candidate reader indexed by genuine reached detected occurrences. -/
def sourceQueryMap (source : SourceQuery input mol)
    (candidate : SourceQuery input mol → Option LocalizedTetrahedralRSPseudoDescriptor) :
    DescriptorMap (DetectedOccurrence input.moleculeGraph) :=
  sourceProfileMap input mol source.1 (extendQueryProfile input mol candidate)

/-- Restriction to detected molecular queries loses no supported read, even if the arbitrary
raw profile assigned values outside that domain. -/
theorem sourceProfileMap_eq_restricted
    (source : SourceQuery input mol)
    (candidate : RawMolecule.CanonicalBranchNode → Option LocalizedTetrahedralRSPseudoDescriptor) :
    sourceProfileMap input mol source.1 candidate =
      sourceQueryMap input mol source (fun query => candidate query.1) := by
  funext unit
  unfold sourceQueryMap sourceProfileMap candidateSourceMap candidateSourceReader
  split
  · rename_i supported
    have eligible := supported_query_eligible input mol source.2.1 unit
      (Classical.choose_spec supported.2)
    simp only [extendQueryProfile, dif_pos eligible]
  · rfl

/-- The source query map depends only on strictly deeper molecular queries. -/
theorem sourceQueryMap_local (source : SourceQuery input mol)
    (first second : SourceQuery input mol → Option LocalizedTetrahedralRSPseudoDescriptor)
    (agree : ∀ query, StrictDescendant mol source.1 query.1 → first query = second query) :
    sourceQueryMap input mol source first = sourceQueryMap input mol source second := by
  apply sourceProfileMap_congr input mol source.1 source.2.1
  intro node path
  by_cases eligible : QueryEligible input mol node
  · simp only [extendQueryProfile, dif_pos eligible]
    exact agree ⟨node, eligible⟩ path
  · simp only [extendQueryProfile, dif_neg eligible]

/-- The actual global stable profile, restricted to the molecular query domain. -/
def actualQueryProfile (geom : Geometry) (references : List input.Atom)
    (query : SourceQuery input mol) : Option LocalizedTetrahedralRSPseudoDescriptor :=
  stableProfile input mol geom references query.1

/-- The actual generated descriptor map equals the independent query-state reader of the
actual stable profile. Unsupported entries and refused labels are included pointwise. -/
theorem generated_map_eq_sourceQueryMap (wellFormed : WellFormedBonds mol)
    (geom : Geometry) (references : List input.Atom) (source : SourceQuery input mol) :
    rawStateDescriptorMap input
        (generated input mol (structuralDepth mol source.1) geom source.1 references) =
      sourceQueryMap input mol source (actualQueryProfile input mol geom references) :=
  (generated_map_eq_sourceProfileMap input mol wellFormed geom references source.1 source.2.1).trans
    (sourceProfileMap_eq_restricted input mol source _)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueryMap

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueryMap.sourceProfileMap_eq_restricted
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueryMap.sourceQueryMap_local
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueryMap.generated_map_eq_sourceQueryMap

assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueryMap.sourceQueryMap
  [TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceQueryMap.actualQueryProfile,
   TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedStructuralProfile.stableProfile,
   TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.generated,
   TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedDescriptor?,
   TetraStereo.OneCenter.LocalizedMarkedRetainedOrdinaryRanking.rawStateFrames]
