import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceStateReadback
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedStructuralProfile
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Fuel-free candidate profiles read through molecular occurrence support.
The source map takes a candidate optional descriptor at each raw molecular node. At structural
depth the actual generated snapshot is exactly this map of the evaluator's stable profile.
Unsupported occurrences, refusals, ordered contexts and each geometry are all included. This
removes caller-specific residual fuel from the model's candidate-reader interface.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceProfileMap

open CertifiedLocalizedCIPInput DeclarativeCIP
open LocalizedGenericMarkedRecalculation (Geometry WellFormedBonds structuralDepth)
open LocalizedMarkedReachableConfigurations (Reached)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open LocalizedMarkedRetainedStateReader (rawStateDescriptorMap)
open LocalizedChemicalRingJointPreparedExecution (generated)
open LocalizedChemicalRingJointPreparedSourceStateReadback
open LocalizedChemicalRingJointPreparedStructuralProfile

noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)

/-- The source map of an arbitrary candidate profile. The node's complete molecular occurrence
identity, strict descent and detection determine support; the candidate supplies only its label. -/
def sourceProfileMap (source : RawMolecule.CanonicalBranchNode)
    (candidate : RawMolecule.CanonicalBranchNode → Option LocalizedTetrahedralRSPseudoDescriptor) :
    DescriptorMap (DetectedOccurrence input.moleculeGraph) :=
  candidateSourceMap input mol (structuralDepth mol source) source (fun _ => candidate)

/-- Source-map locality uses strict canonical descendants, with no equality at the source or on
unrelated branches. Changing contexts or geometries can be handled before supplying the profile. -/
theorem sourceProfileMap_congr
    (source : RawMolecule.CanonicalBranchNode) (reached : Reached mol source)
    (first second : RawMolecule.CanonicalBranchNode → Option LocalizedTetrahedralRSPseudoDescriptor)
    (agree : ∀ query, StrictDescendant mol source query → first query = second query) :
    sourceProfileMap input mol source first = sourceProfileMap input mol source second :=
  candidateSourceMap_congr_of_agree input mol (structuralDepth mol source) source
    (fun _ => first) (fun _ => second) reached (fun _ query path _ => agree query path)

/-- On every detected occurrence, the actual generated map at structural depth is the source
map of one global stable profile. No supplied-label or successful-lookup hypothesis remains. -/
theorem generated_map_eq_sourceProfileMap
    (wellFormed : WellFormedBonds mol) (geom : Geometry) (references : List input.Atom)
    (source : RawMolecule.CanonicalBranchNode) (reached : Reached mol source) :
    rawStateDescriptorMap input
        (generated input mol (structuralDepth mol source) geom source references) =
      sourceProfileMap input mol source (stableProfile input mol geom references) := by
  classical
  rw [rawStateDescriptorMap_generated_eq_candidateSourceMap input mol
    (structuralDepth mol source) geom source references reached]
  funext unit
  unfold sourceProfileMap candidateSourceMap candidateSourceReader
  split
  · rw [residual_eq_structuralDepth mol wellFormed reached]
    rfl
  · rfl

/-- Any profile agreeing with the actual stable profile on strict descendants gives the exact
generated descriptor map. This is the induction hypothesis used by the independent-model join. -/
theorem generated_map_eq_of_descendant_profile
    (wellFormed : WellFormedBonds mol) (geom : Geometry) (references : List input.Atom)
    (source : RawMolecule.CanonicalBranchNode) (reached : Reached mol source)
    (candidate : RawMolecule.CanonicalBranchNode → Option LocalizedTetrahedralRSPseudoDescriptor)
    (agree : ∀ query, StrictDescendant mol source query →
      stableProfile input mol geom references query = candidate query) :
    rawStateDescriptorMap input
        (generated input mol (structuralDepth mol source) geom source references) =
      sourceProfileMap input mol source candidate :=
  (generated_map_eq_sourceProfileMap input mol wellFormed geom references source reached).trans
    (sourceProfileMap_congr input mol source reached _ _ agree)

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceProfileMap

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceProfileMap.sourceProfileMap_congr
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceProfileMap.generated_map_eq_sourceProfileMap
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceProfileMap.generated_map_eq_of_descendant_profile

assert_closure_excludes TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceProfileMap.sourceProfileMap
  [TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedStructuralProfile.stableProfile,
   TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedExecution.generated,
   TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedFacts,
   TetraStereo.OneCenter.LocalizedChemicalRingPreparedContextRecursion.preparedDescriptor?,
   TetraStereo.OneCenter.LocalizedMarkedRetainedStateReader.rawStateDescriptorMap]
