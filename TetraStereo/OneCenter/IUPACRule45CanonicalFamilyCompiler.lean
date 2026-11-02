import TetraStereo.OneCenter.IUPACRule45CanonicalProvisionFamily

set_option autoImplicit false

/-!
# Compiler boundary for the canonical Rules 4b/5 family

One active builder-free complete trace is projected into all typed family observations and then
compiled into the nonvacuity witnesses consumed by provision batches.  This module is owned by
the mathematical family, so concrete fixtures and global compilers can share it without cycles.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

structure Rule45CanonicalFamilyNonvacuityWitnesses : Prop where
  nonvacuous : ∀ family : Rule45CanonicalProvisionFamily,
    ∃ source, ∃ observation : family.completeReference.Observation,
      source.StructurallyWellFormed ∧
        family.completeReference.Applicable source ∧
          family.completeReference.Judges source observation

/-- Project one complete canonical trace into any typed family observation. -/
def rule45CanonicalTraceFamilyObservation
    (observation : Rule45CanonicalTraceObservation)
    (family : Rule45CanonicalProvisionFamily) :
    Rule45CanonicalFamilyObservation family :=
  { carrierFuel := observation.carrierFuel
    ruleFuel := observation.ruleFuel
    centerAtom := observation.centerAtom
    left := observation.left
    right := observation.right
    outcome := family.project observation.trace }

/-- The sole nonvacuity boundary for every canonical Rules-4b/5 provision. -/
structure Rule45CanonicalTraceNonvacuitySeed where
  source : AuthoritativeChemicalInput
  wellFormed : source.StructurallyWellFormed
  observation : Rule45CanonicalTraceObservation
  canonicalComplete :
    Rule45CanonicalTraceCanonicalCompleteJudged source observation
  active : ∀ family : Rule45CanonicalProvisionFamily,
    family.Active observation.trace

theorem rule45CanonicalFamily_canonicalComplete_of_traceSeed
    (seed : Rule45CanonicalTraceNonvacuitySeed)
    (family : Rule45CanonicalProvisionFamily) :
    Rule45CanonicalFamilyCanonicalCompleteJudged family seed.source
      (rule45CanonicalTraceFamilyObservation seed.observation family) := by
  exact ⟨seed.observation.trace, seed.canonicalComplete, seed.active family, rfl⟩

/-- One molecular trace supplies every family witness consumed by the global compiler. -/
theorem Rule45CanonicalFamilyNonvacuityWitnesses.of_traceSeed
    (seed : Rule45CanonicalTraceNonvacuitySeed) :
    Rule45CanonicalFamilyNonvacuityWitnesses where
  nonvacuous := by
    intro family
    let observation := rule45CanonicalTraceFamilyObservation seed.observation family
    have judged : Rule45CanonicalFamilyCanonicalCompleteJudged
        family seed.source observation :=
      rule45CanonicalFamily_canonicalComplete_of_traceSeed seed family
    exact ⟨seed.source, observation, seed.wellFormed,
      ⟨observation, judged⟩, judged⟩

/-- Build the single trace seed from one actual canonical partition pair. -/
noncomputable def rule45CanonicalTraceNonvacuitySeed_of_activePartitionPair
    (source : AuthoritativeChemicalInput)
    (wellFormed : source.StructurallyWellFormed)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (roots : List (source.AromaticCanonicalRerootCursor carrierFuel))
    (partition : source.AromaticCanonicalRule3Through5InitialPartition carrierFuel)
    (left right : Fin 4)
    (distinct : left ≠ right)
    (rootsComputed : source.aromaticCanonicalOccurrenceLigandFrame?
      (source.aromaticCanonicalFinalOccurrence carrierFuel center) = some roots)
    (partitionCanonical :
      let semantics := source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel
      let target := source.aromaticCanonicalFinalOccurrence carrierFuel center
      let state := source.aromaticCanonicalScheduledAuxiliaryState semantics
      let view := source.aromaticCanonicalDependencyView state target
      source.CanonicalAromaticCanonicalRule3Through5InitialPartition
        target view ruleFuel roots partition)
    (rule3Tie : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
      (partition.frame.keyAt left).rule3 (partition.frame.keyAt right).rule3 = .eq)
    (leftReferences : (partition.frame.keyAt left).rule45.prior.references ≠ [])
    (rightReferences : (partition.frame.keyAt right).rule45.prior.references ≠ [])
    (countTie : compare
      (partition.frame.keyAt left).rule45.prior.referenceCountPriority
      (partition.frame.keyAt right).rule45.prior.referenceCountPriority = .eq)
    (rule4bTie : source.compareAromaticCanonicalRerootCompoundRule4bReadings
      (partition.frame.keyAt left).rule45.prior.readings
      (partition.frame.keyAt right).rule45.prior.readings = .eq)
    (rule4cTie : source.compareAromaticCanonicalRerootCompoundRule4cReadings
      (partition.frame.keyAt left).rule45.prior.readings
      (partition.frame.keyAt right).rule45.prior.readings = .eq) :
    Rule45CanonicalTraceNonvacuitySeed := by
  let trace := source.rule45CanonicalComparisonTrace
    (partition.frame.keyAt left).rule45 (partition.frame.keyAt right).rule45
  let observation : Rule45CanonicalTraceObservation :=
    { carrierFuel
      ruleFuel
      centerAtom := center.1.val
      left
      right
      trace }
  refine
    { source
      wellFormed
      observation
      canonicalComplete := ?_
      active := ?_ }
  · unfold Rule45CanonicalTraceCanonicalCompleteJudged
    dsimp only
    exact ⟨center, roots, partition, rfl, distinct, rootsComputed,
      partitionCanonical, rule3Tie,
      (source.rule45CanonicalComparisonTrace_eq_iff_judgment _ _ trace).mp rfl⟩
  · intro family
    cases family with
    | rule4bPairingMethodology =>
        exact ⟨leftReferences, rightReferences⟩
    | rule4bLikeUnlike =>
        exact ⟨leftReferences, rightReferences, countTie⟩
    | rule5Enantiomorph =>
        exact ⟨countTie, rule4bTie, rule4cTie⟩

end IUPACNormativeProvision
end TetraStereo.OneCenter
