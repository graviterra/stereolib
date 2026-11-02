import TetraStereo.OneCenter.LocalizedRuleMajorActualCompleteReadingComparison
import TetraStereo.OneCenter.LocalizedRuleMajorCompleteReadingPrefix
import TetraStereo.OneCenter.LocalizedRuleMajorCompleteReadingOrder
import TetraStereo.OneCenter.LocalizedRerootCompoundRule4bcOutcomeOrder
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual alternative sorter for one molecular branch agrees with the independent
complete Rule-4b/4c reading order. Earlier-column equalities are derived from the actual
stage executions, not supplied as hypotheses. -/

namespace TetraStereo.OneCenter.Rule4aTableBridge
open LocalizedCumulativeDecoratedTree CertifiedLocalizedCIPInput DeclarativeCIP
open Rule4cObservationBridge
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
  {leftReference rightReference : RS}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (tetrahedral : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
  (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
  (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
  (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
  (a : input.RuleMajorRootArm center index .rule4a (input.molecularReader descriptorMap target))
  (bL : input.RuleMajorRootArm center index (.rule4b leftReference)
    (input.molecularReader descriptorMap target))
  (cL : input.RuleMajorRootArm center index (.rule4c leftReference)
    (input.molecularReader descriptorMap target))
  (bR : input.RuleMajorRootArm center index (.rule4b rightReference)
    (input.molecularReader descriptorMap target))
  (cR : input.RuleMajorRootArm center index (.rule4c rightReference)
    (input.molecularReader descriptorMap target))
  (graph : RootedDigraph input.Atom)
  (faithful : graph.FaithfulExactExpansion input.moleculeGraph center.1
    (input.canonicalLigandAtom center index))
  {W D : Nat}
  (widthBL : (ruleMajorArmGraph bL).width ≤ W) (depthBL : (ruleMajorArmGraph bL).height ≤ D)
  (widthCL : (ruleMajorArmGraph cL).width ≤ W) (depthCL : (ruleMajorArmGraph cL).height ≤ D)
  (widthBR : (ruleMajorArmGraph bR).width ≤ W) (depthBR : (ruleMajorArmGraph bR).height ≤ D)
  (widthCR : (ruleMajorArmGraph cR).width ≤ W) (depthCR : (ruleMajorArmGraph cR).height ≤ D)

include tetrahedral targetRoot targetAddress singleBonded acyclic a faithful
  widthBL depthBL widthCL depthCL widthBR depthBR widthCR depthCR

theorem actual_ruleMajor_completeReading_compare :
    input.compareRule4bcReadingsComplete
        { reference? := some leftReference, rule4bKey := bL.key, rule4cKey := cL.key }
        { reference? := some rightReference, rule4bKey := bR.key, rule4cKey := cR.key } =
      compare
        (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graph W D (some (senseOf leftReference)))
        (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graph W D (some (senseOf rightReference))) := by
  have prefixes := input.ruleMajor_sameBranch_reading_prefixes
    (input.molecularReader descriptorMap target) _ (input.localizedLigandRootCursor center index)
    leftReference rightReference a.key bL.key cL.key bR.key cR.key
    a.built bL.built cL.built bR.built cR.built
  have selfCompare : ∀ table : List (List (OfficialSparseEntry Nat)),
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat table table = .eq :=
    CompilerProjectionFidelity.compareSparseLayers_self OfficialRuleMajorKey.compareNat
      CompilerProjectionFidelity.compareNat_self
  have tiedB : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      bL.key.constitutional.rule1a bR.key.constitutional.rule1a = .eq := by
    rw [prefixes.1]; exact selfCompare _
  have tiedBA : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a bL.key) (scalar4a bR.key) = .eq := by
    rw [prefixes.2.1]; exact selfCompare _
  have tiedC : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      cL.key.constitutional.rule1a cR.key.constitutional.rule1a = .eq := by
    rw [prefixes.2.2.1]; exact selfCompare _
  have tiedCA : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4a cL.key) (scalar4a cR.key) = .eq := by
    rw [prefixes.2.2.2.1]; exact selfCompare _
  have readB := actual_ruleMajor_scalar4b_compare descriptorMap tetrahedral target targetRoot
    targetAddress singleBonded acyclic bL bR graph graph faithful faithful
    widthBL depthBL widthBR depthBR tiedB tiedBA
  have readC := actual_ruleMajor_scalar4c_compare descriptorMap tetrahedral target targetRoot
    targetAddress singleBonded acyclic cL cR graph graph faithful faithful
    widthCL depthCL widthCR depthCR tiedC tiedCA
  rw [completeReading_compare_eq_then]
  change
    (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
      bL.key.descriptor bR.key.descriptor).then
      (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        cL.key.descriptor cR.key.descriptor) =
    (compare
      (readingAt input.moleculeGraph descriptorMap (input.topUnit center) graph W D
        (senseOf leftReference))
      (readingAt input.moleculeGraph descriptorMap (input.topUnit center) graph W D
        (senseOf rightReference))).then _
  rw [compare_descriptor_eq_scalar4b_of_scalar4a_eq bL.tableMatch bR.tableMatch prefixes.2.1,
    ← readB]
  cases comparison : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (scalar4b bL.key) (scalar4b bR.key) with
  | lt => rfl
  | gt => rfl
  | eq =>
      simp only [Ordering.eq_then]
      have equalB : scalar4b cL.key = scalar4b cR.key := by
        rw [← prefixes.2.2.2.2.1, ← prefixes.2.2.2.2.2]
        exact (compareSparseLayers_compareNat_eq_iff _ _).mp comparison
      rw [compare_descriptor_eq_scalar4c_of_prior_columns_eq
        cL.tableMatch cR.tableMatch prefixes.2.2.2.1 equalB]
      exact readC

/-- Outcome-ordering of the actual two alternatives has precisely the independent observable
maximum/minimum order. This assertion deliberately forgets occurrence metadata and identities. -/
theorem actual_ruleMajor_rankReadings_observations :
    (input.rankReadings
      [{ reference? := some leftReference, rule4bKey := bL.key, rule4cKey := cL.key },
       { reference? := some rightReference, rule4bKey := bR.key, rule4cKey := cR.key }]).map
      (fun reading => completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
        graph W D (reading.reference?.map senseOf)) =
      [max
        (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graph W D (some (senseOf leftReference)))
        (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graph W D (some (senseOf rightReference))),
       min
        (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graph W D (some (senseOf leftReference)))
        (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graph W D (some (senseOf rightReference)))] := by
  have comparison := actual_ruleMajor_completeReading_compare descriptorMap tetrahedral target
    targetRoot targetAddress singleBonded acyclic a bL cL bR cR graph faithful
    widthBL depthBL widthCL depthCL widthBR depthBR widthCR depthCR
  simp only [rankReadings]
  rw [comparison]
  split_ifs with h
  · simpa only [List.map_cons, List.map_nil, Option.map_some, if_pos h] using
      (completeReading_descendingPair
        (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graph W D (some (senseOf leftReference)))
        (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graph W D (some (senseOf rightReference))))
  · simpa only [List.map_cons, List.map_nil, Option.map_some, if_neg h] using
      (completeReading_descendingPair
        (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graph W D (some (senseOf leftReference)))
        (completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
          graph W D (some (senseOf rightReference))))

end
end TetraStereo.OneCenter.Rule4aTableBridge

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.actual_ruleMajor_completeReading_compare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.actual_ruleMajor_rankReadings_observations
