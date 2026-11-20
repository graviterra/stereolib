import TetraStereo.OneCenter.LocalizedMarkedRetainedReachDegree
import TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
# The independent-operations report on a genuine cyclic input

`LocalizedMarkedRetainedReachDegree.assign_eq_independent_general` identifies the whole report of
the experimental retained-promoted marked evaluator with the report of the comparator-free
`independentOperations` on every intake-agreeing admitted localized single-bond input.

`cyclic_report_eq_independent` instantiates it on the accepted nine-atom cyclic input (a
three-membered carbon ring `0-2-4` whose three ring atoms are detected centres, with fluorine,
chlorine and hydrogen substituents; `LocalizedCyclicSpatialInputWitness`): every premise is
discharged from accepted facts about that input. For every geometry and every fallback key, the
experimental report equals the independent report; every generated fact on every reached
occurrence agrees.

The ring centres are auxiliary centres for one another; their recursively generated labels are
covered by the fact identification. No descriptor value is computed here and no physical
correctness of either report is claimed.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedCyclicIndependentReport

open CertifiedLocalizedCIPInput DeclarativeCIP MoleculeGraph
open LocalizedMarkedOperationEvaluator LocalizedMarkedRetainedIndependentOperations
open LocalizedMarkedRetainedReachDegree LocalizedMarkedRetainedPromotedOperations
open LocalizedMarkedReachableConfigurations
open LocalizedCyclicInputWitness LocalizedCyclicSpatialInputWitness
open UniversalProof.NativeRingHydrogenFacts UniversalProof.NativeRingRuntimeGraphFacts
open LocalizedGenericMarkedRecalculation (Geometry)

theorem cyclic_supported : ∀ bond ∈ cyclicExpanded.bonds, bond.kind.IsLocalizedCovalent := by
  intro bond member
  have single := expanded_bonds_single 0 TetrahedralInputParity.anticlockwise bond member
  exact ⟨1, by simp [single, ParsedBondKind.localizedBondOrder?]⟩

theorem cyclic_admissible : cyclicExpanded.StereochemicalAdmissible :=
  expanded_stereochemical_admissible 0 TetrahedralInputParity.anticlockwise

/-- **Whole report on the cyclic input.** For every geometry and fallback key. -/
theorem cyclic_report_eq_independent (fallback : CompleteLigandRule5Key) (geom : Geometry) :
    assign cyclicExpanded (operations cyclicSpatialCertified cyclicExpanded) geom =
      assign cyclicExpanded
        (independentOperations cyclicSpatialCertified spatial_simpleBonded fallback cyclicExpanded)
        geom :=
  assign_eq_independent_general cyclicSpatialCertified spatial_simpleBonded fallback
    cyclicExpanded spatial_agreement.1 cyclic_admissible cyclic_supported geom

/-- **Every generated auxiliary fact on the cyclic input**, at every depth, state and context. -/
theorem cyclic_facts_eq_independent (fallback : CompleteLigandRule5Key) :
    ∀ depth geom state ctx node, Reached cyclicExpanded node →
      facts cyclicExpanded (operations cyclicSpatialCertified cyclicExpanded) depth geom state
          ctx node =
        facts cyclicExpanded
          (independentOperations cyclicSpatialCertified spatial_simpleBonded fallback cyclicExpanded)
          depth geom state ctx node :=
  facts_eq_independent_general cyclicSpatialCertified spatial_simpleBonded fallback
    cyclicExpanded spatial_agreement.1 cyclic_admissible cyclic_supported

/-- The three ring atoms are detected centres of this input (accepted inventory). -/
theorem cyclic_ring_centres :
    SA ⟨0, by decide⟩ ∈ cyclicSpatialCertified.tetrahedralCenterSet ∧
      SA ⟨2, by decide⟩ ∈ cyclicSpatialCertified.tetrahedralCenterSet ∧
        SA ⟨4, by decide⟩ ∈ cyclicSpatialCertified.tetrahedralCenterSet :=
  ⟨spatial_detected_inventory.2.2.2.1, spatial_detected_inventory.2.2.2.2.1,
    spatial_detected_inventory.2.2.2.2.2⟩

end TetraStereo.OneCenter.LocalizedMarkedCyclicIndependentReport

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicIndependentReport.cyclic_supported
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicIndependentReport.cyclic_report_eq_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicIndependentReport.cyclic_facts_eq_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedCyclicIndependentReport.cyclic_ring_centres
