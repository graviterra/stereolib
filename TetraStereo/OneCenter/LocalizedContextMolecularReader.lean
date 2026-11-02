import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.OneCenter.LocalizedAcyclicCarrierInjectivity
import TetraStereo.OneCenter.LocalizedAcyclicBranchCarrier
import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-!
# Pointwise molecular reader correspondence at an arbitrary context path

The molecular evidence context starts at its detected unit's existing path and then applies
`rerootWalk`.  This module identifies that result with the runtime reader for arbitrary unit paths;
the top-unit case is only a specialization.  Actual carrier occurrences also have an exact
address-depth / molecular-path-length grading, so callers need not supply those equalities.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP

variable (input : CertifiedLocalizedCIPInput)

/-- In the bounded carrier, the address depth equals the length of the actual molecular path
encoded by `molecularFrameUnit`.  This is a structural grading of the existing carrier, not a
graph-wide path enumeration. -/
theorem molecularFrameUnit_path_length_eq_address_length
    {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel) :
    (input.molecularFrameUnit occurrence.1).path.length = occurrence.1.address.length := by
  have derived := (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
  have rooted : input.DeclarativeLocalizedOccurrenceSubtree occurrence.1.root []
      (fuel + 1) (OfficialCIPNode.root occurrence.1.root) occurrence.1 := derived
  have hhistory := input.declarativeLocalizedOccurrenceSubtree_history_length rooted
    (by simp [OfficialCIPNode.root])
  change (occurrence.1.node.history.reverse.tail).length = occurrence.1.address.length
  simp only [List.length_reverse, List.length_tail]
  omega

/-- General pointwise bridge for any detected unit and any outward/backtracking source-context
walk.  The two strict-depth tests in the runtime and context adapters are aligned by the supplied
address/path length equations; when they hold, both readers consult the same detected unit. -/
theorem molecularReader_eq_readContext_of_walk
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)) {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel) (cursor : input.LocalizedRerootCursor fuel)
    (unit : DetectedOccurrence input.moleculeGraph) (steps : List input.Atom)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (targetDepth : target.1.address.length = unit.1.path.length)
    (cursorRoot : cursor.occurrence.1.root = unit.1.root)
    (cursorUnit : input.molecularFrameUnit cursor.occurrence.1 =
      ⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩)
    (cursorDepth : cursor.occurrence.1.address.length =
      (rerootWalk unit.1.root unit.1.path steps).length)
    (real : cursor.occurrence.1.node.provenance = .realAtom) :
    input.molecularReader descriptorMap target cursor =
      (readContext input.moleculeGraph descriptorMap unit steps).toLocalizedLabel := by
  let walked : OccurrenceUnit input.Atom :=
    ⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩
  have targetRoot : target.1.root = unit.1.root := congrArg OccurrenceUnit.root targetUnit
  have depthEq : input.LocalizedDepthDependency cursor.occurrence target ↔
      unit.1.path.length < walked.path.length := by
    unfold LocalizedDepthDependency
    constructor
    · rintro ⟨_roots, depth⟩
      rw [targetDepth, cursorDepth] at depth
      exact depth
    · intro depth
      constructor
      · exact cursorRoot.trans targetRoot.symm
      · rw [targetDepth, cursorDepth]
        exact depth
  have cursorDetected (h : IsDetectedCenter input.moleculeGraph walked.atom) :
      IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit cursor.occurrence.1).atom := by
    rw [cursorUnit]
    exact h
  have cursorSource (h : IsDetectedCenter input.moleculeGraph walked.atom) :
      (⟨input.molecularFrameUnit cursor.occurrence.1,
        cursorDetected h⟩ : DetectedOccurrence input.moleculeGraph) =
        ⟨walked, h⟩ := by
    apply Subtype.ext
    exact cursorUnit
  by_cases hdepth : unit.1.path.length < walked.path.length
  · have dependency := depthEq.mpr hdepth
    by_cases hcenter : IsDetectedCenter input.moleculeGraph walked.atom
    · have hcenterCursor := cursorDetected hcenter
      have hsource := cursorSource hcenter
      unfold molecularReader localizedDependencyLabel
      rw [dif_pos dependency]
      unfold molecularView
      rw [if_pos real, dif_pos hcenterCursor, hsource]
      unfold readContext contextOccurrence
      cases hvalue : descriptorMap ⟨walked, hcenter⟩ <;>
        simp [walked, hdepth, hcenter, hvalue, OccurrenceReading.toLocalizedLabel]
    · have noCenterCursor : ¬ IsDetectedCenter input.moleculeGraph
        (input.molecularFrameUnit cursor.occurrence.1).atom := by
        intro hc
        apply hcenter
        simpa [cursorUnit] using hc
      unfold molecularReader localizedDependencyLabel
      rw [dif_pos dependency]
      unfold molecularView
      rw [if_pos real, dif_neg noCenterCursor]
      unfold readContext contextOccurrence
      simp [walked, hdepth, hcenter, OccurrenceReading.toLocalizedLabel]
  · have noDependency : ¬ input.LocalizedDepthDependency cursor.occurrence target :=
      fun h => hdepth (depthEq.mp h)
    unfold molecularReader localizedDependencyLabel
    rw [dif_neg noDependency]
    unfold readContext contextOccurrence
    simp [walked, hdepth, OccurrenceReading.toLocalizedLabel]

/-- Actual-carrier façade: the address/path grading and real provenance are derived from carrier
membership and the finite single-bond acyclic hypotheses.  The only correspondence premise left
is the substantive fact that the cursor's molecular unit is the requested `rerootWalk` result. -/
theorem molecularReader_eq_readContext_of_actual_walk
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (target : input.LocalizedCIPOccurrence fuel)
    (cursor : input.LocalizedRerootCursor fuel)
    (unit : DetectedOccurrence input.moleculeGraph) (steps : List input.Atom)
    (targetUnit : input.molecularFrameUnit target.1 = unit.1)
    (cursorUnit : input.molecularFrameUnit cursor.occurrence.1 =
      ⟨unit.1.root, rerootWalk unit.1.root unit.1.path steps⟩) :
    input.molecularReader descriptorMap target cursor =
      (readContext input.moleculeGraph descriptorMap unit steps).toLocalizedLabel := by
  have targetDepth := input.molecularFrameUnit_path_length_eq_address_length target
  have cursorDepth := input.molecularFrameUnit_path_length_eq_address_length cursor.occurrence
  have targetDepth' : target.1.address.length = unit.1.path.length := by
    calc
      target.1.address.length = (input.molecularFrameUnit target.1).path.length :=
        targetDepth.symm
      _ = unit.1.path.length := by
        simpa using congrArg (fun u : OccurrenceUnit input.Atom => u.path.length) targetUnit
  have cursorRoot : cursor.occurrence.1.root = unit.1.root := by
    have h := congrArg OccurrenceUnit.root cursorUnit
    simpa using h
  have real := input.carrierOccurrence_provenance_real singleBonded acyclic cursor.occurrence
  exact input.molecularReader_eq_readContext_of_walk descriptorMap target cursor unit steps
    targetUnit targetDepth' cursorRoot cursorUnit (by
      calc
        cursor.occurrence.1.address.length =
            (input.molecularFrameUnit cursor.occurrence.1).path.length := cursorDepth.symm
        _ = (rerootWalk unit.1.root unit.1.path steps).length := by
          simpa using congrArg (fun u : OccurrenceUnit input.Atom => u.path.length) cursorUnit) real

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularFrameUnit_path_length_eq_address_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularReader_eq_readContext_of_walk
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularReader_eq_readContext_of_actual_walk
