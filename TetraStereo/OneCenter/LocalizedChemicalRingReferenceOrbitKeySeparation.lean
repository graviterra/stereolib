import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringPath
import TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathKeySeparation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 3200000

/-! Concrete original-root comparison data for the accepted 46-atom input. The actual
generated snapshot explicitly uses inherited reference 30. A covering-path observation
connects finite branch-exchange parity to actual key separation without state execution.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitKeySeparation

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry RetainedRingSymmetryReconstruction
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitCoveringPath LocalizedChemicalRingInheritedRefusalCases
open LocalizedChemicalRingCoveredPathKeySeparation LocalizedChemicalRingBoundaryWitnessExecution
open LocalizedChemicalRingBoundaryWitnessFactMatch LocalizedChemicalRingWitnessFactMatch
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedMarkedReachableConfigurations (reached_root)
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedChemicalRingFrameReadback
open LocalizedGenericMarkedRecalculation (structuralDepth)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)

noncomputable section
open scoped Classical

def rootCenter : physical.Center := ⟨(0 : Fin 46), by
  change (0 : Fin 46) ∈ graph.tetrahedralCenterSet
  rw [detected_inventory]
  decide⟩

def rootData : OccurrenceData certified mol rootCenter (canonicalCenterRoot 0) :=
  Classical.choice (occurrenceData_exists certified mol structure_agreement admissible supported
    single_bonded rootCenter (canonicalCenterRoot 0) (reached_root mol 0 (by decide)) rfl rfl)

def rootSnapshot := snapshotWith LocalizedChemicalRingInheritedFallback.rawStep? certified mol
  (structuralDepth mol (canonicalCenterRoot 0)) (inputGeometry certified) (canonicalCenterRoot 0)
  reference.val

private def leftLigand : Fin 4 := Classical.choose
  (physical.ligandAtomAt_surjective rootCenter (28 : Fin 46) (by decide +kernel))
private def rightLigand : Fin 4 := Classical.choose
  (physical.ligandAtomAt_surjective rootCenter (29 : Fin 46) (by decide +kernel))

def leftSlot : Fin 4 := rootData.ligandOf.symm leftLigand
def rightSlot : Fin 4 := rootData.ligandOf.symm rightLigand

theorem slot_atoms :
    referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData leftSlot = (28 : Fin 46) ∧
    referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData rightSlot = (29 : Fin 46) := by
  constructor
  · simpa only [referenceAt, leftSlot, Equiv.apply_symm_apply] using
      Classical.choose_spec (physical.ligandAtomAt_surjective rootCenter (28 : Fin 46) (by decide +kernel))
  · simpa only [referenceAt, rightSlot, Equiv.apply_symm_apply] using
      Classical.choose_spec (physical.ligandAtomAt_surjective rootCenter (29 : Fin 46) (by decide +kernel))

private theorem root_history : rootData.target.1.node.history = [(0 : Fin 46)] := by
  apply List.map_injective_iff.mpr Fin.val_injective
  exact (LocalizedMarkedCarrierLookup.lookup?_sound certified _ _ rootData.found).history

private theorem root_address : rootData.target.1.address = [] := by
  have address := (certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded rootData.target)).sourceAddress
  rw [address]
  simp [CertifiedLocalizedCIPInput.canonicalAddress, root_history]

private theorem root_root : rootData.target.1.root = (0 : Fin 46) := by
  have head := (certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded rootData.target)).sourceHead
  simpa [root_history] using head.symm

private abbrev rootUnit : DetectedOccurrence graph :=
  ⟨certified.molecularFrameUnit rootData.target.1, rootData.detected⟩

private theorem slot_current (slot : Fin 4) (a : Fin 46)
    (atAtom : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData slot = a) :
    ((frames certified single_bonded rootSnapshot rootData.target rootData.real rootUnit rfl).frame.cursorAt slot).occurrence.1.node.current? = some a := by
  have frameEq : (frames certified single_bonded rootSnapshot rootData.target rootData.real rootUnit rfl).frame = rootData.frame :=
    Option.some.inj ((frames certified single_bonded rootSnapshot rootData.target rootData.real rootUnit rfl).frameComputed.symm.trans rootData.frameExec)
  have mapped : (((frames certified single_bonded rootSnapshot rootData.target rootData.real rootUnit rfl).frame.cursorAt slot).occurrence.1.node.current?).map Fin.val = some a.val := by
    change atomAt certified _ slot = some a.val
    rw [frameEq, rootData.atomAt_eq]
    exact congrArg (fun x : Fin 46 => some x.val) atAtom
  cases found : ((frames certified single_bonded rootSnapshot rootData.target rootData.real rootUnit rfl).frame.cursorAt slot).occurrence.1.node.current? with
  | none => simp [found] at mapped
  | some b =>
      simp only [found, Option.map_some, Option.some.injEq] at mapped
      exact congrArg some (Fin.ext mapped)

private theorem covering_residual :
    ResidualObsPath graph [rootData.target.1.root] (28 : Fin 46) coveringPath.tail := by
  rw [root_root]
  refine ⟨by decide, rfl, by decide, ?_, ?_⟩
  · decide +kernel
  · simp only [coveringPath, List.tail_cons, BondedChain]
    decide +kernel

private theorem covering_query :
    rawPathNode rootData.target.1.root (boundaryPath rootData.target coveringPath.tail) = coveringNode := by
  unfold boundaryPath
  rw [root_history, root_root]
  rfl

private theorem covering_query_centers (c : physical.Center) :
    c.1.val ∈ (rawPathNode rootData.target.1.root (boundaryPath rootData.target coveringPath.tail)).history := by
  rw [covering_query]
  exact List.mem_reverse.mpr (List.mem_map.mpr ⟨c.1, covering_detected c.1 c.2, rfl⟩)

/-- The concrete reduction retains no execution, comparison, label-match or descendant
orientation premise. The remaining finite exchange-sign theorem is supplied separately. -/
theorem root_keys_ne_of_exchange_sign
    (reverses : ∀ e : physical.Aut, e.val (0 : Fin 46) = (0 : Fin 46) →
      e.val (28 : Fin 46) = (29 : Fin 46) →
      e.val reference = reference → physical.centerPerm e current = current ∧
        relativeSign physical cfg e current = -1) :
    markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
        rootSnapshot reference leftSlot ≠
      markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
        rootSnapshot reference rightSlot := by
  apply actual_root_keys_ne_of_covered_observation certified mol structure_agreement admissible
    supported single_bonded cfg rootData.target rootData.real rootUnit rfl root_address reference
    (structuralDepth mol (canonicalCenterRoot 0)) (canonicalCenterRoot 0)
    (reached_root mol 0 (by decide)) leftSlot rightSlot (28 : Fin 46) (29 : Fin 46)
    coveringPath.tail covering_residual current rfl calibrated covering_query_centers
    ⟨0, constant_charge⟩
  · simpa only [root_root] using reverses
  · exact slot_current leftSlot 28 slot_atoms.1
  · exact slot_current rightSlot 29 slot_atoms.2
  · rw [covering_query]
    exact covering_snapshot_label_present

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitKeySeparation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitKeySeparation.slot_atoms
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitKeySeparation.root_keys_ne_of_exchange_sign
