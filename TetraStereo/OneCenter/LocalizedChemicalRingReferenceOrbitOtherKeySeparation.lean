import TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathMirrorKeySeparation
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMirrorObservation
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitSecondReferenceSeparation
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingDefaultMarkerLayout
import TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathKeySeparation
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherObservation
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherExchangeSign
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16384

/-! Both O16 inherited references produce four distinct actual root keys, on the
original and reflected geometries. The second covering path supplies actual observations
at center26; any residual O18 branch exchange would reverse that calibrated center.
No descriptor, comparison, successful observation or state agreement is supplied.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherKeySeparation

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry RetainedRingSymmetryReconstruction
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitCoveringPath LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitCoveringSymmetry
open LocalizedChemicalRingReferenceOrbitSecondReferenceSeparation (secondReference)
open LocalizedChemicalRingReferenceOrbitOtherObservation
open LocalizedChemicalRingReferenceOrbitOtherExchangeSign
open LocalizedChemicalRingReferenceOrbitAllCalibration
open LocalizedChemicalRingReferenceOrbitOtherCoveringPath
open LocalizedChemicalRingCoveredPathKeySeparation
open LocalizedChemicalRingReferenceOrbitStabilizer LocalizedChemicalRingInheritedRefusalCases
open LocalizedChemicalRingCoveredPathMirrorKeySeparation LocalizedChemicalRingDefaultMarkerLayout
open LocalizedChemicalRingBoundaryWitnessExecution LocalizedChemicalRingBoundaryWitnessFactMatch
open LocalizedChemicalRingWitnessFactMatch LocalizedChemicalRingFrameReadback
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedMolecularSelection
open LocalizedMarkedRetainedOrdinaryRanking LocalizedMarkedRetainedPromotedRanking
open LocalizedMarkedRetainedStateReader (factLabel)
open LocalizedMarkedReachableConfigurations (reached_root)
open LocalizedGenericMarkedRecalculation (structuralDepth mirror)
open LocalizedPhysicalMarkedParityCompleteness (relativeSign)

noncomputable section
open scoped Classical

def sideSnapshot (side : Bool) (mark : Fin 46) := snapshotWith LocalizedChemicalRingInheritedFallback.rawStep?
  certified mol (structuralDepth mol (canonicalCenterRoot 0)) (observedGeometry certified side)
  (canonicalCenterRoot 0) mark.val

private def leftLigand : Fin 4 := Classical.choose
  (physical.ligandAtomAt_surjective rootCenter (30 : Fin 46) (by decide +kernel))
private def rightLigand : Fin 4 := Classical.choose
  (physical.ligandAtomAt_surjective rootCenter (31 : Fin 46) (by decide +kernel))

def otherLeftSlot : Fin 4 := rootData.ligandOf.symm leftLigand
def otherRightSlot : Fin 4 := rootData.ligandOf.symm rightLigand

private theorem other_slot_atoms :
    referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData otherLeftSlot = (30 : Fin 46) ∧
    referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData otherRightSlot = (31 : Fin 46) := by
  constructor
  · simpa only [referenceAt, otherLeftSlot, Equiv.apply_symm_apply] using
      Classical.choose_spec (physical.ligandAtomAt_surjective rootCenter (30 : Fin 46) (by decide +kernel))
  · simpa only [referenceAt, otherRightSlot, Equiv.apply_symm_apply] using
      Classical.choose_spec (physical.ligandAtomAt_surjective rootCenter (31 : Fin 46) (by decide +kernel))

private def slotAtom (i : Fin 4) : Fin 46 :=
  referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData i

private theorem slotAtom_injective : Function.Injective slotAtom := by
  intro i j same
  apply rootData.ligandOf.injective
  exact physical.ligandAtomAt_injective rootCenter same

private theorem slotAtom_neighbor (i : Fin 4) : graph.Adj 0 (slotAtom i) :=
  physical.ligandAtomAt_adj rootCenter (rootData.ligandOf i)

private theorem fixed28_of_mark (mark : Fin 46)
    (hmark : mark = (28 : Fin 46) ∨ mark = 29) (e : graph.Aut)
    (fixedMark : e.val mark = mark) : e.val (28 : Fin 46) = 28 := by
  rcases hmark with rfl | rfl
  · exact fixedMark
  · apply fixed_of_signature graph e [29] 28
    · intro a present
      have same : a = (29 : Fin 46) := List.mem_singleton.mp present
      simpa only [same] using fixedMark
    · unfold SignatureUnique
      decide +kernel

private theorem exchange_negative (mark : Fin 46)
    (hmark : mark = (28 : Fin 46) ∨ mark = 29) (e : physical.Aut)
    (_rootFixed : e.val (0 : Fin 46) = (0 : Fin 46))
    (entry : e.val (30 : Fin 46) = (31 : Fin 46)) (refFixed : e.val mark = mark) :
    physical.centerPerm e otherCurrent = otherCurrent ∧ relativeSign physical cfg e otherCurrent = -1 :=
  other_exchange_negative cfg e mark hmark refFixed entry

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

private theorem slot_current (side : Bool) (mark : Fin 46) (i : Fin 4) :
    ((frames certified single_bonded (sideSnapshot side mark) rootData.target rootData.real
      rootUnit rfl).frame.cursorAt i).occurrence.1.node.current? = some (slotAtom i) := by
  have frameEq :
      (frames certified single_bonded (sideSnapshot side mark) rootData.target rootData.real rootUnit rfl).frame =
        rootData.frame :=
    Option.some.inj ((frames certified single_bonded (sideSnapshot side mark) rootData.target rootData.real
      rootUnit rfl).frameComputed.symm.trans rootData.frameExec)
  have mapped : (((frames certified single_bonded (sideSnapshot side mark) rootData.target rootData.real
      rootUnit rfl).frame.cursorAt i).occurrence.1.node.current?).map Fin.val =
        some (slotAtom i).val := by
    change atomAt certified _ i = some (slotAtom i).val
    rw [frameEq]
    exact rootData.atomAt_eq i
  cases found : ((frames certified single_bonded (sideSnapshot side mark) rootData.target rootData.real
      rootUnit rfl).frame.cursorAt i).occurrence.1.node.current? with
  | none => simp [found] at mapped
  | some a =>
      simp only [found, Option.map_some, Option.some.injEq] at mapped
      exact congrArg some (Fin.ext mapped)

private theorem covering_residual :
    ResidualObsPath graph [rootData.target.1.root] (30 : Fin 46) otherPath.tail := by
  rw [root_root]
  refine ⟨by decide, rfl, by decide, ?_, ?_⟩
  · decide +kernel
  · simp only [otherPath, List.tail_cons, BondedChain]
    decide +kernel

private theorem covering_query :
    rawPathNode rootData.target.1.root (boundaryPath rootData.target otherPath.tail) = otherNode := by
  unfold boundaryPath
  rw [root_history, root_root]
  rfl

private theorem covering_query_centers (c : physical.Center) :
    c.1.val ∈ (rawPathNode rootData.target.1.root (boundaryPath rootData.target otherPath.tail)).history := by
  rw [covering_query]
  exact List.mem_reverse.mpr (List.mem_map.mpr ⟨c.1, other_detected c.1 c.2, rfl⟩)

/-- Either O16 mark separates the O18 arms on its own generated geometry-side snapshot. -/
theorem other_keys_separate (side : Bool) (mark : Fin 46) (hmark : mark = (28 : Fin 46) ∨ mark = 29) :
    markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
        (sideSnapshot side mark) mark otherLeftSlot ≠
      markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
        (sideSnapshot side mark) mark otherRightSlot := by
  cases side with
  | false =>
    apply actual_root_keys_ne_of_covered_observation certified mol structure_agreement admissible
      supported single_bonded cfg rootData.target rootData.real rootUnit rfl root_address mark
      (structuralDepth mol (canonicalCenterRoot 0)) (canonicalCenterRoot 0)
      (reached_root mol 0 (by decide)) otherLeftSlot otherRightSlot (30 : Fin 46) (31 : Fin 46)
      otherPath.tail covering_residual otherCurrent rfl other_calibrated covering_query_centers
      ⟨0, constant_charge⟩
    · simpa only [root_root] using exchange_negative mark hmark
    · simpa only [slotAtom, other_slot_atoms.1] using slot_current false mark otherLeftSlot
    · simpa only [slotAtom, other_slot_atoms.2] using slot_current false mark otherRightSlot
    · rw [covering_query]
      exact other_snapshot_label_present_at mark
  | true =>
    apply actual_root_mirror_keys_ne_of_covered_observation certified mol structure_agreement admissible
      supported single_bonded cfg rootData.target rootData.real rootUnit rfl root_address mark
      (structuralDepth mol (canonicalCenterRoot 0)) (canonicalCenterRoot 0)
      (reached_root mol 0 (by decide)) otherLeftSlot otherRightSlot (30 : Fin 46) (31 : Fin 46)
      otherPath.tail covering_residual otherCurrent rfl other_calibrated covering_query_centers
      ⟨0, constant_charge⟩
    · simpa only [root_root] using exchange_negative mark hmark
    · simpa only [slotAtom, other_slot_atoms.1] using slot_current true mark otherLeftSlot
    · simpa only [slotAtom, other_slot_atoms.2] using slot_current true mark otherRightSlot
    · rw [covering_query]
      exact other_mirror_snapshot_label_present_at mark

private theorem root_neighbors (a : Fin 46) :
    graph.Adj 0 a → a = 30 ∨ a = 31 ∨ a = 28 ∨ a = 29 := by
  fin_cases a <;> decide +kernel

private theorem remaining_pair (a b : Fin 46)
    (first : a = 30 ∨ a = 31 ∨ a = 28 ∨ a = 29)
    (second : b = 30 ∨ b = 31 ∨ b = 28 ∨ b = 29)
    (different : a ≠ b) (mass : graph.atomMass a = graph.atomMass b)
    (fix30 : a = 28 → b = 28) (fix31 : a = 29 → b = 29) :
    (a = 30 ∧ b = 31) ∨ (a = 31 ∧ b = 30) := by
  revert different mass fix30 fix31
  rcases first with rfl | rfl | rfl | rfl <;>
    rcases second with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Actual key injectivity for either O16 reference, on either geometry side. -/
theorem other_markedKeys_injective (side : Bool) (mark : Fin 46)
    (hmark : mark = (28 : Fin 46) ∨ mark = 29) : Function.Injective
    (markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
      (sideSnapshot side mark) mark) := by
  intro i j tied
  by_cases same : slotAtom i = slotAtom j
  · exact slotAtom_injective same
  obtain ⟨π, aut, _, entry, referenceFixed⟩ :=
    actual_root_default_tie_reference_fixed_aut certified single_bonded (sideSnapshot side mark)
      rootData.target rootData.real rootUnit rfl root_address mark i j tied (slotAtom i) (slotAtom j)
      (slot_current side mark i) (slot_current side mark j) ⟨0, constant_charge⟩
  let e : graph.Aut := ⟨π, aut⟩
  have fixed28 : π (28 : Fin 46) = (28 : Fin 46) := fixed28_of_mark mark hmark e referenceFixed
  have fixed29 : π (29 : Fin 46) = (29 : Fin 46) := by
    apply fixed_of_signature graph e [28] 29
    · intro a present
      have same : a = (28 : Fin 46) := List.mem_singleton.mp present
      simpa only [same] using fixed28
    · unfold SignatureUnique
      decide +kernel
  have mass : graph.atomMass (slotAtom i) = graph.atomMass (slotAtom j) := by
    rw [← entry]
    exact (MoleculeGraph.Aut.atomMass_eq (m := graph) e (slotAtom i)).symm
  have firstFixed : slotAtom i = 28 → slotAtom j = 28 := by
    intro at30
    rw [at30, fixed28] at entry
    exact entry.symm
  have secondFixed : slotAtom i = 29 → slotAtom j = 29 := by
    intro at31
    rw [at31, fixed29] at entry
    exact entry.symm
  have pairCases := remaining_pair (slotAtom i) (slotAtom j)
    (root_neighbors _ (slotAtom_neighbor i)) (root_neighbors _ (slotAtom_neighbor j))
    same mass firstFixed secondFixed
  rcases pairCases with pair | pair
  · have left : i = otherLeftSlot := slotAtom_injective (pair.1.trans other_slot_atoms.1.symm)
    have right : j = otherRightSlot := slotAtom_injective (pair.2.trans other_slot_atoms.2.symm)
    exact False.elim (other_keys_separate side mark hmark (by simpa only [left, right] using tied))
  · have right : i = otherRightSlot := slotAtom_injective (pair.1.trans other_slot_atoms.2.symm)
    have left : j = otherLeftSlot := slotAtom_injective (pair.2.trans other_slot_atoms.1.symm)
    exact False.elim (other_keys_separate side mark hmark (by simpa only [left, right] using tied.symm))

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherKeySeparation

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherKeySeparation.other_keys_separate
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherKeySeparation.other_markedKeys_injective
