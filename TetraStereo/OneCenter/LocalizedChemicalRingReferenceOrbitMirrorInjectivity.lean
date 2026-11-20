import TetraStereo.OneCenter.LocalizedChemicalRingCoveredPathMirrorKeySeparation
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMirrorObservation
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitSecondReferenceSeparation
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitCoveringSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingDefaultMarkerLayout
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16384

/-!
Both O18 marks yield distinct actual root keys in their own reflected snapshots.
The covering observation, physical exchange sign and marker fixation are derived;
no cross-reference or original/reflected-state agreement is asserted.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMirrorInjectivity

open CertifiedLocalizedCIPInput DeclarativeCIP RetainedCoherentSymmetry RetainedRingSymmetryReconstruction
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitCoveringPath LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitCoveringSymmetry
open LocalizedChemicalRingReferenceOrbitSecondReferenceSeparation (secondReference)
open LocalizedChemicalRingReferenceOrbitMirrorObservation
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

def mirrorSnapshot (mark : Fin 46) := snapshotWith LocalizedChemicalRingInheritedFallback.rawStep?
  certified mol (structuralDepth mol (canonicalCenterRoot 0)) (mirror (inputGeometry certified))
  (canonicalCenterRoot 0) mark.val

private def slotAtom (i : Fin 4) : Fin 46 :=
  referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData i

private theorem slotAtom_injective : Function.Injective slotAtom := by
  intro i j same
  apply rootData.ligandOf.injective
  exact physical.ligandAtomAt_injective rootCenter same

private theorem slotAtom_neighbor (i : Fin 4) : graph.Adj 0 (slotAtom i) :=
  physical.ligandAtomAt_adj rootCenter (rootData.ligandOf i)

private theorem fixed30_of_mark (mark : Fin 46)
    (hmark : mark = reference ∨ mark = secondReference) (e : graph.Aut)
    (fixedMark : e.val mark = mark) : e.val (30 : Fin 46) = 30 := by
  rcases hmark with rfl | rfl
  · exact fixedMark
  · apply fixed_of_signature graph e [31] 30
    · intro a present
      have same : a = (31 : Fin 46) := List.mem_singleton.mp present
      simpa only [same] using fixedMark
    · unfold SignatureUnique
      decide +kernel

private theorem exchange_negative (mark : Fin 46)
    (hmark : mark = reference ∨ mark = secondReference) (e : physical.Aut)
    (rootFixed : e.val (0 : Fin 46) = (0 : Fin 46))
    (entry : e.val (28 : Fin 46) = (29 : Fin 46)) (refFixed : e.val mark = mark) :
    physical.centerPerm e current = current ∧ relativeSign physical cfg e current = -1 :=
  reference_exchange_current_negative cfg e rootFixed entry
    (fixed30_of_mark mark hmark ⟨e.val, e.2.1⟩ refFixed)

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

private theorem slot_current (mark : Fin 46) (i : Fin 4) :
    ((frames certified single_bonded (mirrorSnapshot mark) rootData.target rootData.real
      rootUnit rfl).frame.cursorAt i).occurrence.1.node.current? = some (slotAtom i) := by
  have frameEq :
      (frames certified single_bonded (mirrorSnapshot mark) rootData.target rootData.real rootUnit rfl).frame =
        rootData.frame :=
    Option.some.inj ((frames certified single_bonded (mirrorSnapshot mark) rootData.target rootData.real
      rootUnit rfl).frameComputed.symm.trans rootData.frameExec)
  have mapped : (((frames certified single_bonded (mirrorSnapshot mark) rootData.target rootData.real
      rootUnit rfl).frame.cursorAt i).occurrence.1.node.current?).map Fin.val =
        some (slotAtom i).val := by
    change atomAt certified _ i = some (slotAtom i).val
    rw [frameEq]
    exact rootData.atomAt_eq i
  cases found : ((frames certified single_bonded (mirrorSnapshot mark) rootData.target rootData.real
      rootUnit rfl).frame.cursorAt i).occurrence.1.node.current? with
  | none => simp [found] at mapped
  | some a =>
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

/-- Either O18 mark separates the two O16 arms on its actual reflected snapshot. -/
theorem mirror_keys_separate (mark : Fin 46) (hmark : mark = reference ∨ mark = secondReference) :
    markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
        (mirrorSnapshot mark) mark leftSlot ≠
      markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
        (mirrorSnapshot mark) mark rightSlot := by
  apply actual_root_mirror_keys_ne_of_covered_observation certified mol structure_agreement admissible
    supported single_bonded cfg rootData.target rootData.real rootUnit rfl root_address mark
    (structuralDepth mol (canonicalCenterRoot 0)) (canonicalCenterRoot 0)
    (reached_root mol 0 (by decide)) leftSlot rightSlot (28 : Fin 46) (29 : Fin 46)
    coveringPath.tail covering_residual current rfl calibrated covering_query_centers
    ⟨0, constant_charge⟩
  · simpa only [root_root] using exchange_negative mark hmark
  · simpa only [slotAtom, slot_atoms.1] using slot_current mark leftSlot
  · simpa only [slotAtom, slot_atoms.2] using slot_current mark rightSlot
  · rw [covering_query]
    exact covering_mirror_snapshot_label_present_at mark

private theorem root_neighbors (a : Fin 46) :
    graph.Adj 0 a → a = 28 ∨ a = 29 ∨ a = 30 ∨ a = 31 := by
  fin_cases a <;> decide +kernel

private theorem remaining_pair (a b : Fin 46)
    (first : a = 28 ∨ a = 29 ∨ a = 30 ∨ a = 31)
    (second : b = 28 ∨ b = 29 ∨ b = 30 ∨ b = 31)
    (different : a ≠ b) (mass : graph.atomMass a = graph.atomMass b)
    (fix30 : a = 30 → b = 30) (fix31 : a = 31 → b = 31) :
    (a = 28 ∧ b = 29) ∨ (a = 29 ∧ b = 28) := by
  revert different mass fix30 fix31
  rcases first with rfl | rfl | rfl | rfl <;>
    rcases second with rfl | rfl | rfl | rfl <;> decide +kernel

/-- Actual reflected-key injectivity for either of the two O18 reference atoms. -/
theorem mirror_markedKeys_injective (mark : Fin 46)
    (hmark : mark = reference ∨ mark = secondReference) : Function.Injective
    (markedKeys certified mol single_bonded rootCenter (canonicalCenterRoot 0) rootData
      (mirrorSnapshot mark) mark) := by
  intro i j tied
  by_cases same : slotAtom i = slotAtom j
  · exact slotAtom_injective same
  obtain ⟨π, aut, _, entry, referenceFixed⟩ :=
    actual_root_default_tie_reference_fixed_aut certified single_bonded (mirrorSnapshot mark)
      rootData.target rootData.real rootUnit rfl root_address mark i j tied (slotAtom i) (slotAtom j)
      (slot_current mark i) (slot_current mark j) ⟨0, constant_charge⟩
  let e : graph.Aut := ⟨π, aut⟩
  have fixed30 : π (30 : Fin 46) = (30 : Fin 46) := fixed30_of_mark mark hmark e referenceFixed
  have fixed31 : π (31 : Fin 46) = (31 : Fin 46) := by
    apply fixed_of_signature graph e [30] 31
    · intro a present
      have same : a = (30 : Fin 46) := List.mem_singleton.mp present
      simpa only [same] using fixed30
    · unfold SignatureUnique
      decide +kernel
  have mass : graph.atomMass (slotAtom i) = graph.atomMass (slotAtom j) := by
    rw [← entry]
    exact (MoleculeGraph.Aut.atomMass_eq (m := graph) e (slotAtom i)).symm
  have firstFixed : slotAtom i = 30 → slotAtom j = 30 := by
    intro at30
    rw [at30, fixed30] at entry
    exact entry.symm
  have secondFixed : slotAtom i = 31 → slotAtom j = 31 := by
    intro at31
    rw [at31, fixed31] at entry
    exact entry.symm
  have pairCases := remaining_pair (slotAtom i) (slotAtom j)
    (root_neighbors _ (slotAtom_neighbor i)) (root_neighbors _ (slotAtom_neighbor j))
    same mass firstFixed secondFixed
  rcases pairCases with pair | pair
  · have left : i = leftSlot := slotAtom_injective (pair.1.trans slot_atoms.1.symm)
    have right : j = rightSlot := slotAtom_injective (pair.2.trans slot_atoms.2.symm)
    exact False.elim (mirror_keys_separate mark hmark (by simpa only [left, right] using tied))
  · have right : i = rightSlot := slotAtom_injective (pair.1.trans slot_atoms.2.symm)
    have left : j = leftSlot := slotAtom_injective (pair.2.trans slot_atoms.1.symm)
    exact False.elim (mirror_keys_separate mark hmark (by simpa only [left, right] using tied.symm))

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMirrorInjectivity

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMirrorInjectivity.mirror_keys_separate
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitMirrorInjectivity.mirror_markedKeys_injective
