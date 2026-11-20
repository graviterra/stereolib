import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootPhysicalDistinguishability
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitOtherArmSymmetry
import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootCalibration
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

/-!
The accepted 46-atom configuration has no physically enantiomorphic root branches.
The existing three-candidate classification, normalized by the two accepted arm swaps,
shows that every root-fixing graph automorphism is proper at center 3. This uses the
actual opposite coordinate signs at centers 3 and 4, not auxiliary labels. Center 3
is reachable in every root branch, so no branch transport can be a mirror transport.
The result is transferred to the actual detected frames and their accepted configuration.
No evaluator output or reference consensus is asserted.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootMirrorCriterion

open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitCalibration
open LocalizedChemicalRingReferenceOrbitAllCalibration LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingReferenceOrbitArmSymmetry LocalizedChemicalRingReferenceOrbitOtherArmSymmetry
open LocalizedChemicalRingReferenceOrbitCoveringSymmetry LocalizedChemicalRingReferenceOrbitRootCalibration
open LocalizedActualPhysicalBranchDecision RootedTetrahedralBranchSymmetry
open RetainedCoherentSymmetry LocalizedCyclicMatchedReadingPhysicalTransport
open LocalizedPhysicalMarkedParityCompleteness

private theorem isotope16 (a : Fin 46) :
    graph.atomMass a = graph.atomMass (28 : Fin 46) → a = 28 ∨ a = 29 := by
  fin_cases a <;> decide +kernel

private theorem isotope18 (a : Fin 46) :
    graph.atomMass a = graph.atomMass (30 : Fin 46) → a = 30 ∨ a = 31 := by
  fin_cases a <;> decide +kernel

private theorem marked_forms (e : graph.Aut) (root : e.val (0 : Fin 46) = 0)
    (mark : e.val reference = reference) :
    ∃ (k : Fin 3) (a : Bool), e.val = candidate k * (if a then armSwap else 1) := by
  rcases isotope16 (e.val 28) (MoleculeGraph.Aut.atomMass_eq (m := graph) e 28) with
    fixed28 | moved28
  · have fixed29 : e.val (29 : Fin 46) = 29 := by
      rcases isotope16 (e.val 29) (MoleculeGraph.Aut.atomMass_eq (m := graph) e 29) with
        moved29 | fixed29
      · exact False.elim ((by decide : (28 : Fin 46) ≠ 29)
          (e.val.injective (fixed28.trans moved29.symm)))
      · exact fixed29
    obtain ⟨k, same⟩ := reference_exchange_classification (e * graphAut) root fixed29 mark
    refine ⟨k, true, ?_⟩
    change e.val * armSwap = candidate k at same
    calc
      e.val = (e.val * armSwap) * armSwap := by rw [mul_assoc, armSwap_square, mul_one]
      _ = candidate k * armSwap := congrArg (fun p => p * armSwap) same
  · obtain ⟨k, same⟩ := reference_exchange_classification e root moved28 mark
    exact ⟨k, false, by simpa only [Bool.false_eq_true, ↓reduceIte, mul_one] using same⟩

/-- Every root-fixing automorphism is one of twelve forms obtained from the already
classified three candidates and the two already certified arm swaps. -/
theorem root_aut_normal_form (e : graph.Aut) (root : e.val (0 : Fin 46) = 0) :
    ∃ (k : Fin 3) (a r : Bool),
      e.val = candidate k * (if a then armSwap else 1) * (if r then otherArmSwap else 1) := by
  rcases isotope18 (e.val 30) (MoleculeGraph.Aut.atomMass_eq (m := graph) e 30) with
    fixed30 | moved30
  · obtain ⟨k, a, same⟩ := marked_forms e root fixed30
    exact ⟨k, a, false, by simpa only [Bool.false_eq_true, ↓reduceIte, mul_one] using same⟩
  · have moved31 : e.val (31 : Fin 46) = 30 := by
      rcases isotope18 (e.val 31) (MoleculeGraph.Aut.atomMass_eq (m := graph) e 31) with
        moved31 | fixed31
      · exact moved31
      · exact False.elim ((by decide : (30 : Fin 46) ≠ 31)
          (e.val.injective (moved30.trans fixed31.symm)))
    obtain ⟨k, a, same⟩ := marked_forms (e * otherGraphAut) root moved31
    refine ⟨k, a, true, ?_⟩
    change e.val * otherArmSwap = candidate k * (if a then armSwap else 1) at same
    calc
      e.val = (e.val * otherArmSwap) * otherArmSwap := by
        rw [mul_assoc, otherArmSwap_square, mul_one]
      _ = (candidate k * (if a then armSwap else 1)) * otherArmSwap :=
        congrArg (fun p => p * otherArmSwap) same

private def center3 : canon.Center := ⟨(3 : Fin 46), by
  change (3 : Fin 46) ∈ graph.tetrahedralCenterSet
  rw [detected_inventory]
  decide⟩

private def center4 : canon.Center := ⟨(4 : Fin 46), by
  change (4 : Fin 46) ∈ graph.tetrahedralCenterSet
  rw [detected_inventory]
  decide⟩

private def imageCenter (a r : Bool) : canon.Center := if a = r then center4 else center3

private def baseSlots (k : Fin 3) : Equiv.Perm (Fin 4) :=
  if k = 0 then Equiv.swap 1 2 else if k = 1 then Equiv.swap 0 1 else Equiv.swap 0 2

private def normalSlots (k : Fin 3) (a r : Bool) : Equiv.Perm (Fin 4) :=
  baseSlots k * (if a then Equiv.swap 1 2 else 1) * (if r then Equiv.swap 1 2 else 1)

private theorem normal_frame (k : Fin 3) (a r : Bool) (i : Fin 4) :
    (candidate k * (if a then armSwap else 1) * (if r then otherArmSwap else 1))
      (neighborsAt center3.1 i) =
      neighborsAt (imageCenter a r).1 (normalSlots k a r i) := by
  fin_cases k <;> cases a <;> cases r <;> fin_cases i <;> decide +kernel

private theorem coordinate_signs :
    canon.configurationSign (coordinateCfg certified) center3 = 1 ∧
      canon.configurationSign (coordinateCfg certified) center4 = -1 := by
  have volume3 : coordinateVolume? certified center3 = some 1 := by
    simp only [coordinateVolume?, all_observed]
    decide +kernel
  have volume4 : coordinateVolume? certified center4 = some (-1) := by
    simp only [coordinateVolume?, all_observed]
    decide +kernel
  constructor
  · norm_num [MultiCenterMolecule.configurationSign, coordinateCfg, volume3, permHandedness]
  · simp [MultiCenterMolecule.configurationSign, coordinateCfg, volume4, permHandedness]

/-- Actual canonical-coordinate orientation at center 3 is preserved by every root-fixing
graph symmetry, including those exchanging center 3 with center 4. -/
theorem canonical_anchor_proper (e : canon.Aut) (root : e.val (0 : Fin 46) = (0 : Fin 46)) :
    canon.configurationSign (coordinateCfg certified) center3 *
        permHandedness (canon.ligandPermAt e center3) =
      canon.configurationSign (coordinateCfg certified) (canon.centerPerm e center3) := by
  obtain ⟨k, a, r, same⟩ := root_aut_normal_form ⟨e.val, e.2.1⟩ root
  have image : canon.centerPerm e center3 = imageCenter a r := by
    apply Subtype.ext
    change e.val (3 : Fin 46) = (imageCenter a r).1
    rw [same]
    fin_cases k <;> cases a <;> cases r <;> rfl
  have slots : canon.ligandPermAt e center3 = normalSlots k a r := by
    apply Equiv.ext
    intro i
    apply canon.ligandAtomAt_injective (canon.centerPerm e center3)
    rw [canon.ligandAtomAt_ligandPermAt, image, canonical_neighbors, canonical_neighbors, same]
    exact normal_frame k a r i
  rw [slots, image, coordinate_signs.1]
  fin_cases k <;> cases a <;> cases r <;>
    simp [imageCenter, normalSlots, baseSlots, coordinate_signs.1, coordinate_signs.2,
      permHandedness]

private abbrev deleted := residualGraph graph [(0 : Fin 46)]

private theorem neighbor_reaches3 (a : Fin 46) (neighbor : graph.Adj 0 a) :
    deleted.Reachable a 3 := by
  have from32 : deleted.Reachable 32 3 :=
    (show deleted.Adj 32 36 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans
      ((show deleted.Adj 36 42 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans
        ((show deleted.Adj 42 40 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans
          (show deleted.Adj 40 3 from ⟨by decide, by decide, by decide +kernel⟩).reachable))
  have from27 : deleted.Reachable 27 3 :=
    (show deleted.Adj 27 32 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans from32
  have choices : a = 28 ∨ a = 29 ∨ a = 30 ∨ a = 31 := by
    revert neighbor
    fin_cases a <;> decide +kernel
  rcases choices with rfl | rfl | rfl | rfl
  · exact (show deleted.Adj 28 32 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans from32
  · exact (show deleted.Adj 29 33 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans
      ((show deleted.Adj 33 27 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans from27)
  · exact (show deleted.Adj 30 34 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans
      ((show deleted.Adj 34 26 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans
        ((show deleted.Adj 26 27 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans from27))
  · exact (show deleted.Adj 31 35 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans
      ((show deleted.Adj 35 26 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans
        ((show deleted.Adj 26 27 from ⟨by decide, by decide, by decide +kernel⟩).reachable.trans from27))

private theorem canonical_no_mirror (i j : Fin 4) :
    ¬ MirrorTransport canon (coordinateCfg certified) canonicalRoot i j := by
  rintro ⟨e, root, _, signs⟩
  have reaches : LigandBranchReaches canon canonicalRoot i center3.1 := by
    apply inComponent_implies_ligandBranchReaches
    refine ⟨?_, neighbor_reaches3 _ (canon.ligandAtomAt_adj canonicalRoot i)⟩
    simpa only [List.mem_singleton] using ligandAtomAt_ne_center canon canonicalRoot i
  have negative := signs center3 reaches
  have proper := canonical_anchor_proper e (congrArg Subtype.val root)
  have square := permHandedness_mul_self ((coordinateCfg certified) (canon.centerPerm e center3))
  change _ * _ = (-1 : ℝ) * _ at negative
  rw [proper] at negative
  change canon.configurationSign (coordinateCfg certified) (canon.centerPerm e center3) *
    canon.configurationSign (coordinateCfg certified) (canon.centerPerm e center3) = 1 at square
  nlinarith

noncomputable section

private theorem root_transfer :
    Eq.mp (congrArg MultiCenterMolecule.Center frameChange_spec) canonicalRoot = rootCenter := by
  have center_val {m n : MultiCenterMolecule (Fin 46)} (h : m = n) (c : m.Center) :
      (Eq.mp (congrArg MultiCenterMolecule.Center h) c).1 = c.1 := by cases h; rfl
  exact Subtype.ext (center_val frameChange_spec canonicalRoot)

/-- No two actual detected root ligands admit a physical mirror transport. -/
theorem root_not_mirror (i j : Fin 4) : ¬ MirrorTransport physical cfg rootCenter i j := by
  have transfer {m n : MultiCenterMolecule (Fin 46)} (h : m = n)
      (configuration : m.Configuration) (c : m.Center) :
      MirrorTransport n (Eq.mp (congrArg MultiCenterMolecule.Configuration h) configuration)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) c) i j ↔
        MirrorTransport m configuration c i j := by cases h; rfl
  have canonical := canonical_no_mirror (frameChange canonicalRoot i) (frameChange canonicalRoot j)
  have reindexed : ¬ MirrorTransport (canon.reindexFrames frameChange)
      (canon.reindexConfiguration frameChange (coordinateCfg certified)) canonicalRoot i j := by
    intro h
    exact canonical ((MultiCenterMolecule.mirrorTransport_reindexFrames_iff
      canon frameChange (coordinateCfg certified) canonicalRoot i j).mp h)
  intro h
  apply reindexed
  apply (transfer frameChange_spec (canon.reindexConfiguration frameChange (coordinateCfg certified))
    canonicalRoot).mp
  simpa only [cfg, root_transfer] using h

/-- Independent physical enantiomorphy is absent, irrespective of evaluator behavior. -/
theorem root_not_enantiomorphic (i j : Fin 4) : ¬ Enantiomorphic physical cfg rootCenter i j :=
  fun h => root_not_mirror i j h.2.1

/-- The accepted coordinates give zero physical enantiomorphic root pairs. -/
theorem root_pair_count_zero : physicalEnantiomorphicPairCount physical cfg rootCenter = 0 := by
  simp [physicalEnantiomorphicPairCount, sourceEnantiomorphicPairCount, root_not_enantiomorphic]

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootMirrorCriterion

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootMirrorCriterion.root_aut_normal_form
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootMirrorCriterion.canonical_anchor_proper
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootMirrorCriterion.root_not_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootMirrorCriterion.root_not_enantiomorphic
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootMirrorCriterion.root_pair_count_zero
