import TetraStereo.OneCenter.CIPRationalTetrahedralParityPermutation
import TetraStereo.OneCenter.LocalizedRetainedDescriptorTransport
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Refusal and injectivity under retained descriptor reflection

`retainedPairCompare_reflect` preserves equality of full Rule 5 keys, so
injectivity is unchanged when the descriptor map is reflected and an arbitrary
slot permutation moves graphs and points together. A strict sorted judgment
exists exactly when those keys are injective and the tetrahedron has nonzero
volume. Reordering and `applySpace` multiply that volume by `±1`, so zero
stays zero and refusal transports before the reflected sort sign is known.

The descending permutation's sign is not assumed. Letter covariance for counts
0, 1, and 2 stays with the live four-slot parity owner. Same graph arguments
are not a molecular relabel.
-/

namespace TetraStereo.OneCenter.LocalizedRetainedCompleteMirrorCovariance

open DeclarativeCIP
open CertifiedLocalizedCIPInput
open RationalTetrahedralPermutation
open Rule6HandednessSemantics
open RawMolecule
open LocalizedRetainedDescriptorTransport
open scoped Classical

noncomputable section
universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

local instance mirrorNodeFintype (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

variable (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule)

private theorem pointVector_points (points : Fin 4 → CartesianPoint3) (i : Fin 4) :
    pointVector (points 0) (points 1) (points 2) (points 3) i = points i := by
  fin_cases i <;> rfl

private theorem orientedVolume_slotPerm_eq_zero_iff
    (points : Fin 4 → CartesianPoint3) (slotPerm : Equiv.Perm (Fin 4)) :
    CartesianPoint3.orientedVolume (points (slotPerm 0)) (points (slotPerm 1))
        (points (slotPerm 2)) (points (slotPerm 3)) = 0 ↔
      CartesianPoint3.orientedVolume (points 0) (points 1) (points 2) (points 3) = 0 := by
  have h := permutedOrientedVolume_eq_if_permutationIsEven
    (points 0) (points 1) (points 2) (points 3) slotPerm
  have hvol :
      permutedOrientedVolume (points 0) (points 1) (points 2) (points 3) slotPerm =
        CartesianPoint3.orientedVolume (points (slotPerm 0)) (points (slotPerm 1))
          (points (slotPerm 2)) (points (slotPerm 3)) := by
    simp only [permutedOrientedVolume, pointVector_points]
  rw [← hvol, h]
  by_cases even : permutationIsEven (finFourPermutationList slotPerm) = true
  · simp [even]
  · simp [even, neg_eq_zero]

theorem orientedVolume_reindex_applySpace_eq_zero_iff
    (spaceMirror : Bool) (points : Fin 4 → CartesianPoint3) (slotPerm : Equiv.Perm (Fin 4)) :
    CartesianPoint3.orientedVolume
        (applySpace spaceMirror (points (slotPerm 0)))
        (applySpace spaceMirror (points (slotPerm 1)))
        (applySpace spaceMirror (points (slotPerm 2)))
        (applySpace spaceMirror (points (slotPerm 3))) = 0 ↔
      CartesianPoint3.orientedVolume (points 0) (points 1) (points 2) (points 3) = 0 := by
  cases spaceMirror with
  | false =>
      simp only [applySpace, Bool.false_eq_true, ite_false]
      exact orientedVolume_slotPerm_eq_zero_iff points slotPerm
  | true =>
      have hneg := orientedVolume_reflectZ (points (slotPerm 0)) (points (slotPerm 1))
        (points (slotPerm 2)) (points (slotPerm 3))
      simp only [applySpace, ite_true]
      rw [hneg, neg_eq_zero]
      exact orientedVolume_slotPerm_eq_zero_iff points slotPerm

theorem retainedCompleteLigandRule5KeyAt_reflect_eq_iff
    (left right : RootedDigraph Atom) (W D : ℕ) :
    retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit left W D =
        retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit right W D ↔
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D =
        retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D := by
  rw [← completeLigandRule5Key_compare_eq_iff, ← completeLigandRule5Key_compare_eq_iff]
  rw [retainedPairCompare_reflect molecule descriptorMap unit left right W D]
  by_cases htied :
      retainedCompleteLigandPriorKeyAt molecule descriptorMap unit left W D =
        retainedCompleteLigandPriorKeyAt molecule descriptorMap unit right W D
  · rw [if_pos htied]
    cases hcmp : compare
        (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit left W D)
        (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit right W D) with
    | lt => decide
    | eq => decide
    | gt => decide
  · rw [if_neg htied]

theorem retainedRule5Keys_reindex_reflect_injective_iff
    (graphs : Fin 4 → RootedDigraph Atom) (slotPerm : Equiv.Perm (Fin 4)) (W D : ℕ) :
    Function.Injective (fun slot =>
        retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit
          (graphs (slotPerm⁻¹ slot)) W D) ↔
      Function.Injective (fun slot =>
        retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D) := by
  constructor
  · intro hinj a b hab
    have himage :=
      (retainedCompleteLigandRule5KeyAt_reflect_eq_iff molecule descriptorMap unit
        (graphs a) (graphs b) W D).2 hab
    have hslots : slotPerm a = slotPerm b :=
      hinj (by simpa [Equiv.symm_apply_apply] using himage)
    exact slotPerm.injective hslots
  · intro hinj a b hab
    have hsource :=
      (retainedCompleteLigandRule5KeyAt_reflect_eq_iff molecule descriptorMap unit
        (graphs (slotPerm⁻¹ a)) (graphs (slotPerm⁻¹ b)) W D).1 hab
    exact slotPerm.symm.injective (hinj hsource)

private theorem exists_strict_descending
    (keys : Fin 4 → CompleteLigandRule5Key) (inj : Function.Injective keys) :
    ∃ order : List (Fin 4),
      order.Perm (List.finRange 4) ∧
        order.Pairwise (fun left right => keys right < keys left) := by
  obtain ⟨a, ha, hmaxa⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin 4)) keys Finset.univ_nonempty
  let s1 := (Finset.univ : Finset (Fin 4)).erase a
  have hcard1 : s1.card = 3 := by
    rw [Finset.card_erase_of_mem ha, Finset.card_univ, Fintype.card_fin]
  have hs1 : s1.Nonempty := Finset.card_pos.mp (hcard1 ▸ (by decide : 0 < 3))
  obtain ⟨b, hb, hmaxb⟩ := Finset.exists_max_image s1 keys hs1
  let s2 := s1.erase b
  have hcard2 : s2.card = 2 := by
    rw [Finset.card_erase_of_mem hb, hcard1]
  have hs2 : s2.Nonempty := Finset.card_pos.mp (hcard2 ▸ (by decide : 0 < 2))
  obtain ⟨c, hc, hmaxc⟩ := Finset.exists_max_image s2 keys hs2
  let s3 := s2.erase c
  have hcard3 : s3.card = 1 := by
    rw [Finset.card_erase_of_mem hc, hcard2]
  have hs3 : s3.Nonempty := Finset.card_pos.mp (hcard3 ▸ (by decide : 0 < 1))
  obtain ⟨d, hd, _⟩ := Finset.exists_max_image s3 keys hs3
  have hba : b ≠ a := (Finset.mem_erase.mp hb).1
  have hc1 : c ∈ s1 := (Finset.mem_erase.mp hc).2
  have hca : c ≠ a := (Finset.mem_erase.mp hc1).1
  have hcb : c ≠ b := (Finset.mem_erase.mp hc).1
  have hd2 : d ∈ s2 := (Finset.mem_erase.mp hd).2
  have hd1 : d ∈ s1 := (Finset.mem_erase.mp hd2).2
  have hda : d ≠ a := (Finset.mem_erase.mp hd1).1
  have hdb : d ≠ b := (Finset.mem_erase.mp hd2).1
  have hdc : d ≠ c := (Finset.mem_erase.mp hd).1
  have strict : ∀ {i j : Fin 4}, keys i ≤ keys j → i ≠ j → keys i < keys j := by
    intro i j hle hne
    exact lt_of_le_of_ne hle (fun heq => hne (inj heq))
  have hab : keys b < keys a := strict (hmaxa b (Finset.mem_univ b)) hba
  have hac : keys c < keys a := strict (hmaxa c (Finset.mem_univ c)) hca
  have had : keys d < keys a := strict (hmaxa d (Finset.mem_univ d)) hda
  have hbc : keys c < keys b := strict (hmaxb c hc1) hcb
  have hbd : keys d < keys b := strict (hmaxb d hd1) hdb
  have hcd : keys d < keys c := strict (hmaxc d hd2) hdc
  let order : List (Fin 4) := [a, b, c, d]
  have hnodup : order.Nodup := by
    simp [order, List.nodup_cons, Ne.symm hba, Ne.symm hca, Ne.symm hda, Ne.symm hcb,
      Ne.symm hdb, Ne.symm hdc]
  have hlen : order.length = 4 := by simp [order]
  let f : Fin 4 → Fin 4 := fun i => order.get (Fin.cast hlen.symm i)
  have hinj : Function.Injective f := by
    intro i j hij
    have hidx := (List.Nodup.get_inj_iff hnodup).mp hij
    exact Fin.ext (congrArg Fin.val hidx)
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  have horder : order = (List.finRange 4).map (⇑σ) := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hi'
      have hi4 : i < 4 := by simpa [hlen] using hi
      have hget : order[i] = σ ⟨i, hi4⟩ := by
        have : f ⟨i, hi4⟩ = order[i]'(by simpa [hlen] using hi4) := rfl
        simpa [σ, Equiv.ofBijective_apply] using this.symm
      rw [List.getElem_map, List.getElem_finRange, hget]
      exact congrArg (⇑σ) (Fin.ext rfl)
  have hperm : order.Perm (List.finRange 4) := by
    rw [horder]
    exact σ.map_finRange_perm
  have hpair : order.Pairwise (fun left right => keys right < keys left) := by
    refine List.Pairwise.cons (fun y hy => ?_) ?_
    · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
      rcases hy with rfl | rfl | rfl
      · exact hab
      · exact hac
      · exact had
    · refine List.Pairwise.cons (fun y hy => ?_) ?_
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
        rcases hy with rfl | rfl
        · exact hbc
        · exact hbd
      · refine List.Pairwise.cons (fun y hy => ?_) ?_
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hy
          subst hy
          exact hcd
        · exact List.Pairwise.cons (fun _ hy => nomatch hy) List.Pairwise.nil
  exact ⟨order, hperm, hpair⟩

private theorem map_points_eq_perm (points : Fin 4 → CartesianPoint3)
    {order : List (Fin 4)} (hperm : order.Perm (List.finRange 4)) :
    ∃ σ : Equiv.Perm (Fin 4),
      order.map points = [points (σ 0), points (σ 1), points (σ 2), points (σ 3)] := by
  have hlen : order.length = 4 := by simpa using hperm.length_eq
  have hnodup : order.Nodup := hperm.nodup_iff.mpr (List.nodup_finRange _)
  let f : Fin 4 → Fin 4 := fun i => order[i.1]'(by simpa [hlen] using i.isLt)
  have hinj : Function.Injective f := by
    intro i j hij
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnodup).mp hij)
  let σ : Equiv.Perm (Fin 4) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj)
  refine ⟨σ, ?_⟩
  apply List.ext_getElem
  · simp [hlen]
  · intro i hi hi'
    have hi4 : i < 4 := by simpa [hlen] using hi
    have hslot : order[i]'(by simpa [hlen] using hi) = σ ⟨i, hi4⟩ := by
      have : f ⟨i, hi4⟩ = order[i]'(by simpa [hlen] using hi4) := rfl
      simpa [σ, Equiv.ofBijective_apply] using this.symm
    match i with
    | 0 => simp [List.getElem_map, hslot]
    | 1 => simp [List.getElem_map, hslot]
    | 2 => simp [List.getElem_map, hslot]
    | 3 => simp [List.getElem_map, hslot]
    | n + 4 => omega

theorem completeRootDescriptorJudgment_exists_iff
    (keys : Fin 4 → CompleteLigandRule5Key) (points : Fin 4 → CartesianPoint3) :
    (∃ descriptor, CompleteRootDescriptorJudgment keys points descriptor) ↔
      Function.Injective keys ∧
        CartesianPoint3.orientedVolume (points 0) (points 1) (points 2) (points 3) ≠ 0 := by
  constructor
  · intro ⟨descriptor, judgment⟩
    refine ⟨completeRootDescriptorJudgment_injective judgment, ?_⟩
    obtain ⟨order, raw, hperm, _, hgeom, _⟩ := judgment
    obtain ⟨a, b, c, d, hlist, hsign⟩ := hgeom
    obtain ⟨σ, hmap⟩ := map_points_eq_perm points hperm
    have hfour := hlist.symm.trans hmap
    injection hfour with ha hrest
    injection hrest with hb hrest
    injection hrest with hc hrest
    injection hrest with hd _
    subst ha hb hc hd
    have hne : CartesianPoint3.orientedVolume (points (σ 0)) (points (σ 1))
        (points (σ 2)) (points (σ 3)) ≠ 0 := by
      cases raw with
      | R => exact ne_of_lt hsign
      | S => exact ne_of_gt hsign
    exact (orientedVolume_slotPerm_eq_zero_iff points σ).not.mp hne
  · intro ⟨hinj, hvol⟩
    obtain ⟨order, hperm, hsorted⟩ := exists_strict_descending keys hinj
    obtain ⟨σ, hmap⟩ := map_points_eq_perm points hperm
    have hpermVol :
        CartesianPoint3.orientedVolume (points (σ 0)) (points (σ 1))
          (points (σ 2)) (points (σ 3)) ≠ 0 :=
      (orientedVolume_slotPerm_eq_zero_iff points σ).not.mpr hvol
    rcases lt_trichotomy
        (CartesianPoint3.orientedVolume (points (σ 0)) (points (σ 1))
          (points (σ 2)) (points (σ 3))) 0 with
      hlt | heq | hgt
    · exact ⟨classifyTetrahedralRSPseudo RS.R (completeRule5PairCount keys), order, RS.R,
        hperm, hsorted,
        ⟨points (σ 0), points (σ 1), points (σ 2), points (σ 3), hmap, hlt⟩, rfl⟩
    · exact absurd heq hpermVol
    · exact ⟨classifyTetrahedralRSPseudo RS.S (completeRule5PairCount keys), order, RS.S,
        hperm, hsorted,
        ⟨points (σ 0), points (σ 1), points (σ 2), points (σ 3), hmap, hgt⟩, rfl⟩

theorem completeRootJudgment_exists_mapReflect_space_iff
    (graphs : Fin 4 → RootedDigraph Atom) (points : Fin 4 → CartesianPoint3)
    (slotPerm : Equiv.Perm (Fin 4)) (spaceMirror : Bool) (W D : ℕ) :
    (∃ descriptor, CompleteRootDescriptorJudgment
        (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit
          (graphs (slotPerm⁻¹ slot)) W D)
        (fun slot => applySpace spaceMirror (points (slotPerm⁻¹ slot))) descriptor) ↔
      (∃ descriptor, CompleteRootDescriptorJudgment
        (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit
          (graphs slot) W D)
        points descriptor) := by
  rw [completeRootDescriptorJudgment_exists_iff, completeRootDescriptorJudgment_exists_iff]
  constructor
  · intro ⟨hinj, hvol⟩
    refine ⟨(retainedRule5Keys_reindex_reflect_injective_iff molecule descriptorMap unit
      graphs slotPerm W D).1 hinj, ?_⟩
    exact (orientedVolume_reindex_applySpace_eq_zero_iff spaceMirror points slotPerm⁻¹).not.mp hvol
  · intro ⟨hinj, hvol⟩
    refine ⟨(retainedRule5Keys_reindex_reflect_injective_iff molecule descriptorMap unit
      graphs slotPerm W D).2 hinj, ?_⟩
    exact (orientedVolume_reindex_applySpace_eq_zero_iff spaceMirror points slotPerm⁻¹).not.mpr hvol

theorem completeRootOutcome_none_mapReflect_space_iff
    (graphs : Fin 4 → RootedDigraph Atom) (points : Fin 4 → CartesianPoint3)
    (slotPerm : Equiv.Perm (Fin 4)) (spaceMirror : Bool) (W D : ℕ) :
    CompleteRootOutcome
        (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit
          (graphs (slotPerm⁻¹ slot)) W D)
        (fun slot => applySpace spaceMirror (points (slotPerm⁻¹ slot))) none ↔
      CompleteRootOutcome
        (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap unit
          (graphs slot) W D)
        points none := by
  simpa [CompleteRootOutcome] using not_iff_not.mpr
    (completeRootJudgment_exists_mapReflect_space_iff molecule descriptorMap unit
      graphs points slotPerm spaceMirror W D)

end

end TetraStereo.OneCenter.LocalizedRetainedCompleteMirrorCovariance

assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCompleteMirrorCovariance.orientedVolume_reindex_applySpace_eq_zero_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCompleteMirrorCovariance.retainedCompleteLigandRule5KeyAt_reflect_eq_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCompleteMirrorCovariance.retainedRule5Keys_reindex_reflect_injective_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCompleteMirrorCovariance.completeRootDescriptorJudgment_exists_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCompleteMirrorCovariance.completeRootJudgment_exists_mapReflect_space_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedCompleteMirrorCovariance.completeRootOutcome_none_mapReflect_space_iff
