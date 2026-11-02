import Mathlib.Tactic.IntervalCases
import TetraStereo.OneCenter.LocalizedFourSlotReflectionParity
import TetraStereo.OneCenter.LocalizedRetainedCompleteMirrorCovariance
import TetraStereo.OneCenter.LocalizedRetainedPhysicalConfigurationTransport
import TetraStereo.OneCenter.LocalizedRetainedRule5ClassBound
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 4096
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

/-!
# Retained descriptor correctness under proper and physical mirror transport

The four-slot reflection package is instantiated from retained keys: injectivity
from a strict judgment and the accepted reflected-injectivity theorem, prior
classes from the Boolean color bound, and tie reversal from
`retainedPairCompare_reflect`. The sort sign is the approved parity theorem.

Proper transport keeps the letter. Physical mirror transport reflects the
descriptor map and multiplies the rational volume sign by `physicalMirrorFactor`.
Uppercase `R/S` swaps, lowercase `r/s` stays fixed, and `none` stays `none`,
for pair counts 0, 1, and 2. An arbitrary slot permutation moves keys and the
volume sign together. The points are any tuples with that sign; coordinatewise
`z`-reflection is a corollary. The same arm graphs are not a cut relabel and
are not a generated state.
-/

namespace TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness

open DeclarativeCIP
open CertifiedLocalizedCIPInput
open LocalizedRetainedDescriptorTransport
open LocalizedRetainedRule5ClassBound
open LocalizedRetainedCompleteMirrorCovariance
open LocalizedFourSlotReflectionParity
open Certificate.CanonicalSphereKey (Key)
open scoped Classical

noncomputable section
universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

local instance mirrorDescriptorNodeFintype (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

variable (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule)

def retainedPhysicalLetter (mirror : Bool) :
    LocalizedAuxiliaryLabel → LocalizedAuxiliaryLabel :=
  if mirror then reflectUppercaseAuxiliaryLabel else id

theorem retainedPhysicalLetter_involutive (mirror : Bool) (descriptor : LocalizedAuxiliaryLabel) :
    retainedPhysicalLetter mirror (retainedPhysicalLetter mirror descriptor) = descriptor := by
  cases mirror with
  | false => simp [retainedPhysicalLetter]
  | true =>
      cases descriptor with
      | chiral raw => cases raw <;> simp [retainedPhysicalLetter, reflectUppercaseAuxiliaryLabel, RS.swap]
      | pseudoasymmetric raw =>
          cases raw <;> simp [retainedPhysicalLetter, reflectUppercaseAuxiliaryLabel]

def slotVolume (points : Fin 4 → CartesianPoint3) : ℚ :=
  CartesianPoint3.orientedVolume (points 0) (points 1) (points 2) (points 3)

def retainedSourceKey (graphs : Fin 4 → RootedDigraph Atom) (W D : ℕ) (slot : Fin 4) :=
  retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D

def retainedImageKey (mirror : Bool) (graphs : Fin 4 → RootedDigraph Atom)
    (slotPerm : Equiv.Perm (Fin 4)) (W D : ℕ) (slot : Fin 4) :=
  retainedCompleteLigandRule5KeyAt molecule
    (if mirror then descriptorMap.reflect else descriptorMap) unit
    (graphs (slotPerm⁻¹ slot)) W D

private theorem ofFn_fin4 {α : Type*} (f : Fin 4 → α) :
    List.ofFn f = [f 0, f 1, f 2, f 3] := by
  refine List.ext_get (by simp) ?_
  intro n h1 _h2
  have hn : n < 4 := by simpa using h1
  interval_cases n <;> simp

private theorem sortedVolume_sign (points : Fin 4 → CartesianPoint3) (σ : Equiv.Perm (Fin 4)) :
    rationalVolumeSign (CartesianPoint3.orientedVolume (points (σ 0)) (points (σ 1))
        (points (σ 2)) (points (σ 3))) =
      rationalVolumeSign (slotVolume points) * permHandedness σ := by
  have hcal := orientedVolume_calibrated_eq (fun index => points (σ index)) points σ fun _ => rfl
  rw [hcal, rationalVolumeSign_permutedOrientedVolume]
  rfl

private theorem completeRule5PairCount_reindex (keys : Fin 4 → CompleteLigandRule5Key)
    (σ : Equiv.Perm (Fin 4)) :
    completeRule5PairCount (fun slot => keys (σ slot)) = completeRule5PairCount keys := by
  classical
  have hiff : ∀ i j,
      CompletePriorPair (fun slot => keys (σ slot)) i j ↔ CompletePriorPair keys (σ i) (σ j) := by
    intro i j
    constructor
    · intro h
      exact ⟨σ.injective.ne h.1, h.2⟩
    · intro h
      exact ⟨fun hij => h.1 (congrArg σ hij), h.2⟩
  have hsym : ∀ first second, CompletePriorPair keys first second →
      CompletePriorPair keys second first := fun _ _ h => ⟨h.1.symm, h.2.symm⟩
  have hperm := sourceEnantiomorphicPairCount_perm (CompletePriorPair keys) hsym σ
  have hcong := sourceEnantiomorphicPairCount_congr_of_forall
    (CompletePriorPair (fun slot => keys (σ slot)))
    (fun i j => CompletePriorPair keys (σ i) (σ j)) hiff
  simpa [completeRule5PairCount] using hcong.trans hperm

private theorem mirrorFactor_ne_zero (mirror : Bool) (slotPerm : Equiv.Perm (Fin 4)) :
    physicalMirrorFactor mirror * permHandedness slotPerm ≠ 0 := by
  cases mirror <;> rcases permHandedness_eq_one_or_eq_neg_one slotPerm with h | h <;>
    simp [physicalMirrorFactor, h]

private theorem slotVolume_ne_zero_iff (mirror : Bool) (slotPerm : Equiv.Perm (Fin 4))
    (sourcePoints imagePoints : Fin 4 → CartesianPoint3)
    (hsign : rationalVolumeSign (slotVolume imagePoints) =
      physicalMirrorFactor mirror * permHandedness slotPerm *
        rationalVolumeSign (slotVolume sourcePoints)) :
    slotVolume imagePoints ≠ 0 ↔ slotVolume sourcePoints ≠ 0 := by
  have hfactor := mirrorFactor_ne_zero mirror slotPerm
  constructor
  · intro himageNe hsourceZero
    apply himageNe
    apply (rationalVolumeSign_eq_zero_iff (slotVolume imagePoints)).1
    rw [hsign, (rationalVolumeSign_eq_zero_iff (slotVolume sourcePoints)).2 hsourceZero]
    ring
  · intro hsourceNe himageZero
    apply hsourceNe
    apply (rationalVolumeSign_eq_zero_iff (slotVolume sourcePoints)).1
    have hmul : physicalMirrorFactor mirror * permHandedness slotPerm *
        rationalVolumeSign (slotVolume sourcePoints) = 0 := by
      rw [← hsign, (rationalVolumeSign_eq_zero_iff (slotVolume imagePoints)).2 himageZero]
    rw [mul_eq_zero] at hmul
    rcases hmul with hfactorZero | hsignZero
    · exact absurd hfactorZero hfactor
    · exact hsignZero

private theorem imageKey_injective_iff (mirror : Bool) (graphs : Fin 4 → RootedDigraph Atom)
    (slotPerm : Equiv.Perm (Fin 4)) (W D : ℕ) :
    Function.Injective (retainedImageKey molecule descriptorMap unit mirror graphs slotPerm W D) ↔
      Function.Injective (retainedSourceKey molecule descriptorMap unit graphs W D) := by
  cases mirror with
  | true =>
      simpa [retainedImageKey, retainedSourceKey, Equiv.refl_symm] using
        retainedRule5Keys_reindex_reflect_injective_iff molecule descriptorMap unit graphs
          slotPerm W D
  | false =>
      constructor
      · intro hinj a b hab
        have hslots : slotPerm a = slotPerm b := hinj (by
          simpa [retainedImageKey, Equiv.symm_apply_apply] using hab)
        exact slotPerm.injective hslots
      · intro hinj a b hab
        exact slotPerm.symm.injective (hinj (by
          simpa [retainedImageKey, retainedSourceKey] using hab))

private theorem sourceSlotKey_eq (graphs : Fin 4 → RootedDigraph Atom) (W D : ℕ) (slot : Fin 4) :
    slotKey (fun s => (ofLex (retainedSourceKey molecule descriptorMap unit graphs W D s)).1)
        (fun s => (ofLex (retainedSourceKey molecule descriptorMap unit graphs W D s)).2) slot =
      retainedSourceKey molecule descriptorMap unit graphs W D slot := by
  simp [slotKey, Prod.mk.eta, toLex_ofLex]

private theorem reflectSlotKey_eq (graphs : Fin 4 → RootedDigraph Atom) (W D : ℕ) (slot : Fin 4) :
    slotKey (fun s => (ofLex (retainedSourceKey molecule descriptorMap unit graphs W D s)).1)
        (fun s => (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit
          (graphs s) W D)).2) slot =
      retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit (graphs slot) W D := by
  have hprior := retainedCompleteLigandPriorKeyAt_reflect molecule descriptorMap unit
    (graphs slot) W D
  have hfst :
      (ofLex (retainedSourceKey molecule descriptorMap unit graphs W D slot)).1 =
        (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit
          (graphs slot) W D)).1 := by
    simp [retainedSourceKey, retainedCompleteLigandRule5KeyAt_prior, hprior]
  simp only [slotKey]
  rw [hfst]
  exact toLex_ofLex _

noncomputable def retainedFourSlotReflection (graphs : Fin 4 → RootedDigraph Atom) (W D : ℕ)
    (inj : Function.Injective (retainedSourceKey molecule descriptorMap unit graphs W D)) :
    FourSlotReflection CompleteLigandPriorKey (List (Key StereoLabel)) where
  prior := fun slot =>
    (ofLex (retainedSourceKey molecule descriptorMap unit graphs W D slot)).1
  later := fun slot =>
    (ofLex (retainedSourceKey molecule descriptorMap unit graphs W D slot)).2
  laterReflect := fun slot =>
    (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit
      (graphs slot) W D)).2
  keyInjective := by
    intro a b hab
    exact inj (by simpa [sourceSlotKey_eq molecule descriptorMap unit graphs W D] using hab)
  reflectInjective := by
    intro a b hab
    exact inj ((retainedCompleteLigandRule5KeyAt_reflect_eq_iff molecule descriptorMap unit
      (graphs a) (graphs b) W D).1 (by
        simpa [reflectSlotKey_eq molecule descriptorMap unit graphs W D] using hab))
  classAtMostTwo := by
    intro i j k hij hik
    have hpri : ∀ slot,
        retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs slot) W D =
          (ofLex (retainedSourceKey molecule descriptorMap unit graphs W D slot)).1 := by
      intro slot
      simp [retainedSourceKey, retainedCompleteLigandRule5KeyAt_prior]
    rcases retainedPriorClass_atMostTwo molecule descriptorMap unit graphs W D inj i j k
        (by rw [hpri, hpri]; exact hij) (by rw [hpri, hpri]; exact hik) with
      hjk | hji | hki
    · exact Or.inr (Or.inr hjk)
    · exact Or.inl hji.symm
    · exact Or.inr (Or.inl hki.symm)
  tieReverses := by
    intro i j _ hprior
    have hpri : retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs i) W D =
        retainedCompleteLigandPriorKeyAt molecule descriptorMap unit (graphs j) W D := by
      simpa [retainedSourceKey, retainedCompleteLigandRule5KeyAt_prior] using hprior
    have hcmpR := retainedPairCompare_reflect molecule descriptorMap unit
      (graphs j) (graphs i) W D
    rw [if_pos hpri.symm] at hcmpR
    rw [compare_comm_swap
      (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs i) W D)
      (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs j) W D)] at hcmpR
    constructor
    · intro hlt
      have hsrc : compare (retainedSourceKey molecule descriptorMap unit graphs W D i)
          (retainedSourceKey molecule descriptorMap unit graphs W D j) = Ordering.lt :=
        (completeLigandRule5Key_compare_lt_iff _ _).2
          (by simpa [sourceSlotKey_eq molecule descriptorMap unit graphs W D] using hlt)
      simp only [retainedSourceKey] at hsrc
      rw [hsrc] at hcmpR
      simp only [Ordering.swap] at hcmpR
      simpa [reflectSlotKey_eq molecule descriptorMap unit graphs W D] using
        (completeLigandRule5Key_compare_lt_iff _ _).1 hcmpR
    · intro hlt
      have hrev : compare (retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit
          (graphs j) W D) (retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit
          (graphs i) W D) = Ordering.lt :=
        (completeLigandRule5Key_compare_lt_iff _ _).2
          (by simpa [reflectSlotKey_eq molecule descriptorMap unit graphs W D] using hlt)
      rw [hcmpR] at hrev
      cases hsrc : compare
          (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs i) W D)
          (retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs j) W D) with
      | lt =>
          simpa [sourceSlotKey_eq molecule descriptorMap unit graphs W D, retainedSourceKey] using
            (completeLigandRule5Key_compare_lt_iff _ _).1 hsrc
      | eq =>
          rw [hsrc] at hrev
          simp only [Ordering.swap] at hrev
          cases hrev
      | gt =>
          rw [hsrc] at hrev
          simp only [Ordering.swap] at hrev
          cases hrev

private theorem count_trichotomy (graphs : Fin 4 → RootedDigraph Atom) (W D : ℕ)
    (inj : Function.Injective (retainedSourceKey molecule descriptorMap unit graphs W D)) :
    completeRule5PairCount (retainedSourceKey molecule descriptorMap unit graphs W D) = 0 ∨
      completeRule5PairCount (retainedSourceKey molecule descriptorMap unit graphs W D) = 1 ∨
      completeRule5PairCount (retainedSourceKey molecule descriptorMap unit graphs W D) = 2 := by
  have hbound := completeRule5PairCount_even_or_one_of_injective molecule descriptorMap unit
    graphs W D (by simpa [retainedSourceKey] using inj)
  have hle := completeRule5PairCount_le_two_of_injective molecule descriptorMap unit graphs W D
    (by simpa [retainedSourceKey] using inj)
  unfold retainedSourceKey at hbound hle ⊢
  generalize hcount : completeRule5PairCount (fun slot =>
      retainedCompleteLigandRule5KeyAt molecule descriptorMap unit (graphs slot) W D) = n
    at hbound hle ⊢
  have h012 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  rcases hbound with hEven | rfl
  · rcases h012 with rfl | rfl | rfl
    · left; rfl
    · exact absurd hEven Nat.not_even_one
    · right; right; rfl
  · right; left; rfl

theorem classify_retainedPhysicalLetter (mirror : Bool) (raw : RS) (count : ℕ)
    (hcount : count = 0 ∨ count = 1 ∨ count = 2)
    (rawImage : RS)
    (hraw : rawImage = if mirror = true ∧ (count = 0 ∨ count = 2) then RS.swap raw else raw) :
    classifyTetrahedralRSPseudo rawImage count =
      retainedPhysicalLetter mirror (classifyTetrahedralRSPseudo raw count) := by
  cases mirror with
  | false =>
      have hsame : rawImage = raw := by simpa using hraw
      subst hsame
      simp [retainedPhysicalLetter]
  | true =>
      rcases hcount with rfl | rfl | rfl
      · have hswap : rawImage = RS.swap raw := by simpa using hraw
        cases raw <;> simp [hswap, classifyTetrahedralRSPseudo, retainedPhysicalLetter,
          reflectUppercaseAuxiliaryLabel, RS.swap]
      · have hsame : rawImage = raw := by simpa using hraw
        cases raw <;> simp [hsame, classifyTetrahedralRSPseudo, retainedPhysicalLetter,
          reflectUppercaseAuxiliaryLabel, pseudoRSOfRS]
      · have hswap : rawImage = RS.swap raw := by simpa using hraw
        cases raw <;> simp [hswap, classifyTetrahedralRSPseudo, retainedPhysicalLetter,
          reflectUppercaseAuxiliaryLabel, RS.swap]

private theorem judgment_of_descending (keys : Fin 4 → CompleteLigandRule5Key)
    (points : Fin 4 → CartesianPoint3) (inj : Function.Injective keys)
    (hvol : CartesianPoint3.orientedVolume (points ((descendingOrder keys inj) 0))
      (points ((descendingOrder keys inj) 1)) (points ((descendingOrder keys inj) 2))
      (points ((descendingOrder keys inj) 3)) ≠ 0) :
    CompleteRootDescriptorJudgment keys points (classifyTetrahedralRSPseudo
      (if CartesianPoint3.orientedVolume (points ((descendingOrder keys inj) 0))
          (points ((descendingOrder keys inj) 1)) (points ((descendingOrder keys inj) 2))
          (points ((descendingOrder keys inj) 3)) < 0 then RS.R else RS.S)
      (completeRule5PairCount keys)) := by
  let σ := descendingOrder keys inj
  let vol := CartesianPoint3.orientedVolume (points (σ 0)) (points (σ 1)) (points (σ 2))
    (points (σ 3))
  have hlist : (List.ofFn σ).map points = [points (σ 0), points (σ 1), points (σ 2), points (σ 3)] := by
    rw [List.map_ofFn]
    exact ofFn_fin4 _
  rcases lt_trichotomy vol 0 with hlt | heq | hgt
  · exact ⟨List.ofFn σ, RS.R, descendingOrder_perm_finRange keys inj,
      descendingOrder_pairwise keys inj, ⟨points (σ 0), points (σ 1), points (σ 2),
        points (σ 3), hlist, hlt⟩, by
          change classifyTetrahedralRSPseudo (if vol < 0 then RS.R else RS.S)
              (completeRule5PairCount keys) =
            classifyTetrahedralRSPseudo RS.R (completeRule5PairCount keys)
          rw [if_pos hlt]⟩
  · exact absurd heq hvol
  · exact ⟨List.ofFn σ, RS.S, descendingOrder_perm_finRange keys inj,
      descendingOrder_pairwise keys inj, ⟨points (σ 0), points (σ 1), points (σ 2),
        points (σ 3), hlist, hgt⟩, by
          change classifyTetrahedralRSPseudo (if vol < 0 then RS.R else RS.S)
              (completeRule5PairCount keys) =
            classifyTetrahedralRSPseudo RS.S (completeRule5PairCount keys)
          rw [if_neg (not_lt_of_gt hgt)]⟩

private theorem presented_count (mirror : Bool) (graphs : Fin 4 → RootedDigraph Atom)
    (slotPerm : Equiv.Perm (Fin 4)) (W D : ℕ) :
    completeRule5PairCount (retainedImageKey molecule descriptorMap unit mirror graphs slotPerm W D) =
      completeRule5PairCount (retainedSourceKey molecule descriptorMap unit graphs W D) := by
  cases mirror with
  | false =>
      simpa [retainedImageKey, retainedSourceKey] using
        completeRule5PairCount_reindex (retainedSourceKey molecule descriptorMap unit graphs W D)
          slotPerm⁻¹
  | true =>
      have hreflected := completeRule5PairCount_reflect molecule descriptorMap unit graphs W D
      have hreindex := completeRule5PairCount_reindex
        (fun slot => retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect unit
          (graphs slot) W D) slotPerm⁻¹
      simpa [retainedImageKey, retainedSourceKey] using hreindex.trans hreflected

theorem enumerationSign_applySpace_reindex (mirror : Bool) (slotPerm : Equiv.Perm (Fin 4))
    (sourcePoints : Fin 4 → CartesianPoint3) :
    rationalVolumeSign (slotVolume fun slot =>
        applySpace mirror (sourcePoints (slotPerm⁻¹ slot))) =
      physicalMirrorFactor mirror * permHandedness slotPerm *
        rationalVolumeSign (slotVolume sourcePoints) := by
  have hspace := orientedVolume_applySpace mirror (sourcePoints (slotPerm⁻¹ 0))
    (sourcePoints (slotPerm⁻¹ 1)) (sourcePoints (slotPerm⁻¹ 2)) (sourcePoints (slotPerm⁻¹ 3))
  have hperm := sortedVolume_sign sourcePoints slotPerm⁻¹
  rw [permHandedness_inv] at hperm
  cases mirror with
  | false =>
      simp only [applySpace, physicalMirrorFactor, Bool.false_eq_true, ite_false, slotVolume] at hperm ⊢
      rw [hperm, mul_comm, one_mul]
  | true =>
      simp only [applySpace, physicalMirrorFactor, ite_true, slotVolume] at hspace hperm ⊢
      rw [hspace]
      have hcast : ((-1 : ℤ) : ℚ) *
          CartesianPoint3.orientedVolume (sourcePoints (slotPerm⁻¹ 0))
            (sourcePoints (slotPerm⁻¹ 1)) (sourcePoints (slotPerm⁻¹ 2))
            (sourcePoints (slotPerm⁻¹ 3)) =
        -CartesianPoint3.orientedVolume (sourcePoints (slotPerm⁻¹ 0))
            (sourcePoints (slotPerm⁻¹ 1)) (sourcePoints (slotPerm⁻¹ 2))
            (sourcePoints (slotPerm⁻¹ 3)) := by norm_num
      rw [hcast, rationalVolumeSign_neg, hperm, mul_comm]
      ring

private theorem raw_of_descriptor {points : List CartesianPoint3} {raw : RS}
    (h : RationalTetrahedralDescriptor points raw) {a b c d : CartesianPoint3}
    (hlist : points = [a, b, c, d]) :
    (if CartesianPoint3.orientedVolume a b c d < 0 then RS.R else RS.S) = raw := by
  obtain ⟨a', b', c', d', hpoints, hsign⟩ := h
  rw [hlist] at hpoints
  injection hpoints with ha hrest
  injection hrest with hb hrest
  injection hrest with hc hrest
  injection hrest with hd _
  subst ha
  subst hb
  subst hc
  subst hd
  cases raw with
  | R => simp [hsign]
  | S =>
      have hnot : ¬ CartesianPoint3.orientedVolume a b c d < 0 := not_lt_of_gt hsign
      simp [hnot]

private theorem raw_eq_of_same_sign (volume other : ℚ)
    (hsign : rationalVolumeSign volume = rationalVolumeSign other)
    (hvol : volume ≠ 0) (hother : other ≠ 0) :
    (if volume < 0 then RS.R else RS.S) = if other < 0 then RS.R else RS.S := by
  rcases rationalVolumeSign_eq_neg_or_one hother with hneg | hpos
  · have hotherLt : other < 0 := (rationalVolumeSign_eq_neg_iff_of_ne hother).1 hneg
    have hvolLt : volume < 0 := (rationalVolumeSign_eq_neg_iff_of_ne hvol).1 (hsign.trans hneg)
    simp [hotherLt, hvolLt]
  · have hotherGt : 0 < other := (rationalVolumeSign_eq_one_iff_of_ne hother).1 hpos
    have hvolGt : 0 < volume := (rationalVolumeSign_eq_one_iff_of_ne hvol).1 (hsign.trans hpos)
    simp [not_lt_of_gt hotherGt, not_lt_of_gt hvolGt]

private theorem raw_swap_of_neg_sign (volume other : ℚ)
    (hsign : rationalVolumeSign volume = -rationalVolumeSign other)
    (hvol : volume ≠ 0) (hother : other ≠ 0) :
    (if volume < 0 then RS.R else RS.S) =
      RS.swap (if other < 0 then RS.R else RS.S) := by
  rcases rationalVolumeSign_eq_neg_or_one hother with hneg | hpos
  · have hotherLt : other < 0 := (rationalVolumeSign_eq_neg_iff_of_ne hother).1 hneg
    have hvolSign : rationalVolumeSign volume = 1 := by
      calc
        rationalVolumeSign volume = -rationalVolumeSign other := hsign
        _ = 1 := by rw [hneg]; norm_num
    have hvolGt : 0 < volume := (rationalVolumeSign_eq_one_iff_of_ne hvol).1 hvolSign
    simp [hotherLt, not_lt_of_gt hvolGt, RS.swap]
  · have hotherGt : 0 < other := (rationalVolumeSign_eq_one_iff_of_ne hother).1 hpos
    have hvolSign : rationalVolumeSign volume = -1 := by
      rw [hsign, hpos]
    have hvolLt : volume < 0 := (rationalVolumeSign_eq_neg_iff_of_ne hvol).1 hvolSign
    simp [hvolLt, not_lt_of_gt hotherGt, RS.swap]

theorem completeRootDescriptorJudgment_retainedPhysical (mirror : Bool)
    (graphs : Fin 4 → RootedDigraph Atom) (slotPerm : Equiv.Perm (Fin 4))
    (sourcePoints imagePoints : Fin 4 → CartesianPoint3) (W D : ℕ)
    (descriptor : LocalizedAuxiliaryLabel)
    (hsign : rationalVolumeSign (slotVolume imagePoints) =
      physicalMirrorFactor mirror * permHandedness slotPerm *
        rationalVolumeSign (slotVolume sourcePoints))
    (judgment : CompleteRootDescriptorJudgment
      (retainedSourceKey molecule descriptorMap unit graphs W D) sourcePoints descriptor) :
    CompleteRootDescriptorJudgment
      (retainedImageKey molecule descriptorMap unit mirror graphs slotPerm W D) imagePoints
      (retainedPhysicalLetter mirror descriptor) := by
  have hinj := completeRootDescriptorJudgment_injective judgment
  have hsourceExists : slotVolume sourcePoints ≠ 0 :=
    ((completeRootDescriptorJudgment_exists_iff
      (retainedSourceKey molecule descriptorMap unit graphs W D) sourcePoints).1
      ⟨descriptor, judgment⟩).2
  have hcount012 := count_trichotomy molecule descriptorMap unit graphs W D hinj
  let sourceKey := retainedSourceKey molecule descriptorMap unit graphs W D
  let imageKey := retainedImageKey molecule descriptorMap unit mirror graphs slotPerm W D
  have hinjI := (imageKey_injective_iff molecule descriptorMap unit mirror graphs slotPerm W D).2 hinj
  let σS := descendingOrder sourceKey hinj
  let volS := CartesianPoint3.orientedVolume (sourcePoints (σS 0)) (sourcePoints (σS 1))
    (sourcePoints (σS 2)) (sourcePoints (σS 3))
  have hvolS : volS ≠ 0 := by
    intro hzero
    have hsignS := sortedVolume_sign sourcePoints σS
    have hzeroSign : rationalVolumeSign volS = 0 := (rationalVolumeSign_eq_zero_iff _).2 hzero
    rw [hsignS] at hzeroSign
    have hhand := permHandedness_eq_one_or_eq_neg_one σS
    have henum : rationalVolumeSign (slotVolume sourcePoints) ≠ 0 :=
      (rationalVolumeSign_eq_zero_iff _).not.mpr hsourceExists
    rcases hhand with h | h <;> simp [h] at hzeroSign <;> exact henum hzeroSign
  let rawS : RS := if volS < 0 then RS.R else RS.S
  have hsourceCanon := judgment_of_descending sourceKey sourcePoints hinj hvolS
  have hletterS : classifyTetrahedralRSPseudo rawS (completeRule5PairCount sourceKey) = descriptor :=
    completeRootDescriptorJudgment_unique hsourceCanon judgment
  have hcountEq := presented_count molecule descriptorMap unit mirror graphs slotPerm W D
  let σI := descendingOrder imageKey hinjI
  let volI := CartesianPoint3.orientedVolume (imagePoints (σI 0)) (imagePoints (σI 1))
    (imagePoints (σI 2)) (imagePoints (σI 3))
  have hdescS : ∀ p q, p < q → sourceKey (σS q) < sourceKey (σS p) := by
    have hpair := descendingOrder_pairwise sourceKey hinj
    rw [List.pairwise_ofFn] at hpair
    exact hpair
  have hsignSorted : rationalVolumeSign volI =
      (if mirror = true ∧ (completeRule5PairCount sourceKey = 0 ∨
        completeRule5PairCount sourceKey = 2) then (-1 : ℝ) else 1) *
        rationalVolumeSign volS := by
    have hbaseS := sortedVolume_sign sourcePoints σS
    have hbaseI := sortedVolume_sign imagePoints σI
    cases mirror with
    | false =>
        have hσ : σI = slotPerm * σS := by
          refine (descendingOrder_unique imageKey hinjI (slotPerm * σS) ?_).symm
          intro p q hpq
          simpa [imageKey, retainedImageKey, Equiv.Perm.mul_apply, Equiv.symm_apply_apply] using
            hdescS p q hpq
        rw [hσ, permHandedness_mul, hsign] at hbaseI
        simp only [physicalMirrorFactor, Bool.false_eq_true, ite_false, slotVolume, volS] at hbaseI hbaseS ⊢
        rcases permHandedness_eq_one_or_eq_neg_one slotPerm with hτ | hτ <;>
          rcases permHandedness_eq_one_or_eq_neg_one σS with hσS | hσS
        all_goals
          simp only [hτ, hσS, volI, hσ, false_and, if_false] at hbaseI hbaseS ⊢
          rw [hbaseI, hbaseS]
          ring
    | true =>
        let data := retainedFourSlotReflection molecule descriptorMap unit graphs W D hinj
        let ρ := descendingOrder (slotKey data.prior data.laterReflect) data.reflectInjective
        have hslotS : ∀ p q, p < q →
            slotKey data.prior data.later (σS q) < slotKey data.prior data.later (σS p) := by
          intro p q hpq
          change retainedSourceKey molecule descriptorMap unit graphs W D (σS q) <
            retainedSourceKey molecule descriptorMap unit graphs W D (σS p)
          exact hdescS p q hpq
        have hslotR : ∀ p q, p < q →
            slotKey data.prior data.laterReflect (ρ q) <
              slotKey data.prior data.laterReflect (ρ p) := by
          have hpair := descendingOrder_pairwise (slotKey data.prior data.laterReflect)
            data.reflectInjective
          rw [List.pairwise_ofFn] at hpair
          simpa using hpair
        have hrefl := descendingReflection_sign data σS ρ hslotS hslotR
        have hσ : σI = slotPerm * ρ := by
          refine (descendingOrder_unique imageKey hinjI (slotPerm * ρ) ?_).symm
          intro p q hpq
          have hdesc := hslotR p q hpq
          change slotKey
              (fun s => (ofLex (retainedSourceKey molecule descriptorMap unit graphs W D s)).1)
              (fun s => (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect
                unit (graphs s) W D)).2) (ρ q) <
            slotKey
              (fun s => (ofLex (retainedSourceKey molecule descriptorMap unit graphs W D s)).1)
              (fun s => (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect
                unit (graphs s) W D)).2) (ρ p) at hdesc
          rw [reflectSlotKey_eq molecule descriptorMap unit graphs W D (ρ q),
            reflectSlotKey_eq molecule descriptorMap unit graphs W D (ρ p)] at hdesc
          simpa [imageKey, retainedImageKey, Equiv.Perm.mul_apply,
            Equiv.symm_apply_apply] using hdesc
        have htie : priorTieCount data.prior = completeRule5PairCount sourceKey := by
          simpa [data, sourceKey] using priorTieCount_completeRule5PairCount sourceKey
        have hpermρ : permHandedness ρ =
            permHandedness σS * (-1) ^ completeRule5PairCount sourceKey := by
          have hmul : σS * (σS⁻¹ * ρ) = ρ := by group
          calc permHandedness ρ
              = permHandedness (σS * (σS⁻¹ * ρ)) := congrArg permHandedness hmul.symm
            _ = permHandedness σS * permHandedness (σS⁻¹ * ρ) := permHandedness_mul _ _
            _ = permHandedness σS * (-1) ^ priorTieCount data.prior := by
              exact congrArg (fun x => permHandedness σS * x) hrefl.2.2
            _ = permHandedness σS * (-1) ^ completeRule5PairCount sourceKey := by rw [htie]
        rw [hσ, permHandedness_mul, hpermρ, hsign] at hbaseI
        simp only [physicalMirrorFactor, ite_true, slotVolume, volS] at hbaseI hbaseS hcount012 ⊢
        rcases hcount012 with hcount0 | hcount1 | hcount2
        · have hcount0' : completeRule5PairCount sourceKey = 0 := by simpa [sourceKey] using hcount0
          rw [hcount0'] at hbaseI ⊢
          rcases permHandedness_eq_one_or_eq_neg_one slotPerm with hτ | hτ <;>
            rcases permHandedness_eq_one_or_eq_neg_one σS with hσS | hσS
          all_goals
            simp only [hτ, hσS, pow_zero, volI, hσ] at hbaseI hbaseS ⊢
            rw [hbaseI, hbaseS]
            norm_num
        · have hcount1' : completeRule5PairCount sourceKey = 1 := by simpa [sourceKey] using hcount1
          rw [hcount1'] at hbaseI ⊢
          rcases permHandedness_eq_one_or_eq_neg_one slotPerm with hτ | hτ <;>
            rcases permHandedness_eq_one_or_eq_neg_one σS with hσS | hσS
          all_goals
            simp only [hτ, hσS, pow_one, volI, hσ] at hbaseI hbaseS ⊢
            rw [hbaseI, hbaseS]
            norm_num
        · have hcount2' : completeRule5PairCount sourceKey = 2 := by simpa [sourceKey] using hcount2
          rw [hcount2'] at hbaseI ⊢
          rcases permHandedness_eq_one_or_eq_neg_one slotPerm with hτ | hτ <;>
            rcases permHandedness_eq_one_or_eq_neg_one σS with hσS | hσS
          all_goals
            simp only [hτ, hσS, volI, hσ] at hbaseI hbaseS ⊢
            rw [hbaseI, hbaseS]
            norm_num
  have hvolI : volI ≠ 0 := by
    intro hzero
    have hzeroSign := (rationalVolumeSign_eq_zero_iff volI).2 hzero
    rw [hsignSorted] at hzeroSign
    have hsourceSign : rationalVolumeSign volS ≠ 0 :=
      fun h => hvolS ((rationalVolumeSign_eq_zero_iff volS).1 h)
    have hfactor : (if mirror = true ∧ (completeRule5PairCount sourceKey = 0 ∨
        completeRule5PairCount sourceKey = 2) then (-1 : ℝ) else 1) ≠ 0 := by
      split_ifs <;> norm_num
    rw [mul_eq_zero] at hzeroSign
    rcases hzeroSign with hbad | hbad
    · exact hfactor hbad
    · exact hsourceSign hbad
  let rawI : RS := if volI < 0 then RS.R else RS.S
  have hraw : rawI = if mirror = true ∧ (completeRule5PairCount sourceKey = 0 ∨
      completeRule5PairCount sourceKey = 2) then RS.swap rawS else rawS := by
    cases mirror with
    | false =>
        have hsame : rationalVolumeSign volI = rationalVolumeSign volS := by
          simpa [Bool.false_eq_true] using hsignSorted
        simpa [rawI, rawS, Bool.false_eq_true] using
          raw_eq_of_same_sign volI volS hsame hvolI hvolS
    | true =>
        let data := retainedFourSlotReflection molecule descriptorMap unit graphs W D hinj
        let ρ := descendingOrder (slotKey data.prior data.laterReflect) data.reflectInjective
        let volρ := CartesianPoint3.orientedVolume (sourcePoints (ρ 0)) (sourcePoints (ρ 1))
          (sourcePoints (ρ 2)) (sourcePoints (ρ 3))
        have hslotS : ∀ p q, p < q →
            slotKey data.prior data.later (σS q) < slotKey data.prior data.later (σS p) := by
          intro p q hpq
          change retainedSourceKey molecule descriptorMap unit graphs W D (σS q) <
            retainedSourceKey molecule descriptorMap unit graphs W D (σS p)
          exact hdescS p q hpq
        have hslotR : ∀ p q, p < q →
            slotKey data.prior data.laterReflect (ρ q) <
              slotKey data.prior data.laterReflect (ρ p) := by
          have hpair := descendingOrder_pairwise (slotKey data.prior data.laterReflect)
            data.reflectInjective
          rw [List.pairwise_ofFn] at hpair
          simpa using hpair
        have hσ : σI = slotPerm * ρ := by
          refine (descendingOrder_unique imageKey hinjI (slotPerm * ρ) ?_).symm
          intro p q hpq
          have hdesc := hslotR p q hpq
          change slotKey
              (fun s => (ofLex (retainedSourceKey molecule descriptorMap unit graphs W D s)).1)
              (fun s => (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect
                unit (graphs s) W D)).2) (ρ q) <
            slotKey
              (fun s => (ofLex (retainedSourceKey molecule descriptorMap unit graphs W D s)).1)
              (fun s => (ofLex (retainedCompleteLigandRule5KeyAt molecule descriptorMap.reflect
                unit (graphs s) W D)).2) (ρ p) at hdesc
          rw [reflectSlotKey_eq molecule descriptorMap unit graphs W D (ρ q),
            reflectSlotKey_eq molecule descriptorMap unit graphs W D (ρ p)] at hdesc
          simpa [imageKey, retainedImageKey, Equiv.Perm.mul_apply,
            Equiv.symm_apply_apply] using hdesc
        have hvolρ : volρ ≠ 0 := by
          intro hzero
          have hρs := sortedVolume_sign sourcePoints ρ
          have hz := (rationalVolumeSign_eq_zero_iff volρ).2 hzero
          rw [hρs] at hz
          have hsrc : rationalVolumeSign (slotVolume sourcePoints) ≠ 0 :=
            fun h => hsourceExists ((rationalVolumeSign_eq_zero_iff _).1 h)
          rcases permHandedness_eq_one_or_eq_neg_one ρ with h | h <;> simp [h] at hz <;> exact hsrc hz
        have hneg : rationalVolumeSign volI = -rationalVolumeSign volρ := by
          have hI := sortedVolume_sign imagePoints σI
          have hρs := sortedVolume_sign sourcePoints ρ
          rw [hσ, permHandedness_mul, hsign] at hI
          simp only [physicalMirrorFactor, ite_true, slotVolume, volρ] at hI hρs ⊢
          rcases permHandedness_eq_one_or_eq_neg_one slotPerm with hτ | hτ <;>
            rcases permHandedness_eq_one_or_eq_neg_one ρ with hρh | hρh
          all_goals
            simp only [hτ, hρh, volI, hσ] at hI hρs ⊢
            rw [hI, hρs]
            ring
        have hdescRaw : RationalTetrahedralDescriptor
            (List.ofFn fun i => sourcePoints (σS i)) rawS := by
          rw [ofFn_fin4]
          refine ⟨sourcePoints (σS 0), sourcePoints (σS 1), sourcePoints (σS 2),
            sourcePoints (σS 3), rfl, ?_⟩
          by_cases hlt : volS < 0
          · have hrawS : rawS = RS.R := by simp [rawS, hlt]
            simpa [hrawS, volS] using hlt
          · have hgt : 0 < volS := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm hvolS)
            have hrawS : rawS = RS.S := by simp [rawS, hlt]
            simpa [hrawS, volS] using hgt
        have hletter := rationalDescriptor_reflection data sourcePoints σS ρ hslotS hslotR hdescRaw
        have htie : priorTieCount data.prior = completeRule5PairCount sourceKey := by
          simpa [data, sourceKey] using priorTieCount_completeRule5PairCount sourceKey
        have hrawρ := raw_of_descriptor hletter (ofFn_fin4 fun i => sourcePoints (ρ i))
        have hswapRaw := raw_swap_of_neg_sign volI volρ hneg hvolI hvolρ
        have hrawI : rawI =
            RS.swap (if Even (completeRule5PairCount sourceKey) then rawS else RS.swap rawS) := by
          have hρraw : (if volρ < 0 then RS.R else RS.S) =
              if Even (priorTieCount data.prior) then rawS else RS.swap rawS := by
            simpa [volρ] using hrawρ
          rw [hρraw, htie] at hswapRaw
          simpa [rawI] using hswapRaw
        rcases hcount012 with h0 | h1 | h2
        · have hcount0 : completeRule5PairCount sourceKey = 0 := by simpa [sourceKey] using h0
          rw [hcount0] at hrawI ⊢
          norm_num at hrawI ⊢
          simpa [hrawI, RS.swap]
        · have hcount1 : completeRule5PairCount sourceKey = 1 := by simpa [sourceKey] using h1
          rw [hcount1] at hrawI ⊢
          norm_num at hrawI ⊢
          exact hrawI
        · have hcount2 : completeRule5PairCount sourceKey = 2 := by simpa [sourceKey] using h2
          rw [hcount2] at hrawI ⊢
          norm_num at hrawI ⊢
          simpa [hrawI, RS.swap]
  have himageCanon := judgment_of_descending imageKey imagePoints hinjI hvolI
  have hclass := classify_retainedPhysicalLetter mirror rawS (completeRule5PairCount sourceKey)
    hcount012 rawI hraw
  change CompleteRootDescriptorJudgment imageKey imagePoints
    (classifyTetrahedralRSPseudo rawI (completeRule5PairCount imageKey)) at himageCanon
  rw [hcountEq, hclass, hletterS] at himageCanon
  simpa [imageKey] using himageCanon

theorem completeRootOutcome_retainedPhysical (mirror : Bool)
    (graphs : Fin 4 → RootedDigraph Atom) (slotPerm : Equiv.Perm (Fin 4))
    (sourcePoints imagePoints : Fin 4 → CartesianPoint3) (W D : ℕ)
    (outcome : Option LocalizedAuxiliaryLabel)
    (hsign : rationalVolumeSign (slotVolume imagePoints) =
      physicalMirrorFactor mirror * permHandedness slotPerm *
        rationalVolumeSign (slotVolume sourcePoints)) :
    CompleteRootOutcome (retainedImageKey molecule descriptorMap unit mirror graphs slotPerm W D)
        imagePoints (Option.map (retainedPhysicalLetter mirror) outcome) ↔
      CompleteRootOutcome (retainedSourceKey molecule descriptorMap unit graphs W D)
        sourcePoints outcome := by
  cases outcome with
  | none =>
      simp only [Option.map, CompleteRootOutcome]
      constructor
      · intro hnone ⟨descriptor, judgment⟩
        exact hnone ⟨retainedPhysicalLetter mirror descriptor,
          completeRootDescriptorJudgment_retainedPhysical molecule descriptorMap unit mirror graphs
            slotPerm sourcePoints imagePoints W D descriptor hsign judgment⟩
      · intro hnone ⟨descriptor, judgment⟩
        have hinjI := completeRootDescriptorJudgment_injective judgment
        have hvolI : slotVolume imagePoints ≠ 0 :=
          ((completeRootDescriptorJudgment_exists_iff _ imagePoints).1 ⟨descriptor, judgment⟩).2
        have hinj := (imageKey_injective_iff molecule descriptorMap unit mirror graphs slotPerm W D).1
          hinjI
        have hvol := (slotVolume_ne_zero_iff mirror slotPerm sourcePoints imagePoints hsign).1 hvolI
        obtain ⟨sourceDescriptor, sourceJudgment⟩ :=
          (completeRootDescriptorJudgment_exists_iff _ sourcePoints).2 ⟨hinj, hvol⟩
        exact hnone ⟨sourceDescriptor, sourceJudgment⟩
  | some descriptor =>
      simp only [Option.map, CompleteRootOutcome]
      constructor
      · intro judgment
        have hinjI := completeRootDescriptorJudgment_injective judgment
        have hvolI : slotVolume imagePoints ≠ 0 :=
          ((completeRootDescriptorJudgment_exists_iff _ imagePoints).1
            ⟨retainedPhysicalLetter mirror descriptor, judgment⟩).2
        have hinj := (imageKey_injective_iff molecule descriptorMap unit mirror graphs slotPerm W D).1
          hinjI
        have hvol := (slotVolume_ne_zero_iff mirror slotPerm sourcePoints imagePoints hsign).1 hvolI
        obtain ⟨sourceDescriptor, sourceJudgment⟩ :=
          (completeRootDescriptorJudgment_exists_iff _ sourcePoints).2 ⟨hinj, hvol⟩
        have himage := completeRootDescriptorJudgment_retainedPhysical molecule descriptorMap unit
          mirror graphs slotPerm sourcePoints imagePoints W D sourceDescriptor hsign sourceJudgment
        have hsame := completeRootDescriptorJudgment_unique judgment himage
        have hback := congrArg (retainedPhysicalLetter mirror) hsame
        rw [retainedPhysicalLetter_involutive, retainedPhysicalLetter_involutive] at hback
        exact hback.symm ▸ sourceJudgment
      · intro judgment
        exact completeRootDescriptorJudgment_retainedPhysical molecule descriptorMap unit mirror
          graphs slotPerm sourcePoints imagePoints W D descriptor hsign judgment

theorem completeRootOutcome_applySpace_reindex (mirror : Bool)
    (graphs : Fin 4 → RootedDigraph Atom) (slotPerm : Equiv.Perm (Fin 4))
    (sourcePoints : Fin 4 → CartesianPoint3) (W D : ℕ)
    (outcome : Option LocalizedAuxiliaryLabel) :
    CompleteRootOutcome (retainedImageKey molecule descriptorMap unit mirror graphs slotPerm W D)
        (fun slot => applySpace mirror (sourcePoints (slotPerm⁻¹ slot)))
        (Option.map (retainedPhysicalLetter mirror) outcome) ↔
      CompleteRootOutcome (retainedSourceKey molecule descriptorMap unit graphs W D)
        sourcePoints outcome :=
  completeRootOutcome_retainedPhysical molecule descriptorMap unit mirror graphs slotPerm
    sourcePoints (fun slot => applySpace mirror (sourcePoints (slotPerm⁻¹ slot))) W D outcome
    (enumerationSign_applySpace_reindex mirror slotPerm sourcePoints)

theorem completeRootOutcome_branchMirror (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center) (branchFrom branchTo : Fin 4) (mirror : Bool)
    (transport : input.DetectedBranchTransport e cfg root branchFrom branchTo mirror)
    (reached : RootedTetrahedralBranchSymmetry.LigandBranchReaches
      input.detectedMultiCenterMolecule root branchFrom (input.physicalSourceCenter center).1)
    (sourcePointAt imagePointAt : Fin 4 → CartesianPoint3)
    (sourceCalibration : rationalVolumeSign (enumerationVolume sourcePointAt) =
      input.detectedMultiCenterMolecule.configurationSign cfg (input.physicalSourceCenter center))
    (imageCalibration : rationalVolumeSign (enumerationVolume imagePointAt) =
      input.detectedMultiCenterMolecule.configurationSign cfg (input.physicalImageCenter e center))
    (graphs : Fin 4 → RootedDigraph (Fin input.certified.input.molecule.atomCount))
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (W D : ℕ)
    (outcome : Option LocalizedAuxiliaryLabel) :
    CompleteRootOutcome
        (retainedImageKey input.moleculeGraph descriptorMap unit mirror graphs packed.slotPerm W D)
        (fun slot => imagePointAt (packed.imageReindex slot))
        (Option.map (retainedPhysicalLetter mirror) outcome) ↔
      CompleteRootOutcome
        (retainedSourceKey input.moleculeGraph descriptorMap unit graphs W D)
        (fun slot => sourcePointAt (packed.sourceReindex slot)) outcome := by
  have hsign := input.actualFrame_orientedVolumeSign_branchMirror singleBonded e target center
    packed cfg root branchFrom branchTo mirror transport reached sourcePointAt imagePointAt
    sourceCalibration imageCalibration
  have hsource : slotVolume (fun slot => sourcePointAt (packed.sourceReindex slot)) =
      reindexedVolume sourcePointAt packed.sourceReindex := rfl
  have himage : slotVolume (fun slot => imagePointAt (packed.imageReindex slot)) =
      reindexedVolume imagePointAt packed.imageReindex := rfl
  apply completeRootOutcome_retainedPhysical input.moleculeGraph descriptorMap unit mirror graphs
    packed.slotPerm (fun slot => sourcePointAt (packed.sourceReindex slot))
    (fun slot => imagePointAt (packed.imageReindex slot)) W D outcome
  rw [hsource, himage]
  exact hsign

end

end TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness

assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness.retainedPhysicalLetter_involutive
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness.retainedFourSlotReflection
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness.classify_retainedPhysicalLetter
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness.enumerationSign_applySpace_reindex
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness.completeRootDescriptorJudgment_retainedPhysical
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness.completeRootOutcome_retainedPhysical
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness.completeRootOutcome_applySpace_reindex
assert_kernel_only TetraStereo.OneCenter.LocalizedRetainedMirrorDescriptorCorrectness.completeRootOutcome_branchMirror
