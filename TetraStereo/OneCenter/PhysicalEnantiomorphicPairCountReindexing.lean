import TetraStereo.OneCenter.LocalizedTrackedSortSourcePairFidelity
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
import TetraStereo.KernelOnly
import Mathlib.Data.List.Perm.Subperm

set_option autoImplicit false

namespace TetraStereo.OneCenter

open RootedTetrahedralBranchSymmetry

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
















































/-! ## Off-diagonal congruence of the source pair count -/

/-- Two `if p then 1 else 0` terms agree when the propositions are equivalent. -/
private theorem ite_one_zero_congr {p q : Prop} [Decidable p] [Decidable q]
    (h : p ↔ q) : (if p then (1 : ℕ) else 0) = (if q then 1 else 0) := by
  by_cases hp : p
  · have hq : q := h.mp hp
    simp [hp, hq]
  · have hq : ¬ q := fun hh => hp (h.mpr hh)
    simp [hp, hq]

/-- The independent source pair count depends only on the off-diagonal values of the relation.

The six summands are the six increasing representatives of the unordered pairs, so no diagonal
value is ever inspected.  This is the form needed to transport a count between two descriptions
that agree on distinct positions. -/
theorem sourceEnantiomorphicPairCount_congr
    (relation other : Fin 4 → Fin 4 → Prop)
    [DecidableRel relation] [DecidableRel other]
    (agree : ∀ first second : Fin 4, first ≠ second →
      (relation first second ↔ other first second)) :
    sourceEnantiomorphicPairCount relation = sourceEnantiomorphicPairCount other := by
  have e01 := ite_one_zero_congr (agree 0 1 (by decide))
  have e02 := ite_one_zero_congr (agree 0 2 (by decide))
  have e12 := ite_one_zero_congr (agree 1 2 (by decide))
  have e03 := ite_one_zero_congr (agree 0 3 (by decide))
  have e13 := ite_one_zero_congr (agree 1 3 (by decide))
  have e23 := ite_one_zero_congr (agree 2 3 (by decide))
  unfold sourceEnantiomorphicPairCount
  rw [e01, e02, e12, e03, e13, e23]

/-- The pointwise (all-pairs) form of `sourceEnantiomorphicPairCount_congr`. -/
theorem sourceEnantiomorphicPairCount_congr_of_forall
    (relation other : Fin 4 → Fin 4 → Prop)
    [DecidableRel relation] [DecidableRel other]
    (agree : ∀ first second : Fin 4, relation first second ↔ other first second) :
    sourceEnantiomorphicPairCount relation = sourceEnantiomorphicPairCount other :=
  sourceEnantiomorphicPairCount_congr relation other
    (fun first second _ => agree first second)

/-! ## Canonical ordered representatives of unordered slot pairs -/

/-- The ordered representative of the unordered slot pair `{first, second}` with the smaller
component first.  For distinct inputs this is precisely the unique increasing representative used
by `sourceUnorderedPairList`. -/
def canonicalOrderedPair (first second : Fin 4) : Fin 4 × Fin 4 :=
  if first < second then (first, second) else (second, first)

/-- For distinct inputs the canonical representative is increasing. -/
theorem canonicalOrderedPair_lt {first second : Fin 4} (hne : first ≠ second) :
    (canonicalOrderedPair first second).1 < (canonicalOrderedPair first second).2 := by
  by_cases h : first < second
  · rw [canonicalOrderedPair, if_pos h]
    exact h
  · have hgt : second < first := lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hne)
    rw [canonicalOrderedPair, if_neg h]
    exact hgt

/-- Evaluation at an increasing pair. -/
theorem canonicalOrderedPair_of_lt {first second : Fin 4} (h : first < second) :
    canonicalOrderedPair first second = (first, second) := by
  simp [canonicalOrderedPair, h]

/-- Evaluation at a decreasing pair. -/
theorem canonicalOrderedPair_of_gt {first second : Fin 4} (h : second < first) :
    canonicalOrderedPair first second = (second, first) := by
  simp [canonicalOrderedPair, not_lt_of_gt h]

/-- The canonical representative ignores the order of its arguments. -/
theorem canonicalOrderedPair_comm (first second : Fin 4) :
    canonicalOrderedPair first second = canonicalOrderedPair second first := by
  by_cases h : first < second
  · rw [canonicalOrderedPair_of_lt h, canonicalOrderedPair_of_gt h]
  · by_cases h' : second < first
    · rw [canonicalOrderedPair_of_gt h', canonicalOrderedPair_of_lt h']
    · have heq : first = second :=
        le_antisymm (le_of_not_gt h') (le_of_not_gt h)
      subst heq
      rfl

/-- On increasing pairs the canonical representative is injective. -/
theorem canonicalOrderedPair_inj_of_lt {a b c d : Fin 4}
    (hab : a < b) (hcd : c < d)
    (heq : canonicalOrderedPair a b = canonicalOrderedPair c d) :
    a = c ∧ b = d := by
  rw [canonicalOrderedPair_of_lt hab, canonicalOrderedPair_of_lt hcd] at heq
  exact ⟨congrArg Prod.fst heq, congrArg Prod.snd heq⟩

/-- The canonical pair attached to a frame enumeration: the slot pair `(first, second)` is sent
to the increasing representative of the canonical slot pair `{alpha first, alpha second}`. -/
def canonicalizedFramePair (sigma : Equiv.Perm (Fin 4)) (pair : Fin 4 × Fin 4) : Fin 4 × Fin 4 :=
  canonicalOrderedPair (sigma pair.1) (sigma pair.2)

/-- Applying a frame permutation and canonicalising the result permutes the six enumerated
unordered pairs.  This is the combinatorial core of frame invariance: the map is a bijection of
`sourceUnorderedPairList` onto itself. -/
theorem canonicalizedFramePair_perm_sourceUnorderedPairList (sigma : Equiv.Perm (Fin 4)) :
    (sourceUnorderedPairList.map (canonicalizedFramePair sigma)).Perm
      sourceUnorderedPairList := by
  classical
  have hnodup : (sourceUnorderedPairList.map (canonicalizedFramePair sigma)).Nodup := by
    apply List.Nodup.map_on _ nodup_sourceUnorderedPairList
    intro p hp q hq heq
    have hp_lt : p.1 < p.2 := (mem_sourceUnorderedPairList_iff p.1 p.2).mp hp
    have hq_lt : q.1 < q.2 := (mem_sourceUnorderedPairList_iff q.1 q.2).mp hq
    have hp_ne : p.1 ≠ p.2 := ne_of_lt hp_lt
    have hq_ne : q.1 ≠ q.2 := ne_of_lt hq_lt
    have heq' : canonicalOrderedPair (sigma p.1) (sigma p.2) =
        canonicalOrderedPair (sigma q.1) (sigma q.2) := heq
    by_cases hpcase : sigma p.1 < sigma p.2
    · have hL : canonicalOrderedPair (sigma p.1) (sigma p.2) = (sigma p.1, sigma p.2) :=
        canonicalOrderedPair_of_lt hpcase
      by_cases hqcase : sigma q.1 < sigma q.2
      · have hR : canonicalOrderedPair (sigma q.1) (sigma q.2) = (sigma q.1, sigma q.2) :=
          canonicalOrderedPair_of_lt hqcase
        rw [hL, hR] at heq'
        exact Prod.ext (sigma.injective (congrArg Prod.fst heq'))
          (sigma.injective (congrArg Prod.snd heq'))
      · have hq_gt : sigma q.2 < sigma q.1 :=
          lt_of_le_of_ne (le_of_not_gt hqcase)
            (Ne.symm (fun h : sigma q.1 = sigma q.2 => hq_ne (sigma.injective h)))
        have hR : canonicalOrderedPair (sigma q.1) (sigma q.2) = (sigma q.2, sigma q.1) :=
          canonicalOrderedPair_of_gt hq_gt
        rw [hL, hR] at heq'
        have e1 : p.1 = q.2 := sigma.injective (congrArg Prod.fst heq')
        have e2 : p.2 = q.1 := sigma.injective (congrArg Prod.snd heq')
        exfalso
        have hpv : (p.1 : ℕ) < (p.2 : ℕ) := hp_lt
        have hqv : (q.1 : ℕ) < (q.2 : ℕ) := hq_lt
        have e1v : (p.1 : ℕ) = (q.2 : ℕ) := congrArg Fin.val e1
        have e2v : (p.2 : ℕ) = (q.1 : ℕ) := congrArg Fin.val e2
        omega
    · have hp_gt : sigma p.2 < sigma p.1 :=
        lt_of_le_of_ne (le_of_not_gt hpcase)
          (Ne.symm (fun h : sigma p.1 = sigma p.2 => hp_ne (sigma.injective h)))
      have hL : canonicalOrderedPair (sigma p.1) (sigma p.2) = (sigma p.2, sigma p.1) :=
        canonicalOrderedPair_of_gt hp_gt
      by_cases hqcase : sigma q.1 < sigma q.2
      · have hR : canonicalOrderedPair (sigma q.1) (sigma q.2) = (sigma q.1, sigma q.2) :=
          canonicalOrderedPair_of_lt hqcase
        rw [hL, hR] at heq'
        have e1 : p.2 = q.1 := sigma.injective (congrArg Prod.fst heq')
        have e2 : p.1 = q.2 := sigma.injective (congrArg Prod.snd heq')
        exfalso
        have hpv : (p.1 : ℕ) < (p.2 : ℕ) := hp_lt
        have hqv : (q.1 : ℕ) < (q.2 : ℕ) := hq_lt
        have e1v : (p.2 : ℕ) = (q.1 : ℕ) := congrArg Fin.val e1
        have e2v : (p.1 : ℕ) = (q.2 : ℕ) := congrArg Fin.val e2
        omega
      · have hq_gt : sigma q.2 < sigma q.1 :=
          lt_of_le_of_ne (le_of_not_gt hqcase)
            (Ne.symm (fun h : sigma q.1 = sigma q.2 => hq_ne (sigma.injective h)))
        have hR : canonicalOrderedPair (sigma q.1) (sigma q.2) = (sigma q.2, sigma q.1) :=
          canonicalOrderedPair_of_gt hq_gt
        rw [hL, hR] at heq'
        exact Prod.ext (sigma.injective (congrArg Prod.snd heq'))
          (sigma.injective (congrArg Prod.fst heq'))
  have hmem : ∀ x ∈ sourceUnorderedPairList.map (canonicalizedFramePair sigma),
      x ∈ sourceUnorderedPairList := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hp_lt : p.1 < p.2 := (mem_sourceUnorderedPairList_iff p.1 p.2).mp hp
    have hp_ne : p.1 ≠ p.2 := ne_of_lt hp_lt
    exact (mem_sourceUnorderedPairList_iff _ _).mpr
      (canonicalOrderedPair_lt (fun h => hp_ne (sigma.injective h)))
  have hsub : List.Subperm (sourceUnorderedPairList.map (canonicalizedFramePair sigma))
      sourceUnorderedPairList :=
    List.Nodup.subperm hnodup hmem
  obtain ⟨candidate, hcandidateperm, hcandidatesubl⟩ := List.subperm_iff.mp hsub
  have hlen : (sourceUnorderedPairList.map (canonicalizedFramePair sigma)).length =
      candidate.length := by
    have hleft : (sourceUnorderedPairList.map (canonicalizedFramePair sigma)).length =
        sourceUnorderedPairList.length := List.length_map ..
    have hright : candidate.length = sourceUnorderedPairList.length :=
      hcandidateperm.length_eq
    omega
  have heq : sourceUnorderedPairList.map (canonicalizedFramePair sigma) = candidate :=
    hcandidatesubl.eq_of_length hlen
  rw [heq]
  exact hcandidateperm

/-! ## Pointwise predicate preservation and permutation invariance -/

/-- Reindexing by a permutation preserves the truth value of a symmetric relation between the
canonicalised increasing representatives and the original slot pair. -/
theorem canonicalizedFramePair_pointwise
    (relation : Fin 4 → Fin 4 → Prop) [DecidableRel relation]
    (symmetric : ∀ first second, relation first second → relation second first)
    (sigma : Equiv.Perm (Fin 4)) {pair : Fin 4 × Fin 4}
    (hmem : pair ∈ sourceUnorderedPairList) :
    decide (relation (sigma pair.1) (sigma pair.2)) =
      decide (relation (canonicalizedFramePair sigma pair).1
        (canonicalizedFramePair sigma pair).2) := by
  have hp_lt : pair.1 < pair.2 := (mem_sourceUnorderedPairList_iff pair.1 pair.2).mp hmem
  have hp_ne : pair.1 ≠ pair.2 := ne_of_lt hp_lt
  have hsig_ne : sigma pair.1 ≠ sigma pair.2 :=
    fun h => hp_ne (sigma.injective h)
  by_cases h : sigma pair.1 < sigma pair.2
  · have hval : canonicalizedFramePair sigma pair = (sigma pair.1, sigma pair.2) := by
      simp [canonicalizedFramePair, canonicalOrderedPair, h]
    rw [hval]
  · have hgt : sigma pair.2 < sigma pair.1 :=
      lt_of_le_of_ne (le_of_not_gt h) (Ne.symm hsig_ne)
    have hval : canonicalizedFramePair sigma pair = (sigma pair.2, sigma pair.1) := by
      simp [canonicalizedFramePair, canonicalOrderedPair, h]
    rw [hval]
    exact decide_eq_decide.mpr
      ⟨fun hr => symmetric _ _ hr, fun hr => symmetric _ _ hr⟩

/-- The independent source count is invariant under an arbitrary permutation of the four slot
labels, **provided the relation is symmetric**.

Symmetry is essential.  The enumeration `sourceUnorderedPairList` uses only increasing
representatives `i < j`; a composition with a permutation can move a directed satisfied pair to a
decreasing representative, which the count does not see.  See
`sourceEnantiomorphicPairCount_perm_counterexample`. -/
theorem sourceEnantiomorphicPairCount_perm
    (relation : Fin 4 → Fin 4 → Prop) [DecidableRel relation]
    (symmetric : ∀ first second, relation first second → relation second first)
    (sigma : Equiv.Perm (Fin 4)) :
    sourceEnantiomorphicPairCount
        (fun first second => relation (sigma first) (sigma second)) =
      sourceEnantiomorphicPairCount relation := by
  classical
  rw [sourceEnantiomorphicPairCount_eq_filter_length,
    sourceEnantiomorphicPairCount_eq_filter_length]
  have hfilter :
      (sourceUnorderedPairList.filter
          (fun pair => decide (relation (sigma pair.1) (sigma pair.2)))) =
        (sourceUnorderedPairList.filter
          (fun pair => decide (relation (canonicalizedFramePair sigma pair).1
            (canonicalizedFramePair sigma pair).2))) :=
    List.filter_congr (l := sourceUnorderedPairList)
      (fun pair hmem => canonicalizedFramePair_pointwise relation symmetric sigma hmem)
  have hfilterPerm :
      ((sourceUnorderedPairList.map (canonicalizedFramePair sigma)).filter
          (fun pair => decide (relation pair.1 pair.2))).Perm
        (sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2))) :=
    (canonicalizedFramePair_perm_sourceUnorderedPairList sigma).filter
      (fun pair : Fin 4 × Fin 4 => decide (relation pair.1 pair.2))
  calc
    (sourceUnorderedPairList.filter
        (fun pair => decide (relation (sigma pair.1) (sigma pair.2)))).length
        = (sourceUnorderedPairList.filter
            (fun pair => decide (relation (canonicalizedFramePair sigma pair).1
              (canonicalizedFramePair sigma pair).2))).length := by rw [hfilter]
    _ = ((sourceUnorderedPairList.map (canonicalizedFramePair sigma)).filter
          (fun pair => decide (relation pair.1 pair.2))).length := by
          rw [List.filter_map, List.length_map]
          rfl
    _ = (sourceUnorderedPairList.filter
          (fun pair => decide (relation pair.1 pair.2))).length := hfilterPerm.length_eq

/-! ## The symmetry hypothesis is not removable -/

/-- The directed relation holding only for the ordered pair `(0, 1)`. -/
def directedWitnessRelation (first second : Fin 4) : Prop :=
  first = 0 ∧ second = 1

instance directedWitnessRelationDecidableRel : DecidableRel directedWitnessRelation :=
  fun first second => by
    unfold directedWitnessRelation
    infer_instance

/-- The directed witness relation is not symmetric. -/
theorem directedWitnessRelation_not_symmetric :
    ¬ (∀ first second : Fin 4, directedWitnessRelation first second →
      directedWitnessRelation second first) := by
  intro symmetric
  have both := symmetric 0 1 ⟨rfl, rfl⟩
  exact absurd both.2 (by decide)

/-- Its source count is one: the unique satisfied ordered pair is the increasing representative
`(0, 1)`. -/
theorem directedWitness_count :
    sourceEnantiomorphicPairCount directedWitnessRelation = 1 := by
  decide

/-- After composing with the transposition `0 1`, the unique satisfied ordered pair is `(1, 0)`,
which is not one of the increasing representatives, so the count is zero. -/
theorem directedWitness_swap_count :
    sourceEnantiomorphicPairCount
        (fun first second =>
          directedWitnessRelation (Equiv.swap (0 : Fin 4) 1 first)
            (Equiv.swap (0 : Fin 4) 1 second)) = 0 := by
  decide

/-- **Without symmetry, permutation invariance of the source count is false.**  The directed
relation `i = 0 ∧ j = 1` has count `1`, while its composition with the slot transposition `0 1`
has count `0`.  Hence `sourceEnantiomorphicPairCount_perm` must carry its explicit symmetry
hypothesis; the physical branch relation supplies it via `enantiomorphic_symm`. -/
theorem sourceEnantiomorphicPairCount_perm_counterexample :
    sourceEnantiomorphicPairCount
        (fun first second =>
          directedWitnessRelation (Equiv.swap (0 : Fin 4) 1 first)
            (Equiv.swap (0 : Fin 4) 1 second)) ≠
      sourceEnantiomorphicPairCount directedWitnessRelation := by
  rw [directedWitness_swap_count, directedWitness_count]
  decide

/-! ## The physical pair count -/

/-- Classical decidability of the physical enantiomorphic relation at a root. -/
instance physicalEnantiomorphicPairCountDecidableRel
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) :
    DecidableRel (fun first second : Fin 4 => Enantiomorphic m cfg c first second) :=
  fun _ _ => Classical.propDecidable _

/-- The physical count of unordered enantiomorphic ligand-branch pairs at a root.

This is the existing independent source count applied to the existing frame-aware physical
relation, not a new counting implementation.  Only the six increasing representatives of the four
slots are inspected. -/
def physicalEnantiomorphicPairCount (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) : ℕ :=
  sourceEnantiomorphicPairCount (fun first second : Fin 4 => Enantiomorphic m cfg c first second)

/-- Defining equation of the physical count. -/
theorem physicalEnantiomorphicPairCount_eq_sourceCount (m : MultiCenterMolecule V)
    (cfg : m.Configuration) (c : m.Center) :
    physicalEnantiomorphicPairCount m cfg c =
      sourceEnantiomorphicPairCount
        (fun first second : Fin 4 => Enantiomorphic m cfg c first second) := rfl

/-- The physical enantiomorphic relation is symmetric (existing theorem). -/
theorem physicalEnantiomorphic_symmetric (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) :
    ∀ first second : Fin 4, Enantiomorphic m cfg c first second →
      Enantiomorphic m cfg c second first :=
  fun _ _ h => enantiomorphic_symm m cfg c h



def frameEnumeratedEnantiomorphic (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) (alpha : Equiv.Perm (Fin 4)) (first second : Fin 4) : Prop :=
  Enantiomorphic m cfg c (alpha first) (alpha second)

/-- Classical decidability of the frame-enumerated physical relation. -/
instance frameEnumeratedEnantiomorphicDecidableRel (m : MultiCenterMolecule V)
    (cfg : m.Configuration) (c : m.Center) (alpha : Equiv.Perm (Fin 4)) :
    DecidableRel (frameEnumeratedEnantiomorphic m cfg c alpha) :=
  fun _ _ => Classical.propDecidable _



def frameEnumeratedEnantiomorphicPairCount (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) (alpha : Equiv.Perm (Fin 4)) : ℕ :=
  sourceEnantiomorphicPairCount (frameEnumeratedEnantiomorphic m cfg c alpha)

/-- Defining equation of the frame-enumerated count. -/
theorem frameEnumeratedEnantiomorphicPairCount_eq_sourceCount
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (alpha : Equiv.Perm (Fin 4)) :
    frameEnumeratedEnantiomorphicPairCount m cfg c alpha =
      sourceEnantiomorphicPairCount
        (fun first second : Fin 4 =>
          Enantiomorphic m cfg c (alpha first) (alpha second)) := rfl




theorem frameEnumeratedEnantiomorphicPairCount_eq
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (alpha : Equiv.Perm (Fin 4)) :
    frameEnumeratedEnantiomorphicPairCount m cfg c alpha =
      physicalEnantiomorphicPairCount m cfg c := by
  rw [frameEnumeratedEnantiomorphicPairCount_eq_sourceCount,
    physicalEnantiomorphicPairCount_eq_sourceCount]
  exact sourceEnantiomorphicPairCount_perm
    (fun first second : Fin 4 => Enantiomorphic m cfg c first second)
    (fun first second h => enantiomorphic_symm m cfg c h) alpha

/-- **Exactly one unordered physical enantiomorphic pair.**  The physical count is one exactly
when there is a unique unordered enantiomorphic pair, expressed via ordered-pair uniqueness. -/
theorem physicalEnantiomorphicPairCount_eq_one_iff (m : MultiCenterMolecule V)
    (cfg : m.Configuration) (c : m.Center) :
    physicalEnantiomorphicPairCount m cfg c = 1 ↔
      ∃ first second : Fin 4,
        first ≠ second ∧ Enantiomorphic m cfg c first second ∧
          ∀ otherFirst otherSecond : Fin 4, otherFirst ≠ otherSecond →
            Enantiomorphic m cfg c otherFirst otherSecond →
            ((otherFirst = first ∧ otherSecond = second) ∨
             (otherFirst = second ∧ otherSecond = first)) := by
  rw [physicalEnantiomorphicPairCount_eq_sourceCount]
  exact sourceEnantiomorphicPairCount_eq_one_iff
    (fun first second : Fin 4 => Enantiomorphic m cfg c first second)
    (fun first second h => enantiomorphic_symm m cfg c h)

/-- The same exactly-one characterisation for the count read through an arbitrary frame
enumeration. -/
theorem frameEnumeratedEnantiomorphicPairCount_eq_one_iff
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (alpha : Equiv.Perm (Fin 4)) :
    frameEnumeratedEnantiomorphicPairCount m cfg c alpha = 1 ↔
      ∃ first second : Fin 4,
        first ≠ second ∧ Enantiomorphic m cfg c (alpha first) (alpha second) ∧
          ∀ otherFirst otherSecond : Fin 4, otherFirst ≠ otherSecond →
            Enantiomorphic m cfg c (alpha otherFirst) (alpha otherSecond) →
            ((otherFirst = first ∧ otherSecond = second) ∨
             (otherFirst = second ∧ otherSecond = first)) := by
  rw [frameEnumeratedEnantiomorphicPairCount_eq_sourceCount]
  exact sourceEnantiomorphicPairCount_eq_one_iff
    (fun first second : Fin 4 => Enantiomorphic m cfg c (alpha first) (alpha second))
    (fun first second h => enantiomorphic_symm m cfg c h)

/-- **The physical pair count is invariant under per-center ligand-frame reindexing.**  This is
the direct coordinate statement: `reindexFrames` changes only the slot numbering, and the
existing reindexing equivalence for `Enantiomorphic` transports the relation into the permuted
slot description, where `sourceEnantiomorphicPairCount_perm` applies. -/
theorem physicalEnantiomorphicPairCount_reindexFrames (m : MultiCenterMolecule V)
    (tau : m.Center → Equiv.Perm (Fin 4)) (cfg : m.Configuration) (c : m.Center) :
    physicalEnantiomorphicPairCount (m.reindexFrames tau) (m.reindexConfiguration tau cfg) c =
      physicalEnantiomorphicPairCount m cfg c := by
  rw [physicalEnantiomorphicPairCount_eq_sourceCount,
    physicalEnantiomorphicPairCount_eq_sourceCount]
  calc
    sourceEnantiomorphicPairCount
        (fun first second : Fin 4 =>
          Enantiomorphic (m.reindexFrames tau) (m.reindexConfiguration tau cfg) c
            first second)
        = sourceEnantiomorphicPairCount
            (fun first second : Fin 4 =>
              Enantiomorphic m cfg c (tau c first) (tau c second)) :=
          sourceEnantiomorphicPairCount_congr _ _
            (fun first second _ => MultiCenterMolecule.enantiomorphic_reindexFrames_iff
              m tau cfg c first second)
    _ = sourceEnantiomorphicPairCount
          (fun first second : Fin 4 => Enantiomorphic m cfg c first second) :=
          sourceEnantiomorphicPairCount_perm
            (fun first second : Fin 4 => Enantiomorphic m cfg c first second)
            (fun first second h => enantiomorphic_symm m cfg c h) (tau c)

/-! ## Partner uniqueness at the physical level -/

/-- Two enantiomorphic partners of the same physical branch coincide, given pairwise
proper-distinguishability of the root branches.  This is the existing source-symmetry matching
result, restated at the physical relation; it does not assume a bridge from the actual
classifier's tie relation to `Enantiomorphic`. -/
theorem physicalEnantiomorphicPartner_unique (m : MultiCenterMolecule V)
    (cfg : m.Configuration) (c : m.Center)
    (hdistinct : ∀ first second : Fin 4, first ≠ second →
      ¬ ProperTransport m cfg c first second)
    {first second third : Fin 4}
    (hsecond : Enantiomorphic m cfg c first second)
    (hthird : Enantiomorphic m cfg c first third) : second = third :=
  enantiomorphic_partner_unique m cfg c hdistinct hsecond hthird

/-- The subtype of physical enantiomorphic partners of a fixed branch is a subsingleton under
pairwise proper-distinguishability. -/
theorem physicalEnantiomorphicPartner_subsingleton (m : MultiCenterMolecule V)
    (cfg : m.Configuration) (c : m.Center)
    (hdistinct : ∀ first second : Fin 4, first ≠ second →
      ¬ ProperTransport m cfg c first second)
    (first : Fin 4) :
    Subsingleton { second : Fin 4 // Enantiomorphic m cfg c first second } :=
  enantiomorphicPartner_subsingleton m cfg c first hdistinct

/-! ## Kernel-authority guards -/

assert_kernel_only sourceEnantiomorphicPairCount_congr
assert_kernel_only sourceEnantiomorphicPairCount_congr_of_forall
assert_kernel_only canonicalOrderedPair
assert_kernel_only canonicalOrderedPair_lt
assert_kernel_only canonicalOrderedPair_of_lt
assert_kernel_only canonicalOrderedPair_of_gt
assert_kernel_only canonicalOrderedPair_comm
assert_kernel_only canonicalOrderedPair_inj_of_lt
assert_kernel_only canonicalizedFramePair
assert_kernel_only canonicalizedFramePair_perm_sourceUnorderedPairList
assert_kernel_only canonicalizedFramePair_pointwise
assert_kernel_only sourceEnantiomorphicPairCount_perm
assert_kernel_only directedWitnessRelation
assert_kernel_only directedWitnessRelationDecidableRel
assert_kernel_only directedWitnessRelation_not_symmetric
assert_kernel_only directedWitness_count
assert_kernel_only directedWitness_swap_count
assert_kernel_only sourceEnantiomorphicPairCount_perm_counterexample
assert_kernel_only physicalEnantiomorphicPairCountDecidableRel
assert_kernel_only physicalEnantiomorphicPairCount
assert_kernel_only physicalEnantiomorphicPairCount_eq_sourceCount
assert_kernel_only physicalEnantiomorphic_symmetric
assert_kernel_only frameEnumeratedEnantiomorphic
assert_kernel_only frameEnumeratedEnantiomorphicDecidableRel
assert_kernel_only frameEnumeratedEnantiomorphicPairCount
assert_kernel_only frameEnumeratedEnantiomorphicPairCount_eq_sourceCount
assert_kernel_only frameEnumeratedEnantiomorphicPairCount_eq
assert_kernel_only physicalEnantiomorphicPairCount_eq_one_iff
assert_kernel_only frameEnumeratedEnantiomorphicPairCount_eq_one_iff
assert_kernel_only physicalEnantiomorphicPairCount_reindexFrames
assert_kernel_only physicalEnantiomorphicPartner_unique
assert_kernel_only physicalEnantiomorphicPartner_subsingleton

end

end TetraStereo.OneCenter
