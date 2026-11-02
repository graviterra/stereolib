import TetraStereo.OneCenter.LocalizedActualOrderedRootPhysicalCorrectness
import TetraStereo.OneCenter.LocalizedActualRankKeyBridge
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The multi-reference root: a fully independent Rules-1–4c priority

R1 (`LocalizedActualOrderedRootPhysicalCorrectness`) states the absolute letter of the ordered
evaluator at a multi-reference root against a *hybrid* comparison (`independentCompare`): the
actual cumulative Rule-4a key comparison followed by the independent ligand-signature comparison,
and it takes the strict numeric priority realizing that comparison as a premise.  This module
removes both:

* `independentKey` — the independent key of a ligand: the independent **pair key** of
  `DeclarativeCIPRankKeyProjection` at the ligand root (constitutional vector key, then the Rule-4a
  component of the ordinary key over the rank evidence) followed by the independent ligand
  signature, all at one common layout.  It is an element of a linear order.
* `independentCompare_eq_lt_iff` / `independentCompare_eq_eq_iff` — the hybrid comparison *is*
  the comparison of the independent keys in their linear order.  The constitutional prefix is the accepted cross-arm constitutional transfer
  (`arm_compare_eq_compare_vector`), the Rule-4a step is the Rule-4a table bridge
  (`arm_node_bridge4a`, `compare_descriptor_eq_compare_key`) under the molecular readback of the
  arm (`armReadback_of_treeLike`), and the signature step is C5 as in R1.
* `priority` — the numeric priority of a ligand is the number of ligands with a strictly smaller
  independent key; when the four keys are pairwise distinct it is injective and realizes the
  comparison (`compare_priority`).
* `orderedReferenceState_top_eq_chiral_of_independentKeys` — **the absolute letter from the
  independent keys alone**: if the four independent keys are pairwise distinct, the ordered
  evaluator's fixed point at the centre is the uppercase letter read from the oriented volume of
  the canonical ligand atoms' coordinates listed in descending independent key.

No priority, rank or comparison outcome is supplied.  Pairwise distinctness of the independent keys
is the pre-Rule-5 separation condition; a pair with equal independent keys is the Rule-5 case.
-/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open CertifiedLocalizedCIPInput
open CertifiedLocalizedCIPInput.OriginalRootArm
open DeclarativeCIP
open Certificate.CanonicalSphereKey (Key)

noncomputable section
open scoped Classical

/-! ## Generic facts about comparators and lexicographic products -/

/-- An ordering value characterized by `lt` and `eq` against a linear order is the comparison. -/
theorem eq_compare_of_iff {α : Type*} [LinearOrder α] (o : Ordering) (x y : α)
    (hlt : o = .lt ↔ x < y) (heq : o = .eq ↔ x = y) : o = compare x y := by
  rcases lt_trichotomy x y with h | h | h
  · rw [hlt.2 h, compare_lt_iff_lt.2 h]
  · rw [heq.2 h, compare_eq_iff_eq.2 h]
  · have h1 : o ≠ .lt := fun e => absurd (hlt.1 e) (not_lt.2 h.le)
    have h2 : o ≠ .eq := fun e => absurd (heq.1 e) h.ne'
    have h3 : o = .gt := by cases o <;> simp_all
    rw [h3, compare_gt_iff_gt.2 h]

/-- The lexicographic combination of two characterized comparators is characterized on the
lexicographic product: the `lt` half. -/
theorem then_eq_lt_iff_lex {A B : Type*} [LinearOrder A] [LinearOrder B]
    (cmpA : A → A → Ordering) (cmpB : B → B → Ordering)
    (hltA : ∀ a b, cmpA a b = .lt ↔ a < b) (heqA : ∀ a b, cmpA a b = .eq ↔ a = b)
    (hltB : ∀ a b, cmpB a b = .lt ↔ a < b) (a a' : A) (b b' : B) :
    (cmpA a a').then (cmpB b b') = .lt ↔ toLex (a, b) < toLex (a', b') := by
  rw [Prod.Lex.lt_iff]
  simp only [ofLex_toLex]
  cases h : cmpA a a' with
  | lt => simp [Ordering.then, (hltA _ _).1 h]
  | eq =>
      have hab := (heqA _ _).1 h
      subst hab
      simp [Ordering.then, hltB]
  | gt =>
      have hnlt : ¬ a < a' := fun hab => by
        rw [← hltA] at hab; simp [h] at hab
      have hne : a ≠ a' := fun hab => by
        rw [← heqA] at hab; simp [h] at hab
      simp [Ordering.then, hnlt, hne]

/-- The `eq` half. -/
theorem then_eq_eq_iff_lex {A B : Type*} [LinearOrder A] [LinearOrder B]
    (cmpA : A → A → Ordering) (cmpB : B → B → Ordering)
    (heqA : ∀ a b, cmpA a b = .eq ↔ a = b) (heqB : ∀ a b, cmpB a b = .eq ↔ a = b)
    (a a' : A) (b b' : B) :
    (cmpA a a').then (cmpB b b') = .eq ↔ toLex (a, b) = toLex (a', b') := by
  simp only [toLex_inj, Prod.mk.injEq]
  cases h : cmpA a a' with
  | lt =>
      have hne : a ≠ a' := fun hab => by
        rw [← heqA] at hab; simp [h] at hab
      simp [Ordering.then, hne]
  | eq =>
      have hab := (heqA _ _).1 h
      subst hab
      simp [Ordering.then, heqB]
  | gt =>
      have hne : a ≠ a' := fun hab => by
        rw [← heqA] at hab; simp [h] at hab
      simp [Ordering.then, hne]

/-- Lists of sphere keys: the list comparator against the lexicographic order. -/
theorem listKey_compare_lt_iff {α : Type*} [LinearOrder α] (l₁ l₂ : List (Key α)) :
    List.compareLex compare l₁ l₂ = .lt ↔ l₁ < l₂ :=
  compareLex_eq_lt_iff_of compare key_compare_lt_iff key_compare_eq_iff l₁ l₂

theorem listKey_compare_eq_iff {α : Type*} [LinearOrder α] (l₁ l₂ : List (Key α)) :
    List.compareLex compare l₁ l₂ = .eq ↔ l₁ = l₂ :=
  compareLex_eq_eq_iff_of compare key_compare_eq_iff l₁ l₂

/-- The independent signature comparator against the lexicographic order. -/
theorem signatureCompare_eq_lt_iff (s t : Lex (ℕ × List (Key StereoLabel))) :
    signatureCompare (ofLex s) (ofLex t) = .lt ↔ s < t :=
  then_eq_lt_iff_lex compare (List.compareLex compare)
    (fun _ _ => compare_lt_iff_lt) (fun _ _ => compare_eq_iff_eq) listKey_compare_lt_iff
    (ofLex s).1 (ofLex t).1 (ofLex s).2 (ofLex t).2

theorem signatureCompare_eq_eq_iff (s t : Lex (ℕ × List (Key StereoLabel))) :
    signatureCompare (ofLex s) (ofLex t) = .eq ↔ s = t :=
  then_eq_eq_iff_lex compare (List.compareLex compare)
    (fun _ _ => compare_eq_iff_eq) listKey_compare_eq_iff
    (ofLex s).1 (ofLex t).1 (ofLex s).2 (ofLex t).2

/-- The pair-key comparator (constitutional vector key, then Rule-4a key). -/
def pairKeyCompare (p q : Lex (List (Key ℤ) × Key StereoLabel)) : Ordering :=
  (compare (ofLex p).1 (ofLex q).1).then (compare (ofLex p).2 (ofLex q).2)

theorem pairKeyCompare_eq_lt_iff (p q : Lex (List (Key ℤ) × Key StereoLabel)) :
    pairKeyCompare p q = .lt ↔ p < q :=
  then_eq_lt_iff_lex compare compare listKey_compare_lt_iff listKey_compare_eq_iff
    key_compare_lt_iff (ofLex p).1 (ofLex q).1 (ofLex p).2 (ofLex q).2

theorem pairKeyCompare_eq_eq_iff (p q : Lex (List (Key ℤ) × Key StereoLabel)) :
    pairKeyCompare p q = .eq ↔ p = q :=
  then_eq_eq_iff_lex compare compare listKey_compare_eq_iff key_compare_eq_iff
    (ofLex p).1 (ofLex q).1 (ofLex p).2 (ofLex q).2

/-! ## Ranks from a finite injective key -/

section Rank

variable {α : Type*} [LinearOrder α] (key : Fin 4 → α)

/-- The number of positions whose key is strictly smaller. -/
def keyRank (ℓ : Fin 4) : ℕ := (Finset.univ.filter fun m => key m < key ℓ).card

theorem keyRank_lt_of_lt {ℓ m : Fin 4} (h : key ℓ < key m) : keyRank key ℓ < keyRank key m := by
  unfold keyRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · exact ⟨ℓ, by simp [h], by simp⟩
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.trans h

theorem compare_keyRank (injective : Function.Injective key) (ℓ m : Fin 4) :
    compare (keyRank key ℓ) (keyRank key m) = compare (key ℓ) (key m) := by
  rcases lt_trichotomy (key ℓ) (key m) with h | h | h
  · rw [compare_lt_iff_lt.2 h, compare_lt_iff_lt.2 (keyRank_lt_of_lt key h)]
  · rw [injective h, compare_eq_iff_eq.2 rfl, compare_eq_iff_eq.2 rfl]
  · rw [compare_gt_iff_gt.2 h, compare_gt_iff_gt.2 (keyRank_lt_of_lt key h)]

theorem keyRank_injective (injective : Function.Injective key) :
    Function.Injective (keyRank key) := by
  intro ℓ m h
  have := compare_keyRank key injective ℓ m
  rw [compare_eq_iff_eq.2 h] at this
  exact injective (compare_eq_iff_eq.1 this.symm)

theorem keyRank_lt_iff (injective : Function.Injective key) (ℓ m : Fin 4) :
    keyRank key ℓ < keyRank key m ↔ key ℓ < key m := by
  rw [← compare_lt_iff_lt, compare_keyRank key injective, compare_lt_iff_lt]

theorem keyRank_eq_iff (injective : Function.Injective key) (ℓ m : Fin 4) :
    keyRank key ℓ = keyRank key m ↔ key ℓ = key m :=
  ⟨fun h => congrArg key (keyRank_injective key injective h), fun h => by rw [injective h]⟩

end Rank

namespace ActualCentrePhysicalSetup

variable {input : LocalizedUniversalReference.Input} (S : ActualCentrePhysicalSetup input)

/-! ## The independent keys of the four ligands -/

/-- The independent rank evidence of ligand `ℓ`'s arm graph (Rules 3 and 4a over the generated
descriptor map). -/
abbrev rankEvidenceOf (ℓ : Fin 4) :=
  rankEvidence input.certified.moleculeGraph (actualReferenceDescriptorMap input)
    (input.certified.topUnit S.center) (armGraph (S.arm4a ℓ))

/-- The independent pair key of ligand `ℓ` at the common layout: constitutional vector key, then
the Rule-4a component of the ordinary key over the rank evidence, both at the ligand root. -/
def independentPairKey (ℓ : Fin 4) : Lex (List (Key ℤ) × Key StereoLabel) :=
  pairKey input.certified.moleculeGraph (armGraph (S.arm4a ℓ)) (S.rankEvidenceOf ℓ)
    S.layoutWidth S.layoutHeight (armGraph (S.arm4a ℓ)).root

/-- The independent key of ligand `ℓ`: the pair key, then the ligand signature. -/
def independentKey (ℓ : Fin 4) :
    Lex (Lex (List (Key ℤ) × Key StereoLabel) × Lex (ℕ × List (Key StereoLabel))) :=
  toLex (S.independentPairKey ℓ, toLex (S.signature ℓ))

/-! ## The Rule-4a prefix is the independent pair-key comparison -/

/-- Molecular readback of the chosen stage-`.rule4a` arm (B-chain). -/
theorem armReadback4a (ℓ : Fin 4) :
    ArmReadback (S.arm4a ℓ) (actualReferenceDescriptorMap input)
      (input.certified.topUnit S.center) :=
  armReadback_of_treeLike input _
    ((ActualReaderPhysicalBranchInverse.topTarget_root input S.c).trans S.hcenter.symm)
    (ActualReaderPhysicalBranchInverse.topTarget_address input S.c) S.singleBonded S.acyclic
    (S.arm4a ℓ)

/-- The independent Rule-4a component at the ligand root represents the arm's actual Rule-4a
column (the root case of the recursive Rule-4a bridge). -/
theorem represents4a (ℓ : Fin 4) :
    Represents4a S.layoutWidth S.layoutHeight (ofLex (S.independentPairKey ℓ)).2
      (S.arm4a ℓ).key :=
  (arm_node_bridge4a (S.arm4a ℓ) (S.armReadback4a ℓ)
    (le_layoutBound (fun ℓ => (armGraph (S.arm4a ℓ)).width) ℓ)
    (le_layoutBound (fun ℓ => (armGraph (S.arm4a ℓ)).height) ℓ)
    (armGraph (S.arm4a ℓ)).root (S.arm4a ℓ).tree (S.arm4a ℓ).key (S.arm4a ℓ).trace
    (by
      change (S.arm4a ℓ).tree.decoratedSubtreeAt? [] = some (S.arm4a ℓ).tree
      rw [LocalizedCumulativeDecoratedTree.decoratedSubtreeAt?])).2

theorem wellShaped4a (ℓ : Fin 4) :
    Certificate.CanonicalSphereKey.WellShaped S.layoutWidth S.layoutHeight
      (ofLex (S.independentPairKey ℓ)).2 :=
  ordinaryKey_stereo_wellShaped input.certified.moleculeGraph (armGraph (S.arm4a ℓ))
    (S.rankEvidenceOf ℓ) S.layoutWidth S.layoutHeight .rule4aStereogenicUnitKind
    (armGraph (S.arm4a ℓ)).root

/-- The actual constitutional comparison of two arms is the comparison of the independent
constitutional vector keys (the accepted cross-arm transfer at the common layout). -/
theorem constitutional_compare (ℓ m : Fin 4) :
    OfficialRuleMajorKey.compare (S.arm4a ℓ).key.constitutional (S.arm4a m).key.constitutional =
      compare (ofLex (S.independentPairKey ℓ)).1 (ofLex (S.independentPairKey m)).1 :=
  arm_compare_eq_compare_vector (S.arm4a ℓ) (S.arm4a m)
    (le_layoutBound (fun ℓ => (armGraph (S.arm4a ℓ)).width) ℓ)
    (le_layoutBound (fun ℓ => (armGraph (S.arm4a ℓ)).height) ℓ)
    (le_layoutBound (fun ℓ => (armGraph (S.arm4a ℓ)).width) m)
    (le_layoutBound (fun ℓ => (armGraph (S.arm4a ℓ)).height) m)

/-- After a constitutional tie, the actual Rule-4a descriptor comparison of two arms is the
comparison of the independent Rule-4a keys. -/
theorem descriptor_compare_of_tie {ℓ m : Fin 4}
    (tie : OfficialRuleMajorKey.compare (S.arm4a ℓ).key.constitutional
      (S.arm4a m).key.constitutional = .eq) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (S.arm4a ℓ).key.descriptor (S.arm4a m).key.descriptor =
      compare (ofLex (S.independentPairKey ℓ)).2 (ofLex (S.independentPairKey m)).2 := by
  have tied : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (S.arm4a ℓ).key.constitutional.rule1a (S.arm4a m).key.constitutional.rule1a = .eq := by
    have h := tie
    simp only [OfficialRuleMajorKey.compare, compareLex, Ordering.byKey, Ordering.then_eq_eq] at h
    exact h.1
  exact compare_descriptor_eq_compare_key (S.arm4a ℓ).tableMatch (S.arm4a m).tableMatch
    (S.arm4a ℓ).realizes (S.arm4a m).realizes tied (S.wellShaped4a ℓ) (S.wellShaped4a m)
    (S.represents4a ℓ) (S.represents4a m)

/-- **The Rule-4a prefix.**  The actual cumulative Rule-4a key comparison of two slots is the
independent pair-key comparison. -/
theorem cumulative_compare_eq_pairKeyCompare (ℓ m : Fin 4) :
    input.certified.compareLocalizedRerootCumulativeRule45Keys
        (S.slotKey ℓ).prior.rule4aKey (S.slotKey m).prior.rule4aKey =
      pairKeyCompare (S.independentPairKey ℓ) (S.independentPairKey m) := by
  rw [S.rule4aKey_eq (S.arm4a ℓ), S.rule4aKey_eq (S.arm4a m)]
  unfold compareLocalizedRerootCumulativeRule45Keys pairKeyCompare
  simp only [compareLex, Ordering.byKey]
  rw [S.constitutional_compare ℓ m]
  cases h : compare (ofLex (S.independentPairKey ℓ)).1 (ofLex (S.independentPairKey m)).1 with
  | lt => rfl
  | gt => rfl
  | eq =>
      simp only [Ordering.eq_then]
      exact S.descriptor_compare_of_tie ((S.constitutional_compare ℓ m).trans h)

/-! ## The hybrid comparison is the independent-key comparison -/

theorem independentCompare_eq_lt_iff (ℓ m : Fin 4) :
    S.independentCompare ℓ m = .lt ↔ S.independentKey ℓ < S.independentKey m := by
  unfold independentCompare
  rw [S.cumulative_compare_eq_pairKeyCompare]
  exact then_eq_lt_iff_lex pairKeyCompare (fun s t => signatureCompare (ofLex s) (ofLex t))
    pairKeyCompare_eq_lt_iff pairKeyCompare_eq_eq_iff signatureCompare_eq_lt_iff
    (S.independentPairKey ℓ) (S.independentPairKey m) (toLex (S.signature ℓ))
    (toLex (S.signature m))

theorem independentCompare_eq_eq_iff (ℓ m : Fin 4) :
    S.independentCompare ℓ m = .eq ↔ S.independentKey ℓ = S.independentKey m := by
  unfold independentCompare
  rw [S.cumulative_compare_eq_pairKeyCompare]
  exact then_eq_eq_iff_lex pairKeyCompare (fun s t => signatureCompare (ofLex s) (ofLex t))
    pairKeyCompare_eq_eq_iff signatureCompare_eq_eq_iff
    (S.independentPairKey ℓ) (S.independentPairKey m) (toLex (S.signature ℓ))
    (toLex (S.signature m))

/-! ## Numeric priorities from the finite key order -/

/-- The numeric priority of a ligand: the number of ligands with a strictly smaller independent
key. -/
def priority : Fin 4 → ℕ := keyRank S.independentKey

/-- Pairwise distinct independent keys. -/
def KeysSeparated : Prop := ∀ ℓ m : Fin 4, ℓ ≠ m → S.independentKey ℓ ≠ S.independentKey m

theorem independentKey_injective (separated : S.KeysSeparated) :
    Function.Injective S.independentKey := fun ℓ m h =>
  by_contra fun hne => separated ℓ m hne h

theorem priority_injective (separated : S.KeysSeparated) : Function.Injective S.priority :=
  keyRank_injective _ (S.independentKey_injective separated)

theorem priority_lt_iff (separated : S.KeysSeparated) (ℓ m : Fin 4) :
    S.priority ℓ < S.priority m ↔ S.independentKey ℓ < S.independentKey m :=
  keyRank_lt_iff _ (S.independentKey_injective separated) ℓ m

theorem priority_eq_iff (separated : S.KeysSeparated) (ℓ m : Fin 4) :
    S.priority ℓ = S.priority m ↔ S.independentKey ℓ = S.independentKey m :=
  keyRank_eq_iff _ (S.independentKey_injective separated) ℓ m

/-- **The numeric priority realizes the independent comparison.** -/
theorem compare_priority (separated : S.KeysSeparated) (ℓ m : Fin 4) :
    compare (S.priority ℓ) (S.priority m) = S.independentCompare ℓ m :=
  (eq_compare_of_iff _ _ _
    ((S.independentCompare_eq_lt_iff ℓ m).trans (S.priority_lt_iff separated ℓ m).symm)
    ((S.independentCompare_eq_eq_iff ℓ m).trans (S.priority_eq_iff separated ℓ m).symm)).symm

/-! ## The absolute letter from the independent keys -/

/-- **Absolute-letter conclusion from the independent keys.**  If the four independent keys are
pairwise distinct, the ordered evaluator's fixed point at the centre is the uppercase letter read
from the oriented volume of the canonical ligand atoms' coordinates listed in descending
independent key.  No priority, rank or comparison outcome is supplied. -/
theorem orderedReferenceState_top_eq_chiral_of_independentKeys
    (separated : S.KeysSeparated)
    (order : List (Fin 4)) (perm : order.Perm (List.finRange 4))
    (sorted : order.Pairwise fun a b => S.independentKey b < S.independentKey a)
    (points : List CartesianPoint3)
    (hpoints : order.mapM (fun ℓ => input.certified.spatialPointAt?
      (input.certified.canonicalLigandAtom S.center ℓ)) = some points)
    (raw : RS) (hraw : descriptorOfPriorityOrderedPoints? points = some raw) :
    input.certified.orderedReferenceState (LocalizedUniversalReference.carrierFuel input) S.top =
      some (.chiral raw) :=
  S.orderedReferenceState_top_eq_chiral S.priority (S.priority_injective separated)
    (fun ℓ m _ => (S.compare_priority separated ℓ m).symm) order perm
    (sorted.imp fun h => (S.priority_lt_iff separated _ _).2 h) points hpoints raw hraw

end ActualCentrePhysicalSetup

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.cumulative_compare_eq_pairKeyCompare
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.independentCompare_eq_lt_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.independentCompare_eq_eq_iff
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.compare_priority
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedReferenceState_top_eq_chiral_of_independentKeys
