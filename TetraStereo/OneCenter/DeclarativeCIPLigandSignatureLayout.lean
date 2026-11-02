import TetraStereo.OneCenter.DeclarativeCIPMolecularReferenceSelection
import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidenceNaturality
import TetraStereo.OneCenter.DeclarativeCIPFaithfulExpansionBisimulation
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The ligand-level Rule-4b signature at a shared layout

`ligandSignature` (`DeclarativeCIPMolecularReferenceSelection`) lays each complete reading out at
the ligand graph's own `width`/`height`.  Two ligands of one centre have different graphs, so a
comparison of their signatures is only meaningful at a layout that bounds both.  This module adds
the layout-parametrised form and proves it is the same object:

* `readingAt W D reference` — the Rule-4b hierarchy component of the ligand root's ordinary key
  at layout `(W, D)`; `reading = readingAt width height` definitionally;
* `descendingPair` — the two complete readings of a tied population, better reading first, by the
  key comparator; it is `[max, min]` for the key order (`descendingPair_eq_max_min`);
* `ligandSignatureAt W D` — count, then the readings at layout `(W, D)`;
  `ligandSignatureAt width height = ligandSignature`;
* `signatureCompare` — the lexicographic comparator the outcome relation `LigandSignatureOutcome`
  unfolds to (`ligandSignatureOutcome_iff`).

Expansion independence: `readingAt`, `width` and `height` are invariant under rooted-digraph
isomorphisms that are the identity on atoms (`readingAt_iso`), hence equal for any two faithful
exact expansions of the same molecular branch (`readingAt_eq_of_faithful`).

The key comparator `compare` on `Key StereoLabel` is the list comparator `List.compareLex`
(instance `List.instOrd`), while `max`/`min` come from the lexicographic linear order; the bridge
`key_compare_lt_iff`/`key_compare_eq_iff` identifies the two.
-/

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

open Certificate.CanonicalSphereKey (Key Level)
open RootedDigraph

noncomputable section
open scoped Classical

universe u

/-! ## The list comparator against the lexicographic order -/

section ListCompare

variable {α : Type*} [LinearOrder α]

omit [LinearOrder α] in
theorem compareLex_eq_eq_iff_of (cmp : α → α → Ordering)
    (heq : ∀ a b, cmp a b = .eq ↔ a = b) :
    ∀ l₁ l₂ : List α, List.compareLex cmp l₁ l₂ = .eq ↔ l₁ = l₂
  | [], [] => by simp [List.compareLex]
  | [], _ :: _ => by simp [List.compareLex]
  | _ :: _, [] => by simp [List.compareLex]
  | a :: l₁, b :: l₂ => by
      rw [List.compareLex_cons_cons]
      cases h : cmp a b with
      | lt =>
          have hne : a ≠ b := fun hab => by rw [← heq] at hab; simp [h] at hab
          simp [Ordering.then, hne]
      | eq =>
          have hab := (heq a b).1 h
          subst hab
          simp [Ordering.then, compareLex_eq_eq_iff_of cmp heq l₁ l₂]
      | gt =>
          have hne : a ≠ b := fun hab => by rw [← heq] at hab; simp [h] at hab
          simp [Ordering.then, hne]

theorem compareLex_eq_lt_iff_of (cmp : α → α → Ordering)
    (hlt : ∀ a b, cmp a b = .lt ↔ a < b) (heq : ∀ a b, cmp a b = .eq ↔ a = b) :
    ∀ l₁ l₂ : List α, List.compareLex cmp l₁ l₂ = .lt ↔ List.Lex (· < ·) l₁ l₂
  | [], [] => by simp [List.compareLex]
  | [], _ :: _ => by simp [List.compareLex]
  | _ :: _, [] => by simp [List.compareLex]
  | a :: l₁, b :: l₂ => by
      rw [List.compareLex_cons_cons, List.cons_lex_cons_iff]
      cases h : cmp a b with
      | lt => simp [Ordering.then, (hlt a b).1 h]
      | eq =>
          have hab := (heq a b).1 h
          subst hab
          simp [Ordering.then, compareLex_eq_lt_iff_of cmp hlt heq l₁ l₂]
      | gt =>
          have hnlt : ¬ a < b := fun hab => by rw [← hlt] at hab; simp [h] at hab
          have hne : a ≠ b := fun hab => by rw [← heq] at hab; simp [h] at hab
          simp [Ordering.then, hnlt, hne]

theorem level_compare_eq_iff (l₁ l₂ : Level α) : compare l₁ l₂ = .eq ↔ l₁ = l₂ :=
  compareLex_eq_eq_iff_of compare (fun _ _ => compare_eq_iff_eq) l₁ l₂

theorem level_compare_lt_iff (l₁ l₂ : Level α) : compare l₁ l₂ = .lt ↔ l₁ < l₂ :=
  compareLex_eq_lt_iff_of compare (fun _ _ => compare_lt_iff_lt) (fun _ _ => compare_eq_iff_eq)
    l₁ l₂

theorem key_compare_eq_iff (k₁ k₂ : Key α) : compare k₁ k₂ = .eq ↔ k₁ = k₂ :=
  compareLex_eq_eq_iff_of compare level_compare_eq_iff k₁ k₂

theorem key_compare_lt_iff (k₁ k₂ : Key α) : compare k₁ k₂ = .lt ↔ k₁ < k₂ :=
  compareLex_eq_lt_iff_of compare level_compare_lt_iff level_compare_eq_iff k₁ k₂

end ListCompare

/-! ## The signature at a shared layout -/

section Layout

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

/-- The complete reading under one reference at layout `(W, D)`. -/
def readingAt (W D : ℕ) (reference : DescriptorSense) : Key StereoLabel :=
  ((ofLex (ordinaryKey molecule graph (readingEvidence molecule descriptorMap unit graph reference)
      W D graph.root)).2).getD
    (stereoIndex .rule4bLikeUnlikeDescriptorPairs) []

theorem reading_eq_readingAt (reference : DescriptorSense) :
    reading molecule descriptorMap unit graph reference =
      readingAt molecule descriptorMap unit graph graph.width graph.height reference := rfl

/-- Two complete readings, better reading first (the key comparator). -/
def descendingPair (first second : Key StereoLabel) : List (Key StereoLabel) :=
  if compare first second = .lt then [second, first] else [first, second]

theorem descendingPair_eq_max_min (first second : Key StereoLabel) :
    descendingPair first second = [max first second, min first second] := by
  unfold descendingPair
  split_ifs with h
  · rw [key_compare_lt_iff] at h
    rw [max_eq_right h.le, min_eq_left h.le]
  · rw [key_compare_lt_iff, not_lt] at h
    rw [max_eq_left h, min_eq_right h]

/-- The ligand signature at layout `(W, D)`: the criterion-(c)(i) count, then the complete
readings in descending order. -/
def ligandSignatureAt (W D : ℕ) : ℕ × List (Key StereoLabel) :=
  match referenceSelection molecule descriptorMap unit graph with
  | .empty => (0, [])
  | .one reference => (2, [readingAt molecule descriptorMap unit graph W D reference])
  | .both =>
      (1, descendingPair (readingAt molecule descriptorMap unit graph W D .senior)
        (readingAt molecule descriptorMap unit graph W D .junior))

/-- At the graph's own layout the layout-parametrised signature is the original one. -/
theorem ligandSignatureAt_layout :
    ligandSignatureAt molecule descriptorMap unit graph graph.width graph.height =
      ligandSignature molecule descriptorMap unit graph := by
  unfold ligandSignatureAt ligandSignature
  cases referenceSelection molecule descriptorMap unit graph with
  | empty => rfl
  | one reference => rfl
  | both => rw [descendingPair_eq_max_min]; rfl

/-- The signature comparator: count, then the readings lexicographically. -/
def signatureCompare (left right : ℕ × List (Key StereoLabel)) : Ordering :=
  (compare left.1 right.1).then (List.compareLex compare left.2 right.2)

theorem ligandSignatureOutcome_iff (left right : ℕ × List (Key StereoLabel)) (outcome : Ordering) :
    LigandSignatureOutcome left right outcome ↔ signatureCompare left right = outcome :=
  Iff.rfl

end Layout

/-! ## Expansion independence -/

section Iso

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) {left right : RootedDigraph Atom}
  (iso : RootedDigraph.Iso left right)

local instance layoutNodeFintype (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

theorem readingEvidence_preserved (reference : DescriptorSense) :
    RootedDigraph.Addressing.EvidencePreserved iso
      (readingEvidence molecule descriptorMap unit left reference)
      (readingEvidence molecule descriptorMap unit right reference) := by
  intro node
  simp only [readingEvidence]
  rw [rule3Observation_iso molecule descriptorMap unit iso node,
    rule4aObservation_iso molecule descriptorMap unit iso node,
    eligibleSense_iso molecule descriptorMap unit iso node]

include iso in
theorem readingAt_iso (W D : ℕ) (reference : DescriptorSense) :
    readingAt molecule descriptorMap unit right W D reference =
      readingAt molecule descriptorMap unit left W D reference := by
  unfold readingAt
  rw [← iso.map_root,
    ordinaryKey_iso molecule iso (readingEvidence_preserved molecule descriptorMap unit iso reference)
      W D left.root]

omit [Fintype Atom] [DecidableEq Atom] in
include iso in
theorem width_iso : right.width = left.width :=
  Fintype.card_congr iso.toEquiv.symm

omit [Fintype Atom] [DecidableEq Atom] in
include iso in
theorem height_iso : right.height = left.height := by
  unfold RootedDigraph.height
  apply le_antisymm
  · refine Finset.sup_le fun node _ => ?_
    rw [← iso.toEquiv.apply_symm_apply node, ← iso.map_depth]
    exact Finset.le_sup (f := left.depth) (Finset.mem_univ _)
  · refine Finset.sup_le fun node _ => ?_
    rw [iso.map_depth]
    exact Finset.le_sup (f := right.depth) (Finset.mem_univ _)

end Iso

section Faithful

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (externalParent ligand : Atom)
  {first second : RootedDigraph Atom}
  (hfirst : RootedDigraph.FaithfulExactExpansion molecule externalParent ligand first)
  (hsecond : RootedDigraph.FaithfulExactExpansion molecule externalParent ligand second)

include hfirst hsecond in
/-- Any two faithful exact expansions of one molecular branch give the same complete readings at
every layout. -/
theorem readingAt_eq_of_faithful (W D : ℕ) (reference : DescriptorSense) :
    readingAt molecule descriptorMap unit first W D reference =
      readingAt molecule descriptorMap unit second W D reference := by
  obtain ⟨iso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso molecule externalParent
    ligand first second hfirst hsecond
  exact (readingAt_iso molecule descriptorMap unit iso W D reference).symm

include hfirst hsecond in
theorem width_eq_of_faithful : first.width = second.width := by
  obtain ⟨iso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso molecule externalParent
    ligand first second hfirst hsecond
  exact (width_iso iso).symm

include hfirst hsecond in
theorem height_eq_of_faithful : first.height = second.height := by
  obtain ⟨iso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso molecule externalParent
    ligand first second hfirst hsecond
  exact (height_iso iso).symm

end Faithful

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.key_compare_lt_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.key_compare_eq_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.descendingPair_eq_max_min
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ligandSignatureAt_layout
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ligandSignatureOutcome_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.readingAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.readingAt_eq_of_faithful
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.width_eq_of_faithful
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.height_eq_of_faithful
