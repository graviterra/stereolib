import TetraStereo.OneCenter.DeclarativeCIPRule4cReadingEvidence
import TetraStereo.OneCenter.DeclarativeCIPMultiReferenceProblem
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Independent complete alternative readings through Rule 4c.
The reference population is selected from the molecular graph, and each alternative is read
at one common layout. Alternatives are ordered by their complete Rule-4b, then Rule-4c
observations. The ligand comparison exhausts all Rule-4b readings before consulting Rule 4c.
An empty uppercase-reference population retains its genuine no-reference Rule-4c reading;
it does not erase possible lowercase descriptors. This module constructs the independent
object and proves its invariances; agreement with a runtime builder is a separate obligation. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
open Certificate.CanonicalSphereKey (Key)
noncomputable section
open scoped Classical
universe u

abbrev CompleteReadingKey := Lex (Key StereoLabel × Key StereoLabel)
abbrev CompletePriorSignature := Lex (ℕ × Lex (List (Key StereoLabel) × List (Key StereoLabel)))

section Reading
variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

/-- An independent alternative. The absent reference still carries its Rule-4c observation. -/
def completeReadingAt (W D : ℕ) (reference : Option DescriptorSense) : CompleteReadingKey :=
  match reference with
  | none => toLex ([], rule4cComponent molecule graph
      (noReferenceEvidence4c molecule descriptorMap unit graph) W D graph.root)
  | some sense => toLex (readingAt molecule descriptorMap unit graph W D sense,
      rule4cComponent molecule graph (readingEvidence4c molecule descriptorMap unit graph sense)
        W D graph.root)

/-- Complete alternatives in descending order. No identities or occurrence metadata enter
the order, and a complete tie therefore has a unique observable list. -/
def completeReadingsAt (W D : ℕ) : List CompleteReadingKey :=
  match referenceSelection molecule descriptorMap unit graph with
  | .empty => [completeReadingAt molecule descriptorMap unit graph W D none]
  | .one sense => [completeReadingAt molecule descriptorMap unit graph W D (some sense)]
  | .both =>
      let first := completeReadingAt molecule descriptorMap unit graph W D (some .senior)
      let second := completeReadingAt molecule descriptorMap unit graph W D (some .junior)
      [max first second, min first second]

/-- Count, then every Rule-4b reading, then every Rule-4c reading, in the one alternative order.
The empty reference case has no Rule-4b readings and one retained Rule-4c reading. -/
def completePriorSignatureAt (W D : ℕ) : CompletePriorSignature :=
  let selection := referenceSelection molecule descriptorMap unit graph
  let readings := completeReadingsAt molecule descriptorMap unit graph W D
  toLex (selection.countPriority, toLex
    ((if selection = .empty then [] else readings.map (fun key => (ofLex key).1)),
      readings.map (fun key => (ofLex key).2)))

theorem completeReadingsAt_length (W D : ℕ) :
    (completeReadingsAt molecule descriptorMap unit graph W D).length =
      if referenceSelection molecule descriptorMap unit graph = .both then 2 else 1 := by
  unfold completeReadingsAt
  cases referenceSelection molecule descriptorMap unit graph <;> simp

theorem completePriorSignatureAt_empty (W D : ℕ)
    (empty : referenceSelection molecule descriptorMap unit graph = .empty) :
    completePriorSignatureAt molecule descriptorMap unit graph W D =
      toLex (0, toLex ([], [rule4cComponent molecule graph
        (noReferenceEvidence4c molecule descriptorMap unit graph) W D graph.root])) := by
  simp [completePriorSignatureAt, completeReadingsAt, completeReadingAt, empty,
    ReferenceSelection.countPriority]

theorem rule4cObservation_reflect (node : graph.Node) :
    rule4cObservation molecule descriptorMap.reflect unit graph node =
      rule4cObservation molecule descriptorMap unit graph node := by
  unfold rule4cObservation
  rw [occurrenceReading_reflect]
  cases occurrenceReading molecule descriptorMap unit graph node <;>
    simp [OccurrenceReading.reflect]

theorem readingEvidence4c_reflect (sense : DescriptorSense) :
    readingEvidence4c molecule descriptorMap.reflect unit graph sense =
      readingEvidence4c molecule descriptorMap unit graph sense.mirror := by
  funext node
  simp only [readingEvidence4c, readingEvidence_reflect, rule4cObservation_reflect]

theorem noReferenceEvidence4c_reflect :
    noReferenceEvidence4c molecule descriptorMap.reflect unit graph =
      noReferenceEvidence4c molecule descriptorMap unit graph := by
  funext node
  simp only [noReferenceEvidence4c, rankEvidence_reflect, rule4cObservation_reflect]

theorem completeReadingAt_reflect (W D : ℕ) (reference : Option DescriptorSense) :
    completeReadingAt molecule descriptorMap.reflect unit graph W D reference =
      completeReadingAt molecule descriptorMap unit graph W D
        (reference.map DescriptorSense.mirror) := by
  cases reference <;>
    simp only [completeReadingAt, readingAt, rule4cComponent, readingEvidence_reflect,
      readingEvidence4c_reflect, noReferenceEvidence4c_reflect, Option.map_none, Option.map_some]

/-- Reflecting the molecular descriptor map exchanges reference senses, but leaves the
complete observable alternative list unchanged, including genuine Rule-4c observations. -/
theorem completeReadingsAt_reflect (W D : ℕ) :
    completeReadingsAt molecule descriptorMap.reflect unit graph W D =
      completeReadingsAt molecule descriptorMap unit graph W D := by
  unfold completeReadingsAt
  rw [referenceSelection_reflect]
  cases referenceSelection molecule descriptorMap unit graph with
  | empty => simp [ReferenceSelection.mirror, completeReadingAt_reflect]
  | one sense =>
      simp [ReferenceSelection.mirror, completeReadingAt_reflect]
  | both =>
      simp only [ReferenceSelection.mirror, completeReadingAt_reflect, Option.map_some,
        DescriptorSense.mirror]
      rw [max_comm, min_comm]

theorem completePriorSignatureAt_reflect (W D : ℕ) :
    completePriorSignatureAt molecule descriptorMap.reflect unit graph W D =
      completePriorSignatureAt molecule descriptorMap unit graph W D := by
  unfold completePriorSignatureAt
  simp only [referenceSelection_reflect, completeReadingsAt_reflect]
  cases referenceSelection molecule descriptorMap unit graph <;> rfl

end Reading

section Iso
variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) {left right : RootedDigraph Atom}
  (iso : RootedDigraph.Iso left right)

theorem readingEvidence4c_preserved (sense : DescriptorSense) :
    RootedDigraph.Addressing.EvidencePreserved iso
      (readingEvidence4c molecule descriptorMap unit left sense)
      (readingEvidence4c molecule descriptorMap unit right sense) := by
  intro node
  simp only [readingEvidence4c, readingEvidence_preserved molecule descriptorMap unit iso sense node,
    rule4cObservation_iso molecule descriptorMap unit iso node]

theorem noReferenceEvidence4c_preserved :
    RootedDigraph.Addressing.EvidencePreserved iso
      (noReferenceEvidence4c molecule descriptorMap unit left)
      (noReferenceEvidence4c molecule descriptorMap unit right) := by
  intro node
  simp only [noReferenceEvidence4c, rankEvidence_preserved molecule descriptorMap unit iso node,
    rule4cObservation_iso molecule descriptorMap unit iso node]

include iso in
theorem completeReadingAt_iso (W D : ℕ) (reference : Option DescriptorSense) :
    completeReadingAt molecule descriptorMap unit right W D reference =
      completeReadingAt molecule descriptorMap unit left W D reference := by
  have fourC : ∀ reference : Option DescriptorSense,
      rule4cComponent molecule right
          (match reference with
            | none => noReferenceEvidence4c molecule descriptorMap unit right
            | some sense => readingEvidence4c molecule descriptorMap unit right sense)
          W D right.root =
        rule4cComponent molecule left
          (match reference with
            | none => noReferenceEvidence4c molecule descriptorMap unit left
            | some sense => readingEvidence4c molecule descriptorMap unit left sense)
          W D left.root := by
    intro reference
    unfold rule4cComponent
    rw [← iso.map_root]
    cases reference with
    | none => rw [ordinaryKey_iso molecule iso
        (noReferenceEvidence4c_preserved molecule descriptorMap unit iso)]
    | some sense => rw [ordinaryKey_iso molecule iso
        (readingEvidence4c_preserved molecule descriptorMap unit iso sense)]
  cases reference with
  | none => exact congrArg (fun key => toLex ([], key)) (fourC none)
  | some sense =>
      simp only [completeReadingAt, readingAt_iso molecule descriptorMap unit iso W D sense,
        fourC (some sense)]

include iso in
theorem completeReadingsAt_iso (W D : ℕ) :
    completeReadingsAt molecule descriptorMap unit right W D =
      completeReadingsAt molecule descriptorMap unit left W D := by
  unfold completeReadingsAt
  rw [referenceSelection_iso molecule descriptorMap unit iso]
  simp only [completeReadingAt_iso molecule descriptorMap unit iso]

include iso in
theorem completePriorSignatureAt_iso (W D : ℕ) :
    completePriorSignatureAt molecule descriptorMap unit right W D =
      completePriorSignatureAt molecule descriptorMap unit left W D := by
  unfold completePriorSignatureAt
  rw [referenceSelection_iso molecule descriptorMap unit iso,
    completeReadingsAt_iso molecule descriptorMap unit iso]

end Iso

section Faithful
variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (externalParent ligand : Atom)
  {left right : RootedDigraph Atom}
  (faithfulL : RootedDigraph.FaithfulExactExpansion molecule externalParent ligand left)
  (faithfulR : RootedDigraph.FaithfulExactExpansion molecule externalParent ligand right)

include faithfulL faithfulR in
theorem completeReadingAt_eq_of_faithful (W D : ℕ) (reference : Option DescriptorSense) :
    completeReadingAt molecule descriptorMap unit left W D reference =
      completeReadingAt molecule descriptorMap unit right W D reference := by
  obtain ⟨iso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso
    molecule externalParent ligand left right faithfulL faithfulR
  exact (completeReadingAt_iso molecule descriptorMap unit iso W D reference).symm

include faithfulL faithfulR in
theorem completePriorSignatureAt_eq_of_faithful (W D : ℕ) :
    completePriorSignatureAt molecule descriptorMap unit left W D =
      completePriorSignatureAt molecule descriptorMap unit right W D := by
  obtain ⟨iso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso
    molecule externalParent ligand left right faithfulL faithfulR
  exact (completePriorSignatureAt_iso molecule descriptorMap unit iso W D).symm

end Faithful
end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeReadingsAt_length
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completePriorSignatureAt_empty
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule4cObservation_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.readingEvidence4c_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.noReferenceEvidence4c_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeReadingAt_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeReadingsAt_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completePriorSignatureAt_reflect
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.readingEvidence4c_preserved
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.noReferenceEvidence4c_preserved
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeReadingAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeReadingsAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completePriorSignatureAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completeReadingAt_eq_of_faithful
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.completePriorSignatureAt_eq_of_faithful
