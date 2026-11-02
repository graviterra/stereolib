import TetraStereo.OneCenter.LocalizedRule3DoubleBondEdgeDecidable
import TetraStereo.OneCenter.LocalizedRerootDescriptorBearingRule3Key

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Executable base reader of the descriptor-bearing Rule-3 recursion

`localizedDescriptorBearingRule3StructuralNode?` is the index-zero structural reader of
`LocalizedRerootDescriptorBearingRule3Key`: it returns `some none` exactly at proved structural
nonunits, and refuses (`none`) at a genuine real order-two parent/current edge.  Its definition ran
under `classical`.

This module supplies the executable replacement:

* `localizedRule3StructuralNodeExec` is a plain definition whose only decision is the executable
  edge test of `LocalizedRule3DoubleBondEdgeDecidable` — no `Classical.propDecidable` occurs in it;
* `localizedRule3StructuralNodeExec_eq_none_iff` and
  `localizedRule3StructuralNodeExec_eq_some_none_iff` restate the two possible outcomes directly in
  terms of the structural edge proposition; and
* `localizedDescriptorBearingRule3StructuralNode?_eq_localizedRule3StructuralNodeExec` proves the
  executable reader extensionally equal to the original classical reader at every occurrence, so
  the replacement changes no result anywhere in the recursion.
-/

namespace CertifiedLocalizedCIPInput

/-- Executable base reader: a real order-two parent/current edge is refused; every other occurrence
is a skippable structural nonunit. -/
def localizedRule3StructuralNodeExec (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    Option (Option input.LocalizedRule3SpatialNodeResult) :=
  if input.localizedRule3DoubleBondEdgeExec occurrence = true then none else some none

/-- The executable base reader refuses exactly at real order-two parent/current edges. -/
theorem localizedRule3StructuralNodeExec_eq_none_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.localizedRule3StructuralNodeExec occurrence = none ↔
      input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
  unfold localizedRule3StructuralNodeExec
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  · rw [if_pos ((input.localizedRule3DoubleBondEdgeExec_eq_true_iff occurrence).mpr edge)]
    exact ⟨fun _ => edge, fun _ => rfl⟩
  · rw [if_neg (fun isTrue =>
      edge ((input.localizedRule3DoubleBondEdgeExec_eq_true_iff occurrence).mp isTrue))]
    constructor
    · intro impossible
      cases impossible
    · intro positive
      exact absurd positive edge

/-- The executable base reader skips exactly the occurrences that are not real order-two
parent/current edges. -/
theorem localizedRule3StructuralNodeExec_eq_some_none_iff
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.localizedRule3StructuralNodeExec occurrence = some none ↔
      ¬ input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence := by
  unfold localizedRule3StructuralNodeExec
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  · rw [if_pos ((input.localizedRule3DoubleBondEdgeExec_eq_true_iff occurrence).mpr edge)]
    constructor
    · intro impossible
      cases impossible
    · intro noEdge
      exact absurd edge noEdge
  · rw [if_neg (fun isTrue =>
      edge ((input.localizedRule3DoubleBondEdgeExec_eq_true_iff occurrence).mp isTrue))]
    exact ⟨fun _ => edge, fun _ => rfl⟩

/-- The executable base reader and the original classical base reader agree at every occurrence of
every carrier fuel. -/
theorem localizedDescriptorBearingRule3StructuralNode?_eq_localizedRule3StructuralNodeExec
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    input.localizedDescriptorBearingRule3StructuralNode? occurrence =
      input.localizedRule3StructuralNodeExec occurrence := by
  unfold localizedDescriptorBearingRule3StructuralNode? localizedRule3StructuralNodeExec
  by_cases edge : input.LocalizedOccurrenceHasRule3DoubleBondEdge occurrence
  · rw [if_pos edge,
      if_pos ((input.localizedRule3DoubleBondEdgeExec_eq_true_iff occurrence).mpr edge)]
  · rw [if_neg edge, if_neg (fun isTrue =>
      edge ((input.localizedRule3DoubleBondEdgeExec_eq_true_iff occurrence).mp isTrue))]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
