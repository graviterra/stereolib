import TetraStereo.OneCenter.AuthoritativeCIPGraph
import TetraStereo.OneCenter.AuthoritativeChemicalInput

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput
namespace SingleWedgeSource

theorem wedge_semanticEdgeKey_eq_iff (left right first second : Nat) :
    semanticEdgeKey left right = semanticEdgeKey first second ↔
      (left = first ∧ right = second) ∨ (left = second ∧ right = first) := by
  simp only [semanticEdgeKey]
  by_cases lr : left ≤ right <;> by_cases fs : first ≤ second <;>
    simp [Nat.min_def, Nat.max_def, lr, fs] <;> omega

/-- Decode a real record, without requiring that all interactions be localized pairs. -/
theorem wedge_localized_record_endpoints (interaction : SemanticInteraction)
    (key : Nat × Nat) (order : Nat)
    (recorded : interaction.localizedCovalentRecord? = some (key, order)) :
    ∃ first second, interaction.participants = [first, second] ∧
      interaction.kind = .covalent order ∧ key = semanticEdgeKey first second := by
  rcases interaction with ⟨participants, kind⟩
  rcases participants with _ | ⟨first, participants⟩
  · simp [SemanticInteraction.localizedCovalentRecord?] at recorded
  rcases participants with _ | ⟨second, participants⟩
  · simp [SemanticInteraction.localizedCovalentRecord?] at recorded
  rcases participants with _ | ⟨third, rest⟩
  · cases kind with
    | covalent bondOrder =>
        change (if 0 < bondOrder then
          some (semanticEdgeKey first second, bondOrder) else none) = some (key, order)
          at recorded
        split at recorded
        · simp only [Option.some.injEq, Prod.mk.injEq] at recorded
          rcases recorded with ⟨rfl, rfl⟩
          exact ⟨first, second, rfl, rfl, rfl⟩
        · simp at recorded
    | _ => simp [SemanticInteraction.localizedCovalentRecord?] at recorded
  · simp [SemanticInteraction.localizedCovalentRecord?] at recorded

end SingleWedgeSource
end AuthoritativeChemicalInput
end TetraStereo.OneCenter
