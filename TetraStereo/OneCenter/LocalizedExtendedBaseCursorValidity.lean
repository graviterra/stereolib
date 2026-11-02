import TetraStereo.OneCenter.LocalizedNoDoubleWithChildren
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Independently meaningful four-ligand bases contain only valid zipper cursors. -/
theorem DeclarativeLocalizedOccurrenceFourLigandFrame.cursors_valid
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {target : input.LocalizedCIPOccurrence carrierFuel}
    {base : input.LocalizedOccurrenceFourLigandFrame carrierFuel}
    (derived : input.DeclarativeLocalizedOccurrenceFourLigandFrame target base) :
    ∀ cursor ∈ base.cursors, input.LocalizedRerootCursorValid cursor := by
  intro cursor present
  exact input.localizedRerootChild_valid { occurrence := target, previous? := none }
    cursor base.cursors derived.1 present

/-- Successful executable base construction supplies the validity needed by structural fuel bounds. -/
theorem localizedNoDoubleFourLigandFrameExec?_cursors_valid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedNoDoubleFourLigandFrameExec? target = some base) :
    ∀ cursor ∈ base.cursors, input.LocalizedRerootCursorValid cursor := by
  rw [localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?] at computed
  exact (input.localizedOccurrenceFourLigandFrame?_sound target base computed).cursors_valid

namespace WithChildren

/-- Exact materialized child readers preserve the base-cursor validity certificate. -/
theorem localizedNoDoubleFourLigandFrameExec?_cursors_valid
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (readChildren : input.LocalizedRerootCursor carrierFuel →
      Option (List (input.LocalizedRerootCursor carrierFuel)))
    (readEq : ∀ cursor, readChildren cursor = input.executableLocalizedRerootChildren? cursor)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (base : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : localizedNoDoubleFourLigandFrameExec? input readChildren target = some base) :
    ∀ cursor ∈ base.cursors, input.LocalizedRerootCursorValid cursor := by
  rw [localizedNoDoubleFourLigandFrameExec?_eq_original input readChildren readEq] at computed
  exact input.localizedNoDoubleFourLigandFrameExec?_cursors_valid target base computed

end WithChildren

/-- The linear two-pass structural budget never exceeds the existing production budget. -/
theorem localizedExtendedLinearFuel_le_production (carrierFuel : Nat) :
    2 * (carrierFuel + 1) + 2 ≤ localizedDescriptorBearingRule3EvaluationFuel carrierFuel := by
  unfold localizedDescriptorBearingRule3EvaluationFuel
  nlinarith

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
