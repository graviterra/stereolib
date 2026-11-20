import TetraStereo.OneCenter.LocalizedRuleMajorCompoundReadback
import TetraStereo.KernelOnly
set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

theorem buildRuleMajorCompoundRule45KeyWith?_singleton_readback
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (compileStage : input.RuleMajorCompoundStageCompiler carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (compound : input.LocalizedRerootCompoundRule45Key) (own : RS)
    (built : input.buildRuleMajorCompoundRule45KeyWith? compileStage cursor = some compound)
    (selected : localizedRule4bReferencesFromRankedLabels
      compound.prior.rule4aKey.rankedLabels = [own]) :
    ∃ reading, compound.rule5Readings = [reading] ∧
      reading.prior.reference? = some own ∧
      compileStage (localizedRule5StageFor (some own) .R) cursor = some reading.commonR ∧
      compileStage (localizedRule5StageFor (some own) .S) cursor = some reading.commonS := by
  obtain ⟨_, references, _, raw, rawBuilt, ranked, rule5Built⟩ :=
    input.buildRuleMajorCompoundRule45KeyWith?_readback compileStage cursor built
  have refs : compound.prior.references = [own] := references.trans selected
  rw [refs] at rawBuilt
  change (do
    let prior ← input.buildRuleMajorCompoundRule4bcReadingWith? compileStage cursor (some own)
    some [prior]) = some raw at rawBuilt
  obtain ⟨prior, priorBuilt, rawEq⟩ := Option.bind_eq_some_iff.mp rawBuilt
  have rawSingleton : raw = [prior] := (Option.some.inj rawEq).symm
  have priorSingleton : compound.prior.readings = [prior] := by
    rw [ranked, rawSingleton]
    rfl
  obtain ⟨_, _, _, _, priorReference, _, _⟩ :=
    (input.buildRuleMajorCompoundRule4bcReadingWith?_eq_some_iff_stageBuilds
      compileStage cursor (some own) prior).mp priorBuilt
  rw [priorSingleton] at rule5Built
  change (do
    let reading ← input.buildRuleMajorCompoundRule5ReadingWith? compileStage cursor prior
    some [reading]) = some compound.rule5Readings at rule5Built
  obtain ⟨reading, readingBuilt, readingsEq⟩ := Option.bind_eq_some_iff.mp rule5Built
  have singleton : compound.rule5Readings = [reading] := (Option.some.inj readingsEq).symm
  unfold buildRuleMajorCompoundRule5ReadingWith? at readingBuilt
  obtain ⟨commonR, commonRBuilt, tail⟩ := Option.bind_eq_some_iff.mp readingBuilt
  obtain ⟨commonS, commonSBuilt, result⟩ := Option.bind_eq_some_iff.mp tail
  have readingEq : reading = { prior := prior, commonR := commonR, commonS := commonS } :=
    (Option.some.inj result).symm
  refine ⟨reading, singleton, ?_, ?_, ?_⟩
  · simpa only [readingEq] using priorReference
  · simpa only [readingEq, priorReference] using commonRBuilt
  · simpa only [readingEq, priorReference] using commonSBuilt

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule45KeyWith?_singleton_readback
