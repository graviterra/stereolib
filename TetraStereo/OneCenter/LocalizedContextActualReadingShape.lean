import TetraStereo.OneCenter.LocalizedContextCompoundReadback
import TetraStereo.OneCenter.LocalizedContextCompoundRule5Readback
import TetraStereo.OneCenter.LocalizedRuleMajorActualReadingShape
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The actual selector, prior-reading list, and Rule-5 lifts determine the complete legal
reading shape at an arbitrary context cursor. No reference population or tag ordering is supplied. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP Rule4aTableBridge LocalizedCumulativeDecoratedTree
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
  {cursor : input.LocalizedRerootCursor carrierFuel}

private theorem contextSelectorShape
    (labels : List (List (OfficialSparseEntry (Option LocalizedAuxiliaryLabel)))) :
    localizedRule4bReferencesFromRankedLabels labels = [] ∨
      localizedRule4bReferencesFromRankedLabels labels = [.R] ∨
      localizedRule4bReferencesFromRankedLabels labels = [.S] ∨
      localizedRule4bReferencesFromRankedLabels labels = [.R, .S] := by
  rcases localizedRule4bReferencesFromRankedLabels_shape labels with referencesNil |
      ⟨reference, referencesOne⟩ | referencesBoth
  · exact Or.inl referencesNil
  · cases reference with
    | R => exact Or.inr (Or.inl referencesOne)
    | S => exact Or.inr (Or.inr (Or.inl referencesOne))
  · exact Or.inr (Or.inr (Or.inr referencesBoth))

/-- A successful uniform compound build from the actual context stages has one of the five
legal reference tag/count shapes. The Rule-5 list is the exact lift of the retained prior list.
The selector's empty, singleton, and paired outputs and the actual two-element sorter supply all
shape cases; none is a caller premise. -/
theorem contextStages_compound_rule5ReadingShape
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.buildRuleMajorCumulativeWithRead? stage read
        (2 * (carrierFuel + 1)) position) cursor = some compound) :
    input.RuleMajorReadingShape compound := by
  obtain ⟨_aEq, referencesEq, countEq, readingsEq⟩ :=
    input.contextStages_compound_readback stages built
  have rule5Eq := input.contextStages_compound_rule5Readings_eq_map stages built
  rcases contextSelectorShape stages.a.key.rankedLabels with
    referencesNil | referencesR | referencesS | referencesBoth
  · have count : compound.prior.referenceCountPriority = 0 := by
      rw [countEq, referencesEq, referencesNil]
      rfl
    have tags : compound.prior.readings.map (fun reading => reading.reference?) = [none] := by
      rw [readingsEq, referencesEq, referencesNil]
      simp [localizedRule4bcReferenceAlternatives, contextStageReading, rankReadings]
    exact ⟨Or.inl ⟨count, tags⟩, rule5Eq⟩
  · have count : compound.prior.referenceCountPriority = 2 := by
      rw [countEq, referencesEq, referencesR]
      rfl
    have tags : compound.prior.readings.map (fun reading => reading.reference?) = [some .R] := by
      rw [readingsEq, referencesEq, referencesR]
      simp [localizedRule4bcReferenceAlternatives, contextStageReading, rankReadings]
    exact ⟨Or.inr (Or.inl ⟨count, tags⟩), rule5Eq⟩
  · have count : compound.prior.referenceCountPriority = 2 := by
      rw [countEq, referencesEq, referencesS]
      rfl
    have tags : compound.prior.readings.map (fun reading => reading.reference?) = [some .S] := by
      rw [readingsEq, referencesEq, referencesS]
      simp [localizedRule4bcReferenceAlternatives, contextStageReading, rankReadings]
    exact ⟨Or.inr (Or.inr (Or.inl ⟨count, tags⟩)), rule5Eq⟩
  · have count : compound.prior.referenceCountPriority = 1 := by
      rw [countEq, referencesEq, referencesBoth]
      rfl
    have tags :
        compound.prior.readings.map (fun reading => reading.reference?) = [some .R, some .S] ∨
        compound.prior.readings.map (fun reading => reading.reference?) = [some .S, some .R] := by
      rw [readingsEq, referencesEq, referencesBoth]
      simp only [localizedRule4bcReferenceAlternatives, rankReadings,
        List.map_cons, List.map_nil]
      split_ifs <;> simp [contextStageReading]
    rcases tags with tagsRS | tagsSR
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inl ⟨count, tagsRS⟩))), rule5Eq⟩
    · exact ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨count, tagsSR⟩))), rule5Eq⟩

/-- Every generated executable child has a successful actual compound whose reading list has
the derived legal shape, including the no-reference lowercase Rule-4c case. -/
theorem exists_generatedContextCompound_rule5ReadingShape
    (input : LocalizedRuleMajorReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (target : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.occurrence.1 = unit.1)
    (cursor : input.certified.LocalizedRerootCursor
      (input.certified.certified.input.molecule.atomCount + 1))
    (rootChild : cursor ∈ input.certified.executableLocalizedRerootChildren target) :
    ∃ compound : input.certified.LocalizedRerootCompoundRule45Key,
      input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursor = some compound ∧
      input.certified.RuleMajorReadingShape compound := by
  let view := input.certified.localizedDependencyView
    (LocalizedRuleMajorReference.referenceState input) target.occurrence
  let read := input.certified.localizedDependencyLabel target.occurrence view
  obtain ⟨stages, compound, built, _aEq, _references, _count, _readings⟩ :=
    exists_generatedContextStages_compound_readback input
      singleBonded acyclic target unit targetUnit cursor rootChild
  let fuel := 2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)
  have uniformBuilt : input.certified.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position =>
        input.certified.buildRuleMajorCumulativeWithRead? stage read fuel position)
      cursor = some compound := by
    rw [← input.certified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact built
  refine ⟨compound, built, ?_⟩
  exact input.certified.contextStages_compound_rule5ReadingShape stages uniformBuilt

end
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.contextStages_compound_rule5ReadingShape
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_generatedContextCompound_rule5ReadingShape
