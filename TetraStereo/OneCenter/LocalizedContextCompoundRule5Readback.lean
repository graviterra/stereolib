import TetraStereo.OneCenter.LocalizedContextCompoundReadback
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundRule5Readback
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Exact contextual Rule-5 readback from an actual successful compound build. The staged
Rule-4b/4c alternatives determine the prior reading records, and the two Rule-5 keys are the
corresponding lifts. Empty-reference lift behavior is obtained from the actual alternative list. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP Rule4aTableBridge LocalizedCumulativeDecoratedTree
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
  {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
  {cursor : input.LocalizedRerootCursor carrierFuel}

private def contextRuleMajorCompiler (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) : input.RuleMajorCompoundStageCompiler carrierFuel :=
  fun stage position => input.buildRuleMajorCumulativeWithRead? stage read fuel position

private theorem mem_contextRankReadings
    {prior : input.LocalizedRerootRule4bcReading}
    {readings : List input.LocalizedRerootRule4bcReading}
    (present : prior ∈ input.rankReadings readings) : prior ∈ readings := by
  unfold rankReadings at present
  split at present
  · split_ifs at present <;> simp at present ⊢ <;> tauto
  · exact present

private theorem contextRule5ReadingWith?_eq_expected
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (prior : input.LocalizedRerootRule4bcReading)
    (selectorEmpty : prior.reference? = none →
      localizedRule4bReferencesFromRankedLabels stages.a.key.rankedLabels = [])
    (inPrior : prior.reference? = none →
      prior.rule4bKey = stages.a.key ∧ prior.rule4cKey = stages.noReference.key)
    (selectedPrior : ∀ reference, prior.reference? = some reference →
      prior.rule4bKey = (stages.b reference).key ∧
        prior.rule4cKey = (stages.c reference).key) :
    input.buildRuleMajorCompoundRule5ReadingWith?
        (contextRuleMajorCompiler input read (2 * (carrierFuel + 1))) cursor prior =
      some (input.ruleMajorExpectedRule5Reading prior) := by
  let fuel := 2 * (carrierFuel + 1)
  cases hreference : prior.reference? with
  | none =>
      have hprior := inPrior hreference
      have hRule4a : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
          read fuel cursor = some stages.a.key := by
        rw [← input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized read fuel cursor]
        simpa [fuel] using stages.a.built
      have hNoReference : input.buildRuleMajorCumulativeWithRead? .rule4cNoReference
          read fuel cursor = some stages.noReference.key := by
        simpa [fuel] using stages.noReference.built
      have hRule5 := input.buildRuleMajorCumulativeWithRead?_rule5NoReference_of_rule4aSelection_eq_nil
        .R read fuel cursor stages.a.key hRule4a (selectorEmpty hreference)
        stages.noReference.key hNoReference
      have hRule5S := input.buildRuleMajorCumulativeWithRead?_rule5NoReference_of_rule4aSelection_eq_nil
        .S read fuel cursor stages.a.key hRule4a (selectorEmpty hreference)
        stages.noReference.key hNoReference
      have hR : contextRuleMajorCompiler input read (2 * (carrierFuel + 1))
          (localizedRule5StageFor none .R) cursor =
          some (input.rule5LiftKey false prior.rule4cKey) := by
        change input.buildRuleMajorCumulativeWithRead? (.rule5NoRule4bReference .R)
          read fuel cursor = _
        rw [hRule5, hprior.2]
      have hS : contextRuleMajorCompiler input read (2 * (carrierFuel + 1))
          (localizedRule5StageFor none .S) cursor =
          some (input.rule5LiftKey false prior.rule4cKey) := by
        change input.buildRuleMajorCumulativeWithRead? (.rule5NoRule4bReference .S)
          read fuel cursor = _
        rw [hRule5S, hprior.2]
      unfold buildRuleMajorCompoundRule5ReadingWith?
      rw [hreference, hR, hS]
      simp [hreference, ruleMajorExpectedRule5Reading]
  | some reference =>
      have hprior := selectedPrior reference hreference
      have hCommon (common : RS) :
          contextRuleMajorCompiler input read (2 * (carrierFuel + 1))
            (localizedRule5StageFor (some reference) common) cursor =
            some (input.rule5LiftKey (common == reference) prior.rule4cKey) := by
        have hRule4c : input.buildRuleMajorCumulativeWithRead? (.rule4c reference)
            read fuel cursor = some (stages.c reference).key := by
          simpa [fuel] using (stages.c reference).built
        have hRule5 := input.buildRuleMajorCumulativeWithRead?_rule5 reference common
          read fuel cursor
        change input.buildRuleMajorCumulativeWithRead? (.rule5 reference common) read fuel cursor = _
          at hRule5
        rw [hRule4c] at hRule5
        simpa [hprior.2] using hRule5
      unfold buildRuleMajorCompoundRule5ReadingWith?
      rw [hreference, hCommon .R, hCommon .S]
      simp [hreference, ruleMajorExpectedRule5Reading]

private theorem contextRule5ReadingsWith?_eq_map
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    (priors : List input.LocalizedRerootRule4bcReading)
    (selectorEmpty : ∀ prior ∈ priors, prior.reference? = none →
      localizedRule4bReferencesFromRankedLabels stages.a.key.rankedLabels = [])
    (inPrior : ∀ prior ∈ priors, prior.reference? = none →
      prior.rule4bKey = stages.a.key ∧ prior.rule4cKey = stages.noReference.key)
    (selectedPrior : ∀ prior ∈ priors, ∀ reference, prior.reference? = some reference →
      prior.rule4bKey = (stages.b reference).key ∧
        prior.rule4cKey = (stages.c reference).key) :
    input.buildRuleMajorCompoundRule5ReadingsWith?
        (contextRuleMajorCompiler input read (2 * (carrierFuel + 1))) cursor priors =
      some (priors.map input.ruleMajorExpectedRule5Reading) := by
  induction priors with
  | nil => rfl
  | cons prior priors ih =>
      have first := contextRule5ReadingWith?_eq_expected stages prior
        (fun h => selectorEmpty prior (by simp) h)
        (inPrior prior (by simp))
        (fun reference h => selectedPrior prior (by simp) reference h)
      have tail := ih
        (fun p h => selectorEmpty p (List.mem_cons_of_mem prior h))
        (fun p h => inPrior p (List.mem_cons_of_mem prior h))
        (fun p h reference href => selectedPrior p (List.mem_cons_of_mem prior h)
          reference href)
      simp [buildRuleMajorCompoundRule5ReadingsWith?, first, tail]

/-- Every ranked Rule-4b/4c prior reading comes from one of the actual alternative records. -/
private theorem contextStageSource_of_reading_mem
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (readingsEq : compound.prior.readings = input.rankReadings
      ((localizedRule4bcReferenceAlternatives compound.prior.references).map
        (contextStageReading stages)))
    {prior : input.LocalizedRerootRule4bcReading}
    (present : prior ∈ compound.prior.readings) :
    ∃ reference ∈ localizedRule4bcReferenceAlternatives compound.prior.references,
      contextStageReading stages reference = prior := by
  rw [readingsEq] at present
  exact List.mem_map.mp (mem_contextRankReadings present)

/-- For any reader and cursor, a successful uniform compound build made from the six actual
context stages has its exact Rule-5 output list as the expected lift of every prior reading.
The no-reference selector condition is derived from the builder's alternative list. -/
theorem contextStages_compound_rule5Readings_eq_map
    (stages : input.RuleMajorContextStages carrierFuel read cursor)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildRuleMajorCompoundRule45KeyWith?
      (contextRuleMajorCompiler input read (2 * (carrierFuel + 1))) cursor = some compound) :
    compound.rule5Readings =
      compound.prior.readings.map input.ruleMajorExpectedRule5Reading := by
  obtain ⟨_rule4aBuilt, _references, _count, _rawReadings, _rawBuilt, _ranked,
    rule5Built⟩ := input.buildRuleMajorCompoundRule45KeyWith?_readback
      (contextRuleMajorCompiler input read (2 * (carrierFuel + 1))) cursor built
  obtain ⟨_aEq, referencesEq, _countEq, readingsEq⟩ :=
    input.contextStages_compound_readback stages built
  have stageSource : ∀ prior ∈ compound.prior.readings,
      ∃ reference ∈ localizedRule4bcReferenceAlternatives compound.prior.references,
        contextStageReading stages reference = prior := by
    intro prior present
    exact contextStageSource_of_reading_mem stages readingsEq present
  have selectorEmpty : ∀ prior ∈ compound.prior.readings, prior.reference? = none →
      localizedRule4bReferencesFromRankedLabels stages.a.key.rankedLabels = [] := by
    intro prior present noReference
    obtain ⟨alternative, alternativeMem, readingEq⟩ := stageSource prior present
    have alternativeNone : alternative = none := by
      have tag : (contextStageReading stages alternative).reference? = none := by
        rw [readingEq]
        exact noReference
      cases alternative with
      | none => rfl
      | some selected => simp [contextStageReading] at tag
    have noneMem : (none : Option RS) ∈
        localizedRule4bcReferenceAlternatives compound.prior.references := by
      simpa [alternativeNone] using alternativeMem
    have referencesNil : compound.prior.references = [] := by
      cases hreferences : compound.prior.references with
      | nil => rfl
      | cons reference references =>
          simp [localizedRule4bcReferenceAlternatives, hreferences] at noneMem
    exact referencesEq.symm.trans referencesNil
  have inPrior : ∀ prior ∈ compound.prior.readings, prior.reference? = none →
      prior.rule4bKey = stages.a.key ∧ prior.rule4cKey = stages.noReference.key := by
    intro prior present noReference
    obtain ⟨alternative, _alternativeMem, readingEq⟩ := stageSource prior present
    have tag : (contextStageReading stages alternative).reference? = none := by
      rw [readingEq]
      exact noReference
    cases alternative with
    | none =>
        constructor
        · have keyEq := congrArg (fun reading : input.LocalizedRerootRule4bcReading =>
            reading.rule4bKey) readingEq
          simpa [contextStageReading] using keyEq.symm
        · have keyEq := congrArg (fun reading : input.LocalizedRerootRule4bcReading =>
            reading.rule4cKey) readingEq
          simpa [contextStageReading] using keyEq.symm
    | some selected => simp [contextStageReading] at tag
  have selectedPrior : ∀ prior ∈ compound.prior.readings, ∀ reference,
      prior.reference? = some reference →
        prior.rule4bKey = (stages.b reference).key ∧
          prior.rule4cKey = (stages.c reference).key := by
    intro prior present reference selected
    obtain ⟨alternative, _alternativeMem, readingEq⟩ := stageSource prior present
    have tag : (contextStageReading stages alternative).reference? = some reference := by
      rw [readingEq]
      exact selected
    cases alternative with
    | none => simp [contextStageReading] at tag
    | some alternative =>
        have alternativeEq : alternative = reference := by
          simpa [contextStageReading] using tag
        subst alternative
        constructor
        · have keyEq := congrArg (fun reading : input.LocalizedRerootRule4bcReading =>
            reading.rule4bKey) readingEq
          simpa [contextStageReading] using keyEq.symm
        · have keyEq := congrArg (fun reading : input.LocalizedRerootRule4bcReading =>
            reading.rule4cKey) readingEq
          simpa [contextStageReading] using keyEq.symm
  have rule5Mapped := contextRule5ReadingsWith?_eq_map stages compound.prior.readings
    selectorEmpty inPrior selectedPrior
  exact Option.some.inj (rule5Built.symm.trans rule5Mapped)

/-- The actual generated auxiliary-child pipeline also carries the exact Rule-5 list readback;
its stage family and successful compound build are still derived from the input. -/
theorem exists_generatedContextStages_compound_rule5Readback
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
    ∃ (compound : input.certified.LocalizedRerootCompoundRule45Key),
      input.certified.buildActualRuleMajorCompoundRule45KeyExec? target.occurrence
        (input.certified.localizedDependencyView
          (LocalizedRuleMajorReference.referenceState input) target.occurrence)
        (2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)) cursor = some compound ∧
      compound.rule5Readings =
        compound.prior.readings.map input.certified.ruleMajorExpectedRule5Reading := by
  let view := input.certified.localizedDependencyView
    (LocalizedRuleMajorReference.referenceState input) target.occurrence
  let read := input.certified.localizedDependencyLabel target.occurrence view
  obtain ⟨stages, compound, built, _aEq, _references, _count, _readings⟩ :=
    exists_generatedContextStages_compound_readback input
      singleBonded acyclic target unit targetUnit cursor rootChild
  let fuel := 2 * (input.certified.certified.input.molecule.atomCount + 1 + 1)
  have uniformBuilt : input.certified.buildRuleMajorCompoundRule45KeyWith?
      (fun stage position => input.certified.buildRuleMajorCumulativeWithRead? stage read fuel position)
      cursor = some compound := by
    rw [← input.certified.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor]
    rw [← input.certified.buildActualRuleMajorCompoundRule45KeyExec?_eq]
    exact built
  refine ⟨compound, built, ?_⟩
  exact input.certified.contextStages_compound_rule5Readings_eq_map stages uniformBuilt

end
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.contextStages_compound_rule5Readings_eq_map
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_generatedContextStages_compound_rule5Readback
