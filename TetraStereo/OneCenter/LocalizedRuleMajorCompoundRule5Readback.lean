import TetraStereo.OneCenter.LocalizedRuleMajorCompoundIndependentReadings
import TetraStereo.OneCenter.LocalizedRuleMajorEmptyReferenceRule5
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Exact list-level Rule-5 readback for the actual rule-major compound builder. Each successful
reading keeps its Rule-4c key; the two common keys are the corresponding reference-sensitive
Rule-5 lifts. The empty-reference case is the false lift, preserving lowercase Rule-4c data. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP LocalizedCumulativeDecoratedTree
noncomputable section

/-- The Rule-5 record determined by one Rule-4b/4c reading and its reference population. -/
def ruleMajorExpectedRule5Reading (input : CertifiedLocalizedCIPInput)
    (prior : input.LocalizedRerootRule4bcReading) : input.LocalizedRerootRule5Reading :=
  let sameAs (reference : RS) : Bool :=
    match prior.reference? with
    | none => false
    | some selected => reference == selected
  { prior := prior
    commonR := input.rule5LiftKey (sameAs .R) prior.rule4cKey
    commonS := input.rule5LiftKey (sameAs .S) prior.rule4cKey }

private def actualRuleMajorCompiler (input : CertifiedLocalizedCIPInput)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (fuel : Nat) : input.RuleMajorCompoundStageCompiler carrierFuel :=
  fun stage cursor => input.buildRuleMajorCumulativeWithRead? stage
    (input.molecularReader descriptorMap target) fuel cursor

private theorem actualRuleMajorCompoundRule5ReadingWith?_eq_expected
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (prior : input.LocalizedRerootRule4bcReading)
    (selectorEmpty : prior.reference? = none →
      localizedRule4bReferencesFromRankedLabels stages.a.key.rankedLabels = [])
    (inPrior : prior.reference? = none →
      prior.rule4bKey = stages.a.key ∧ prior.rule4cKey = stages.noReference.key)
    (selectedPrior : ∀ reference, prior.reference? = some reference →
      prior.rule4bKey = (stages.b reference).key ∧ prior.rule4cKey = (stages.c reference).key) :
    input.buildRuleMajorCompoundRule5ReadingWith?
        (actualRuleMajorCompiler input descriptorMap target
          (2 * (input.certified.input.molecule.atomCount + 1 + 1)))
        (input.localizedLigandRootCursor center index) prior =
      some (input.ruleMajorExpectedRule5Reading prior) := by
  let read := input.molecularReader descriptorMap target
  let fuel := 2 * (input.certified.input.molecule.atomCount + 1 + 1)
  let cursor := input.localizedLigandRootCursor center index
  cases hreference : prior.reference? with
  | none =>
      have hprior := inPrior hreference
      have hRule4a : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
          read fuel cursor = some stages.a.key := by
        rw [← input.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized read fuel cursor]
        simpa [read, fuel, cursor] using stages.a.built
      have hNoReference : input.buildRuleMajorCumulativeWithRead? .rule4cNoReference
          read fuel cursor = some stages.noReference.key := by
        simpa [read, fuel, cursor] using stages.noReference.built
      have hRule5 := input.buildRuleMajorCumulativeWithRead?_rule5NoReference_of_rule4aSelection_eq_nil
        .R read fuel cursor stages.a.key hRule4a
        (selectorEmpty hreference) stages.noReference.key hNoReference
      have hRule5S := input.buildRuleMajorCumulativeWithRead?_rule5NoReference_of_rule4aSelection_eq_nil
        .S read fuel cursor stages.a.key hRule4a
        (selectorEmpty hreference) stages.noReference.key hNoReference
      have hR : actualRuleMajorCompiler input descriptorMap target fuel
          (localizedRule5StageFor none .R) cursor =
            some (input.rule5LiftKey false prior.rule4cKey) := by
        change input.buildRuleMajorCumulativeWithRead? (.rule5NoRule4bReference .R)
          read fuel cursor = _
        rw [hRule5, hprior.2]
      have hS : actualRuleMajorCompiler input descriptorMap target fuel
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
          actualRuleMajorCompiler input descriptorMap target fuel
            (localizedRule5StageFor (some reference) common) cursor =
          some (input.rule5LiftKey (common == reference) prior.rule4cKey) := by
        have hRule4c : input.buildRuleMajorCumulativeWithRead? (.rule4c reference)
            read fuel cursor = some (stages.c reference).key := by
          simpa [read, fuel, cursor] using (stages.c reference).built
        have hRule5 := input.buildRuleMajorCumulativeWithRead?_rule5 reference common
          read fuel cursor
        change input.buildRuleMajorCumulativeWithRead? (.rule5 reference common) read fuel cursor = _
        rw [hRule4c] at hRule5
        simpa [hprior.2] using hRule5
      unfold buildRuleMajorCompoundRule5ReadingWith?
      rw [hreference, hCommon .R, hCommon .S]
      simp [hreference, ruleMajorExpectedRule5Reading]

private theorem actualRuleMajorCompoundRule5ReadingsWith?_eq_map
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (priors : List input.LocalizedRerootRule4bcReading)
    (selectorEmpty : ∀ prior ∈ priors, prior.reference? = none →
      localizedRule4bReferencesFromRankedLabels stages.a.key.rankedLabels = [])
    (inPrior : ∀ prior ∈ priors, prior.reference? = none →
      prior.rule4bKey = stages.a.key ∧ prior.rule4cKey = stages.noReference.key)
    (selectedPrior : ∀ prior ∈ priors, ∀ reference, prior.reference? = some reference →
      prior.rule4bKey = (stages.b reference).key ∧ prior.rule4cKey = (stages.c reference).key) :
    input.buildRuleMajorCompoundRule5ReadingsWith?
        (actualRuleMajorCompiler input descriptorMap target
          (2 * (input.certified.input.molecule.atomCount + 1 + 1)))
        (input.localizedLigandRootCursor center index) priors =
      some (priors.map input.ruleMajorExpectedRule5Reading) := by
  let cursor := input.localizedLigandRootCursor center index
  induction priors with
  | nil => rfl
  | cons prior priors ih =>
      have first := actualRuleMajorCompoundRule5ReadingWith?_eq_expected target stages
        prior (fun h => selectorEmpty prior (by simp) h)
        (inPrior prior (by simp))
        (fun reference h => selectedPrior prior (by simp) reference h)
      have tail := ih
        (fun p h => selectorEmpty p (List.mem_cons_of_mem prior h))
        (fun p h => inPrior p (List.mem_cons_of_mem prior h))
        (fun p h reference href => selectedPrior p (List.mem_cons_of_mem prior h) reference href)
      simp [buildRuleMajorCompoundRule5ReadingsWith?, first, tail]

/-- Actual compound Rule-5 readback as an exact map over the already ranked Rule-4b/4c readings.
The theorem retains all reading metadata and both stage keys, including empty-reference lowercase
observations. -/
theorem buildActualRuleMajorCompoundRule45Key?_rule5Readings_eq_map
    {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter} {index : Fin 4}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetRoot : target.1.root = center.1) (targetAddress : target.1.address = [])
    (singleBonded : input.moleculeGraph.SimpleBonded) (acyclic : input.moleculeGraph.Acyclic)
    (stages : input.RuleMajorBranchStages center index descriptorMap target)
    {W D : Nat} (widthBound : stages.widthBound ≤ W) (depthBound : stages.depthBound ≤ D)
    {compound : input.LocalizedRerootCompoundRule45Key}
    (built : input.buildActualRuleMajorCompoundRule45Key? target
      (input.molecularView descriptorMap target)
      (2 * (input.certified.input.molecule.atomCount + 1 + 1))
      (input.localizedLigandRootCursor center index) = some compound) :
    compound.rule5Readings = compound.prior.readings.map input.ruleMajorExpectedRule5Reading := by
  let compiler := actualRuleMajorCompiler input descriptorMap target
    (2 * (input.certified.input.molecule.atomCount + 1 + 1))
  let cursor := input.localizedLigandRootCursor center index
  have uniformBuilt : input.buildRuleMajorCompoundRule45KeyWith? compiler cursor = some compound := by
    have uniform := input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor target
      (input.molecularView descriptorMap target)
      (2 * (input.certified.input.molecule.atomCount + 1 + 1)) cursor
    simpa [compiler, actualRuleMajorCompiler] using uniform.symm.trans built
  obtain ⟨_rule4aBuilt, _references, _count, _rawReadings, _rawBuilt, _ranked,
    rule5Built⟩ := input.buildRuleMajorCompoundRule45KeyWith?_readback compiler cursor uniformBuilt
  have readback := input.buildActualRuleMajorCompoundRule45Key?_independentReadback
    descriptorMap tetrahedralMap target targetRoot targetAddress singleBonded acyclic stages
    widthBound depthBound built
  have selectorEmpty : ∀ prior ∈ compound.prior.readings, prior.reference? = none →
      localizedRule4bReferencesFromRankedLabels stages.a.key.rankedLabels = [] := by
    intro prior priorMem noneReference
    have selectionEmpty := (readback.readingEmpty prior priorMem).mp noneReference
    have priorReferencesEmpty : compound.prior.references = [] := by
      rw [readback.references, selectionEmpty]
      simp [Rule4aTableBridge.toReferenceList]
    have genericReadback := input.buildRuleMajorCompoundRule45KeyWith?_readback
      compiler cursor uniformBuilt
    calc
      localizedRule4bReferencesFromRankedLabels stages.a.key.rankedLabels =
          localizedRule4bReferencesFromRankedLabels compound.prior.rule4aKey.rankedLabels := by
        rw [readback.aKey]
      _ = compound.prior.references := genericReadback.2.1.symm
      _ = [] := priorReferencesEmpty
  have inPrior : ∀ prior ∈ compound.prior.readings, prior.reference? = none →
      prior.rule4bKey = stages.a.key ∧ prior.rule4cKey = stages.noReference.key := by
    intro prior present noneReference
    have actual := readback.readingStages prior present
    simpa [noneReference] using actual
  have selectedPrior : ∀ prior ∈ compound.prior.readings, ∀ reference,
      prior.reference? = some reference →
        prior.rule4bKey = (stages.b reference).key ∧
          prior.rule4cKey = (stages.c reference).key := by
    intro prior present reference selected
    have actual := readback.readingStages prior present
    simpa [selected] using actual
  have rule5Mapped := actualRuleMajorCompoundRule5ReadingsWith?_eq_map target stages
    compound.prior.readings selectorEmpty inPrior selectedPrior
  have equality := rule5Built.symm.trans rule5Mapped
  exact Option.some.inj equality

end
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorExpectedRule5Reading
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildActualRuleMajorCompoundRule45Key?_rule5Readings_eq_map
