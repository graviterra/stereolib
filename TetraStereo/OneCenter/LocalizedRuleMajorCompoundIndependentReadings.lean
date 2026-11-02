import TetraStereo.OneCenter.LocalizedRuleMajorBranchStages
import TetraStereo.OneCenter.LocalizedRuleMajorCompoundReadback
import TetraStereo.OneCenter.LocalizedRuleMajorActualAlternativeOrdering
import TetraStereo.OneCenter.LocalizedRuleMajorReferenceSelection
import TetraStereo.OneCenter.DeclarativeCIPCompleteReadingSignature
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Actual compound success determines the exact stage key used by every alternative, the
independent reference population, and the complete observable ordering of its readings.  The
empty-reference reading retains its Rule-4c key, including any lowercase pseudoasymmetric data. -/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP
open Rule4aTableBridge
noncomputable section

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
  {index : Fin 4}
  {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
  {target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1)}

/-- The derived readback data for an actual successful compound build at one common layout. -/
structure RuleMajorCompoundReadbackData
    (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (compound : input.LocalizedRerootCompoundRule45Key) (W D : Nat) : Prop where
  /-- The production compound retained the exact `.rule4a` whole-rule stage key. -/
  aKey : compound.prior.rule4aKey = stages.a.key
  /-- P-92's selected references are those of the independent graph selection. -/
  references : compound.prior.references =
    Rule4aTableBridge.toReferenceList
      (referenceSelection input.moleculeGraph descriptorMap (input.topUnit center) stages.graph)
  /-- The retained criterion (c)(i) count agrees with that independent selection. -/
  count : compound.prior.referenceCountPriority =
    (referenceSelection input.moleculeGraph descriptorMap (input.topUnit center)
      stages.graph).countPriority
  /-- Every compound reading retains its exact successful Rule-4b and Rule-4c stage keys. -/
  readingStages : ∀ reading ∈ compound.prior.readings,
    match reading.reference? with
    | none => reading.rule4bKey = stages.a.key ∧
        reading.rule4cKey = stages.noReference.key
    | some reference => reading.rule4bKey = (stages.b reference).key ∧
        reading.rule4cKey = (stages.c reference).key
  /-- A `none` reading occurs exactly in the genuinely empty selected-reference case. -/
  readingEmpty : ∀ reading ∈ compound.prior.readings,
    reading.reference? = none ↔
      referenceSelection input.moleculeGraph descriptorMap (input.topUnit center)
        stages.graph = .empty
  /-- Projecting the actual `rankReadings` result gives the independent complete-reading list. -/
  observations : compound.prior.readings.map (fun reading =>
      completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
        stages.graph W D (reading.reference?.map senseOf)) =
    completeReadingsAt input.moleculeGraph descriptorMap (input.topUnit center)
      stages.graph W D

private def actualBranchCompiler (input : CertifiedLocalizedCIPInput)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (fuel : Nat) : input.RuleMajorCompoundStageCompiler carrierFuel :=
  fun stage cursor => input.buildRuleMajorCumulativeWithRead? stage
    (input.molecularReader descriptorMap target) fuel cursor

private def branchReading (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (reference : Option RS) : input.LocalizedRerootRule4bcReading :=
  match reference with
  | none =>
      { reference? := none, rule4bKey := stages.a.key,
        rule4cKey := stages.noReference.key }
  | some selected =>
      { reference? := some selected, rule4bKey := (stages.b selected).key,
        rule4cKey := (stages.c selected).key }

private theorem branchReading_build
    (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (reference : Option RS) :
    input.buildRuleMajorCompoundRule4bcReadingWith?
        (actualBranchCompiler input descriptorMap target
          (2 * (input.certified.input.molecule.atomCount + 1 + 1)))
        (input.localizedLigandRootCursor center index) reference =
      some (branchReading stages reference) := by
  cases reference with
  | none =>
      simp [CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingWith?,
        actualBranchCompiler, branchReading, stages.a.built,
        stages.noReference.built]
  | some selected =>
      simp [CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingWith?,
        actualBranchCompiler, branchReading, (stages.b selected).built,
        (stages.c selected).built]

private theorem branchReadings_build
    (stages : input.RuleMajorBranchStages center index descriptorMap target)
    (references : List (Option RS)) :
    input.buildRuleMajorCompoundRule4bcReadingsWith?
        (actualBranchCompiler input descriptorMap target
          (2 * (input.certified.input.molecule.atomCount + 1 + 1)))
        (input.localizedLigandRootCursor center index) references =
      some (references.map (branchReading stages)) := by
  induction references with
  | nil => rfl
  | cons reference references ih =>
      simp only [CertifiedLocalizedCIPInput.buildRuleMajorCompoundRule4bcReadingsWith?,
        Option.bind_eq_bind, branchReading_build stages reference, ih,
        Option.bind_some]
      rfl

/-- Readback for the actual production builder.  All branch equalities are obtained from its
success equation and the actual stage-family executions; no caller-supplied reading relation,
reference ordering, or label restriction is assumed. -/
theorem buildActualRuleMajorCompoundRule45Key?_independentReadback
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
    RuleMajorCompoundReadbackData stages compound W D := by
  let compiler := actualBranchCompiler input descriptorMap target
    (2 * (input.certified.input.molecule.atomCount + 1 + 1))
  let cursor := input.localizedLigandRootCursor center index
  have uniformBuilt : input.buildRuleMajorCompoundRule45KeyWith? compiler cursor =
      some compound := by
    have uniform := input.buildActualRuleMajorCompoundRule45Key?_eq_uniformRuleMajor
      target (input.molecularView descriptorMap target)
      (2 * (input.certified.input.molecule.atomCount + 1 + 1)) cursor
    simpa [compiler, actualBranchCompiler] using uniform.symm.trans built
  obtain ⟨rule4aBuilt, _referencesFromKey, countFromReferences, rawReadings,
      rawBuilt, rankedReadings, _rule5Built⟩ :=
    input.buildRuleMajorCompoundRule45KeyWith?_readback compiler cursor uniformBuilt
  have stage4aBuilt : compiler .rule4a cursor = some stages.a.key := by
    simpa [compiler, actualBranchCompiler, cursor] using stages.a.built
  have aKey : compound.prior.rule4aKey = stages.a.key :=
    Option.some.inj (rule4aBuilt.symm.trans stage4aBuilt)

  let actualInput : LocalizedUniversalReference.Input := ⟨input⟩
  obtain ⟨originalArm, originalCompound, originalBuilt, originalReferences⟩ :=
    Rule4aTableBridge.actualRuleMajorCompound_references_eq_referenceSelection actualInput
      descriptorMap tetrahedralMap target targetRoot targetAddress singleBonded acyclic
  have originalBuilt' : input.buildActualRuleMajorCompoundRule45Key? target
      (input.molecularView descriptorMap target)
      (2 * (input.certified.input.molecule.atomCount + 1 + 1)) cursor =
        some originalCompound := by
    simpa [actualInput, cursor] using originalBuilt
  have originalCompoundEq : originalCompound = compound :=
    Option.some.inj (originalBuilt'.symm.trans (by simpa [cursor] using built))
  subst originalCompound
  let originalGraph := OriginalRootArm.armGraph originalArm
  let branchGraph := stages.graph
  obtain ⟨iso⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso
    input.moleculeGraph center.1 (input.canonicalLigandAtom center index)
    originalGraph branchGraph originalArm.faithful stages.a.faithful
  have selectionIso := DeclarativeCIP.referenceSelection_iso input.moleculeGraph
    descriptorMap (input.topUnit center) iso
  have references : compound.prior.references =
      Rule4aTableBridge.toReferenceList
        (DeclarativeCIP.referenceSelection input.moleculeGraph descriptorMap
          (input.topUnit center) branchGraph) := by
    rw [originalReferences, ← selectionIso]

  let alternatives := localizedRule4bcReferenceAlternatives compound.prior.references
  have expectedRawBuild := branchReadings_build stages alternatives
  have rawEq : rawReadings = alternatives.map (branchReading stages) :=
    Option.some.inj (rawBuilt.symm.trans expectedRawBuild)
  have readingsEq : compound.prior.readings =
      input.rankReadings (alternatives.map (branchReading stages)) := by
    rw [rankedReadings, rawEq]
  have readingsEqSelection : compound.prior.readings = input.rankReadings
      ((localizedRule4bcReferenceAlternatives
        (Rule4aTableBridge.toReferenceList
          (DeclarativeCIP.referenceSelection input.moleculeGraph descriptorMap
            (input.topUnit center) branchGraph))).map (branchReading stages)) := by
    rw [readingsEq]
    dsimp [alternatives]
    rw [references]

  have count : compound.prior.referenceCountPriority =
      (DeclarativeCIP.referenceSelection input.moleculeGraph descriptorMap
        (input.topUnit center) branchGraph).countPriority := by
    rw [countFromReferences, references]
    cases selection : DeclarativeCIP.referenceSelection input.moleculeGraph descriptorMap
        (input.topUnit center) branchGraph with
    | empty => simp [Rule4aTableBridge.toReferenceList,
        constitutionalRule4bReferenceCountPriority, DeclarativeCIP.ReferenceSelection.countPriority]
    | one sense => cases sense <;>
        simp [Rule4aTableBridge.toReferenceList, constitutionalRule4bReferenceCountPriority,
          DeclarativeCIP.ReferenceSelection.countPriority]
    | both => simp [Rule4aTableBridge.toReferenceList,
        constitutionalRule4bReferenceCountPriority, DeclarativeCIP.ReferenceSelection.countPriority]

  have stageProvenance : ∀ reading ∈ compound.prior.readings,
      match reading.reference? with
      | none => reading.rule4bKey = stages.a.key ∧
          reading.rule4cKey = stages.noReference.key
      | some reference => reading.rule4bKey = (stages.b reference).key ∧
          reading.rule4cKey = (stages.c reference).key := by
    intro reading readingMem
    cases selection : DeclarativeCIP.referenceSelection input.moleculeGraph descriptorMap
        (input.topUnit center) branchGraph with
    | empty =>
        have readEq : compound.prior.readings = [branchReading stages none] := by
          rw [readingsEqSelection, selection]
          simp [localizedRule4bcReferenceAlternatives, rankReadings,
            Rule4aTableBridge.toReferenceList]
        have equal := List.mem_singleton.mp (by rw [← readEq]; exact readingMem)
        subst reading
        simp [branchReading]
    | one sense =>
        cases sense with
        | senior =>
            have readEq : compound.prior.readings =
                [branchReading stages (some .R)] := by
              rw [readingsEqSelection, selection]
              simp [localizedRule4bcReferenceAlternatives, rankReadings,
                Rule4aTableBridge.toReferenceList]
            have equal := List.mem_singleton.mp (by rw [← readEq]; exact readingMem)
            subst reading
            simp [branchReading]
        | junior =>
            have readEq : compound.prior.readings =
                [branchReading stages (some .S)] := by
              rw [readingsEqSelection, selection]
              simp [localizedRule4bcReferenceAlternatives, rankReadings,
                Rule4aTableBridge.toReferenceList]
            have equal := List.mem_singleton.mp (by rw [← readEq]; exact readingMem)
            subst reading
            simp [branchReading]
    | both =>
        have readEq : compound.prior.readings = input.rankReadings
            [branchReading stages (some .R), branchReading stages (some .S)] := by
          rw [readingsEqSelection, selection]
          simp [localizedRule4bcReferenceAlternatives,
            Rule4aTableBridge.toReferenceList]
        rw [readEq] at readingMem
        simp only [rankReadings] at readingMem
        split at readingMem <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at readingMem
        all_goals
          rcases readingMem with referenceR | referenceS
          · cases referenceR
            simp [branchReading]
          · cases referenceS
            simp [branchReading]

  have readingEmpty : ∀ reading ∈ compound.prior.readings,
      reading.reference? = none ↔
        DeclarativeCIP.referenceSelection input.moleculeGraph descriptorMap
          (input.topUnit center) branchGraph = .empty := by
    intro reading readingMem
    have provenance := stageProvenance reading readingMem
    cases selection : DeclarativeCIP.referenceSelection input.moleculeGraph descriptorMap
        (input.topUnit center) branchGraph with
    | empty =>
        have readEq : compound.prior.readings = [branchReading stages none] := by
          rw [readingsEqSelection, selection]
          simp [localizedRule4bcReferenceAlternatives, rankReadings,
            Rule4aTableBridge.toReferenceList]
        have equal := List.mem_singleton.mp (by rw [← readEq]; exact readingMem)
        subst reading
        simp [branchReading]
    | one sense =>
        cases sense with
        | senior =>
            have readEq : compound.prior.readings =
                [branchReading stages (some .R)] := by
              rw [readingsEqSelection, selection]
              simp [localizedRule4bcReferenceAlternatives, rankReadings,
                Rule4aTableBridge.toReferenceList]
            have equal := List.mem_singleton.mp (by rw [← readEq]; exact readingMem)
            subst reading
            simp [branchReading]
        | junior =>
            have readEq : compound.prior.readings =
                [branchReading stages (some .S)] := by
              rw [readingsEqSelection, selection]
              simp [localizedRule4bcReferenceAlternatives, rankReadings,
                Rule4aTableBridge.toReferenceList]
            have equal := List.mem_singleton.mp (by rw [← readEq]; exact readingMem)
            subst reading
            simp [branchReading]
    | both =>
        have readEq : compound.prior.readings = input.rankReadings
            [branchReading stages (some .R), branchReading stages (some .S)] := by
          rw [readingsEqSelection, selection]
          simp [localizedRule4bcReferenceAlternatives,
            Rule4aTableBridge.toReferenceList]
        rw [readEq] at readingMem
        simp only [rankReadings] at readingMem
        split at readingMem <;>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at readingMem
        all_goals
          rcases readingMem with referenceR | referenceS
          · cases referenceR
            simp [branchReading]
          · cases referenceS
            simp [branchReading]

  have observations : compound.prior.readings.map (fun reading =>
      completeReadingAt input.moleculeGraph descriptorMap (input.topUnit center)
        branchGraph W D (reading.reference?.map senseOf)) =
      completeReadingsAt input.moleculeGraph descriptorMap (input.topUnit center)
        branchGraph W D := by
    cases selection : DeclarativeCIP.referenceSelection input.moleculeGraph descriptorMap
        (input.topUnit center) branchGraph with
    | empty =>
        have readEq : compound.prior.readings = [branchReading stages none] := by
          rw [readingsEqSelection, selection]
          simp [localizedRule4bcReferenceAlternatives, rankReadings,
            Rule4aTableBridge.toReferenceList]
        rw [readEq]
        simp [DeclarativeCIP.completeReadingsAt, branchReading, selection]
    | one sense =>
        cases sense with
        | senior =>
            have readEq : compound.prior.readings =
                [branchReading stages (some .R)] := by
              rw [readingsEqSelection, selection]
              simp [localizedRule4bcReferenceAlternatives, rankReadings,
                Rule4aTableBridge.toReferenceList]
            rw [readEq]
            simp [DeclarativeCIP.completeReadingsAt, branchReading, selection,
              Rule4aTableBridge.senseOf]
        | junior =>
            have readEq : compound.prior.readings =
                [branchReading stages (some .S)] := by
              rw [readingsEqSelection, selection]
              simp [localizedRule4bcReferenceAlternatives, rankReadings,
                Rule4aTableBridge.toReferenceList]
            rw [readEq]
            simp [DeclarativeCIP.completeReadingsAt, branchReading, selection,
              Rule4aTableBridge.senseOf]
    | both =>
        have readEq : compound.prior.readings = input.rankReadings
            [branchReading stages (some .R), branchReading stages (some .S)] := by
          rw [readingsEqSelection, selection]
          simp [localizedRule4bcReferenceAlternatives,
            Rule4aTableBridge.toReferenceList]
        rw [readEq]
        have ordered := Rule4aTableBridge.actual_ruleMajor_rankReadings_observations
          descriptorMap tetrahedralMap target targetRoot targetAddress singleBonded acyclic
          stages.a (stages.b .R) (stages.c .R) (stages.b .S) (stages.c .S)
          branchGraph stages.a.faithful
          (stages.b_width_le .R |>.trans widthBound)
          (stages.b_depth_le .R |>.trans depthBound)
          (stages.c_width_le .R |>.trans widthBound)
          (stages.c_depth_le .R |>.trans depthBound)
          (stages.b_width_le .S |>.trans widthBound)
          (stages.b_depth_le .S |>.trans depthBound)
          (stages.c_width_le .S |>.trans widthBound)
          (stages.c_depth_le .S |>.trans depthBound)
        simpa [DeclarativeCIP.completeReadingsAt, selection, branchReading,
          Rule4aTableBridge.senseOf] using ordered

  exact {
    aKey := aKey
    references := references
    count := count
    readingStages := stageProvenance
    readingEmpty := readingEmpty
    observations := observations }

end
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RuleMajorCompoundReadbackData
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildActualRuleMajorCompoundRule45Key?_independentReadback
