import TetraStereo.OneCenter.LocalizedRootBranchAuxiliaryLocality
import TetraStereo.OneCenter.LocalizedRootwardSeparatedArmBridge
import TetraStereo.OneCenter.LocalizedRuleMajorSeparatedArmLocality
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unnecessarySimpa false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-!
# Descriptor equality from strict dependencies of one tied root arm

The frozen bridge asks the two descriptor maps to agree on every unit of the
root arm, including the target and its ancestors. A depth induction only has
the strictly deeper occurrences. This module uses the derived parent separation
and the outward-consult theorem: agreement on those strict dependencies whose full occurrence units remain in
the chosen branch is enough for the actual descriptor. No agreement at spectator
branches, the target itself, or its ancestors is required.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

open DeclarativeCIP
open LocalizedRootwardConstitutionalSeparation (carrierFuel)

private theorem executableChild_neighbor
    (input : CertifiedLocalizedCIPInput)
    (parent child : input.LocalizedRerootCursor (carrierFuel input))
    (mem : child ∈ input.executableLocalizedRerootChildren parent) :
    child.occurrence.1 ∈ input.localizedRerootNeighborFrames (fuel := carrierFuel input)
      parent.occurrence.1 := by
  have intended : child.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames parent := by
    rw [← input.executableLocalizedRerootChildren_map parent]
    exact List.mem_map.mpr ⟨child, mem, rfl⟩
  unfold intendedLocalizedRerootChildFrames at intended
  by_cases duplicate : parent.occurrence.1.node.isDuplicateLeaf = true
  · simp [duplicate] at intended
  · have notDuplicate : parent.occurrence.1.node.isDuplicateLeaf = false :=
      Bool.eq_false_of_not_eq_true duplicate
    cases previous : parent.previous?
    · simp [notDuplicate, previous] at intended
      exact intended
    · simp [notDuplicate, previous] at intended
      exact intended.1

private theorem target_address_ne_nil_of_rootArm
    (input : CertifiedLocalizedCIPInput)
    (rootCursor armCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (inside : input.RootBranchContains armCursor.occurrence target) :
    target.1.address ≠ [] := by
  have neighbor := executableChild_neighbor input rootCursor armCursor armMem
  have adjacent :=
    ((input.mem_localizedRerootNeighborFrames_iff rootCursor.occurrence.1
      armCursor.occurrence.1).mp neighbor).2
  have armLen : armCursor.occurrence.1.address.length = 1 := by
    rcases adjacent with ⟨_, shorter | longer⟩
    · rw [rootAddress] at shorter
      simp at shorter
    · rw [rootAddress] at longer
      exact longer.1.symm
  have targetLen : 1 ≤ target.1.address.length := by
    have lengthLe := List.IsPrefix.length_le inside.2
    simpa [armLen] using lengthLe
  exact List.ne_nil_of_length_pos (by omega)

private theorem consult_agrees_of_strictDependency
    (input : CertifiedLocalizedCIPInput)
    (branch : input.LocalizedRerootCursor (carrierFuel input))
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (inside : input.RootBranchContains branch.occurrence target)
    (start : input.LocalizedRerootCursor (carrierFuel input))
    (outward : OutwardRerootCursor input target start)
    (form : IsLocalizedActualFrameOutwardCursor input target start)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (agree : ∀ source, input.LocalizedDepthDependency source target →
      source.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      ∀ unit, input.molecularFrameUnit source.1 = unit.1 →
        input.OccurrenceUnitExtendsRootBranch branch.occurrence unit.1 →
          map₁ unit = map₂ unit)
    (unit : DetectedOccurrence input.moleculeGraph)
    (consulted : input.ReachableArmDescriptorConsult target start unit) :
    map₁ unit = map₂ unit := by
  let targetCursor : input.LocalizedRerootCursor (carrierFuel input) :=
    { occurrence := target, previous? := none }
  have strictPack := input.outwardConsult_unit_extends_rootBranch branch targetCursor start
    inside outward form unit consulted
  rcases consulted with ⟨cursor, _reachable, dependency, real, unitEq⟩
  exact agree cursor.occurrence dependency real unit unitEq strictPack.1

/-- Outward-consult agreement, with the parent slot separated by the root tie. -/
theorem ruleMajorDescriptor?_eq_of_tiedRootOutwardConsult
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (rootCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (inside : input.RootBranchContains armCursor.occurrence target)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (agree : ∀ start, IsLocalizedActualFrameOutwardCursor input target start →
      OutwardRerootCursor input target start →
      ∀ unit, input.ReachableArmDescriptorConsult target start unit →
        map₁ unit = map₂ unit) :
    input.ruleMajorDescriptor? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptor? target (input.molecularView map₂ target) := by
  have nonroot := target_address_ne_nil_of_rootArm input rootCursor armCursor rootAddress
    armMem target inside
  obtain ⟨index, _, _, isParent, others⟩ :=
    input.actualFrame_parentIndex target frame computed nonroot
  have separated := armConstitutionalRule1aSeparated_of_rootArmRule1aTie input singleBonded
    rootCursor rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal'
    armRead armRead' armKey armKey' armBuilt armBuilt' tie target targetReal inside frame
    computed nonroot index isParent
  have agreeArms : ∀ other, other ≠ index →
      ∀ unit, input.ReachableArmDescriptorConsult target (frame.cursorAt other) unit →
        map₁ unit = map₂ unit := by
    intro other otherNe unit consulted
    obtain ⟨form, outward⟩ := others other otherNe
    exact agree (frame.cursorAt other) form outward unit consulted
  exact input.ruleMajorDescriptor?_eq_of_compiledSeparatedArm target map₁ map₂ frame computed
    index separated agreeArms

theorem ruleMajorDescriptorExec?_eq_of_tiedRootOutwardConsult
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (rootCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (inside : input.RootBranchContains armCursor.occurrence target)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (frame : input.LocalizedOccurrenceFourLigandFrame (carrierFuel input))
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (agree : ∀ start, IsLocalizedActualFrameOutwardCursor input target start →
      OutwardRerootCursor input target start →
      ∀ unit, input.ReachableArmDescriptorConsult target start unit →
        map₁ unit = map₂ unit) :
    input.ruleMajorDescriptorExec? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptorExec? target (input.molecularView map₂ target) := by
  rw [input.ruleMajorDescriptorExec?_eq target (input.molecularView map₁ target),
    input.ruleMajorDescriptorExec?_eq target (input.molecularView map₂ target)]
  exact ruleMajorDescriptor?_eq_of_tiedRootOutwardConsult input singleBonded rootCursor
    rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead armRead'
    armKey armKey' armBuilt armBuilt' tie target targetReal inside map₁ map₂ frame computed agree

/-- Strict-dependency agreement on the outward arms. Refusal cases reuse the
existing descriptor lemmas. -/
theorem ruleMajorDescriptor?_eq_of_tiedRootStrictDependency
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (rootCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (inside : input.RootBranchContains armCursor.occurrence target)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (agree : ∀ source, input.LocalizedDepthDependency source target →
      source.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      ∀ unit, input.molecularFrameUnit source.1 = unit.1 →
        input.OccurrenceUnitExtendsRootBranch armCursor.occurrence unit.1 →
          map₁ unit = map₂ unit) :
    input.ruleMajorDescriptor? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptor? target (input.molecularView map₂ target) := by
  by_cases targetReal : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom
  · cases frameComputed : input.localizedOccurrenceFourLigandFrame? target with
    | none =>
        exact input.ruleMajorDescriptor?_eq_of_missingFrame target map₁ map₂ frameComputed
    | some frame =>
        by_cases absentCenter : input.localizedOccurrenceDescriptorCenter? target = none
        · exact input.ruleMajorDescriptor?_eq_of_missingCenter target map₁ map₂ absentCenter
        · let branchCursor : input.LocalizedRerootCursor (carrierFuel input) :=
            { occurrence := armCursor.occurrence, previous? := none }
          have agreeOut : ∀ start, IsLocalizedActualFrameOutwardCursor input target start →
              OutwardRerootCursor input target start →
              ∀ unit, input.ReachableArmDescriptorConsult target start unit →
                map₁ unit = map₂ unit := by
            intro start form outward unit consulted
            exact consult_agrees_of_strictDependency input branchCursor target inside start
              outward form map₁ map₂ agree unit consulted
          exact ruleMajorDescriptor?_eq_of_tiedRootOutwardConsult input singleBonded rootCursor
            rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead
            armRead' armKey armKey' armBuilt armBuilt' tie target targetReal inside map₁ map₂
            frame frameComputed agreeOut
  · exact input.ruleMajorDescriptor?_eq_of_not_realTarget target map₁ map₂ targetReal

theorem ruleMajorDescriptorExec?_eq_of_tiedRootStrictDependency
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (rootCursor : input.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.LocalizedCIPOccurrence (carrierFuel input))
    (inside : input.RootBranchContains armCursor.occurrence target)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (agree : ∀ source, input.LocalizedDepthDependency source target →
      source.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      ∀ unit, input.molecularFrameUnit source.1 = unit.1 →
        input.OccurrenceUnitExtendsRootBranch armCursor.occurrence unit.1 →
          map₁ unit = map₂ unit) :
    input.ruleMajorDescriptorExec? target (input.molecularView map₁ target) =
      input.ruleMajorDescriptorExec? target (input.molecularView map₂ target) := by
  rw [input.ruleMajorDescriptorExec?_eq target (input.molecularView map₁ target),
    input.ruleMajorDescriptorExec?_eq target (input.molecularView map₂ target)]
  exact ruleMajorDescriptor?_eq_of_tiedRootStrictDependency input singleBonded rootCursor
    rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead armRead'
    armKey armKey' armBuilt armBuilt' tie target inside map₁ map₂ agree

end CertifiedLocalizedCIPInput

namespace LocalizedRuleMajorReference

open CertifiedLocalizedCIPInput DeclarativeCIP

theorem ruleMajorDescriptor?_eq_of_tiedCyclicRootStrictDependency
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootCursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.certified.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.certified.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.certified.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.certified.LocalizedCIPOccurrence (carrierFuel input))
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (inside : input.certified.RootBranchContains armCursor.occurrence target)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (agree : ∀ source, input.certified.LocalizedDepthDependency source target →
      source.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      ∀ unit, input.certified.molecularFrameUnit source.1 = unit.1 →
        input.certified.OccurrenceUnitExtendsRootBranch armCursor.occurrence unit.1 →
          map₁ unit = map₂ unit) :
    input.certified.ruleMajorDescriptor? target (input.certified.molecularView map₁ target) =
      input.certified.ruleMajorDescriptor? target
        (input.certified.molecularView map₂ target) := by
  let compilation := cyclicContextFrameCompilation input singleBonded target real unit targetUnit
  have frameComputed : input.certified.localizedOccurrenceFourLigandFrame? target =
      some compilation.frame := by
    rw [← input.certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?
      target]
    exact compilation.frameComputed
  exact ruleMajorDescriptor?_eq_of_tiedRootStrictDependency input.certified singleBonded
    rootCursor rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal'
    armRead armRead' armKey armKey' armBuilt armBuilt' tie target inside map₁ map₂ agree

theorem ruleMajorDescriptorExec?_eq_of_tiedCyclicRootStrictDependency
    (input : Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (rootCursor : input.certified.LocalizedRerootCursor (carrierFuel input))
    (rootAddress : rootCursor.occurrence.1.address = [])
    (armCursor armCursor' : input.certified.LocalizedRerootCursor (carrierFuel input))
    (armMem : armCursor ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armMem' : armCursor' ∈ input.certified.executableLocalizedRerootChildren rootCursor)
    (armDistinct : armCursor.occurrence ≠ armCursor'.occurrence)
    (armReal : armCursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armReal' : armCursor'.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (armRead armRead' : input.certified.LocalizedRerootCursor (carrierFuel input) →
      Option LocalizedAuxiliaryLabel)
    {armFuel armFuel' : Nat}
    (armKey armKey' : input.certified.LocalizedRerootCumulativeRule45Key)
    (armBuilt : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead armFuel armCursor = some armKey)
    (armBuilt' : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
      armRead' armFuel' armCursor' = some armKey')
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      armKey.constitutional.rule1a armKey'.constitutional.rule1a = Ordering.eq)
    (target : input.certified.LocalizedCIPOccurrence (carrierFuel input))
    (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (targetUnit : input.certified.molecularFrameUnit target.1 = unit.1)
    (inside : input.certified.RootBranchContains armCursor.occurrence target)
    (map₁ map₂ : DescriptorMap (DetectedOccurrence input.certified.moleculeGraph))
    (agree : ∀ source, input.certified.LocalizedDepthDependency source target →
      source.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      ∀ unit, input.certified.molecularFrameUnit source.1 = unit.1 →
        input.certified.OccurrenceUnitExtendsRootBranch armCursor.occurrence unit.1 →
          map₁ unit = map₂ unit) :
    input.certified.ruleMajorDescriptorExec? target
        (input.certified.molecularView map₁ target) =
      input.certified.ruleMajorDescriptorExec? target
        (input.certified.molecularView map₂ target) := by
  rw [input.certified.ruleMajorDescriptorExec?_eq target
      (input.certified.molecularView map₁ target),
    input.certified.ruleMajorDescriptorExec?_eq target
      (input.certified.molecularView map₂ target)]
  exact ruleMajorDescriptor?_eq_of_tiedCyclicRootStrictDependency input singleBonded rootCursor
    rootAddress armCursor armCursor' armMem armMem' armDistinct armReal armReal' armRead armRead'
    armKey armKey' armBuilt armBuilt' tie target real unit targetUnit inside map₁ map₂ agree

end LocalizedRuleMajorReference
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptor?_eq_of_tiedRootOutwardConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?_eq_of_tiedRootOutwardConsult
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptor?_eq_of_tiedRootStrictDependency
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ruleMajorDescriptorExec?_eq_of_tiedRootStrictDependency
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ruleMajorDescriptor?_eq_of_tiedCyclicRootStrictDependency
assert_kernel_only TetraStereo.OneCenter.LocalizedRuleMajorReference.ruleMajorDescriptorExec?_eq_of_tiedCyclicRootStrictDependency
