import TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness
import TetraStereo.OneCenter.LocalizedRetainedContextGeneratedDescriptor
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Spatial cyclic root: own state, without a letter

The spatial fixture is unchanged. At standard fuel `carrierFuel = 10`, the own
reference state of the detected root is read at `localizedFinalOccurrenceExecutable`,
whose root is that center. `SimpleBonded` is the only graph hypothesis.
`referenceState_at_final_occurrence_some_iff_retainedJudgment` identifies that state
with `RetainedContextualDescriptorJudgmentAt` on the compiled Rule-4a arm graphs.
Acyclicity is not used, and the arm graphs are not executed here.

A letter would be one strict descending permutation of those retained keys together
with `classifyTetrahedralRSPseudo` of the coordinates in that order. The four written
root neighbors are atoms `5`, `1`, `2`, and `4`, with source atomic numbers `1`, `9`,
`6`, and `6`. Atoms `2` and `4` are both carbon, so the first Rule-1a sphere does not
strictly order the four ligands. The atomic-number-separated positivity theorem does
not apply.

Atom `2`'s written neighbors include chlorine, atomic number `17`. Atom `4`'s other
written neighbors are carbon and two terminal hydrogens. That inventory is not a
retained-key comparison. `ruleMajorTreeGraph_faithfulExactExpansion` assumes
`MoleculeGraph.Acyclic`, and this carrier has the accepted 3-cycle on atoms
`{0, 2, 4}`. No accepted theorem transports an official second-sphere comparison to
`frames.retainedKeys` or to `referenceState`.

No `R`, `S`, `r`, or `s` is asserted. The all-ring theorem stays separate.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.LocalizedRuleMajorReference
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.LocalizedCyclicInputWitness
open TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness
open TetraStereo.OneCenter.MoleculeGraph
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission

noncomputable section

def spatialRootCenter : cyclicSpatialCertified.TetrahedralCenter :=
  ⟨SA ⟨0, by decide⟩, spatial_detected_inventory.2.2.2.1⟩

theorem spatialRoot_fuel : carrierFuel cyclicSpatialReference = 10 :=
  standardFuel_eq_ten

theorem spatialRoot_provenance :
    (cyclicSpatialCertified.localizedFinalOccurrenceExecutable
        (carrierFuel cyclicSpatialReference) spatialRootCenter).1.node.provenance =
      OfficialCIPNodeProvenance.realAtom :=
  finalOccurrence_provenance_real cyclicSpatialReference spatialRootCenter

theorem spatialRoot_own_root :
    (cyclicSpatialCertified.localizedFinalOccurrenceExecutable
        (carrierFuel cyclicSpatialReference) spatialRootCenter).1.root =
      spatialRootCenter.val :=
  cyclicSpatialCertified.localizedFinalOccurrenceExecutable_root
    (carrierFuel cyclicSpatialReference) spatialRootCenter

theorem spatialRoot_address :
    (cyclicSpatialCertified.localizedFinalOccurrenceExecutable
        (carrierFuel cyclicSpatialReference) spatialRootCenter).1.address = [] :=
  cyclicSpatialCertified.localizedFinalOccurrenceExecutable_address
    (carrierFuel cyclicSpatialReference) spatialRootCenter

/-- Own reference state at the spatial root, at fuel 10, agrees with the retained judgment
of the compiled Rule-4a arm graphs. No letter is selected. -/
theorem spatialRoot_referenceState_eq_some_iff (descriptor : LocalizedAuxiliaryLabel) :
    let target := cyclicSpatialReference.certified.localizedFinalOccurrenceExecutable
      (carrierFuel cyclicSpatialReference) spatialRootCenter
    let unit := finalCenterUnit cyclicSpatialReference spatialRootCenter
    let frames := cyclicContextFrameCompilation cyclicSpatialReference spatial_simpleBonded
      target (finalOccurrence_provenance_real cyclicSpatialReference spatialRootCenter)
      unit (finalOccurrence_molecularFrameUnit cyclicSpatialReference spatialRootCenter)
    referenceState cyclicSpatialReference target = some descriptor ↔
      RetainedContextualDescriptorJudgmentAt cyclicSpatialReference.certified.moleculeGraph
        (descriptorMap cyclicSpatialReference) unit frames.actualArmGraphs frames.W frames.D
        frames.actualCoordinates descriptor :=
  referenceState_at_final_occurrence_some_iff_retainedJudgment
    cyclicSpatialReference spatial_simpleBonded spatialRootCenter descriptor

theorem spatialRoot_referenceState_eq_none_iff :
    let target := cyclicSpatialReference.certified.localizedFinalOccurrenceExecutable
      (carrierFuel cyclicSpatialReference) spatialRootCenter
    let unit := finalCenterUnit cyclicSpatialReference spatialRootCenter
    let frames := cyclicContextFrameCompilation cyclicSpatialReference spatial_simpleBonded
      target (finalOccurrence_provenance_real cyclicSpatialReference spatialRootCenter)
      unit (finalOccurrence_molecularFrameUnit cyclicSpatialReference spatialRootCenter)
    referenceState cyclicSpatialReference target = none ↔
      ¬ ∃ descriptor,
        RetainedContextualDescriptorJudgmentAt cyclicSpatialReference.certified.moleculeGraph
          (descriptorMap cyclicSpatialReference) unit frames.actualArmGraphs frames.W frames.D
          frames.actualCoordinates descriptor :=
  referenceState_none_iff_no_retainedJudgment_of_real cyclicSpatialReference
    spatial_simpleBonded
    (cyclicSpatialReference.certified.localizedFinalOccurrenceExecutable
      (carrierFuel cyclicSpatialReference) spatialRootCenter)
    (finalOccurrence_provenance_real cyclicSpatialReference spatialRootCenter)
    (finalCenterUnit cyclicSpatialReference spatialRootCenter)
    (finalOccurrence_molecularFrameUnit cyclicSpatialReference spatialRootCenter)

theorem hydrogenFive_source_atomicNumber :
    ∃ spec, cyclicExpanded.atomAt? 5 = some spec ∧
      spec.element = .H ∧ spec.element.atomicNumber = 1 := by
  obtain ⟨spec, lookup, aliphatic, _bondSum⟩ := fresh_hydrogen 5 (by decide) (by decide)
  refine ⟨spec, lookup, ?_, ?_⟩
  · simp [aliphatic, AtomSpec.aliphatic]
  · simp [aliphatic, AtomSpec.aliphatic, Element.atomicNumber]

theorem fluorine_source_atomicNumber :
    ∃ spec, cyclicExpanded.atomAt? 1 = some spec ∧
      spec.element = .F ∧ spec.element.atomicNumber = 9 := by
  let rawSpec : AtomSpec := { AtomSpec.aliphatic .F with explicitHydrogens? := some 0 }
  refine ⟨materializedAtomSpec rawSpec,
    expanded_original_atom 0 TetrahedralInputParity.anticlockwise 1 rawSpec
      (ringRaw_atomAt_one 0 TetrahedralInputParity.anticlockwise), ?_, ?_⟩
  · simp [materializedAtomSpec_element, rawSpec, AtomSpec.aliphatic]
  · simp [materializedAtomSpec_element, rawSpec, AtomSpec.aliphatic, Element.atomicNumber]

theorem armCarbon_source_atomicNumber :
    ∃ spec, cyclicExpanded.atomAt? 2 = some spec ∧
      spec.element = .C ∧ spec.element.atomicNumber = 6 := by
  refine ⟨materializedAtomSpec (carbon 1),
    expanded_original_atom 0 TetrahedralInputParity.anticlockwise 2 (carbon 1)
      (ringRaw_atomAt_two 0 TetrahedralInputParity.anticlockwise), ?_, ?_⟩
  · simp [materializedAtomSpec_element, carbon, AtomSpec.aliphatic]
  · simp [materializedAtomSpec_element, carbon, AtomSpec.aliphatic, Element.atomicNumber]

theorem closingCarbon_source_atomicNumber :
    ∃ spec, cyclicExpanded.atomAt? 4 = some spec ∧
      spec.element = .C ∧ spec.element.atomicNumber = 6 := by
  have raw := ringRaw_atomAt_chain 0 TetrahedralInputParity.anticlockwise 0 (Nat.le_refl _)
  refine ⟨materializedAtomSpec (carbon 2),
    expanded_original_atom 0 TetrahedralInputParity.anticlockwise 4 (carbon 2)
      (by simpa using raw), ?_, ?_⟩
  · simp [materializedAtomSpec_element, carbon, AtomSpec.aliphatic]
  · simp [materializedAtomSpec_element, carbon, AtomSpec.aliphatic, Element.atomicNumber]

theorem chlorine_source_atomicNumber :
    ∃ spec, cyclicExpanded.atomAt? 3 = some spec ∧
      spec.element = .Cl ∧ spec.element.atomicNumber = 17 := by
  let rawSpec : AtomSpec := { AtomSpec.aliphatic .Cl with explicitHydrogens? := some 0 }
  refine ⟨materializedAtomSpec rawSpec,
    expanded_original_atom 0 TetrahedralInputParity.anticlockwise 3 rawSpec
      (ringRaw_atomAt_three 0 TetrahedralInputParity.anticlockwise), ?_, ?_⟩
  · simp [materializedAtomSpec_element, rawSpec, AtomSpec.aliphatic]
  · simp [materializedAtomSpec_element, rawSpec, AtomSpec.aliphatic, Element.atomicNumber]

theorem terminalHydrogen_source_atomicNumber
    (index : ℕ) (low : 5 ≤ index) (high : index < 9) :
    ∃ spec, cyclicExpanded.atomAt? index = some spec ∧
      spec.element = .H ∧ spec.element.atomicNumber = 1 := by
  obtain ⟨spec, lookup, aliphatic, _bondSum⟩ := fresh_hydrogen index low high
  refine ⟨spec, lookup, ?_, ?_⟩
  · simp [aliphatic, AtomSpec.aliphatic]
  · simp [aliphatic, AtomSpec.aliphatic, Element.atomicNumber]

/-- The four written root neighbors are H, F, C, C. The two carbons share atomic number 6. -/
theorem root_written_ligands_not_separated :
    ∃ hydrogen fluorine arm closing,
      cyclicExpanded.atomAt? 5 = some hydrogen ∧ hydrogen.element.atomicNumber = 1 ∧
      cyclicExpanded.atomAt? 1 = some fluorine ∧ fluorine.element.atomicNumber = 9 ∧
      cyclicExpanded.atomAt? 2 = some arm ∧ arm.element.atomicNumber = 6 ∧
      cyclicExpanded.atomAt? 4 = some closing ∧ closing.element.atomicNumber = 6 ∧
      cyclicExpanded.writtenNeighbors 0 = [5, 1, 2, 4] ∧
      arm.element.atomicNumber = closing.element.atomicNumber ∧
      2 ≠ 4 := by
  obtain ⟨hydrogen, hydrogenAt, _, hydrogenZ⟩ := hydrogenFive_source_atomicNumber
  obtain ⟨fluorine, fluorineAt, _, fluorineZ⟩ := fluorine_source_atomicNumber
  obtain ⟨arm, armAt, _, armZ⟩ := armCarbon_source_atomicNumber
  obtain ⟨closing, closingAt, _, closingZ⟩ := closingCarbon_source_atomicNumber
  refine ⟨hydrogen, fluorine, arm, closing, hydrogenAt, hydrogenZ, fluorineAt, fluorineZ,
    armAt, armZ, closingAt, closingZ, root_written_row, armZ.trans closingZ.symm, by decide⟩

/-- Written-neighbor atomic numbers one bond out from the two carbon ligands.
This is source inventory, not a retained-key order. -/
theorem carbon_branch_written_atomic_numbers :
    cyclicExpanded.writtenNeighbors 2 = [0, 6, 3, 4] ∧
      cyclicExpanded.writtenNeighbors 4 = [2, 7, 8, 0] ∧
      (∃ chlorine, cyclicExpanded.atomAt? 3 = some chlorine ∧
        chlorine.element.atomicNumber = 17) ∧
      (∃ hydrogen, cyclicExpanded.atomAt? 6 = some hydrogen ∧
        hydrogen.element.atomicNumber = 1) ∧
      (∃ hydrogen, cyclicExpanded.atomAt? 7 = some hydrogen ∧
        hydrogen.element.atomicNumber = 1) ∧
      (∃ hydrogen, cyclicExpanded.atomAt? 8 = some hydrogen ∧
        hydrogen.element.atomicNumber = 1) ∧
      (∃ carbon, cyclicExpanded.atomAt? 2 = some carbon ∧
        carbon.element.atomicNumber = 6) ∧
      (∃ carbon, cyclicExpanded.atomAt? 4 = some carbon ∧
        carbon.element.atomicNumber = 6) := by
  obtain ⟨chlorine, chlorineAt, _, chlorineZ⟩ := chlorine_source_atomicNumber
  obtain ⟨h6, h6At, _, h6Z⟩ := terminalHydrogen_source_atomicNumber 6 (by decide) (by decide)
  obtain ⟨h7, h7At, _, h7Z⟩ := terminalHydrogen_source_atomicNumber 7 (by decide) (by decide)
  obtain ⟨h8, h8At, _, h8Z⟩ := terminalHydrogen_source_atomicNumber 8 (by decide) (by decide)
  obtain ⟨arm, armAt, _, armZ⟩ := armCarbon_source_atomicNumber
  obtain ⟨closing, closingAt, _, closingZ⟩ := closingCarbon_source_atomicNumber
  refine ⟨arm_written_row, closing_written_row, ⟨chlorine, chlorineAt, chlorineZ⟩,
    ⟨h6, h6At, h6Z⟩, ⟨h7, h7At, h7Z⟩, ⟨h8, h8At, h8Z⟩,
    ⟨arm, armAt, armZ⟩, ⟨closing, closingAt, closingZ⟩⟩

/-- The four written root ligands have coordinates. Absence of geometry is not the gap. -/
theorem root_written_ligand_coordinates :
    cyclicSpatialCertified.spatialPointAt? (SA ⟨5, by decide⟩) = some P5 ∧
      cyclicSpatialCertified.spatialPointAt? (SA ⟨1, by decide⟩) = some P1 ∧
        cyclicSpatialCertified.spatialPointAt? (SA ⟨2, by decide⟩) = some P2 ∧
          cyclicSpatialCertified.spatialPointAt? (SA ⟨4, by decide⟩) = some P4 :=
  ⟨coordinate_lookup.2.2.2.2.2.1, coordinate_lookup.2.1, coordinate_lookup.2.2.1,
    coordinate_lookup.2.2.2.2.1⟩

end

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.spatialRoot_fuel
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.spatialRoot_provenance
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.spatialRoot_own_root
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.spatialRoot_address
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.spatialRoot_referenceState_eq_some_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.spatialRoot_referenceState_eq_none_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.hydrogenFive_source_atomicNumber
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.fluorine_source_atomicNumber
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.armCarbon_source_atomicNumber
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.closingCarbon_source_atomicNumber
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.chlorine_source_atomicNumber
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.terminalHydrogen_source_atomicNumber
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.root_written_ligands_not_separated
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.carbon_branch_written_atomic_numbers
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialDescriptorWitness.root_written_ligand_coordinates
