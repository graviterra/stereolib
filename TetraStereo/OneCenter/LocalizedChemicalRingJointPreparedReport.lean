import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedRootPhysicalPairCount
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1800000

/-! Whole detected-center report for the prepared joint-context evaluator.
The report calls that evaluator itself and retains refusals. Its candidate inventory is
exact and duplicate-free without physical assumptions. At every properly distinguishable
center the proved physical root theorem supplies success and the exact lowercase criterion.
This does not change the public evaluator's default or prove IUPAC reference-policy fidelity. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingJointMarkerOperations (jointOperations)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingPreparedContextRecursion (preparedAssignCenter?)
open LocalizedChemicalRingJointPreparedRootPhysicalPairCount
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)
open MultiCenterMolecule (PairwiseProperDistinguishable)

noncomputable section
open scoped Classical

abbrev Report := List (Nat × Option LocalizedAuxiliaryLabel)

/-- Evaluate every actual detected candidate once, in semantic atom-index order.
`none` remains a report entry instead of silently dropping an unassigned candidate. -/
def analyze (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) : Report :=
  input.canonicalTetrahedralCenters.map fun center =>
    (center.1.val, preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input) center.1.val)

theorem analyze_center_indices (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) :
    (analyze input mol).map Prod.fst =
      input.canonicalTetrahedralCenters.map (fun center => center.1.val) := by
  simp [analyze, List.map_map]

theorem analyze_indices_nodup (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) :
    ((analyze input mol).map Prod.fst).Nodup := by
  rw [analyze_center_indices]
  unfold canonicalTetrahedralCenters
  simp only [List.map_map, Function.comp_def, List.attach_map_val]
  exact (Finset.sort_nodup input.tetrahedralCenterSet (· ≤ ·)).map
    (fun _ _ h => Fin.ext h)

theorem analyze_length (input : CertifiedLocalizedCIPInput) (mol : RawMolecule) :
    (analyze input mol).length = input.tetrahedralCenterSet.card := by
  rw [analyze, List.length_map]
  unfold canonicalTetrahedralCenters
  rw [List.length_map, List.length_attach, Finset.length_sort]

theorem mem_analyze_iff (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (atom : Nat) (outcome : Option LocalizedAuxiliaryLabel) :
    (atom, outcome) ∈ analyze input mol ↔
      ∃ center : input.TetrahedralCenter, center.1.val = atom ∧
        preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input)
          center.1.val = outcome := by
  constructor
  · intro member
    obtain ⟨center, _, equal⟩ := List.mem_map.mp member
    exact ⟨center, congrArg Prod.fst equal, congrArg Prod.snd equal⟩
  · rintro ⟨center, atomEq, outcomeEq⟩
    exact List.mem_map.mpr ⟨center,
      (input.mem_canonicalTetrahedralCenters_iff center).mpr center.2,
      Prod.ext atomEq outcomeEq⟩

theorem mem_analyze_at_center_iff (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
    (center : input.detectedMultiCenterMolecule.Center) (outcome : Option LocalizedAuxiliaryLabel) :
    (center.1.val, outcome) ∈ analyze input mol ↔
      preparedAssignCenter? mol (jointOperations input mol) (inputGeometry input)
        center.1.val = outcome := by
  rw [mem_analyze_iff]
  constructor
  · rintro ⟨other, same, computed⟩
    have equal : other = center := Subtype.ext (Fin.ext same)
    subst other
    exact computed
  · intro computed
    exact ⟨center, rfl, computed⟩

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)
  (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
  (cfg : input.detectedMultiCenterMolecule.Configuration)
  (calibrated : ∀ d : input.detectedMultiCenterMolecule.Center,
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg d)

include agreement admissible supported single charge calibrated in
/-- Every properly distinguishable detected center appears with a physically classified label.
No rerooted success, auxiliary label, key order or selected reference is supplied. -/
theorem detected_entry_physical
    (center : input.detectedMultiCenterMolecule.Center)
    (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg center) :
    ∃ descriptor, (center.1.val, some descriptor) ∈ analyze input mol ∧
      (descriptor.IsLowercase ↔
        physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg center = 1) := by
  obtain ⟨descriptor, computed, physical⟩ := assignCenter_success_lowercase_iff input mol
    agreement admissible supported single charge cfg calibrated center properDistinct
  exact ⟨descriptor, (mem_analyze_at_center_iff input mol center _).mpr computed, physical⟩

include agreement admissible supported single charge calibrated in
/-- The same report entry carries the exact absolute coordinate/key letter as well as the
independent physical lowercase count. The auxiliary-policy fidelity question stays separate. -/
theorem detected_entry_classification
    (center : input.detectedMultiCenterMolecule.Center)
    (properDistinct : PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg center) :
    ∃ (data : LocalizedChemicalRingInheritedRefusalCases.OccurrenceData input mol center
        (canonicalCenterRoot center.1.val)) (_rootAddress : data.target.1.address = []),
      (center.1.val, some (classifyTetrahedralRSPseudo
        (LocalizedChemicalRingPhysicalSense.letterOfSign
          (input.detectedMultiCenterMolecule.configurationSign cfg center *
            permHandedness (LocalizedChemicalRingJointPreparedRootEmptyContext.ordinaryGeometryRank
              input single mol center (canonicalCenterRoot center.1.val) data false)))
        (physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg center))) ∈
      analyze input mol := by
  obtain ⟨data, rootAddress, computed⟩ := assignCenter_eq_physical_classification input mol
    agreement admissible supported single charge cfg calibrated center properDistinct
  exact ⟨data, rootAddress, (mem_analyze_at_center_iff input mol center _).mpr computed⟩

include agreement admissible supported single charge calibrated in
/-- If every detected center satisfies the physical assignment domain, the complete report has
no refusals; its literal entries, not a second result list, satisfy the physical criterion. -/
theorem all_entries_physical
    (properDistinct : ∀ center : input.detectedMultiCenterMolecule.Center,
      PairwiseProperDistinguishable input.detectedMultiCenterMolecule cfg center) :
    ∀ atom outcome, (atom, outcome) ∈ analyze input mol →
      ∃ (center : input.detectedMultiCenterMolecule.Center) (descriptor : LocalizedAuxiliaryLabel),
        center.1.val = atom ∧ outcome = some descriptor ∧
        (descriptor.IsLowercase ↔
          physicalEnantiomorphicPairCount input.detectedMultiCenterMolecule cfg center = 1) := by
  intro atom outcome member
  obtain ⟨center, atomEq, computed⟩ := (mem_analyze_iff input mol atom outcome).mp member
  obtain ⟨descriptor, assigned, physical⟩ := assignCenter_success_lowercase_iff input mol
    agreement admissible supported single charge cfg calibrated center (properDistinct center)
  exact ⟨center, descriptor, atomEq, computed.symm.trans assigned, physical⟩

end
end TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport.analyze_center_indices
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport.analyze_indices_nodup
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport.analyze_length
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport.mem_analyze_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport.mem_analyze_at_center_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport.detected_entry_physical
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport.all_entries_physical

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedReport.detected_entry_classification
