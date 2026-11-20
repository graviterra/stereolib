import TetraStereo.OneCenter.LocalizedActualPhysicalBranchDecision
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Checked coordinate admission for the current ring physical domain. The executable gate
rejects missing or zero-volume ligand coordinates at any detected center. Its configuration
certificate uses proof-level frame reindexing; physical admission rejection is not evaluator
refusal and this module makes no assignment or source-policy claim. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingPhysicalAdmission

open CertifiedLocalizedCIPInput CartesianPoint3
open LocalizedActualPhysicalBranchDecision
open LocalizedRecursiveAuxiliaryPhysicalDomain (ActualPhysicalCalibratedCoordinates)

/-- Executable check of the canonical coordinate frame at one detected center. -/
def centerAdmitted (input : CertifiedLocalizedCIPInput)
    (c : (actualCanonicalMolecule input).Center) : Bool :=
  match coordinateVolume? input c with
  | none => false
  | some volume => decide (volume ≠ 0)

/-- Executable all-center admission; no frame reindexing choice is evaluated here. -/
def allCentersAdmitted (input : CertifiedLocalizedCIPInput) : Bool :=
  decide (∀ c : (actualCanonicalMolecule input).Center, centerAdmitted input c = true)

/-- Computational admission status, independent of any descriptor evaluator. -/
def physicalAdmission? (input : CertifiedLocalizedCIPInput) : Option Unit :=
  if allCentersAdmitted input then some () else none

theorem centerAdmitted_iff (input : CertifiedLocalizedCIPInput)
    (c : (actualCanonicalMolecule input).Center) :
    centerAdmitted input c = true ↔
      ∃ volume, coordinateVolume? input c = some volume ∧ volume ≠ 0 := by
  cases found : coordinateVolume? input c <;> simp [centerAdmitted, found]

/-- The gate is exactly the declared present/nonzero-coordinate domain at every center. -/
theorem allCentersAdmitted_iff (input : CertifiedLocalizedCIPInput) :
    allCentersAdmitted input = true ↔
      ∀ c : (actualCanonicalMolecule input).Center,
        ∃ volume, coordinateVolume? input c = some volume ∧ volume ≠ 0 := by
  simp only [allCentersAdmitted, decide_eq_true_eq, centerAdmitted_iff]

theorem physicalAdmission_accept_iff (input : CertifiedLocalizedCIPInput) :
    physicalAdmission? input = some () ↔
      ∀ c : (actualCanonicalMolecule input).Center,
        ∃ volume, coordinateVolume? input c = some volume ∧ volume ≠ 0 := by
  simp only [physicalAdmission?]
  split <;> simp_all [allCentersAdmitted_iff]

/-- Rejection supplies a concrete bad detected center, including the missing-coordinate case. -/
theorem physicalAdmission_reject_iff (input : CertifiedLocalizedCIPInput) :
    physicalAdmission? input = none ↔
      ∃ c : (actualCanonicalMolecule input).Center,
        coordinateVolume? input c = none ∨ coordinateVolume? input c = some 0 := by
  classical
  have centerBad (c : (actualCanonicalMolecule input).Center) :
      (¬ ∃ volume, coordinateVolume? input c = some volume ∧ volume ≠ 0) ↔
        coordinateVolume? input c = none ∨ coordinateVolume? input c = some 0 := by
    cases coordinateVolume? input c <;> simp
  have rejected : physicalAdmission? input = none ↔ allCentersAdmitted input ≠ true := by
    simp [physicalAdmission?]
  rw [rejected]
  change (¬ allCentersAdmitted input = true) ↔ _
  rw [allCentersAdmitted_iff, not_forall]
  simp only [centerBad]

/-- A successful volume computation exposes all four actual coordinates. -/
theorem points_of_volume (input : CertifiedLocalizedCIPInput)
    (c : (actualCanonicalMolecule input).Center) (volume : ℚ)
    (found : coordinateVolume? input c = some volume) :
    ∃ points : Fin 4 → CartesianPoint3,
      (∀ i, input.spatialPointAt? ((actualCanonicalMolecule input).ligandAtomAt c i) =
        some (points i)) ∧
      orientedVolume (points 0) (points 1) (points 2) (points 3) = volume := by
  cases h0 : input.spatialPointAt? ((actualCanonicalMolecule input).ligandAtomAt c 0) with
  | none => simp [coordinateVolume?, h0] at found
  | some p0 =>
    cases h1 : input.spatialPointAt? ((actualCanonicalMolecule input).ligandAtomAt c 1) with
    | none => simp [coordinateVolume?, h0, h1] at found
    | some p1 =>
      cases h2 : input.spatialPointAt? ((actualCanonicalMolecule input).ligandAtomAt c 2) with
      | none => simp [coordinateVolume?, h0, h1, h2] at found
      | some p2 =>
        cases h3 : input.spatialPointAt? ((actualCanonicalMolecule input).ligandAtomAt c 3) with
        | none => simp [coordinateVolume?, h0, h1, h2, h3] at found
        | some p3 =>
          refine ⟨![p0, p1, p2, p3], ?_, ?_⟩
          · intro i
            fin_cases i <;> simp [h0, h1, h2, h3]
          · simpa [coordinateVolume?, h0, h1, h2, h3] using found

/-- Canonical calibration is derived only after the actual coordinate gate succeeds. -/
theorem canonical_all_calibrated (input : CertifiedLocalizedCIPInput)
    (accepted : allCentersAdmitted input = true) (c : (actualCanonicalMolecule input).Center) :
    ActualPhysicalCalibratedCoordinates input (actualCanonicalMolecule input) (coordinateCfg input) c := by
  obtain ⟨volume, found, nonzero⟩ := (allCentersAdmitted_iff input).mp accepted c
  obtain ⟨points, observed, actualVolume⟩ := points_of_volume input c volume found
  exact coordinateCfg_calibrated input c points observed (by rw [actualVolume]; exact nonzero)

/-- Calibration transports across any frame permutation, independently of descriptor output. -/
theorem calibration_reindexed (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom) (cfg : m.Configuration)
    (change : m.Center → Equiv.Perm (Fin 4)) (c : m.Center)
    (calibrated : ActualPhysicalCalibratedCoordinates input m cfg c) :
    ActualPhysicalCalibratedCoordinates input (m.reindexFrames change)
      (m.reindexConfiguration change cfg) c := by
  obtain ⟨P, seen, nonzero, sign⟩ := calibrated
  refine ⟨fun i => P (change c i), ?_, ?_, ?_⟩
  · intro i
    rw [MultiCenterMolecule.reindexFrames_ligandAtomAt]
    exact seen _
  · exact cartesianOrientedVolume_perm_ne_zero P (change c) nonzero
  · have vec : ∀ k : Fin 4,
        RationalTetrahedralPermutation.pointVector (P 0) (P 1) (P 2) (P 3) k = P k := by
      intro k
      fin_cases k <;> rfl
    have volume : RationalTetrahedralPermutation.permutedOrientedVolume
        (P 0) (P 1) (P 2) (P 3) (change c) =
        orientedVolume (P (change c 0)) (P (change c 1))
          (P (change c 2)) (P (change c 3)) := by
      simp only [RationalTetrahedralPermutation.permutedOrientedVolume, vec]
    rw [← volume, rationalVolumeSign_permutedOrientedVolume, sign,
      MultiCenterMolecule.configurationSign_reindexConfiguration]

noncomputable section

/-- A canonical-to-detected frame change. It belongs to proof construction, not the executable gate. -/
def frameChange (input : CertifiedLocalizedCIPInput) :
    (actualCanonicalMolecule input).Center → Equiv.Perm (Fin 4) :=
  Classical.choose (exists_canonical_reindex input)

theorem frameChange_spec (input : CertifiedLocalizedCIPInput) :
    (actualCanonicalMolecule input).reindexFrames (frameChange input) =
      input.detectedMultiCenterMolecule := Classical.choose_spec (exists_canonical_reindex input)

/-- Actual detected-frame configuration constructed from coordinates and frame correspondence. -/
def detectedCoordinateCfg (input : CertifiedLocalizedCIPInput) :
    input.detectedMultiCenterMolecule.Configuration :=
  Eq.mp (congrArg MultiCenterMolecule.Configuration (frameChange_spec input))
    ((actualCanonicalMolecule input).reindexConfiguration (frameChange input) (coordinateCfg input))

/-- Acceptance discharges the all-center physical calibration hypothesis on the actual frames. -/
theorem detected_all_calibrated (input : CertifiedLocalizedCIPInput)
    (accepted : allCentersAdmitted input = true) (c : input.detectedMultiCenterMolecule.Center) :
    ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule
      (detectedCoordinateCfg input) c := by
  let c' : (actualCanonicalMolecule input).Center := ⟨c.1, c.2⟩
  have transferred : Eq.mp (congrArg MultiCenterMolecule.Center (frameChange_spec input)) c' = c := by
    have center_val {m n : MultiCenterMolecule input.Atom} (h : m = n) (d : m.Center) :
        (Eq.mp (congrArg MultiCenterMolecule.Center h) d).1 = d.1 := by cases h; rfl
    exact Subtype.ext (center_val (frameChange_spec input) c')
  have transport {m n : MultiCenterMolecule input.Atom} (h : m = n)
      (configuration : m.Configuration) (d : m.Center)
      (hcal : ActualPhysicalCalibratedCoordinates input m configuration d) :
      ActualPhysicalCalibratedCoordinates input n
        (Eq.mp (congrArg MultiCenterMolecule.Configuration h) configuration)
        (Eq.mp (congrArg MultiCenterMolecule.Center h) d) := by
    cases h
    exact hcal
  simpa only [detectedCoordinateCfg, transferred] using transport (frameChange_spec input)
    ((actualCanonicalMolecule input).reindexConfiguration (frameChange input) (coordinateCfg input)) c'
    (calibration_reindexed input _ _ _ c' (canonical_all_calibrated input accepted c'))

/-- Physical evidence returned after admission. This is a proof-level certificate. -/
structure PhysicalCertificate (input : CertifiedLocalizedCIPInput) where
  cfg : input.detectedMultiCenterMolecule.Configuration
  calibrated : ∀ c, ActualPhysicalCalibratedCoordinates input input.detectedMultiCenterMolecule cfg c

/-- A checked proof-level certificate; rejection remains separate from evaluator refusal. -/
def checkedPhysicalCertificate? (input : CertifiedLocalizedCIPInput) : Option (PhysicalCertificate input) :=
  if accepted : allCentersAdmitted input = true then
    some ⟨detectedCoordinateCfg input, detected_all_calibrated input accepted⟩
  else none

theorem checkedPhysicalCertificate_isSome_iff (input : CertifiedLocalizedCIPInput) :
    (checkedPhysicalCertificate? input).isSome = true ↔ allCentersAdmitted input = true := by
  unfold checkedPhysicalCertificate?
  split <;> simp_all

end
end TetraStereo.OneCenter.LocalizedChemicalRingPhysicalAdmission

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalAdmission.centerAdmitted_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalAdmission.allCentersAdmitted_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalAdmission.physicalAdmission_accept_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalAdmission.physicalAdmission_reject_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalAdmission.points_of_volume
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalAdmission.canonical_all_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalAdmission.calibration_reindexed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalAdmission.detected_all_calibrated
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPhysicalAdmission.checkedPhysicalCertificate_isSome_iff
