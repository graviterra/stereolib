import TetraStereo.OneCenter.LocalizedRootZAutomorphismLabelCovariance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter




































/-! ## Two-sign logic -/






theorem signLaw_eq_opposite_of_not_eq
    {A B L : ℝ}
    (hA : A = 1 ∨ A = -1) (hB : B = 1 ∨ B = -1) (hL : L = 1 ∨ L = -1)
    (mirror : Bool)
    (fails : ¬ A * L = (if mirror then (-1 : ℝ) else 1) * B) :
    A * L = (if (!mirror) then (-1 : ℝ) else 1) * B := by
  have flipped :
      (if (!mirror) then (-1 : ℝ) else 1) = -(if mirror then (-1 : ℝ) else 1) := by
    cases mirror <;> simp
  rw [flipped]
  rcases hA with rfl | rfl <;> rcases hB with rfl | rfl <;> rcases hL with rfl | rfl <;>
    cases mirror <;> norm_num at fails
  all_goals norm_num

/-! ## Actual positivity from calibrated physical geometry -/







theorem exists_chiral_referenceState_of_nondegenerateFrame
    (input : LocalizedUniversalReference.Input)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (target : LocalizedUniversalReference.Occurrence input)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame)
    (separated : input.certified.ConstitutionallyAtomicNumberSeparatedFrame frame)
    (center : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node center)
    (pointsAt : Fin 4 → CartesianPoint3)
    (spatial : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
        some (pointsAt index))
    (nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0) :
    ∃ rs : RS, LocalizedUniversalReference.referenceState input target = some (.chiral rs) := by
  have writtenParity :
      AuthoritativeChemicalInput.RationalTetrahedralInputParity
        [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3]
        (parityOfVolumeSign
          (rationalVolumeSign
            (CartesianPoint3.orientedVolume
              (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3)))) :=
    rationalTetrahedralInputParity_parityOfVolumeSign
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) nonzero
  obtain ⟨tracked, _computed, _pseudo, state⟩ :=
    referenceState_reader_eq_chiral_of_physicalFrame
      input noDouble target frame derived separated center centerReal pointsAt spatial
      (parityOfVolumeSign
        (rationalVolumeSign
          (CartesianPoint3.orientedVolume
            (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3))))
      writtenParity
  exact ⟨_, state⟩

/-! ## Exact label/sign equivalence -/


























theorem referenceState_rootZAutomorphism_label_sign_iff
    (input : LocalizedUniversalReference.Input)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (molEq : m.mol = input.certified.moleculeGraph)
    (cfg : m.Configuration) (d : m.Center) (e : m.Aut) (mirror : Bool)
    (t u : LocalizedUniversalReference.Occurrence input)
    (F G : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (derivedF : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame t F)
    (derivedG : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame u G)
    (separatedF : input.certified.ConstitutionallyAtomicNumberSeparatedFrame F)
    (separatedG : input.certified.ConstitutionallyAtomicNumberSeparatedFrame G)
    (centerF centerU : input.certified.TetrahedralCenter)
    (centerRealF : input.certified.RealTetrahedralCenterNode t.1.node centerF)
    (centerRealU : input.certified.RealTetrahedralCenterNode u.1.node centerU)
    (centerF_at : centerF.1 = d.1)
    (centerU_at : centerU.1 = (m.centerPerm e d).1)
    (alphaF alphaG : Equiv.Perm (Fin 4))
    (matchF : ActualFrameLigandMatch input m F d alphaF)
    (matchG : ActualFrameLigandMatch input m G (m.centerPerm e d) alphaG)
    (pointsF pointsU : Fin 4 → CartesianPoint3)
    (spatialF : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (F.cursorAt index) =
        some (pointsF index))
    (spatialU : ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (G.cursorAt index) =
        some (pointsU index))
    (calibrationF : PhysicalFrameCalibration m cfg d alphaF pointsF)
    (calibrationU : PhysicalFrameCalibration m cfg (m.centerPerm e d) alphaG pointsU) :
    LocalizedUniversalReference.referenceState input u =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input t) ↔
    m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
      (if mirror then -1 else 1) *
        m.configurationSign cfg (m.centerPerm e d) := by
  constructor
  · -- Actual label relation `→` physical sign law.  No desired sign is assumed.
    intro stateEq
    by_contra signFails
    have hA : m.configurationSign cfg d = 1 ∨ m.configurationSign cfg d = -1 :=
      permHandedness_eq_one_or_eq_neg_one (cfg d)
    have hB :
        m.configurationSign cfg (m.centerPerm e d) = 1 ∨
          m.configurationSign cfg (m.centerPerm e d) = -1 :=
      permHandedness_eq_one_or_eq_neg_one (cfg (m.centerPerm e d))
    have hL :
        permHandedness (m.ligandPermAt e d) = 1 ∨
          permHandedness (m.ligandPermAt e d) = -1 :=
      permHandedness_eq_one_or_eq_neg_one (m.ligandPermAt e d)
    have oppositeSignLaw :
        m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
          (if (!mirror) then (-1 : ℝ) else 1) *
            m.configurationSign cfg (m.centerPerm e d) :=
      signLaw_eq_opposite_of_not_eq hA hB hL mirror signFails
    have oppositeState :
        LocalizedUniversalReference.referenceState input u =
          (if (!mirror) then
              CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel
            else id)
            (LocalizedUniversalReference.referenceState input t) :=
      referenceState_rootZAutomorphism_label_covariance
        input noDouble m molEq cfg d e (!mirror) t u F G derivedF derivedG
        separatedF separatedG centerF centerU centerRealF centerRealU centerF_at centerU_at
        alphaF alphaG matchF matchG pointsF pointsU spatialF spatialU calibrationF calibrationU
        oppositeSignLaw
    have statesAgree :
        (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
            (LocalizedUniversalReference.referenceState input t) =
          (if (!mirror) then
              CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel
            else id)
            (LocalizedUniversalReference.referenceState input t) :=
      stateEq.symm.trans oppositeState
    have reflected :
        LocalizedUniversalReference.referenceState input t =
          CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel
            (LocalizedUniversalReference.referenceState input t) := by
      cases mirror with
      | false => simpa using statesAgree
      | true => simpa using statesAgree.symm
    obtain ⟨rs, rsEq⟩ :=
      exists_chiral_referenceState_of_nondegenerateFrame
        input noDouble t F derivedF separatedF centerF centerRealF pointsF spatialF
        calibrationF.written_nondegenerate
    rw [rsEq] at reflected
    cases rs <;>
      simp [CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel,
        CertifiedLocalizedCIPInput.reflectUppercaseAuxiliaryLabel, RS.swap] at reflected
  ·
    intro signLaw
    exact referenceState_rootZAutomorphism_label_covariance
      input noDouble m molEq cfg d e mirror t u F G derivedF derivedG
      separatedF separatedG centerF centerU centerRealF centerRealU centerF_at centerU_at
      alphaF alphaG matchF matchG pointsF pointsU spatialF spatialU calibrationF calibrationU
      signLaw

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.signLaw_eq_opposite_of_not_eq
assert_kernel_only TetraStereo.OneCenter.exists_chiral_referenceState_of_nondegenerateFrame
assert_kernel_only TetraStereo.OneCenter.referenceState_rootZAutomorphism_label_sign_iff

end TetraStereo.OneCenter
