import TetraStereo.OneCenter.LocalizedAcyclicPhysicalPseudoFidelity
import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Key
import TetraStereo.OneCenter.MultiCenterConfiguration
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false

namespace TetraStereo.OneCenter






























/-! ## The physical sign of an exact rational oriented volume -/

/-- The sign of an exact rational oriented volume as a real number in `{-1, 0, 1}`. -/
def rationalVolumeSign (volume : ℚ) : ℝ :=
  if volume < 0 then -1 else if 0 < volume then 1 else 0

theorem rationalVolumeSign_of_neg {volume : ℚ} (negative : volume < 0) :
    rationalVolumeSign volume = -1 := by
  simp [rationalVolumeSign, negative]

theorem rationalVolumeSign_of_pos {volume : ℚ} (positive : 0 < volume) :
    rationalVolumeSign volume = 1 := by
  have notNegative : ¬ volume < 0 := not_lt_of_ge positive.le
  simp [rationalVolumeSign, notNegative, positive]

theorem rationalVolumeSign_eq_neg_iff_of_ne {volume : ℚ} (nonzero : volume ≠ 0) :
    rationalVolumeSign volume = -1 ↔ volume < 0 := by
  constructor
  · intro equal
    by_contra notNegative
    have positive : 0 < volume :=
      lt_of_le_of_ne (le_of_not_gt notNegative) (Ne.symm nonzero)
    rw [rationalVolumeSign_of_pos positive] at equal
    norm_num at equal
  · exact rationalVolumeSign_of_neg

theorem rationalVolumeSign_eq_one_iff_of_ne {volume : ℚ} (nonzero : volume ≠ 0) :
    rationalVolumeSign volume = 1 ↔ 0 < volume := by
  constructor
  · intro equal
    by_contra notPositive
    have negative : volume < 0 :=
      lt_of_le_of_ne (le_of_not_gt notPositive) nonzero
    rw [rationalVolumeSign_of_neg negative] at equal
    norm_num at equal
  · exact rationalVolumeSign_of_pos

theorem rationalVolumeSign_eq_neg_or_one {volume : ℚ} (nonzero : volume ≠ 0) :
    rationalVolumeSign volume = -1 ∨ rationalVolumeSign volume = 1 := by
  rcases lt_trichotomy volume 0 with negative | zero | positive
  · exact Or.inl (rationalVolumeSign_of_neg negative)
  · exact absurd zero nonzero
  · exact Or.inr (rationalVolumeSign_of_pos positive)

theorem rationalVolumeSign_neg (volume : ℚ) :
    rationalVolumeSign (-volume) = -rationalVolumeSign volume := by
  rcases lt_trichotomy volume 0 with negative | zero | positive
  · have positive' : 0 < -volume := by linarith
    rw [rationalVolumeSign_of_neg negative, rationalVolumeSign_of_pos positive']
    norm_num
  · subst volume
    simp [rationalVolumeSign]
  · have negative' : -volume < 0 := by linarith
    rw [rationalVolumeSign_of_pos positive, rationalVolumeSign_of_neg negative']

/-- The real factor by which an even/odd Boolean of the production inversion parity scales a
signed volume. -/
def parityFactor (even : Bool) : ℝ :=
  if even then 1 else -1

theorem parityFactor_eq_one_or_neg_one (even : Bool) :
    parityFactor even = 1 ∨ parityFactor even = -1 := by
  cases even <;> simp [parityFactor]

theorem rationalVolumeSign_if {volume : ℚ} (even : Bool) :
    rationalVolumeSign (if even then volume else -volume) =
      rationalVolumeSign volume * parityFactor even := by
  cases even with
  | false =>
      simp only [Bool.false_eq_true, if_false, parityFactor]
      rw [rationalVolumeSign_neg]
      ring
  | true =>
      simp [parityFactor]

/-- The production inversion parity Boolean is the group-theoretic sign, expressed as the real
factor `±1`. -/
theorem parityFactor_permutationIsEven (permutation : Equiv.Perm (Fin 4)) :
    parityFactor
      (RawMolecule.permutationIsEven
        (Rule6HandednessSemantics.finFourPermutationList permutation)) =
      permHandedness permutation := by
  rw [Rule6HandednessSemantics.finFourPermutationIsEven_eq_sign]
  rcases Int.units_eq_one_or (Equiv.Perm.sign permutation) with signEq | signEq
  · simp [parityFactor, permHandedness, signEq]
  · simp [parityFactor, permHandedness, signEq]

/-- The written-order sign of a permuted exact frame is the original sign scaled by the sign of the
permutation.  No nondegeneracy is needed. -/
theorem rationalVolumeSign_permutedOrientedVolume
    (first second third fourth : CartesianPoint3) (permutation : Equiv.Perm (Fin 4)) :
    rationalVolumeSign
      (RationalTetrahedralPermutation.permutedOrientedVolume
        first second third fourth permutation) =
      rationalVolumeSign
        (CartesianPoint3.orientedVolume first second third fourth) *
        permHandedness permutation := by
  rw [RationalTetrahedralPermutation.permutedOrientedVolume_eq_if_permutationIsEven,
    rationalVolumeSign_if, parityFactor_permutationIsEven]

/-- Reindexing the physical points through an `S₄` permutation gives the corresponding permuted
oriented volume. -/
theorem orientedVolume_calibrated_eq
    (pointsAt physicalPointAt : Fin 4 → CartesianPoint3)
    (permutation : Equiv.Perm (Fin 4))
    (calibrated : ∀ index, pointsAt index = physicalPointAt (permutation index)) :
    CartesianPoint3.orientedVolume (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) =
      RationalTetrahedralPermutation.permutedOrientedVolume
        (physicalPointAt 0) (physicalPointAt 1) (physicalPointAt 2) (physicalPointAt 3)
        permutation := by
  have pointVectorEq : ∀ index : Fin 4,
      RationalTetrahedralPermutation.pointVector
        (physicalPointAt 0) (physicalPointAt 1) (physicalPointAt 2) (physicalPointAt 3)
        index = physicalPointAt index := by
    intro index
    fin_cases index <;> rfl
  rw [calibrated 0, calibrated 1, calibrated 2, calibrated 3]
  simp [RationalTetrahedralPermutation.permutedOrientedVolume, pointVectorEq]

/-! ## The written-order parity chosen by a nondegenerate volume -/

/-- The parity constructor determined by a nonzero written-order sign. -/
noncomputable def parityOfVolumeSign (sign : ℝ) : TetrahedralInputParity :=
  if sign = -1 then .clockwise else .anticlockwise

theorem ofHandedness_parityFactor_clockwise (even : Bool) :
    RS.ofHandedness ((-1 : ℝ) * parityFactor even) =
      RawMolecule.descriptorOfParity .clockwise even := by
  cases even <;>
    norm_num [parityFactor, RawMolecule.descriptorOfParity, RS.ofHandedness]

theorem ofHandedness_parityFactor_anticlockwise (even : Bool) :
    RS.ofHandedness ((1 : ℝ) * parityFactor even) =
      RawMolecule.descriptorOfParity .anticlockwise even := by
  cases even <;>
    norm_num [parityFactor, RawMolecule.descriptorOfParity, RS.ofHandedness]

/-- A nonzero rational oriented volume realizes exactly the parity constructor selected by its
sign. -/
theorem rationalTetrahedralInputParity_parityOfVolumeSign
    (first second third fourth : CartesianPoint3)
    (nonzero : CartesianPoint3.orientedVolume first second third fourth ≠ 0) :
    AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [first, second, third, fourth]
      (parityOfVolumeSign
        (rationalVolumeSign
          (CartesianPoint3.orientedVolume first second third fourth))) := by
  unfold AuthoritativeChemicalInput.RationalTetrahedralInputParity
  refine ⟨first, second, third, fourth, rfl, ?_⟩
  by_cases negativeSign :
      rationalVolumeSign (CartesianPoint3.orientedVolume first second third fourth) = -1
  · have negative :
        CartesianPoint3.orientedVolume first second third fourth < 0 :=
      (rationalVolumeSign_eq_neg_iff_of_ne nonzero).mp negativeSign
    simp [parityOfVolumeSign, negativeSign, negative]
  · have positiveSign :
        rationalVolumeSign (CartesianPoint3.orientedVolume first second third fourth) = 1 := by
      rcases rationalVolumeSign_eq_neg_or_one nonzero with lower | one
      · exact absurd lower negativeSign
      · exact one
    have positive :
        0 < CartesianPoint3.orientedVolume first second third fourth :=
      (rationalVolumeSign_eq_one_iff_of_ne nonzero).mp positiveSign
    simp [parityOfVolumeSign, negativeSign, positive]

/-- The production parity descriptor of a nonzero written frame is the calibrated handedness sign
times the inversion-parity factor. -/
theorem descriptorOfParity_parityOfVolumeSign
    (first second third fourth : CartesianPoint3)
    (nonzero : CartesianPoint3.orientedVolume first second third fourth ≠ 0)
    (even : Bool) :
    RawMolecule.descriptorOfParity
      (parityOfVolumeSign
        (rationalVolumeSign
          (CartesianPoint3.orientedVolume first second third fourth)))
      even =
      RS.ofHandedness
        (rationalVolumeSign
          (CartesianPoint3.orientedVolume first second third fourth) *
          parityFactor even) := by
  by_cases negativeSign :
      rationalVolumeSign (CartesianPoint3.orientedVolume first second third fourth) = -1
  · have parityEq : parityOfVolumeSign
        (rationalVolumeSign
          (CartesianPoint3.orientedVolume first second third fourth)) = .clockwise := by
      simp [parityOfVolumeSign, negativeSign]
    rw [parityEq, negativeSign]
    exact (ofHandedness_parityFactor_clockwise even).symm
  · have positiveSign :
        rationalVolumeSign (CartesianPoint3.orientedVolume first second third fourth) = 1 := by
      rcases rationalVolumeSign_eq_neg_or_one nonzero with lower | one
      · exact absurd lower negativeSign
      · exact one
    have parityEq : parityOfVolumeSign
        (rationalVolumeSign
          (CartesianPoint3.orientedVolume first second third fourth)) = .anticlockwise := by
      simp [parityOfVolumeSign, negativeSign]
    rw [parityEq, positiveSign]
    exact (ofHandedness_parityFactor_anticlockwise even).symm

/-! ## Pure sorting-parity covariance -/

/-- A four-element list whose `Fin.val` image is the production permutation list of `q` is exactly
`List.ofFn q`. -/
private theorem ofFn_eq_of_map_val_eq
    {q : Equiv.Perm (Fin 4)} {list : List (Fin 4)}
    (lengthEq : list.length = 4)
    (mapEq : list.map Fin.val =
      Rule6HandednessSemantics.finFourPermutationList q) :
    list = List.ofFn q := by
  let getAt : Fin 4 → Fin 4 := fun index => list[Fin.cast lengthEq.symm index]
  have mapValEq : (fun index : Fin 4 => (getAt index).val) =
      fun index : Fin 4 => (q index).val := by
    apply List.ofFn_inj.mp
    calc
      List.ofFn (fun index : Fin 4 => (getAt index).val)
          = List.ofFn
              (fun index : Fin 4 => (list[Fin.cast lengthEq.symm index]).val) := rfl
      _ = list.map Fin.val := by
            refine (List.ofFn_congr lengthEq
              (fun index : Fin list.length => (list[index]).val)).symm.trans ?_
            exact List.ofFn_getElem_eq_map list Fin.val
      _ = Rule6HandednessSemantics.finFourPermutationList q := mapEq
      _ = List.ofFn (fun index : Fin 4 => (q index).val) := rfl
  have getAtEq : getAt = q := funext fun index => Fin.ext (congrFun mapValEq index)
  calc
    list = List.ofFn (fun index : Fin list.length => list[index]) := by
      simp
    _ = List.ofFn getAt :=
      List.ofFn_congr lengthEq (fun index : Fin list.length => list[index])
    _ = List.ofFn q := by rw [getAtEq]


noncomputable def trackedPriorityOrdering (tracked : TrackedLocalizedLigandOrder)
    (permutation : tracked.highestFirst.Perm (List.finRange 4)) :
    Equiv.Perm (Fin 4) :=
  Rule6HandednessSemantics.finFourEquivOfPermutationList
    (tracked.highestFirst.map Fin.val)
    (by
      simpa [List.map_coe_finRange_eq_range] using permutation.map Fin.val)

theorem trackedPriorityOrdering_list (tracked : TrackedLocalizedLigandOrder)
    (permutation : tracked.highestFirst.Perm (List.finRange 4)) :
    Rule6HandednessSemantics.finFourPermutationList
      (trackedPriorityOrdering tracked permutation) =
      tracked.highestFirst.map Fin.val :=
  Rule6HandednessSemantics.finFourPermutationList_equivOfPermutationList _ _

/-- The tracked list is exactly `List.ofFn` of its priority ordering. -/
theorem ofFn_trackedPriorityOrdering (tracked : TrackedLocalizedLigandOrder)
    (permutation : tracked.highestFirst.Perm (List.finRange 4)) :
    List.ofFn (trackedPriorityOrdering tracked permutation) = tracked.highestFirst := by
  have lengthEq : tracked.highestFirst.length = 4 := by
    simpa using permutation.length_eq
  exact (ofFn_eq_of_map_val_eq lengthEq
    (trackedPriorityOrdering_list tracked permutation).symm).symm



theorem parityFactor_permutationIsEven_map
    (list : List (Fin 4)) (permutation : Equiv.Perm (Fin 4))
    (permutationList : list.Perm (List.finRange 4)) :
    parityFactor
      (RawMolecule.permutationIsEven ((list.map permutation).map Fin.val)) =
      permHandedness permutation *
        parityFactor (RawMolecule.permutationIsEven (list.map Fin.val)) := by
  have mapPermutation : List.Perm (list.map Fin.val) (List.range 4) := by
    have mapped := permutationList.map Fin.val
    simpa [List.map_coe_finRange_eq_range] using mapped
  let ordering : Equiv.Perm (Fin 4) :=
    Rule6HandednessSemantics.finFourEquivOfPermutationList
      (list.map Fin.val) mapPermutation
  have orderingList :
      Rule6HandednessSemantics.finFourPermutationList ordering =
        list.map Fin.val :=
    Rule6HandednessSemantics.finFourPermutationList_equivOfPermutationList _ _
  have lengthEq : list.length = 4 := by simpa using permutationList.length_eq
  have listOfFn : list = List.ofFn ordering :=
    ofFn_eq_of_map_val_eq lengthEq orderingList.symm
  have leftEq : (list.map permutation).map Fin.val =
      Rule6HandednessSemantics.finFourPermutationList (permutation * ordering) := by
    calc
      (list.map permutation).map Fin.val
          = ((List.ofFn ordering).map permutation).map Fin.val := by rw [listOfFn]
      _ = (List.ofFn (fun index : Fin 4 => permutation (ordering index))).map Fin.val := by
            simp only [List.map_ofFn, Function.comp_apply]
            exact List.ofFn_inj.mpr (by funext index; rfl)
      _ = List.ofFn (fun index : Fin 4 => (permutation (ordering index)).val) := by
            simp only [List.map_ofFn, Function.comp_apply]
            exact List.ofFn_inj.mpr (by funext index; rfl)
      _ = Rule6HandednessSemantics.finFourPermutationList (permutation * ordering) := rfl
  have rightEq : list.map Fin.val =
      Rule6HandednessSemantics.finFourPermutationList ordering := orderingList.symm
  rw [leftEq, rightEq, parityFactor_permutationIsEven, parityFactor_permutationIsEven,
    permHandedness_mul]

/-! ## Actual graph linkage of a physical frame -/

/-- The actual cursor atoms of a localized four-ligand frame are the molecular ligand atoms of one
distinguished center, read through a slot equivalence `alpha`. -/
structure ActualFrameLigandMatch
    (input : LocalizedUniversalReference.Input)
    (m : MultiCenterMolecule input.certified.Atom)
    {carrierFuel : Nat}
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (center : m.Center) (alpha : Equiv.Perm (Fin 4)) : Prop where
  real : ∀ index,
    (frame.cursorAt index).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom
  atom : ∀ index,
    (frame.cursorAt index).occurrence.1.node.current? =
      some (m.ligandAtomAt center (alpha index))

/-- The root atomic number of a real frame cursor is the molecular graph's atomic number of its
current atom. -/
theorem rootAtomicNumberAt_eq_atomZ_of_real
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (index : Fin 4) (atom : input.Atom)
    (real : (frame.cursorAt index).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (current : (frame.cursorAt index).occurrence.1.node.current? = some atom) :
    frame.rootAtomicNumberAt input index = input.moleculeGraph.atomZ atom := by
  unfold CertifiedLocalizedCIPInput.LocalizedOccurrenceFourLigandFrame.rootAtomicNumberAt
    CertifiedLocalizedCIPInput.localizedRerootCursorRootAtomicNumber
  rw [MoleculeGraph.officialNodeAtomLabel, current, real]
  rfl

/-- A multi-center automorphism preserves the molecular graph's atomic number. -/
theorem multiCenterAut_atomZ_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (mol : MoleculeGraph V) (molEq : m.mol = mol)
    (e : m.Aut) (atom : V) :
    mol.atomZ ((e : Equiv.Perm V) atom) = mol.atomZ atom := by
  rw [← molEq]
  exact MoleculeGraph.Aut.atomZ_eq (m := m.mol)
    (e := ⟨(e : Equiv.Perm V),
      MultiCenterMolecule.Aut.mem_molAut (m := m) e⟩) atom





theorem trackedHighestFirst_eq_map_of_actualRootZTransport
    (input : LocalizedUniversalReference.Input)
    (m : MultiCenterMolecule input.certified.Atom)
    (molEq : m.mol = input.certified.moleculeGraph)
    (d : m.Center) (e : m.Aut)
    (F G : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (separatedF : input.certified.ConstitutionallyAtomicNumberSeparatedFrame F)
    (separatedG : input.certified.ConstitutionallyAtomicNumberSeparatedFrame G)
    (alphaF alphaG : Equiv.Perm (Fin 4))
    (matchF : ActualFrameLigandMatch input m F d alphaF)
    (matchG : ActualFrameLigandMatch input m G (m.centerPerm e d) alphaG)
    (trackedF trackedG : TrackedLocalizedLigandOrder)
    (permutationF : trackedF.highestFirst.Perm (List.finRange 4))
    (strictF : trackedF.highestFirst.Pairwise (fun left right =>
      F.rootAtomicNumberAt input.certified right <
        F.rootAtomicNumberAt input.certified left))
    (permutationG : trackedG.highestFirst.Perm (List.finRange 4))
    (strictG : trackedG.highestFirst.Pairwise (fun left right =>
      G.rootAtomicNumberAt input.certified right <
        G.rootAtomicNumberAt input.certified left)) :
    let p : Equiv.Perm (Fin 4) := alphaG.symm * m.ligandPermAt e d * alphaF
    trackedG.highestFirst = trackedF.highestFirst.map p := by
  let p : Equiv.Perm (Fin 4) := alphaG.symm * m.ligandPermAt e d * alphaF
  let ZF : Fin 4 → Nat := fun index => F.rootAtomicNumberAt input.certified index
  let ZG : Fin 4 → Nat := fun index => G.rootAtomicNumberAt input.certified index
  have injectiveG : Function.Injective ZG := by
    intro left right equal
    by_contra different
    exact separatedG left right different equal
  have atomZTransport : ∀ index : Fin 4, ZG (p index) = ZF index := by
    intro index
    have leftEq : ZF index = input.certified.moleculeGraph.atomZ
        (m.ligandAtomAt d (alphaF index)) :=
      rootAtomicNumberAt_eq_atomZ_of_real input.certified F index
        (m.ligandAtomAt d (alphaF index)) (matchF.real index) (matchF.atom index)
    have rightEq : ZG (p index) = input.certified.moleculeGraph.atomZ
        (m.ligandAtomAt (m.centerPerm e d) (alphaG (p index))) :=
      rootAtomicNumberAt_eq_atomZ_of_real input.certified G (p index)
        (m.ligandAtomAt (m.centerPerm e d) (alphaG (p index)))
        (matchG.real (p index)) (matchG.atom (p index))
    have permutationApply : alphaG (p index) = m.ligandPermAt e d (alphaF index) := by
      dsimp [p]
      simp
    rw [leftEq, rightEq, permutationApply, m.ligandAtomAt_ligandPermAt]
    exact multiCenterAut_atomZ_eq m input.certified.moleculeGraph molEq e
      (m.ligandAtomAt d (alphaF index))
  have permutationTransport : List.Perm trackedG.highestFirst
      (trackedF.highestFirst.map p) := by
    have mapped : List.Perm (trackedF.highestFirst.map p) (List.finRange 4) :=
      (permutationF.map p).trans (Equiv.Perm.map_finRange_perm p)
    exact permutationG.trans mapped.symm
  refine List.Perm.eq_of_pairwise
    (le := fun left right => ¬ ZG left < ZG right) ?_ ?_ ?_ permutationTransport
  · intro left right _ _ notLeft notRight
    exact injectiveG (le_antisymm (Nat.le_of_not_lt notRight) (Nat.le_of_not_lt notLeft))
  · exact strictG.imp (by
      intro left right higher
      exact Nat.not_lt_of_ge (Nat.le_of_lt higher))
  · rw [List.pairwise_map]
    exact strictF.imp (by
      intro left right higher
      rw [atomZTransport left, atomZTransport right]
      exact Nat.not_lt_of_ge (Nat.le_of_lt higher))

/-! ## Physical frame calibration -/

/-- The actual written frame coordinates are the same physical configuration's coordinates in the
molecular ligand enumeration, reindexed by `alpha`, with nonzero volume and a physical sign equal
to the configuration sign at the center. -/
structure PhysicalFrameCalibration
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (center : m.Center)
    (alpha : Equiv.Perm (Fin 4)) (pointsAt : Fin 4 → CartesianPoint3) where
  physicalPointAt : Fin 4 → CartesianPoint3
  calibrated : ∀ index, pointsAt index = physicalPointAt (alpha index)
  nondegenerate :
    CartesianPoint3.orientedVolume
      (physicalPointAt 0) (physicalPointAt 1) (physicalPointAt 2) (physicalPointAt 3) ≠ 0
  sign_eq :
    rationalVolumeSign
      (CartesianPoint3.orientedVolume
        (physicalPointAt 0) (physicalPointAt 1) (physicalPointAt 2) (physicalPointAt 3)) =
      m.configurationSign cfg center

/-- A calibrated frame has nonzero written-order volume. -/
theorem PhysicalFrameCalibration.written_nondegenerate
    {V : Type*} [Fintype V] [DecidableEq V]
    {m : MultiCenterMolecule V} {cfg : m.Configuration} {center : m.Center}
    {alpha : Equiv.Perm (Fin 4)} {pointsAt : Fin 4 → CartesianPoint3}
    (calibration : PhysicalFrameCalibration m cfg center alpha pointsAt) :
    CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0 := by
  rw [orientedVolume_calibrated_eq pointsAt calibration.physicalPointAt alpha
      calibration.calibrated,
    RationalTetrahedralPermutation.permutedOrientedVolume_eq_if_permutationIsEven]
  cases RawMolecule.permutationIsEven
      (Rule6HandednessSemantics.finFourPermutationList alpha) with
  | false => simpa using neg_ne_zero.mpr calibration.nondegenerate
  | true => simpa using calibration.nondegenerate

/-- The precise repository convention for the written-frame sign: the written sign is the
configuration sign at the center multiplied by the sign of the frame-slot permutation. -/
theorem PhysicalFrameCalibration.sign_eq_configurationSign_mul
    {V : Type*} [Fintype V] [DecidableEq V]
    {m : MultiCenterMolecule V} {cfg : m.Configuration} {center : m.Center}
    {alpha : Equiv.Perm (Fin 4)} {pointsAt : Fin 4 → CartesianPoint3}
    (calibration : PhysicalFrameCalibration m cfg center alpha pointsAt) :
    rationalVolumeSign
      (CartesianPoint3.orientedVolume
        (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3)) =
      m.configurationSign cfg center * permHandedness alpha := by
  rw [orientedVolume_calibrated_eq pointsAt calibration.physicalPointAt alpha
      calibration.calibrated,
    rationalVolumeSign_permutedOrientedVolume, calibration.sign_eq]

/-! ## Final actual generated-reference-state covariance -/

private theorem mul_eq_one_or_neg_one {first second : ℝ}
    (firstCases : first = 1 ∨ first = -1)
    (secondCases : second = 1 ∨ second = -1) :
    first * second = 1 ∨ first * second = -1 := by
  rcases firstCases with rfl | rfl <;> rcases secondCases with rfl | rfl <;> norm_num

/-- **Actual normalized-label covariance at root-`Z`-separated physical centers.**

For paired actual real occurrences `t`, `u` at distinguished physical centers `d`, `e d`, with
actual four-ligand frames `F`, `G`, actual graph linkage through slot equivalences `alphaF`,
`alphaG`, pairwise distinct root atomic numbers, nondegenerate actual coordinates calibrated to the
same physical configuration `cfg`, and the physical local sign law, the actual generated reference
state at `u` is the uppercase reflection of the actual generated reference state at `t` exactly
when the sign law has `epsilon = -1`. -/
theorem referenceState_rootZAutomorphism_label_covariance
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
    (spatialF : ∀ index,
      input.certified.localizedRerootCursorSpatialPoint? (F.cursorAt index) =
        some (pointsF index))
    (spatialU : ∀ index,
      input.certified.localizedRerootCursorSpatialPoint? (G.cursorAt index) =
        some (pointsU index))
    (calibrationF : PhysicalFrameCalibration m cfg d alphaF pointsF)
    (calibrationU : PhysicalFrameCalibration m cfg (m.centerPerm e d) alphaG pointsU)
    (signLaw :
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (if mirror then -1 else 1) *
          m.configurationSign cfg (m.centerPerm e d)) :
    LocalizedUniversalReference.referenceState input u =
      (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input t) := by
  let viewF : input.certified.LocalizedDependencyView t :=
    input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) t
  let viewU : input.certified.LocalizedDependencyView u :=
    input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) u
  obtain ⟨trackedF, computedF, permutationF, strictF, _pseudoF⟩ :=
    input.certified.exists_localizedConstitutionalFrame_trackedOrder
      t viewF F derivedF separatedF
  obtain ⟨trackedU, computedU, permutationU, strictU, _pseudoU⟩ :=
    input.certified.exists_localizedConstitutionalFrame_trackedOrder
      u viewU G derivedG separatedG
  have sortedTransport : trackedU.highestFirst =
      trackedF.highestFirst.map
        (alphaG.symm * m.ligandPermAt e d * alphaF) :=
    trackedHighestFirst_eq_map_of_actualRootZTransport
      input m molEq d e F G separatedF separatedG alphaF alphaG
      matchF matchG trackedF trackedU permutationF strictF permutationU strictU
  let sF : ℝ := rationalVolumeSign
    (CartesianPoint3.orientedVolume (pointsF 0) (pointsF 1) (pointsF 2) (pointsF 3))
  let sU : ℝ := rationalVolumeSign
    (CartesianPoint3.orientedVolume (pointsU 0) (pointsU 1) (pointsU 2) (pointsU 3))
  have volumeF_nonzero : CartesianPoint3.orientedVolume
      (pointsF 0) (pointsF 1) (pointsF 2) (pointsF 3) ≠ 0 :=
    calibrationF.written_nondegenerate
  have volumeU_nonzero : CartesianPoint3.orientedVolume
      (pointsU 0) (pointsU 1) (pointsU 2) (pointsU 3) ≠ 0 :=
    calibrationU.written_nondegenerate
  let parityF : TetrahedralInputParity := parityOfVolumeSign sF
  let parityU : TetrahedralInputParity := parityOfVolumeSign sU
  have writtenParityF : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsF 0, pointsF 1, pointsF 2, pointsF 3] parityF :=
    rationalTetrahedralInputParity_parityOfVolumeSign
      (pointsF 0) (pointsF 1) (pointsF 2) (pointsF 3) volumeF_nonzero
  have writtenParityU : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsU 0, pointsU 1, pointsU 2, pointsU 3] parityU :=
    rationalTetrahedralInputParity_parityOfVolumeSign
      (pointsU 0) (pointsU 1) (pointsU 2) (pointsU 3) volumeU_nonzero
  obtain ⟨trackedF141, computedF141, _pseudoF141, stateF⟩ :=
    referenceState_reader_eq_chiral_of_physicalFrame
      input noDouble t F derivedF separatedF centerF centerRealF
      pointsF spatialF parityF writtenParityF
  obtain ⟨trackedU141, computedU141, _pseudoU141, stateU⟩ :=
    referenceState_reader_eq_chiral_of_physicalFrame
      input noDouble u G derivedG separatedG centerU centerRealU
      pointsU spatialU parityU writtenParityU
  have trackedF_eq : trackedF141 = trackedF := by
    rw [computedF141] at computedF
    exact Option.some.inj computedF
  have trackedU_eq : trackedU141 = trackedU := by
    rw [computedU141] at computedU
    exact Option.some.inj computedU
  rw [trackedF_eq] at stateF
  rw [trackedU_eq] at stateU
  let eF : ℝ := parityFactor
    (RawMolecule.permutationIsEven (trackedF.highestFirst.map Fin.val))
  let eU : ℝ := parityFactor
    (RawMolecule.permutationIsEven (trackedU.highestFirst.map Fin.val))
  have labelF_eq :
      RawMolecule.descriptorOfParity parityF
        (RawMolecule.permutationIsEven
          (trackedF.highestFirst.map Fin.val)) =
        RS.ofHandedness (sF * eF) := by
    simpa [parityF, sF, eF] using
      descriptorOfParity_parityOfVolumeSign
        (pointsF 0) (pointsF 1) (pointsF 2) (pointsF 3) volumeF_nonzero
        (RawMolecule.permutationIsEven (trackedF.highestFirst.map Fin.val))
  have labelU_eq :
      RawMolecule.descriptorOfParity parityU
        (RawMolecule.permutationIsEven
          (trackedU.highestFirst.map Fin.val)) =
        RS.ofHandedness (sU * eU) := by
    simpa [parityU, sU, eU] using
      descriptorOfParity_parityOfVolumeSign
        (pointsU 0) (pointsU 1) (pointsU 2) (pointsU 3) volumeU_nonzero
        (RawMolecule.permutationIsEven (trackedU.highestFirst.map Fin.val))
  have permutationSign : permHandedness
      (alphaG.symm * m.ligandPermAt e d * alphaF) =
      permHandedness alphaG * permHandedness (m.ligandPermAt e d) *
        permHandedness alphaF := by
    change permHandedness (alphaG⁻¹ * m.ligandPermAt e d * alphaF) =
      permHandedness alphaG * permHandedness (m.ligandPermAt e d) *
        permHandedness alphaF
    simp only [permHandedness_mul, permHandedness_inv]
  have parityTransport : eU =
      permHandedness (alphaG.symm * m.ligandPermAt e d * alphaF) * eF := by
    have transported := parityFactor_permutationIsEven_map
      trackedF.highestFirst
      (alphaG.symm * m.ligandPermAt e d * alphaF) permutationF
    rw [← sortedTransport] at transported
    simpa [eU, eF] using transported
  have signF : sF =
      m.configurationSign cfg d * permHandedness alphaF :=
    calibrationF.sign_eq_configurationSign_mul
  have signU : sU =
      m.configurationSign cfg (m.centerPerm e d) *
        permHandedness alphaG :=
    calibrationU.sign_eq_configurationSign_mul
  have signProduct : sU * eU =
      (if mirror then (-1 : ℝ) else 1) * (sF * eF) := by
    have ligandSignSquared :
        permHandedness (m.ligandPermAt e d) *
          permHandedness (m.ligandPermAt e d) = 1 :=
      permHandedness_mul_self (m.ligandPermAt e d)
    have frameSignSquared :
        permHandedness alphaG * permHandedness alphaG = 1 :=
      permHandedness_mul_self alphaG
    have epsilonSquared :
        (if mirror then (-1 : ℝ) else 1) *
          (if mirror then (-1 : ℝ) else 1) = 1 := by
      cases mirror <;> norm_num
    have reversedSignLaw :
        m.configurationSign cfg (m.centerPerm e d) *
          permHandedness (m.ligandPermAt e d) =
          (if mirror then (-1 : ℝ) else 1) * m.configurationSign cfg d := by
      calc
        m.configurationSign cfg (m.centerPerm e d) *
            permHandedness (m.ligandPermAt e d)
            = ((if mirror then (-1 : ℝ) else 1) *
                  (if mirror then (-1 : ℝ) else 1)) *
                (m.configurationSign cfg (m.centerPerm e d) *
                  permHandedness (m.ligandPermAt e d)) := by
              rw [epsilonSquared]
              ring
        _ = (if mirror then (-1 : ℝ) else 1) *
              (((if mirror then (-1 : ℝ) else 1) *
                  m.configurationSign cfg (m.centerPerm e d)) *
                permHandedness (m.ligandPermAt e d)) := by ring
        _ = (if mirror then (-1 : ℝ) else 1) *
              (m.configurationSign cfg d *
                permHandedness (m.ligandPermAt e d)) *
                permHandedness (m.ligandPermAt e d) := by
              rw [← signLaw]
              ring
        _ = ((if mirror then (-1 : ℝ) else 1) *
                m.configurationSign cfg d) *
              (permHandedness (m.ligandPermAt e d) *
                permHandedness (m.ligandPermAt e d)) := by ring
        _ = (if mirror then (-1 : ℝ) else 1) *
              m.configurationSign cfg d := by
              rw [ligandSignSquared]
              ring
    calc
      sU * eU =
          (m.configurationSign cfg (m.centerPerm e d) *
              permHandedness alphaG) *
            ((permHandedness alphaG *
                permHandedness (m.ligandPermAt e d) *
                permHandedness alphaF) * eF) := by
            rw [signU, parityTransport, permutationSign]
      _ = ((m.configurationSign cfg (m.centerPerm e d) *
                permHandedness (m.ligandPermAt e d)) *
              (permHandedness alphaF * eF)) *
            (permHandedness alphaG * permHandedness alphaG) := by ring
      _ = (m.configurationSign cfg (m.centerPerm e d) *
              permHandedness (m.ligandPermAt e d)) *
            (permHandedness alphaF * eF) := by
            rw [frameSignSquared]
            ring
      _ = ((if mirror then (-1 : ℝ) else 1) *
              m.configurationSign cfg d) *
            (permHandedness alphaF * eF) := by
            rw [reversedSignLaw]
      _ = (if mirror then (-1 : ℝ) else 1) * (sF * eF) := by
            rw [signF]
            ring
  have signF_eq_one_or_neg_one : sF = 1 ∨ sF = -1 := by
    rw [signF]
    exact mul_eq_one_or_neg_one
      (permHandedness_eq_one_or_eq_neg_one (cfg d))
      (permHandedness_eq_one_or_eq_neg_one alphaF)
  have productSign : sF * eF = 1 ∨ sF * eF = -1 :=
    mul_eq_one_or_neg_one signF_eq_one_or_neg_one
      (parityFactor_eq_one_or_neg_one _)
  have reflectedLabel : RS.ofHandedness (sU * eU) =
      (if mirror then RS.swap (RS.ofHandedness (sF * eF))
        else RS.ofHandedness (sF * eF)) := by
    rw [signProduct]
    cases mirror with
    | false => simp
    | true =>
        rw [show (if true then (-1 : ℝ) else 1) = -1 by norm_num]
        rw [neg_mul, one_mul, RS.ofHandedness_neg (sF * eF) productSign]
        simp
  rw [stateU, labelU_eq, stateF, labelF_eq, reflectedLabel]
  cases mirror <;> rfl

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.rationalVolumeSign
assert_kernel_only TetraStereo.OneCenter.rationalVolumeSign_of_neg
assert_kernel_only TetraStereo.OneCenter.rationalVolumeSign_of_pos
assert_kernel_only TetraStereo.OneCenter.rationalVolumeSign_eq_neg_iff_of_ne
assert_kernel_only TetraStereo.OneCenter.rationalVolumeSign_eq_one_iff_of_ne
assert_kernel_only TetraStereo.OneCenter.rationalVolumeSign_eq_neg_or_one
assert_kernel_only TetraStereo.OneCenter.rationalVolumeSign_neg
assert_kernel_only TetraStereo.OneCenter.parityFactor
assert_kernel_only TetraStereo.OneCenter.parityFactor_eq_one_or_neg_one
assert_kernel_only TetraStereo.OneCenter.rationalVolumeSign_if
assert_kernel_only TetraStereo.OneCenter.parityFactor_permutationIsEven
assert_kernel_only TetraStereo.OneCenter.rationalVolumeSign_permutedOrientedVolume
assert_kernel_only TetraStereo.OneCenter.orientedVolume_calibrated_eq
assert_kernel_only TetraStereo.OneCenter.parityOfVolumeSign
assert_kernel_only TetraStereo.OneCenter.ofHandedness_parityFactor_clockwise
assert_kernel_only TetraStereo.OneCenter.ofHandedness_parityFactor_anticlockwise
assert_kernel_only TetraStereo.OneCenter.rationalTetrahedralInputParity_parityOfVolumeSign
assert_kernel_only TetraStereo.OneCenter.descriptorOfParity_parityOfVolumeSign
assert_kernel_only TetraStereo.OneCenter.trackedPriorityOrdering
assert_kernel_only TetraStereo.OneCenter.trackedPriorityOrdering_list
assert_kernel_only TetraStereo.OneCenter.ofFn_trackedPriorityOrdering
assert_kernel_only TetraStereo.OneCenter.parityFactor_permutationIsEven_map
assert_kernel_only TetraStereo.OneCenter.ActualFrameLigandMatch
assert_kernel_only TetraStereo.OneCenter.rootAtomicNumberAt_eq_atomZ_of_real
assert_kernel_only TetraStereo.OneCenter.multiCenterAut_atomZ_eq
assert_kernel_only TetraStereo.OneCenter.trackedHighestFirst_eq_map_of_actualRootZTransport
assert_kernel_only TetraStereo.OneCenter.PhysicalFrameCalibration
assert_kernel_only TetraStereo.OneCenter.PhysicalFrameCalibration.written_nondegenerate
assert_kernel_only TetraStereo.OneCenter.PhysicalFrameCalibration.sign_eq_configurationSign_mul
assert_kernel_only TetraStereo.OneCenter.referenceState_rootZAutomorphism_label_covariance

end TetraStereo.OneCenter
