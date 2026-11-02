/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TetraStereo.OneCenter.LocalizedIndependentAuxiliaryRS
import TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalLabelCovariance
import TetraStereo.OneCenter.Rule4bSparseSourceDecisionFidelity
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

noncomputable section

namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open Rule4bSparseSource





































































/-! ## A. The physical local discrepancy -/

section Algebra

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The **physical local discrepancy** of an automorphism at a centre, in the original detected
ligand enumeration and at the original physical configuration.  It is the product of the local
configuration signs at the centre and at its image with the handedness of the induced ligand
permutation. -/
def localDiscrepancy (m : MultiCenterMolecule V) (cfg : m.Configuration) (e : m.Aut)
    (d : m.Center) : ℝ :=
  m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) *
    m.configurationSign cfg (m.centerPerm e d)

/-- Every physical local discrepancy is `+1` or `-1`: all three factors are configuration or
permutation signs. -/
theorem localDiscrepancy_eq_one_or_neg_one (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e : m.Aut) (d : m.Center) :
    localDiscrepancy m cfg e d = 1 ∨ localDiscrepancy m cfg e d = -1 := by
  have hd : m.configurationSign cfg d = permHandedness (cfg d) := rfl
  have himage : m.configurationSign cfg (m.centerPerm e d) =
      permHandedness (cfg (m.centerPerm e d)) := rfl
  unfold localDiscrepancy
  rw [hd, himage]
  rcases permHandedness_eq_one_or_eq_neg_one (cfg d) with h1 | h1 <;>
    rcases permHandedness_eq_one_or_eq_neg_one (m.ligandPermAt e d) with h2 | h2 <;>
      rcases permHandedness_eq_one_or_eq_neg_one (cfg (m.centerPerm e d)) with h3 | h3 <;>
        rw [h1, h2, h3] <;> norm_num

/-- The physical local discrepancy never vanishes. -/
theorem localDiscrepancy_ne_zero (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e : m.Aut) (d : m.Center) :
    localDiscrepancy m cfg e d ≠ 0 := by
  rcases localDiscrepancy_eq_one_or_neg_one m cfg e d with h | h <;> rw [h] <;> norm_num


theorem actualLocalSignLaw_iff_localDiscrepancy (m : MultiCenterMolecule V)
    (cfg : m.Configuration) (e : m.Aut) (mirror : Bool) (d : m.Center) :
    ActualLocalSignLaw m cfg e mirror d ↔
      localDiscrepancy m cfg e d = (if mirror then (-1 : ℝ) else 1) := by
  have hsq : m.configurationSign cfg (m.centerPerm e d) *
      m.configurationSign cfg (m.centerPerm e d) = 1 := by
    have himage : m.configurationSign cfg (m.centerPerm e d) =
        permHandedness (cfg (m.centerPerm e d)) := rfl
    rw [himage]
    exact permHandedness_mul_self _
  unfold ActualLocalSignLaw localDiscrepancy
  constructor
  · intro h
    calc
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) *
            m.configurationSign cfg (m.centerPerm e d)
          = ((if mirror then (-1 : ℝ) else 1) *
              m.configurationSign cfg (m.centerPerm e d)) *
              m.configurationSign cfg (m.centerPerm e d) := by rw [h]
      _ = (if mirror then (-1 : ℝ) else 1) *
            (m.configurationSign cfg (m.centerPerm e d) *
              m.configurationSign cfg (m.centerPerm e d)) := by ring
      _ = (if mirror then (-1 : ℝ) else 1) := by rw [hsq]; ring
  · intro h
    have hx : (m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) *
          m.configurationSign cfg (m.centerPerm e d)) *
          m.configurationSign cfg (m.centerPerm e d) =
        m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) := by
      rw [mul_assoc, hsq, mul_one]
    calc
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d)
          = (m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) *
              m.configurationSign cfg (m.centerPerm e d)) *
              m.configurationSign cfg (m.centerPerm e d) := hx.symm
      _ = (if mirror then (-1 : ℝ) else 1) *
            m.configurationSign cfg (m.centerPerm e d) := by rw [h]

/-- The Boolean mirror flag carried by a physical discrepancy: `true` exactly when the
discrepancy is `-1`.  This is a definition, not an assumed local sign law. -/
def discrepancyMirror (m : MultiCenterMolecule V) (cfg : m.Configuration) (e : m.Aut)
    (d : m.Center) : Bool :=
  if localDiscrepancy m cfg e d = -1 then true else false

/-- The sign law at the derived mirror flag always holds. -/
theorem actualLocalSignLaw_discrepancyMirror (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e : m.Aut) (d : m.Center) :
    ActualLocalSignLaw m cfg e (discrepancyMirror m cfg e d) d := by
  rw [actualLocalSignLaw_iff_localDiscrepancy]
  rcases localDiscrepancy_eq_one_or_neg_one m cfg e d with h | h <;>
    simp [discrepancyMirror, h]

/-- **The sign law pins down the mirror flag uniquely.**  A mirror is admissible at a centre
exactly when it is the discrepancy flag of that centre. -/
theorem actualLocalSignLaw_iff_mirror_eq (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e : m.Aut) (mirror : Bool) (d : m.Center) :
    ActualLocalSignLaw m cfg e mirror d ↔ mirror = discrepancyMirror m cfg e d := by
  rw [actualLocalSignLaw_iff_localDiscrepancy]
  rcases localDiscrepancy_eq_one_or_neg_one m cfg e d with h | h <;>
    cases mirror <;> simp [discrepancyMirror, h] <;> norm_num

/-- Two mirror flags agree exactly when the two physical discrepancies agree. -/
theorem discrepancyMirror_eq_iff (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (e : m.Aut) (first second : m.Center) :
    discrepancyMirror m cfg e first = discrepancyMirror m cfg e second ↔
      localDiscrepancy m cfg e first = localDiscrepancy m cfg e second := by
  have hfirst := localDiscrepancy_eq_one_or_neg_one m cfg e first
  have hsecond := localDiscrepancy_eq_one_or_neg_one m cfg e second
  rcases hfirst with h1 | h1 <;> rcases hsecond with h2 | h2 <;>
    simp [discrepancyMirror, h1, h2]; norm_num

/-- **Gauge invariance of the physical discrepancy.**  Under an arbitrary per-centre
re-indexing `τ` of the ligand frames, with the configuration transported as `cfg * τ⁻¹`, the
discrepancy at a centre is unchanged: the parity factors of `τ d` cancel against themselves and
the parity factors of `τ (e d)` cancel between the ligand permutation and the image sign.  This is
the frame-reindexing content of `RootedBranchFrameReindexInvariance`; the corresponding branch
transport relations and the chemical configuration are unchanged by the same module. -/
theorem localDiscrepancy_reindexFrames (m : MultiCenterMolecule V)
    (τ : m.Center → Equiv.Perm (Fin 4)) (cfg : m.Configuration) (e : m.Aut)
    (d : m.Center) :
    localDiscrepancy (m.reindexFrames τ) (m.reindexConfiguration τ cfg)
        (m.autReindex τ e) d = localDiscrepancy m cfg e d := by
  have hcenter : (m.reindexFrames τ).centerPerm (m.autReindex τ e) d = m.centerPerm e d :=
    MultiCenterMolecule.reindexFrames_centerPerm m τ e d
  have hsignD : (m.reindexFrames τ).configurationSign (m.reindexConfiguration τ cfg) d =
      m.configurationSign cfg d * permHandedness (τ d) :=
    MultiCenterMolecule.configurationSign_reindexConfiguration m τ cfg d
  have hsignE : (m.reindexFrames τ).configurationSign (m.reindexConfiguration τ cfg)
        ((m.reindexFrames τ).centerPerm (m.autReindex τ e) d) =
      m.configurationSign cfg (m.centerPerm e d) *
        permHandedness (τ (m.centerPerm e d)) := by
    rw [hcenter]
    exact MultiCenterMolecule.configurationSign_reindexConfiguration m τ cfg (m.centerPerm e d)
  have hlig : permHandedness ((m.reindexFrames τ).ligandPermAt (m.autReindex τ e) d) =
      permHandedness (τ (m.centerPerm e d)) * permHandedness (m.ligandPermAt e d) *
        permHandedness (τ d) := by
    have h := congrArg permHandedness (MultiCenterMolecule.reindexFrames_ligandPermAt m τ e d)
    rw [hcenter] at h
    rw [h]
    simp [permHandedness_mul]
  have hpp : permHandedness (τ d) * permHandedness (τ d) = 1 :=
    permHandedness_mul_self (τ d)
  have hqq : permHandedness (τ (m.centerPerm e d)) *
      permHandedness (τ (m.centerPerm e d)) = 1 :=
    permHandedness_mul_self (τ (m.centerPerm e d))
  unfold localDiscrepancy
  rw [hsignD, hsignE, hlig]
  calc
    (m.configurationSign cfg d * permHandedness (τ d)) *
          (permHandedness (τ (m.centerPerm e d)) * permHandedness (m.ligandPermAt e d) *
            permHandedness (τ d)) *
          (m.configurationSign cfg (m.centerPerm e d) *
            permHandedness (τ (m.centerPerm e d)))
        = m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) *
            m.configurationSign cfg (m.centerPerm e d) *
              (permHandedness (τ d) * permHandedness (τ d)) *
              (permHandedness (τ (m.centerPerm e d)) *
                permHandedness (τ (m.centerPerm e d))) := by ring
    _ = m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) *
          m.configurationSign cfg (m.centerPerm e d) := by rw [hpp, hqq]; ring

end Algebra

/-! ## B. Reflection of uppercase letters and the pair-class bridge -/

/-- **Reflection contrast on uppercase letters.**  Reflecting zero, one or both of two uppercase
letters leaves them equal exactly when the two choices of reflection agree with the letters'
equality.  This is the `RS.swap` square: reflection is injective and fixed-point free. -/
theorem reflectUppercaseOptionalLabel_chiral_eq_iff (first second : RS) (reflectFirst
    reflectSecond : Bool) :
    ((if reflectFirst then reflectUppercaseOptionalLabel else id) (some (.chiral first)) =
      (if reflectSecond then reflectUppercaseOptionalLabel else id) (some (.chiral second))) ↔
      (first = second ↔ reflectFirst = reflectSecond) := by
  cases reflectFirst <;> cases reflectSecond <;> cases first <;> cases second <;>
    simp [reflectUppercaseOptionalLabel, reflectUppercaseAuxiliaryLabel, RS.swap]

/-- `RS.ofHandedness` is injective on the two nondegenerate handedness values, expressed through
the product being one. -/
theorem ofHandedness_eq_iff_mul_eq_one {reference observed : ℝ}
    (referenceCases : reference = 1 ∨ reference = -1)
    (observedCases : observed = 1 ∨ observed = -1) :
    RS.ofHandedness observed = RS.ofHandedness reference ↔ reference * observed = 1 := by
  have hneg : (-1 : ℝ) ≠ 1 := by norm_num
  have hpos : (1 : ℝ) ≠ -1 := by norm_num
  rcases referenceCases with rfl | rfl <;> rcases observedCases with rfl | rfl <;>
    simp [RS.ofHandedness, hneg, hpos]

/-- The Boolean letter comparison of two nondegenerate handedness values is exactly the product
test. -/
theorem ofHandedness_beq_iff_mul_eq_one {reference observed : ℝ}
    (referenceCases : reference = 1 ∨ reference = -1)
    (observedCases : observed = 1 ∨ observed = -1) :
    (RS.ofHandedness observed == RS.ofHandedness reference) = true ↔
      reference * observed = 1 := by
  rw [beq_iff_eq]
  exact ofHandedness_eq_iff_mul_eq_one referenceCases observedCases

/-- The **physical pair class**: `like` exactly when the product of the two normalized physical
senses is one, equivalently when the two physical senses agree.  The common R/S convention
cancels in this product; no absolute convention is chosen or calibrated here. -/
def physicalPairClass (reference observed : ℝ) : BlueBookP92.Rule4bPairClass :=
  if reference * observed = 1 then .like else .unlike

/-- The pair class is `like` exactly at product one. -/
theorem physicalPairClass_eq_like_iff {reference observed : ℝ} :
    physicalPairClass reference observed = .like ↔ reference * observed = 1 := by
  unfold physicalPairClass
  by_cases h : reference * observed = 1 <;> simp [h]

/-- The pair class is `unlike` exactly away from product one. -/
theorem physicalPairClass_eq_unlike_iff {reference observed : ℝ} :
    physicalPairClass reference observed = .unlike ↔ reference * observed ≠ 1 := by
  unfold physicalPairClass
  by_cases h : reference * observed = 1 <;> simp [h]

/-- **The source observation of two physical letters is the physical pair class.**  When the
observed occurrence carries the uppercase letter `RS.ofHandedness observed` and the selected
reference carries `RS.ofHandedness reference`, the actual source Rule-4b observation is the
physical pair class of the two normalized senses. -/
theorem sourceObserveRule4bLabel_ofHandedness_pairClass {reference observed : ℝ}
    (referenceCases : reference = 1 ∨ reference = -1)
    (observedCases : observed = 1 ∨ observed = -1) :
    sourceObserveRule4bLabel (RS.ofHandedness reference)
        (some (.chiral (RS.ofHandedness observed))) =
      .withRule4b .chiral (some (physicalPairClass reference observed)) := by
  have hneg : (-1 : ℝ) ≠ 1 := by norm_num
  rcases referenceCases with rfl | rfl <;> rcases observedCases with rfl | rfl <;>
    simp [sourceObserveRule4bLabel, physicalPairClass, hneg]

/-- **Reflection contrast of actual source observations.**  Reflecting the selected reference
letter and the observed letter by two independent `RS.swap` choices leaves the actual source
Rule-4b observation unchanged exactly when the two choices agree.  This is the pair algebra used
for the physical contrast, stated directly on the uppercase letters. -/
theorem sourceObserveRule4bLabel_reflect_contrast (reference observed : RS)
    (reflectReference reflectObserved : Bool) :
    sourceObserveRule4bLabel
        ((if reflectReference then RS.swap else id) reference)
        (some (.chiral ((if reflectObserved then RS.swap else id) observed))) =
      sourceObserveRule4bLabel reference (some (.chiral observed)) ↔
      reflectReference = reflectObserved := by
  cases reflectReference <;> cases reflectObserved <;> cases reference <;> cases observed <;>
    simp [sourceObserveRule4bLabel, RS.swap]

/-! ## C. The normalized physical sense -/

/-- The physically written sign of a frame-ordered coordinate table: the sign of the exact
oriented volume of the four slot points. -/
def physicalWrittenSign (pointsAt : Fin 4 → CartesianPoint3) : ℝ :=
  rationalVolumeSign
    (CartesianPoint3.orientedVolume (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3))

/-- **The normalized physical sense** of one actual occurrence.  `detectedOrder` is the physical
high-to-low priority order of the ligands, expressed in the detected ligand enumeration of the
centre (the physical priority order composed with the actual frame's slot-to-ligand permutation).
The sense is the physical configuration sign at the centre times the parity of that order.

The definition uses neither `tracked.highestFirst` nor any executable sorter, rank, key or runtime
comparison output; the order is a parameter supplied with its constitutional faithfulness proof. -/
def physicalNormalizedSense {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (center : m.Center)
    (detectedOrder : List (Fin 4)) : ℝ :=
  m.configurationSign cfg center *
    parityFactor (RawMolecule.permutationIsEven (detectedOrder.map Fin.val))

/-- Every normalized physical sense is `+1` or `-1`. -/
theorem physicalNormalizedSense_eq_one_or_neg_one {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (center : m.Center)
    (detectedOrder : List (Fin 4)) :
    physicalNormalizedSense m cfg center detectedOrder = 1 ∨
      physicalNormalizedSense m cfg center detectedOrder = -1 := by
  have hsign : m.configurationSign cfg center = permHandedness (cfg center) := rfl
  unfold physicalNormalizedSense
  rw [hsign]
  rcases permHandedness_eq_one_or_eq_neg_one (cfg center) with h1 | h1 <;>
    rcases parityFactor_eq_one_or_neg_one
      (RawMolecule.permutationIsEven (detectedOrder.map Fin.val)) with h2 | h2 <;>
      rw [h1, h2] <;> norm_num








theorem descriptorOfParity_writtenSign_eq_ofHandedness_normalizedSense
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (center : m.Center)
    (alpha : Equiv.Perm (Fin 4)) (pointsAt : Fin 4 → CartesianPoint3)
    (calibration : PhysicalFrameCalibration m cfg center alpha pointsAt)
    (order : List (Fin 4)) (permutation : order.Perm (List.finRange 4)) :
    RawMolecule.descriptorOfParity
        (parityOfVolumeSign (physicalWrittenSign pointsAt))
        (RawMolecule.permutationIsEven (order.map Fin.val)) =
      RS.ofHandedness
        (physicalNormalizedSense m cfg center (order.map alpha)) := by
  unfold physicalWrittenSign
  have nonzero := calibration.written_nondegenerate
  have hdescriptor := descriptorOfParity_parityOfVolumeSign (pointsAt 0) (pointsAt 1)
    (pointsAt 2) (pointsAt 3) nonzero (RawMolecule.permutationIsEven (order.map Fin.val))
  rw [hdescriptor, calibration.sign_eq_configurationSign_mul]
  have hmap := parityFactor_permutationIsEven_map order alpha permutation
  unfold physicalNormalizedSense
  rw [hmap]
  congr 1
  ring





















/-- One actual occurrence with its physical order data. -/
structure PhysicalRule4bOrderData
    (input : LocalizedUniversalReference.Input)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (target : LocalizedUniversalReference.Occurrence input)
    (center : m.Center)
    (centerTetra : input.certified.TetrahedralCenter)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node centerTetra) where
  singleBonded : input.certified.moleculeGraph.SimpleBonded
  acyclic : input.certified.moleculeGraph.Acyclic
  charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph
  frame : input.certified.LocalizedOccurrenceFourLigandFrame
    (LocalizedUniversalReference.carrierFuel input)
  derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame
  frameComputed : input.certified.localizedOccurrenceFourLigandFrame? target = some frame
  priority : Fin 4 → Fin 4 → Prop
  rigid : ConstitutionallyRigid input.certified.detectedMultiCenterMolecule
    ⟨centerTetra.1, centerTetra.2⟩
  correspondence : ConstitutionalPriorityCorrespondence input.certified target
    (input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target)
    frame derived priority
  pointsAt : Fin 4 → CartesianPoint3
  spatial : ∀ index : Fin 4,
    input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
      some (pointsAt index)
  nonzero : CartesianPoint3.orientedVolume
    (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0
  alpha : Equiv.Perm (Fin 4)
  calibration : PhysicalFrameCalibration m cfg center alpha pointsAt
  order : List (Fin 4)
  independent : IndependentHighestFirstFor priority order

/-- The **normalized physical sense** of one actual occurrence, expressed in the detected ligand
enumeration: the physical configuration sign times the parity of the physically ordered detected
ligands. -/
def PhysicalRule4bOrderData.normalizedSense
    {input : LocalizedUniversalReference.Input}
    {m : MultiCenterMolecule input.certified.Atom}
    {cfg : m.Configuration}
    {target : LocalizedUniversalReference.Occurrence input}
    {center : m.Center}
    {centerTetra : input.certified.TetrahedralCenter}
    {centerReal : input.certified.RealTetrahedralCenterNode target.1.node centerTetra}
    (data : PhysicalRule4bOrderData input m cfg target center centerTetra centerReal) : ℝ :=
  physicalNormalizedSense m cfg center (data.order.map data.alpha)

/-- Every normalized physical sense is `+1` or `-1`. -/
theorem PhysicalRule4bOrderData.normalizedSense_eq_one_or_neg_one
    {input : LocalizedUniversalReference.Input}
    {m : MultiCenterMolecule input.certified.Atom}
    {cfg : m.Configuration}
    {target : LocalizedUniversalReference.Occurrence input}
    {center : m.Center}
    {centerTetra : input.certified.TetrahedralCenter}
    {centerReal : input.certified.RealTetrahedralCenterNode target.1.node centerTetra}
    (data : PhysicalRule4bOrderData input m cfg target center centerTetra centerReal) :
    data.normalizedSense = 1 ∨ data.normalizedSense = -1 :=
  physicalNormalizedSense_eq_one_or_neg_one m cfg center (data.order.map data.alpha)







theorem PhysicalRule4bOrderData.referenceState_eq_chiral
    {input : LocalizedUniversalReference.Input}
    {m : MultiCenterMolecule input.certified.Atom}
    {cfg : m.Configuration}
    {target : LocalizedUniversalReference.Occurrence input}
    {center : m.Center}
    {centerTetra : input.certified.TetrahedralCenter}
    {centerReal : input.certified.RealTetrahedralCenterNode target.1.node centerTetra}
    (data : PhysicalRule4bOrderData input m cfg target center centerTetra centerReal)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords) :
    LocalizedUniversalReference.referenceState input target =
      some (.chiral (RS.ofHandedness data.normalizedSense)) := by
  have rational : CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
      (data.order.map data.pointsAt) (RS.ofHandedness data.normalizedSense) := by
    unfold PhysicalRule4bOrderData.normalizedSense
    rw [← descriptorOfParity_writtenSign_eq_ofHandedness_normalizedSense m cfg center
      data.alpha data.pointsAt data.calibration data.order data.independent.1]
    exact rationalTetrahedralDescriptor_of_independentOrder data.pointsAt data.order
      data.independent.1 (parityOfVolumeSign (physicalWrittenSign data.pointsAt))
      (rationalTetrahedralInputParity_parityOfVolumeSign (data.pointsAt 0) (data.pointsAt 1)
        (data.pointsAt 2) (data.pointsAt 3) data.nonzero)
  exact (referenceState_eq_chiral_iff_priorityDescriptor input data.singleBonded data.acyclic
    data.charge noDouble target data.frame data.derived centerTetra centerReal data.rigid
    data.priority data.correspondence data.pointsAt data.spatial data.nonzero data.order
    data.independent (RS.ofHandedness data.normalizedSense)).mpr rational







theorem exists_physicalRule4bOrderData
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (centerReal : input.certified.RealTetrahedralCenterNode target.1.node ⟨center.1, center.2⟩)
    (calibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg center) :
    Nonempty (PhysicalRule4bOrderData input input.certified.detectedMultiCenterMolecule cfg
      target center ⟨center.1, center.2⟩ centerReal) := by
  classical
  let centerTetra : input.certified.TetrahedralCenter := ⟨center.1, center.2⟩
  let view := input.certified.localizedDependencyView
    (LocalizedUniversalReference.referenceState input) target
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    simp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel, LocalizedReference.Input.molecule]
  have rigidGraph : ConstitutionallyRigidGraphAt input.certified.moleculeGraph centerTetra.1 :=
    constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified center
      calibrated.1
  obtain ⟨frame, alpha, pointAt, frameComputed, _ligandMatch, spatial, _observed,
    calibrationNonempty⟩ :=
    ActualGeneralRigidPhysicalBranchInverse.exists_physicalFrameAndCalibration_of_physicalGeneralRigidCenter
      input singleBonded acyclic input.certified.detectedMultiCenterMolecule rfl cfg center
      target targetCurrent calibrated
  let pointsAt : Fin 4 → CartesianPoint3 := fun index => pointAt (alpha index)
  have calibration : PhysicalFrameCalibration input.certified.detectedMultiCenterMolecule cfg
      center alpha pointsAt := calibrationNonempty.some
  have nonzero : CartesianPoint3.orientedVolume
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) ≠ 0 :=
    calibration.written_nondegenerate
  have derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame :=
    input.certified.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed
  let priority : Fin 4 → Fin 4 → Prop := fun left right =>
    frameSlotPhysicalOutcome input.certified target view frame derived singleBonded acyclic
      target.1.root left right Ordering.gt
  have correspondence : ConstitutionalPriorityCorrespondence input.certified target view frame
      derived priority := by
    intro left right _different
    exact (frameSlotPhysicalOutcome_iff_constitutionalCompare input.certified target view frame
      derived singleBonded acyclic left right Ordering.gt).symm
  obtain ⟨order, independent⟩ :=
    exists_independentPhysicalHighestFirst input.certified target view frame derived centerTetra
      centerReal rigidGraph acyclic singleBonded hcharge enough
  exact ⟨{ singleBonded := singleBonded
           acyclic := acyclic
           charge := hcharge
           frame := frame
           derived := derived
           frameComputed := frameComputed
           priority := priority
           rigid := calibrated.1
           correspondence := correspondence
           pointsAt := pointsAt
           spatial := spatial
           nonzero := nonzero
           alpha := alpha
           calibration := calibration
           order := order
           independent := independent }⟩














/-- The shared data of a physical constitutional automorphism fixing the original outer root. -/
structure PhysicalAutomorphismContext (input : LocalizedUniversalReference.Input) where
  noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords
  singleBonded : input.certified.moleculeGraph.SimpleBonded
  acyclic : input.certified.moleculeGraph.Acyclic
  charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph
  cfg : input.certified.detectedMultiCenterMolecule.Configuration
  rootCenter : input.certified.detectedMultiCenterMolecule.Center
  domain : ActualGeneralRigidPhysicalDomain input.certified
    input.certified.detectedMultiCenterMolecule cfg rootCenter
  root : input.certified.Atom
  e : input.certified.detectedMultiCenterMolecule.Aut
  rootFixed : (e : Equiv.Perm input.certified.Atom) root = root

/-- The two actual reader occurrences related by `e` at one marked centre `d`. -/
structure PhysicalReaderStep (input : LocalizedUniversalReference.Input)
    (context : PhysicalAutomorphismContext input)
    (d : input.certified.detectedMultiCenterMolecule.Center) where
  t : LocalizedUniversalReference.Occurrence input
  u : LocalizedUniversalReference.Occurrence input
  d_ne_root : d ≠ context.rootCenter
  image_ne_root : input.certified.detectedMultiCenterMolecule.centerPerm context.e d ≠
    context.rootCenter
  notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
    input.certified.detectedMultiCenterMolecule d
  image_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
    input.certified.detectedMultiCenterMolecule
      (input.certified.detectedMultiCenterMolecule.centerPerm context.e d)
  tRoot : t.1.root = context.root
  uRoot : u.1.root = context.root
  tCurrent : t.1.node.current? = some d.1
  uCurrent : u.1.node.current? =
    some (input.certified.detectedMultiCenterMolecule.centerPerm context.e d).1




theorem PhysicalReaderStep.reader_reflect
    {input : LocalizedUniversalReference.Input}
    {context : PhysicalAutomorphismContext input}
    {d : input.certified.detectedMultiCenterMolecule.Center}
    (step : PhysicalReaderStep input context d) :
    LocalizedUniversalReference.referenceState input step.u =
      (if discrepancyMirror input.certified.detectedMultiCenterMolecule context.cfg context.e d
        then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input step.t) :=
  referenceState_generalRigidAutomorphism_label_of_physicalDomain input context.noDouble
    context.singleBonded context.acyclic context.charge context.cfg context.rootCenter
    context.domain context.root context.e
    (discrepancyMirror input.certified.detectedMultiCenterMolecule context.cfg context.e d)
    context.rootFixed d step.t step.u step.d_ne_root step.image_ne_root step.notTwin
    step.image_notTwin step.tRoot step.uRoot step.tCurrent step.uCurrent
    (actualLocalSignLaw_discrepancyMirror input.certified.detectedMultiCenterMolecule
      context.cfg context.e d)






theorem PhysicalReaderStep.sourceObservation_contrast
    {input : LocalizedUniversalReference.Input}
    {context : PhysicalAutomorphismContext input}
    {dReference dObserved : input.certified.detectedMultiCenterMolecule.Center}
    (stepReference : PhysicalReaderStep input context dReference)
    (stepObserved : PhysicalReaderStep input context dObserved)
    (referenceLetter imageReferenceLetter observedLetter imageObservedLetter : RS)
    (referenceStateEq : LocalizedUniversalReference.referenceState input stepReference.t =
      some (.chiral referenceLetter))
    (imageReferenceStateEq : LocalizedUniversalReference.referenceState input stepReference.u =
      some (.chiral imageReferenceLetter))
    (observedStateEq : LocalizedUniversalReference.referenceState input stepObserved.t =
      some (.chiral observedLetter))
    (imageObservedStateEq : LocalizedUniversalReference.referenceState input stepObserved.u =
      some (.chiral imageObservedLetter)) :
    sourceObserveRule4bLabel imageReferenceLetter (some (.chiral imageObservedLetter)) =
      sourceObserveRule4bLabel referenceLetter (some (.chiral observedLetter)) ↔
      localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
          dReference =
        localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
          dObserved := by
  have reflectedReference := stepReference.reader_reflect
  have reflectedObserved := stepObserved.reader_reflect
  have imageReferenceEq : imageReferenceLetter =
      (if discrepancyMirror input.certified.detectedMultiCenterMolecule context.cfg context.e
          dReference then RS.swap else id) referenceLetter := by
    have equation := reflectedReference
    rw [referenceStateEq, imageReferenceStateEq] at equation
    by_cases flag : discrepancyMirror input.certified.detectedMultiCenterMolecule context.cfg
        context.e dReference <;>
      simpa [flag, reflectUppercaseOptionalLabel, reflectUppercaseAuxiliaryLabel] using equation
  have imageObservedEq : imageObservedLetter =
      (if discrepancyMirror input.certified.detectedMultiCenterMolecule context.cfg context.e
          dObserved then RS.swap else id) observedLetter := by
    have equation := reflectedObserved
    rw [observedStateEq, imageObservedStateEq] at equation
    by_cases flag : discrepancyMirror input.certified.detectedMultiCenterMolecule context.cfg
        context.e dObserved <;>
      simpa [flag, reflectUppercaseOptionalLabel, reflectUppercaseAuxiliaryLabel] using equation
  rw [imageReferenceEq, imageObservedEq]
  rw [sourceObserveRule4bLabel_reflect_contrast referenceLetter observedLetter
    (discrepancyMirror input.certified.detectedMultiCenterMolecule context.cfg context.e
      dReference)
    (discrepancyMirror input.certified.detectedMultiCenterMolecule context.cfg context.e
      dObserved)]
  exact discrepancyMirror_eq_iff input.certified.detectedMultiCenterMolecule context.cfg
    context.e dReference dObserved

/-- **Complement form of the physical contrast.**  The two actual source observations differ
exactly when the two physical discrepancies differ. -/
theorem PhysicalReaderStep.sourceObservation_differ
    {input : LocalizedUniversalReference.Input}
    {context : PhysicalAutomorphismContext input}
    {dReference dObserved : input.certified.detectedMultiCenterMolecule.Center}
    (stepReference : PhysicalReaderStep input context dReference)
    (stepObserved : PhysicalReaderStep input context dObserved)
    (referenceLetter imageReferenceLetter observedLetter imageObservedLetter : RS)
    (referenceStateEq : LocalizedUniversalReference.referenceState input stepReference.t =
      some (.chiral referenceLetter))
    (imageReferenceStateEq : LocalizedUniversalReference.referenceState input stepReference.u =
      some (.chiral imageReferenceLetter))
    (observedStateEq : LocalizedUniversalReference.referenceState input stepObserved.t =
      some (.chiral observedLetter))
    (imageObservedStateEq : LocalizedUniversalReference.referenceState input stepObserved.u =
      some (.chiral imageObservedLetter)) :
    sourceObserveRule4bLabel imageReferenceLetter (some (.chiral imageObservedLetter)) ≠
      sourceObserveRule4bLabel referenceLetter (some (.chiral observedLetter)) ↔
      localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
          dReference ≠
        localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
          dObserved := by
  have equality := stepReference.sourceObservation_contrast stepObserved referenceLetter
    imageReferenceLetter observedLetter imageObservedLetter referenceStateEq
    imageReferenceStateEq observedStateEq imageObservedStateEq
  constructor
  · intro different same
    exact different (equality.mpr same)
  · intro different same
    exact different (equality.mp same)





theorem PhysicalReaderStep.exists_t_letter
    {input : LocalizedUniversalReference.Input}
    {context : PhysicalAutomorphismContext input}
    {d : input.certified.detectedMultiCenterMolecule.Center}
    (step : PhysicalReaderStep input context d) :
    ∃ letter : RS, LocalizedUniversalReference.referenceState input step.t =
      some (.chiral letter) :=
  ActualGeneralRigidPhysicalBranchInverse.exists_chiral_referenceState_of_canonicalDomain
    input context.singleBonded context.acyclic context.charge context.noDouble
    (input.certified.canonicalReindexConfiguration context.cfg) context.rootCenter
    (input.certified.actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      context.cfg context.rootCenter context.domain)
    d step.d_ne_root step.notTwin step.t step.tCurrent



theorem PhysicalReaderStep.exists_u_letter
    {input : LocalizedUniversalReference.Input}
    {context : PhysicalAutomorphismContext input}
    {d : input.certified.detectedMultiCenterMolecule.Center}
    (step : PhysicalReaderStep input context d) :
    ∃ letter : RS, LocalizedUniversalReference.referenceState input step.u =
      some (.chiral letter) :=
  ActualGeneralRigidPhysicalBranchInverse.exists_chiral_referenceState_of_canonicalDomain
    input context.singleBonded context.acyclic context.charge context.noDouble
    (input.certified.canonicalReindexConfiguration context.cfg) context.rootCenter
    (input.certified.actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
      context.cfg context.rootCenter context.domain)
    (input.certified.detectedMultiCenterMolecule.centerPerm context.e d)
    step.image_ne_root step.image_notTwin step.u step.uCurrent

/-- The four actual generated uppercase letters of a reference and an observed reader step.  All
fields are produced from the actual reader states; none is supplied. -/
structure ActualPhysicalReaderPair (input : LocalizedUniversalReference.Input)
    (context : PhysicalAutomorphismContext input)
    (dReference dObserved : input.certified.detectedMultiCenterMolecule.Center) where
  stepReference : PhysicalReaderStep input context dReference
  stepObserved : PhysicalReaderStep input context dObserved
  referenceLetter : RS
  imageReferenceLetter : RS
  observedLetter : RS
  imageObservedLetter : RS
  referenceStateEq : LocalizedUniversalReference.referenceState input stepReference.t =
    some (.chiral referenceLetter)
  imageReferenceStateEq : LocalizedUniversalReference.referenceState input stepReference.u =
    some (.chiral imageReferenceLetter)
  observedStateEq : LocalizedUniversalReference.referenceState input stepObserved.t =
    some (.chiral observedLetter)
  imageObservedStateEq : LocalizedUniversalReference.referenceState input stepObserved.u =
    some (.chiral imageObservedLetter)





theorem exists_actualPhysicalReaderPair
    {input : LocalizedUniversalReference.Input}
    {context : PhysicalAutomorphismContext input}
    {dReference dObserved : input.certified.detectedMultiCenterMolecule.Center}
    (stepReference : PhysicalReaderStep input context dReference)
    (stepObserved : PhysicalReaderStep input context dObserved) :
    Nonempty (ActualPhysicalReaderPair input context dReference dObserved) := by
  obtain ⟨referenceLetter, referenceStateEq⟩ := stepReference.exists_t_letter
  obtain ⟨imageReferenceLetter, imageReferenceStateEq⟩ := stepReference.exists_u_letter
  obtain ⟨observedLetter, observedStateEq⟩ := stepObserved.exists_t_letter
  obtain ⟨imageObservedLetter, imageObservedStateEq⟩ := stepObserved.exists_u_letter
  exact ⟨{ stepReference := stepReference
           stepObserved := stepObserved
           referenceLetter := referenceLetter
           imageReferenceLetter := imageReferenceLetter
           observedLetter := observedLetter
           imageObservedLetter := imageObservedLetter
           referenceStateEq := referenceStateEq
           imageReferenceStateEq := imageReferenceStateEq
           observedStateEq := observedStateEq
           imageObservedStateEq := imageObservedStateEq }⟩

/-- **Physical contrast of the actual generated source observations.**  The actual source Rule-4b
observation at the image pair (image reference occurrence, image observed occurrence) equals the
actual source observation at the original pair exactly when the physical discrepancies of the
automorphism at the reference and observed centres agree.  Everything on the left is produced from
the actual reader, not assumed. -/
theorem ActualPhysicalReaderPair.sourceObservation_contrast
    {input : LocalizedUniversalReference.Input}
    {context : PhysicalAutomorphismContext input}
    {dReference dObserved : input.certified.detectedMultiCenterMolecule.Center}
    (pair : ActualPhysicalReaderPair input context dReference dObserved) :
    sourceObserveRule4bLabel pair.imageReferenceLetter (some (.chiral pair.imageObservedLetter)) =
      sourceObserveRule4bLabel pair.referenceLetter (some (.chiral pair.observedLetter)) ↔
      localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
          dReference =
        localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
          dObserved :=
  pair.stepReference.sourceObservation_contrast pair.stepObserved pair.referenceLetter
    pair.imageReferenceLetter pair.observedLetter pair.imageObservedLetter
    pair.referenceStateEq pair.imageReferenceStateEq pair.observedStateEq
    pair.imageObservedStateEq

/-- **Turnkey physical pair contrast.**  From the two physical reader steps alone there exists an
actual reader pair whose image-pair source observation agrees with the original pair exactly when
the two physical discrepancies agree.  No actual label is supplied. -/
theorem exists_actualSourceObservation_contrast
    {input : LocalizedUniversalReference.Input}
    {context : PhysicalAutomorphismContext input}
    {dReference dObserved : input.certified.detectedMultiCenterMolecule.Center}
    (stepReference : PhysicalReaderStep input context dReference)
    (stepObserved : PhysicalReaderStep input context dObserved) :
    ∃ pair : ActualPhysicalReaderPair input context dReference dObserved,
      (sourceObserveRule4bLabel pair.imageReferenceLetter
          (some (.chiral pair.imageObservedLetter)) =
        sourceObserveRule4bLabel pair.referenceLetter (some (.chiral pair.observedLetter)) ↔
        localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
            dReference =
          localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
            dObserved) := by
  obtain ⟨pair⟩ := exists_actualPhysicalReaderPair stepReference stepObserved
  exact ⟨pair, pair.sourceObservation_contrast⟩











/-- **An absent or non-chiral label carries no Rule-4b pair.**  Only an uppercase chiral
observation produces a like/unlike component; absence and pseudoasymmetry stay pair-free. -/
theorem sourceObserveRule4bLabel_pair?_eq_none_of_not_chiral (reference : RS)
    (label : Option LocalizedAuxiliaryLabel)
    (notChiral : ∀ letter, label ≠ some (.chiral letter)) :
    (sourceObserveRule4bLabel reference label).pair? = none := by
  cases label with
  | none => rfl
  | some label =>
      cases label with
      | chiral letter => exact absurd rfl (notChiral letter)
      | pseudoasymmetric descriptor => rfl

/-- A Rule-4a-only source observation never carries a Rule-4b pair. -/
theorem sourceObserveRule4aLabel_pair?_eq_none (label : Option LocalizedAuxiliaryLabel) :
    (sourceObserveRule4aLabel label).pair? = none := by
  cases label with
  | none => rfl
  | some label => cases label <;> rfl

/-- **The actual Rule-4b build position decodes to the actual source observation.**  A successful
actual cumulative build at a selected reference stores at its head address exactly this stage's
root priority vector, and that vector decodes to the reference-relative source observation of the
actual restricted dependency label at the source cursor.  Both identities concern the actual key;
no vector and no observation is supplied. -/
theorem sourceBuildHead_rule4b_observation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (reference : RS) (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      (.rule4b reference) target view fuel cursor = some key) :
    key.descriptor.head? =
        some [([], localizedCumulativeRule45Priority (.rule4b reference)
          (input.localizedDependencyLabel target view cursor))] ∧
      sourceDecodeRule45Vector?
          (localizedCumulativeRule45Priority (.rule4b reference)
            (input.localizedDependencyLabel target view cursor)) =
        some (sourceObserveRule4bLabel reference
          (input.localizedDependencyLabel target view cursor)) :=
  ⟨sourceBuildCumulative_descriptor_head input (.rule4b reference) target view fuel cursor key
      computed,
    sourceDecodeRule45Vector?_rule4b reference _⟩

/-- **The actual Rule-4a build position.**  The no-reference cumulative stage stores the Rule-4a
priority vector at the head address, and its source observation carries no pair. -/
theorem sourceBuildHead_rule4a_observation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor = some key) :
    key.descriptor.head? =
        some [([], localizedCumulativeRule45Priority .rule4a
          (input.localizedDependencyLabel target view cursor))] ∧
      sourceDecodeRule45Vector?
          (localizedCumulativeRule45Priority .rule4a
            (input.localizedDependencyLabel target view cursor)) =
        some (sourceObserveRule4aLabel (input.localizedDependencyLabel target view cursor)) ∧
      (sourceObserveRule4aLabel (input.localizedDependencyLabel target view cursor)).pair? =
        none :=
  ⟨sourceBuildCumulative_descriptor_head input .rule4a target view fuel cursor key computed,
    sourceDecodeRule45Vector?_rule4a _,
    sourceObserveRule4aLabel_pair?_eq_none _⟩

/-- **The actual source observation at the actual occurrence.**  When the source cursor occurrence
is a strict depth dependency of the build target, the restricted read is the whole actual reader
state at that occurrence; hence the actual head vector decodes to the Rule-4b observation of the
actual selected reference against the letter the reader actually returns at the occurrence. -/
theorem sourceBuildHead_rule4b_stateObservation
    (input : LocalizedUniversalReference.Input)
    (target : LocalizedUniversalReference.Occurrence input)
    (reference letter : RS) (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (key : input.certified.LocalizedRerootCumulativeRule45Key)
    (computed : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (.rule4b reference) target
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) target) fuel cursor = some key)
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence target)
    (stateEq : LocalizedUniversalReference.referenceState input cursor.occurrence =
      some (.chiral letter)) :
    key.descriptor.head? =
        some [([], localizedCumulativeRule45Priority (.rule4b reference)
          (input.certified.localizedDependencyLabel target
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input) target) cursor))] ∧
      sourceDecodeRule45Vector?
          (localizedCumulativeRule45Priority (.rule4b reference)
            (input.certified.localizedDependencyLabel target
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input) target) cursor)) =
        some (sourceObserveRule4bLabel reference (some (.chiral letter))) := by
  have head := sourceBuildCumulative_descriptor_head input.certified (.rule4b reference) target
    (input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target) fuel cursor key computed
  refine ⟨head, ?_⟩
  rw [localizedDependencyLabel_eq_state_of_dependency input.certified target
    (LocalizedUniversalReference.referenceState input) cursor dependency, stateEq]
  exact sourceDecodeRule45Vector?_rule4b reference _

/-- **Actual build position and the physical pair class.**  Suppose the actual selected reference
letter is the physical uppercase letter of the reference occurrence's normalized sense (the
detected/canonical-frame conversion `RS.ofHandedness` of `PhysicalRule4bOrderData`), and the
observed source-cursor occurrence carries the physical uppercase letter of its own normalized
sense.  Then the actual head vector of the actual Rule-4b build decodes to the physical pair class
of the two normalized senses: `like` exactly when their product is one. -/
theorem sourceBuildHead_rule4b_physicalPairClass
    (input : LocalizedUniversalReference.Input)
    {m : MultiCenterMolecule input.certified.Atom}
    {cfg : m.Configuration}
    (target : LocalizedUniversalReference.Occurrence input)
    (reference : RS)
    (referenceOccurrence : LocalizedUniversalReference.Occurrence input)
    (centerReference : m.Center)
    (centerTetraReference : input.certified.TetrahedralCenter)
    (centerRealReference : input.certified.RealTetrahedralCenterNode
      referenceOccurrence.1.node centerTetraReference)
    (referenceData : PhysicalRule4bOrderData input m cfg referenceOccurrence centerReference
      centerTetraReference centerRealReference)
    (referenceEq : reference = RS.ofHandedness referenceData.normalizedSense)
    (fuel : Nat)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (centerObserved : m.Center)
    (centerTetraObserved : input.certified.TetrahedralCenter)
    (centerRealObserved : input.certified.RealTetrahedralCenterNode
      cursor.occurrence.1.node centerTetraObserved)
    (observedData : PhysicalRule4bOrderData input m cfg cursor.occurrence centerObserved
      centerTetraObserved centerRealObserved)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence target)
    (key : input.certified.LocalizedRerootCumulativeRule45Key)
    (computed : input.certified.buildLocalizedRerootCumulativeRule45Key?
      (.rule4b reference) target
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) target) fuel cursor = some key) :
    key.descriptor.head? =
        some [([], localizedCumulativeRule45Priority (.rule4b reference)
          (input.certified.localizedDependencyLabel target
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input) target) cursor))] ∧
      sourceDecodeRule45Vector?
          (localizedCumulativeRule45Priority (.rule4b reference)
            (input.certified.localizedDependencyLabel target
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input) target) cursor)) =
        some (.withRule4b .chiral
          (some (physicalPairClass referenceData.normalizedSense
            observedData.normalizedSense))) := by
  have head := sourceBuildCumulative_descriptor_head input.certified (.rule4b reference) target
    (input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target) fuel cursor key computed
  refine ⟨head, ?_⟩
  have labelEq : input.certified.localizedDependencyLabel target
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) target) cursor =
      some (.chiral (RS.ofHandedness observedData.normalizedSense)) := by
    rw [localizedDependencyLabel_eq_state_of_dependency input.certified target
      (LocalizedUniversalReference.referenceState input) cursor dependency]
    exact observedData.referenceState_eq_chiral noDouble
  rw [labelEq, sourceDecodeRule45Vector?_rule4b reference, referenceEq]
  exact congrArg some (sourceObserveRule4bLabel_ofHandedness_pairClass
    (referenceData.normalizedSense_eq_one_or_neg_one)
    (observedData.normalizedSense_eq_one_or_neg_one))

/-- **The selected reference is the actual reader letter at the reference occurrence.**  When the
selected reference letter is the physical uppercase letter of the reference occurrence's
normalized sense, the actual reader at that occurrence returns exactly that letter.  This is the
selected-reference identity: the source observation compares the observed occurrence against a
letter that the reader actually produces at a concrete occurrence, not against a supplied
desired label. -/
theorem selectedReference_eq_referenceState_of_orderData
    {input : LocalizedUniversalReference.Input}
    {m : MultiCenterMolecule input.certified.Atom}
    {cfg : m.Configuration}
    {referenceOccurrence : LocalizedUniversalReference.Occurrence input}
    {center : m.Center}
    {centerTetra : input.certified.TetrahedralCenter}
    {centerReal : input.certified.RealTetrahedralCenterNode
      referenceOccurrence.1.node centerTetra}
    (data : PhysicalRule4bOrderData input m cfg referenceOccurrence center centerTetra centerReal)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (reference : RS)
    (referenceEq : reference = RS.ofHandedness data.normalizedSense) :
    LocalizedUniversalReference.referenceState input referenceOccurrence =
      some (.chiral reference) := by
  rw [referenceEq]
  exact data.referenceState_eq_chiral noDouble

/-- **The empty-reference branch.**  An empty selected-reference population produces exactly the
genuine no-reference alternative `none`, and its source stage is Rule 4a.  Consequently the actual
build at that alternative is the Rule-4a-only build of `sourceBuildHead_rule4a_observation`, whose
observation has no pair: no like/unlike class is asserted when no reference exists. -/
theorem localizedRule4bcReferenceAlternatives_nil_stage :
    localizedRule4bcReferenceAlternatives ([] : List RS) = [none] ∧
      sourceStageOfReference none = .rule4a :=
  ⟨rfl, rfl⟩

/-! ## G. Kernel-authority guards for the exported endpoints -/

assert_kernel_only TetraStereo.OneCenter.localDiscrepancy_eq_one_or_neg_one
assert_kernel_only TetraStereo.OneCenter.localDiscrepancy_ne_zero
assert_kernel_only TetraStereo.OneCenter.actualLocalSignLaw_iff_localDiscrepancy
assert_kernel_only TetraStereo.OneCenter.actualLocalSignLaw_discrepancyMirror
assert_kernel_only TetraStereo.OneCenter.actualLocalSignLaw_iff_mirror_eq
assert_kernel_only TetraStereo.OneCenter.discrepancyMirror_eq_iff
assert_kernel_only TetraStereo.OneCenter.localDiscrepancy_reindexFrames
assert_kernel_only TetraStereo.OneCenter.reflectUppercaseOptionalLabel_chiral_eq_iff
assert_kernel_only TetraStereo.OneCenter.ofHandedness_eq_iff_mul_eq_one
assert_kernel_only TetraStereo.OneCenter.ofHandedness_beq_iff_mul_eq_one
assert_kernel_only TetraStereo.OneCenter.physicalPairClass_eq_like_iff
assert_kernel_only TetraStereo.OneCenter.physicalPairClass_eq_unlike_iff
assert_kernel_only TetraStereo.OneCenter.sourceObserveRule4bLabel_ofHandedness_pairClass
assert_kernel_only TetraStereo.OneCenter.sourceObserveRule4bLabel_reflect_contrast
assert_kernel_only TetraStereo.OneCenter.physicalNormalizedSense_eq_one_or_neg_one
assert_kernel_only TetraStereo.OneCenter.descriptorOfParity_writtenSign_eq_ofHandedness_normalizedSense
assert_kernel_only TetraStereo.OneCenter.PhysicalRule4bOrderData.normalizedSense_eq_one_or_neg_one
assert_kernel_only TetraStereo.OneCenter.PhysicalRule4bOrderData.referenceState_eq_chiral
assert_kernel_only TetraStereo.OneCenter.exists_physicalRule4bOrderData
assert_kernel_only TetraStereo.OneCenter.PhysicalReaderStep.reader_reflect
assert_kernel_only TetraStereo.OneCenter.PhysicalReaderStep.sourceObservation_contrast
assert_kernel_only TetraStereo.OneCenter.PhysicalReaderStep.sourceObservation_differ
assert_kernel_only TetraStereo.OneCenter.PhysicalReaderStep.exists_t_letter
assert_kernel_only TetraStereo.OneCenter.PhysicalReaderStep.exists_u_letter
assert_kernel_only TetraStereo.OneCenter.exists_actualPhysicalReaderPair
assert_kernel_only TetraStereo.OneCenter.ActualPhysicalReaderPair.sourceObservation_contrast
assert_kernel_only TetraStereo.OneCenter.exists_actualSourceObservation_contrast
assert_kernel_only TetraStereo.OneCenter.sourceObserveRule4bLabel_pair?_eq_none_of_not_chiral
assert_kernel_only TetraStereo.OneCenter.sourceObserveRule4aLabel_pair?_eq_none
assert_kernel_only TetraStereo.OneCenter.sourceBuildHead_rule4b_observation
assert_kernel_only TetraStereo.OneCenter.sourceBuildHead_rule4a_observation
assert_kernel_only TetraStereo.OneCenter.sourceBuildHead_rule4b_stateObservation
assert_kernel_only TetraStereo.OneCenter.sourceBuildHead_rule4b_physicalPairClass
assert_kernel_only TetraStereo.OneCenter.selectedReference_eq_referenceState_of_orderData
assert_kernel_only TetraStereo.OneCenter.localizedRule4bcReferenceAlternatives_nil_stage
assert_kernel_only TetraStereo.OneCenter.localDiscrepancy
assert_kernel_only TetraStereo.OneCenter.discrepancyMirror
assert_kernel_only TetraStereo.OneCenter.physicalPairClass
assert_kernel_only TetraStereo.OneCenter.physicalWrittenSign
assert_kernel_only TetraStereo.OneCenter.physicalNormalizedSense
assert_kernel_only TetraStereo.OneCenter.PhysicalRule4bOrderData.normalizedSense

end TetraStereo.OneCenter
