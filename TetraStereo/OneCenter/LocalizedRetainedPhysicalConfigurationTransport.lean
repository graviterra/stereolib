import TetraStereo.OneCenter.LocalizedRetainedActualFrameTransport
import TetraStereo.OneCenter.LocalizedRootZAutomorphismLabelCovariance
import TetraStereo.OneCenter.MultiCenterDetection
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.KernelOnly
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Sign transport for actual frames

`actualFrame_orientedVolume_calibration` is the strong intermediate in which image
points are the identity or a `z`-reflection of source points. It is not used here.
An arbitrary conformation with the same handedness need not have those coordinates
or the same distances.

Two sign laws are proved. They are not the same factor.

* `actualFrame_orientedVolumeSign_transport` is proper action. The source volume is
  calibrated to `cfg` and the image volume to `e • cfg`. `permHandedness framePerm`
  is only the parity of the detected ligand enumeration. An odd enumeration is not
  a physical mirror.
* `actualFrame_orientedVolumeSign_branchMirror` is the physical mirror law. Source
  and image volumes are both calibrated to the same actual `cfg`. `BranchTransport`
  at a reached detected center supplies an independent factor
  `if mirror then -1 else 1`. The frame-slot sign is that factor times
  `permHandedness slotPerm` times the source sign. The mirror factor is not
  absorbed into `framePerm`.

`configurationSign_mul_ligandPermAt` is the enumeration step inside proper action,
transported onto `framePerm` by `framePerm_eq_ligandPermAt`. Calibration has the
shape of `DomainPhysicalFrameData.signEq`: the sign of the oriented volume in
`detectedMultiCenterMolecule.ligandAtomAt` order is `configurationSign` at that
center. `sourceReindex`, `imageReindex`, and `slotPerm` come from the actual frames.

`configurationSign` is the handedness of a local frame permutation. It is not a
CIP letter and it is not a generated descriptor. `DomainPhysicalContext` is not a
hypothesis: it requires `Acyclic`. Parent and ring-duplicate slots stay because
every theorem quantifies over the actual frame cursors.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-- The tetrahedral-center proof carried by a detected center. -/
def sourceTetra (center : input.TetrahedralCenter) :
    input.moleculeGraph.IsTetrahedralCenter center.1 :=
  (input.moleculeGraph.mem_tetrahedralCenterSet center.1).mp center.2

/-- The same center as a center of the detected multi-center molecule. -/
def physicalSourceCenter (center : input.TetrahedralCenter) :
    input.detectedMultiCenterMolecule.Center :=
  ⟨center.1, center.2⟩

/-- The graph automorphism as an automorphism of the detected molecule. -/
def physicalDetectedAut (e : input.moleculeGraph.Aut) :
    input.detectedMultiCenterMolecule.Aut :=
  input.moleculeGraph.detectedMultiCenterAutOfGraphAut e

/-- Image of a detected center under that automorphism. -/
noncomputable def physicalImageCenter (e : input.moleculeGraph.Aut)
    (center : input.TetrahedralCenter) : input.detectedMultiCenterMolecule.Center :=
  input.detectedMultiCenterMolecule.centerPerm (input.physicalDetectedAut e)
    (input.physicalSourceCenter center)

/-- Oriented volume in detected-enumeration order. -/
abbrev enumerationVolume (pointAt : Fin 4 → CartesianPoint3) : ℚ :=
  CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3)

/-- The same points read in an arbitrary ligand order. -/
abbrev reindexedVolume (pointAt : Fin 4 → CartesianPoint3) (order : Equiv.Perm (Fin 4)) : ℚ :=
  CartesianPoint3.orientedVolume (pointAt (order 0)) (pointAt (order 1))
    (pointAt (order 2)) (pointAt (order 3))

theorem ligandEnum_proof_irrel (center : input.Atom)
    (h1 h2 : input.moleculeGraph.IsTetrahedralCenter center) :
    input.moleculeGraph.ligandEquivOfIsTetrahedralCenter center h1 =
      input.moleculeGraph.ligandEquivOfIsTetrahedralCenter center h2 := by
  have proofEq : h1 = h2 := Subsingleton.elim h1 h2
  rw [proofEq]

/-- Detected `ligandAtomAt` is the value of `ligandEquivOfIsTetrahedralCenter`. -/
theorem detectedLigandAtom_eq_enum (center : input.TetrahedralCenter) (i : Fin 4) :
    input.detectedMultiCenterMolecule.ligandAtomAt (input.physicalSourceCenter center) i =
      (input.moleculeGraph.ligandEquivOfIsTetrahedralCenter center.1 (input.sourceTetra center)
        i).1 := by
  rfl

/-- The configuration image center is the transported tetrahedral center. -/
theorem physicalImageCenter_eq (e : input.moleculeGraph.Aut) (center : input.TetrahedralCenter) :
    input.physicalImageCenter e center =
      input.physicalSourceCenter (input.transportTetrahedralCenter e center) := by
  apply Subtype.ext
  rfl

/-- `framePerm` sends detected ligand atoms to their images under the automorphism. -/
theorem framePerm_ligandAtom_transport (e : input.moleculeGraph.Aut)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    input.detectedMultiCenterMolecule.ligandAtomAt (input.physicalImageCenter e center)
        (input.framePerm e center.1 (input.sourceTetra center) index) =
      (e : Equiv.Perm input.Atom)
        (input.detectedMultiCenterMolecule.ligandAtomAt (input.physicalSourceCenter center)
          index) := by
  let tetra := input.sourceTetra center
  let imageCenter := input.transportTetrahedralCenter e center
  let imageTetraAuto :=
    (input.moleculeGraph.isTetrahedralCenter_apply_aut_iff e center.1).2 tetra
  let imageTetraDetected := input.sourceTetra imageCenter
  have centerEq : input.physicalImageCenter e center = input.physicalSourceCenter imageCenter :=
    input.physicalImageCenter_eq e center
  have enumIrrel :=
    input.ligandEnum_proof_irrel imageCenter.1 imageTetraAuto imageTetraDetected
  have imageDetected := input.detectedLigandAtom_eq_enum imageCenter
    (input.framePerm e center.1 tetra index)
  have sourceDetected := input.detectedLigandAtom_eq_enum center index
  have moved := input.framePerm_ligand e center.1 tetra index
  calc
    input.detectedMultiCenterMolecule.ligandAtomAt (input.physicalImageCenter e center)
        (input.framePerm e center.1 tetra index)
      = input.detectedMultiCenterMolecule.ligandAtomAt (input.physicalSourceCenter imageCenter)
          (input.framePerm e center.1 tetra index) := by rw [centerEq]
    _ = (input.moleculeGraph.ligandEquivOfIsTetrahedralCenter imageCenter.1 imageTetraDetected
          (input.framePerm e center.1 tetra index)).1 := imageDetected
    _ = (input.moleculeGraph.ligandEquivOfIsTetrahedralCenter imageCenter.1 imageTetraAuto
          (input.framePerm e center.1 tetra index)).1 := by rw [← enumIrrel]
    _ = (e : Equiv.Perm input.Atom)
          ((input.moleculeGraph.ligandEquivOfIsTetrahedralCenter center.1 tetra index).1) :=
        moved
    _ = (e : Equiv.Perm input.Atom)
          (input.detectedMultiCenterMolecule.ligandAtomAt (input.physicalSourceCenter center)
            index) := by rw [← sourceDetected]

/-- `framePerm` is the detected molecule's `ligandPermAt`. -/
theorem framePerm_eq_ligandPermAt (e : input.moleculeGraph.Aut)
    (center : input.TetrahedralCenter) :
    input.framePerm e center.1 (input.sourceTetra center) =
      input.detectedMultiCenterMolecule.ligandPermAt (input.physicalDetectedAut e)
        (input.physicalSourceCenter center) := by
  classical
  refine Equiv.ext fun index => ?_
  apply input.detectedMultiCenterMolecule.ligandAtomAt_injective
    (input.physicalImageCenter e center)
  unfold physicalImageCenter
  rw [input.detectedMultiCenterMolecule.ligandAtomAt_ligandPermAt
    (input.physicalDetectedAut e) (input.physicalSourceCenter center) index]
  exact input.framePerm_ligandAtom_transport e center index

/-- Proper action on configurations. `permHandedness framePerm` is detected-ligand
enumeration parity under `e`, not the physical mirror of `BranchTransport`. -/
theorem configurationSign_mul_framePerm (e : input.moleculeGraph.Aut)
    (center : input.TetrahedralCenter) (cfg : input.detectedMultiCenterMolecule.Configuration) :
    input.detectedMultiCenterMolecule.configurationSign cfg (input.physicalSourceCenter center) *
        permHandedness (input.framePerm e center.1 (input.sourceTetra center)) =
      input.detectedMultiCenterMolecule.configurationSign
        ((input.physicalDetectedAut e) • cfg) (input.physicalImageCenter e center) := by
  rw [input.framePerm_eq_ligandPermAt e center]
  exact RootedTetrahedralBranchSymmetry.configurationSign_mul_ligandPermAt
    input.detectedMultiCenterMolecule (input.physicalDetectedAut e) cfg
    (input.physicalSourceCenter center)

/-- `permHandedness framePerm` is `1` or `-1`. This is enumeration parity, not a
physical mirror. -/
theorem framePerm_enumerationParity_one_or_neg (e : input.moleculeGraph.Aut)
    (center : input.TetrahedralCenter) :
    permHandedness (input.framePerm e center.1 (input.sourceTetra center)) = 1 ∨
      permHandedness (input.framePerm e center.1 (input.sourceTetra center)) = -1 :=
  permHandedness_eq_one_or_eq_neg_one _

/-- Boolean form of the enumeration parity. `true` means the detected ligand
enumeration is odd. It is not `BranchTransport`'s mirror flag. -/
theorem framePerm_enumerationParity_bool (e : input.moleculeGraph.Aut)
    (center : input.TetrahedralCenter) :
    ∃ oddEnumeration : Bool,
      permHandedness (input.framePerm e center.1 (input.sourceTetra center)) =
        if oddEnumeration then -1 else 1 := by
  rcases input.framePerm_enumerationParity_one_or_neg e center with even | odd
  · exact ⟨false, by simp [even]⟩
  · exact ⟨true, by simp [odd]⟩

theorem permHandedness_mul_ne_zero (σ τ : Equiv.Perm (Fin 4)) :
    permHandedness σ * permHandedness τ ≠ 0 := by
  rcases permHandedness_eq_one_or_eq_neg_one σ with hσ | hσ <;>
    rcases permHandedness_eq_one_or_eq_neg_one τ with hτ | hτ <;>
      norm_num [hσ, hτ]

theorem rationalVolumeSign_eq_zero_iff (volume : ℚ) :
    rationalVolumeSign volume = 0 ↔ volume = 0 := by
  constructor
  · intro signZero
    by_contra nonzero
    rcases rationalVolumeSign_eq_neg_or_one nonzero with negative | positive
    · rw [negative] at signZero
      norm_num at signZero
    · rw [positive] at signZero
      norm_num at signZero
  · intro zero
    rw [zero]
    simp [rationalVolumeSign]

/-- Any ligand order, not a CIP sort: the sign scales by `permHandedness order`. -/
theorem calibratedVolumeSign_anyOrder (pointAt : Fin 4 → CartesianPoint3)
    (order : Equiv.Perm (Fin 4)) {signAt : ℝ}
    (calibration : rationalVolumeSign (enumerationVolume pointAt) = signAt) :
    rationalVolumeSign (reindexedVolume pointAt order) = signAt * permHandedness order := by
  have volumeEq : reindexedVolume pointAt order =
      RationalTetrahedralPermutation.permutedOrientedVolume
        (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) order :=
    orientedVolume_calibrated_eq (fun index => pointAt (order index)) pointAt order
      (fun _ => rfl)
  rw [volumeEq, rationalVolumeSign_permutedOrientedVolume, calibration]

theorem enumerationCalibration_ne_zero (pointAt : Fin 4 → CartesianPoint3)
    (σ : Equiv.Perm (Fin 4))
    (calibration : rationalVolumeSign (enumerationVolume pointAt) = permHandedness σ) :
    enumerationVolume pointAt ≠ 0 := by
  intro zero
  have signZero := (rationalVolumeSign_eq_zero_iff (enumerationVolume pointAt)).2 zero
  rw [calibration] at signZero
  rcases permHandedness_eq_one_or_eq_neg_one σ with even | odd
  · rw [even] at signZero
    norm_num at signZero
  · rw [odd] at signZero
    norm_num at signZero

theorem zero_enumeration_refuses (pointAt : Fin 4 → CartesianPoint3)
    (zero : enumerationVolume pointAt = 0) :
    descriptorOfOrientedVolume? (enumerationVolume pointAt) = none :=
  actualFrame_zero_volume_refuses (enumerationVolume pointAt) zero

theorem actualFrame_slotPerm_handedness
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center) :
    permHandedness packed.slotPerm =
      permHandedness packed.imageReindex *
        (permHandedness (input.framePerm e center.1 (input.sourceTetra center)) *
          permHandedness packed.sourceReindex) := by
  have transMul : ∀ σ τ : Equiv.Perm (Fin 4),
      permHandedness (σ.trans τ) = permHandedness τ * permHandedness σ := by
    intro σ τ
    have compose : σ.trans τ = τ * σ := by
      ext i
      rfl
    rw [compose, permHandedness_mul]
  rw [packed.slotPerm_eq, transMul, transMul]
  unfold permHandedness
  rw [Equiv.Perm.sign_symm]

/-- Every actual source slot, including a parent or a ring leaf, reads the detected ligand atom. -/
theorem actualFrame_sourceSlot_ligandAtom
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center) (i : Fin 4) :
    (packed.sourceFrame.cursorAt i).occurrence.1.node.current? =
      some (input.detectedMultiCenterMolecule.ligandAtomAt (input.physicalSourceCenter center)
        (packed.sourceReindex i)) := by
  rw [packed.source_current i]
  apply congrArg some
  have reindex := packed.reindex_source i
  have valEq : (packed.sourceLigand i).1 =
      (input.moleculeGraph.ligandEquivOfIsTetrahedralCenter center.1 (input.sourceTetra center)
        (packed.sourceReindex i)).1 :=
    congrArg Subtype.val reindex
  rw [valEq]
  exact (input.detectedLigandAtom_eq_enum center (packed.sourceReindex i)).symm

/-- Every actual image slot reads the detected ligand atom of the transported center. -/
theorem actualFrame_imageSlot_ligandAtom
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center) (i : Fin 4) :
    (packed.imageFrame.cursorAt i).occurrence.1.node.current? =
      some (input.detectedMultiCenterMolecule.ligandAtomAt (input.physicalImageCenter e center)
        (packed.imageReindex i)) := by
  rw [packed.image_current i]
  apply congrArg some
  let imageCenter := input.transportTetrahedralCenter e center
  let tetra := input.sourceTetra center
  let imageTetraAuto :=
    (input.moleculeGraph.isTetrahedralCenter_apply_aut_iff e center.1).2 tetra
  let imageTetraDetected := input.sourceTetra imageCenter
  have reindex := packed.reindex_image i
  have autoVal : (packed.imageLigand i).1 =
      (input.moleculeGraph.ligandEquivOfIsTetrahedralCenter imageCenter.1 imageTetraAuto
        (packed.imageReindex i)).1 :=
    congrArg Subtype.val reindex
  rw [autoVal]
  have irrel := input.ligandEnum_proof_irrel imageCenter.1 imageTetraAuto imageTetraDetected
  rw [irrel]
  have detected := input.detectedLigandAtom_eq_enum imageCenter (packed.imageReindex i)
  rw [← detected]
  rw [input.physicalImageCenter_eq e center]

theorem actualFrame_source_cursorPoint
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center)
    (sourcePointAt : Fin 4 → CartesianPoint3)
    (sourceObserved : ∀ j, input.spatialPointAt?
      (input.detectedMultiCenterMolecule.ligandAtomAt (input.physicalSourceCenter center) j) =
        some (sourcePointAt j))
    (i : Fin 4) :
    input.localizedRerootCursorSpatialPoint? (packed.sourceFrame.cursorAt i) =
      some (sourcePointAt (packed.sourceReindex i)) := by
  unfold localizedRerootCursorSpatialPoint?
  rw [input.actualFrame_sourceSlot_ligandAtom singleBonded e target center packed i]
  exact sourceObserved (packed.sourceReindex i)

theorem actualFrame_image_cursorPoint
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center)
    (imagePointAt : Fin 4 → CartesianPoint3)
    (imageObserved : ∀ j, input.spatialPointAt?
      (input.detectedMultiCenterMolecule.ligandAtomAt (input.physicalImageCenter e center) j) =
        some (imagePointAt j))
    (i : Fin 4) :
    input.localizedRerootCursorSpatialPoint? (packed.imageFrame.cursorAt i) =
      some (imagePointAt (packed.imageReindex i)) := by
  unfold localizedRerootCursorSpatialPoint?
  rw [input.actualFrame_imageSlot_ligandAtom singleBonded e target center packed i]
  exact imageObserved (packed.imageReindex i)

theorem actualFrame_source_volumeSign
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (sourcePointAt : Fin 4 → CartesianPoint3)
    (sourceCalibration : rationalVolumeSign (enumerationVolume sourcePointAt) =
      input.detectedMultiCenterMolecule.configurationSign cfg
        (input.physicalSourceCenter center)) :
    rationalVolumeSign (reindexedVolume sourcePointAt packed.sourceReindex) =
      input.detectedMultiCenterMolecule.configurationSign cfg
          (input.physicalSourceCenter center) *
        permHandedness packed.sourceReindex :=
  calibratedVolumeSign_anyOrder sourcePointAt packed.sourceReindex sourceCalibration

/-- Image frame sign when the image points are calibrated to the transported
configuration `e • cfg`. This is proper action, not the physical mirror law. -/
theorem actualFrame_image_volumeSign
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (imagePointAt : Fin 4 → CartesianPoint3)
    (imageCalibration : rationalVolumeSign (enumerationVolume imagePointAt) =
      input.detectedMultiCenterMolecule.configurationSign
        ((input.physicalDetectedAut e) • cfg) (input.physicalImageCenter e center)) :
    rationalVolumeSign (reindexedVolume imagePointAt packed.imageReindex) =
      input.detectedMultiCenterMolecule.configurationSign
          ((input.physicalDetectedAut e) • cfg) (input.physicalImageCenter e center) *
        permHandedness packed.imageReindex :=
  calibratedVolumeSign_anyOrder imagePointAt packed.imageReindex imageCalibration

theorem actualFrame_source_frameVolume_ne_zero
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (sourcePointAt : Fin 4 → CartesianPoint3)
    (sourceCalibration : rationalVolumeSign (enumerationVolume sourcePointAt) =
      input.detectedMultiCenterMolecule.configurationSign cfg
        (input.physicalSourceCenter center)) :
    reindexedVolume sourcePointAt packed.sourceReindex ≠ 0 := by
  intro zero
  have signZero :=
    (rationalVolumeSign_eq_zero_iff
      (reindexedVolume sourcePointAt packed.sourceReindex)).2 zero
  rw [input.actualFrame_source_volumeSign singleBonded e target center packed cfg sourcePointAt
    sourceCalibration] at signZero
  exact permHandedness_mul_ne_zero (cfg (input.physicalSourceCenter center))
    packed.sourceReindex signZero

theorem actualFrame_image_frameVolume_ne_zero
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (imagePointAt : Fin 4 → CartesianPoint3)
    (imageCalibration : rationalVolumeSign (enumerationVolume imagePointAt) =
      input.detectedMultiCenterMolecule.configurationSign
        ((input.physicalDetectedAut e) • cfg) (input.physicalImageCenter e center)) :
    reindexedVolume imagePointAt packed.imageReindex ≠ 0 := by
  intro zero
  have signZero :=
    (rationalVolumeSign_eq_zero_iff (reindexedVolume imagePointAt packed.imageReindex)).2 zero
  rw [input.actualFrame_image_volumeSign singleBonded e target center packed cfg imagePointAt
    imageCalibration] at signZero
  exact permHandedness_mul_ne_zero
    (((input.physicalDetectedAut e) • cfg) (input.physicalImageCenter e center))
    packed.imageReindex signZero

/-- Proper action. Source points calibrate to `cfg`; image points calibrate to
`e • cfg`. The two tuples need not be congruent. `permHandedness framePerm` is
enumeration parity already inside `slotPerm`, not a physical mirror. -/
theorem actualFrame_orientedVolumeSign_transport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (sourcePointAt imagePointAt : Fin 4 → CartesianPoint3)
    (sourceCalibration : rationalVolumeSign (enumerationVolume sourcePointAt) =
      input.detectedMultiCenterMolecule.configurationSign cfg
        (input.physicalSourceCenter center))
    (imageCalibration : rationalVolumeSign (enumerationVolume imagePointAt) =
      input.detectedMultiCenterMolecule.configurationSign
        ((input.physicalDetectedAut e) • cfg) (input.physicalImageCenter e center)) :
    rationalVolumeSign (reindexedVolume imagePointAt packed.imageReindex) =
      rationalVolumeSign (reindexedVolume sourcePointAt packed.sourceReindex) *
        permHandedness packed.slotPerm := by
  have sourceSign := input.actualFrame_source_volumeSign singleBonded e target center packed cfg
    sourcePointAt sourceCalibration
  have imageSign := input.actualFrame_image_volumeSign singleBonded e target center packed cfg
    imagePointAt imageCalibration
  have factor := input.configurationSign_mul_framePerm e center cfg
  have handed := input.actualFrame_slotPerm_handedness singleBonded e target center packed
  have square := permHandedness_mul_self packed.sourceReindex
  rw [imageSign, sourceSign, handed, ← factor]
  calc
    (input.detectedMultiCenterMolecule.configurationSign cfg (input.physicalSourceCenter center) *
          permHandedness (input.framePerm e center.1 (input.sourceTetra center))) *
        permHandedness packed.imageReindex
      = input.detectedMultiCenterMolecule.configurationSign cfg
            (input.physicalSourceCenter center) *
          permHandedness (input.framePerm e center.1 (input.sourceTetra center)) *
          permHandedness packed.imageReindex * 1 := by ring
    _ = input.detectedMultiCenterMolecule.configurationSign cfg
            (input.physicalSourceCenter center) *
          permHandedness (input.framePerm e center.1 (input.sourceTetra center)) *
          permHandedness packed.imageReindex *
          (permHandedness packed.sourceReindex * permHandedness packed.sourceReindex) := by
        rw [← square]
    _ = (input.detectedMultiCenterMolecule.configurationSign cfg
            (input.physicalSourceCenter center) * permHandedness packed.sourceReindex) *
          (permHandedness packed.imageReindex *
            (permHandedness (input.framePerm e center.1 (input.sourceTetra center)) *
              permHandedness packed.sourceReindex)) := by ring

/-- Physical mirror factor of `BranchTransport`. Independent of enumeration parity. -/
def physicalMirrorFactor (mirror : Bool) : ℝ :=
  if mirror then -1 else 1

/-- Turn the `BranchTransport` sign equation around.
`permHandedness (ligandPermAt e d)` stays the enumeration factor. -/
theorem configurationSign_image_of_branchSign
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (e : m.Aut) (cfg : m.Configuration)
    (mirror : Bool) (d : m.Center)
    (signLaw : m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
      physicalMirrorFactor mirror * m.configurationSign cfg (m.centerPerm e d)) :
    m.configurationSign cfg (m.centerPerm e d) =
      physicalMirrorFactor mirror * m.configurationSign cfg d *
        permHandedness (m.ligandPermAt e d) := by
  have square : physicalMirrorFactor mirror * physicalMirrorFactor mirror = 1 := by
    cases mirror <;> simp [physicalMirrorFactor]
  calc
    m.configurationSign cfg (m.centerPerm e d)
      = 1 * m.configurationSign cfg (m.centerPerm e d) := by ring
    _ = physicalMirrorFactor mirror * physicalMirrorFactor mirror *
          m.configurationSign cfg (m.centerPerm e d) := by rw [← square]
    _ = physicalMirrorFactor mirror *
          (physicalMirrorFactor mirror * m.configurationSign cfg (m.centerPerm e d)) := by ring
    _ = physicalMirrorFactor mirror *
          (m.configurationSign cfg d * permHandedness (m.ligandPermAt e d)) := by
        rw [← signLaw]
    _ = physicalMirrorFactor mirror * m.configurationSign cfg d *
          permHandedness (m.ligandPermAt e d) := by ring

/-- `BranchTransport` for the detected lift of the frame automorphism.
The sign field is the configuration relation, not a volume equation. -/
structure DetectedBranchTransport (e : input.moleculeGraph.Aut)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center) (i j : Fin 4) (mirror : Bool) : Prop where
  rootFixed : input.detectedMultiCenterMolecule.centerPerm (input.physicalDetectedAut e) root =
    root
  ligandSent : input.detectedMultiCenterMolecule.ligandPermAt (input.physicalDetectedAut e) root i =
    j
  signLaw : ∀ d : input.detectedMultiCenterMolecule.Center,
    RootedTetrahedralBranchSymmetry.LigandBranchReaches
        input.detectedMultiCenterMolecule root i d.1 →
      input.detectedMultiCenterMolecule.configurationSign cfg d *
          permHandedness (input.detectedMultiCenterMolecule.ligandPermAt
            (input.physicalDetectedAut e) d) =
        (if mirror then (-1 : ℝ) else 1) *
          input.detectedMultiCenterMolecule.configurationSign cfg
            (input.detectedMultiCenterMolecule.centerPerm (input.physicalDetectedAut e) d)

theorem DetectedBranchTransport.toBranchTransport {e : input.moleculeGraph.Aut}
    {cfg : input.detectedMultiCenterMolecule.Configuration}
    {root : input.detectedMultiCenterMolecule.Center} {i j : Fin 4} {mirror : Bool}
    (transport : input.DetectedBranchTransport e cfg root i j mirror) :
    RootedTetrahedralBranchSymmetry.BranchTransport input.detectedMultiCenterMolecule cfg root i j
      mirror :=
  ⟨input.physicalDetectedAut e, transport.rootFixed, transport.ligandSent, transport.signLaw⟩

/-- `BranchTransport` at the reached detected center, rewritten onto `framePerm`. -/
theorem detectedBranch_configurationSign_image (e : input.moleculeGraph.Aut)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center) (i j : Fin 4) (mirror : Bool)
    (center : input.TetrahedralCenter)
    (transport : input.DetectedBranchTransport e cfg root i j mirror)
    (reached : RootedTetrahedralBranchSymmetry.LigandBranchReaches
      input.detectedMultiCenterMolecule root i (input.physicalSourceCenter center).1) :
    input.detectedMultiCenterMolecule.configurationSign cfg (input.physicalImageCenter e center) =
      physicalMirrorFactor mirror *
        input.detectedMultiCenterMolecule.configurationSign cfg
          (input.physicalSourceCenter center) *
        permHandedness (input.framePerm e center.1 (input.sourceTetra center)) := by
  have raw := configurationSign_image_of_branchSign input.detectedMultiCenterMolecule
    (input.physicalDetectedAut e) cfg mirror (input.physicalSourceCenter center)
    (transport.signLaw (input.physicalSourceCenter center) reached)
  rw [← input.framePerm_eq_ligandPermAt e center] at raw
  exact raw

/-- Frame signs from a local configuration relation. `physicalMirrorFactor` is not
`permHandedness framePerm`; that parity stays inside `slotPerm`. The two point
tuples are independent. -/
theorem actualFrame_orientedVolumeSign_localPhysical
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center)
    (mirror : Bool) (sourceSign imageSign : ℝ)
    (relation : imageSign =
      physicalMirrorFactor mirror * sourceSign *
        permHandedness (input.framePerm e center.1 (input.sourceTetra center)))
    (sourcePointAt imagePointAt : Fin 4 → CartesianPoint3)
    (sourceCalibration : rationalVolumeSign (enumerationVolume sourcePointAt) = sourceSign)
    (imageCalibration : rationalVolumeSign (enumerationVolume imagePointAt) = imageSign) :
    rationalVolumeSign (reindexedVolume imagePointAt packed.imageReindex) =
      physicalMirrorFactor mirror * permHandedness packed.slotPerm *
        rationalVolumeSign (reindexedVolume sourcePointAt packed.sourceReindex) := by
  have sourceFrame := calibratedVolumeSign_anyOrder sourcePointAt packed.sourceReindex
    sourceCalibration
  have imageFrame := calibratedVolumeSign_anyOrder imagePointAt packed.imageReindex
    imageCalibration
  have handed := input.actualFrame_slotPerm_handedness singleBonded e target center packed
  have square := permHandedness_mul_self packed.sourceReindex
  rw [imageFrame, sourceFrame, relation, handed]
  calc
    (physicalMirrorFactor mirror * sourceSign *
          permHandedness (input.framePerm e center.1 (input.sourceTetra center))) *
        permHandedness packed.imageReindex
      = physicalMirrorFactor mirror * sourceSign *
          permHandedness (input.framePerm e center.1 (input.sourceTetra center)) *
          permHandedness packed.imageReindex * 1 := by ring
    _ = physicalMirrorFactor mirror * sourceSign *
          permHandedness (input.framePerm e center.1 (input.sourceTetra center)) *
          permHandedness packed.imageReindex *
          (permHandedness packed.sourceReindex * permHandedness packed.sourceReindex) := by
        rw [← square]
    _ = physicalMirrorFactor mirror *
          (permHandedness packed.imageReindex *
            (permHandedness (input.framePerm e center.1 (input.sourceTetra center)) *
              permHandedness packed.sourceReindex)) *
          (sourceSign * permHandedness packed.sourceReindex) := by ring

/-- Physical mirror law. Source and image coordinates both calibrate to `cfg`.
`transport` is `BranchTransport` for this frame automorphism, and `reached` is its
branch-reach premise at the mapped detected center. `e` does not provide
coordinates: the two calibrations are the physical input, and a missing
`spatialPointAt?` stays `none` in the cursor readback. Parent and ring slots stay
in `slotPerm`. -/
theorem actualFrame_orientedVolumeSign_branchMirror
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center) (i j : Fin 4) (mirror : Bool)
    (transport : input.DetectedBranchTransport e cfg root i j mirror)
    (reached : RootedTetrahedralBranchSymmetry.LigandBranchReaches
      input.detectedMultiCenterMolecule root i (input.physicalSourceCenter center).1)
    (sourcePointAt imagePointAt : Fin 4 → CartesianPoint3)
    (sourceCalibration : rationalVolumeSign (enumerationVolume sourcePointAt) =
      input.detectedMultiCenterMolecule.configurationSign cfg
        (input.physicalSourceCenter center))
    (imageCalibration : rationalVolumeSign (enumerationVolume imagePointAt) =
      input.detectedMultiCenterMolecule.configurationSign cfg
        (input.physicalImageCenter e center)) :
    rationalVolumeSign (reindexedVolume imagePointAt packed.imageReindex) =
      physicalMirrorFactor mirror * permHandedness packed.slotPerm *
        rationalVolumeSign (reindexedVolume sourcePointAt packed.sourceReindex) :=
  input.actualFrame_orientedVolumeSign_localPhysical singleBonded e target center packed mirror
    (input.detectedMultiCenterMolecule.configurationSign cfg (input.physicalSourceCenter center))
    (input.detectedMultiCenterMolecule.configurationSign cfg (input.physicalImageCenter e center))
    (input.detectedBranch_configurationSign_image e cfg root i j mirror center transport reached)
    sourcePointAt imagePointAt sourceCalibration imageCalibration

/-- Image frame volume is nonzero when it is calibrated to `cfg` at the image center.
The automorphism does not supply those coordinates. -/
theorem actualFrame_image_sameCfg_frameVolume_ne_zero
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {carrierFuel : Nat} (target : input.LocalizedCIPOccurrence carrierFuel)
    (center : input.TetrahedralCenter)
    (packed : input.ActualFrameSlotTransport singleBonded e target center)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (imagePointAt : Fin 4 → CartesianPoint3)
    (imageCalibration : rationalVolumeSign (enumerationVolume imagePointAt) =
      input.detectedMultiCenterMolecule.configurationSign cfg
        (input.physicalImageCenter e center)) :
    reindexedVolume imagePointAt packed.imageReindex ≠ 0 := by
  intro zero
  have signZero :=
    (rationalVolumeSign_eq_zero_iff (reindexedVolume imagePointAt packed.imageReindex)).2 zero
  rw [calibratedVolumeSign_anyOrder imagePointAt packed.imageReindex imageCalibration] at signZero
  exact permHandedness_mul_ne_zero (cfg (input.physicalImageCenter e center))
    packed.imageReindex signZero

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ligandEnum_proof_irrel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.detectedLigandAtom_eq_enum
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.physicalImageCenter_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.framePerm_ligandAtom_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.framePerm_eq_ligandPermAt
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.configurationSign_mul_framePerm
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.framePerm_enumerationParity_one_or_neg
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.framePerm_enumerationParity_bool
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.permHandedness_mul_ne_zero
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.rationalVolumeSign_eq_zero_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.calibratedVolumeSign_anyOrder
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.enumerationCalibration_ne_zero
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.zero_enumeration_refuses
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_slotPerm_handedness
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_sourceSlot_ligandAtom
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_imageSlot_ligandAtom
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_source_cursorPoint
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_image_cursorPoint
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_source_volumeSign
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_image_volumeSign
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_source_frameVolume_ne_zero
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_image_frameVolume_ne_zero
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_orientedVolumeSign_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.configurationSign_image_of_branchSign
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.DetectedBranchTransport.toBranchTransport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.detectedBranch_configurationSign_image
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_orientedVolumeSign_localPhysical
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_orientedVolumeSign_branchMirror
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualFrame_image_sameCfg_frameVolume_ne_zero

end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter
