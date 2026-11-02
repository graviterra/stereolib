/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TetraStereo.OneCenter.LocalizedIndependentAuxiliaryRS
import TetraStereo.OneCenter.LocalizedGeneralRigidPhysicalBranchInverse
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






























































































































/-! ## A. Domain data at one actual occurrence -/

/-- **The physical geometry derived from one original physical domain at one actual occurrence.**

`frame` is the actual four-ligand frame of the occurrence (`frameComputed` is the actual executable
frame call; `derived` is its declarative meaning).  `alpha` is the detected-enumeration slot
permutation: the cursor at slot `index` observes the molecule's own ligand atom
`ligandAtomAt center (alpha index)`.  `pointAt` reads the source coordinates of the molecule's own
ligand atoms, `nonzero` is the written oriented volume in the frame-slot order, and `signEq` ties
that same `pointAt` to the centre's sign in the **original** physical configuration `cfg` — it is
the domain's own calibration equation, retained rather than existentially discarded.

Every field is derived from the domain; none is a caller input. -/
structure DomainPhysicalFrameData
    (input : LocalizedUniversalReference.Input)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (target : LocalizedUniversalReference.Occurrence input)
    (center : input.certified.detectedMultiCenterMolecule.Center) where
  /-- The actual four-ligand occurrence frame. -/
  frame : input.certified.LocalizedOccurrenceFourLigandFrame
    (LocalizedUniversalReference.carrierFuel input)
  /-- The detected-enumeration ligand-slot permutation read by the frame cursors. -/
  alpha : Equiv.Perm (Fin 4)
  /-- The source coordinates of the molecule's own ligand atoms. -/
  pointAt : Fin 4 → CartesianPoint3
  /-- The frame is exactly the executable frame of the occurrence. -/
  frameComputed : input.certified.localizedOccurrenceFourLigandFrame? target = some frame
  /-- The declarative meaning of the executable frame. -/
  derived : input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame
  /-- Every frame cursor observes the molecule's own ligand atom at the slot `alpha index`. -/
  cursorAtom : ∀ index : Fin 4,
    (frame.cursorAt index).occurrence.1.node.current? =
      some (input.certified.detectedMultiCenterMolecule.ligandAtomAt center (alpha index))
  /-- The actual cursor-level spatial reads at the frame slots. -/
  spatial : ∀ index : Fin 4,
    input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
      some (pointAt (alpha index))
  /-- The source-coordinate reads of the molecule's own ligand atoms. -/
  observed : ∀ index : Fin 4,
    input.certified.spatialPointAt?
      (input.certified.detectedMultiCenterMolecule.ligandAtomAt center index) =
        some (pointAt index)
  /-- The written oriented volume of the frame-slot coordinates is nonzero. -/
  nonzero : CartesianPoint3.orientedVolume
    (pointAt (alpha 0)) (pointAt (alpha 1)) (pointAt (alpha 2)) (pointAt (alpha 3)) ≠ 0
  /-- **The retained original-configuration calibration.**  The sign of the source oriented volume
  in the molecule's own detected ligand enumeration is exactly the centre's sign in the original
  physical configuration `cfg`.  This is the domain's own calibration equation for the *same*
  `pointAt`; it is not a separately chosen existential. -/
  signEq : rationalVolumeSign
    (CartesianPoint3.orientedVolume (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3)) =
      input.certified.detectedMultiCenterMolecule.configurationSign cfg center

namespace DomainPhysicalFrameData

variable {input : LocalizedUniversalReference.Input}
variable {cfg : input.certified.detectedMultiCenterMolecule.Configuration}
variable {target : LocalizedUniversalReference.Occurrence input}
variable {center : input.certified.detectedMultiCenterMolecule.Center}

/-- The physically written coordinates in frame-slot order, as consumed by the descriptor. -/
def pointsAt (data : DomainPhysicalFrameData input cfg target center) :
    Fin 4 → CartesianPoint3 :=
  fun index => data.pointAt (data.alpha index)

/-- The frame-slot spatial reads, restated in `pointsAt` form. -/
theorem spatial_pointsAt (data : DomainPhysicalFrameData input cfg target center) :
    ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint? (data.frame.cursorAt index) =
        some (data.pointsAt index) := by
  intro index
  simpa [pointsAt] using data.spatial index

/-- The nonzero written volume in `pointsAt` form. -/
theorem nonzero_pointsAt (data : DomainPhysicalFrameData input cfg target center) :
    CartesianPoint3.orientedVolume
      (data.pointsAt 0) (data.pointsAt 1) (data.pointsAt 2) (data.pointsAt 3) ≠ 0 := by
  simpa [pointsAt] using data.nonzero

/-- **The frame-slot volume is the detected-enumeration volume permuted by `alpha`.** -/
theorem orientedVolume_pointsAt_eq (data : DomainPhysicalFrameData input cfg target center) :
    CartesianPoint3.orientedVolume
        (data.pointsAt 0) (data.pointsAt 1) (data.pointsAt 2) (data.pointsAt 3) =
      RationalTetrahedralPermutation.permutedOrientedVolume
        (data.pointAt 0) (data.pointAt 1) (data.pointAt 2) (data.pointAt 3) data.alpha :=
  orientedVolume_calibrated_eq data.pointsAt data.pointAt data.alpha (fun _ => rfl)

/-- **Sign transport through the detected-enumeration slot permutation.**  The written-order sign of
the frame-slot volume is the source sign scaled by the handedness of `alpha`. -/
theorem rationalVolumeSign_pointsAt_eq (data : DomainPhysicalFrameData input cfg target center) :
    rationalVolumeSign
        (CartesianPoint3.orientedVolume
          (data.pointsAt 0) (data.pointsAt 1) (data.pointsAt 2) (data.pointsAt 3)) =
      rationalVolumeSign
          (CartesianPoint3.orientedVolume
            (data.pointAt 0) (data.pointAt 1) (data.pointAt 2) (data.pointAt 3)) *
        permHandedness data.alpha := by
  rw [orientedVolume_pointsAt_eq, rationalVolumeSign_permutedOrientedVolume]

/-- **The frame-slot sign against the original physical configuration.**  The sign of the
frame-slot volume is the centre's sign in the original configuration `cfg`, scaled by the
handedness of the detected-enumeration slot permutation.  This is the normalized physical sense
tied to the untransported original configuration. -/
theorem rationalVolumeSign_pointsAt_eq_configurationSign
    (data : DomainPhysicalFrameData input cfg target center) :
    rationalVolumeSign
        (CartesianPoint3.orientedVolume
          (data.pointsAt 0) (data.pointsAt 1) (data.pointsAt 2) (data.pointsAt 3)) =
      input.certified.detectedMultiCenterMolecule.configurationSign cfg center *
        permHandedness data.alpha := by
  rw [rationalVolumeSign_pointsAt_eq, data.signEq]

/-! ### Uniqueness: the derived data is not a choice

Two derived data objects for the same actual occurrence agree on the frame, on the
detected-enumeration slot permutation and on the written coordinates.  The endpoint's coordinates
are therefore forced by the occurrence and the domain, not selected by `Classical.choice`. -/

/-- The executable frame call determines the frame. -/
theorem frame_eq (first second : DomainPhysicalFrameData input cfg target center) :
    first.frame = second.frame :=
  Option.some.inj (first.frameComputed.symm.trans second.frameComputed)

/-- The frame cursors and injectivity of the detected ligand enumeration determine the slot
permutation. -/
theorem alpha_eq (first second : DomainPhysicalFrameData input cfg target center) :
    first.alpha = second.alpha := by
  refine Equiv.ext (fun index => ?_)
  have firstAt := first.cursorAtom index
  have secondAt := second.cursorAtom index
  rw [frame_eq first second] at firstAt
  exact MultiCenterMolecule.ligandAtomAt_injective
    input.certified.detectedMultiCenterMolecule center
    (Option.some.inj (firstAt.symm.trans secondAt))

/-- The source-coordinate reads determine the source coordinates. -/
theorem pointAt_eq (first second : DomainPhysicalFrameData input cfg target center) :
    first.pointAt = second.pointAt := by
  funext index
  exact Option.some.inj ((first.observed index).symm.trans (second.observed index))

/-- The physically written coordinates in frame-slot order are unique. -/
theorem pointsAt_eq (first second : DomainPhysicalFrameData input cfg target center) :
    first.pointsAt = second.pointsAt := by
  funext index
  simp only [pointsAt, alpha_eq first second]
  exact congrFun (pointAt_eq first second) (second.alpha index)

end DomainPhysicalFrameData

/-! ## B. Deriving the data from the original physical domain -/





theorem calibratedOfDomain_of_notTwin
    (input : CertifiedLocalizedCIPInput)
    (cfg : input.detectedMultiCenterMolecule.Configuration)
    (root : input.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input input.detectedMultiCenterMolecule cfg root)
    (center : input.detectedMultiCenterMolecule.Center)
    (center_ne_root : center ≠ root)
    (notTwin : ¬ ActualPhysicalTerminalTwinCenter input input.detectedMultiCenterMolecule
      center) :
    ActualPhysicalGeneralRigidCalibratedCenter input input.detectedMultiCenterMolecule cfg
      center := by
  rcases domain.centerCase center center_ne_root with twin | calibrated
  · exact absurd twin notTwin
  · exact calibrated









theorem exists_domainPhysicalFrameData
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg root)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (center_ne_root : center ≠ root)
    (notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule center)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)) (pointAt : Fin 4 → CartesianPoint3),
      input.certified.localizedOccurrenceFourLigandFrame? target = some frame ∧
        input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame ∧
        (∀ index : Fin 4,
          (frame.cursorAt index).occurrence.1.node.current? =
            some (input.certified.detectedMultiCenterMolecule.ligandAtomAt center
              (alpha index))) ∧
        (∀ index : Fin 4,
          input.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt index) =
            some (pointAt (alpha index))) ∧
        (∀ index : Fin 4,
          input.certified.spatialPointAt?
            (input.certified.detectedMultiCenterMolecule.ligandAtomAt center index) =
              some (pointAt index)) ∧
        CartesianPoint3.orientedVolume
          (pointAt (alpha 0)) (pointAt (alpha 1)) (pointAt (alpha 2))
            (pointAt (alpha 3)) ≠ 0 ∧
        rationalVolumeSign
          (CartesianPoint3.orientedVolume
            (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3)) =
          input.certified.detectedMultiCenterMolecule.configurationSign cfg center ∧
        ConstitutionallyRigid input.certified.detectedMultiCenterMolecule center := by
  have calibrated : ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule cfg center :=
    calibratedOfDomain_of_notTwin input.certified cfg root domain center center_ne_root notTwin
  obtain ⟨rigid, pointAt, observed, nonzero, signEq⟩ := calibrated
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    simp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel,
      LocalizedReference.Input.molecule]
  obtain ⟨frame, alpha, frameComputed, ligandLink⟩ :=
    input.certified.exists_physicalFrameSlotLink target singleBonded acyclic enough center
      targetCurrent
  refine ⟨frame, alpha, pointAt, frameComputed,
    input.certified.localizedOccurrenceFourLigandFrame?_sound target frame frameComputed,
    ligandLink, ?_, observed, ?_, signEq, rigid⟩
  · intro index
    simp [localizedRerootCursorSpatialPoint?, ligandLink index, observed (alpha index)]
  · exact cartesianOrientedVolume_perm_ne_zero pointAt alpha nonzero

/-- **The canonical derived physical frame data** of one actual occurrence under one original
physical domain.  Every field is produced by `exists_domainPhysicalFrameData`; nothing is supplied
by the caller. -/
def domainPhysicalFrameData
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg root)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (center_ne_root : center ≠ root)
    (notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule center)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1) :
    DomainPhysicalFrameData input cfg target center :=
  Classical.choice (by
    obtain ⟨frame, alpha, pointAt, frameComputed, derived, cursorAtom, spatial, observed,
      nonzero, signEq, _rigid⟩ :=
      exists_domainPhysicalFrameData input singleBonded acyclic cfg root domain center
        center_ne_root notTwin target targetCurrent
    exact ⟨⟨frame, alpha, pointAt, frameComputed, derived, cursorAtom, spatial, observed,
      nonzero, signEq⟩⟩)

/-- The derived frame is exactly the occurrence's executable frame. -/
theorem domainPhysicalFrameData_frameComputed
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg root)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (center_ne_root : center ≠ root)
    (notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule center)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1) :
    input.certified.localizedOccurrenceFourLigandFrame? target =
      some (domainPhysicalFrameData input singleBonded acyclic cfg root domain center
        center_ne_root notTwin target targetCurrent).frame :=
  (domainPhysicalFrameData input singleBonded acyclic cfg root domain center center_ne_root
    notTwin target targetCurrent).frameComputed

/-- The derived data's centre is constitutionally rigid. -/
theorem constitutionallyRigid_of_domainPhysicalFrameData
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (root : input.certified.detectedMultiCenterMolecule.Center)
    (domain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg root)
    (center : input.certified.detectedMultiCenterMolecule.Center)
    (center_ne_root : center ≠ root)
    (notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule center)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1) :
    ConstitutionallyRigid input.certified.detectedMultiCenterMolecule center :=
  (calibratedOfDomain_of_notTwin input.certified cfg root domain center center_ne_root
    notTwin).1

/-! ## C. One original physical domain as a single context -/
























structure DomainPhysicalContext (input : LocalizedUniversalReference.Input) where
  /-- The certified molecule's bond graph is simple-bonded. -/
  singleBonded : input.certified.moleculeGraph.SimpleBonded
  /-- The certified molecule's bond graph is acyclic. -/
  acyclic : input.certified.moleculeGraph.Acyclic
  /-- Every atom carries the same formal charge. -/
  hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph
  /-- The molecule has no localized double-bond records. -/
  noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords
  /-- The original physical configuration enumeration. -/
  cfg : input.certified.detectedMultiCenterMolecule.Configuration
  /-- The original outer root. -/
  root : input.certified.detectedMultiCenterMolecule.Center
  /-- The actual general-rigid physical domain: original configuration, nondegenerate physical
  geometry at the rigid centres, terminal twins admitted at the remaining non-root candidates. -/
  domain : ActualGeneralRigidPhysicalDomain input.certified
    input.certified.detectedMultiCenterMolecule cfg root
  /-- The actual non-root centre under consideration. -/
  center : input.certified.detectedMultiCenterMolecule.Center
  /-- The centre is not the outer root. -/
  center_ne_root : center ≠ root
  /-- The actual occurrence whose current atom is the centre. -/
  target : LocalizedUniversalReference.Occurrence input
  /-- The occurrence's current atom is the centre. -/
  targetCurrent : target.1.node.current? = some center.1
  /-- The occurrence retains the domain's original outer root. -/
  root_eq : root.1 = target.1.root

/-- **The rigid branch of one original physical domain at one actual non-root centre.**  `notTwin`
selects the rigid disjunct of the domain's own case split at the centre; the calibrated data
(rigidity, source coordinates, nonzero volume and the original configuration sign) then follows
from `ActualGeneralRigidPhysicalDomain`.  The twin disjunct is the separate endpoint below. -/
structure DomainPhysicalRigidBranch {input : LocalizedUniversalReference.Input}
    (context : DomainPhysicalContext input) where
  /-- The centre is not a physical terminal twin, hence is a rigid calibrated centre. -/
  notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
    input.certified.detectedMultiCenterMolecule context.center

/-- A `Nodup` list whose pairs satisfy `r` satisfies `s` whenever `s` holds for every **distinct**
pair on which `r` holds.  Used to transfer a highest-first order from the physical priority to any
priority that agrees with it off the diagonal. -/
private theorem pairwise_of_nodup_pairwise {α : Type} {r s : α → α → Prop} {list : List α}
    (nodup : list.Nodup) (pairwise : list.Pairwise r)
    (step : ∀ first second, first ≠ second → r first second → s first second) :
    list.Pairwise s := by
  induction list with
  | nil => simp
  | cons head tail inductionHypothesis =>
      rw [List.pairwise_cons] at pairwise ⊢
      refine ⟨fun value member => step head value ?_ (pairwise.1 value member),
        inductionHypothesis (List.nodup_cons.mp nodup).2 pairwise.2⟩
      intro same
      exact (List.nodup_cons.mp nodup).1 (same ▸ member)

namespace DomainPhysicalContext

variable {input : LocalizedUniversalReference.Input}

/-- The generated dependency view of the occurrence under the generated reference state.  This is
the view the auxiliary letter is actually read against. -/
def view (context : DomainPhysicalContext input) :
    input.certified.LocalizedDependencyView context.target :=
  input.certified.localizedDependencyView (LocalizedUniversalReference.referenceState input)
    context.target

/-- **The physical frame data derived from the domain.**  Not a field of the context: obtained from
`exists_domainPhysicalFrameData` by `Classical.choice`. -/
def frameData (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    DomainPhysicalFrameData input context.cfg context.target context.center :=
  domainPhysicalFrameData input context.singleBonded context.acyclic context.cfg context.root
    context.domain context.center context.center_ne_root branch.notTwin context.target
    context.targetCurrent

/-- The actual four-ligand frame of the occurrence. -/
def frame (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input) :=
  (context.frameData branch).frame

/-- The declarative derivation of the actual frame. -/
def derived (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    input.certified.DeclarativeLocalizedOccurrenceFourLigandFrame context.target
      (context.frame branch) :=
  (context.frameData branch).derived

/-- The physically written coordinates in derived frame-slot order. -/
def pointsAt (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) : Fin 4 → CartesianPoint3 :=
  (context.frameData branch).pointsAt

/-- The frame is the occurrence's executable frame. -/
theorem frameComputed (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    input.certified.localizedOccurrenceFourLigandFrame? context.target =
      some (context.frame branch) :=
  (context.frameData branch).frameComputed

/-- The frame-slot spatial reads, in `pointsAt` form. -/
theorem spatial (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    ∀ index : Fin 4,
      input.certified.localizedRerootCursorSpatialPoint?
        ((context.frame branch).cursorAt index) =
        some (context.pointsAt branch index) :=
  (context.frameData branch).spatial_pointsAt

/-- The written oriented volume of the frame-slot coordinates is nonzero. -/
theorem nonzero (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    CartesianPoint3.orientedVolume
      (context.pointsAt branch 0) (context.pointsAt branch 1)
        (context.pointsAt branch 2) (context.pointsAt branch 3) ≠ 0 :=
  (context.frameData branch).nonzero_pointsAt

/-- **The original-configuration calibration, retained.**  The sign of the source oriented volume
in the molecule's own detected ligand enumeration is exactly the centre's sign in the original
physical configuration `cfg`. -/
theorem configurationSign_eq (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    rationalVolumeSign
        (CartesianPoint3.orientedVolume
          ((context.frameData branch).pointAt 0) ((context.frameData branch).pointAt 1)
            ((context.frameData branch).pointAt 2) ((context.frameData branch).pointAt 3)) =
      input.certified.detectedMultiCenterMolecule.configurationSign context.cfg
        context.center :=
  (context.frameData branch).signEq

/-- **Normalized physical sense against the original configuration.**  The sign of the written
frame-slot volume equals the centre's original configuration sign scaled by the handedness of the
detected-enumeration slot permutation `alpha`. -/
theorem rationalVolumeSign_pointsAt_eq_configurationSign
    (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    rationalVolumeSign
        (CartesianPoint3.orientedVolume
          (context.pointsAt branch 0) (context.pointsAt branch 1)
            (context.pointsAt branch 2) (context.pointsAt branch 3)) =
      input.certified.detectedMultiCenterMolecule.configurationSign context.cfg
          context.center *
        permHandedness (context.frameData branch).alpha :=
  (context.frameData branch).rationalVolumeSign_pointsAt_eq_configurationSign

/-- **The endpoints do not depend on the derived-data choice.**  Any `DomainPhysicalFrameData` for
the same occurrence has exactly the same written coordinates as the canonical `frameData`. -/
theorem pointsAt_eq_frameData (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context)
    (other : DomainPhysicalFrameData input context.cfg context.target context.center) :
    other.pointsAt = context.pointsAt branch :=
  DomainPhysicalFrameData.pointsAt_eq other (context.frameData branch)

/-- The centre's calibrated physical data: constitutional rigidity, the source coordinates of its
ligand atoms, their nondegenerate volume and the physical configuration sign. -/
theorem calibrated (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    ActualPhysicalGeneralRigidCalibratedCenter input.certified
      input.certified.detectedMultiCenterMolecule context.cfg context.center :=
  calibratedOfDomain_of_notTwin input.certified context.cfg context.root context.domain
    context.center context.center_ne_root branch.notTwin

/-- The centre is constitutionally rigid in the detected enumeration. -/
theorem rigid (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    ConstitutionallyRigid input.certified.detectedMultiCenterMolecule context.center :=
  (context.calibrated branch).1

/-- The centre is constitutionally rigid in the molecule's bond graph. -/
theorem rigidGraph (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    ConstitutionallyRigidGraphAt input.certified.moleculeGraph context.center.1 :=
  constitutionallyRigidGraphAt_of_constitutionallyRigid_detected input.certified context.center
    (context.rigid branch)

/-- The occurrence's current node really is the centre. -/
theorem centerReal (context : DomainPhysicalContext input) :
    input.certified.RealTetrahedralCenterNode context.target.1.node
      ⟨context.center.1, context.center.2⟩ :=
  ⟨carrierOccurrence_provenance_real input.certified context.singleBonded context.acyclic
    context.target, context.targetCurrent⟩

/-- The retained outer root is a tetrahedral centre (needed for the twin classification). -/
theorem rootTetrahedral (context : DomainPhysicalContext input) :
    input.certified.moleculeGraph.IsTetrahedralCenter context.target.1.root := by
  have member : context.root.1 ∈ input.certified.moleculeGraph.tetrahedralCenterSet := by
    simpa [CertifiedLocalizedCIPInput.detectedMultiCenterMolecule,
      MoleculeGraph.detectedMultiCenterMolecule] using context.root.2
  have isT : input.certified.moleculeGraph.IsTetrahedralCenter context.root.1 :=
    (MoleculeGraph.mem_tetrahedralCenterSet input.certified.moleculeGraph context.root.1).1 member
  rwa [context.root_eq] at isT




def priority (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) : Fin 4 → Fin 4 → Prop :=
  fun left right =>
    frameSlotPhysicalOutcome input.certified context.target context.view (context.frame branch)
      (context.derived branch) context.singleBonded context.acyclic context.target.1.root
      left right Ordering.gt





theorem correspondence (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    ConstitutionalPriorityCorrespondence input.certified context.target context.view
      (context.frame branch) (context.derived branch) (context.priority branch) := by
  intro left right _different
  exact (frameSlotPhysicalOutcome_iff_constitutionalCompare input.certified context.target
    context.view (context.frame branch) (context.derived branch) context.singleBonded
    context.acyclic left right Ordering.gt).symm




theorem exists_order (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    ∃ order : List (Fin 4),
      IndependentHighestFirstFor (context.priority branch) order := by
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    simp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel,
      LocalizedReference.Input.molecule]
  exact exists_independentPhysicalHighestFirst input.certified context.target context.view
    (context.frame branch) (context.derived branch) ⟨context.center.1, context.center.2⟩
    context.centerReal (context.rigidGraph branch) context.acyclic context.singleBonded
    context.hcharge enough

/-- **The derived independent highest-first order of the domain occurrence.**  Obtained by
`Classical.choice` from `exists_order`; the `IndependentHighestFirstFor` proof is
`order_independent`. -/
def order (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) : List (Fin 4) :=
  Classical.choose (context.exists_order branch)

/-- The derived order is a permutation of the four physical slots and is strictly descending for
the physical priority. -/
theorem order_independent (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    IndependentHighestFirstFor (context.priority branch) (context.order branch) :=
  Classical.choose_spec (context.exists_order branch)


theorem order_independent_physical (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    IndependentPhysicalHighestFirst input.certified context.target context.view
      (context.frame branch) (context.derived branch) context.singleBonded context.acyclic
      (context.order branch) :=
  context.order_independent branch





theorem order_independent_of_correspondence (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context)
    (priority : Fin 4 → Fin 4 → Prop)
    (correspondence : ConstitutionalPriorityCorrespondence input.certified context.target
      context.view (context.frame branch) (context.derived branch) priority) :
    IndependentHighestFirstFor priority (context.order branch) := by
  have physical := context.order_independent branch
  refine ⟨physical.1, ?_⟩
  refine pairwise_of_nodup_pairwise ?_ physical.2 ?_
  · exact (List.nodup_finRange 4).perm physical.1.symm
  · intro left right different higher
    simp only [DomainPhysicalContext.priority] at higher
    exact (correspondence left right different).mpr
      ((frameSlotPhysicalOutcome_iff_constitutionalCompare input.certified context.target
        context.view (context.frame branch) (context.derived branch) context.singleBonded
        context.acyclic left right Ordering.gt).mpr higher)

/-- **A chiral letter is actually produced at every rigid context.**  The generated reader returns
`some (.chiral …)` for the derived frame with the derived written parity; this is an existence
statement about the executable reader, not a consequence of the descriptor equivalence. -/
theorem exists_chiral (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    ∃ rs : RS,
      LocalizedUniversalReference.referenceState input context.target = some (.chiral rs) := by
  let pointsAt : Fin 4 → CartesianPoint3 := context.pointsAt branch
  let volume : ℚ :=
    CartesianPoint3.orientedVolume (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3)
  let parity : TetrahedralInputParity := parityOfVolumeSign (rationalVolumeSign volume)
  have writtenParity : AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3] parity :=
    rationalTetrahedralInputParity_parityOfVolumeSign
      (pointsAt 0) (pointsAt 1) (pointsAt 2) (pointsAt 3) (context.nonzero branch)
  obtain ⟨_tracked, _computed, _pseudo, state⟩ :=
    referenceState_reader_eq_chiral_of_detectedRigid_derived (input := input)
      (noDouble := context.noDouble) (target := context.target)
      (frame := context.frame branch) (derived := context.derived branch)
      (center := ⟨context.center.1, context.center.2⟩) (centerReal := context.centerReal)
      (rigid := context.rigid branch) (hacyc := context.acyclic)
      (hsimple := context.singleBonded) (hcharge := context.hcharge)
      (pointsAt := pointsAt) (spatial := context.spatial branch) (parity := parity)
      (writtenParity := writtenParity)
  exact ⟨_, state⟩

end DomainPhysicalContext

/-! ## D. The final endpoints: reader letter against the derived physical descriptor -/




















theorem referenceState_eq_chiral_iff_domainPhysicalDescriptor
    (input : LocalizedUniversalReference.Input)
    (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context)
    (rs : RS) :
    LocalizedUniversalReference.referenceState input context.target = some (.chiral rs) ↔
      CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        ((context.order branch).map (context.pointsAt branch)) rs :=
  referenceState_eq_chiral_iff_priorityDescriptor input context.singleBonded context.acyclic
    context.hcharge context.noDouble context.target (context.frame branch)
    (context.derived branch) ⟨context.center.1, context.center.2⟩ context.centerReal
    (context.rigid branch) (context.priority branch) (context.correspondence branch)
    (context.pointsAt branch) (context.spatial branch) (context.nonzero branch)
    (context.order branch) (context.order_independent branch) rs

/-- **MAIN ENDPOINT, twin counterpart.**  At a physical terminal twin the generated reference
state reads `none`, so the chiral calibration never manufactures a letter for a twin.  Same domain
context, same retained outer root. -/
theorem referenceState_eq_none_of_domainPhysicalTwin
    (input : LocalizedUniversalReference.Input)
    (context : DomainPhysicalContext input)
    (twin : ActualPhysicalTerminalTwinCenter input.certified
      input.certified.detectedMultiCenterMolecule context.center) :
    LocalizedUniversalReference.referenceState input context.target = none :=
  referenceState_eq_none_of_independentPhysicalTwin input context.singleBonded context.acyclic
    context.noDouble context.center context.target context.targetCurrent context.rootTetrahedral
    twin

/-- **EXISTENCE ENDPOINT — a chiral letter exists at every rigid context, with its same-data
original-configuration sense.**

At every rigid context the executable reader returns an uppercase `R/S` letter for the derived
coordinates, that letter is the rational tetrahedral descriptor of the independently
highest-priority-ordered derived coordinates, and the written frame-slot volume sign is the
centre's **original** configuration sign scaled by the handedness of the detected-enumeration slot
permutation `alpha`.  The three facts are about the same data object; nothing is re-chosen. -/
theorem exists_domainPhysicalChiralLetter
    (input : LocalizedUniversalReference.Input)
    (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    ∃ rs : RS,
      LocalizedUniversalReference.referenceState input context.target = some (.chiral rs) ∧
        CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
          ((context.order branch).map (context.pointsAt branch)) rs ∧
        rationalVolumeSign
          (CartesianPoint3.orientedVolume
            (context.pointsAt branch 0) (context.pointsAt branch 1)
              (context.pointsAt branch 2) (context.pointsAt branch 3)) =
          input.certified.detectedMultiCenterMolecule.configurationSign context.cfg
              context.center *
            permHandedness (context.frameData branch).alpha := by
  obtain ⟨rs, state⟩ := context.exists_chiral branch
  exact ⟨rs, state,
    (referenceState_eq_chiral_iff_domainPhysicalDescriptor input context branch rs).mp state,
    context.rationalVolumeSign_pointsAt_eq_configurationSign branch⟩

/-- **The complete domain classification at one actual occurrence.**  Twin centres read `none`;
non-twin (rigid) centres read `some (.chiral rs)` exactly for the descriptor letter of the
independent physical order. -/
theorem referenceState_classification
    (input : LocalizedUniversalReference.Input)
    (context : DomainPhysicalContext input) :
    (ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule context.center →
      LocalizedUniversalReference.referenceState input context.target = none) ∧
    (∀ (notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified
        input.certified.detectedMultiCenterMolecule context.center),
      ∀ rs : RS,
        LocalizedUniversalReference.referenceState input context.target = some (.chiral rs) ↔
          CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
            ((context.order ⟨notTwin⟩).map (context.pointsAt ⟨notTwin⟩)) rs) :=
  ⟨fun twin => referenceState_eq_none_of_domainPhysicalTwin input context twin,
   fun notTwin rs =>
    referenceState_eq_chiral_iff_domainPhysicalDescriptor input context ⟨notTwin⟩ rs⟩

/-- **Independence of the derived order.**  Any independently highest-first order of the derived
frame gives the same reader/descriptor equivalence; the endpoint does not depend on which
admissible order is chosen.  (`DomainPhysicalContext.order` is one such order.) -/
theorem referenceState_eq_chiral_iff_domainIndependentOrder
    (input : LocalizedUniversalReference.Input)
    (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context)
    (order : List (Fin 4))
    (independent : IndependentPhysicalHighestFirst input.certified context.target context.view
      (context.frame branch) (context.derived branch) context.singleBonded context.acyclic
      order)
    (rs : RS) :
    LocalizedUniversalReference.referenceState input context.target = some (.chiral rs) ↔
      CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        (order.map (context.pointsAt branch)) rs :=
  referenceState_eq_chiral_iff_physicalDescriptor input context.singleBonded context.acyclic
    context.hcharge context.noDouble context.target (context.frame branch)
    (context.derived branch) ⟨context.center.1, context.center.2⟩ context.centerReal
    (context.rigid branch) (context.pointsAt branch) (context.spatial branch)
    (context.nonzero branch) order independent rs

/-- **The domain-level descriptor letter is unique.**  At a fixed occurrence there is at most one
`R/S` letter satisfying the descriptor of the physically ordered coordinates, so the equivalence
above determines the letter. -/
theorem domainPhysicalDescriptor_unique
    (input : LocalizedUniversalReference.Input)
    (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context)
    {first second : RS}
    (left : CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
      ((context.order branch).map (context.pointsAt branch)) first)
    (right : CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
      ((context.order branch).map (context.pointsAt branch)) second) :
    first = second :=
  rationalTetrahedralDescriptor_unique left right








theorem referenceState_eq_chiral_iff_domainPriorityDescriptor
    (input : LocalizedUniversalReference.Input)
    (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context)
    (priority : Fin 4 → Fin 4 → Prop)
    (correspondence : ConstitutionalPriorityCorrespondence input.certified context.target
      context.view (context.frame branch) (context.derived branch) priority)
    (rs : RS) :
    LocalizedUniversalReference.referenceState input context.target = some (.chiral rs) ↔
      CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        ((context.order branch).map (context.pointsAt branch)) rs :=
  referenceState_eq_chiral_iff_priorityDescriptor input context.singleBonded context.acyclic
    context.hcharge context.noDouble context.target (context.frame branch)
    (context.derived branch) ⟨context.center.1, context.center.2⟩ context.centerReal
    (context.rigid branch) priority correspondence (context.pointsAt branch)
    (context.spatial branch) (context.nonzero branch) (context.order branch)
    (context.order_independent_of_correspondence branch priority correspondence) rs












theorem referenceState_eq_chiral_iff_domainCanonicalPriorityDescriptor
    (input : LocalizedUniversalReference.Input)
    (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context)
    (priority : Fin 4 → Fin 4 → Prop)
    (correspondence : ConstitutionalPriorityCorrespondence input.certified context.target
      context.view (context.frame branch) (context.derived branch) priority)
    (order : List (Fin 4))
    (independent : IndependentHighestFirstFor priority order)
    (rs : RS) :
    LocalizedUniversalReference.referenceState input context.target = some (.chiral rs) ↔
      CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
        (order.map (context.pointsAt branch)) rs :=
  referenceState_eq_chiral_iff_priorityDescriptor input context.singleBonded context.acyclic
    context.hcharge context.noDouble context.target (context.frame branch)
    (context.derived branch) ⟨context.center.1, context.center.2⟩ context.centerReal
    (context.rigid branch) priority correspondence (context.pointsAt branch)
    (context.spatial branch) (context.nonzero branch) order independent rs

assert_kernel_only TetraStereo.OneCenter.DomainPhysicalFrameData
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalFrameData.pointsAt
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalFrameData.spatial_pointsAt
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalFrameData.nonzero_pointsAt
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalFrameData.orientedVolume_pointsAt_eq
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalFrameData.rationalVolumeSign_pointsAt_eq
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalFrameData.rationalVolumeSign_pointsAt_eq_configurationSign
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalFrameData.frame_eq
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalFrameData.alpha_eq
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalFrameData.pointAt_eq
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalFrameData.pointsAt_eq
assert_kernel_only TetraStereo.OneCenter.calibratedOfDomain_of_notTwin
assert_kernel_only TetraStereo.OneCenter.exists_domainPhysicalFrameData
assert_kernel_only TetraStereo.OneCenter.domainPhysicalFrameData
assert_kernel_only TetraStereo.OneCenter.domainPhysicalFrameData_frameComputed
assert_kernel_only TetraStereo.OneCenter.constitutionallyRigid_of_domainPhysicalFrameData
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalRigidBranch
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.view
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.frameData
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.frame
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.derived
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.pointsAt
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.frameComputed
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.spatial
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.nonzero
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.configurationSign_eq
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.rationalVolumeSign_pointsAt_eq_configurationSign
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.pointsAt_eq_frameData
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.calibrated
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.rigid
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.rigidGraph
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.centerReal
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.rootTetrahedral
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.priority
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.correspondence
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.exists_order
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.order
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.order_independent
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.order_independent_physical
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.order_independent_of_correspondence
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.exists_chiral
assert_kernel_only TetraStereo.OneCenter.referenceState_eq_chiral_iff_domainPhysicalDescriptor
assert_kernel_only TetraStereo.OneCenter.exists_domainPhysicalChiralLetter
assert_kernel_only TetraStereo.OneCenter.referenceState_eq_none_of_domainPhysicalTwin
assert_kernel_only TetraStereo.OneCenter.referenceState_classification
assert_kernel_only TetraStereo.OneCenter.referenceState_eq_chiral_iff_domainIndependentOrder
assert_kernel_only TetraStereo.OneCenter.domainPhysicalDescriptor_unique
assert_kernel_only TetraStereo.OneCenter.referenceState_eq_chiral_iff_domainPriorityDescriptor
assert_kernel_only TetraStereo.OneCenter.referenceState_eq_chiral_iff_domainCanonicalPriorityDescriptor

end TetraStereo.OneCenter
