/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TetraStereo.OneCenter.LocalizedPhysicalRelativeRule4bObservations
import TetraStereo.OneCenter.LocalizedIndependentAuxiliaryRSClosure
import TetraStereo.OneCenter.LocalizedPhysicalRule5PrefixClosure
import TetraStereo.OneCenter.LocalizedActualNearestStagePrefixCovariance
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










































/-! ## A. Exact-input occurrence retention -/

/-- **The actual four generated letters at exactly the supplied reader steps.**  The structure is
indexed by `stepReference` and `stepObserved`, so the reader equations below are equations at the
caller's own occurrences; no existential re-selection of a pair is possible. -/
structure SuppliedPhysicalReaderPair (input : LocalizedUniversalReference.Input)
    (context : PhysicalAutomorphismContext input)
    (dReference dObserved : input.certified.detectedMultiCenterMolecule.Center)
    (stepReference : PhysicalReaderStep input context dReference)
    (stepObserved : PhysicalReaderStep input context dObserved) where
  /-- The actual uppercase letter at `stepReference.t`. -/
  referenceLetter : RS
  /-- The actual uppercase letter at `stepReference.u`. -/
  imageReferenceLetter : RS
  /-- The actual uppercase letter at `stepObserved.t`. -/
  observedLetter : RS
  /-- The actual uppercase letter at `stepObserved.u`. -/
  imageObservedLetter : RS
  /-- The actual reader state at the supplied reference occurrence. -/
  referenceStateEq : LocalizedUniversalReference.referenceState input stepReference.t =
    some (.chiral referenceLetter)
  /-- The actual reader state at the supplied image reference occurrence. -/
  imageReferenceStateEq : LocalizedUniversalReference.referenceState input stepReference.u =
    some (.chiral imageReferenceLetter)
  /-- The actual reader state at the supplied observed occurrence. -/
  observedStateEq : LocalizedUniversalReference.referenceState input stepObserved.t =
    some (.chiral observedLetter)
  /-- The actual reader state at the supplied image observed occurrence. -/
  imageObservedStateEq : LocalizedUniversalReference.referenceState input stepObserved.u =
    some (.chiral imageObservedLetter)





theorem exists_suppliedPhysicalReaderPair
    {input : LocalizedUniversalReference.Input}
    {context : PhysicalAutomorphismContext input}
    {dReference dObserved : input.certified.detectedMultiCenterMolecule.Center}
    (stepReference : PhysicalReaderStep input context dReference)
    (stepObserved : PhysicalReaderStep input context dObserved) :
    Nonempty (SuppliedPhysicalReaderPair input context dReference dObserved stepReference
      stepObserved) := by
  obtain ⟨referenceLetter, referenceStateEq⟩ := stepReference.exists_t_letter
  obtain ⟨imageReferenceLetter, imageReferenceStateEq⟩ := stepReference.exists_u_letter
  obtain ⟨observedLetter, observedStateEq⟩ := stepObserved.exists_t_letter
  obtain ⟨imageObservedLetter, imageObservedStateEq⟩ := stepObserved.exists_u_letter
  exact ⟨{ referenceLetter := referenceLetter
           imageReferenceLetter := imageReferenceLetter
           observedLetter := observedLetter
           imageObservedLetter := imageObservedLetter
           referenceStateEq := referenceStateEq
           imageReferenceStateEq := imageReferenceStateEq
           observedStateEq := observedStateEq
           imageObservedStateEq := imageObservedStateEq }⟩

namespace SuppliedPhysicalReaderPair

variable {input : LocalizedUniversalReference.Input}
variable {context : PhysicalAutomorphismContext input}
variable {dReference dObserved : input.certified.detectedMultiCenterMolecule.Center}
variable {stepReference : PhysicalReaderStep input context dReference}
variable {stepObserved : PhysicalReaderStep input context dObserved}



def toActualPair (pair : SuppliedPhysicalReaderPair input context dReference dObserved
    stepReference stepObserved) :
    ActualPhysicalReaderPair input context dReference dObserved where
  stepReference := stepReference
  stepObserved := stepObserved
  referenceLetter := pair.referenceLetter
  imageReferenceLetter := pair.imageReferenceLetter
  observedLetter := pair.observedLetter
  imageObservedLetter := pair.imageObservedLetter
  referenceStateEq := pair.referenceStateEq
  imageReferenceStateEq := pair.imageReferenceStateEq
  observedStateEq := pair.observedStateEq
  imageObservedStateEq := pair.imageObservedStateEq

/-- The actual pair uses exactly the supplied reference step. -/
theorem toActualPair_stepReference (pair : SuppliedPhysicalReaderPair input context dReference
    dObserved stepReference stepObserved) :
    pair.toActualPair.stepReference = stepReference := rfl

/-- The actual pair uses exactly the supplied observed step. -/
theorem toActualPair_stepObserved (pair : SuppliedPhysicalReaderPair input context dReference
    dObserved stepReference stepObserved) :
    pair.toActualPair.stepObserved = stepObserved := rfl

/-- **Contrast at the supplied occurrences.**  The source observations at the supplied image pair
and at the supplied original pair are equal exactly when the two physical discrepancies agree.  The
equations of the four letters are equations at `stepReference.t/u` and `stepObserved.t/u`. -/
theorem sourceObservation_contrast
    (pair : SuppliedPhysicalReaderPair input context dReference dObserved stepReference
      stepObserved) :
    sourceObserveRule4bLabel pair.imageReferenceLetter (some (.chiral pair.imageObservedLetter)) =
      sourceObserveRule4bLabel pair.referenceLetter (some (.chiral pair.observedLetter)) ↔
      localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
          dReference =
        localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
          dObserved :=
  stepReference.sourceObservation_contrast stepObserved pair.referenceLetter
    pair.imageReferenceLetter pair.observedLetter pair.imageObservedLetter
    pair.referenceStateEq pair.imageReferenceStateEq pair.observedStateEq
    pair.imageObservedStateEq

/-- **Complement form at the supplied occurrences.** -/
theorem sourceObservation_differ
    (pair : SuppliedPhysicalReaderPair input context dReference dObserved stepReference
      stepObserved) :
    sourceObserveRule4bLabel pair.imageReferenceLetter (some (.chiral pair.imageObservedLetter)) ≠
      sourceObserveRule4bLabel pair.referenceLetter (some (.chiral pair.observedLetter)) ↔
      localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
          dReference ≠
        localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
          dObserved :=
  stepReference.sourceObservation_differ stepObserved pair.referenceLetter
    pair.imageReferenceLetter pair.observedLetter pair.imageObservedLetter
    pair.referenceStateEq pair.imageReferenceStateEq pair.observedStateEq
    pair.imageObservedStateEq

end SuppliedPhysicalReaderPair






theorem exists_actualPhysicalReaderPair_supplied
    {input : LocalizedUniversalReference.Input}
    {context : PhysicalAutomorphismContext input}
    {dReference dObserved : input.certified.detectedMultiCenterMolecule.Center}
    (stepReference : PhysicalReaderStep input context dReference)
    (stepObserved : PhysicalReaderStep input context dObserved) :
    ∃ pair : ActualPhysicalReaderPair input context dReference dObserved,
      pair.stepReference = stepReference ∧
        pair.stepObserved = stepObserved ∧
          (sourceObserveRule4bLabel pair.imageReferenceLetter
              (some (.chiral pair.imageObservedLetter)) =
            sourceObserveRule4bLabel pair.referenceLetter (some (.chiral pair.observedLetter)) ↔
            localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
                dReference =
              localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
                dObserved) ∧
          (sourceObserveRule4bLabel pair.imageReferenceLetter
              (some (.chiral pair.imageObservedLetter)) ≠
            sourceObserveRule4bLabel pair.referenceLetter (some (.chiral pair.observedLetter)) ↔
            localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
                dReference ≠
              localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
                dObserved) := by
  obtain ⟨pair⟩ := exists_suppliedPhysicalReaderPair stepReference stepObserved
  refine ⟨pair.toActualPair, rfl, rfl, pair.sourceObservation_contrast,
    pair.sourceObservation_differ⟩

/-- **Strongest exact-input contrast export.**  A pair indexed by the supplied steps together with
its contrast and difference laws; the letters and reader equations are fields at the supplied
occurrences. -/
theorem exists_suppliedSourceObservation_contrast
    {input : LocalizedUniversalReference.Input}
    {context : PhysicalAutomorphismContext input}
    {dReference dObserved : input.certified.detectedMultiCenterMolecule.Center}
    (stepReference : PhysicalReaderStep input context dReference)
    (stepObserved : PhysicalReaderStep input context dObserved) :
    ∃ pair : SuppliedPhysicalReaderPair input context dReference dObserved stepReference
        stepObserved,
      (sourceObserveRule4bLabel pair.imageReferenceLetter
          (some (.chiral pair.imageObservedLetter)) =
        sourceObserveRule4bLabel pair.referenceLetter (some (.chiral pair.observedLetter)) ↔
        localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
            dReference =
          localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
            dObserved) ∧
      (sourceObserveRule4bLabel pair.imageReferenceLetter
          (some (.chiral pair.imageObservedLetter)) ≠
        sourceObserveRule4bLabel pair.referenceLetter (some (.chiral pair.observedLetter)) ↔
        localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
            dReference ≠
          localDiscrepancy input.certified.detectedMultiCenterMolecule context.cfg context.e
            dObserved) := by
  obtain ⟨pair⟩ := exists_suppliedPhysicalReaderPair stepReference stepObserved
  exact ⟨pair, pair.sourceObservation_contrast, pair.sourceObservation_differ⟩



namespace DomainPhysicalFrameData

variable {input : LocalizedUniversalReference.Input}
variable {cfg : input.certified.detectedMultiCenterMolecule.Configuration}
variable {target : LocalizedUniversalReference.Occurrence input}
variable {center : input.certified.detectedMultiCenterMolecule.Center}

/-- **The frame calibration derived from the original domain data.**  The physical coordinates are
the data's own detected-enumeration coordinates `pointAt`; the written frame-slot coordinates are
`pointsAt = pointAt ∘ alpha` by definition, the physical sign is the retained original-configuration
`signEq`, and nondegeneracy of the detected-enumeration volume is transported back through `alpha`
from the written nonzero volume.  No coordinate, permutation or sign is re-chosen. -/
def calibration (data : DomainPhysicalFrameData input cfg target center) :
    PhysicalFrameCalibration input.certified.detectedMultiCenterMolecule cfg center data.alpha
      data.pointsAt where
  physicalPointAt := data.pointAt
  calibrated := fun _ => rfl
  nondegenerate := by
    have permuted := cartesianOrientedVolume_perm_ne_zero
      (fun index => data.pointAt (data.alpha index)) data.alpha.symm data.nonzero
    simpa using permuted
  sign_eq := data.signEq

end DomainPhysicalFrameData

namespace DomainPhysicalContext

variable {input : LocalizedUniversalReference.Input}






def orderData (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    PhysicalRule4bOrderData input input.certified.detectedMultiCenterMolecule context.cfg
      context.target context.center ⟨context.center.1, context.center.2⟩ context.centerReal where
  singleBonded := context.singleBonded
  acyclic := context.acyclic
  charge := context.hcharge
  frame := context.frame branch
  derived := context.derived branch
  frameComputed := context.frameComputed branch
  priority := context.priority branch
  rigid := context.rigid branch
  correspondence := context.correspondence branch
  pointsAt := context.pointsAt branch
  spatial := context.spatial branch
  nonzero := context.nonzero branch
  alpha := (context.frameData branch).alpha
  calibration := (context.frameData branch).calibration
  order := context.order branch
  independent := context.order_independent branch

/-- **The normalized physical sense of the domain occurrence.**  The original configuration sign at
the centre times the parity of the independently highest-first ordered detected ligands
(`order ∘ alpha`, where `alpha` is the actual frame's detected-enumeration slot permutation). -/
def normalizedSense (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) : ℝ :=
  physicalNormalizedSense input.certified.detectedMultiCenterMolecule context.cfg context.center
    ((context.order branch).map (context.frameData branch).alpha)

/-- Every normalized sense of the domain occurrence is `+1` or `-1`. -/
theorem normalizedSense_eq_one_or_neg_one (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    context.normalizedSense branch = 1 ∨ context.normalizedSense branch = -1 :=
  physicalNormalizedSense_eq_one_or_neg_one input.certified.detectedMultiCenterMolecule
    context.cfg context.center ((context.order branch).map (context.frameData branch).alpha)






theorem referenceState_eq_chiral_ofHandedness (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    LocalizedUniversalReference.referenceState input context.target =
      some (.chiral (RS.ofHandedness (context.normalizedSense branch))) :=
  (context.orderData branch).referenceState_eq_chiral context.noDouble

/-- **The reader letter is exactly the normalized sense.**  The forward direction uses uniqueness of
the actual reader letter; the converse substitutes the produced equation.  No desired letter is
assumed and no second calibration is introduced. -/
theorem referenceState_eq_chiral_iff_ofHandedness (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) (rs : RS) :
    LocalizedUniversalReference.referenceState input context.target = some (.chiral rs) ↔
      rs = RS.ofHandedness (context.normalizedSense branch) := by
  constructor
  · intro stateEq
    have produced := context.referenceState_eq_chiral_ofHandedness branch
    have labelsEq : LocalizedTetrahedralRSPseudoDescriptor.chiral rs =
        LocalizedTetrahedralRSPseudoDescriptor.chiral
          (RS.ofHandedness (context.normalizedSense branch)) :=
      Option.some.inj (stateEq.symm.trans produced)
    exact LocalizedTetrahedralRSPseudoDescriptor.chiral.inj labelsEq
  · intro letterEq
    rw [letterEq]
    exact context.referenceState_eq_chiral_ofHandedness branch






theorem sourceObserve_ofHandedness_eq_pairClass (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) {referenceSense : ℝ}
    (referenceCases : referenceSense = 1 ∨ referenceSense = -1) :
    sourceObserveRule4bLabel (RS.ofHandedness referenceSense)
        (LocalizedUniversalReference.referenceState input context.target) =
      .withRule4b .chiral
        (some (physicalPairClass referenceSense (context.normalizedSense branch))) ∧
      (physicalPairClass referenceSense (context.normalizedSense branch) = .like ↔
        referenceSense * context.normalizedSense branch = 1) := by
  rw [context.referenceState_eq_chiral_ofHandedness branch]
  exact ⟨sourceObserveRule4bLabel_ofHandedness_pairClass referenceCases
      (context.normalizedSense_eq_one_or_neg_one branch),
    physicalPairClass_eq_like_iff⟩

/-- **The reference-relative source observation of the context's own physical letter.**  This is
the same pair-class law with the arbitrary reference sense *removed*: the reference is the actual
reader letter of this very context, so the two senses are the context's own normalized sense and
the source observation is `like` exactly at `ν * ν = 1`. -/
theorem sourceObserve_referenceState_eq_pairClass (context : DomainPhysicalContext input)
    (branch : DomainPhysicalRigidBranch context) :
    sourceObserveRule4bLabel (RS.ofHandedness (context.normalizedSense branch))
        (LocalizedUniversalReference.referenceState input context.target) =
      .withRule4b .chiral
        (some (physicalPairClass (context.normalizedSense branch)
          (context.normalizedSense branch))) ∧
      (physicalPairClass (context.normalizedSense branch)
          (context.normalizedSense branch) = .like ↔
        context.normalizedSense branch * context.normalizedSense branch = 1) :=
  context.sourceObserve_ofHandedness_eq_pairClass branch
    (context.normalizedSense_eq_one_or_neg_one branch)






theorem referenceState_eq_chiral_iff_canonicalDescriptor
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
  referenceState_eq_chiral_iff_domainCanonicalPriorityDescriptor input context branch priority
    correspondence order independent rs

end DomainPhysicalContext













/-- The actual certified data of one frame slot of the detected final occurrence: the detected
degree-four centre, the actually computed four-ligand frame and slot, the certified simple-bonded
acyclic constant-charge no-double-bond facts, the **original** physical configuration, the physical
general-rigid/terminal-twin domain at the slot centre, and the attachment atom actually observed by
the slot cursor.  The fields `frameComputed` and `oObserved` are success equations of the executable
frame, not scientific inputs: this structure is the setup-relative interface, while
`ActualSlotPhysicalSetupOf`/`exists_actualSlotPhysicalSetupOf` derive both from the physical input
and an actually bonded attachment atom alone.  No letter, order or selection is ever supplied. -/
structure ActualSlotPhysicalSetup (input : LocalizedUniversalReference.Input) where
  /-- The detected degree-four final centre. -/
  c : input.certified.detectedMultiCenterMolecule.Center
  /-- The actually computed four-ligand frame of the final occurrence. -/
  frame : input.certified.LocalizedOccurrenceFourLigandFrame
    (LocalizedUniversalReference.carrierFuel input)
  /-- The frame really is the executable frame of the final occurrence. -/
  frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
    (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame
  /-- The chosen frame slot. -/
  slot : Fin 4
  /-- The certified bond graph is simple-bonded. -/
  singleBonded : input.certified.moleculeGraph.SimpleBonded
  /-- The certified bond graph is acyclic. -/
  acyclic : input.certified.moleculeGraph.Acyclic
  /-- Every atom carries the same formal charge. -/
  hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph
  /-- The molecule has no localized double-bond records. -/
  noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords
  /-- The **original** physical configuration enumeration. -/
  cfg : input.certified.detectedMultiCenterMolecule.Configuration
  /-- The physical general-rigid/terminal-twin domain in the original configuration. -/
  physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
    input.certified.detectedMultiCenterMolecule cfg c
  /-- The attachment atom actually observed by the slot cursor. -/
  oAtom : input.certified.Atom
  /-- The slot cursor observes the attachment atom. -/
  oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom

namespace ActualSlotPhysicalSetup

variable {input : LocalizedUniversalReference.Input}

/-- The actual decorated Rule-4a tree of the slot. -/
def tree (setup : ActualSlotPhysicalSetup input) :
    LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input) :=
  actualSlotTree input setup.c setup.frame setup.frameComputed setup.slot

/-- The actual production compound Rules-4a--5 key of the slot. -/
def key (setup : ActualSlotPhysicalSetup input) :
    input.certified.LocalizedRerootCompoundRule45Key :=
  actualSlotCompoundKey input setup.c setup.frame setup.frameComputed setup.slot

/-- The retained outer root: the detected centre of the slot. -/
def root (setup : ActualSlotPhysicalSetup input) :
    input.certified.detectedMultiCenterMolecule.Center :=
  setup.c

/-- The incoming physical bond from the final root to the slot's attachment atom, derived from the
actual carrier neighbour classification of the frame cursor. -/
def incomingEdge (setup : ActualSlotPhysicalSetup input) :
    input.certified.moleculeGraph.Adj setup.c.1 setup.oAtom :=
  actualSlot_incomingEdge input setup.c setup.frame setup.frameComputed setup.slot setup.oObserved




def globalDomain (setup : ActualSlotPhysicalSetup input) :
    ActualGeneralRigidGlobalPhysicalDomain input.certified
      (input.certified.canonicalReindexConfiguration setup.cfg) setup.root :=
  actualGeneralRigidGlobalPhysicalDomain_of_actualGeneralRigidPhysicalDomain
    input.certified setup.cfg setup.c setup.physicalDomain

theorem tree_source (setup : ActualSlotPhysicalSetup input) :
    setup.tree.source = setup.frame.cursorAt setup.slot :=
  actualSlotTree_source input setup.c setup.frame setup.frameComputed setup.slot

theorem tree_labelTable (setup : ActualSlotPhysicalSetup input) :
    setup.tree.labelTable = setup.key.prior.rule4aKey.labels :=
  actualSlotTree_labelTable input setup.c setup.frame setup.frameComputed setup.slot

theorem tree_realizes (setup : ActualSlotPhysicalSetup input) :
    LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) setup.tree :=
  actualSlotTree_realizes input setup.c setup.frame setup.frameComputed setup.slot

theorem tree_previousEq (setup : ActualSlotPhysicalSetup input) :
    setup.tree.source.previous? = some (ActualReaderPhysicalBranchInverse.topTarget input setup.c) :=
  actualSlotTree_previousEq input setup.c setup.frame setup.frameComputed setup.slot

theorem tree_valid (setup : ActualSlotPhysicalSetup input) :
    input.certified.LocalizedRerootCursorValid setup.tree.source :=
  actualSlotTree_valid input setup.c setup.frame setup.frameComputed setup.slot

theorem tree_sameRoot (setup : ActualSlotPhysicalSetup input) :
    setup.tree.source.occurrence.1.root =
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c).1.root :=
  actualSlotTree_sameRoot input setup.c setup.frame setup.frameComputed setup.slot

theorem tree_oObserved (setup : ActualSlotPhysicalSetup input) :
    setup.tree.source.occurrence.1.node.current? = some setup.oAtom :=
  actualSlotTree_oObserved input setup.c setup.frame setup.frameComputed setup.slot setup.oObserved

theorem tree_previousShorter (setup : ActualSlotPhysicalSetup input) :
    (ActualReaderPhysicalBranchInverse.topTarget input setup.c).1.address.length <
      setup.tree.source.occurrence.1.address.length :=
  actualSlotTree_previousShorter input setup.c setup.frame setup.frameComputed setup.slot

/-- The actual production compound key build at the slot cursor. -/
theorem compoundBuilt (setup : ActualSlotPhysicalSetup input) :
    input.certified.buildLocalizedRerootCompoundRule45Key?
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
        (referenceDependencyView input setup.c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (setup.frame.cursorAt setup.slot) = some setup.key :=
  actualSlotCompoundBuilt input setup.c setup.frame setup.frameComputed setup.slot

/-- The actual production Rules-4b/4c prior build at the slot cursor. -/
theorem priorBuilt (setup : ActualSlotPhysicalSetup input) :
    input.certified.buildLocalizedRerootCompoundRule4bcKey?
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
        (referenceDependencyView input setup.c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (setup.frame.cursorAt setup.slot) = some setup.key.prior :=
  actualSlotPriorBuilt input setup.c setup.frame setup.frameComputed setup.slot

/-- The actual production Rule-4a cumulative build at the slot cursor. -/
theorem rule4aBuilt (setup : ActualSlotPhysicalSetup input) :
    input.certified.buildLocalizedRerootCumulativeRule45Key?
        .rule4a
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
        (referenceDependencyView input setup.c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (setup.frame.cursorAt setup.slot) = some setup.key.prior.rule4aKey :=
  actualSlotRule4aBuilt input setup.c setup.frame setup.frameComputed setup.slot

/-- The actual occurrence root of every position is the final root. -/
theorem position_source_root_eq (setup : ActualSlotPhysicalSetup input)
    (p : Position setup.tree) :
    (positionSource p).occurrence.1.root = setup.c.1 := by
  rw [positionSource_root_eq_of_realized (input := input.certified)
      (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      (read := ActualReaderPhysicalBranchInverse.dependencyReader input setup.c)
      setup.tree_realizes p,
    setup.tree_sameRoot, ActualReaderPhysicalBranchInverse.topTarget_root]

/-- The actual node label at every position is the actual whole reader state at that position. -/
theorem tree_positionNode_label_eq_state (setup : ActualSlotPhysicalSetup input)
    (p : Position setup.tree) :
    (positionNode p).label =
      LocalizedUniversalReference.referenceState input (positionSource p).occurrence :=
  actualSlotTree_positionNode_label_eq_state input setup.c setup.frame setup.frameComputed
    setup.slot p




theorem tree_positionNode_label_eq_state_of_actualStage (setup : ActualSlotPhysicalSetup input)
    (p : Position setup.tree) :
    (positionNode p).label =
      LocalizedUniversalReference.referenceState input (positionSource p).occurrence :=
  LocalizedActualNearestStagePrefixCovariance.position_label_eq_referenceState_of_actualStage
    input setup.c setup.frame setup.frameComputed setup.slot (oAtom := setup.oAtom)
    setup.oObserved setup.tree_source setup.tree_realizes p

/-- The physical mark of an actual position: a non-root detected degree-four candidate that is not
a physical terminal twin. -/
def PositionMarked (setup : ActualSlotPhysicalSetup input)
    (p : Position setup.tree) : Prop :=
  PhysicalMarkedAtom input setup.root
    (positionAtom setup.singleBonded setup.acyclic p)

/-- Every position atom lies in the physical cut branch of the slot attachment. -/
theorem position_atom_mem_cutBranch (setup : ActualSlotPhysicalSetup input)
    (p : Position setup.tree) :
    positionAtom setup.singleBonded setup.acyclic p ∈
      AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph setup.c.1
        setup.oAtom :=
  positionAtom_mem_cutBranch (input := input.certified)
    (carrierFuel := LocalizedUniversalReference.carrierFuel input)
    (read := ActualReaderPhysicalBranchInverse.dependencyReader input setup.c)
    setup.singleBonded setup.acyclic (globalCarrierFuel_adequate input)
    setup.tree_realizes
    (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
    setup.tree_previousEq setup.tree_valid
    setup.tree_oObserved
    (ActualReaderPhysicalBranchInverse.topTarget_current input setup.c)
    setup.incomingEdge p

/-- The detected centre of a marked position. -/
def positionCenter (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (marked : setup.PositionMarked p) :
    input.certified.detectedMultiCenterMolecule.Center :=
  ⟨positionAtom setup.singleBonded setup.acyclic p, marked.2.1⟩

/-- A marked position is not the retained outer root. -/
theorem positionCenter_ne_root (setup : ActualSlotPhysicalSetup input)
    (p : Position setup.tree) (marked : setup.PositionMarked p) :
    setup.positionCenter p marked ≠ setup.root := by
  intro same
  exact AcyclicCutBranchAutomorphism.cutBranch_ne_center input.certified.moleculeGraph
    (setup.position_atom_mem_cutBranch p) (congrArg Subtype.val same)




def positionContext (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (marked : setup.PositionMarked p) : DomainPhysicalContext input where
  singleBonded := setup.singleBonded
  acyclic := setup.acyclic
  hcharge := setup.hcharge
  noDouble := setup.noDouble
  cfg := setup.cfg
  root := setup.root
  domain := setup.physicalDomain
  center := setup.positionCenter p marked
  center_ne_root := setup.positionCenter_ne_root p marked
  target := (positionSource p).occurrence
  targetCurrent := positionAtom_spec setup.singleBonded setup.acyclic p
  root_eq := (setup.position_source_root_eq p).symm

/-- The rigid branch at a marked position: the mark supplies the non-twin fact. -/
def positionBranch (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (marked : setup.PositionMarked p) :
    DomainPhysicalRigidBranch (setup.positionContext p marked) where
  notTwin := marked.2.2

/-- **The normalized physical sense of an actual position.**  The original configuration sign at
the position's centre times the parity of the independently highest-first ordered detected ligands
of the position's own actual frame. -/
def positionSense (setup : ActualSlotPhysicalSetup input) (p : Position setup.tree)
    (marked : setup.PositionMarked p) : ℝ :=
  (setup.positionContext p marked).normalizedSense (setup.positionBranch p marked)

/-- Every position sense is `±1`. -/
theorem positionSense_eq_one_or_neg_one (setup : ActualSlotPhysicalSetup input)
    (p : Position setup.tree) (marked : setup.PositionMarked p) :
    setup.positionSense p marked = 1 ∨ setup.positionSense p marked = -1 :=
  (setup.positionContext p marked).normalizedSense_eq_one_or_neg_one
    (setup.positionBranch p marked)

/-- **The executed reader at a marked position returns `RS.ofHandedness` of its own normalized
physical sense.** -/
theorem position_referenceState_eq_chiral (setup : ActualSlotPhysicalSetup input)
    (p : Position setup.tree) (marked : setup.PositionMarked p) :
    LocalizedUniversalReference.referenceState input (positionSource p).occurrence =
      some (.chiral (RS.ofHandedness (setup.positionSense p marked))) :=
  (setup.positionContext p marked).referenceState_eq_chiral_ofHandedness
    (setup.positionBranch p marked)

/-- **The tree label at a marked position is that same physical letter.** -/
theorem position_label_eq_ofHandedness (setup : ActualSlotPhysicalSetup input)
    (p : Position setup.tree) (marked : setup.PositionMarked p) :
    (positionNode p).label =
      some (.chiral (RS.ofHandedness (setup.positionSense p marked))) := by
  rw [setup.tree_positionNode_label_eq_state p]
  exact setup.position_referenceState_eq_chiral p marked

/-- **The pointwise physical pair class at any marked position.**  For any reference letter that is
`RS.ofHandedness` of a `±1` sense, decoding the observed label of *this* position gives exactly the
physical pair class of the two normalized senses, with `like` iff their product is one. -/
theorem position_sourceObserve_eq_pairClass (setup : ActualSlotPhysicalSetup input)
    (p : Position setup.tree) (marked : setup.PositionMarked p) {referenceSense : ℝ}
    (referenceCases : referenceSense = 1 ∨ referenceSense = -1) :
    sourceObserveRule4bLabel (RS.ofHandedness referenceSense) ((positionNode p).label) =
      .withRule4b .chiral
        (some (physicalPairClass referenceSense (setup.positionSense p marked))) ∧
      (physicalPairClass referenceSense (setup.positionSense p marked) = .like ↔
        referenceSense * setup.positionSense p marked = 1) := by
  rw [setup.position_label_eq_ofHandedness p marked]
  exact ⟨sourceObserveRule4bLabel_ofHandedness_pairClass referenceCases
      (setup.positionSense_eq_one_or_neg_one p marked),
    physicalPairClass_eq_like_iff⟩

/-- **An unmarked position carries no uppercase letter.**  The classification is derived from the
original physical domain through the explicit canonical adapter; no absence of a label is assumed.
-/
theorem position_not_chiral_of_not_marked (setup : ActualSlotPhysicalSetup input)
    (p : Position setup.tree) (notMarked : ¬ setup.PositionMarked p) :
    ∀ letter : RS, (positionNode p).label ≠ some (.chiral letter) := by
  intro letter labelEq
  have stateChiral : LocalizedUniversalReference.referenceState input
      (positionSource p).occurrence = some (.chiral letter) := by
    rw [← setup.tree_positionNode_label_eq_state p]
    exact labelEq
  exact notMarked
    ((referenceState_chiral_iff_physicalMarked input setup.singleBonded setup.acyclic
      setup.hcharge setup.noDouble (input.certified.canonicalReindexConfiguration setup.cfg)
      setup.c setup.globalDomain setup.incomingEdge (positionSource p).occurrence
      (setup.position_source_root_eq p)
      (positionAtom_spec setup.singleBonded setup.acyclic p)
      (setup.position_atom_mem_cutBranch p)).mp ⟨letter, stateChiral⟩)

/-- An unmarked position reads back as no upper-case descriptor. -/
theorem position_chiralDescriptorOfLabel_eq_none (setup : ActualSlotPhysicalSetup input)
    (p : Position setup.tree) (notMarked : ¬ setup.PositionMarked p) :
    chiralDescriptorOfLabel ((positionNode p).label) = none := by
  rw [chiralDescriptorOfLabel_eq_none_iff]
  exact setup.position_not_chiral_of_not_marked p notMarked

/-- **An unmarked position is pair-free for every candidate reference letter.** -/
theorem position_sourceObserve_pair?_eq_none (setup : ActualSlotPhysicalSetup input)
    (p : Position setup.tree) (notMarked : ¬ setup.PositionMarked p) (reference : RS) :
    (sourceObserveRule4bLabel reference ((positionNode p).label)).pair? = none :=
  sourceObserveRule4bLabel_pair?_eq_none_of_not_chiral reference _
    (setup.position_not_chiral_of_not_marked p notMarked)

/-! ## D. The unique nearest actual position and the selected reference -/




def nearestPosition (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) :
    Position setup.tree :=
  (actualSlotCutEquiv input setup.c setup.frame setup.frameComputed setup.slot setup.singleBonded
    setup.acyclic setup.oAtom setup.oObserved).symm ⟨center, unique.1⟩

/-- The nearest position's atom is the nearest centre. -/
theorem nearestPosition_atom (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) :
    positionAtom setup.singleBonded setup.acyclic (setup.nearestPosition unique) = center :=
  actualSlotCutEquiv_symm_apply input setup.c setup.frame setup.frameComputed setup.slot
    setup.singleBonded setup.acyclic setup.oAtom setup.oObserved unique.1

/-- The nearest position is physically marked. -/
theorem nearestPosition_marked (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) :
    setup.PositionMarked (setup.nearestPosition unique) := by
  show PhysicalMarkedAtom input setup.root
    (positionAtom setup.singleBonded setup.acyclic (setup.nearestPosition unique))
  rw [setup.nearestPosition_atom unique]
  exact unique.2.1

/-- The nearest position's actual occurrence keeps the final root. -/
theorem nearestPosition_root (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) :
    (positionSource (setup.nearestPosition unique)).occurrence.1.root = setup.c.1 :=
  actualSlotCutEquiv_symm_root input setup.c setup.frame setup.frameComputed setup.slot
    setup.singleBonded setup.acyclic setup.oAtom setup.oObserved unique.1

/-- The nearest position's actual occurrence observes the nearest centre. -/
theorem nearestPosition_current (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) :
    (positionSource (setup.nearestPosition unique)).occurrence.1.node.current? = some center :=
  actualSlotCutEquiv_symm_current input setup.c setup.frame setup.frameComputed setup.slot
    setup.singleBonded setup.acyclic setup.oAtom setup.oObserved unique.1

/-- **The actual selected reference is the actual reader letter at the nearest occurrence.**  The
branch mark at the unique nearest centre equals `RS.ofHandedness` of that position's normalized
physical sense, derived from the reader equation at the *actual* nearest occurrence. -/
theorem branchMarkedDescriptor_nearestPosition (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) :
    branchMarkedDescriptor input setup.c setup.frame setup.frameComputed setup.slot
        setup.singleBonded setup.acyclic setup.oAtom setup.oObserved center =
      some (RS.ofHandedness (setup.positionSense (setup.nearestPosition unique)
        (setup.nearestPosition_marked unique))) := by
  have mark := branchMarkedDescriptor_positionAtom input setup.c setup.frame setup.frameComputed
    setup.slot setup.singleBonded setup.acyclic setup.oAtom setup.oObserved
    (p := setup.nearestPosition unique)
  rw [setup.nearestPosition_atom unique] at mark
  rw [mark, setup.position_referenceState_eq_chiral (setup.nearestPosition unique)
    (setup.nearestPosition_marked unique)]
  rfl






theorem nearestPosition_selectedReference_eq_state (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat} {descriptor : RS}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    (centerMarked : branchMarkedDescriptor input setup.c setup.frame setup.frameComputed
      setup.slot setup.singleBonded setup.acyclic setup.oAtom setup.oObserved center =
        some descriptor) :
    LocalizedUniversalReference.referenceState input
        (positionSource (setup.nearestPosition unique)).occurrence =
      some (.chiral descriptor) := by
  have produced := setup.position_referenceState_eq_chiral (setup.nearestPosition unique)
    (setup.nearestPosition_marked unique)
  have selectedEq := setup.branchMarkedDescriptor_nearestPosition unique
  have descriptorEq : descriptor = RS.ofHandedness (setup.positionSense
      (setup.nearestPosition unique) (setup.nearestPosition_marked unique)) :=
    Option.some.inj (centerMarked.symm.trans selectedEq)
  rw [descriptorEq]
  exact produced








def nearestOccurrenceContext (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    {occurrence : LocalizedUniversalReference.Occurrence input}
    (occurrenceRoot : occurrence.1.root = setup.c.1)
    (occurrenceCurrent : occurrence.1.node.current? = some center) :
    DomainPhysicalContext input :=
  { singleBonded := setup.singleBonded
    acyclic := setup.acyclic
    hcharge := setup.hcharge
    noDouble := setup.noDouble
    cfg := setup.cfg
    root := setup.root
    domain := setup.physicalDomain
    center := ⟨center, unique.2.1.2.1⟩
    center_ne_root := by
      intro same
      exact AcyclicCutBranchAutomorphism.cutBranch_ne_center input.certified.moleculeGraph
        unique.1 (congrArg Subtype.val same)
    target := occurrence
    targetCurrent := occurrenceCurrent
    root_eq := occurrenceRoot.symm }

@[simp] theorem nearestOccurrenceContext_cfg (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    {occurrence : LocalizedUniversalReference.Occurrence input}
    (occurrenceRoot : occurrence.1.root = setup.c.1)
    (occurrenceCurrent : occurrence.1.node.current? = some center) :
    (setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent).cfg = setup.cfg := rfl

@[simp] theorem nearestOccurrenceContext_root (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    {occurrence : LocalizedUniversalReference.Occurrence input}
    (occurrenceRoot : occurrence.1.root = setup.c.1)
    (occurrenceCurrent : occurrence.1.node.current? = some center) :
    (setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent).root = setup.root := rfl

@[simp] theorem nearestOccurrenceContext_domain (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    {occurrence : LocalizedUniversalReference.Occurrence input}
    (occurrenceRoot : occurrence.1.root = setup.c.1)
    (occurrenceCurrent : occurrence.1.node.current? = some center) :
    (setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent).domain =
      setup.physicalDomain := rfl

@[simp] theorem nearestOccurrenceContext_singleBonded (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    {occurrence : LocalizedUniversalReference.Occurrence input}
    (occurrenceRoot : occurrence.1.root = setup.c.1)
    (occurrenceCurrent : occurrence.1.node.current? = some center) :
    (setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent).singleBonded =
      setup.singleBonded := rfl

@[simp] theorem nearestOccurrenceContext_acyclic (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    {occurrence : LocalizedUniversalReference.Occurrence input}
    (occurrenceRoot : occurrence.1.root = setup.c.1)
    (occurrenceCurrent : occurrence.1.node.current? = some center) :
    (setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent).acyclic =
      setup.acyclic := rfl

@[simp] theorem nearestOccurrenceContext_hcharge (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    {occurrence : LocalizedUniversalReference.Occurrence input}
    (occurrenceRoot : occurrence.1.root = setup.c.1)
    (occurrenceCurrent : occurrence.1.node.current? = some center) :
    (setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent).hcharge =
      setup.hcharge := rfl

@[simp] theorem nearestOccurrenceContext_noDouble (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    {occurrence : LocalizedUniversalReference.Occurrence input}
    (occurrenceRoot : occurrence.1.root = setup.c.1)
    (occurrenceCurrent : occurrence.1.node.current? = some center) :
    (setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent).noDouble =
      setup.noDouble := rfl

@[simp] theorem nearestOccurrenceContext_target (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    {occurrence : LocalizedUniversalReference.Occurrence input}
    (occurrenceRoot : occurrence.1.root = setup.c.1)
    (occurrenceCurrent : occurrence.1.node.current? = some center) :
    (setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent).target =
      occurrence := rfl

/-- The rigid branch at the named nearest-occurrence context, taken from the nearest witness's own
non-twin fact; retained definitionally. -/
def nearestOccurrenceBranch (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    {occurrence : LocalizedUniversalReference.Occurrence input}
    (occurrenceRoot : occurrence.1.root = setup.c.1)
    (occurrenceCurrent : occurrence.1.node.current? = some center) :
    DomainPhysicalRigidBranch
      (setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent) :=
  ⟨unique.2.1.2.2⟩










theorem nearestOccurrence_context_normalized (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance)
    {occurrence : LocalizedUniversalReference.Occurrence input}
    (occurrenceRoot : occurrence.1.root = setup.c.1)
    (occurrenceCurrent : occurrence.1.node.current? = some center)
    {r : RS}
    (occurrenceState : LocalizedUniversalReference.referenceState input occurrence =
      some (.chiral r)) :
    r = RS.ofHandedness
        ((setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent).normalizedSense
          (setup.nearestOccurrenceBranch unique occurrenceRoot occurrenceCurrent)) ∧
      (setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent).target =
        occurrence := by
  have produced :=
    (setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent).referenceState_eq_chiral_ofHandedness
      (setup.nearestOccurrenceBranch unique occurrenceRoot occurrenceCurrent)
  have occurrenceState' : LocalizedUniversalReference.referenceState input
      (setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent).target =
        some (.chiral r) := occurrenceState
  have labelsEq : LocalizedTetrahedralRSPseudoDescriptor.chiral r =
      LocalizedTetrahedralRSPseudoDescriptor.chiral
        (RS.ofHandedness
          ((setup.nearestOccurrenceContext unique occurrenceRoot occurrenceCurrent).normalizedSense
            (setup.nearestOccurrenceBranch unique occurrenceRoot occurrenceCurrent))) :=
    Option.some.inj (occurrenceState'.symm.trans produced)
  exact ⟨LocalizedTetrahedralRSPseudoDescriptor.chiral.inj labelsEq, rfl⟩









theorem nearest_signedRule5_normalized (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) :
    ∃ (slot : Fin 4)
      (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c) = some frame)
      (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some setup.oAtom)
      (r : RS)
      (priorReading : input.certified.LocalizedRerootRule4bcReading),
      input.certified.buildLocalizedRerootCompoundRule45Key?
            (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
            (referenceDependencyView input setup.c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt slot) =
          some (actualSlotCompoundKey input setup.c frame frameComputed slot) ∧
        (actualSlotCompoundKey input setup.c frame frameComputed slot).prior.references = [r] ∧
          (actualSlotCompoundKey input setup.c frame frameComputed slot).prior.readings =
            [priorReading] ∧
            priorReading.reference? = some r ∧
              branchMarkedDescriptor input setup.c frame frameComputed slot setup.singleBonded
                setup.acyclic setup.oAtom oObserved center = some r ∧
                ∃ (occurrence : LocalizedUniversalReference.Occurrence input)
                  (occurrenceRoot : occurrence.1.root = setup.c.1)
                  (occurrenceCurrent : occurrence.1.node.current? = some center),
                  LocalizedUniversalReference.referenceState input occurrence =
                      some (.chiral r) ∧
                    r = RS.ofHandedness
                        ((setup.nearestOccurrenceContext unique occurrenceRoot
                            occurrenceCurrent).normalizedSense
                          (setup.nearestOccurrenceBranch unique occurrenceRoot
                            occurrenceCurrent)) ∧
                      (setup.nearestOccurrenceContext unique occurrenceRoot
                          occurrenceCurrent).target = occurrence := by
  obtain ⟨slot, frame, frameComputed, oObserved, r, priorReading, reading, keyR, keyS,
    compoundBuilt, references, readings, referenceSome, rule5Readings, priorEq, builtR, builtS,
    commonR, commonS, treeMark, branchMark, _sphereBefore, _sphereAt, _direction, occurrence,
    occurrenceRoot, occurrenceCurrent, occurrenceState⟩ :=
    LocalizedPhysicalRule5PrefixClosure.exists_actualSlot_compoundReading_stageFor_signed_of_physicalAtom_noPrefix
      input setup.c setup.oAtom setup.incomingEdge setup.singleBonded setup.acyclic setup.hcharge
      setup.noDouble setup.cfg setup.physicalDomain unique
  obtain ⟨senseEq, targetEq⟩ :=
    setup.nearestOccurrence_context_normalized unique occurrenceRoot occurrenceCurrent
      occurrenceState
  exact ⟨slot, frame, frameComputed, oObserved, r, priorReading, compoundBuilt, references,
    readings, referenceSome, branchMark, occurrence, occurrenceRoot, occurrenceCurrent,
    occurrenceState, senseEq, targetEq⟩










theorem nearest_signedRule5_normalized_payload (setup : ActualSlotPhysicalSetup input)
    {center : input.certified.Atom} {distance : Nat}
    (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance) :
    ∃ (slot : Fin 4)
      (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c) = some frame)
      (oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some setup.oAtom)
      (r : RS)
      (priorReading : input.certified.LocalizedRerootRule4bcReading)
      (reading : input.certified.LocalizedRerootRule5Reading)
      (keyR keyS : input.certified.LocalizedRerootCumulativeRule45Key),
      input.certified.buildLocalizedRerootCompoundRule45Key?
            (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
            (referenceDependencyView input setup.c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt slot) =
          some (actualSlotCompoundKey input setup.c frame frameComputed slot) ∧
        (actualSlotCompoundKey input setup.c frame frameComputed slot).prior.references = [r] ∧
        (actualSlotCompoundKey input setup.c frame frameComputed slot).prior.readings =
          [priorReading] ∧
        priorReading.reference? = some r ∧
        (actualSlotCompoundKey input setup.c frame frameComputed slot).rule5Readings = [reading] ∧
        reading.prior = priorReading ∧
        input.certified.buildLocalizedRerootCumulativeRule45Key?
            (localizedRule5StageFor (some r) .R)
            (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
            (referenceDependencyView input setup.c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt slot) = some keyR ∧
        input.certified.buildLocalizedRerootCumulativeRule45Key?
            (localizedRule5StageFor (some r) .S)
            (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
            (referenceDependencyView input setup.c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (frame.cursorAt slot) = some keyS ∧
        reading.commonR = keyR ∧
        reading.commonS = keyS ∧
        LocalizedUniqueNearestRule5Direction.actualTreeMark input setup.singleBonded setup.acyclic
          (actualSlotTree input setup.c frame frameComputed slot) center = some r ∧
        branchMarkedDescriptor input setup.c frame frameComputed slot setup.singleBonded
          setup.acyclic setup.oAtom oObserved center = some r ∧
        (∀ e, e < distance →
          LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
            ((keyR.labels.getD e []).map Prod.snd) = []) ∧
        LocalizedCumulativeDecoratedTree.chiralDescriptorsOfObservations
          ((keyR.labels.getD distance []).map Prod.snd) = [r] ∧
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
            keyR.descriptor keyS.descriptor =
          (if r = RS.R then Ordering.gt else Ordering.lt) ∧
        ∃ (occurrence : LocalizedUniversalReference.Occurrence input)
          (occurrenceRoot : occurrence.1.root = setup.c.1)
          (occurrenceCurrent : occurrence.1.node.current? = some center),
          LocalizedUniversalReference.referenceState input occurrence = some (.chiral r) ∧
            r = RS.ofHandedness
                ((setup.nearestOccurrenceContext unique occurrenceRoot
                    occurrenceCurrent).normalizedSense
                  (setup.nearestOccurrenceBranch unique occurrenceRoot occurrenceCurrent)) ∧
              (setup.nearestOccurrenceContext unique occurrenceRoot
                  occurrenceCurrent).target = occurrence := by
  obtain ⟨slot, frame, frameComputed, oObserved, r, priorReading, reading, keyR, keyS,
    compoundBuilt, references, readings, referenceSome, rule5Readings, priorEq, builtR, builtS,
    commonR, commonS, treeMark, branchMark, sphereBefore, sphereAt, direction, occurrence,
    occurrenceRoot, occurrenceCurrent, occurrenceState⟩ :=
    LocalizedPhysicalRule5PrefixClosure.exists_actualSlot_compoundReading_stageFor_signed_of_physicalAtom_noPrefix
      input setup.c setup.oAtom setup.incomingEdge setup.singleBonded setup.acyclic setup.hcharge
      setup.noDouble setup.cfg setup.physicalDomain unique
  obtain ⟨senseEq, targetEq⟩ :=
    setup.nearestOccurrence_context_normalized unique occurrenceRoot occurrenceCurrent
      occurrenceState
  exact ⟨slot, frame, frameComputed, oObserved, r, priorReading, reading, keyR, keyS,
    compoundBuilt, references, readings, referenceSome, rule5Readings, priorEq, builtR, builtS,
    commonR, commonS, treeMark, branchMark, sphereBefore, sphereAt, direction, occurrence,
    occurrenceRoot, occurrenceCurrent, occurrenceState, senseEq, targetEq⟩

/-! ## E. The actual physical reference observation closure -/

/-- **Pointwise physical reference selection and observations at the actual slot.**

The hypothesis is only the reader-independent physical branch domain at the final root
(`PhysicalBranchDomain`): the physical cut branch carries either no physically marked atom, or a
unique nearest one.  The conclusions are:

* in the empty case the *actual executable* reference list and the actual production `prior`
  reference list are empty, the single actual reading has no reference, every actual position is
  physically unmarked, and every position's source observation is pair-free;
* in the nearest case the actual descriptor is the branch mark at the unique nearest centre, the
  actual executable and production reference lists are the singleton `[descriptor]`, the single
  actual reading selects it, and at **every** actual position the label is the physical letter
  `RS.ofHandedness` of that position's own normalized sense; at every marked position the source
  observation is exactly the physical pair class of the nearest sense and the position's sense
  (`like` iff the product is one), while unmarked positions stay pair-free.

No reference letter, selector output or absent label is assumed anywhere. -/
theorem physicalReferenceSelection_pointwise (setup : ActualSlotPhysicalSetup input)
    (branchDomain : PhysicalBranchDomain input setup.root setup.oAtom) :
    (localizedRule4bReferencesFromRankedLabels setup.key.prior.rule4aKey.rankedLabels = [] ∧
        setup.key.prior.references = [] ∧
          ∃ reading : input.certified.LocalizedRerootRule4bcReading,
            setup.key.prior.readings = [reading] ∧ reading.reference? = none ∧
            (∀ p : Position setup.tree, ¬ setup.PositionMarked p) ∧
            (∀ (p : Position setup.tree) (reference : RS),
              (sourceObserveRule4bLabel reference ((positionNode p).label)).pair? = none)) ∨
      ∃ (center : input.certified.Atom) (distance : Nat) (descriptor : RS)
          (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom center distance),
        branchMarkedDescriptor input setup.c setup.frame setup.frameComputed setup.slot
            setup.singleBonded setup.acyclic setup.oAtom setup.oObserved center = some descriptor ∧
          localizedRule4bReferencesFromRankedLabels
              setup.key.prior.rule4aKey.rankedLabels = [descriptor] ∧
            setup.key.prior.references = [descriptor] ∧
              (∃ reading : input.certified.LocalizedRerootRule4bcReading,
                setup.key.prior.readings = [reading] ∧ reading.reference? = some descriptor) ∧
                descriptor = RS.ofHandedness (setup.positionSense (setup.nearestPosition unique)
                  (setup.nearestPosition_marked unique)) ∧
                  (∀ (p : Position setup.tree) (marked : setup.PositionMarked p),
                    (positionNode p).label =
                      some (.chiral (RS.ofHandedness (setup.positionSense p marked)))) ∧
                    (∀ (p : Position setup.tree) (marked : setup.PositionMarked p),
                      sourceObserveRule4bLabel descriptor ((positionNode p).label) =
                          .withRule4b .chiral (some (physicalPairClass
                            (setup.positionSense (setup.nearestPosition unique)
                              (setup.nearestPosition_marked unique))
                            (setup.positionSense p marked))) ∧
                        (physicalPairClass
                            (setup.positionSense (setup.nearestPosition unique)
                              (setup.nearestPosition_marked unique))
                            (setup.positionSense p marked) = .like ↔
                          setup.positionSense (setup.nearestPosition unique)
                              (setup.nearestPosition_marked unique) *
                            setup.positionSense p marked = 1)) ∧
                      (∀ (p : Position setup.tree) (notMarked : ¬ setup.PositionMarked p),
                        chiralDescriptorOfLabel ((positionNode p).label) = none ∧
                          ∀ reference : RS,
                            (sourceObserveRule4bLabel reference
                              ((positionNode p).label)).pair? = none) := by
  rcases branchDomain with unmarked | ⟨center, distance, unique⟩
  · obtain ⟨selectionNil, referencesNil, reading, readings, referenceNone⟩ :=
      actualSlot_physicalBranchUnmarked_references_nil input setup.c setup.frame setup.frameComputed
        setup.slot setup.singleBonded setup.acyclic setup.hcharge setup.noDouble
        (input.certified.canonicalReindexConfiguration setup.cfg) setup.globalDomain
        setup.oAtom setup.oObserved unmarked
    refine Or.inl ⟨selectionNil, referencesNil, reading, readings, referenceNone, ?_, ?_⟩
    · intro p marked
      exact unmarked (positionAtom setup.singleBonded setup.acyclic p)
        (setup.position_atom_mem_cutBranch p) marked
    · intro p reference
      exact setup.position_sourceObserve_pair?_eq_none p (fun marked =>
        unmarked _ (setup.position_atom_mem_cutBranch p) marked) reference
  · obtain ⟨descriptor, marked⟩ :=
      exists_markedBranchUniqueNearest_of_physicalBranchUniqueNearest input setup.c setup.frame
        setup.frameComputed setup.slot setup.singleBonded setup.acyclic setup.hcharge
        setup.noDouble (input.certified.canonicalReindexConfiguration setup.cfg)
        setup.globalDomain setup.oAtom setup.oObserved unique
    obtain ⟨selectionSingleton, referencesSingleton, reading, readings, referenceSome⟩ :=
      actualSlot_markedBranchUniqueNearest_references_singleton input setup.c setup.frame
        setup.frameComputed setup.slot setup.singleBonded setup.acyclic setup.hcharge
        setup.noDouble (input.certified.canonicalReindexConfiguration setup.cfg)
        setup.globalDomain setup.oAtom setup.oObserved marked
    have descriptorEq : descriptor = RS.ofHandedness (setup.positionSense
        (setup.nearestPosition unique) (setup.nearestPosition_marked unique)) :=
      Option.some.inj (marked.2.1.symm.trans
        (setup.branchMarkedDescriptor_nearestPosition unique))
    refine Or.inr ⟨center, distance, descriptor, unique, marked.2.1, selectionSingleton,
      referencesSingleton, ⟨reading, readings, referenceSome⟩, descriptorEq, ?_, ?_, ?_⟩
    · intro p markedP
      exact setup.position_label_eq_ofHandedness p markedP
    · intro p markedP
      have pairClass := setup.position_sourceObserve_eq_pairClass p markedP
        (setup.positionSense_eq_one_or_neg_one (setup.nearestPosition unique)
          (setup.nearestPosition_marked unique))
      refine ⟨?_, pairClass.2⟩
      rw [descriptorEq]
      exact pairClass.1
    · intro p notMarked
      exact ⟨setup.position_chiralDescriptorOfLabel_eq_none p notMarked, fun reference =>
        setup.position_sourceObserve_pair?_eq_none p notMarked reference⟩

/-- **The full actual observation closure as a named proposition.**  Conjoins the actual compound
build, the actual Rules-4b/4c prior build, the actual Rule-4a build, the actual tree source, its
exact label table and its realization of the generated restricted dependency reader with the
pointwise physical selection/observation disjunction.  Being a `Prop`-valued abbreviation, it can be
used as the body of an existential (`physicalReferenceObservation_closure_of_physical`); it never
supplies any of these objects. -/
abbrev PhysicalReferenceObservationClosure (setup : ActualSlotPhysicalSetup input)
    (branchDomain : PhysicalBranchDomain input setup.root setup.oAtom) : Prop :=
  input.certified.buildLocalizedRerootCompoundRule45Key?
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
        (referenceDependencyView input setup.c)
        (localizedOccurrenceRerootEvaluationFuel
          (LocalizedUniversalReference.carrierFuel input))
        (setup.frame.cursorAt setup.slot) = some setup.key ∧
      input.certified.buildLocalizedRerootCompoundRule4bcKey?
          (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
          (referenceDependencyView input setup.c)
          (localizedOccurrenceRerootEvaluationFuel
            (LocalizedUniversalReference.carrierFuel input))
          (setup.frame.cursorAt setup.slot) = some setup.key.prior ∧
        input.certified.buildLocalizedRerootCumulativeRule45Key?
            .rule4a
            (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
            (referenceDependencyView input setup.c)
            (localizedOccurrenceRerootEvaluationFuel
              (LocalizedUniversalReference.carrierFuel input))
            (setup.frame.cursorAt setup.slot) = some setup.key.prior.rule4aKey ∧
          setup.tree.source = setup.frame.cursorAt setup.slot ∧
            setup.tree.labelTable = setup.key.prior.rule4aKey.labels ∧
              LocalizedCumulativeTreeRealizes input.certified
                  (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c)
                  setup.tree ∧
                ((localizedRule4bReferencesFromRankedLabels
                      setup.key.prior.rule4aKey.rankedLabels = [] ∧
                    setup.key.prior.references = [] ∧
                      ∃ reading : input.certified.LocalizedRerootRule4bcReading,
                        setup.key.prior.readings = [reading] ∧ reading.reference? = none ∧
                        (∀ p : Position setup.tree, ¬ setup.PositionMarked p) ∧
                        (∀ (p : Position setup.tree) (reference : RS),
                          (sourceObserveRule4bLabel reference
                            ((positionNode p).label)).pair? = none)) ∨
                  ∃ (center : input.certified.Atom) (distance : Nat) (descriptor : RS)
                      (unique : PhysicalBranchUniqueNearest input setup.root setup.oAtom
                        center distance),
                    branchMarkedDescriptor input setup.c setup.frame setup.frameComputed setup.slot
                        setup.singleBonded setup.acyclic setup.oAtom setup.oObserved center =
                          some descriptor ∧
                      localizedRule4bReferencesFromRankedLabels
                          setup.key.prior.rule4aKey.rankedLabels = [descriptor] ∧
                        setup.key.prior.references = [descriptor] ∧
                          (∃ reading : input.certified.LocalizedRerootRule4bcReading,
                            setup.key.prior.readings = [reading] ∧
                              reading.reference? = some descriptor) ∧
                            descriptor = RS.ofHandedness
                              (setup.positionSense (setup.nearestPosition unique)
                                (setup.nearestPosition_marked unique)) ∧
                              (∀ (p : Position setup.tree) (marked : setup.PositionMarked p),
                                (positionNode p).label =
                                  some (.chiral (RS.ofHandedness
                                    (setup.positionSense p marked)))) ∧
                                (∀ (p : Position setup.tree)
                                    (marked : setup.PositionMarked p),
                                  sourceObserveRule4bLabel descriptor ((positionNode p).label) =
                                      .withRule4b .chiral (some (physicalPairClass
                                        (setup.positionSense (setup.nearestPosition unique)
                                          (setup.nearestPosition_marked unique))
                                        (setup.positionSense p marked))) ∧
                                    (physicalPairClass
                                        (setup.positionSense (setup.nearestPosition unique)
                                          (setup.nearestPosition_marked unique))
                                        (setup.positionSense p marked) = .like ↔
                                      setup.positionSense (setup.nearestPosition unique)
                                          (setup.nearestPosition_marked unique) *
                                        setup.positionSense p marked = 1)) ∧
                                  (∀ (p : Position setup.tree)
                                      (notMarked : ¬ setup.PositionMarked p),
                                    chiralDescriptorOfLabel ((positionNode p).label) = none ∧
                                      ∀ reference : RS,
                                        (sourceObserveRule4bLabel reference
                                          ((positionNode p).label)).pair? = none))

/-- **Final wrapper retaining the actual production builds.**  The conclusion conjoins the actual
compound build, the actual Rules-4b/4c prior build, the actual Rule-4a build, the actual tree source,
its exact label table and its realization of the generated restricted dependency reader with the
pointwise physical selection/observation disjunction.  None of these objects is supplied by the
caller; all are the actual outputs retained from the adequacy theorems. -/
theorem physicalReferenceObservation_closure (setup : ActualSlotPhysicalSetup input)
    (branchDomain : PhysicalBranchDomain input setup.root setup.oAtom) :
    setup.PhysicalReferenceObservationClosure branchDomain :=
  ⟨setup.compoundBuilt, setup.priorBuilt, setup.rule4aBuilt, setup.tree_source,
    setup.tree_labelTable, setup.tree_realizes,
    setup.physicalReferenceSelection_pointwise branchDomain⟩

end ActualSlotPhysicalSetup

/-! ## F. Physical entry point without any frame-success or unique-nearest premise

`ActualSlotPhysicalSetup` carries `frameComputed` and `oObserved` as fields: success facts for the
executable frame of the final occurrence.  Those are *not* scientific inputs.  The accepted physical
frame link (`CertifiedLocalizedCIPInput.exists_physicalFrameSlotLink`) derives an actual frame and
slot from the original physical data plus an atom actually bonded to the detected centre, with no
frame success, canonical sorting or desired geometry assumed.  The indexed structure below keeps the
original centre, configuration, physical domain and attachment atom as **indices**, so they are
retained definitionally instead of being hidden behind an existential, and
`exists_actualSlotPhysicalSetupOf` produces one from the physical input alone.  Frame construction is
independent of the reference selector, so the empty branch needs no unique nearest. -/

/-- The physical-input-indexed slot setup: the same actual data as `ActualSlotPhysicalSetup`, but
with the original detected centre, original configuration, original physical general-rigid/twin
domain and attachment atom as **indices**.  A consumer therefore sees those exact inputs
definitionally through `toSetup` and the `toSetup_*` projections, while the frame, its executable
success equation, the slot and the slot observation remain the derived actual data. -/
structure ActualSlotPhysicalSetupOf (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (oAtom : input.certified.Atom) where
  /-- The actual four-ligand frame derived from the physical frame link. -/
  frame : input.certified.LocalizedOccurrenceFourLigandFrame
    (LocalizedUniversalReference.carrierFuel input)
  /-- The frame really is the executable frame of the final occurrence. -/
  frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
    (ActualReaderPhysicalBranchInverse.topTarget input c) = some frame
  /-- The derived frame slot whose cursor observes the attachment atom. -/
  slot : Fin 4
  /-- The certified bond graph is simple-bonded. -/
  singleBonded : input.certified.moleculeGraph.SimpleBonded
  /-- The certified bond graph is acyclic. -/
  acyclic : input.certified.moleculeGraph.Acyclic
  /-- Every atom carries the same formal charge. -/
  hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph
  /-- The molecule has no localized double-bond records. -/
  noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords
  /-- The derived slot cursor observes the attachment atom. -/
  oObserved : (frame.cursorAt slot).occurrence.1.node.current? = some oAtom

namespace ActualSlotPhysicalSetupOf

variable {input : LocalizedUniversalReference.Input}
variable {c : input.certified.detectedMultiCenterMolecule.Center}
variable {cfg : input.certified.detectedMultiCenterMolecule.Configuration}
variable {physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
  input.certified.detectedMultiCenterMolecule cfg c}
variable {oAtom : input.certified.Atom}

/-- Forget the indices: the same actual data viewed as a setup at its own original inputs. -/
def toSetup (setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) :
    ActualSlotPhysicalSetup input :=
  { c := c
    frame := setup.frame
    frameComputed := setup.frameComputed
    slot := setup.slot
    singleBonded := setup.singleBonded
    acyclic := setup.acyclic
    hcharge := setup.hcharge
    noDouble := setup.noDouble
    cfg := cfg
    physicalDomain := physicalDomain
    oAtom := oAtom
    oObserved := setup.oObserved }

@[simp] theorem toSetup_c (setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) :
    setup.toSetup.c = c := rfl

@[simp] theorem toSetup_frame (setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) :
    setup.toSetup.frame = setup.frame := rfl

@[simp] theorem toSetup_frameComputed
    (setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) :
    setup.toSetup.frameComputed = setup.frameComputed := rfl

@[simp] theorem toSetup_slot (setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) :
    setup.toSetup.slot = setup.slot := rfl

@[simp] theorem toSetup_singleBonded
    (setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) :
    setup.toSetup.singleBonded = setup.singleBonded := rfl

@[simp] theorem toSetup_acyclic
    (setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) :
    setup.toSetup.acyclic = setup.acyclic := rfl

@[simp] theorem toSetup_hcharge
    (setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) :
    setup.toSetup.hcharge = setup.hcharge := rfl

@[simp] theorem toSetup_noDouble
    (setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) :
    setup.toSetup.noDouble = setup.noDouble := rfl

@[simp] theorem toSetup_cfg (setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) :
    setup.toSetup.cfg = cfg := rfl

@[simp] theorem toSetup_physicalDomain
    (setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) :
    setup.toSetup.physicalDomain = physicalDomain := rfl

@[simp] theorem toSetup_oAtom
    (setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) :
    setup.toSetup.oAtom = oAtom := rfl

@[simp] theorem toSetup_oObserved
    (setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) :
    setup.toSetup.oObserved = setup.oObserved := rfl

end ActualSlotPhysicalSetupOf

/-- **The actual physical frame/slot is derived, not assumed.**  From the certified graph facts, the
original configuration, the original physical general-rigid/twin domain at the detected centre, and
an atom actually bonded to that centre, an indexed setup exists.  The frame is the accepted physical
frame link's actual frame at the final occurrence, and the slot is the slot whose cursor observes
the attachment atom.  No frame success, desired letter, reader equation or nearest selection is
assumed, so empty branches are included. -/
theorem exists_actualSlotPhysicalSetupOf
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (oAtom : input.certified.Atom)
    (adjacent : input.certified.moleculeGraph.Adj c.1 oAtom) :
    Nonempty (ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom) := by
  classical
  obtain ⟨frame, alpha, frameComputed, cursor⟩ :=
    CertifiedLocalizedCIPInput.exists_physicalFrameSlotLink input.certified
      (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      (ActualReaderPhysicalBranchInverse.topTarget input c)
      singleBonded acyclic (globalCarrierFuel_adequate input) c
      (ActualReaderPhysicalBranchInverse.topTarget_current input c)
  obtain ⟨i, ligandEq⟩ :=
    MultiCenterMolecule.ligandAtomAt_surjective
      input.certified.detectedMultiCenterMolecule c oAtom adjacent
  have oObserved : (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? = some oAtom := by
    simpa [Equiv.apply_symm_apply, ligandEq] using cursor (alpha.symm i)
  exact ⟨{ frame := frame
           frameComputed := frameComputed
           slot := alpha.symm i
           singleBonded := singleBonded
           acyclic := acyclic
           hcharge := hcharge
           noDouble := noDouble
           oObserved := oObserved }⟩

/-- **Full physical closure from the original physical data, with the frame derived.**  The caller
supplies only the certified graph facts, the original configuration, the original physical
general-rigid/twin domain at the detected centre, an actually bonded attachment atom, and the
reader-independent physical branch domain (zero eligible references, or a unique nearest one).  The
actual frame and slot are derived, and the full closure — the actual compound, prior and Rule-4a
builds, tree source, exact label table, realization, and the pointwise physical selection and
observation disjunction — holds at them.  No frame success and no unique nearest are assumed for
construction, so the empty branch is covered. -/
theorem physicalReferenceObservation_closure_of_physical
    (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (hcharge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (physicalDomain : ActualGeneralRigidPhysicalDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (oAtom : input.certified.Atom)
    (adjacent : input.certified.moleculeGraph.Adj c.1 oAtom)
    (branchDomain : PhysicalBranchDomain input c oAtom) :
    ∃ setup : ActualSlotPhysicalSetupOf input c cfg physicalDomain oAtom,
      ActualSlotPhysicalSetup.PhysicalReferenceObservationClosure setup.toSetup branchDomain := by
  obtain ⟨setup⟩ := exists_actualSlotPhysicalSetupOf input c singleBonded acyclic hcharge noDouble
    cfg physicalDomain oAtom adjacent
  exact ⟨setup, setup.toSetup.physicalReferenceObservation_closure branchDomain⟩

/-! ## G. Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.SuppliedPhysicalReaderPair
assert_kernel_only TetraStereo.OneCenter.exists_suppliedPhysicalReaderPair
assert_kernel_only TetraStereo.OneCenter.SuppliedPhysicalReaderPair.toActualPair
assert_kernel_only TetraStereo.OneCenter.SuppliedPhysicalReaderPair.toActualPair_stepReference
assert_kernel_only TetraStereo.OneCenter.SuppliedPhysicalReaderPair.toActualPair_stepObserved
assert_kernel_only TetraStereo.OneCenter.SuppliedPhysicalReaderPair.sourceObservation_contrast
assert_kernel_only TetraStereo.OneCenter.SuppliedPhysicalReaderPair.sourceObservation_differ
assert_kernel_only TetraStereo.OneCenter.exists_actualPhysicalReaderPair_supplied
assert_kernel_only TetraStereo.OneCenter.exists_suppliedSourceObservation_contrast
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalFrameData.calibration
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.orderData
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.normalizedSense
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.normalizedSense_eq_one_or_neg_one
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.referenceState_eq_chiral_ofHandedness
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.referenceState_eq_chiral_iff_ofHandedness
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.sourceObserve_ofHandedness_eq_pairClass
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.sourceObserve_referenceState_eq_pairClass
assert_kernel_only TetraStereo.OneCenter.DomainPhysicalContext.referenceState_eq_chiral_iff_canonicalDescriptor
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.tree
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.key
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.root
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.incomingEdge
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.globalDomain
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.tree_source
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.tree_labelTable
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.tree_realizes
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.tree_previousEq
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.tree_valid
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.tree_sameRoot
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.tree_oObserved
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.tree_previousShorter
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.compoundBuilt
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.priorBuilt
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.rule4aBuilt
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_source_root_eq
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.tree_positionNode_label_eq_state
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.tree_positionNode_label_eq_state_of_actualStage
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.PositionMarked
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_atom_mem_cutBranch
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.positionCenter
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.positionCenter_ne_root
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.positionContext
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.positionBranch
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.positionSense
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.positionSense_eq_one_or_neg_one
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_referenceState_eq_chiral
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_label_eq_ofHandedness
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_sourceObserve_eq_pairClass
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_not_chiral_of_not_marked
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_chiralDescriptorOfLabel_eq_none
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.position_sourceObserve_pair?_eq_none
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestPosition
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestPosition_atom
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestPosition_marked
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestPosition_root
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestPosition_current
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.branchMarkedDescriptor_nearestPosition
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestPosition_selectedReference_eq_state
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestOccurrenceContext
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestOccurrenceContext_cfg
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestOccurrenceContext_root
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestOccurrenceContext_domain
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestOccurrenceContext_singleBonded
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestOccurrenceContext_acyclic
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestOccurrenceContext_hcharge
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestOccurrenceContext_noDouble
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestOccurrenceContext_target
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestOccurrenceBranch
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearestOccurrence_context_normalized
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearest_signedRule5_normalized
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.nearest_signedRule5_normalized_payload
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.physicalReferenceSelection_pointwise
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.PhysicalReferenceObservationClosure
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetup.physicalReferenceObservation_closure
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf.toSetup
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf.toSetup_c
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf.toSetup_frame
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf.toSetup_frameComputed
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf.toSetup_slot
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf.toSetup_singleBonded
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf.toSetup_acyclic
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf.toSetup_hcharge
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf.toSetup_noDouble
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf.toSetup_cfg
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf.toSetup_physicalDomain
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf.toSetup_oAtom
assert_kernel_only TetraStereo.OneCenter.ActualSlotPhysicalSetupOf.toSetup_oObserved
assert_kernel_only TetraStereo.OneCenter.exists_actualSlotPhysicalSetupOf
assert_kernel_only TetraStereo.OneCenter.physicalReferenceObservation_closure_of_physical

end TetraStereo.OneCenter
