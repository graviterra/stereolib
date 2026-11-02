import TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureDomain
import TetraStereo.OneCenter.LocalizedCyclicGeneralRigidLabelCovariance
import TetraStereo.OneCenter.LocalizedRule3DeclarativePriorityAgreement
import TetraStereo.OneCenter.LocalizedCyclicContextFrameCompilation
import TetraStereo.OneCenter.LocalizedOccurrenceExecutableRoots
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalTransport
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# First-sphere observations of actual localized builds for the symmetric fixture

This module establishes a reusable fact about the actual localized rule-major builder: a
successful constitutional key retains the cursor's current atomic number as the singleton first
Rule-1a sphere. Consequently an actual Rule-1a tie between two built cursors forces their root
atomic numbers to agree. This is the local obstruction needed to separate outward siblings by
their immediate elements; it assumes no generated labels or desired result.
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.LocalizedRuleMajorReference
open TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixture
open TetraStereo.OneCenter.MoleculeGraph
open TetraStereo.OneCenter.OfficialCIPNode

/-! ## The actual builder's retained first sphere -/

theorem actual_rule1a_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor : input.LocalizedRerootCursor carrierFuel}
    {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {key : input.LocalizedRerootCumulativeRule45Key}
    (built : input.buildRuleMajorCumulativeWithRead? stage read fuel cursor = some key) :
    key.constitutional.rule1a.head? =
      some [([], input.localizedRerootCursorRootAtomicNumber cursor)] := by
  have derivation : input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor
      key.constitutional :=
    LocalizedCyclicGeneralRigidLabelCovariance.ruleMajorBuild_declarative input built
  exact input.declarative_constitutional_rule1a_head cursor fuel key.constitutional derivation

theorem actual_rule1a_tie_rootAtomicNumber_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {left right : input.LocalizedRerootCursor carrierFuel}
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {fuelL fuelR : Nat}
    {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL readL fuelL left = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR readR fuelR right = some keyR)
    (tie : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyL.constitutional.rule1a keyR.constitutional.rule1a = Ordering.eq) :
    input.localizedRerootCursorRootAtomicNumber left =
      input.localizedRerootCursorRootAtomicNumber right := by
  have layers := (compareSparseLayers_compareNat_eq_iff _ _).mp tie
  have heads := congrArg List.head? layers
  rw [actual_rule1a_head input builtL, actual_rule1a_head input builtR] at heads
  have listEq := Option.some.inj heads
  have firstEq := congrArg List.head? listEq
  have pairEq := Option.some.inj firstEq
  exact congrArg Prod.snd pairEq

/-- Different first-sphere atomic numbers force reader-independent constitutional separation
between actual reroot cursors. A tie of any two full constitutional keys would imply a Rule-1a
tie, which the preceding head theorem turns into equality of the cursor root observations. -/
theorem constitutionallySeparated_of_rootAtomicNumber_ne
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {left right : input.LocalizedRerootCursor carrierFuel}
    (different : input.localizedRerootCursorRootAtomicNumber left ≠
      input.localizedRerootCursorRootAtomicNumber right) :
    LocalizedCyclicGeneralRigidPriority.ConstitutionallySeparated left right := by
  intro stageL stageR readL readR fuelL fuelR keyL keyR builtL builtR tied
  have columns := (officialRuleMajorKey_compare_eq_iff _ _).mp tied
  have rule1aTie := (compareSparseLayers_compareNat_eq_iff _ _).mpr columns.1
  exact different (actual_rule1a_tie_rootAtomicNumber_eq input builtL builtR rule1aTie)

theorem cursorRootAtomicNumber_eq_atomZ_of_current
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) {atom : input.Atom}
    (current : cursor.occurrence.1.node.current? = some atom) :
    input.localizedRerootCursorRootAtomicNumber cursor = input.moleculeGraph.atomZ atom := by
  cases provenance : cursor.occurrence.1.node.provenance <;>
    simp [CertifiedLocalizedCIPInput.localizedRerootCursorRootAtomicNumber,
      MoleculeGraph.officialNodeAtomLabel, current, provenance,
      MoleculeGraph.rawCIPAtomLabel, ofLex_toLex]

/-! ## The production root-0 occurrence and its detected frame -/

noncomputable section
open scoped Classical

def fixtureReference : LocalizedRuleMajorReference.Input where
  certified := symmetricCertified

private theorem atomCount :
    symmetricCertified.certified.input.molecule.atomCount = 9 := rfl

private def SA (i : Fin 9) : symmetricCertified.Atom :=
  ⟨i.val, by rw [atomCount]; exact i.isLt⟩

private theorem SA_eq (i : Fin 9) : SA i = i := by
  apply Fin.ext
  rfl

private theorem spatial_adj (i j : Fin 9) :
    symmetricCertified.moleculeGraph.Adj (SA i) (SA j) ↔ graph.Adj i j := by
  rw [SA_eq, SA_eq]

private theorem spatial_simpleBonded :
    symmetricCertified.moleculeGraph.SimpleBonded := by
  intro left right adjacent
  have leftEq : left = SA ⟨left.val, by rw [← atomCount]; exact left.isLt⟩ := Fin.ext rfl
  have rightEq : right = SA ⟨right.val, by rw [← atomCount]; exact right.isLt⟩ := Fin.ext rfl
  rw [leftEq, rightEq, spatial_adj] at adjacent
  exact simple_bonded _ _ adjacent

private theorem center_membership (i : Fin 9)
    (member : i ∈ graph.tetrahedralCenterSet) :
    SA i ∈ symmetricCertified.tetrahedralCenterSet := by
  rw [SA_eq]
  exact member

def rootTetra : symmetricCertified.TetrahedralCenter :=
  ⟨SA ⟨0, by decide⟩,
    center_membership ⟨0, by decide⟩ ((degree_four_iff 0).mpr (Or.inl rfl))⟩

abbrev rootTarget : Occurrence fixtureReference :=
  symmetricCertified.localizedFinalOccurrenceExecutable
    (carrierFuel fixtureReference) rootTetra

private theorem root_provenance_real :
    rootTarget.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  finalOccurrence_provenance_real fixtureReference rootTetra

abbrev rootUnit := finalCenterUnit fixtureReference rootTetra

abbrev rootTargetUnit := finalOccurrence_molecularFrameUnit fixtureReference rootTetra

abbrev rootFrames : ContextFrameCompilation fixtureReference rootTarget rootUnit rootTargetUnit :=
  cyclicContextFrameCompilation fixtureReference spatial_simpleBonded rootTarget
    root_provenance_real rootUnit rootTargetUnit

private theorem root_center : rootFrames.center.1 = SA ⟨0, by decide⟩ := by
  rw [rootFrames.centerEq]
  simp [rootUnit, finalCenterUnit, OccurrenceUnit.atom, rootTetra, SA]

private theorem root_slot (index : Fin 9)
    (adjacent : graph.Adj ⟨0, by decide⟩ index) :
    ∃ slot : Fin 4, rootFrames.actualLigandAtoms slot = SA index := by
  have adjacentCenter : symmetricCertified.moleculeGraph.Adj rootFrames.center.1
      (SA index) := by
    rw [root_center, spatial_adj]
    exact adjacent
  obtain ⟨i, atomEq⟩ :=
    symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt_surjective
      rootFrames.center (SA index) adjacentCenter
  refine ⟨rootFrames.detectedLigandPermutation.symm i, ?_⟩
  unfold fixtureReference
  simp [ContextFrameCompilation.actualLigandAtoms, Equiv.apply_symm_apply, atomEq]

def rootArmSlot : Fin 4 := Classical.choose
  (root_slot ⟨2, by decide⟩ ((adj_root 2).mpr (Or.inr (Or.inl rfl))))

theorem rootArmSlot_atom : rootFrames.actualLigandAtoms rootArmSlot = SA ⟨2, by decide⟩ :=
  Classical.choose_spec
    (root_slot ⟨2, by decide⟩ ((adj_root 2).mpr (Or.inr (Or.inl rfl))))

def rootClosingSlot : Fin 4 := Classical.choose
  (root_slot ⟨4, by decide⟩ ((adj_root 4).mpr (Or.inr (Or.inr (Or.inl rfl)))) )

theorem rootClosingSlot_atom :
    rootFrames.actualLigandAtoms rootClosingSlot = SA ⟨4, by decide⟩ :=
  Classical.choose_spec
    (root_slot ⟨4, by decide⟩ ((adj_root 4).mpr (Or.inr (Or.inr (Or.inl rfl)))) )

theorem rootArmSlot_ne_rootClosingSlot : rootArmSlot ≠ rootClosingSlot := by
  intro same
  have atoms := congrArg rootFrames.actualLigandAtoms same
  rw [rootArmSlot_atom, rootClosingSlot_atom] at atoms
  simp [SA] at atoms

def rootArmSwap : symmetricCertified.moleculeGraph.Aut :=
  ⟨swap24, swap24_isAutomorphism⟩

private theorem rootArmSwap_fixed0 :
    (rootArmSwap : Equiv.Perm symmetricCertified.Atom) (SA 0) = SA 0 := by
  change swap24 (SA 0) = SA 0
  simp [swap24, swap24Fun, SA]

private theorem rootTarget_transport :
    symmetricCertified.transportOccurrence spatial_simpleBonded rootArmSwap rootTarget =
      rootTarget := by
  apply Subtype.ext
  apply LocalizedCIPOccurrenceFrame.ext
  · change (rootArmSwap : Equiv.Perm symmetricCertified.Atom) (SA 0) = SA 0
    exact rootArmSwap_fixed0
  · change symmetricCertified.transportedAddress rootArmSwap (SA 0) (OfficialCIPNode.root (SA 0)) = []
    simp [CertifiedLocalizedCIPInput.transportedAddress, OfficialCIPNode.root,
      rootArmSwap_fixed0]

  · change mapOfficialNode (rootArmSwap : Equiv.Perm symmetricCertified.Atom)
      (OfficialCIPNode.root (SA 0)) = OfficialCIPNode.root (SA 0)
    simp [mapOfficialNode, OfficialCIPNode.root, rootArmSwap_fixed0]
  · change carrierFuel fixtureReference + 1 -
      (symmetricCertified.transportedAddress rootArmSwap (SA 0)
        (OfficialCIPNode.root (SA 0))).length = carrierFuel fixtureReference + 1
    simp [CertifiedLocalizedCIPInput.transportedAddress, OfficialCIPNode.root,
      rootArmSwap_fixed0]

/-- The fixture's root-0 occurrence is fixed by the explicit arm-swap automorphism. -/
theorem rootTarget_fixed_by_rootArmSwap :
    symmetricCertified.transportOccurrence spatial_simpleBonded rootArmSwap rootTarget =
      rootTarget := rootTarget_transport

private noncomputable def rootArmFrameTransport :
    symmetricCertified.ActualFrameSlotTransport spatial_simpleBonded rootArmSwap
      rootTarget rootFrames.center :=
  symmetricCertified.actualFrameSlotTransport spatial_simpleBonded rootArmSwap
    (globalCarrierFuel_adequate fixtureReference) rootTarget rootFrames.center
    ((symmetricCertified.localizedOccurrenceDescriptorCenter?_eq_some_iff
      rootTarget rootFrames.center).mp rootFrames.centerComputed)

private theorem rootArmFrameTransport_sourceFrame :
    rootArmFrameTransport.sourceFrame = rootFrames.frame :=
  Option.some.inj (rootArmFrameTransport.sourceComputed.symm.trans
    (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed rootFrames))

private theorem rootArmFrameTransport_imageFrame :
    rootArmFrameTransport.imageFrame = rootFrames.frame := by
  have imageComputed := rootArmFrameTransport.imageComputed
  rw [rootTarget_transport] at imageComputed
  exact Option.some.inj (imageComputed.symm.trans
    (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed rootFrames))

theorem rootArmSlot_transported :
    symmetricCertified.transportCursor spatial_simpleBonded rootArmSwap
        (rootFrames.frame.cursorAt rootArmSlot) =
      rootFrames.frame.cursorAt (rootArmFrameTransport.slotPerm rootArmSlot) := by
  have slots := rootArmFrameTransport.cursorAt_eq rootArmSlot
  rw [rootArmFrameTransport_sourceFrame, rootArmFrameTransport_imageFrame] at slots
  exact slots.symm

private theorem rootFrames_actualLigandAtoms_injective :
    Function.Injective rootFrames.actualLigandAtoms := by
  intro left right equal
  apply rootFrames.detectedLigandPermutation.injective
  apply symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt_injective
  simpa [ContextFrameCompilation.actualLigandAtoms] using equal

private theorem rootCursorCurrent_eq_atom (slot : Fin 4) :
    (rootFrames.frame.cursorAt slot).occurrence.1.node.current? =
      some (rootFrames.actualLigandAtoms slot) := by
  simpa [ContextFrameCompilation.actualLigandAtoms] using rootFrames.ligandAt slot

private theorem rootArmSwap_maps_2 :
    (rootArmSwap : Equiv.Perm symmetricCertified.Atom)
      (SA ⟨2, by decide⟩) = SA ⟨4, by decide⟩ := by
  apply Fin.ext
  change (swap24Fun (2 : Fin 9)).val = 4
  decide

private theorem rootArmFrameTransport_slotPerm_maps_arm_to_closing :
    rootArmFrameTransport.slotPerm rootArmSlot = rootClosingSlot := by
  have current := rootArmFrameTransport.current_eq rootArmSlot
  rw [rootArmFrameTransport_sourceFrame, rootArmFrameTransport_imageFrame,
    rootCursorCurrent_eq_atom rootArmSlot, rootArmSlot_atom] at current
  simp only [Option.map_some] at current
  rw [rootArmSwap_maps_2] at current
  have imageAtom : rootFrames.actualLigandAtoms
      (rootArmFrameTransport.slotPerm rootArmSlot) = SA ⟨4, by decide⟩ := by
    have slotCurrent := rootCursorCurrent_eq_atom
      (rootArmFrameTransport.slotPerm rootArmSlot)
    exact Option.some.inj (slotCurrent.symm.trans current)
  have closingAtom : rootFrames.actualLigandAtoms rootClosingSlot =
      SA ⟨4, by decide⟩ := rootClosingSlot_atom
  exact rootFrames_actualLigandAtoms_injective (imageAtom.trans closingAtom.symm)

theorem root_arm_rule1a_tie :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      (rootFrames.stages rootArmSlot).a.key.constitutional.rule1a
      (rootFrames.stages rootClosingSlot).a.key.constitutional.rule1a = Ordering.eq := by
  have sent := rootArmSlot_transported
  rw [rootArmFrameTransport_slotPerm_maps_arm_to_closing] at sent
  exact LocalizedRecursiveAuxiliaryPhysicalTransport.rootArms_rule1aTie
    (input := fixtureReference) spatial_simpleBonded rootFrames rootArmSwap sent

/-! ## The actual direct root-arm occurrence

Use the frame cursor itself as the auxiliary target. This retains the production occurrence
coordinate and avoids identifying it with a separately constructed child occurrence. -/

theorem rootArmCursor_real :
    (rootFrames.frame.cursorAt rootArmSlot).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom := by
  rw [LocalizedCyclicRootArmReachability.rootSlot_eq_canonicalLigandCursor
    spatial_simpleBonded rootFrames rfl root_provenance_real rootArmSlot]
  exact symmetricCertified.localizedLigandRootNode_provenance rootFrames.center
    (symmetricCertified.canonicalLigandReindex rootFrames.center
      (rootFrames.detectedLigandPermutation rootArmSlot))

theorem rootArmCursor_current :
    (rootFrames.frame.cursorAt rootArmSlot).occurrence.1.node.current? =
      some (SA ⟨2, by decide⟩) := by
  rw [rootCursorCurrent_eq_atom rootArmSlot, rootArmSlot_atom]

theorem rootArmCursor_isDetected :
    IsDetectedCenter symmetricCertified.moleculeGraph
      (symmetricCertified.molecularFrameUnit
        (rootFrames.frame.cursorAt rootArmSlot).occurrence.1).atom := by
  rw [LocalizedCyclicRootArmReachability.rootSlot_eq_canonicalLigandCursor
    spatial_simpleBonded rootFrames rfl root_provenance_real rootArmSlot]
  let canonicalIndex := symmetricCertified.canonicalLigandReindex rootFrames.center
    (rootFrames.detectedLigandPermutation rootArmSlot)
  have ligandEq : symmetricCertified.canonicalLigandAtom rootFrames.center canonicalIndex =
      SA ⟨2, by decide⟩ := by
    calc
      symmetricCertified.canonicalLigandAtom rootFrames.center canonicalIndex =
          symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
            (rootFrames.detectedLigandPermutation rootArmSlot) :=
        (symmetricCertified.canonicalLigandReindex_spec rootFrames.center
          (rootFrames.detectedLigandPermutation rootArmSlot)).symm
      _ = rootFrames.actualLigandAtoms rootArmSlot := by
        rfl
      _ = SA ⟨2, by decide⟩ := rootArmSlot_atom
  have unitAtom : (symmetricCertified.molecularFrameUnit
      (symmetricCertified.localizedLigandRootCursor rootFrames.center canonicalIndex).occurrence.1).atom =
      symmetricCertified.canonicalLigandAtom rootFrames.center canonicalIndex := by
    simp [CertifiedLocalizedCIPInput.localizedLigandRootCursor,
      CertifiedLocalizedCIPInput.localizedLigandRootNode,
      CertifiedLocalizedCIPInput.molecularFrameUnit,
      OfficialCIPNode.extend_history, OfficialCIPNode.root]
    rfl
  have detectedAtom : IsDetectedCenter symmetricCertified.moleculeGraph (SA ⟨2, by decide⟩) := by
    rw [IsDetectedCenter]
    apply (symmetricCertified.moleculeGraph.isTetrahedralCenter_iff_neighborFinset_card _).mp
    apply (symmetricCertified.moleculeGraph.mem_tetrahedralCenterSet _).mp
    rw [SA_eq]
    exact (degree_four_iff ⟨2, by decide⟩).mpr (Or.inr (Or.inl rfl))
  have detectedCanonical : IsDetectedCenter symmetricCertified.moleculeGraph
      (symmetricCertified.canonicalLigandAtom rootFrames.center canonicalIndex) := by
    simpa [ligandEq] using detectedAtom
  simpa [unitAtom, canonicalIndex] using detectedCanonical

abbrev rootArmTarget : Occurrence fixtureReference :=
  (rootFrames.frame.cursorAt rootArmSlot).occurrence

/-- The transported production arm occurrence is exactly the production closing-arm occurrence.
This exposes the already-proved cursor transport at occurrence level for downstream evaluation. -/
theorem rootArm_transportOccurrence_eq_closing :
    symmetricCertified.transportOccurrence spatial_simpleBonded rootArmSwap rootArmTarget =
      (rootFrames.frame.cursorAt rootClosingSlot).occurrence := by
  have sent := rootArmSlot_transported
  rw [rootArmFrameTransport_slotPerm_maps_arm_to_closing] at sent
  have occurrenceEq := congrArg
    (fun cursor : symmetricCertified.LocalizedRerootCursor (carrierFuel fixtureReference) =>
      cursor.occurrence) sent
  simpa only [symmetricCertified.transportCursor_occurrence] using occurrenceEq

def rootArmUnit : DetectedOccurrence symmetricCertified.moleculeGraph :=
  ⟨symmetricCertified.molecularFrameUnit rootArmTarget.1, rootArmCursor_isDetected⟩

noncomputable def rootArmContextFrames : ContextFrameCompilation fixtureReference rootArmTarget
    rootArmUnit rfl :=
  cyclicContextFrameCompilation fixtureReference spatial_simpleBonded rootArmTarget
    rootArmCursor_real rootArmUnit rfl

theorem rootArmUnit_atom : rootArmUnit.1.atom = SA ⟨2, by decide⟩ := by
  change (symmetricCertified.molecularFrameUnit
    (rootFrames.frame.cursorAt rootArmSlot).occurrence.1).atom = SA ⟨2, by decide⟩
  have cursorEq := LocalizedCyclicRootArmReachability.rootSlot_eq_canonicalLigandCursor
    spatial_simpleBonded rootFrames rfl root_provenance_real rootArmSlot
  have unitEq := congrArg (fun cursor : symmetricCertified.LocalizedRerootCursor
      (carrierFuel fixtureReference) =>
        (symmetricCertified.molecularFrameUnit cursor.occurrence.1).atom) cursorEq
  let canonicalIndex := symmetricCertified.canonicalLigandReindex rootFrames.center
    (rootFrames.detectedLigandPermutation rootArmSlot)
  have ligandEq : symmetricCertified.canonicalLigandAtom rootFrames.center canonicalIndex =
      SA ⟨2, by decide⟩ := by
    calc
      symmetricCertified.canonicalLigandAtom rootFrames.center canonicalIndex =
          symmetricCertified.detectedMultiCenterMolecule.ligandAtomAt rootFrames.center
            (rootFrames.detectedLigandPermutation rootArmSlot) :=
        (symmetricCertified.canonicalLigandReindex_spec rootFrames.center
          (rootFrames.detectedLigandPermutation rootArmSlot)).symm
      _ = rootFrames.actualLigandAtoms rootArmSlot := rfl
      _ = SA ⟨2, by decide⟩ := rootArmSlot_atom
  have unitAtom : (symmetricCertified.molecularFrameUnit
      (symmetricCertified.localizedLigandRootCursor rootFrames.center canonicalIndex).occurrence.1).atom =
      symmetricCertified.canonicalLigandAtom rootFrames.center canonicalIndex := by
    simp [CertifiedLocalizedCIPInput.localizedLigandRootCursor,
      CertifiedLocalizedCIPInput.localizedLigandRootNode,
      CertifiedLocalizedCIPInput.molecularFrameUnit,
      OfficialCIPNode.extend_history, OfficialCIPNode.root]
    rfl
  calc
    (symmetricCertified.molecularFrameUnit
      (rootFrames.frame.cursorAt rootArmSlot).occurrence.1).atom =
        (symmetricCertified.molecularFrameUnit
          (symmetricCertified.localizedLigandRootCursor rootFrames.center canonicalIndex).occurrence.1).atom :=
      unitEq
    _ = symmetricCertified.canonicalLigandAtom rootFrames.center canonicalIndex := unitAtom
    _ = SA ⟨2, by decide⟩ := ligandEq

theorem rootArmContextCenter_ne_root : rootArmContextFrames.center ≠ rootFrames.center := by
  intro same
  have atoms := congrArg Subtype.val same
  rw [rootArmContextFrames.centerEq, rootArmUnit_atom, root_center] at atoms
  simp [SA] at atoms

theorem rootArmCoordinates :
    LocalizedRecursiveAuxiliaryPhysicalDomain.ActualPhysicalCalibratedCoordinates symmetricCertified
      symmetricCertified.detectedMultiCenterMolecule
      LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedCfg rootArmContextFrames.center :=
  LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedCoordinates_at rootArmContextFrames.center

theorem rootArm_actualState_isChiral_of_strict
    (strict : LocalizedCyclicGeneralRigidPriority.FrameConstitutionalStrict
      rootArmContextFrames.frame) :
    ∃ raw : RS, referenceState fixtureReference rootArmTarget = some (.chiral raw) := by
  obtain ⟨pointAt, observed, _volumeNonzero, signEq⟩ := rootArmCoordinates
  let points : Fin 4 → CartesianPoint3 :=
    fun slot => pointAt (rootArmContextFrames.detectedLigandPermutation slot)
  have available := LocalizedCyclicGeneralRigidGeneratedLabels.actualCoordinates_of_calibrated
    rootArmContextFrames pointAt observed
  have sign := LocalizedCyclicGeneralRigidGeneratedLabels.priorityVolume_sign_of_calibrated
    rootArmContextFrames strict spatial_simpleBonded
    LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedCfg pointAt signEq
  have signUnit :
      symmetricCertified.detectedMultiCenterMolecule.configurationSign
          LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedCfg rootArmContextFrames.center *
        permHandedness rootArmContextFrames.detectedLigandPermutation *
        permHandedness (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder
          rootArmContextFrames strict spatial_simpleBonded) = 1 ∨
      symmetricCertified.detectedMultiCenterMolecule.configurationSign
          LocalizedRecursiveCyclicSymmetricFixtureDomain.detectedCfg rootArmContextFrames.center *
        permHandedness rootArmContextFrames.detectedLigandPermutation *
        permHandedness (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder
          rootArmContextFrames strict spatial_simpleBonded) = -1 := by
    rw [← permHandedness_mul, ← permHandedness_mul]
    exact permHandedness_eq_one_or_eq_neg_one _
  have nonzero : reindexedVolume points
      (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder rootArmContextFrames strict
        spatial_simpleBonded) ≠ 0 := by
    intro zero
    have signZero := (rationalVolumeSign_eq_zero_iff _).mpr zero
    change rationalVolumeSign (reindexedVolume points
      (LocalizedCyclicGeneralRigidGeneratedLabels.priorityOrder rootArmContextFrames strict
        spatial_simpleBonded)) = _ at sign
    rw [signZero] at sign
    rcases signUnit with one | negOne
    · rw [one] at sign
      norm_num at sign
    · rw [negOne] at sign
      norm_num at sign
  exact LocalizedCyclicGeneralRigidGeneratedLabels.referenceState_isChiral
    rootArmContextFrames strict spatial_simpleBonded points available nonzero

private theorem rootArmTarget_parent :
    rootArmTarget.1.node.parent? = some (SA ⟨0, by decide⟩) := by
  change (rootFrames.frame.cursorAt rootArmSlot).occurrence.1.node.parent? = _
  rw [LocalizedCyclicRootArmReachability.rootSlot_eq_canonicalLigandCursor
    spatial_simpleBonded rootFrames rfl root_provenance_real rootArmSlot]
  simp [CertifiedLocalizedCIPInput.localizedLigandRootCursor,
    CertifiedLocalizedCIPInput.localizedLigandRootNode,
    OfficialCIPNode.extend, OfficialCIPNode.root, OfficialCIPNode.parent?, root_center]

private theorem actualOutwardCursor_current_atom_range
    (child : symmetricCertified.LocalizedRerootCursor (carrierFuel fixtureReference))
    (childOut : child.occurrence.1 ∈
      symmetricCertified.localizedCarrierOutwardChildFrames
        (fuel := carrierFuel fixtureReference) rootArmTarget.1) :
    ∃ atom : symmetricCertified.Atom,
      child.occurrence.1.node = rootArmTarget.1.node.extend atom 0 ∧
      child.occurrence.1.node.current? = some atom ∧
        (atom = SA ⟨3, by decide⟩ ∨ atom = SA ⟨4, by decide⟩ ∨ atom = SA ⟨6, by decide⟩) := by
  have targetCurrent : rootArmTarget.1.node.current? = some (SA ⟨2, by decide⟩) :=
    rootArmCursor_current
  obtain ⟨w, slot, nodeEq, current, _rootEq, _addressEq, _zip, notParent, adjacent⟩ :=
    symmetricCertified.simpleBond_outwardFrame_extend_zero spatial_simpleBonded
      rootArmTarget targetCurrent rootArmCursor_real child.occurrence.1 childOut
  have nodeCurrent : child.occurrence.1.node.current? = some w := by
    rw [nodeEq]
    simp [OfficialCIPNode.extend]
  have wNotZero : w ≠ SA ⟨0, by decide⟩ := by
    intro same
    rw [same, rootArmTarget_parent] at notParent
    exact notParent rfl
  have graphAdjacent : graph.Adj ⟨2, by decide⟩ w := by
    apply (spatial_adj ⟨2, by decide⟩ w).mp
    simpa [SA_eq] using adjacent
  have neighbor := (adj_arm w).mp graphAdjacent
  rcases neighbor with h | h | h | h
  · exact (wNotZero (by simpa [SA_eq] using h)).elim
  · exact ⟨w, nodeEq, nodeCurrent, Or.inl (by simpa [SA_eq] using h)⟩
  · exact ⟨w, nodeEq, nodeCurrent, Or.inr (Or.inl (by simpa [SA_eq] using h))⟩
  · exact ⟨w, nodeEq, nodeCurrent, Or.inr (Or.inr (by simpa [SA_eq] using h))⟩

private theorem actualOutwardPair_current_atom_range
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair
      symmetricCertified (carrierFuel fixtureReference))
    (targetEq : pair.target = ({ occurrence := rootArmTarget, previous? := none } :
      symmetricCertified.LocalizedRerootCursor (carrierFuel fixtureReference)))
    (side : Bool) :
    ∃ atom : symmetricCertified.Atom,
      (if side then pair.left else pair.right).occurrence.1.node = rootArmTarget.1.node.extend atom 0 ∧
      (if side then pair.left else pair.right).occurrence.1.node.current? = some atom ∧
        (atom = SA ⟨3, by decide⟩ ∨ atom = SA ⟨4, by decide⟩ ∨ atom = SA ⟨6, by decide⟩) := by
  have targetOccurrence : pair.target.occurrence = rootArmTarget := by
    simpa only [rootArmTarget] using congrArg (fun c : symmetricCertified.LocalizedRerootCursor
      (carrierFuel fixtureReference) => c.occurrence) targetEq
  have targetAddress : pair.target.occurrence.1.address = rootArmTarget.1.address :=
    congrArg (fun occurrence : Occurrence fixtureReference => occurrence.1.address) targetOccurrence
  have targetRoot : pair.target.occurrence.1.root = rootArmTarget.1.root :=
    congrArg (fun occurrence : Occurrence fixtureReference => occurrence.1.root) targetOccurrence
  cases side with
  | false =>
      have out : pair.right.occurrence.1 ∈
          symmetricCertified.localizedCarrierOutwardChildFrames
            (fuel := carrierFuel fixtureReference) rootArmTarget.1 := by
        apply (symmetricCertified.mem_localizedCarrierOutwardChildFrames_iff
          rootArmTarget.1 pair.right.occurrence.1).mpr
        refine ⟨pair.right.occurrence.2, ?_, ?_, ?_⟩
        · exact pair.rightRoot.trans targetRoot
        · have h : pair.right.occurrence.1.address = rootArmTarget.1.address ++ [pair.rightSlot] := by
            rw [pair.rightAddress, targetAddress]
          rw [h]
          simp
        · have h : pair.right.occurrence.1.address = rootArmTarget.1.address ++ [pair.rightSlot] := by
            rw [pair.rightAddress, targetAddress]
          rw [h]
          simp
      simpa using actualOutwardCursor_current_atom_range pair.right out
  | true =>
      have out : pair.left.occurrence.1 ∈
          symmetricCertified.localizedCarrierOutwardChildFrames
            (fuel := carrierFuel fixtureReference) rootArmTarget.1 := by
        apply (symmetricCertified.mem_localizedCarrierOutwardChildFrames_iff
          rootArmTarget.1 pair.left.occurrence.1).mpr
        refine ⟨pair.left.occurrence.2, ?_, ?_, ?_⟩
        · exact pair.leftRoot.trans targetRoot
        · have h : pair.left.occurrence.1.address = rootArmTarget.1.address ++ [pair.leftSlot] := by
            rw [pair.leftAddress, targetAddress]
          rw [h]
          simp
        · have h : pair.left.occurrence.1.address = rootArmTarget.1.address ++ [pair.leftSlot] := by
            rw [pair.leftAddress, targetAddress]
          rw [h]
          simp
      simpa using actualOutwardCursor_current_atom_range pair.left out

private theorem actualOutwardPair_separated
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair
      symmetricCertified (carrierFuel fixtureReference))
    (targetEq : pair.target = ({ occurrence := rootArmTarget, previous? := none } :
      symmetricCertified.LocalizedRerootCursor (carrierFuel fixtureReference)))
    (distinct : pair.left ≠ pair.right) :
    LocalizedCyclicGeneralRigidPriority.ConstitutionallySeparated pair.left pair.right := by
  obtain ⟨leftAtom, leftNode, leftCurrent, leftRange⟩ :=
    actualOutwardPair_current_atom_range pair targetEq true
  obtain ⟨rightAtom, rightNode, rightCurrent, rightRange⟩ :=
    actualOutwardPair_current_atom_range pair targetEq false
  simp at leftNode leftCurrent leftRange
  simp at rightNode rightCurrent rightRange
  have atomsDistinct : leftAtom ≠ rightAtom := by
    intro same
    have nodeEq : pair.left.occurrence.1.node = pair.right.occurrence.1.node := by
      rw [leftNode, rightNode, same]
    have cursorEq := LocalizedActualBoundaryObservationReadback.outwardChild_eq_of_node_eq
      symmetricCertified spatial_simpleBonded pair.target pair.left pair.right
      pair.leftPrevious pair.rightPrevious pair.leftRoot pair.rightRoot pair.leftSlot pair.rightSlot
      pair.leftAddress pair.rightAddress nodeEq
    exact distinct cursorEq
  have z3 : graph.atomZ (3 : Fin 9) = 17 :=
    (atomZ_cases (3 : Fin 9)).2.1.mpr (Or.inr (Or.inl rfl))
  have z4 : graph.atomZ (4 : Fin 9) = 6 :=
    (atomZ_cases (4 : Fin 9)).1.mpr (Or.inr (Or.inr rfl))
  have z6 : graph.atomZ (6 : Fin 9) = 1 :=
    (atomZ_cases (6 : Fin 9)).2.2.mpr (Or.inr (Or.inl rfl))
  have atomicNumbersDistinct : graph.atomZ leftAtom ≠ graph.atomZ rightAtom := by
    intro equalZ
    have equalAtom : leftAtom = rightAtom := by
      rcases leftRange with leftThree | leftFour | leftSix <;>
        rcases rightRange with rightThree | rightFour | rightSix
      all_goals
        subst leftAtom
        subst rightAtom
        simp only [SA_eq] at equalZ
        first
        | exact False.elim (atomsDistinct rfl)
        | have contradiction : False := by
            simp only [z3, z4, z6] at equalZ
            norm_num at equalZ
          exact contradiction.elim
    exact atomsDistinct equalAtom
  have leftRootZ := cursorRootAtomicNumber_eq_atomZ_of_current symmetricCertified
    pair.left leftCurrent
  have rightRootZ := cursorRootAtomicNumber_eq_atomZ_of_current symmetricCertified
    pair.right rightCurrent
  apply constitutionallySeparated_of_rootAtomicNumber_ne symmetricCertified
  rw [leftRootZ, rightRootZ]
  exact atomicNumbersDistinct

theorem rootClosingCursor_real :
    (rootFrames.frame.cursorAt rootClosingSlot).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom := by
  rw [LocalizedCyclicRootArmReachability.rootSlot_eq_canonicalLigandCursor
    spatial_simpleBonded rootFrames rfl root_provenance_real rootClosingSlot]
  exact symmetricCertified.localizedLigandRootNode_provenance rootFrames.center
    (symmetricCertified.canonicalLigandReindex rootFrames.center
      (rootFrames.detectedLigandPermutation rootClosingSlot))

theorem rootClosingCursor_current :
    (rootFrames.frame.cursorAt rootClosingSlot).occurrence.1.node.current? =
      some (SA ⟨4, by decide⟩) := by
  rw [rootCursorCurrent_eq_atom rootClosingSlot, rootClosingSlot_atom]


theorem rootArmContextStrict :
    LocalizedCyclicGeneralRigidPriority.FrameConstitutionalStrict
      rootArmContextFrames.frame := by
  let rootCursor : symmetricCertified.LocalizedRerootCursor (carrierFuel fixtureReference) :=
    { occurrence := rootTarget, previous? := none }
  let armCursor := rootFrames.frame.cursorAt rootArmSlot
  let closingCursor := rootFrames.frame.cursorAt rootClosingSlot
  have computed : symmetricCertified.localizedOccurrenceFourLigandFrame? rootTarget =
      some rootFrames.frame :=
    LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed rootFrames
  have armMem := LocalizedCyclicGeneralRigidPriority.frame_cursorAt_mem_executable
    rootTarget rootFrames.frame computed rootArmSlot
  have closingMem := LocalizedCyclicGeneralRigidPriority.frame_cursorAt_mem_executable
    rootTarget rootFrames.frame computed rootClosingSlot
  have armDistinct : armCursor.occurrence ≠ closingCursor.occurrence := by
    intro same
    have currents : armCursor.occurrence.1.node.current? =
        closingCursor.occurrence.1.node.current? :=
      congrArg (fun occurrence : Occurrence fixtureReference => occurrence.1.node.current?) same
    rw [rootArmCursor_current, rootClosingCursor_current] at currents
    exact (by decide : SA (2 : Fin 9) ≠ SA (4 : Fin 9)) (Option.some.inj currents)
  let rootRead := contextOccurrenceRead fixtureReference rootTarget
  have armBuilt : symmetricCertified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a rootRead (2 * (carrierFuel fixtureReference + 1)) armCursor =
      some (rootFrames.stages rootArmSlot).a.key :=
    (symmetricCertified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
      rootRead (2 * (carrierFuel fixtureReference + 1)) armCursor).symm.trans
      (rootFrames.stages rootArmSlot).a.built
  have closingBuilt : symmetricCertified.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a rootRead (2 * (carrierFuel fixtureReference + 1)) closingCursor =
      some (rootFrames.stages rootClosingSlot).a.key :=
    (symmetricCertified.buildRuleMajorCumulativeWithRead?_rule4a_eq_localized
      rootRead (2 * (carrierFuel fixtureReference + 1)) closingCursor).symm.trans
      (rootFrames.stages rootClosingSlot).a.built
  have targetNonroot : rootArmTarget.1.address ≠ [] := by
    have addressEq : rootArmTarget.1.address =
        [symmetricCertified.localizedLigandRootSlot rootFrames.center
          (symmetricCertified.canonicalLigandReindex rootFrames.center
            (rootFrames.detectedLigandPermutation rootArmSlot))] := by
      change (rootFrames.frame.cursorAt rootArmSlot).occurrence.1.address = _
      have cursorEq := LocalizedCyclicRootArmReachability.rootSlot_eq_canonicalLigandCursor
        spatial_simpleBonded rootFrames rfl root_provenance_real rootArmSlot
      have addressEq := congrArg (fun cursor : symmetricCertified.LocalizedRerootCursor
          (carrierFuel fixtureReference) => cursor.occurrence.1.address) cursorEq
      simpa [CertifiedLocalizedCIPInput.localizedLigandRootCursor_address] using addressEq
    intro empty
    rw [addressEq] at empty
    simp at empty
  exact LocalizedCyclicGeneralRigidPriority.frameConstitutionalStrict_of_rootArmRule1aTie
    symmetricCertified spatial_simpleBonded rootCursor rfl armCursor closingCursor armMem
    closingMem armDistinct rootArmCursor_real rootClosingCursor_real rootRead rootRead
    (rootFrames.stages rootArmSlot).a.key (rootFrames.stages rootClosingSlot).a.key
    armBuilt closingBuilt root_arm_rule1a_tie rootArmTarget rootArmCursor_real
    ⟨rfl, List.prefix_rfl⟩ rootArmContextFrames.frame
    (LocalizedCyclicGeneralRigidGeneratedLabels.frame_computed rootArmContextFrames)
    targetNonroot (fun pair pairTarget distinct =>
      actualOutwardPair_separated pair pairTarget distinct)

theorem rootArm_actualState_isChiral :
    ∃ raw : RS, referenceState fixtureReference rootArmTarget = some (.chiral raw) :=
  rootArm_actualState_isChiral_of_strict rootArmContextStrict



end

end TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.actual_rule1a_head
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.actual_rule1a_tie_rootAtomicNumber_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.constitutionallySeparated_of_rootAtomicNumber_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootTarget_fixed_by_rootArmSwap
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArm_transportOccurrence_eq_closing
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmCursor_real
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmCursor_current
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmCursor_isDetected
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextFrames
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmUnit_atom
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextCenter_ne_root
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmCoordinates
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArm_actualState_isChiral_of_strict
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArmContextStrict
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootArm_actualState_isChiral
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootClosingCursor_real
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveCyclicSymmetricFixtureGeneratedLabels.rootClosingCursor_current
