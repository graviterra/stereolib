import TetraStereo.OneCenter.LocalizedRealizedTreeCutIsomorphism
import TetraStereo.OneCenter.LocalizedPhysicalCalibratedRootReader
import TetraStereo.OneCenter.LocalizedActualFrameChildClassification
import TetraStereo.OneCenter.LocalizedOutwardRerootDependencySupport
import TetraStereo.OneCenter.LocalizedActualKeyTiePhysicalTransport
import TetraStereo.MultiCenter.RootedBranchTerminalTwinCompletion
import TetraStereo.KernelOnly

set_option autoImplicit false


























namespace TetraStereo.OneCenter

namespace ActualReaderPhysicalBranchInverse

open CertifiedLocalizedCIPInput

/-! ## The actual final original-root target and its generated dependency reader -/

/-- The actual final target occurrence of the original root carried by a detected center. -/
noncomputable def topTarget (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    LocalizedUniversalReference.Occurrence input :=
  input.certified.localizedFinalOccurrence (LocalizedUniversalReference.carrierFuel input)
    ⟨c.1, c.2⟩

/-- The final target's root is the detected center. -/
theorem topTarget_root (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    (topTarget input c).1.root = c.1 :=
  AuxiliaryContextIntegrity.localizedFinalOccurrence_root input.certified
    (LocalizedUniversalReference.carrierFuel input) ⟨c.1, c.2⟩

/-- The final target sits at the empty address, i.e. it is the original root. -/
theorem topTarget_address (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    (topTarget input c).1.address = [] :=
  AuxiliaryContextIntegrity.localizedFinalOccurrence_address input.certified
    (LocalizedUniversalReference.carrierFuel input) ⟨c.1, c.2⟩

/-- The final target observes exactly the detected center atom. -/
theorem topTarget_node (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    (topTarget input c).1.node = OfficialCIPNode.root c.1 :=
  AuxiliaryContextIntegrity.localizedFinalOccurrence_node input.certified
    (LocalizedUniversalReference.carrierFuel input) ⟨c.1, c.2⟩

/-- The final target's current atom is the detected center atom. -/
theorem topTarget_current (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    (topTarget input c).1.node.current? = some c.1 := by
  rw [topTarget_node]
  rfl

/-- The generated localized dependency reader at the final original-root target.  This is the
actual production reader restricted to strict deeper dependencies of the final target; no read
support or eligibility predicate is assumed. -/
noncomputable def dependencyReader (input : LocalizedUniversalReference.Input)
    (c : input.certified.detectedMultiCenterMolecule.Center) :
    input.certified.LocalizedRerootCursor (LocalizedUniversalReference.carrierFuel input) →
      Option LocalizedAuxiliaryLabel :=
  fun cursor =>
    input.certified.localizedDependencyLabel (topTarget input c)
      (input.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState input) (topTarget input c)) cursor

/-! ## Frame cursors are executable children of the target-start cursor -/

/-- Every cursor of an actual four-ligand frame is an executable child of the target-start cursor
`{ occurrence := target, previous? := none }`.  The frame's declarative zipper expansion identifies
the ordered occurrence frames with the intended cut-neighborhood; the recorded incoming cut is the
target, so attaching the carrier certificate produces this exact cursor. -/
theorem mem_executableLocalizedRerootChildren_of_frame
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ frame.cursors) :
    cursor ∈ input.executableLocalizedRerootChildren
      ({ occurrence := target, previous? := none } : input.LocalizedRerootCursor carrierFuel) := by
  let start : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  have derived :=
    (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target frame).mp computed
  have memIntended : cursor.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames start := by
    rw [← derived.1.1]
    exact List.mem_map.mpr ⟨cursor, present, rfl⟩
  refine List.mem_map.mpr ⟨⟨cursor.occurrence.1, memIntended⟩, by simp, ?_⟩
  apply LocalizedRerootCursor.ext
  · rfl
  · exact (derived.1.2 cursor present).symm

/-- Any cursor of an actual four-ligand frame at the final original-root target is strictly deeper
than that target.  This is the binding that makes the reader eligibility shortcut available: the
target address is empty, and the frame cursor is an uncut carrier child of it. -/
theorem frame_cursor_strictlyDeeper_of_target_address_nil
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (computed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (addressNil : target.1.address = [])
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (present : cursor ∈ frame.cursors) :
    target.1.address.length < cursor.occurrence.1.address.length := by
  let start : input.LocalizedRerootCursor carrierFuel :=
    { occurrence := target, previous? := none }
  have derived :=
    (input.localizedOccurrenceFourLigandFrame?_eq_some_iff target frame).mp computed
  have memIntended : cursor.occurrence.1 ∈
      input.intendedLocalizedRerootChildFrames start := by
    rw [← derived.1.1]
    exact List.mem_map.mpr ⟨cursor, present, rfl⟩
  have neighbor : cursor.occurrence.1 ∈
      input.localizedRerootNeighborFrames (fuel := carrierFuel) target.1 :=
    input.mem_localizedRerootNeighborFrames_of_mem_intended start cursor.occurrence.1 memIntended
  have adjacent :=
    (input.mem_localizedRerootNeighborFrames_iff target.1 cursor.occurrence.1).mp neighbor |>.2
  have targetLength : target.1.address.length = 0 := by simp [addressNil]
  rcases adjacent with ⟨_sameRoot, parent | child⟩
  · omega
  · omega

/-! ## Physical slot indices from atom images -/

/-- A root-fixing automorphism of a multi-center molecule that carries the physical ligand at slot
`i` to the physical ligand at slot `j` carries the slot index `i` to the slot index `j`. -/
theorem ligandPermAt_eq_of_ligandAtomAt_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (e : m.Aut) (c : m.Center) (i j : Fin 4)
    (centerFixed : m.centerPerm e c = c)
    (ligandMaps : (e : Equiv.Perm V) (m.ligandAtomAt c i) = m.ligandAtomAt c j) :
    m.ligandPermAt e c i = j := by
  apply m.ligandAtomAt_injective c
  have h := m.ligandAtomAt_ligandPermAt (e := e) (c := c) i
  rw [centerFixed] at h
  rw [h, ligandMaps]

/-! ## The central physical inverse join -/


















theorem actualReaderPhysicalBranchTransport
    (input : LocalizedUniversalReference.Input)
    (noDouble : input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.certified.moleculeGraph)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (i j : Fin 4) (hij : i ≠ j)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (topTarget input c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index)))
    (tL tR : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input))
    (sourceL : tL.source = frame.cursorAt (alpha.symm i))
    (sourceR : tR.source = frame.cursorAt (alpha.symm j))
    (realizesL : LocalizedCumulativeTreeRealizes input.certified
      (dependencyReader input c) tL)
    (realizesR : LocalizedCumulativeTreeRealizes input.certified
      (dependencyReader input c) tR)
    (hshape : LocalizedCumulativeDecoratedTree.shape tL =
      LocalizedCumulativeDecoratedTree.shape tR)
    (mirror : Bool)
    (labels : ∀ (path : List Nat)
        (nodeL nodeR : LocalizedCumulativeDecoratedTree input.certified
          (LocalizedUniversalReference.carrierFuel input)),
      subtreeAt? tL path = some nodeL →
        subtreeAt? tR path = some nodeR →
          nodeR.label = labelMirror mirror nodeL.label) :
    RootedTetrahedralBranchSymmetry.BranchTransport
      input.certified.detectedMultiCenterMolecule cfg c i j mirror := by
  classical
  let m : MultiCenterMolecule input.certified.Atom := input.certified.detectedMultiCenterMolecule
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input :=
    globalCarrierFuel_adequate input
  have targetCurrent : (topTarget input c).1.node.current? = some c.1 :=
    topTarget_current input c
  have targetAddress : (topTarget input c).1.address = [] :=
    topTarget_address input c
  have hcu : input.certified.moleculeGraph.Adj c.1 (m.ligandAtomAt c i) :=
    m.ligandAtomAt_adj c i
  have hcv : input.certified.moleculeGraph.Adj c.1 (m.ligandAtomAt c j) :=
    m.ligandAtomAt_adj c j
  have huv : m.ligandAtomAt c i ≠ m.ligandAtomAt c j :=
    fun h => hij (m.ligandAtomAt_injective c h)
  have presentL : frame.cursorAt (alpha.symm i) ∈ frame.cursors :=
    List.get_mem frame.cursors _
  have presentR : frame.cursorAt (alpha.symm j) ∈ frame.cursors :=
    List.get_mem frame.cursors _
  have previousEqL : tL.source.previous? = some (topTarget input c) := by
    rw [sourceL]
    exact input.certified.localizedOccurrenceFourLigandFrame_cursor_previous
      (topTarget input c) frame frameComputed (frame.cursorAt (alpha.symm i)) presentL
  have validL : input.certified.LocalizedRerootCursorValid tL.source := by
    rw [sourceL]
    exact input.certified.localizedOccurrenceFourLigandFrame_cursor_valid
      (topTarget input c) frame frameComputed (frame.cursorAt (alpha.symm i)) presentL
  have sameRootL : tL.source.occurrence.1.root = (topTarget input c).1.root := by
    rw [sourceL]
    exact input.certified.localizedOccurrenceFourLigandFrame_cursor_root
      (topTarget input c) frame frameComputed (frame.cursorAt (alpha.symm i)) presentL
  have previousEqR : tR.source.previous? = some (topTarget input c) := by
    rw [sourceR]
    exact input.certified.localizedOccurrenceFourLigandFrame_cursor_previous
      (topTarget input c) frame frameComputed (frame.cursorAt (alpha.symm j)) presentR
  have validR : input.certified.LocalizedRerootCursorValid tR.source := by
    rw [sourceR]
    exact input.certified.localizedOccurrenceFourLigandFrame_cursor_valid
      (topTarget input c) frame frameComputed (frame.cursorAt (alpha.symm j)) presentR
  have sameRootR : tR.source.occurrence.1.root = (topTarget input c).1.root := by
    rw [sourceR]
    exact input.certified.localizedOccurrenceFourLigandFrame_cursor_root
      (topTarget input c) frame frameComputed (frame.cursorAt (alpha.symm j)) presentR
  have oObservedL : tL.source.occurrence.1.node.current? = some (m.ligandAtomAt c i) := by
    rw [sourceL]
    have h := slotSpec (alpha.symm i)
    rw [show alpha (alpha.symm i) = i from Equiv.apply_symm_apply alpha i] at h
    exact h
  have oObservedR : tR.source.occurrence.1.node.current? = some (m.ligandAtomAt c j) := by
    rw [sourceR]
    have h := slotSpec (alpha.symm j)
    rw [show alpha (alpha.symm j) = j from Equiv.apply_symm_apply alpha j] at h
    exact h
  let φ : AcyclicCutBranchAutomorphism.RootedCutBranchIso input.certified.moleculeGraph
      c.1 (m.ligandAtomAt c i) (m.ligandAtomAt c j) :=
    rootedCutBranchIso_of_shapeMatch (input := input.certified)
      (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      (singleBonded := singleBonded) (acyclic := acyclic)
      enough hshape realizesL realizesR previousEqL validL sameRootL
      previousEqR validR sameRootR oObservedL targetCurrent oObservedR targetCurrent hcu hcv
  let e : m.Aut :=
    AcyclicCutBranchAutomorphism.detectedCutBranchSwapAut input.certified.moleculeGraph c.1
      (m.ligandAtomAt c i) (m.ligandAtomAt c j) acyclic hcu hcv huv singleBonded charge φ
  have physicalFix : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 := by
    have h := AcyclicCutBranchAutomorphism.detectedCutBranchSwapAut_apply_center
      input.certified.moleculeGraph c.1 (m.ligandAtomAt c i) (m.ligandAtomAt c j)
      acyclic hcu hcv huv singleBonded charge φ
    simpa [e] using h
  have centerFixed : m.centerPerm e c = c :=
    (RootedTetrahedralBranchSymmetry.centerPerm_eq_iff m e c).mpr physicalFix
  have physicalImage : (e : Equiv.Perm input.certified.Atom) (m.ligandAtomAt c i) =
      m.ligandAtomAt c j := by
    have h := AcyclicCutBranchAutomorphism.cutBranchSwap_apply_left
      input.certified.moleculeGraph c.1 (m.ligandAtomAt c i) (m.ligandAtomAt c j)
      acyclic hcu hcv huv φ
    simpa [e, AcyclicCutBranchAutomorphism.detectedCutBranchSwapAut_apply] using h
  refine (RootedBranchTerminalTwinCompletion.branchTransport_iff_orientationAtNonTwinCenters
    m cfg c i j mirror).mpr ⟨e, centerFixed, ?_, ?_⟩
  · exact ligandPermAt_eq_of_ligandAtomAt_eq m e c i j centerFixed physicalImage
  · intro d branch notTwin
    have hd : d.1 ∈ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph
        c.1 (m.ligandAtomAt c i) :=
      (AcyclicCutBranchAutomorphism.ligandBranchReaches_iff_cutBranchReaches m c i d.1).mp branch
    obtain ⟨p, pAtom⟩ := exists_position_of_mem_cutBranch (input := input.certified)
      (carrierFuel := LocalizedUniversalReference.carrierFuel input)
      (read := dependencyReader input c) (tree := tL)
      (oAtom := m.ligandAtomAt c i) (pAtom := c.1) (w := d.1)
      singleBonded acyclic enough realizesL (topTarget input c) previousEqL validL sameRootL
      oObservedL targetCurrent hcu hd
    let q : Position tR := shapePositionEquiv hshape p
    have subtreeR : subtreeAt? tR p.val = some (positionNode q) := by
      have h := positionNode_spec q
      simpa [q] using h
    have labelL : (positionNode p).label = dependencyReader input c (positionSource p) :=
      positionNode_label_eq_read realizesL p
    have labelR : (positionNode q).label = dependencyReader input c (positionSource q) :=
      positionNode_label_eq_read realizesR q
    have labelRel : (positionNode q).label = labelMirror mirror (positionNode p).label :=
      labels p.val (positionNode p) (positionNode q) (positionNode_spec p) subtreeR
    have hswap : (e : Equiv.Perm input.certified.Atom)
          (positionAtom singleBonded acyclic p) =
        positionAtom singleBonded acyclic q := by
      have h := rootedCutBranchIso_of_shapeMatch_swap_apply (input := input.certified)
        (carrierFuel := LocalizedUniversalReference.carrierFuel input)
        (singleBonded := singleBonded) (acyclic := acyclic)
        (readL := dependencyReader input c) (readR := dependencyReader input c)
        (tL := tL) (tR := tR) (previousL := topTarget input c) (previousR := topTarget input c)
        enough hshape realizesL realizesR previousEqL validL sameRootL
        previousEqR validR sameRootR oObservedL targetCurrent oObservedR targetCurrent
        hcu hcv acyclic huv singleBonded charge p
      simpa [e, q, AcyclicCutBranchAutomorphism.detectedCutBranchSwapAut_apply] using h
    have qAtom : positionAtom singleBonded acyclic q = (m.centerPerm e d).1 := by
      rw [← hswap, pAtom]
      rfl
    have pCurrent : (positionSource p).occurrence.1.node.current? = some d.1 := by
      have h := positionAtom_spec singleBonded acyclic p
      rw [pAtom] at h
      exact h
    have qCurrent : (positionSource q).occurrence.1.node.current? =
        some (m.centerPerm e d).1 := by
      have h := positionAtom_spec singleBonded acyclic q
      rw [qAtom] at h
      exact h
    have reachable : input.certified.ActualChildReachable tL.source (positionSource p) :=
      actualChildReachable_positionSource realizesL p
    have reachableStart : input.certified.ActualChildReachable
        (frame.cursorAt (alpha.symm i)) (positionSource p) := by
      rw [sourceL] at reachable
      exact reachable
    have firstChild : frame.cursorAt (alpha.symm i) ∈
        input.certified.executableLocalizedRerootChildren
          ({ occurrence := topTarget input c, previous? := none } :
            input.certified.LocalizedRerootCursor
              (LocalizedUniversalReference.carrierFuel input)) :=
      mem_executableLocalizedRerootChildren_of_frame input.certified (topTarget input c) frame
        frameComputed (frame.cursorAt (alpha.symm i)) presentL
    have firstDeeper : (topTarget input c).1.address.length <
        (frame.cursorAt (alpha.symm i)).occurrence.1.address.length :=
      frame_cursor_strictlyDeeper_of_target_address_nil input.certified (topTarget input c) frame
        frameComputed targetAddress (frame.cursorAt (alpha.symm i)) presentL
    have readEqL : dependencyReader input c (positionSource p) =
        LocalizedUniversalReference.referenceState input (positionSource p).occurrence := by
      have h := outward_reachable_dependencyLabel_eq_state input.certified (topTarget input c)
        (LocalizedUniversalReference.referenceState input)
        (frame.cursorAt (alpha.symm i)) (positionSource p) firstChild firstDeeper reachableStart
      simpa [dependencyReader] using h
    have readEqR : dependencyReader input c (positionSource q) =
        LocalizedUniversalReference.referenceState input (positionSource q).occurrence := by
      have reachableR : input.certified.ActualChildReachable tR.source (positionSource q) :=
        actualChildReachable_positionSource realizesR q
      have reachableStartR : input.certified.ActualChildReachable
          (frame.cursorAt (alpha.symm j)) (positionSource q) := by
        rw [sourceR] at reachableR
        exact reachableR
      have firstChildR : frame.cursorAt (alpha.symm j) ∈
          input.certified.executableLocalizedRerootChildren
            ({ occurrence := topTarget input c, previous? := none } :
              input.certified.LocalizedRerootCursor
                (LocalizedUniversalReference.carrierFuel input)) :=
        mem_executableLocalizedRerootChildren_of_frame input.certified (topTarget input c) frame
          frameComputed (frame.cursorAt (alpha.symm j)) presentR
      have firstDeeperR : (topTarget input c).1.address.length <
          (frame.cursorAt (alpha.symm j)).occurrence.1.address.length :=
        frame_cursor_strictlyDeeper_of_target_address_nil input.certified (topTarget input c) frame
          frameComputed targetAddress (frame.cursorAt (alpha.symm j)) presentR
      have h := outward_reachable_dependencyLabel_eq_state input.certified (topTarget input c)
        (LocalizedUniversalReference.referenceState input)
        (frame.cursorAt (alpha.symm j)) (positionSource q) firstChildR firstDeeperR reachableStartR
      simpa [dependencyReader] using h
    have stateRel : LocalizedUniversalReference.referenceState input (positionSource q).occurrence =
        (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
          (LocalizedUniversalReference.referenceState input (positionSource p).occurrence) := by
      calc LocalizedUniversalReference.referenceState input (positionSource q).occurrence
          = dependencyReader input c (positionSource q) := readEqR.symm
        _ = labelMirror mirror (dependencyReader input c (positionSource p)) := by
              rw [← labelR, ← labelL]
              exact labelRel
        _ = (if mirror then CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel else id)
              (LocalizedUniversalReference.referenceState input (positionSource p).occurrence) := by
              simp only [labelMirror_eq_if, readEqL]
              cases mirror <;> rfl
    have d_ne_root : d ≠ c := by
      intro hEq
      exact RootedBranchTerminalTwinCompletion.ligandBranchReaches_ne_root m c i branch
        (congrArg Subtype.val hEq)
    have image_ne_root : m.centerPerm e d ≠ c := by
      intro hEq
      have hval : (e : Equiv.Perm input.certified.Atom) d.1 = c.1 :=
        congrArg Subtype.val hEq
      have hdEq : d.1 = c.1 := (e : Equiv.Perm input.certified.Atom).injective
        (hval.trans physicalFix.symm)
      exact d_ne_root (Subtype.ext hdEq)
    have d_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified m d :=
      fun h => notTwin
        ((actualPhysicalTerminalTwinCenter_iff_hasTerminalTwins input.certified m d).mp h)
    have image_notTwin :
        ¬ ActualPhysicalTerminalTwinCenter input.certified m (m.centerPerm e d) :=
      fun h => d_notTwin
        ((actualPhysicalTerminalTwinCenter_centerPerm_iff input.certified m e d).mp h)
    exact (actual_referenceState_automorphism_sign_iff_localSignLaw input noDouble singleBonded
      acyclic m cfg c domain d e mirror d_ne_root image_ne_root d_notTwin image_notTwin
      (positionSource p).occurrence (positionSource q).occurrence pCurrent qCurrent).mp stateRel

assert_kernel_only TetraStereo.OneCenter.ActualReaderPhysicalBranchInverse.topTarget
assert_kernel_only TetraStereo.OneCenter.ActualReaderPhysicalBranchInverse.topTarget_root
assert_kernel_only TetraStereo.OneCenter.ActualReaderPhysicalBranchInverse.topTarget_address
assert_kernel_only TetraStereo.OneCenter.ActualReaderPhysicalBranchInverse.topTarget_node
assert_kernel_only TetraStereo.OneCenter.ActualReaderPhysicalBranchInverse.topTarget_current
assert_kernel_only TetraStereo.OneCenter.ActualReaderPhysicalBranchInverse.dependencyReader
assert_kernel_only TetraStereo.OneCenter.ActualReaderPhysicalBranchInverse.mem_executableLocalizedRerootChildren_of_frame
assert_kernel_only TetraStereo.OneCenter.ActualReaderPhysicalBranchInverse.frame_cursor_strictlyDeeper_of_target_address_nil
assert_kernel_only TetraStereo.OneCenter.ActualReaderPhysicalBranchInverse.ligandPermAt_eq_of_ligandAtomAt_eq
assert_kernel_only TetraStereo.OneCenter.ActualReaderPhysicalBranchInverse.actualReaderPhysicalBranchTransport

end ActualReaderPhysicalBranchInverse

end TetraStereo.OneCenter
