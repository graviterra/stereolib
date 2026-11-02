import TetraStereo.OneCenter.LocalizedCumulativeCursorTransport
import TetraStereo.OneCenter.LocalizedAcyclicAutomorphismCursorTransport
import TetraStereo.OneCenter.LocalizedAcyclicGeneralCutCorrespondence
import TetraStereo.OneCenter.LocalizedAcyclicFourLigandFrameCompleteness
import TetraStereo.OneCenter.LocalizedPhysicalTerminalTwinOutwardDomain
import TetraStereo.OneCenter.LocalizedPhysicalSparseRootReader
import TetraStereo.OneCenter.LocalizedPhysicalCalibratedRootReader
import TetraStereo.OneCenter.LocalizedRootZLabelSignEquivalence
import TetraStereo.OneCenter.LocalizedPhysicalLeafModelNone
import TetraStereo.OneCenter.LocalizedNoDoubleWholeStateRule45Bridge
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false










































namespace TetraStereo.OneCenter

open RootedTetrahedralBranchSymmetry

namespace CertifiedLocalizedCIPInput





noncomputable def graphAutOfMultiCenterAut
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom)
    (graphEq : m.mol = input.moleculeGraph)
    (e : m.Aut) : input.moleculeGraph.Aut :=
  ⟨(e : Equiv.Perm input.Atom), by
    rw [← graphEq]
    exact e.property.1⟩

/-- The atom permutation underlying `graphAutOfMultiCenterAut` is the physical one. -/
@[simp] theorem coe_graphAutOfMultiCenterAut
    (input : CertifiedLocalizedCIPInput)
    (m : MultiCenterMolecule input.Atom)
    (graphEq : m.mol = input.moleculeGraph)
    (e : m.Aut) :
    (graphAutOfMultiCenterAut input m graphEq e : Equiv.Perm input.Atom) =
      (e : Equiv.Perm input.Atom) := rfl

/-! ## The actual physical-branch relation on reroot cursors -/







def LocalizedPhysicalBranchRelation
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (e : input.moleculeGraph.Aut) (root : input.Atom)
    (startL startR : input.LocalizedRerootCursor carrierFuel)
    (x y : input.LocalizedRerootCursor carrierFuel) : Prop :=
  LocalizedAutCursorCorrespondence input e root x y ∧
    input.ActualChildReachable startL x ∧
      input.ActualChildReachable startR y

/-- Projection of the physical-branch relation to the physical automorphism correspondence. -/
theorem localizedPhysicalBranchRelation_correspondence
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    {startL startR x y : input.LocalizedRerootCursor carrierFuel}
    (related : LocalizedPhysicalBranchRelation input e root startL startR x y) :
    LocalizedAutCursorCorrespondence input e root x y :=
  related.1

/-- Projection of the physical-branch relation to left actual reachability. -/
theorem localizedPhysicalBranchRelation_reachable_left
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    {startL startR x y : input.LocalizedRerootCursor carrierFuel}
    (related : LocalizedPhysicalBranchRelation input e root startL startR x y) :
    input.ActualChildReachable startL x :=
  related.2.1

/-- Projection of the physical-branch relation to right actual reachability. -/
theorem localizedPhysicalBranchRelation_reachable_right
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    {startL startR x y : input.LocalizedRerootCursor carrierFuel}
    (related : LocalizedPhysicalBranchRelation input e root startL startR x y) :
    input.ActualChildReachable startR y :=
  related.2.2

/-- Every related pair is a pair of actual carrier cursors whose physical current atoms are
related by the automorphism. -/
theorem localizedPhysicalBranchRelation_current_atoms
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    {startL startR x y : input.LocalizedRerootCursor carrierFuel}
    (related : LocalizedPhysicalBranchRelation input e root startL startR x y)
    {a b : input.Atom}
    (xCurrent : x.occurrence.1.node.current? = some a)
    (yCurrent : y.occurrence.1.node.current? = some b) :
    b = (e : Equiv.Perm input.Atom) a :=
  related.1.current_maps xCurrent yCurrent

/-! ## Structural clause (1): official atom-label covariance -/

/-- **Official atom-label clause.**  Related actual cursors have equal official node atom labels.
Both occurrences are real path nodes of the certified acyclic single-bond graph, so the official
label is the raw CIP label of the current atom, and the physical automorphism preserves atomic
number and mass. -/
theorem localizedPhysicalBranchRelation_atomLabel
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat} {e : input.moleculeGraph.Aut} {root : input.Atom}
    {startL startR x y : input.LocalizedRerootCursor carrierFuel}
    (related : LocalizedPhysicalBranchRelation input e root startL startR x y) :
    input.moleculeGraph.officialNodeAtomLabel x.occurrence.1.node =
      input.moleculeGraph.officialNodeAtomLabel y.occurrence.1.node := by
  obtain ⟨a, xCurrent⟩ := input.occurrence_current_exists x.occurrence
  obtain ⟨b, yCurrent⟩ := input.occurrence_current_exists y.occurrence
  exact input.officialNodeAtomLabel_eq_of_correspondence singleBonded acyclic
    related.1 xCurrent yCurrent

/-! ## Structural clause (2): stored Rule-1b root-distance covariance -/

/-- **Stored Rule-1b root-distance clause.**  Related actual cursors have equal stored
`rule1bRootDistance`.  The physical automorphism fixes the original root, so the mapped actual
simple path and the target actual simple path coincide by acyclicity, giving equal stored history
lengths and hence equal root distances. -/
theorem localizedPhysicalBranchRelation_rootDistance
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat} {e : input.moleculeGraph.Aut} {root : input.Atom}
    (rootFixed : (e : Equiv.Perm input.Atom) root = root)
    {startL startR x y : input.LocalizedRerootCursor carrierFuel}
    (related : LocalizedPhysicalBranchRelation input e root startL startR x y) :
    x.occurrence.1.node.rule1bRootDistance =
      y.occurrence.1.node.rule1bRootDistance := by
  obtain ⟨a, xCurrent⟩ := input.occurrence_current_exists x.occurrence
  obtain ⟨b, yCurrent⟩ := input.occurrence_current_exists y.occurrence
  exact input.rule1bRootDistance_eq_of_correspondence singleBonded acyclic rootFixed
    related.1 xCurrent yCurrent

/-! ## Structural clause (3): actual child-list correspondence -/

/-- Membership upgrade for `List.Forall₂`: if a pointwise relation can be strengthened using only
membership in the two lists, then the strengthened relation is also `List.Forall₂`. -/
theorem forall₂_of_mem_imp
    {α β : Type*} {R S : α → β → Prop} {left : List α} {right : List β}
    (forall₂ : List.Forall₂ R left right)
    (upgrade : ∀ a ∈ left, ∀ b ∈ right, R a b → S a b) :
    List.Forall₂ S left right := by
  induction forall₂ with
  | nil => exact List.Forall₂.nil
  | cons head tail inductionHypothesis =>
      refine List.Forall₂.cons ?_ ?_
      · exact upgrade _ List.mem_cons_self _ List.mem_cons_self head
      · exact inductionHypothesis (fun a aMem b bMem =>
          upgrade a (List.mem_cons_of_mem _ aMem) b (List.mem_cons_of_mem _ bMem))











theorem localizedPhysicalBranchRelation_children
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {e : input.moleculeGraph.Aut} {root : input.Atom}
    {startL startR x y : input.LocalizedRerootCursor carrierFuel}
    (related : LocalizedPhysicalBranchRelation input e root startL startR x y) :
    ∃ relatedChildren,
      (input.executableLocalizedRerootChildren x).Perm relatedChildren ∧
        List.Forall₂ (LocalizedPhysicalBranchRelation input e root startL startR)
          relatedChildren (input.executableLocalizedRerootChildren y) := by
  classical
  let sourceChildren := input.executableLocalizedRerootChildren x
  let targetChildren := input.executableLocalizedRerootChildren y
  have sourceComputed : input.localizedRerootChildren? x = some sourceChildren :=
    input.localizedRerootChildren?_eq_some_executable x
  have targetComputed : input.localizedRerootChildren? y = some targetChildren :=
    input.localizedRerootChildren?_eq_some_executable y
  obtain ⟨image, imagePerm, forall₂Correspondence⟩ :=
    input.exists_permuted_children_forall₂_of_correspondence singleBonded acyclic enough
      related.1 sourceComputed targetComputed
  -- Upgrade the pointwise correspondence to the full physical-branch relation.  A source child
  -- is reached by one actual executable step from the left parent; a target child is reached by
  -- one actual executable step from the right parent.
  have forall₂Relation :
      List.Forall₂ (LocalizedPhysicalBranchRelation input e root startL startR)
        sourceChildren image := by
    refine forall₂_of_mem_imp (R := LocalizedAutCursorCorrespondence input e root)
      (S := LocalizedPhysicalBranchRelation input e root startL startR) forall₂Correspondence ?_
    intro sourceChild sourceMem targetChild targetMem correspondence
    have sourceEdge : E input x sourceChild := sourceMem
    have targetEdge : E input y targetChild := by
      have targetMem' : targetChild ∈ targetChildren :=
        (imagePerm.mem_iff).mp targetMem
      exact targetMem'
    exact ⟨correspondence,
      Relation.ReflTransGen.tail related.2.1 sourceEdge,
      Relation.ReflTransGen.tail related.2.2 targetEdge⟩

  have composed : Relation.Comp
      (List.Forall₂ (LocalizedPhysicalBranchRelation input e root startL startR))
      List.Perm sourceChildren targetChildren :=
    ⟨image, forall₂Relation, imagePerm⟩
  have reoriented : Relation.Comp List.Perm
      (List.Forall₂ (LocalizedPhysicalBranchRelation input e root startL startR))
      sourceChildren targetChildren := by
    rw [← List.forall₂_comp_perm_eq_perm_comp_forall₂]
    exact composed
  obtain ⟨relatedChildren, permutation, forall₂⟩ := reoriented
  exact ⟨relatedChildren, permutation, forall₂⟩


















structure LocalizedPhysicalTwinData
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence carrierFuel)
    (centerAtom leftAtom rightAtom : input.Atom) : Prop where
  center_at : occurrence.1.node.current? = some centerAtom
  tetrahedral : input.moleculeGraph.IsTetrahedralCenter centerAtom
  leftNeighbors : input.moleculeGraph.neighborFinset leftAtom = {centerAtom}
  rightNeighbors : input.moleculeGraph.neighborFinset rightAtom = {centerAtom}
  left_ne : leftAtom ≠ rightAtom
  root_ne_left : occurrence.1.root ≠ leftAtom
  root_ne_right : occurrence.1.root ≠ rightAtom
  z_eq : input.moleculeGraph.atomZ leftAtom = input.moleculeGraph.atomZ rightAtom
  mass_eq : input.moleculeGraph.atomMass leftAtom = input.moleculeGraph.atomMass rightAtom






structure LocalizedPhysicalCalibratedData
    (input : LocalizedUniversalReference.Input)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    {carrierFuel : Nat}
    (occurrence : input.certified.LocalizedCIPOccurrence carrierFuel)
    (center : m.Center) : Prop where
  center_at : occurrence.1.node.current? = some center.1
  separated : ∀ frame,
    input.certified.localizedOccurrenceFourLigandFrame? occurrence = some frame →
      input.certified.ConstitutionallyAtomicNumberSeparatedFrame frame
  coordinates : ∀ frame,
    input.certified.localizedOccurrenceFourLigandFrame? occurrence = some frame →
      ∃ (alpha : Equiv.Perm (Fin 4)) (points : Fin 4 → CartesianPoint3),
        (∀ index, (frame.cursorAt index).occurrence.1.node.current? =
          some (m.ligandAtomAt center (alpha index))) ∧
        (∀ index, input.certified.localizedRerootCursorSpatialPoint?
          (frame.cursorAt index) = some (points index)) ∧
        Nonempty (PhysicalFrameCalibration m cfg center alpha points)

/-- The strong physical domain at a pair of actual cursors: either both current atoms are
non-candidates, or both occurrences have physical terminal-twin data, or both have calibrated
root-`Z`-rigid data at physical centers.  The calibration data at the two sides are independent
frame-level facts; their center compatibility is derived from the automorphism correspondence in
the reader theorem below. -/
def LocalizedPhysicalPairCase
    (input : LocalizedUniversalReference.Input)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (e : m.Aut)
    {carrierFuel : Nat}
    (x y : input.certified.LocalizedRerootCursor carrierFuel) : Prop :=
  (∃ xAtom yAtom,
      x.occurrence.1.node.current? = some xAtom ∧
      y.occurrence.1.node.current? = some yAtom ∧
      xAtom ∉ input.certified.tetrahedralCenterSet ∧
      yAtom ∉ input.certified.tetrahedralCenterSet) ∨
    (∃ xAtom xLeft xRight yAtom yLeft yRight,
      LocalizedPhysicalTwinData input.certified x.occurrence xAtom xLeft xRight ∧
      LocalizedPhysicalTwinData input.certified y.occurrence yAtom yLeft yRight) ∨
      (∃ xCenter yCenter,
        LocalizedPhysicalCalibratedData input m cfg x.occurrence xCenter ∧
        LocalizedPhysicalCalibratedData input m cfg y.occurrence yCenter)

/-! ## Actual dependency reads -/

/-- The actual reference dependency read at a cursor of the target equals the generated reference
state at that cursor's occurrence, whenever the cursor is a strict depth dependency of the
target. -/
theorem localizedReferenceDependencyLabel_eq_state
    (input : LocalizedUniversalReference.Input)
    (target : LocalizedUniversalReference.Occurrence input)
    (cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (dependency : input.certified.LocalizedDepthDependency cursor.occurrence target) :
    input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) cursor =
      LocalizedUniversalReference.referenceState input cursor.occurrence := by
  simp only [CertifiedLocalizedCIPInput.localizedDependencyLabel,
    CertifiedLocalizedCIPInput.localizedDependencyView, dependency, dif_pos]

/-! ## Reader covariance derived from the physical domain -/












theorem localizedPhysicalBranchRelation_referenceState
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (cfg : m.Configuration) (c : m.Center) (e : m.Aut) (mirror : Bool)
    (i j : Fin 4)
    (signLaw : ∀ d : m.Center, LigandBranchReaches m c i d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d))
    {startL startR : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    {x y : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    (related : LocalizedPhysicalBranchRelation input.certified
      (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR x y)
    (pairCase : LocalizedPhysicalPairCase input m cfg e x y)
    (branchAtLeft : ∀ d : m.Center,
      LocalizedPhysicalCalibratedData input m cfg x.occurrence d →
        LigandBranchReaches m c i d.1) :
    LocalizedUniversalReference.referenceState input y.occurrence =
      (if mirror then reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input x.occurrence) := by
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    dsimp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel, LocalizedReference.carrierFuel,
      LocalizedReference.Input.molecule]
    omega
  rcases pairCase with
    ⟨xAtom, yAtom, xCurrent, yCurrent, xNotMem, yNotMem⟩ |
    ⟨xAtom, xLeft, xRight, yAtom, yLeft, yRight, xTwin, yTwin⟩ |
    ⟨xCenter, yCenter, xCalibrated, yCalibrated⟩
  · -- Non-candidates: both occurrences read `none`.
    have model :=
      LocalizedUniversalReference.referenceState_bareRule45CIPModel_of_noDoubleRecords
        input noDouble
    have xNone :=
      input.certified.localizedOccurrenceRule45CIPModel_eq_none_of_current_not_mem
        x.occurrence xAtom xCurrent xNotMem model
    have yNone :=
      input.certified.localizedOccurrenceRule45CIPModel_eq_none_of_current_not_mem
        y.occurrence yAtom yCurrent yNotMem model
    rw [xNone, yNone]
    cases mirror <;>
      simp [CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel]
  ·
    have xNone :=
      referenceState_eq_none_of_physical_terminalTwinLeaves
        input singleBonded acyclic noDouble x.occurrence xAtom xLeft xRight
        xTwin.center_at xTwin.tetrahedral xTwin.leftNeighbors xTwin.rightNeighbors
        xTwin.left_ne xTwin.root_ne_left xTwin.root_ne_right xTwin.z_eq xTwin.mass_eq
    have yNone :=
      referenceState_eq_none_of_physical_terminalTwinLeaves
        input singleBonded acyclic noDouble y.occurrence yAtom yLeft yRight
        yTwin.center_at yTwin.tetrahedral yTwin.leftNeighbors yTwin.rightNeighbors
        yTwin.left_ne yTwin.root_ne_left yTwin.root_ne_right yTwin.z_eq yTwin.mass_eq
    rw [xNone, yNone]
    cases mirror <;>
      simp [CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel]
  ·
    have xCurrent : x.occurrence.1.node.current? = some xCenter.1 := xCalibrated.center_at
    have yCurrent : y.occurrence.1.node.current? = some yCenter.1 := yCalibrated.center_at
    have centerEq : yCenter = m.centerPerm e xCenter := by
      apply Subtype.ext
      have mapped : yCenter.1 = (e : Equiv.Perm input.certified.Atom) xCenter.1 := by
        simpa [graphAutOfMultiCenterAut] using
          related.1.current_maps xCurrent yCurrent
      exact mapped
    subst centerEq
    -- Actual four-ligand frames at the two occurrences, from the physical degree data.
    obtain ⟨F, _alphaF, frameF, _slotF⟩ :=
      input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation
        singleBonded acyclic enough x.occurrence (oAtom := xCenter.1)
        xCalibrated.center_at m graphEq xCenter rfl
    obtain ⟨G, _alphaG, frameG, _slotG⟩ :=
      input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation
        singleBonded acyclic enough y.occurrence (oAtom := (m.centerPerm e xCenter).1)
        yCalibrated.center_at m graphEq (m.centerPerm e xCenter) rfl
    -- The frame-level physical data at each side.
    obtain ⟨alphaF, pointsF, slotF, spatialF, calibrationF⟩ :=
      xCalibrated.coordinates F frameF
    obtain ⟨alphaG, pointsG, slotG, spatialG, calibrationG⟩ :=
      yCalibrated.coordinates G frameG
    have derivedF :=
      input.certified.localizedOccurrenceFourLigandFrame?_sound x.occurrence F frameF
    have derivedG :=
      input.certified.localizedOccurrenceFourLigandFrame?_sound y.occurrence G frameG
    have separatedF := xCalibrated.separated F frameF
    have separatedG := yCalibrated.separated G frameG
    -- Detected tetrahedral centers of the certified graph at the two physical centers.
    let centerF : input.certified.TetrahedralCenter :=
      ⟨xCenter.1,
        (input.certified.moleculeGraph.mem_tetrahedralCenterSet xCenter.1).mpr
          (input.certified.isTetrahedralCenter_of_physicalLigandEquiv m graphEq xCenter)⟩
    let centerU : input.certified.TetrahedralCenter :=
      ⟨(m.centerPerm e xCenter).1,
        (input.certified.moleculeGraph.mem_tetrahedralCenterSet
          (m.centerPerm e xCenter).1).mpr
          (input.certified.isTetrahedralCenter_of_physicalLigandEquiv m graphEq
            (m.centerPerm e xCenter))⟩
    have centerRealF :
        input.certified.RealTetrahedralCenterNode x.occurrence.1.node centerF :=
      ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic x.occurrence,
        by simpa [centerF] using xCalibrated.center_at⟩
    have centerRealU :
        input.certified.RealTetrahedralCenterNode y.occurrence.1.node centerU :=
      ⟨input.certified.carrierOccurrence_provenance_real singleBonded acyclic y.occurrence,
        by simpa [centerU] using yCalibrated.center_at⟩
    have centerF_at : centerF.1 = xCenter.1 := rfl
    have centerU_at : centerU.1 = (m.centerPerm e xCenter).1 := rfl
    have matchF : ActualFrameLigandMatch input m F xCenter alphaF :=
      { real := fun index =>
          input.certified.carrierOccurrence_provenance_real singleBonded acyclic
            (F.cursorAt index).occurrence
        atom := slotF }
    have matchG : ActualFrameLigandMatch input m G (m.centerPerm e xCenter) alphaG :=
      { real := fun index =>
          input.certified.carrierOccurrence_provenance_real singleBonded acyclic
            (G.cursorAt index).occurrence
        atom := slotG }
    have physicalSign := signLaw xCenter (branchAtLeft xCenter xCalibrated)
    exact (referenceState_rootZAutomorphism_label_sign_iff
      input noDouble m graphEq cfg xCenter e mirror x.occurrence y.occurrence
      F G derivedF derivedG separatedF separatedG centerF centerU
      centerRealF centerRealU centerF_at centerU_at alphaF alphaG matchF matchG
      pointsF pointsG spatialF spatialG
      (Classical.choice calibrationF) (Classical.choice calibrationG)).2 physicalSign

/-- **Actual dependency-label transport.**  Under the same physical domain and branch sign law,
the actual production dependency read at the right cursor is the uppercase reflection (when
`mirror`) of the actual production dependency read at the left cursor, provided both cursors are
strict depth dependencies of the target.  The reader relation is derived, not assumed. -/
theorem localizedPhysicalBranchRelation_reader_transport
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (cfg : m.Configuration) (c : m.Center) (e : m.Aut) (mirror : Bool)
    (i j : Fin 4)
    (signLaw : ∀ d : m.Center, LigandBranchReaches m c i d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d))
    {target : LocalizedUniversalReference.Occurrence input}
    {startL startR : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    {x y : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    (related : LocalizedPhysicalBranchRelation input.certified
      (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR x y)
    (xDependency : input.certified.LocalizedDepthDependency x.occurrence target)
    (yDependency : input.certified.LocalizedDepthDependency y.occurrence target)
    (pairCase : LocalizedPhysicalPairCase input m cfg e x y)
    (branchAtLeft : ∀ d : m.Center,
      LocalizedPhysicalCalibratedData input m cfg x.occurrence d →
        LigandBranchReaches m c i d.1) :
    input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) y =
      (if mirror then reflectUppercaseOptionalLabel else id)
        (input.certified.localizedDependencyLabel target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) x) := by
  rw [localizedReferenceDependencyLabel_eq_state input target x xDependency,
    localizedReferenceDependencyLabel_eq_state input target y yDependency]
  exact localizedPhysicalBranchRelation_referenceState
    input singleBonded acyclic noDouble m graphEq cfg c e mirror i j signLaw
    related pairCase branchAtLeft










/-- Carrier occurrences have node-history length exactly one more than their address length. -/
theorem carrierOccurrence_history_length_eq_address_length
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (occurrence : input.LocalizedCIPOccurrence fuel) :
    occurrence.1.node.history.length = occurrence.1.address.length + 1 := by
  have derived := (input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2
  exact input.declarativeLocalizedOccurrenceSubtree_history_length derived rfl




theorem localizedPhysicalBranchRelation_address_length_eq
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat} {e : input.moleculeGraph.Aut} {root : input.Atom}
    (rootFixed : (e : Equiv.Perm input.Atom) root = root)
    {startL startR x y : input.LocalizedRerootCursor carrierFuel}
    (related : LocalizedPhysicalBranchRelation input e root startL startR x y) :
    x.occurrence.1.address.length = y.occurrence.1.address.length := by
  obtain ⟨a, xCurrent⟩ := input.occurrence_current_exists x.occurrence
  obtain ⟨b, yCurrent⟩ := input.occurrence_current_exists y.occurrence
  have historyEq :
      x.occurrence.1.node.history.length = y.occurrence.1.node.history.length :=
    input.node_history_length_eq_of_correspondence singleBonded acyclic rootFixed
      related.1 xCurrent yCurrent
  have xAlignment :=
    carrierOccurrence_history_length_eq_address_length input x.occurrence
  have yAlignment :=
    carrierOccurrence_history_length_eq_address_length input y.occurrence
  omega

/-- **Dependency eligibility is invariant on the selected physical branch.**  If the target keeps
the same original root as the branch, then one cursor is a strict depth dependency of the target
exactly when the other is. -/
theorem localizedPhysicalBranchRelation_dependency_iff
    (input : CertifiedLocalizedCIPInput)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat} {e : input.moleculeGraph.Aut} {root : input.Atom}
    (rootFixed : (e : Equiv.Perm input.Atom) root = root)
    {startL startR x y : input.LocalizedRerootCursor carrierFuel}
    (related : LocalizedPhysicalBranchRelation input e root startL startR x y)
    {target : input.LocalizedCIPOccurrence carrierFuel}
    (targetRoot : target.1.root = root) :
    input.LocalizedDepthDependency x.occurrence target ↔
      input.LocalizedDepthDependency y.occurrence target := by
  have addressEq :=
    localizedPhysicalBranchRelation_address_length_eq input singleBonded acyclic
      rootFixed related
  constructor
  · intro dependency
    refine ⟨?_, ?_⟩
    · rw [related.1.target_root, targetRoot]
    · rw [← addressEq]
      exact dependency.2
  · intro dependency
    refine ⟨?_, ?_⟩
    · rw [related.1.source_root, targetRoot]
    · rw [addressEq]
      exact dependency.2

/-! ## Actual root-priority covariance on the selected physical branch -/

/-- **Derived actual reader relation on the selected physical branch.**  For every pair of related
actual cursors, the actual production dependency read at the target on the right is the (uppercase
reflection when `mirror` of the) production dependency read on the left.

The reader relation is derived, never assumed: on dependency pairs it is
`localizedPhysicalBranchRelation_reader_transport`, whose inputs are the strong physical domain
and the physical branch sign law; on non-dependency pairs both production reads are `none` because
dependency eligibility is invariant on the branch. -/
theorem localizedPhysicalBranchRelation_reader_relation
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (cfg : m.Configuration) (c : m.Center) (e : m.Aut) (mirror : Bool) (i : Fin 4)
    (centerFixed : m.centerPerm e c = c)
    (signLaw : ∀ d : m.Center, LigandBranchReaches m c i d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d))
    {target : LocalizedUniversalReference.Occurrence input}
    (targetRoot : target.1.root = c.1)
    {startL startR : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    (domain : ∀ x y,
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR x y →
      input.certified.LocalizedDepthDependency x.occurrence target →
      LocalizedPhysicalPairCase input m cfg e x y)
    (branchAtLeft : ∀ (x y : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input)),
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR x y →
      input.certified.LocalizedDepthDependency x.occurrence target →
      ∀ d : m.Center,
        LocalizedPhysicalCalibratedData input m cfg x.occurrence d →
          LigandBranchReaches m c i d.1) :
    ∀ x y,
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR x y →
      input.certified.localizedDependencyLabel target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) y =
        (if mirror then reflectUppercaseOptionalLabel else id)
          (input.certified.localizedDependencyLabel target
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input) target) x) := by
  have rootFixed : ((graphAutOfMultiCenterAut input.certified m graphEq e :
      input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom) c.1 = c.1 := by
    have physical : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
      (centerPerm_eq_iff m e c).mp centerFixed
    simpa [graphAutOfMultiCenterAut] using physical
  intro x y related
  by_cases depX : input.certified.LocalizedDepthDependency x.occurrence target
  · have depY : input.certified.LocalizedDepthDependency y.occurrence target :=
      (localizedPhysicalBranchRelation_dependency_iff input.certified singleBonded acyclic
        rootFixed related targetRoot).mp depX
    exact localizedPhysicalBranchRelation_reader_transport
      input singleBonded acyclic noDouble m graphEq cfg c e mirror i i signLaw
      related depX depY (domain x y related depX) (branchAtLeft x y related depX)
  · have depY : ¬ input.certified.LocalizedDepthDependency y.occurrence target := by
      intro dependency
      exact depX
        ((localizedPhysicalBranchRelation_dependency_iff input.certified singleBonded acyclic
          rootFixed related targetRoot).mpr dependency)
    have labelNoneX : input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) x = none := by
      dsimp only [CertifiedLocalizedCIPInput.localizedDependencyLabel]
      rw [dif_neg depX]
    have labelNoneY : input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) y = none := by
      dsimp only [CertifiedLocalizedCIPInput.localizedDependencyLabel]
      rw [dif_neg depY]
    rw [labelNoneX, labelNoneY]
    cases mirror <;>
      simp [CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel]

/-! ## Proper and mirror production-key observable equality -/

/-- **Proper production transport.**  On the selected non-mirror physical branch, the actual
production cumulative key observables agree at every pair of related cursors, for every recursion
fuel and every cumulative stage. -/
theorem localizedPhysicalBranchRelation_productionKey_observable_eq_proper
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (cfg : m.Configuration) (c : m.Center) (e : m.Aut) (i : Fin 4)
    (centerFixed : m.centerPerm e c = c)
    (signLaw : ∀ d : m.Center, LigandBranchReaches m c i d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (1 : ℝ) * m.configurationSign cfg (m.centerPerm e d))
    (target : LocalizedUniversalReference.Occurrence input)
    (targetRoot : target.1.root = c.1)
    (startL startR : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (domain : ∀ x y,
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR x y →
      input.certified.LocalizedDepthDependency x.occurrence target →
      LocalizedPhysicalPairCase input m cfg e x y)
    (branchAtLeft : ∀ (x y : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input)),
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR x y →
      input.certified.LocalizedDepthDependency x.occurrence target →
      ∀ d : m.Center,
        LocalizedPhysicalCalibratedData input m cfg x.occurrence d →
          LigandBranchReaches m c i d.1)
    (stage : LocalizedCumulativeRule45Stage) :
    ∀ (fuel : Nat) (x y : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input)),
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR x y →
      (input.certified.buildLocalizedRerootCumulativeRule45Key? stage target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) fuel x).map
          (input.certified.localizedRerootCumulativeRule45Observable) =
        (input.certified.buildLocalizedRerootCumulativeRule45Key? stage target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) fuel y).map
          (input.certified.localizedRerootCumulativeRule45Observable) := by
  have rootFixed : ((graphAutOfMultiCenterAut input.certified m graphEq e :
      input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom) c.1 = c.1 := by
    have physical : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
      (centerPerm_eq_iff m e c).mp centerFixed
    simpa [graphAutOfMultiCenterAut] using physical
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    dsimp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel, LocalizedReference.carrierFuel,
      LocalizedReference.Input.molecule]
    omega
  have reader := localizedPhysicalBranchRelation_reader_relation
    input singleBonded acyclic noDouble m graphEq cfg c e false i centerFixed
    (by simpa using signLaw) targetRoot domain branchAtLeft
  have labels : ∀ x y,
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR x y →
      input.certified.localizedDependencyLabel target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) x =
        input.certified.localizedDependencyLabel target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) y := by
    intro x y related
    have := reader x y related
    simpa using this.symm
  exact input.certified.buildLocalizedRerootCumulativeRule45Key?_map_observable_eq_of_related_sameSource
    stage target
    (input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target)
    (LocalizedPhysicalBranchRelation input.certified
      (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR)
    (fun x y related =>
      localizedPhysicalBranchRelation_atomLabel input.certified singleBonded acyclic related)
    (fun x y related =>
      localizedPhysicalBranchRelation_rootDistance input.certified singleBonded acyclic
        rootFixed related)
    (fun x y related =>
      localizedPhysicalBranchRelation_children input.certified singleBonded acyclic
        enough related)
    labels

/-- **Mirror production transport.**  On the selected mirror physical branch, the actual
production cumulative key observable at the right cursor at the uppercase-reflected stage equals
the observable at the left cursor at the original stage, for every recursion fuel and stage. -/
theorem localizedPhysicalBranchRelation_productionKey_observable_eq_mirror
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (cfg : m.Configuration) (c : m.Center) (e : m.Aut) (i : Fin 4)
    (centerFixed : m.centerPerm e c = c)
    (signLaw : ∀ d : m.Center, LigandBranchReaches m c i d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (-1 : ℝ) * m.configurationSign cfg (m.centerPerm e d))
    (target : LocalizedUniversalReference.Occurrence input)
    (targetRoot : target.1.root = c.1)
    (startL startR : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input))
    (domain : ∀ x y,
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR x y →
      input.certified.LocalizedDepthDependency x.occurrence target →
      LocalizedPhysicalPairCase input m cfg e x y)
    (branchAtLeft : ∀ (x y : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input)),
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR x y →
      input.certified.LocalizedDepthDependency x.occurrence target →
      ∀ d : m.Center,
        LocalizedPhysicalCalibratedData input m cfg x.occurrence d →
          LigandBranchReaches m c i d.1)
    (stage : LocalizedCumulativeRule45Stage) :
    ∀ (fuel : Nat) (x y : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input)),
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR x y →
      (input.certified.buildLocalizedRerootCumulativeRule45Key? stage target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) fuel x).map
          (input.certified.localizedRerootCumulativeRule45Observable) =
        (input.certified.buildLocalizedRerootCumulativeRule45Key?
          (reflectLocalizedCumulativeRule45Stage stage) target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) fuel y).map
          (input.certified.localizedRerootCumulativeRule45Observable) := by
  have rootFixed : ((graphAutOfMultiCenterAut input.certified m graphEq e :
      input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom) c.1 = c.1 := by
    have physical : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
      (centerPerm_eq_iff m e c).mp centerFixed
    simpa [graphAutOfMultiCenterAut] using physical
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    dsimp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel, LocalizedReference.carrierFuel,
      LocalizedReference.Input.molecule]
    omega
  have reader := localizedPhysicalBranchRelation_reader_relation
    input singleBonded acyclic noDouble m graphEq cfg c e true i centerFixed
    (by simpa using signLaw) targetRoot domain branchAtLeft
  have readerReflect : ∀ x y,
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR x y →
      input.certified.localizedDependencyLabel target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) y =
        reflectUppercaseOptionalLabel
          (input.certified.localizedDependencyLabel target
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input) target) x) := by
    intro x y related
    have := reader x y related
    simpa using this
  have withRead :=
    input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related_reflectUppercase
      stage
      (input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target))
      (input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target))
      (LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m graphEq e) c.1 startL startR)
      (fun x y related =>
        localizedPhysicalBranchRelation_atomLabel input.certified singleBonded acyclic related)
      (fun x y related =>
        localizedPhysicalBranchRelation_rootDistance input.certified singleBonded acyclic
          rootFixed related)
      (fun x y related =>
        localizedPhysicalBranchRelation_children input.certified singleBonded acyclic
          enough related)
      readerReflect
  intro fuel x y related
  rw [← input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
        stage target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) fuel x,
    ← input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
        (reflectLocalizedCumulativeRule45Stage stage) target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) fuel y]
  exact withRead fuel x y related

/-! ## The actual top occurrence and its physical frame slots -/

/-- The detected tetrahedral center of the certified input carried by a physical center `c`. -/
noncomputable def localizedPhysicalTopCenter
    (input : LocalizedUniversalReference.Input)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (c : m.Center) : input.certified.TetrahedralCenter :=
  ⟨c.1, (input.certified.moleculeGraph.mem_tetrahedralCenterSet c.1).mpr
    (input.certified.isTetrahedralCenter_of_physicalLigandEquiv m graphEq c)⟩

/-- The actual top occurrence rooted at the physical center `c`. -/
noncomputable def localizedPhysicalTopOccurrence
    (input : LocalizedUniversalReference.Input)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (c : m.Center) : LocalizedUniversalReference.Occurrence input :=
  input.certified.localizedFinalOccurrence (LocalizedUniversalReference.carrierFuel input)
    (localizedPhysicalTopCenter input m graphEq c)








theorem exists_localizedPhysicalTopOccurrence_frame_slotCorrespondence
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (c : m.Center) (e : m.Aut) (i j : Fin 4)
    (centerFixed : m.centerPerm e c = c)
    (ligandMaps : m.ligandPermAt e c i = j) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)),
      input.certified.localizedOccurrenceFourLigandFrame?
          (localizedPhysicalTopOccurrence input m graphEq c) = some frame ∧
        (∀ index : Fin 4,
          (frame.cursorAt index).occurrence.1.node.current? =
            some (m.ligandAtomAt c (alpha index))) ∧
        LocalizedAutCursorCorrespondence input.certified
          (graphAutOfMultiCenterAut input.certified m graphEq e) c.1
          (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) := by
  classical
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input := by
    dsimp [LocalizedUniversalReference.carrierFuel,
      LocalizedExtendedShortCircuit.carrierFuel, LocalizedReference.carrierFuel,
      LocalizedReference.Input.molecule]
    omega
  let target := localizedPhysicalTopOccurrence input m graphEq c
  have targetCurrent : target.1.node.current? = some c.1 := rfl
  obtain ⟨frame, alpha, frameComputed, slotSpec⟩ :=
    input.certified.exists_localizedOccurrenceFourLigandFrame_and_ligandPermutation
      singleBonded acyclic enough target (oAtom := c.1) targetCurrent m graphEq c rfl
  refine ⟨frame, alpha, frameComputed, slotSpec, ?_⟩
  have presentL : frame.cursorAt (alpha.symm i) ∈ frame.cursors :=
    List.get_mem frame.cursors _
  have presentR : frame.cursorAt (alpha.symm j) ∈ frame.cursors :=
    List.get_mem frame.cursors _
  have previousL := input.certified.localizedOccurrenceFourLigandFrame_cursor_previous
    target frame frameComputed (frame.cursorAt (alpha.symm i)) presentL
  have previousR := input.certified.localizedOccurrenceFourLigandFrame_cursor_previous
    target frame frameComputed (frame.cursorAt (alpha.symm j)) presentR
  have rootL := input.certified.localizedOccurrenceFourLigandFrame_cursor_root
    target frame frameComputed (frame.cursorAt (alpha.symm i)) presentL
  have rootR := input.certified.localizedOccurrenceFourLigandFrame_cursor_root
    target frame frameComputed (frame.cursorAt (alpha.symm j)) presentR
  have currentL : (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? =
      some (m.ligandAtomAt c i) := by
    have h := slotSpec (alpha.symm i)
    simpa using h
  have currentR : (frame.cursorAt (alpha.symm j)).occurrence.1.node.current? =
      some (m.ligandAtomAt c j) := by
    have h := slotSpec (alpha.symm j)
    simpa using h
  have physicalFix : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
    (centerPerm_eq_iff m e c).mp centerFixed
  refine
    { source_root := ?_
      target_root := ?_
      current_maps := ?_
      previous_none := ?_
      previous_maps := ?_ }
  · simpa using rootL
  · simpa using rootR
  · intro a b ha hb
    have aEq : a = m.ligandAtomAt c i := by
      rw [currentL] at ha
      injection ha with h
      exact h.symm
    have bEq : b = m.ligandAtomAt c j := by
      rw [currentR] at hb
      injection hb with h
      exact h.symm
    have mapped : m.ligandAtomAt c j =
        (e : Equiv.Perm input.certified.Atom) (m.ligandAtomAt c i) := by
      calc m.ligandAtomAt c j
          = m.ligandAtomAt c (m.ligandPermAt e c i) := by rw [← ligandMaps]
        _ = m.ligandAtomAt (m.centerPerm e c) (m.ligandPermAt e c i) := by
              rw [centerFixed]
        _ = (e : Equiv.Perm input.certified.Atom) (m.ligandAtomAt c i) := by simp
    rw [bEq, aEq]
    exact mapped
  · constructor
    · intro hnone
      rw [previousL] at hnone
      cases hnone
    · intro hnone
      rw [previousR] at hnone
      cases hnone
  · intro p q hp hq
    have pEq : p = target := by
      rw [previousL] at hp
      injection hp with h
      exact h.symm
    have qEq : q = target := by
      rw [previousR] at hq
      injection hq with h
      exact h.symm
    refine ⟨?_, ?_, ?_⟩
    · rw [pEq]
      rfl
    · rw [qEq]
      rfl
    · intro a b ha hb
      rw [pEq] at ha
      rw [qEq] at hb
      have aEq : a = c.1 := by
        rw [targetCurrent] at ha
        injection ha with h
        exact h.symm
      have bEq : b = c.1 := by
        rw [targetCurrent] at hb
        injection hb with h
        exact h.symm
      rw [aEq, bEq]
      exact physicalFix.symm









theorem exists_localizedPhysicalTwinData_of_terminalTwinLeaves
    (input : LocalizedUniversalReference.Input)
    (occurrence : LocalizedUniversalReference.Occurrence input)
    (rootTetrahedral :
      input.certified.moleculeGraph.IsTetrahedralCenter occurrence.1.root)
    (leaves : ActualPhysicalTerminalTwinLeaves input occurrence) :
    ∃ centerAtom leftAtom rightAtom : input.certified.Atom,
      LocalizedPhysicalTwinData input.certified occurrence centerAtom leftAtom rightAtom := by
  obtain ⟨centerAtom, leftAtom, rightAtom, current, tetrahedral, leftNeighbors,
    rightNeighbors, left_ne, z_eq, mass_eq, _charge_eq⟩ := leaves
  exact ⟨centerAtom, leftAtom, rightAtom,
    { center_at := current
      tetrahedral := tetrahedral
      leftNeighbors := leftNeighbors
      rightNeighbors := rightNeighbors
      left_ne := left_ne
      root_ne_left :=
        root_ne_terminalLeaf_of_tetrahedralRoot input.certified rootTetrahedral leftNeighbors
      root_ne_right :=
        root_ne_terminalLeaf_of_tetrahedralRoot input.certified rootTetrahedral rightNeighbors
      z_eq := z_eq
      mass_eq := mass_eq }⟩




theorem exists_localizedPhysicalCalibratedData_of_calibratedCenter
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (center : m.Center)
    (target : LocalizedUniversalReference.Occurrence input)
    (targetCurrent : target.1.node.current? = some center.1)
    (calibrated : ActualPhysicalCalibratedCenter input.certified m cfg center) :
    LocalizedPhysicalCalibratedData input m cfg target center := by
  classical
  obtain ⟨frame, alpha, pointAt, frameComputed, matchLigand, separated, spatial, _observed,
    calibration⟩ :=
    exists_frameAndCalibration_of_calibratedCenter input singleBonded acyclic m cfg graphEq
      center target targetCurrent calibrated
  refine
    { center_at := targetCurrent
      separated := ?_
      coordinates := ?_ }
  · intro other otherComputed
    have otherEq : other = frame := Option.some.inj (otherComputed.symm.trans frameComputed)
    rw [otherEq]
    exact separated
  · intro other otherComputed
    have otherEq : other = frame := Option.some.inj (otherComputed.symm.trans frameComputed)
    rw [otherEq]
    exact ⟨alpha, fun index => pointAt (alpha index), matchLigand, spatial, calibration⟩







theorem localizedPhysicalPairCase_of_globalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (c : m.Center) (e : m.Aut)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg c)
    (coverage : m.centers = input.certified.tetrahedralCenterSet)
    (topCenter : input.certified.TetrahedralCenter)
    (topAt : topCenter.1 = c.1)
    (centerFixed : m.centerPerm e c = c)
    {startL startR : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    {x y : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    (related : LocalizedPhysicalBranchRelation input.certified
      (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1 startL startR x y)
    (xDependency : input.certified.LocalizedDepthDependency x.occurrence
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter))
    (yDependency : input.certified.LocalizedDepthDependency y.occurrence
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter)) :
    LocalizedPhysicalPairCase input m cfg e x y := by
  classical
  obtain ⟨a, xCurrent⟩ := input.certified.occurrence_current_exists x.occurrence
  obtain ⟨b, yCurrent⟩ := input.certified.occurrence_current_exists y.occurrence
  have bEq : b = (e : Equiv.Perm input.certified.Atom) a := by
    simpa [graphAutOfMultiCenterAut] using related.1.current_maps xCurrent yCurrent
  have rootX : x.occurrence.1.root = c.1 := by
    rw [xDependency.1,
      AuxiliaryContextIntegrity.localizedFinalOccurrence_root input.certified
        (LocalizedUniversalReference.carrierFuel input) topCenter,
      topAt]
  have rootY : y.occurrence.1.root = c.1 := by
    rw [yDependency.1,
      AuxiliaryContextIntegrity.localizedFinalOccurrence_root input.certified
        (LocalizedUniversalReference.carrierFuel input) topCenter,
      topAt]
  have rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter c.1 :=
    (input.certified.moleculeGraph.mem_tetrahedralCenterSet c.1).mp
      (mem_tetrahedralCenterSet_of_center coverage c)
  have xRootTetrahedral :
      input.certified.moleculeGraph.IsTetrahedralCenter x.occurrence.1.root := by
    rw [rootX]
    exact rootTetrahedral
  have yRootTetrahedral :
      input.certified.moleculeGraph.IsTetrahedralCenter y.occurrence.1.root := by
    rw [rootY]
    exact rootTetrahedral
  have aNotRoot : a ≠ c.1 := by
    intro aEq
    apply dependency_current_ne_topAtom_of_finalOccurrence input singleBonded acyclic
      topCenter x xDependency
    rw [xCurrent, aEq, ← topAt]
  by_cases candidate : a ∈ m.centers
  · let centerX : m.Center := ⟨a, candidate⟩
    have centerX_ne : centerX ≠ c := fun h => aNotRoot (congrArg Subtype.val h)
    have bMem : b ∈ m.centers := by
      rw [bEq]
      exact (MultiCenterMolecule.Aut.mem_centers_iff (m := m) (e := e) a).mp candidate
    let centerY : m.Center := ⟨b, bMem⟩
    have centerEq : m.centerPerm e centerX = centerY := Subtype.ext bEq.symm
    rcases domain.centerCase centerX centerX_ne with twinX | calibratedX
    · have twinY : ActualPhysicalTerminalTwinCenter input.certified m centerY := by
        have transported : ActualPhysicalTerminalTwinCenter input.certified m
            (m.centerPerm e centerX) :=
          (actualPhysicalTerminalTwinCenter_centerPerm_iff input.certified m e centerX).mpr twinX
        rw [centerEq] at transported
        exact transported
      obtain ⟨xC, xL, xR, xTwin⟩ :=
        exists_localizedPhysicalTwinData_of_terminalTwinLeaves input x.occurrence
          xRootTetrahedral
          (actualPhysicalTerminalTwinLeaves_of_globalTwinCenter input m domain.graphEq
            centerX x.occurrence xCurrent twinX)
      obtain ⟨yC, yL, yR, yTwin⟩ :=
        exists_localizedPhysicalTwinData_of_terminalTwinLeaves input y.occurrence
          yRootTetrahedral
          (actualPhysicalTerminalTwinLeaves_of_globalTwinCenter input m domain.graphEq
            centerY y.occurrence yCurrent twinY)
      exact Or.inr (Or.inl ⟨xC, xL, xR, yC, yL, yR, xTwin, yTwin⟩)
    · have physicalFix : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
        (centerPerm_eq_iff m e c).mp centerFixed
      have centerY_ne : centerY ≠ c := by
        intro h
        have valEq : b = c.1 := congrArg Subtype.val h
        have eaEq : (e : Equiv.Perm input.certified.Atom) a = c.1 := bEq.symm.trans valEq
        exact aNotRoot ((e : Equiv.Perm input.certified.Atom).injective
          (eaEq.trans physicalFix.symm))
      have twinYFalse : ¬ ActualPhysicalTerminalTwinCenter input.certified m centerY := by
        intro twinY
        have transported : ActualPhysicalTerminalTwinCenter input.certified m
            (m.centerPerm e centerX) := by
          rw [centerEq]
          exact twinY
        exact actualPhysicalTerminalTwinCenter_false_of_calibrated calibratedX
          ((actualPhysicalTerminalTwinCenter_centerPerm_iff input.certified m e centerX).mp
            transported)
      have calibratedY : ActualPhysicalCalibratedCenter input.certified m cfg centerY :=
        actualPhysicalCalibratedCenter_of_globalDomain domain centerY_ne twinYFalse
      exact Or.inr (Or.inr
        ⟨centerX, centerY,
          exists_localizedPhysicalCalibratedData_of_calibratedCenter input singleBonded acyclic
            m cfg domain.graphEq centerX x.occurrence xCurrent calibratedX,
          exists_localizedPhysicalCalibratedData_of_calibratedCenter input singleBonded acyclic
            m cfg domain.graphEq centerY y.occurrence yCurrent calibratedY⟩)
  · have aNotMem : a ∉ input.certified.tetrahedralCenterSet := by
      intro h
      exact candidate (mem_centers_of_mem_tetrahedralCenterSet coverage h)
    have bNotMem : b ∉ input.certified.tetrahedralCenterSet := by
      intro h
      have bMem : b ∈ m.centers := mem_centers_of_mem_tetrahedralCenterSet coverage h
      have eaMem : (e : Equiv.Perm input.certified.Atom) a ∈ m.centers := by
        rw [← bEq]
        exact bMem
      exact candidate
        ((MultiCenterMolecule.Aut.apply_mem_centers_iff (m := m) (e := e) a).mp eaMem)
    exact Or.inl ⟨a, b, xCurrent, yCurrent, aNotMem, bNotMem⟩





theorem localizedPhysicalBranchLeftMembership
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (m : MultiCenterMolecule input.certified.Atom)
    (graphEq : m.mol = input.certified.moleculeGraph)
    (c : m.Center) (i : Fin 4)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (localizedPhysicalTopOccurrence input m graphEq c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (m.ligandAtomAt c (alpha index)))
    {x : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    (reachable : input.certified.ActualChildReachable
      (frame.cursorAt (alpha.symm i)) x)
    {a : input.certified.Atom}
    (xCurrent : x.occurrence.1.node.current? = some a) :
    LigandBranchReaches m c i a := by
  classical
  let target := localizedPhysicalTopOccurrence input m graphEq c
  let startL := frame.cursorAt (alpha.symm i)
  have present : startL ∈ frame.cursors := List.get_mem frame.cursors _
  have previousEq : startL.previous? = some target :=
    input.certified.localizedOccurrenceFourLigandFrame_cursor_previous target frame frameComputed
      startL present
  have validStart : input.certified.LocalizedRerootCursorValid startL :=
    input.certified.localizedOccurrenceFourLigandFrame_cursor_valid target frame frameComputed
      startL present
  have oObserved : startL.occurrence.1.node.current? = some (m.ligandAtomAt c i) := by
    have h := slotSpec (alpha.symm i)
    simpa [startL] using h
  have pObserved : target.1.node.current? = some c.1 := rfl
  have incomingEdge : input.certified.moleculeGraph.Adj c.1 (m.ligandAtomAt c i) := by
    rw [← graphEq]
    exact m.ligandAtomAt_adj c i
  have cut := input.certified.actualReachable_current_mem_cutBranch_general
    singleBonded acyclic (globalCarrierFuel_adequate input) startL target previousEq validStart
    oObserved pObserved incomingEdge x reachable xCurrent
  unfold LigandBranchReaches
  rw [graphEq]
  simpa [AcyclicCutBranchAutomorphism.CutBranch,
    AcyclicCutBranchAutomorphism.CutBranchReaches] using cut








/-- A vertex reached inside the ligand branch at `i` is never the root atom itself. -/
theorem ligandBranchReaches_ne_center {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (c : m.Center) (i : Fin 4) {v : V}
    (reachable : LigandBranchReaches m c i v) : v ≠ c.1 := by
  rintro rfl
  rcases reachable with ⟨p, hp⟩
  exact hp (SimpleGraph.Walk.end_mem_support p)






theorem localizedPhysicalBranchRelation_referenceState_globalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (c : m.Center) (e : m.Aut) (mirror : Bool) (i : Fin 4)
    (centerFixed : m.centerPerm e c = c)
    (signLaw : ∀ d : m.Center, LigandBranchReaches m c i d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d))
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg c)
    (coverage : m.centers = input.certified.tetrahedralCenterSet)
    (topCenter : input.certified.TetrahedralCenter)
    (topAt : topCenter.1 = c.1)
    {startL startR : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    (branchAtLeft : ∀ (x : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input)) (a : input.certified.Atom),
      input.certified.ActualChildReachable startL x →
      x.occurrence.1.node.current? = some a →
      LigandBranchReaches m c i a)
    {x y : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    (related : LocalizedPhysicalBranchRelation input.certified
      (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1 startL startR x y)
    (xDependency : input.certified.LocalizedDepthDependency x.occurrence
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter))
    (yDependency : input.certified.LocalizedDepthDependency y.occurrence
      (input.certified.localizedFinalOccurrence
        (LocalizedUniversalReference.carrierFuel input) topCenter)) :
    LocalizedUniversalReference.referenceState input y.occurrence =
      (if mirror then reflectUppercaseOptionalLabel else id)
        (LocalizedUniversalReference.referenceState input x.occurrence) := by
  classical
  obtain ⟨a, xCurrent⟩ := input.certified.occurrence_current_exists x.occurrence
  obtain ⟨b, yCurrent⟩ := input.certified.occurrence_current_exists y.occurrence
  have bEq : b = (e : Equiv.Perm input.certified.Atom) a := by
    simpa [graphAutOfMultiCenterAut] using related.1.current_maps xCurrent yCurrent
  have rootX : x.occurrence.1.root = c.1 := by
    rw [xDependency.1,
      AuxiliaryContextIntegrity.localizedFinalOccurrence_root input.certified
        (LocalizedUniversalReference.carrierFuel input) topCenter,
      topAt]
  have rootY : y.occurrence.1.root = c.1 := by
    rw [yDependency.1,
      AuxiliaryContextIntegrity.localizedFinalOccurrence_root input.certified
        (LocalizedUniversalReference.carrierFuel input) topCenter,
      topAt]
  have rootTetrahedral : input.certified.moleculeGraph.IsTetrahedralCenter c.1 :=
    (input.certified.moleculeGraph.mem_tetrahedralCenterSet c.1).mp
      (mem_tetrahedralCenterSet_of_center coverage c)
  have xRootTetrahedral :
      input.certified.moleculeGraph.IsTetrahedralCenter x.occurrence.1.root := by
    rw [rootX]
    exact rootTetrahedral
  have yRootTetrahedral :
      input.certified.moleculeGraph.IsTetrahedralCenter y.occurrence.1.root := by
    rw [rootY]
    exact rootTetrahedral
  by_cases candidate : a ∈ m.centers
  · let d : m.Center := ⟨a, candidate⟩
    have d_ne_root : d ≠ c := by
      intro h
      have valEq : a = c.1 := congrArg Subtype.val h
      exact (ligandBranchReaches_ne_center m c i
        (branchAtLeft x a related.2.1 xCurrent)) valEq
    have yCurrentImage : y.occurrence.1.node.current? = some (m.centerPerm e d).1 := by
      rw [yCurrent]
      show some b = some ((e : Equiv.Perm input.certified.Atom) a)
      exact congrArg some bEq
    rcases domain.centerCase d d_ne_root with twinD | calibratedD
    · have twinImage : ActualPhysicalTerminalTwinCenter input.certified m (m.centerPerm e d) :=
        (actualPhysicalTerminalTwinCenter_centerPerm_iff input.certified m e d).mpr twinD
      have xNone :=
        referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic noDouble m
          domain.graphEq d x.occurrence xCurrent xRootTetrahedral twinD
      have yNone :=
        referenceState_eq_none_of_globalTwinCenter input singleBonded acyclic noDouble m
          domain.graphEq (m.centerPerm e d) y.occurrence yCurrentImage yRootTetrahedral twinImage
      rw [xNone, yNone]
      cases mirror <;>
        simp [CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel]
    · have d_notTwin : ¬ ActualPhysicalTerminalTwinCenter input.certified m d :=
        actualPhysicalTerminalTwinCenter_false_of_calibrated calibratedD
      have physicalFix : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
        (centerPerm_eq_iff m e c).mp centerFixed
      have image_ne_root : m.centerPerm e d ≠ c := by
        intro h
        have valEq : (e : Equiv.Perm input.certified.Atom) a = c.1 := congrArg Subtype.val h
        exact (ligandBranchReaches_ne_center m c i
          (branchAtLeft x a related.2.1 xCurrent))
          ((e : Equiv.Perm input.certified.Atom).injective
            (valEq.trans physicalFix.symm))
      have image_notTwin :
          ¬ ActualPhysicalTerminalTwinCenter input.certified m (m.centerPerm e d) := by
        intro twinImage
        exact d_notTwin
          ((actualPhysicalTerminalTwinCenter_centerPerm_iff input.certified m e d).mp twinImage)
      have branchMem : LigandBranchReaches m c i d.1 :=
        branchAtLeft x a related.2.1 xCurrent
      have signLocal : ActualLocalSignLaw m cfg e mirror d := by
        simpa [ActualLocalSignLaw] using signLaw d branchMem
      exact (actual_referenceState_automorphism_sign_iff_localSignLaw input noDouble singleBonded
        acyclic m cfg c domain d e mirror d_ne_root image_ne_root d_notTwin image_notTwin
        x.occurrence y.occurrence xCurrent yCurrentImage).2 signLocal
  · have aNotMem : a ∉ input.certified.tetrahedralCenterSet := by
      intro h
      exact candidate (mem_centers_of_mem_tetrahedralCenterSet coverage h)
    have bNotMem : b ∉ input.certified.tetrahedralCenterSet := by
      intro hb
      have hImage : (graphAutOfMultiCenterAut input.certified m domain.graphEq e :
          Equiv.Perm input.certified.Atom) a ∈ input.certified.tetrahedralCenterSet := by
        simpa [graphAutOfMultiCenterAut, bEq] using hb
      exact aNotMem
        ((input.certified.moleculeGraph.mem_tetrahedralCenterSet_apply_aut_iff
          (graphAutOfMultiCenterAut input.certified m domain.graphEq e) a).mpr hImage)
    have xNone := referenceState_eq_none_of_actualPhysicalNoncandidate input noDouble
      x.occurrence ⟨a, xCurrent, aNotMem⟩
    have yNone := referenceState_eq_none_of_actualPhysicalNoncandidate input noDouble
      y.occurrence ⟨b, yCurrent, bNotMem⟩
    rw [xNone, yNone]
    cases mirror <;>
      simp [CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel]






theorem localizedPhysicalBranchRelation_reader_relation_globalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (c : m.Center) (e : m.Aut) (mirror : Bool) (i j : Fin 4)
    (centerFixed : m.centerPerm e c = c)
    (signLaw : ∀ d : m.Center, LigandBranchReaches m c i d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d))
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg c)
    (coverage : m.centers = input.certified.tetrahedralCenterSet)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (localizedPhysicalTopOccurrence input m domain.graphEq c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (m.ligandAtomAt c (alpha index))) :
    ∀ x y,
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) x y →
      input.certified.localizedDependencyLabel
          (localizedPhysicalTopOccurrence input m domain.graphEq c)
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input)
            (localizedPhysicalTopOccurrence input m domain.graphEq c)) y =
        (if mirror then reflectUppercaseOptionalLabel else id)
          (input.certified.localizedDependencyLabel
            (localizedPhysicalTopOccurrence input m domain.graphEq c)
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input)
              (localizedPhysicalTopOccurrence input m domain.graphEq c)) x) := by
  let target := localizedPhysicalTopOccurrence input m domain.graphEq c
  let topCenter := localizedPhysicalTopCenter input m domain.graphEq c
  have targetRoot : target.1.root = c.1 := rfl
  have rootFixed : ((graphAutOfMultiCenterAut input.certified m domain.graphEq e :
      input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom) c.1 = c.1 := by
    have physical : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
      (centerPerm_eq_iff m e c).mp centerFixed
    simpa [graphAutOfMultiCenterAut] using physical
  intro x y related
  by_cases depX : input.certified.LocalizedDepthDependency x.occurrence target
  · have depY : input.certified.LocalizedDepthDependency y.occurrence target :=
      (localizedPhysicalBranchRelation_dependency_iff input.certified singleBonded acyclic
        rootFixed related targetRoot).mp depX
    rw [localizedReferenceDependencyLabel_eq_state input target x depX,
      localizedReferenceDependencyLabel_eq_state input target y depY]
    exact localizedPhysicalBranchRelation_referenceState_globalDomain
      input singleBonded acyclic noDouble m cfg c e mirror i centerFixed signLaw domain
      coverage topCenter rfl
      (fun x a reachable current =>
        localizedPhysicalBranchLeftMembership input singleBonded acyclic m domain.graphEq c i
          frame alpha frameComputed slotSpec reachable current)
      related depX depY
  · have depY : ¬ input.certified.LocalizedDepthDependency y.occurrence target := by
      intro dependency
      exact depX
        ((localizedPhysicalBranchRelation_dependency_iff input.certified singleBonded acyclic
          rootFixed related targetRoot).mpr dependency)
    have labelNoneX : input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) x = none := by
      dsimp only [CertifiedLocalizedCIPInput.localizedDependencyLabel]
      rw [dif_neg depX]
    have labelNoneY : input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) y = none := by
      dsimp only [CertifiedLocalizedCIPInput.localizedDependencyLabel]
      rw [dif_neg depY]
    rw [labelNoneX, labelNoneY]
    cases mirror <;>
      simp [CertifiedLocalizedCIPInput.reflectUppercaseOptionalLabel]

/-- **Direct proper production transport from the global domain.** -/
theorem localizedPhysicalBranchRelation_productionKey_observable_eq_proper_globalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (c : m.Center) (e : m.Aut) (i j : Fin 4)
    (centerFixed : m.centerPerm e c = c)
    (signLaw : ∀ d : m.Center, LigandBranchReaches m c i d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (1 : ℝ) * m.configurationSign cfg (m.centerPerm e d))
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg c)
    (coverage : m.centers = input.certified.tetrahedralCenterSet)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (localizedPhysicalTopOccurrence input m domain.graphEq c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (m.ligandAtomAt c (alpha index)))
    (stage : LocalizedCumulativeRule45Stage) :
    ∀ (fuel : Nat) (x y : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input)),
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) x y →
      (input.certified.buildLocalizedRerootCumulativeRule45Key? stage
          (localizedPhysicalTopOccurrence input m domain.graphEq c)
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input)
            (localizedPhysicalTopOccurrence input m domain.graphEq c)) fuel x).map
          (input.certified.localizedRerootCumulativeRule45Observable) =
        (input.certified.buildLocalizedRerootCumulativeRule45Key? stage
          (localizedPhysicalTopOccurrence input m domain.graphEq c)
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input)
            (localizedPhysicalTopOccurrence input m domain.graphEq c)) fuel y).map
          (input.certified.localizedRerootCumulativeRule45Observable) := by
  have rootFixed : ((graphAutOfMultiCenterAut input.certified m domain.graphEq e :
      input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom) c.1 = c.1 := by
    have physical : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
      (centerPerm_eq_iff m e c).mp centerFixed
    simpa [graphAutOfMultiCenterAut] using physical
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input :=
    globalCarrierFuel_adequate input
  let target := localizedPhysicalTopOccurrence input m domain.graphEq c
  have reader := localizedPhysicalBranchRelation_reader_relation_globalDomain
    input singleBonded acyclic noDouble m cfg c e false i j centerFixed
    (fun d h => by simpa using signLaw d h) domain coverage frame alpha frameComputed slotSpec
  have labels : ∀ x y,
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) x y →
      input.certified.localizedDependencyLabel target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) x =
        input.certified.localizedDependencyLabel target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) y := by
    intro x y related
    have := reader x y related
    simpa using this.symm
  exact input.certified.buildLocalizedRerootCumulativeRule45Key?_map_observable_eq_of_related_sameSource
    stage target
    (input.certified.localizedDependencyView
      (LocalizedUniversalReference.referenceState input) target)
    (LocalizedPhysicalBranchRelation input.certified
      (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
      (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)))
    (fun x y related =>
      localizedPhysicalBranchRelation_atomLabel input.certified singleBonded acyclic related)
    (fun x y related =>
      localizedPhysicalBranchRelation_rootDistance input.certified singleBonded acyclic
        rootFixed related)
    (fun x y related =>
      localizedPhysicalBranchRelation_children input.certified singleBonded acyclic
        enough related)
    labels

/-- **Direct mirror production transport from the global domain.** -/
theorem localizedPhysicalBranchRelation_productionKey_observable_eq_mirror_globalDomain
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration)
    (c : m.Center) (e : m.Aut) (i j : Fin 4)
    (centerFixed : m.centerPerm e c = c)
    (signLaw : ∀ d : m.Center, LigandBranchReaches m c i d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (-1 : ℝ) * m.configurationSign cfg (m.centerPerm e d))
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg c)
    (coverage : m.centers = input.certified.tetrahedralCenterSet)
    (frame : input.certified.LocalizedOccurrenceFourLigandFrame
      (LocalizedUniversalReference.carrierFuel input))
    (alpha : Equiv.Perm (Fin 4))
    (frameComputed : input.certified.localizedOccurrenceFourLigandFrame?
      (localizedPhysicalTopOccurrence input m domain.graphEq c) = some frame)
    (slotSpec : ∀ index : Fin 4,
      (frame.cursorAt index).occurrence.1.node.current? =
        some (m.ligandAtomAt c (alpha index)))
    (stage : LocalizedCumulativeRule45Stage) :
    ∀ (fuel : Nat) (x y : input.certified.LocalizedRerootCursor
        (LocalizedUniversalReference.carrierFuel input)),
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) x y →
      (input.certified.buildLocalizedRerootCumulativeRule45Key? stage
          (localizedPhysicalTopOccurrence input m domain.graphEq c)
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input)
            (localizedPhysicalTopOccurrence input m domain.graphEq c)) fuel x).map
          (input.certified.localizedRerootCumulativeRule45Observable) =
        (input.certified.buildLocalizedRerootCumulativeRule45Key?
          (reflectLocalizedCumulativeRule45Stage stage)
          (localizedPhysicalTopOccurrence input m domain.graphEq c)
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input)
            (localizedPhysicalTopOccurrence input m domain.graphEq c)) fuel y).map
          (input.certified.localizedRerootCumulativeRule45Observable) := by
  have rootFixed : ((graphAutOfMultiCenterAut input.certified m domain.graphEq e :
      input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom) c.1 = c.1 := by
    have physical : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
      (centerPerm_eq_iff m e c).mp centerFixed
    simpa [graphAutOfMultiCenterAut] using physical
  have enough : input.certified.certified.input.molecule.atomCount ≤
      LocalizedUniversalReference.carrierFuel input :=
    globalCarrierFuel_adequate input
  let target := localizedPhysicalTopOccurrence input m domain.graphEq c
  have reader := localizedPhysicalBranchRelation_reader_relation_globalDomain
    input singleBonded acyclic noDouble m cfg c e true i j centerFixed
    (fun d h => by simpa using signLaw d h) domain coverage frame alpha frameComputed slotSpec
  have readerReflect : ∀ x y,
      LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)) x y →
      input.certified.localizedDependencyLabel target
          (input.certified.localizedDependencyView
            (LocalizedUniversalReference.referenceState input) target) y =
        reflectUppercaseOptionalLabel
          (input.certified.localizedDependencyLabel target
            (input.certified.localizedDependencyView
              (LocalizedUniversalReference.referenceState input) target) x) := by
    intro x y related
    have := reader x y related
    simpa using this
  have withRead :=
    input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_map_observable_eq_of_related_reflectUppercase
      stage
      (input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target))
      (input.certified.localizedDependencyLabel target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target))
      (LocalizedPhysicalBranchRelation input.certified
        (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
        (frame.cursorAt (alpha.symm i)) (frame.cursorAt (alpha.symm j)))
      (fun x y related =>
        localizedPhysicalBranchRelation_atomLabel input.certified singleBonded acyclic related)
      (fun x y related =>
        localizedPhysicalBranchRelation_rootDistance input.certified singleBonded acyclic
          rootFixed related)
      (fun x y related =>
        localizedPhysicalBranchRelation_children input.certified singleBonded acyclic
          enough related)
      readerReflect
  intro fuel x y related
  rw [← input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
        stage target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) fuel x,
    ← input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
        (reflectLocalizedCumulativeRule45Stage stage) target
        (input.certified.localizedDependencyView
          (LocalizedUniversalReference.referenceState input) target) fuel y]
  exact withRead fuel x y related

/-! ## Final physical Proper/Mirror branch observable equality -/












theorem localizedPhysicalBranch_finalOccurrence_observable_eq
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration) (c : m.Center) (e : m.Aut)
    (i j : Fin 4) (mirror : Bool)
    (centerFixed : m.centerPerm e c = c)
    (ligandMaps : m.ligandPermAt e c i = j)
    (signLaw : ∀ d : m.Center, LigandBranchReaches m c i d.1 →
      m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
        (if mirror then -1 else 1) * m.configurationSign cfg (m.centerPerm e d))
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg c)
    (coverage : m.centers = input.certified.tetrahedralCenterSet) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)),
      input.certified.localizedOccurrenceFourLigandFrame?
          (localizedPhysicalTopOccurrence input m domain.graphEq c) = some frame ∧
        (∀ index : Fin 4,
          (frame.cursorAt index).occurrence.1.node.current? =
            some (m.ligandAtomAt c (alpha index))) ∧
        (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? =
          some (m.ligandAtomAt c i) ∧
        (frame.cursorAt (alpha.symm j)).occurrence.1.node.current? =
          some (m.ligandAtomAt c j) ∧
        ∀ (fuel : Nat) (stage : LocalizedCumulativeRule45Stage),
          (input.certified.buildLocalizedRerootCumulativeRule45Key? stage
              (localizedPhysicalTopOccurrence input m domain.graphEq c)
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input)
                (localizedPhysicalTopOccurrence input m domain.graphEq c)) fuel
              (frame.cursorAt (alpha.symm i))).map
            (input.certified.localizedRerootCumulativeRule45Observable) =
          (input.certified.buildLocalizedRerootCumulativeRule45Key?
              (if mirror then reflectLocalizedCumulativeRule45Stage stage else stage)
              (localizedPhysicalTopOccurrence input m domain.graphEq c)
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input)
                (localizedPhysicalTopOccurrence input m domain.graphEq c)) fuel
              (frame.cursorAt (alpha.symm j))).map
            (input.certified.localizedRerootCumulativeRule45Observable) := by
  classical
  obtain ⟨frame, alpha, frameComputed, slotSpec, correspondence⟩ :=
    exists_localizedPhysicalTopOccurrence_frame_slotCorrespondence input singleBonded acyclic
      m domain.graphEq c e i j centerFixed ligandMaps
  let target := localizedPhysicalTopOccurrence input m domain.graphEq c
  let topCenter := localizedPhysicalTopCenter input m domain.graphEq c
  let startL := frame.cursorAt (alpha.symm i)
  let startR := frame.cursorAt (alpha.symm j)
  have targetRoot : target.1.root = c.1 := rfl
  have rootFixed : ((graphAutOfMultiCenterAut input.certified m domain.graphEq e :
      input.certified.moleculeGraph.Aut) : Equiv.Perm input.certified.Atom) c.1 = c.1 := by
    have physical : (e : Equiv.Perm input.certified.Atom) c.1 = c.1 :=
      (centerPerm_eq_iff m e c).mp centerFixed
    simpa [graphAutOfMultiCenterAut] using physical
  have relatedStart : LocalizedPhysicalBranchRelation input.certified
      (graphAutOfMultiCenterAut input.certified m domain.graphEq e) c.1
      startL startR startL startR :=
    ⟨correspondence, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  refine ⟨frame, alpha, frameComputed, slotSpec, ?_, ?_, ?_⟩
  · have h := slotSpec (alpha.symm i)
    simpa [startL] using h
  · have h := slotSpec (alpha.symm j)
    simpa [startR] using h
  · cases mirror with
    | false =>
        intro fuel stage
        exact localizedPhysicalBranchRelation_productionKey_observable_eq_proper_globalDomain
          input singleBonded acyclic noDouble m cfg c e i j centerFixed
          (fun d h => by simpa using signLaw d h) domain coverage
          frame alpha frameComputed slotSpec stage fuel startL startR relatedStart
    | true =>
        intro fuel stage
        exact localizedPhysicalBranchRelation_productionKey_observable_eq_mirror_globalDomain
          input singleBonded acyclic noDouble m cfg c e i j centerFixed
          (fun d h => by simpa using signLaw d h) domain coverage
          frame alpha frameComputed slotSpec stage fuel startL startR relatedStart







theorem localizedPhysicalBranch_transport_observable_eq
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (m : MultiCenterMolecule input.certified.Atom)
    (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) (mirror : Bool)
    (transport : BranchTransport m cfg c i j mirror)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified m cfg c)
    (coverage : m.centers = input.certified.tetrahedralCenterSet) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)),
      input.certified.localizedOccurrenceFourLigandFrame?
          (localizedPhysicalTopOccurrence input m domain.graphEq c) = some frame ∧
        (∀ index : Fin 4,
          (frame.cursorAt index).occurrence.1.node.current? =
            some (m.ligandAtomAt c (alpha index))) ∧
        (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? =
          some (m.ligandAtomAt c i) ∧
        (frame.cursorAt (alpha.symm j)).occurrence.1.node.current? =
          some (m.ligandAtomAt c j) ∧
        ∀ (fuel : Nat) (stage : LocalizedCumulativeRule45Stage),
          (input.certified.buildLocalizedRerootCumulativeRule45Key? stage
              (localizedPhysicalTopOccurrence input m domain.graphEq c)
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input)
                (localizedPhysicalTopOccurrence input m domain.graphEq c)) fuel
              (frame.cursorAt (alpha.symm i))).map
            (input.certified.localizedRerootCumulativeRule45Observable) =
          (input.certified.buildLocalizedRerootCumulativeRule45Key?
              (if mirror then reflectLocalizedCumulativeRule45Stage stage else stage)
              (localizedPhysicalTopOccurrence input m domain.graphEq c)
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input)
                (localizedPhysicalTopOccurrence input m domain.graphEq c)) fuel
              (frame.cursorAt (alpha.symm j))).map
            (input.certified.localizedRerootCumulativeRule45Observable) := by
  obtain ⟨e, centerFixed, ligandMaps, signLaw⟩ := transport
  exact localizedPhysicalBranch_finalOccurrence_observable_eq
    input singleBonded acyclic noDouble m cfg c e i j mirror centerFixed ligandMaps signLaw
    domain coverage




theorem localizedPhysicalBranch_detected_transport_observable_eq
    (input : LocalizedUniversalReference.Input)
    (singleBonded : input.certified.moleculeGraph.SimpleBonded)
    (acyclic : input.certified.moleculeGraph.Acyclic)
    (noDouble :
      input.certified.certified.input.molecule.NoLocalizedDoubleBondRecords)
    (cfg : input.certified.detectedMultiCenterMolecule.Configuration)
    (c : input.certified.detectedMultiCenterMolecule.Center)
    (i j : Fin 4) (mirror : Bool)
    (transport : BranchTransport input.certified.detectedMultiCenterMolecule cfg c i j mirror)
    (domain : ActualGlobalPhysicalCalibratedDomain input.certified
      input.certified.detectedMultiCenterMolecule cfg c) :
    ∃ (frame : input.certified.LocalizedOccurrenceFourLigandFrame
        (LocalizedUniversalReference.carrierFuel input))
      (alpha : Equiv.Perm (Fin 4)),
      input.certified.localizedOccurrenceFourLigandFrame?
          (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
            domain.graphEq c) = some frame ∧
        (∀ index : Fin 4,
          (frame.cursorAt index).occurrence.1.node.current? =
            some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c (alpha index))) ∧
        (frame.cursorAt (alpha.symm i)).occurrence.1.node.current? =
          some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c i) ∧
        (frame.cursorAt (alpha.symm j)).occurrence.1.node.current? =
          some (input.certified.detectedMultiCenterMolecule.ligandAtomAt c j) ∧
        ∀ (fuel : Nat) (stage : LocalizedCumulativeRule45Stage),
          (input.certified.buildLocalizedRerootCumulativeRule45Key? stage
              (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
                domain.graphEq c)
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input)
                (localizedPhysicalTopOccurrence input
                  input.certified.detectedMultiCenterMolecule domain.graphEq c)) fuel
              (frame.cursorAt (alpha.symm i))).map
            (input.certified.localizedRerootCumulativeRule45Observable) =
          (input.certified.buildLocalizedRerootCumulativeRule45Key?
              (if mirror then reflectLocalizedCumulativeRule45Stage stage else stage)
              (localizedPhysicalTopOccurrence input input.certified.detectedMultiCenterMolecule
                domain.graphEq c)
              (input.certified.localizedDependencyView
                (LocalizedUniversalReference.referenceState input)
                (localizedPhysicalTopOccurrence input
                  input.certified.detectedMultiCenterMolecule domain.graphEq c)) fuel
              (frame.cursorAt (alpha.symm j))).map
            (input.certified.localizedRerootCumulativeRule45Observable) := by
  exact localizedPhysicalBranch_transport_observable_eq input singleBonded acyclic noDouble
    input.certified.detectedMultiCenterMolecule cfg c i j mirror transport domain
    (detectedMultiCenter_centers input.certified)

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedPhysicalBranchRelation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_correspondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_reachable_left
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_reachable_right
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_current_atoms
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_atomLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_rootDistance
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.forall₂_of_mem_imp
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_children
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.graphAutOfMultiCenterAut
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.coe_graphAutOfMultiCenterAut
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedPhysicalTwinData
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedPhysicalCalibratedData
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedPhysicalPairCase
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedReferenceDependencyLabel_eq_state
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_referenceState
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_reader_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.carrierOccurrence_history_length_eq_address_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_address_length_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_dependency_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_reader_relation
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_productionKey_observable_eq_proper
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_productionKey_observable_eq_mirror
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalTopCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalTopOccurrence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_localizedPhysicalTopOccurrence_frame_slotCorrespondence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_localizedPhysicalTwinData_of_terminalTwinLeaves
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_localizedPhysicalCalibratedData_of_calibratedCenter
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalPairCase_of_globalDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchLeftMembership
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ligandBranchReaches_ne_center
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_referenceState_globalDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_reader_relation_globalDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_productionKey_observable_eq_proper_globalDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranchRelation_productionKey_observable_eq_mirror_globalDomain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranch_finalOccurrence_observable_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranch_transport_observable_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedPhysicalBranch_detected_transport_observable_eq
