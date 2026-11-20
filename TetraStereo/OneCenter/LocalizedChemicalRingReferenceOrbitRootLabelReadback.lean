import TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitKeySeparation
import TetraStereo.OneCenter.LocalizedChemicalRingHereditaryTie
import TetraStereo.OneCenter.LocalizedChemicalRingPromotedChildMatch
import TetraStereo.OneCenter.LocalizedChemicalRingActualComparisonLabelMatch
import TetraStereo.OneCenter.LocalizedChemicalRingWitnessFactMatch
import TetraStereo.OneCenter.LocalizedChemicalRingSealedCursorReference
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2400000

/-!
Root comparison ties determine the actual auxiliary observations at the two short approaches
to atom 26. The auxiliary state is arbitrary. At each step the actual complete comparison
matches actual children, and molecular atomic numbers force the prescribed next child.
The two natural-boron candidates 27 and 37 are separated by the next sphere: only 27
has a carbon child. Their equal root labels are not treated as distinct.
Neither cursor correspondences nor generated labels are supplied. The final conclusions are
equal optional raw fact labels; presence, physical signs, and reference independence are not
asserted here.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootLabelReadback

open CertifiedLocalizedCIPInput DeclarativeCIP Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedActualBoundaryPathRealization
open LocalizedChemicalRingHereditaryTie LocalizedChemicalRingActualFullLabelMatch
open LocalizedChemicalRingDecodedRelation LocalizedChemicalRingPromotedChildMatch
open LocalizedChemicalRingActualComparisonLabelMatch
open LocalizedMarkedRetainedMolecularSelection LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedCanonicalFrame LocalizedMarkedRetainedStateReader
open LocalizedMarkedRetainedPromotedRanking
open LocalizedChemicalRingReferenceOrbitInput LocalizedChemicalRingReferenceOrbitKeySeparation
open LocalizedChemicalRingInheritedRefusalCases (referenceAt)
open LocalizedChemicalRingWitnessFactMatch
open RawLocalizedOxidoPathInvariant (exists_mem_of_forall₂_left)

noncomputable section
open scoped Classical

private abbrev Cursor := certified.LocalizedRerootCursor (retainedCarrierFuel certified)

private theorem children_nodes (x : Cursor)
    (incoming : LocalizedRerootCursorIncomingParent certified x)
    (real : x.occurrence.1.node.provenance = .realAtom) :
    ((certified.executableLocalizedRerootChildren x).map
      (fun child => child.occurrence.1.node)).Perm
        (certified.executableOfficialCIPChildren x.occurrence.1.node) := by
  obtain ⟨previous, previousEq, previousRoot, previousAddress, previousLength⟩ := incoming
  have maps : (certified.executableLocalizedRerootChildren x).map
      (fun child => child.occurrence.1.node) =
      (certified.intendedLocalizedRerootChildFrames x).map (fun frame => frame.node) := by
    simpa only [List.map_map] using congrArg
      (List.map (fun frame : certified.LocalizedCIPOccurrenceFrame => frame.node))
      (certified.executableLocalizedRerootChildren_map x)
  rw [maps]
  exact certified.intendedLocalizedRerootChildFrames_nodes_perm_executable x
    ((certified.mem_localizedOccurrences_iff _ _).mp x.occurrence.2)
    previous previousEq previousRoot previousAddress previousLength
    (isDuplicateLeaf_of_real certified real)
    (certified.localizedOccurrences_remaining_pos_of_atomCount_le
      (Nat.le_succ _) x.occurrence.1 x.occurrence.2)

private theorem child_incoming (x child : Cursor)
    (incoming : LocalizedRerootCursorIncomingParent certified x)
    (edge : child ∈ certified.executableLocalizedRerootChildren x) :
    LocalizedRerootCursorIncomingParent certified child := by
  have valid := certified.localizedRerootCursorValid_of_incoming x incoming
  obtain ⟨previous, prev, _, _, shorter⟩ := incoming
  obtain ⟨drop, length, root, back, _⟩ := certified.outward_edge x child valid previous prev
    (by omega) edge
  exact ⟨x.occurrence, back, root.symm, drop.symm, length.symm⟩

private theorem matched_atomLabel (state : OccurrenceAuxState) (x y : Cursor)
    (matched : RebuildMatch rootData.target (rawStateView certified state rootData.target) x y) :
    graph.officialNodeAtomLabel x.occurrence.1.node =
      graph.officialNodeAtomLabel y.occurrence.1.node := by
  obtain ⟨left, right, builtL, builtR, tied⟩ := matched
  obtain ⟨treeL, treeR, sourceL, sourceR, realL, realR, same⟩ :=
    full_tie_same_observations _ _ _ _ _ _ _ _ builtL builtR
      (congrArg ConstitutionalRule5Comparison.ordering tied)
  exact related_atomLabel (shape_eq_of_observation_eq treeL treeR same) realL realR
    (shapePositionCursorRelation_sources _ sourceL sourceR)

/-- Actual matched cursors with the specified root-boundary payloads. -/
def PathMatch (state : OccurrenceAuxState) (left right : List (Fin 46)) : Prop :=
  ∃ x y : Cursor,
    LocalizedRerootCursorIncomingParent certified x ∧
    LocalizedRerootCursorIncomingParent certified y ∧
    x.occurrence.1.node = boundaryNode [(0 : Fin 46)] left ∧
    y.occurrence.1.node = boundaryNode [(0 : Fin 46)] right ∧
    RebuildMatch rootData.target (rawStateView certified state rootData.target) x y

private theorem matched_child (state : OccurrenceAuxState) (x y : Cursor)
    (incomingL : LocalizedRerootCursorIncomingParent certified x)
    (realL : x.occurrence.1.node.provenance = .realAtom)
    (matched : RebuildMatch rootData.target (rawStateView certified state rootData.target) x y)
    (next : OfficialCIPNode certified.Atom)
    (edge : next ∈ certified.executableOfficialCIPChildren x.occurrence.1.node) :
    ∃ childL childR : Cursor,
      childL ∈ certified.executableLocalizedRerootChildren x ∧
      childR ∈ certified.executableLocalizedRerootChildren y ∧
      childL.occurrence.1.node = next ∧
      RebuildMatch rootData.target (rawStateView certified state rootData.target) childL childR := by
  have wanted := (children_nodes x incomingL realL).mem_iff.mpr edge
  obtain ⟨childL, childMemL, childNodeL⟩ := List.mem_map.mp wanted
  obtain ⟨leftKey, rightKey, builtL, builtR, tied⟩ := matched
  obtain ⟨frame, permutation, pairs⟩ := full_tie_children rootData.target
    (rawStateView certified state rootData.target) _ _ x y leftKey rightKey builtL builtR
    (congrArg ConstitutionalRule5Comparison.ordering tied)
  obtain ⟨childR, childMemR, pair⟩ := exists_mem_of_forall₂_left pairs
    (permutation.mem_iff.mp childMemL)
  exact ⟨childL, childR, childMemL, childMemR, childNodeL, pair⟩

private theorem matched_atomicNumber (state : OccurrenceAuxState) (x y : Cursor)
    (matched : RebuildMatch rootData.target (rawStateView certified state rootData.target) x y)
    (a b : Fin 46) (atL : x.occurrence.1.node.current? = some a)
    (atR : y.occurrence.1.node.current? = some b) : graph.atomZ a = graph.atomZ b := by
  have atomicEq := congrArg (fun label => (ofLex label).1) (matched_atomLabel state x y matched)
  dsimp only at atomicEq
  rw [MoleculeGraph.officialNodeAtomLabel_first_eq_atomZ_of_current graph _ a atL,
    MoleculeGraph.officialNodeAtomLabel_first_eq_atomZ_of_current graph _ b atR] at atomicEq
  exact atomicEq

/-- The complete comparison itself selects the next matched child; the only finite
disambiguation condition is uniqueness of its atomic number among actual right neighbors. -/
theorem pathMatch_step (state : OccurrenceAuxState) (left right : List (Fin 46))
    (a b currentR : Fin 46)
    (atRight : (boundaryNode [(0 : Fin 46)] right).current? = some currentR)
    (edgeLeft : (boundaryNode [(0 : Fin 46)] left).extend a 0 ∈
      certified.executableOfficialCIPChildren (boundaryNode [(0 : Fin 46)] left))
    (unique : ∀ atom, graph.Adj currentR atom →
      (boundaryNode [(0 : Fin 46)] right).parent? ≠ some atom →
      graph.atomZ atom = graph.atomZ a → atom = b)
    (freshLeft : a ∉ [(0 : Fin 46)] ++ left)
    (freshRight : b ∉ [(0 : Fin 46)] ++ right)
    (matched : PathMatch state left right) :
    PathMatch state (left ++ [a]) (right ++ [b]) := by
  obtain ⟨x, y, incomingL, incomingR, nodeL, nodeR, matched⟩ := matched
  have realL : x.occurrence.1.node.provenance = .realAtom := by rw [nodeL]; rfl
  have realR : y.occurrence.1.node.provenance = .realAtom := by rw [nodeR]; rfl
  obtain ⟨childL, childR, childMemL, childMemR, childNodeL, pair⟩ :=
    matched_child state x y incomingL realL matched _ (by rw [nodeL]; exact edgeLeft)
  have officialR := (children_nodes y incomingR realR).mem_iff.mp
    (List.mem_map.mpr ⟨childR, childMemR, rfl⟩)
  rw [nodeR] at officialR
  obtain ⟨atom, childNodeR, adjacent, notParent⟩ :=
    (mem_executableOfficialCIPChildren_iff certified single_bonded _ atRight rfl _).mp officialR
  have atL : childL.occurrence.1.node.current? = some a := by rw [childNodeL]; rfl
  have atR : childR.occurrence.1.node.current? = some atom := by rw [childNodeR]; rfl
  have atomicEq := matched_atomicNumber state childL childR pair a atom atL atR
  have atomEq := unique atom adjacent notParent atomicEq.symm
  subst atom
  exact ⟨childL, childR, child_incoming x childL incomingL childMemL,
    child_incoming y childR incomingR childMemR,
    childNodeL.trans (extend_boundaryNode freshLeft),
    childNodeR.trans (extend_boundaryNode freshRight), pair⟩

/-- A further actual comparison step transports a probe child. This resolves siblings
whose root atom labels agree but whose next constitutional sphere differs. -/
theorem pathMatch_step_probe (state : OccurrenceAuxState) (left right : List (Fin 46))
    (a b currentR probe : Fin 46)
    (atRight : (boundaryNode [(0 : Fin 46)] right).current? = some currentR)
    (edgeLeft : (boundaryNode [(0 : Fin 46)] left).extend a 0 ∈
      certified.executableOfficialCIPChildren (boundaryNode [(0 : Fin 46)] left))
    (probeEdge : ((boundaryNode [(0 : Fin 46)] left).extend a 0).extend probe 0 ∈
      certified.executableOfficialCIPChildren ((boundaryNode [(0 : Fin 46)] left).extend a 0))
    (freshLeft : a ∉ [(0 : Fin 46)] ++ left)
    (freshCandidates : ∀ atom, graph.Adj currentR atom →
      (boundaryNode [(0 : Fin 46)] right).parent? ≠ some atom →
      atom ∉ [(0 : Fin 46)] ++ right)
    (unique : ∀ atom, graph.Adj currentR atom →
      (boundaryNode [(0 : Fin 46)] right).parent? ≠ some atom →
      graph.atomZ atom = graph.atomZ a →
      (∃ neighbor, graph.Adj atom neighbor ∧ graph.atomZ neighbor = graph.atomZ probe) → atom = b)
    (matched : PathMatch state left right) :
    PathMatch state (left ++ [a]) (right ++ [b]) := by
  obtain ⟨x, y, incomingL, incomingR, nodeL, nodeR, matched⟩ := matched
  have realL : x.occurrence.1.node.provenance = .realAtom := by rw [nodeL]; rfl
  have realR : y.occurrence.1.node.provenance = .realAtom := by rw [nodeR]; rfl
  obtain ⟨childL, childR, childMemL, childMemR, childNodeL, pair⟩ :=
    matched_child state x y incomingL realL matched _ (by rw [nodeL]; exact edgeLeft)
  have officialR := (children_nodes y incomingR realR).mem_iff.mp
    (List.mem_map.mpr ⟨childR, childMemR, rfl⟩)
  rw [nodeR] at officialR
  obtain ⟨atom, childNodeR, adjacent, notParent⟩ :=
    (mem_executableOfficialCIPChildren_iff certified single_bonded _ atRight rfl _).mp officialR
  have atL : childL.occurrence.1.node.current? = some a := by rw [childNodeL]; rfl
  have atR : childR.occurrence.1.node.current? = some atom := by rw [childNodeR]; rfl
  have atomicEq := matched_atomicNumber state childL childR pair a atom atL atR
  have incomingChildL := child_incoming x childL incomingL childMemL
  have incomingChildR := child_incoming y childR incomingR childMemR
  have payloadL := childNodeL.trans (extend_boundaryNode freshLeft)
  have payloadR := childNodeR.trans (extend_boundaryNode (freshCandidates atom adjacent notParent))
  have realChildL : childL.occurrence.1.node.provenance = .realAtom := by rw [payloadL]; rfl
  have realChildR : childR.occurrence.1.node.provenance = .realAtom := by rw [payloadR]; rfl
  obtain ⟨probeL, probeR, _, probeMemR, probeNodeL, probePair⟩ :=
    matched_child state childL childR incomingChildL realChildL pair _
      (by rw [childNodeL]; exact probeEdge)
  have probeOfficialR := (children_nodes childR incomingChildR realChildR).mem_iff.mp
    (List.mem_map.mpr ⟨probeR, probeMemR, rfl⟩)
  obtain ⟨neighbor, probeNodeR, probeAdjacent, _⟩ :=
    (mem_executableOfficialCIPChildren_iff certified single_bonded _ atR realChildR _).mp probeOfficialR
  have probeAtL : probeL.occurrence.1.node.current? = some probe := by rw [probeNodeL]; rfl
  have probeAtR : probeR.occurrence.1.node.current? = some neighbor := by rw [probeNodeR]; rfl
  have probeZ := matched_atomicNumber state probeL probeR probePair probe neighbor probeAtL probeAtR
  have atomEq := unique atom adjacent notParent atomicEq.symm ⟨neighbor, probeAdjacent, probeZ.symm⟩
  subst atom
  exact ⟨childL, childR, incomingChildL, incomingChildR, payloadL, payloadR, pair⟩

private theorem root_history : rootData.target.1.node.history = [(0 : Fin 46)] := by
  apply List.map_injective_iff.mpr Fin.val_injective
  exact (LocalizedMarkedCarrierLookup.lookup?_sound certified _ _ rootData.found).history

private theorem root_address : rootData.target.1.address = [] := by
  have address := (certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded rootData.target)).sourceAddress
  rw [address]
  simp [CertifiedLocalizedCIPInput.canonicalAddress, root_history]

private theorem root_root : rootData.target.1.root = (0 : Fin 46) := by
  have head := (certified.legitimateOccurrence_transport single_bonded 1
    (certified.carrierOccurrence_legitimate single_bonded rootData.target)).sourceHead
  simpa [root_history] using head.symm

abbrev rootUnit : DetectedOccurrence graph :=
  ⟨certified.molecularFrameUnit rootData.target.1, rootData.detected⟩

private theorem slot_current (state : OccurrenceAuxState) (slot : Fin 4) (a : Fin 46)
    (atAtom : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData slot = a) :
    ((frames certified single_bonded state rootData.target rootData.real rootUnit rfl).frame.cursorAt
      slot).occurrence.1.node.current? = some a := by
  have frameEq : (frames certified single_bonded state rootData.target rootData.real rootUnit rfl).frame =
      rootData.frame := Option.some.inj ((frames certified single_bonded state rootData.target
        rootData.real rootUnit rfl).frameComputed.symm.trans rootData.frameExec)
  have mapped : (((frames certified single_bonded state rootData.target rootData.real rootUnit
      rfl).frame.cursorAt slot).occurrence.1.node.current?).map Fin.val = some a.val := by
    change LocalizedChemicalRingFrameReadback.atomAt certified _ slot = some a.val
    rw [frameEq, rootData.atomAt_eq]
    exact congrArg (fun x : Fin 46 => some x.val) atAtom
  cases found : ((frames certified single_bonded state rootData.target rootData.real rootUnit
      rfl).frame.cursorAt slot).occurrence.1.node.current? with
  | none => simp [found] at mapped
  | some b =>
      simp only [found, Option.map_some, Option.some.injEq] at mapped
      exact congrArg some (Fin.ext mapped)

private theorem root_slot (state : OccurrenceAuxState) (slot : Fin 4) (a : Fin 46)
    (atAtom : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData slot = a) :
    let cursor := (frames certified single_bonded state rootData.target rootData.real rootUnit rfl).frame.cursorAt slot
    LocalizedRerootCursorIncomingParent certified cursor ∧
      cursor.occurrence.1.node = boundaryNode [(0 : Fin 46)] [a] := by
  let frame := frames certified single_bonded state rootData.target rootData.real rootUnit rfl
  have computed : certified.localizedOccurrenceFourLigandFrame? rootData.target = some frame.frame := by
    rw [← certified.localizedNoDoubleFourLigandFrameExec?_eq_localizedOccurrenceFourLigandFrame?]
    exact frame.frameComputed
  have present : frame.frame.cursorAt slot ∈ frame.frame.cursors :=
    List.get_mem frame.frame.cursors (Fin.cast frame.frame.length_eq.symm slot)
  have outward := certified.localizedOccurrenceFourLigandFrame_cursor_mem_neighborFrames
    rootData.target frame.frame computed _ present
  rw [certified.localizedRerootNeighborFrames_eq_outwardChildFrames_of_address_nil
    rootData.target root_address] at outward
  have targetNode : rootData.target.1.node = OfficialCIPNode.root rootData.target.1.root := by
    have eq := certified.declarativeLocalizedOccurrence_eq_root_of_address_nil
      ((certified.mem_localizedOccurrences_iff _ _).mp rootData.target.2) root_address
    simpa using congrArg (fun occurrence => occurrence.node) eq
  have targetCurrent : rootData.target.1.node.current? = some rootData.target.1.root := by
    rw [targetNode]; rfl
  obtain ⟨neighbor, childSlot, nodeEq, atNeighbor, rootEq, addressEq, _, _, _⟩ :=
    certified.simpleBond_outwardFrame_extend_zero single_bonded rootData.target targetCurrent
      rootData.real _ outward
  have neighborEq : neighbor = a := Option.some.inj
    (atNeighbor.symm.trans (slot_current state slot a atAtom))
  subst neighbor
  have previous := certified.localizedOccurrenceFourLigandFrame_cursor_previous
    rootData.target frame.frame computed _ present
  refine ⟨⟨rootData.target, previous, rootEq.symm, ?_, ?_⟩, ?_⟩
  · change rootData.target.1.address = (frame.frame.cursorAt slot).occurrence.1.address.dropLast
    simp only [addressEq, List.dropLast_concat]
  · change rootData.target.1.address.length + 1 =
      (frame.frame.cursorAt slot).occurrence.1.address.length
    simp only [addressEq, List.length_append, List.length_singleton]
  · rw [nodeEq, targetNode, root_root]
    have different : a ≠ (0 : Fin 46) := by
      have adj := physical.ligandAtomAt_adj rootCenter (rootData.ligandOf slot)
      change graph.Adj 0 (referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData slot) at adj
      rw [atAtom] at adj
      intro same
      rw [same] at adj
      simp [MoleculeGraph.Adj, graph.bond_self] at adj
    exact extend_eq_boundaryNode_history (by
      change a ∉ [(0 : Fin 46)]
      simpa only [List.mem_singleton] using different)

/-- An equality of actual root prior keys starts an actual hereditary match. -/
theorem root_tie_pathMatch (state : OccurrenceAuxState) (left right : Fin 4) (a b : Fin 46)
    (atLeft : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData left = a)
    (atRight : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData right = b)
    (tie : rawStateKeys certified single_bonded state rootData.target rootData.real rootUnit rfl left =
      rawStateKeys certified single_bonded state rootData.target rootData.real rootUnit rfl right) :
    PathMatch state [a] [b] := by
  let frame := frames certified single_bonded state rootData.target rootData.real rootUnit rfl
  have full := frame.fullOrdering (rawStateDescriptorMap_tetrahedral certified state)
    single_bonded rootUnit rfl left right
  change frame.retainedKeys rootUnit left = frame.retainedKeys rootUnit right at tie
  rw [tie, (completeLigandRule5Key_compare_eq_iff _ _).mpr rfl] at full
  have built (slot : Fin 4) := frame_uniform_built (rawStateDescriptorMap certified state)
    rootData.target frame slot
  have leftBuilt := built left
  have rightBuilt := built right
  rw [(frame.stages left).a.sourceEq] at leftBuilt
  rw [(frame.stages right).a.sourceEq] at rightBuilt
  have leftFacts := root_slot state left a atLeft
  have rightFacts := root_slot state right b atRight
  refine ⟨frame.frame.cursorAt left, frame.frame.cursorAt right, leftFacts.1, rightFacts.1,
    leftFacts.2, rightFacts.2, frame.compounds left, frame.compounds right, ?_, ?_,
    through_tie_of_ordering_eq certified _ _ full⟩
  · simpa only [compiler, rawStateView_eq_molecularView, molecularReader] using leftBuilt
  · simpa only [compiler, rawStateView_eq_molecularView, molecularReader] using rightBuilt

/-- Hereditary matching at a detected terminal gives the actual raw fact-label equality.
The optional observations may both be absent. -/
theorem pathMatch_fact_labels (state : OccurrenceAuxState) (left right : List (Fin 46))
    (lastL : left.getLast? = some (26 : Fin 46)) (lastR : right.getLast? = some (26 : Fin 46))
    (matched : PathMatch state left right) :
    (state.factAt? (rawPathNode (0 : Fin 46) left)).map factLabel =
      (state.factAt? (rawPathNode (0 : Fin 46) right)).map factLabel := by
  obtain ⟨x, y, _, _, nodeL, nodeR, keyL, keyR, builtL, builtR, tied⟩ := matched
  have labels := full_tie_root_labels _ _ _ _ _ _ _ _ builtL builtR
    (congrArg ConstitutionalRule5Comparison.ordering tied)
  have detected : IsDetectedCenter graph (26 : Fin 46) := by
    apply (graph.isTetrahedralCenter_iff_neighborFinset_card _).mp
    apply (graph.mem_tetrahedralCenterSet _).mp
    rw [detected_inventory]
    decide
  have leftRead := reader_eq_path_fact single_bonded state rootData.target root_address x left (26 : Fin 46) lastL
    detected (by rw [root_root]; exact nodeL)
  have rightRead := reader_eq_path_fact single_bonded state rootData.target root_address y right (26 : Fin 46) lastR
    detected (by rw [root_root]; exact nodeR)
  rw [root_root] at leftRead rightRead
  exact leftRead.symm.trans (labels.trans rightRead)

private theorem extension_mem (node : OfficialCIPNode certified.Atom) (current next : Fin 46)
    (atCurrent : node.current? = some current) (real : node.provenance = .realAtom)
    (adjacent : graph.Adj current next) (notParent : node.parent? ≠ some next) :
    node.extend next 0 ∈ certified.executableOfficialCIPChildren node :=
  (mem_executableOfficialCIPChildren_iff certified single_bonded node atCurrent real _).mpr
    ⟨next, rfl, adjacent, notParent⟩

/-- Root O16-arm ties force equality at the two actual occurrences of center 26 reached
through 28/32/27 and 29/33/27. No generated-state or successful-label premise is supplied. -/
theorem o_labels_of_root_tie (state : OccurrenceAuxState) (left right : Fin 4)
    (atLeft : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData left = (28 : Fin 46))
    (atRight : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData right = (29 : Fin 46))
    (tie : rawStateKeys certified single_bonded state rootData.target rootData.real rootUnit rfl left =
      rawStateKeys certified single_bonded state rootData.target rootData.real rootUnit rfl right) :
    (state.factAt? (nodeOf [0, 28, 32, 27, 26])).map factLabel =
      (state.factAt? (nodeOf [0, 29, 33, 27, 26])).map factLabel := by
  have start := root_tie_pathMatch state left right 28 29 atLeft atRight tie
  have first := pathMatch_step state [28] [29] 32 33 29 rfl
    (extension_mem _ 28 32 rfl rfl (by decide +kernel) (by decide))
    (by intro atom; fin_cases atom <;> decide +kernel)
    (by decide) (by decide) start
  have probeEdge : ((boundaryNode [(0 : Fin 46)] [28, 32]).extend 27 0).extend 26 0 ∈
      certified.executableOfficialCIPChildren ((boundaryNode [(0 : Fin 46)] [28, 32]).extend 27 0) := by
    rw [extend_boundaryNode (show (27 : Fin 46) ∉ [(0 : Fin 46)] ++ [28, 32] by decide)]
    exact extension_mem _ 27 26 rfl rfl (by decide +kernel) (by decide)
  have second := pathMatch_step_probe state [28, 32] [29, 33] 27 27 33 26 rfl
    (extension_mem _ 32 27 rfl rfl (by decide +kernel) (by decide)) probeEdge
    (by decide) (by intro atom; fin_cases atom <;> decide +kernel)
    (by intro atom; fin_cases atom <;> decide +kernel) first
  have third := pathMatch_step state [28, 32, 27] [29, 33, 27] 26 26 27 rfl
    (extension_mem _ 27 26 rfl rfl (by decide +kernel) (by decide))
    (by intro atom; fin_cases atom <;> decide +kernel)
    (by decide) (by decide) second
  exact pathMatch_fact_labels state [28, 32, 27, 26] [29, 33, 27, 26] rfl rfl third

/-- Root O18-arm ties force equality at the two actual occurrences of center 26 reached
through 30/34 and 31/35, in the same arbitrary raw state. -/
theorem q_labels_of_root_tie (state : OccurrenceAuxState) (left right : Fin 4)
    (atLeft : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData left = (30 : Fin 46))
    (atRight : referenceAt certified mol rootCenter (canonicalCenterRoot 0) rootData right = (31 : Fin 46))
    (tie : rawStateKeys certified single_bonded state rootData.target rootData.real rootUnit rfl left =
      rawStateKeys certified single_bonded state rootData.target rootData.real rootUnit rfl right) :
    (state.factAt? (nodeOf [0, 30, 34, 26])).map factLabel =
      (state.factAt? (nodeOf [0, 31, 35, 26])).map factLabel := by
  have start := root_tie_pathMatch state left right 30 31 atLeft atRight tie
  have first := pathMatch_step state [30] [31] 34 35 31 rfl
    (extension_mem _ 30 34 rfl rfl (by decide +kernel) (by decide))
    (by intro atom; fin_cases atom <;> decide +kernel)
    (by decide) (by decide) start
  have second := pathMatch_step state [30, 34] [31, 35] 26 26 35 rfl
    (extension_mem _ 34 26 rfl rfl (by decide +kernel) (by decide))
    (by intro atom; fin_cases atom <;> decide +kernel)
    (by decide) (by decide) first
  exact pathMatch_fact_labels state [30, 34, 26] [31, 35, 26] rfl rfl second

end
end TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootLabelReadback

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootLabelReadback.pathMatch_step
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootLabelReadback.pathMatch_step_probe
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootLabelReadback.root_tie_pathMatch
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootLabelReadback.pathMatch_fact_labels
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootLabelReadback.o_labels_of_root_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingReferenceOrbitRootLabelReadback.q_labels_of_root_tie
