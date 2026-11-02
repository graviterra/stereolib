import TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource
import TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3RecursiveKey
import TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativeRule3ObserverFrame
import TetraStereo.UniversalProof.SourceNativeRule3ObserverFuelCompletenessProofs.SourceNativeRule3ObserverFuelCompleteness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000




























namespace TetraStereo.UniversalProof.SourceNativePlanarTetrahedralKeyFrameProofs.SourceNativePlanarTetrahedralKeyFrame

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.SourceNativePlanarRule3UnitProofs.SourceNativePlanarRule3Unit
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3RecursiveKey
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativeRule3ObserverFrame
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFuelCompletenessProofs.SourceNativeRule3ObserverFuelCompleteness
open TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource
  (source_structure carbonNode realC5Node cisNodeResult cisUnit reverseCisUnit
   actual_planar_unit actual_reverse_planar_unit roots target actual_ligand_frame
   actual_four_real_roots real_C5_node_resolved actual_carbon_child_seqcis firstCursor
   left_senior nonterminal_carbon_compiler rootNode)

/-- Local alias for the NEW72 actual source.  Declared locally so no other opened namespace can
make the name ambiguous. -/
abbrev source : AuthoritativeChemicalInput :=
  TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource.source

/-- Local alias for the actual atom type of the NEW72 source. -/
abbrev Atom := source.AromaticCanonicalAtom

local instance : NeZero source.molecule.atomCount := ⟨by change (9 : Nat) ≠ 0; decide⟩

/-! ## 1. The concrete source-native planar observer -/



noncomputable def planarObserver : Rule3Observer source :=
  { observe := aromaticCanonicalPlanarRule3Node? source
    NodeOutcome := CanonicalAromaticCanonicalPlanarRule3NodeOutcome source
    nodeExact := aromaticCanonicalPlanarRule3Node?_eq_some_iff_canonical source }

/-! ## 2. Actual totality from the unique ordinary double bond and the actual planar units -/

/-- The only ordinary source double bond of this actual molecule is `1--5`. -/
theorem ordinary_double_bond_pairs :
    ∀ parent current : Atom,
      source.AromaticCanonicalOrdinaryDoubleBond parent current ↔
        (parent = 1 ∧ current = 5) ∨ (parent = 5 ∧ current = 1) := by
  unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent
  decide +kernel



theorem planar_unit_resolved_of_ordinary (parent current : Atom)
    (ordinary : source.AromaticCanonicalOrdinaryDoubleBond parent current) :
    ∃ unit, aromaticCanonicalPlanarRule3Unit? source parent current = some unit := by
  rcases (ordinary_double_bond_pairs parent current).mp ordinary with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨cisUnit, actual_planar_unit⟩
  · exact ⟨reverseCisUnit, actual_reverse_planar_unit⟩

/-- The actual planar observer is total: every node has a resolved reading, since the sole genuine
ordinary double bond is resolved and every other node is the negative nonunit. -/
theorem planarObserver_total : ObserverTotal planarObserver := by
  classical
  intro node
  change ∃ outcome, aromaticCanonicalPlanarRule3Node? source node = some outcome
  by_cases edge : source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node
  · rcases edge with ⟨real, current, parent, currentEq, parentEq, ordinary⟩
    obtain ⟨unit, unitComputed⟩ := planar_unit_resolved_of_ordinary parent current ordinary
    refine ⟨some { left := parent, right := current, unit := unit }, ?_⟩
    exact (aromaticCanonicalPlanarRule3Node?_eq_some_some_iff_canonical source node
      { left := parent, right := current, unit := unit }).mpr
      ⟨real, currentEq, parentEq, ordinary,
        (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical source parent current unit).mp
          unitComputed⟩
  · exact ⟨none, aromaticCanonicalPlanarRule3Node?_eq_some_none_of_not_edge source node edge⟩

/-! ## 3. Actual validity of the returned four-ligand root frame -/

/-- The four returned real original-occurrence cursors form an actual valid ligand frame. -/
theorem roots_valid :
    ∀ cursor ∈ roots, source.AromaticCanonicalRerootCursorValid cursor :=
  source.aromaticCanonicalOccurrenceLigandFrame_cursor_valid target roots actual_ligand_frame

/-! ## 4. Actual four raw keys with the independent recursive judgment -/

private theorem canonicalKeyList_length {carrierFuel fuel : Nat}
    {NodeOutcome :
      OfficialCIPNode Atom → Option source.AromaticCanonicalRule3SpatialNodeResult → Prop}
    {cursors : List (source.AromaticCanonicalRerootCursor carrierFuel)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived :
      source.CanonicalAromaticCanonicalRule3SpatialKeyWithList NodeOutcome fuel cursors keys) :
    keys.length = cursors.length :=
  match derived with
  | .nil _ => rfl
  | .cons _ tail => congrArg Nat.succ (canonicalKeyList_length tail)



theorem actual_four_planar_raw_keys :
    ∃ rawKeys : List source.AromaticCanonicalUncancelledRule3SpatialKey,
      roots.mapM
          (source.buildAromaticCanonicalRule3SpatialKeyWith? planarObserver.observe 4) =
        some rawKeys ∧
      source.CanonicalAromaticCanonicalRule3SpatialKeyWithList
        (CanonicalAromaticCanonicalPlanarRule3NodeOutcome source) 4 roots rawKeys ∧
      rawKeys.length = 4 := by
  obtain ⟨rawKeys, computed, meaning⟩ :=
    exists_observer_key_list_at_or_above_twice (carrierFuel := 1) (evaluationFuel := 4)
      planarObserver planarObserver_total roots roots_valid (by decide)
  exact ⟨rawKeys, computed, meaning, by
    rw [canonicalKeyList_length meaning, actual_four_real_roots.1]⟩

/-- Every returned root has an actual compiled recursive planar key with the independent judgment. -/
theorem actual_root_planar_key (cursor : source.AromaticCanonicalRerootCursor 1)
    (present : cursor ∈ roots) :
    ∃ key, buildAromaticCanonicalPlanarRule3Key? source 4 cursor = some key ∧
      CanonicalAromaticCanonicalPlanarRule3Key source 4 cursor key := by
  obtain ⟨key, computed⟩ :=
    exists_observer_key_at_or_above_twice (carrierFuel := 1) (evaluationFuel := 4)
      planarObserver planarObserver_total cursor (roots_valid cursor present) (by decide)
  have keyComputed :
      buildAromaticCanonicalPlanarRule3Key? source 4 cursor = some key := by
    change source.buildAromaticCanonicalRule3SpatialKeyWith?
      (aromaticCanonicalPlanarRule3Node? source) 4 cursor = some key
    exact computed
  exact ⟨key, keyComputed,
    buildAromaticCanonicalPlanarRule3Key?_sound source 4 cursor key keyComputed⟩

/-! ## 5. Actual reachable-node observations (stage-1 conservation) -/

/-- A node whose concrete current/parent pair is not the sole ordinary double bond is not an
ordinary-double-bond node. -/
theorem not_edge_of_current_parent_ne (node : OfficialCIPNode Atom)
    (current parent : Atom) (currentEq : node.current? = some current)
    (parentEq : node.parent? = some parent)
    (notOrdinary : ¬ source.AromaticCanonicalOrdinaryDoubleBond parent current) :
    ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge node := by
  rintro ⟨_, otherCurrent, otherParent, otherCurrentEq, otherParentEq, ordinary⟩
  have currentIdentity : otherCurrent = current :=
    Option.some.inj (otherCurrentEq.symm.trans currentEq)
  have parentIdentity : otherParent = parent :=
    Option.some.inj (otherParentEq.symm.trans parentEq)
  rw [currentIdentity, parentIdentity] at ordinary
  exact notOrdinary ordinary

theorem carbonNode_not_edge :
    ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge carbonNode :=
  not_edge_of_current_parent_ne carbonNode 1 0 rfl rfl (by
    unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent
    decide +kernel)

/-- The C1 root reads as the negative nonunit; its children are resolved recursively. -/
theorem c1_node_reader :
    aromaticCanonicalPlanarRule3Node? source carbonNode = some none :=
  aromaticCanonicalPlanarRule3Node?_eq_some_none_of_not_edge source carbonNode carbonNode_not_edge

theorem not_edge_terminal (atom : Atom)
    (notOrdinary : ¬ source.AromaticCanonicalOrdinaryDoubleBond (0 : Atom) atom) :
    ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge (rootNode.extend atom 0) :=
  not_edge_of_current_parent_ne (rootNode.extend atom 0) atom 0 rfl rfl notOrdinary

/-- The terminal real ligands F (2), Br (3) and I (4) all read as the negative nonunit. -/
theorem terminal_root_readers :
    aromaticCanonicalPlanarRule3Node? source (rootNode.extend 2 0) = some none ∧
    aromaticCanonicalPlanarRule3Node? source (rootNode.extend 3 0) = some none ∧
    aromaticCanonicalPlanarRule3Node? source (rootNode.extend 4 0) = some none := by
  refine ⟨?_, ?_, ?_⟩
  · exact aromaticCanonicalPlanarRule3Node?_eq_some_none_of_not_edge source (rootNode.extend 2 0)
      (not_edge_terminal 2 (by
        unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent; decide +kernel))
  · exact aromaticCanonicalPlanarRule3Node?_eq_some_none_of_not_edge source (rootNode.extend 3 0)
      (not_edge_terminal 3 (by
        unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent; decide +kernel))
  · exact aromaticCanonicalPlanarRule3Node?_eq_some_none_of_not_edge source (rootNode.extend 4 0)
      (not_edge_terminal 4 (by
        unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent; decide +kernel))

/-- The duplicate C5 child is a multiple-bond duplicate node, hence neutral for Rule 3. -/
theorem duplicate_C5_provenance :
    (carbonNode.extend 5 1).provenance =
      OfficialCIPNodeProvenance.multipleBondDuplicate carbonNode.depth :=
  OfficialCIPNode.childProvenance_copy_pos (copyIndex := 1) carbonNode 5 (by decide)

theorem duplicate_C5_not_edge :
    ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge (carbonNode.extend 5 1) := by
  rintro ⟨real, _⟩
  rw [duplicate_C5_provenance] at real
  exact absurd real (by decide +kernel)

/-- The duplicate C5 child reads as the negative nonunit despite bearing atom 5. -/
theorem duplicate_C5_node_reader :
    aromaticCanonicalPlanarRule3Node? source (carbonNode.extend 5 1) = some none :=
  aromaticCanonicalPlanarRule3Node?_eq_some_none_of_not_edge source _
    duplicate_C5_not_edge

theorem cl6_not_edge :
    ¬ source.AromaticCanonicalRule3NodeHasOrdinaryDoubleBondEdge (carbonNode.extend 6 0) :=
  not_edge_of_current_parent_ne (carbonNode.extend 6 0) 6 1 rfl rfl (by
    unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent
    decide +kernel)

/-- The C1 ligand terminal Cl6 reads as the negative nonunit. -/
theorem cl6_node_reader :
    aromaticCanonicalPlanarRule3Node? source (carbonNode.extend 6 0) = some none :=
  aromaticCanonicalPlanarRule3Node?_eq_some_none_of_not_edge source _ cl6_not_edge



theorem real_C5_node_outcome :
    CanonicalAromaticCanonicalPlanarRule3NodeOutcome source realC5Node (some cisNodeResult) :=
  (aromaticCanonicalPlanarRule3Node?_eq_some_some_iff_canonical source realC5Node cisNodeResult).mp
    real_C5_node_resolved

/-- Node-reading facts at the C1 subtree: the root is negative, the real C5 child reads `seqcis`,
and the duplicate C5 and Cl6 children are neutral.  Returned-key event membership remains open. -/
theorem c1_children_observation_conservation :
    aromaticCanonicalPlanarRule3Node? source carbonNode = some none ∧
    aromaticCanonicalPlanarRule3Node? source realC5Node = some (some cisNodeResult) ∧
    aromaticCanonicalPlanarRule3Node? source (carbonNode.extend 5 1) = some none ∧
    aromaticCanonicalPlanarRule3Node? source (carbonNode.extend 6 0) = some none :=
  ⟨c1_node_reader, real_C5_node_resolved, duplicate_C5_node_reader, cl6_node_reader⟩

/-- The actual C1 child frame contains a child with the full `[5, 1, 0]` history whose node reading
is `seqcis`.  This establishes a child reading, not its propagation into a returned key. -/
theorem c1_child_seqcis_retained :
    ∃ child ∈ source.aromaticCanonicalRerootChildren (firstCursor 0),
      child.occurrence.1.node.history = [5, 1, 0] ∧
      aromaticCanonicalPlanarRule3Node? source child.occurrence.1.node =
        some (some cisNodeResult) := by
  obtain ⟨child, present, history, _, resolved⟩ := actual_carbon_child_seqcis
  exact ⟨child, present, history, resolved⟩

/-- The positive node result identifies the actual physical `1--5` unit. -/
theorem cis_unit_physical_id :
    cisNodeResult.physicalUnitId = source.aromaticCanonicalRule3PhysicalUnitId 1 5 := rfl

/-- Forward and reverse `seqcis` observations share the same traversal-independent physical unit. -/
theorem reverse_cis_same_physical_id :
    source.aromaticCanonicalRule3PhysicalUnitId 5 1 =
      source.aromaticCanonicalRule3PhysicalUnitId 1 5 :=
  (source.aromaticCanonicalRule3PhysicalUnitId_swap 1 5).symm

/-- Endpoint seniority for the `1--5` unit ranks Cl6 above its genuine nonterminal C0 reference
branch.  The C1 ligand's raw cursor cuts that incoming C0 edge. -/
theorem c1_ligand_cl6_seniority :
    source.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference 1 5 6 :=
  left_senior

theorem c1_nonterminal_carbon_branch :
    source.molecule.aromaticCanonicalOfficialCIPChildrenAt 9
      (OfficialCIPNode.rootFromEdge (1 : Atom) 0) ≠ [] :=
  nonterminal_carbon_compiler.1

/-- No spatial record is read for this source. -/
theorem actual_spatial_none : source.spatial? = none := source_structure.2.1

/-! ## 6. Conditional sufficiency for the actual two-pass frame -/

/-- Given raw keys, their actual computation equation, and executable topology unambiguity over
those keys, the common-exclusion second pass and `CanonicalRule3ObserverFrame` exist with the
independent judgment.  This is a conditional sufficiency theorem; it does not discharge topology
readiness for the closed source or prove a converse. -/
theorem actual_twoPass_frame_of_topology
    (rawKeys : List source.AromaticCanonicalUncancelledRule3SpatialKey)
    (rawComputed : roots.mapM
        (source.buildAromaticCanonicalRule3SpatialKeyWith? planarObserver.observe 4) =
      some rawKeys)
    (topology : source.AromaticCanonicalRule3TopologyUnambiguous rawKeys) :
    ∃ frame : source.AromaticCanonicalRule3CanonicalKeyFrame,
      buildRule3ObserverFrame? planarObserver 4 roots = some frame ∧
      frame.rawKeys = rawKeys ∧
      CanonicalRule3ObserverFrame planarObserver 4 roots frame := by
  obtain ⟨resolution, resolutionComputed⟩ := topology
  let excluded := source.aromaticCanonicalRule3ExcludedPhysicalUnits rawKeys resolution
  obtain ⟨keys, keysComputed, _⟩ :=
    exists_observer_key_list_at_or_above_twice (carrierFuel := 1) (evaluationFuel := 4)
      (excludedObserver planarObserver excluded)
      (excludedObserver_total planarObserver planarObserver_total excluded)
      roots roots_valid (by decide)
  change roots.mapM
    (source.buildAromaticCanonicalRule3SpatialKeyWith?
      (observeExcept planarObserver excluded) 4) = some keys at keysComputed
  let frame : source.AromaticCanonicalRule3CanonicalKeyFrame :=
    { rawKeys, resolution, excluded, keys }
  have computed :
      buildRule3ObserverFrame? planarObserver 4 roots = some frame := by
    dsimp only [excluded] at keysComputed
    simp [buildRule3ObserverFrame?, frame, rawComputed, resolutionComputed, excluded, keysComputed]
  exact ⟨frame, computed, rfl,
    buildRule3ObserverFrame?_sound planarObserver 4 roots frame computed⟩

/-- The tagged, unproved closed two-pass frame existence obligation.  The preceding conditional
theorem provides a sufficient route through raw-key computation and topology readiness. -/
def PlanarTetrahedralTwoPassFrameObligation : Prop :=
  ∃ frame : source.AromaticCanonicalRule3CanonicalKeyFrame,
    buildRule3ObserverFrame? planarObserver 4 roots = some frame ∧
    CanonicalRule3ObserverFrame planarObserver 4 roots frame

end TetraStereo.UniversalProof.SourceNativePlanarTetrahedralKeyFrameProofs.SourceNativePlanarTetrahedralKeyFrame
