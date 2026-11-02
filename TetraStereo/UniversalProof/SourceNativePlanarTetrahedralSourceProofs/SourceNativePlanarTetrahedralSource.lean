import TetraStereo.UniversalProof.SourceNativePlanarAlkeneWitnessProofs.SourceNativePlanarAlkeneWitness
import TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3RecursiveKey

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

namespace TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource

open TetraStereo.OneCenter TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.UniversalProof.PlanarRule3DoubleBondGeometryProofs.PlanarRule3DoubleBondGeometry
open TetraStereo.UniversalProof.SourceNativePlanarRule3UnitProofs.SourceNativePlanarRule3Unit
open TetraStereo.UniversalProof.SourceNativeRule3ObserverFrameProofs.SourceNativePlanarRule3RecursiveKey
open TetraStereo.UniversalProof.SourceNativePlanarAlkeneWitnessProofs.SourceNativePlanarAlkeneWitness
  (carbonAtom fluorineAtom chlorineAtom plainBond pt forall₂_map_of_mem
    exactCompareTrace_outcome_eq_rule1a_of_decisive)















def bromineAtom : SemanticAtom := { element := ⟨35, by decide, by decide⟩ }
def iodineAtom : SemanticAtom := { element := ⟨53, by decide, by decide⟩ }
def molecule : SemanticMolecule :=
  { atoms := [carbonAtom, carbonAtom, fluorineAtom, bromineAtom, iodineAtom,
      carbonAtom, chlorineAtom, fluorineAtom, chlorineAtom]
    interactions :=
      [⟨[0, 1], .covalent 1⟩, ⟨[0, 2], .covalent 1⟩, ⟨[0, 3], .covalent 1⟩,
       ⟨[0, 4], .covalent 1⟩, ⟨[1, 5], .covalent 2⟩, ⟨[1, 6], .covalent 1⟩,
       ⟨[5, 7], .covalent 1⟩, ⟨[5, 8], .covalent 1⟩] }
def points : List CartesianPoint2 :=
  [pt (-1) (-1), pt 0 0, pt (-3) (-1), pt (-3) (-2), pt (-2) (-2),
   pt 2 0, pt (-1) 1, pt 3 (-1), pt 3 1]
def diagram : DiagramConfiguration :=
  { atomPositions? := some points
    bonds := [plainBond 0 1, plainBond 0 2, plainBond 0 3, plainBond 0 4,
      plainBond 1 5, plainBond 1 6, plainBond 5 7, plainBond 5 8] }
def source : AuthoritativeChemicalInput := { molecule, diagram? := some diagram }
abbrev Atom := source.AromaticCanonicalAtom
local instance : NeZero source.molecule.atomCount := ⟨by change (9 : Nat) ≠ 0; decide⟩

theorem source_structure : source.StructurallyWellFormed ∧ source.spatial? = none ∧
    diagram.atomConfigurations = [] ∧ molecule.atomCount = 9 :=
  ⟨(AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp
    (by decide +kernel), rfl, rfl, rfl⟩

/-- The literal parser constitution independently supplies the existing encoded valence check. -/
def raw : RawMolecule :=
  { atoms := [AtomSpec.aliphatic .C, AtomSpec.aliphatic .C, AtomSpec.aliphatic .F,
      AtomSpec.aliphatic .Br, AtomSpec.aliphatic .I, AtomSpec.aliphatic .C,
      AtomSpec.aliphatic .Cl, AtomSpec.aliphatic .F, AtomSpec.aliphatic .Cl]
    bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩, ⟨0, 4, .single⟩,
      ⟨1, 5, .double⟩, ⟨1, 6, .single⟩, ⟨5, 7, .single⟩, ⟨5, 8, .single⟩] }
theorem actual_valence_binding : raw.toSemanticMolecule? = some molecule ∧ raw.ValenceOK :=
  ⟨by decide +kernel, (raw.valenceOK?_eq_true_iff).mp (by decide +kernel)⟩

/-- The complete branch compiler is genuinely inhabited, including nonterminal branches. -/
theorem exists_complete_branch (input : AuthoritativeChemicalInput)
    (endpoint reference : input.AromaticCanonicalAtom) (different : reference ≠ endpoint) :
    ∃ key, input.buildAromaticCanonicalRule3BranchKey? endpoint reference = some key ∧
      key.complete = true ∧
      key.sourceNodes.head? = some [([], OfficialCIPNode.rootFromEdge endpoint reference)] := by
  obtain ⟨key, computed, complete⟩ :=
    input.molecule.toLocalizedMoleculeGraph.buildExactOfficialRuleMajorKey_complete_of_expansionCompleteWithin
      (input.molecule.aromaticCanonicalOfficialCIPChildrenAt input.molecule.atomCount)
      (input.molecule.atomCount + 1) (OfficialCIPNode.rootFromEdge endpoint reference)
      (input.molecule.aromaticCanonicalExpansionCompleteWithin_rootFromEdge_default different)
  refine ⟨key, ?_, complete, ?_⟩
  · unfold buildAromaticCanonicalRule3BranchKey?
    rw [input.molecule.toLocalizedMoleculeGraph.buildObservedExactOfficialRuleMajorKey_eq_exact
      input.molecule.semanticExactOfficialRule1aObservation
      input.molecule.semanticExactOfficialRule1aObservation_eq_independent]
    exact computed
  · exact input.molecule.toLocalizedMoleculeGraph.buildExactOfficialRuleMajorKey_sourceNodes_head
      _ _ _ _ computed

/-- The fallback is unreachable on every genuine represented endpoint substituent, as proved
below; the returned key is bound to the actual branch compiler. -/
noncomputable def rankedAt (input : AuthoritativeChemicalInput)
    (endpoint reference : input.AromaticCanonicalAtom) : input.AromaticCanonicalRule3RankedSubstituent :=
  { atom := reference
    key := (input.buildAromaticCanonicalRule3BranchKey? endpoint reference).getD
      (MoleculeGraph.exactOfficialRuleMajorRootKey
        (OfficialCIPNode.rootFromEdge endpoint reference) true) }

theorem rankedAt_actual (input : AuthoritativeChemicalInput)
    (endpoint reference : input.AromaticCanonicalAtom) (different : reference ≠ endpoint) :
    input.buildAromaticCanonicalRule3BranchKey? endpoint reference =
        some (rankedAt input endpoint reference).key ∧
      (rankedAt input endpoint reference).key.complete = true ∧
      (rankedAt input endpoint reference).key.sourceNodes.head? =
        some [([], OfficialCIPNode.rootFromEdge endpoint reference)] := by
  obtain ⟨key, computed, complete, head⟩ := exists_complete_branch input endpoint reference different
  simpa [rankedAt, computed] using (show
    input.buildAromaticCanonicalRule3BranchKey? endpoint reference = some key ∧
      key.complete = true ∧ key.sourceNodes.head? =
        some [([], OfficialCIPNode.rootFromEdge endpoint reference)] from
    ⟨computed, complete, head⟩)

theorem rankedAt_gt_of_atomic_head (input : AuthoritativeChemicalInput)
    (endpoint senior other : input.AromaticCanonicalAtom)
    (seniorNe : senior ≠ endpoint) (otherNe : other ≠ endpoint)
    (higher : input.molecule.toLocalizedMoleculeGraph.atomZ other <
      input.molecule.toLocalizedMoleculeGraph.atomZ senior) :
    ExactOfficialRuleMajorKey.compare input.molecule.toLocalizedMoleculeGraph
      (rankedAt input endpoint senior).key (rankedAt input endpoint other).key = .gt := by
  have leftHead : (ExactOfficialRuleMajorKey.exactRule1aLayers
      input.molecule.toLocalizedMoleculeGraph (rankedAt input endpoint senior).key.sourceNodes).head? =
      some [([], .ofNat (input.molecule.toLocalizedMoleculeGraph.atomZ senior))] := by
    rw [ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head _ _ _
      (rankedAt_actual input endpoint senior seniorNe).2.2]
    simp
  have rightHead : (ExactOfficialRuleMajorKey.exactRule1aLayers
      input.molecule.toLocalizedMoleculeGraph (rankedAt input endpoint other).key.sourceNodes).head? =
      some [([], .ofNat (input.molecule.toLocalizedMoleculeGraph.atomZ other))] := by
    rw [ExactOfficialRuleMajorKey.exactRule1aLayers_head_of_sourceNodes_head _ _ _
      (rankedAt_actual input endpoint other otherNe).2.2]
    simp
  have atomic := ExactOfficialRuleMajorKey.compareSparseExactRule1a_gt_of_heads_gt
    leftHead rightHead higher
  have decisive : OfficialRuleMajorKey.compareSparseLayers
      ExactOfficialRuleMajorKey.compareExactAtomicNumber
      (ExactOfficialRuleMajorKey.exactRule1aLayers input.molecule.toLocalizedMoleculeGraph
        (rankedAt input endpoint senior).key.sourceNodes)
      (ExactOfficialRuleMajorKey.exactRule1aLayers input.molecule.toLocalizedMoleculeGraph
        (rankedAt input endpoint other).key.sourceNodes) ≠ .eq := by rw [atomic]; decide
  rw [← ExactOfficialRuleMajorKey.compareTrace_outcome]
  rw [exactCompareTrace_outcome_eq_rule1a_of_decisive _ _ _ decisive]
  exact atomic

theorem canonical_senior_of_strict_atomic_heads (input : AuthoritativeChemicalInput)
    (endpoint partner senior : input.AromaticCanonicalAtom)
    (present : senior ∈ input.aromaticCanonicalRule3Substituents endpoint partner)
    (higher : ∀ other ∈ input.aromaticCanonicalRule3Substituents endpoint partner, other ≠ senior →
      input.molecule.toLocalizedMoleculeGraph.atomZ other <
        input.molecule.toLocalizedMoleculeGraph.atomZ senior) :
    input.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference endpoint partner senior := by
  refine ⟨(input.aromaticCanonicalRule3Substituents endpoint partner).map (rankedAt input endpoint),
    rankedAt input endpoint senior, ?_, ⟨?_, ?_⟩, rfl⟩
  · exact forall₂_map_of_mem
      (input.CanonicalAromaticCanonicalRule3RankedSubstituent endpoint) (rankedAt input endpoint)
      _ (fun other otherPresent => ⟨rfl,
        (input.buildAromaticCanonicalRule3BranchKey?_eq_some_iff_canonical endpoint partner other
          otherPresent _).mp
          (rankedAt_actual input endpoint other
            (input.aromaticCanonicalRule3Substituent_ne_endpoint endpoint partner other
              otherPresent)).1⟩)
  · exact List.mem_map.mpr ⟨senior, present, rfl⟩
  · intro other otherPresent different
    rcases List.mem_map.mp otherPresent with ⟨atom, atomPresent, rfl⟩
    exact rankedAt_gt_of_atomic_head input endpoint senior atom
      (input.aromaticCanonicalRule3Substituent_ne_endpoint endpoint partner senior present)
      (input.aromaticCanonicalRule3Substituent_ne_endpoint endpoint partner atom atomPresent)
      (higher atom atomPresent different)

theorem left_candidates : ∀ atom : Atom,
    atom ∈ source.aromaticCanonicalRule3Substituents 1 5 ↔ atom = 0 ∨ atom = 6 := by
  simp only [mem_aromaticCanonicalRule3Substituents_iff]
  unfold AromaticCanonicalAdjacent
  decide +kernel
theorem right_candidates : ∀ atom : Atom,
    atom ∈ source.aromaticCanonicalRule3Substituents 5 1 ↔ atom = 7 ∨ atom = 8 := by
  simp only [mem_aromaticCanonicalRule3Substituents_iff]
  unfold AromaticCanonicalAdjacent
  decide +kernel

theorem left_senior : source.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference 1 5 6 := by
  apply canonical_senior_of_strict_atomic_heads source 1 5 6
  · exact (left_candidates 6).mpr (Or.inr rfl)
  · intro atom present different
    rcases (left_candidates atom).mp present with rfl | rfl
    · change 6 < 17
      decide
    · exact (different rfl).elim
theorem right_senior : source.CanonicalAromaticCanonicalRule3ConstitutionalSeniorReference 5 1 8 := by
  apply canonical_senior_of_strict_atomic_heads source 5 1 8
  · exact (right_candidates 8).mpr (Or.inr rfl)
  · intro atom present different
    rcases (right_candidates atom).mp present with rfl | rfl
    · change 9 < 17
      decide
    · exact (different rfl).elim

theorem nonterminal_carbon_compiler :
    molecule.aromaticCanonicalOfficialCIPChildrenAt 9 (OfficialCIPNode.rootFromEdge (1 : Atom) 0) ≠ [] ∧
      source.buildAromaticCanonicalRule3BranchKey? 1 0 = some (rankedAt source 1 0).key ∧
      (rankedAt source 1 0).key.complete = true :=
  ⟨by decide +kernel, (rankedAt_actual source 1 0 (by decide)).1,
    (rankedAt_actual source 1 0 (by decide)).2.1⟩

def cisUnit : source.AromaticCanonicalRule3SpatialUnitResult := ⟨6, 8, .seqcis⟩
theorem ordinary : source.AromaticCanonicalOrdinaryDoubleBond 1 5 := by
  unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent
  decide +kernel
theorem point_lookup : ∀ atom : Atom,
    aromaticCanonicalPlanarPointAt? source atom = points[atom.val]? := fun _ => rfl
theorem unit_canonical : CanonicalAromaticCanonicalPlanarRule3Unit source 1 5 cisUnit := by
  refine ⟨ordinary, left_senior, right_senior, pt 0 0, pt 2 0, pt (-1) 1, pt 3 1,
    ?_, ?_, ?_, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 1 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 5 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 6 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 8 _).mp (by decide +kernel)
  · norm_num [SameSide, planarDirectedArea, pt]
theorem actual_planar_unit : aromaticCanonicalPlanarRule3Unit? source 1 5 = some cisUnit :=
  (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical source 1 5 cisUnit).mpr unit_canonical
def reverseCisUnit : source.AromaticCanonicalRule3SpatialUnitResult := ⟨8, 6, .seqcis⟩
theorem actual_reverse_planar_unit :
    aromaticCanonicalPlanarRule3Unit? source 5 1 = some reverseCisUnit := by
  apply (aromaticCanonicalPlanarRule3Unit?_eq_some_iff_canonical source 5 1 reverseCisUnit).mpr
  refine ⟨?_, right_senior, left_senior, pt 2 0, pt 0 0, pt 3 1, pt (-1) 1,
    ?_, ?_, ?_, ?_, Or.inl ⟨rfl, ?_⟩⟩
  · unfold AromaticCanonicalOrdinaryDoubleBond AromaticCanonicalAdjacent
    decide +kernel
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 5 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 1 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 8 _).mp (by decide +kernel)
  · exact (aromaticCanonicalPlanarPointAt?_eq_some_iff source 6 _).mp (by decide +kernel)
  · norm_num [SameSide, planarDirectedArea, pt]

theorem center_neighbors : source.aromaticCanonicalNeighborFinset 0 = {1, 2, 3, 4} := by
  ext atom
  rw [mem_aromaticCanonicalNeighborFinset_iff]
  unfold AromaticCanonicalAdjacent
  decide +revert +kernel
noncomputable def center : source.AromaticCanonicalTetrahedralCenter :=
  ⟨0, (source.mem_aromaticCanonicalTetrahedralCenterSet_iff 0).mpr ⟨by
    unfold ConnectivityOnlyTetrahedralCenterAtom ConnectivityOnlyTetrahedralPeriodicElement
    decide +kernel, by rw [center_neighbors]; decide +kernel⟩⟩
noncomputable def target : source.AromaticCanonicalOccurrence 1 :=
  source.aromaticCanonicalFinalOccurrence 1 center
def rootNode : OfficialCIPNode Atom := OfficialCIPNode.root 0
def carbonNode : OfficialCIPNode Atom := rootNode.extend 1 0
def realC5Node : OfficialCIPNode Atom := carbonNode.extend 5 0
theorem root_children : molecule.aromaticCanonicalOfficialCIPChildrenAt 9 rootNode =
    [rootNode.extend 1 0, rootNode.extend 2 0, rootNode.extend 3 0, rootNode.extend 4 0] := by
  decide +kernel
theorem carbon_children : molecule.aromaticCanonicalOfficialCIPChildrenAt 9 carbonNode =
    [realC5Node, carbonNode.extend 5 1, carbonNode.extend 6 0] := by decide +kernel
def firstFrame (slot : Fin 4) : source.AromaticCanonicalOccurrenceFrame :=
  { root := 0, address := [slot.val]
    node := rootNode.extend ⟨slot.val + 1, by change slot.val + 1 < 9; omega⟩ 0, remaining := 1 }
noncomputable def firstOccurrence (slot : Fin 4) : source.AromaticCanonicalOccurrence 1 :=
  ⟨firstFrame slot, by
    apply (source.mem_aromaticCanonicalOccurrences_iff 1 _).mpr
    change source.DeclarativeAromaticCanonicalOccurrenceSubtree 0 [] 2 rootNode (firstFrame slot)
    refine .subtreeDescendant ?_ (.subtreeRoot [slot.val] 1 _)
    have children := root_children
    change source.molecule.aromaticCanonicalOfficialCIPChildrenAt source.molecule.atomCount
      rootNode = _ at children
    rw [children]
    fin_cases slot <;> decide +kernel⟩
noncomputable def firstCursor (slot : Fin 4) : source.AromaticCanonicalRerootCursor 1 :=
  { occurrence := firstOccurrence slot, previous? := some target }
noncomputable def roots : List (source.AromaticCanonicalRerootCursor 1) := List.ofFn firstCursor
theorem actual_four_real_roots : roots.length = 4 ∧
    roots.map (fun cursor => cursor.occurrence.1.node.current?) = [some 1, some 2, some 3, some 4] ∧
    ∀ cursor ∈ roots, cursor.occurrence.1.node.provenance = .realAtom := by
  refine ⟨rfl, rfl, ?_⟩
  intro cursor present
  rcases List.mem_ofFn.mp present with ⟨slot, rfl⟩
  fin_cases slot <;> decide +kernel
theorem actual_ligand_frame : source.aromaticCanonicalOccurrenceLigandFrame? target = some roots := by
  apply (source.aromaticCanonicalOccurrenceLigandFrame?_eq_some_iff target roots).mpr
  refine ⟨?_, ?_⟩
  · change (List.ofFn firstFrame) = source.intendedAromaticCanonicalRerootChildFrames
      { occurrence := target, previous? := none }
    decide +kernel
  · intro cursor present
    rcases List.mem_ofFn.mp present with ⟨slot, rfl⟩
    rfl

theorem real_C5_history : realC5Node.history = [5, 1, 0] ∧
    realC5Node.current? = some 5 ∧ realC5Node.parent? = some 1 ∧
    realC5Node.provenance = .realAtom := by decide +kernel
def cisNodeResult : source.AromaticCanonicalRule3SpatialNodeResult := ⟨1, 5, cisUnit⟩
theorem real_C5_node_resolved : aromaticCanonicalPlanarRule3Node? source realC5Node =
    some (some cisNodeResult) :=
  (aromaticCanonicalPlanarRule3Node?_eq_some_some_iff_canonical source realC5Node cisNodeResult).mpr
    ⟨real_C5_history.2.2.2, real_C5_history.2.1, real_C5_history.2.2.1, ordinary, unit_canonical⟩
def carbonChildFrames : List source.AromaticCanonicalOccurrenceFrame :=
  [ { root := 0, address := [0, 0], node := realC5Node, remaining := 0 }
  , { root := 0, address := [0, 1], node := carbonNode.extend 5 1, remaining := 0 }
  , { root := 0, address := [0, 2], node := carbonNode.extend 6 0, remaining := 0 } ]
theorem actual_carbon_child_frames :
    (source.aromaticCanonicalRerootChildren (firstCursor 0)).map (fun cursor => cursor.occurrence.1) =
      carbonChildFrames := by
  rw [(source.aromaticCanonicalRerootChildren_sound (firstCursor 0)).1]
  decide +kernel
theorem actual_carbon_child_seqcis :
    ∃ child ∈ source.aromaticCanonicalRerootChildren (firstCursor 0),
      child.occurrence.1.node.history = [5, 1, 0] ∧
      child.previous? = some (firstCursor 0).occurrence ∧
      aromaticCanonicalPlanarRule3Node? source child.occurrence.1.node = some (some cisNodeResult) := by
  have present : (carbonChildFrames.head (by decide)) ∈
      (source.aromaticCanonicalRerootChildren (firstCursor 0)).map (fun cursor => cursor.occurrence.1) := by
    rw [actual_carbon_child_frames]
    simp [carbonChildFrames]
  rcases List.mem_map.mp present with ⟨child, childPresent, frameEq⟩
  have nodeEq : child.occurrence.1.node = realC5Node := congrArg (fun frame => frame.node) frameEq
  refine ⟨child, childPresent, ?_,
    (source.aromaticCanonicalRerootChildren_sound (firstCursor 0)).2 child childPresent, ?_⟩
  · rw [nodeEq]
    exact real_C5_history.1
  · rw [nodeEq]
    exact real_C5_node_resolved

end TetraStereo.UniversalProof.SourceNativePlanarTetrahedralSourceProofs.SourceNativePlanarTetrahedralSource
