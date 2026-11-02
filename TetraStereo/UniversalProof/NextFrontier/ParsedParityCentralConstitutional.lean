import TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralSourceLeaves
import TetraStereo.UniversalProof.NextFrontier.ParsedParityThreeLeafProjection

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000





namespace TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralConstitutional

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.UniversalProof.NativeOrdinarySourceInputProofs.SourceInputPremiseRecovery
open TetraStereo.UniversalProof.RuntimeSourcePriorityAlignmentProofs.RuntimeSourcePriorityAlignment
open TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
open TetraStereo.UniversalProof.ParsedParitySourceIntake
open TetraStereo.UniversalProof.SecondSphereOwnSourceOrdering
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceFrames
open TetraStereo.UniversalProof.NextFrontier.ParsedParitySourceArmCoordinates
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmSource
open TetraStereo.UniversalProof.NextFrontier.ParsedParityActualArmDescriptor
open TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralSourceLeaves
open TetraStereo.UniversalProof.NextFrontier.ParsedParityThreeLeafProjection

/-- The frozen source-backed natural-abundance mass; no manually supplied mass constants. -/
def massAtAtomicNumber (z : Nat) : Nat := (CIPRule2MassData.rule2MassPico? z none).getD 0

private theorem converted_mass_without_isotope (raw : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : raw.toSemanticMolecule? = some source.molecule)
    (isotopeFree : ∀ spec ∈ raw.atoms, spec.isotope? = none)
    (atom : source.AromaticCanonicalAtom) :
    source.molecule.toLocalizedMoleculeGraph.atomMass atom = massAtAtomicNumber (raw.atomZAt atom.val) := by
  have indexed := raw.toSemanticMolecule?_atomAt? source.molecule converted atom.val
  have lookup := listGet?_eq_some_get source.molecule.atoms atom
  rw [lookup] at indexed
  cases observed : raw.atomAt? atom.val with
  | none => simp [observed] at indexed
  | some spec =>
      have single : spec.toSemanticAtom? = some (source.molecule.atoms.get atom) := by
        simpa [observed] using indexed.symm
      have physical := AtomSpec.toSemanticAtom?_exact spec _ single
      have member : spec ∈ raw.atoms := listGet?_eq_some_implies_mem raw.atoms atom.val spec
        (by simpa only [RawMolecule.atomAt?] using observed)
      change (CIPRule2MassData.rule2MassPico? (source.molecule.atoms.get atom).element.atomicNumber
        (source.molecule.atoms.get atom).isotopeMassNumber?).getD 0 = _
      rw [physical.1, physical.2.1, isotopeFree spec member,
        atomZAt_eq_of_atomAt? raw atom.val spec observed]
      rfl

private theorem real_node_atomic (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) (atom : source.AromaticCanonicalAtom)
    (current : node.current? = some atom) (real : node.provenance = .realAtom) :
    source.molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation node =
      .ofNat (source.molecule.toLocalizedMoleculeGraph.atomZ atom) := by
  simp only [MoleculeGraph.exactOfficialRule1aObservation, current, real]

private theorem real_node_mass (source : AuthoritativeChemicalInput)
    (node : OfficialCIPNode source.AromaticCanonicalAtom) (atom : source.AromaticCanonicalAtom)
    (current : node.current? = some atom) (real : node.provenance = .realAtom) :
    (ofLex (source.molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel node)).2 =
      source.molecule.toLocalizedMoleculeGraph.atomMass atom := by
  simp only [MoleculeGraph.officialNodeAtomLabel, current, real, MoleculeGraph.rawCIPAtomLabel]
  rfl

theorem raw_isotope_free (c l r : TetrahedralInputParity) :
    ∀ spec ∈ (raw c l r).atoms, spec.isotope? = none := by
  have all : (raw c l r).atoms.all (fun spec => decide (spec.isotope? = none)) = true := by
    cases c <;> cases l <;> cases r <;> decide +kernel
  intro spec member
  exact of_decide_eq_true ((List.all_eq_true.mp all) spec member)

theorem arm_child_atomic (c l r : TetrahedralInputParity) (left : Bool)
    (child : (ownSource (raw c l r)).AromaticCanonicalRerootCursor 1)
    (present : child ∈ armChildren c l r left) :
    (ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      child.occurrence.1.node = .ofNat ((raw c l r).atomZAt
        ((cursorAtomID (ownSource (raw c l r)) child).getD 0)) := by
  obtain ⟨atom, current, real, _⟩ := arm_child_real c l r left child present
  rw [real_node_atomic _ _ atom current real, converted_atomic_number (raw c l r)
    (ownSource (raw c l r)) (raw_semantic_conversion c l r)]
  simp only [cursorAtomID, current, Option.map_some, Option.getD_some]

theorem arm_children_atomic_numbers (c l r : TetrahedralInputParity) (left : Bool) :
    ((armChildren c l r left).map (fun child =>
      ((ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        child.occurrence.1.node).numerator)).Perm [17, 9, 1] := by
  have mapped := (arm_children_ids c l r left).map
    (fun id : Option Nat => (raw c l r).atomZAt (id.getD 0))
  have values : (terminalIDs left).map ((raw c l r).atomZAt) = [1, 9, 17] := by
    cases left <;> cases c <;> cases l <;> cases r <;> decide +kernel
  have pointwise : (armChildren c l r left).map (fun child =>
      ((ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
        child.occurrence.1.node).numerator) =
      (armChildren c l r left).map (fun child => (raw c l r).atomZAt
        ((cursorAtomID (ownSource (raw c l r)) child).getD 0)) := by
    apply List.map_congr_left
    intro child present
    rw [arm_child_atomic c l r left child present]
    rfl
  rw [pointwise]
  have simplified : ((armChildren c l r left).map (fun child => (raw c l r).atomZAt
      ((cursorAtomID (ownSource (raw c l r)) child).getD 0))).Perm [1, 9, 17] := by
    simpa only [List.map_map, Function.comp_def, Option.getD_some, values] using mapped
  exact simplified.trans (by decide +kernel)

theorem arm_child_atomic_natural (c l r : TetrahedralInputParity) (left : Bool)
    (child : (ownSource (raw c l r)).AromaticCanonicalRerootCursor 1)
    (present : child ∈ armChildren c l r left) :
    (ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      child.occurrence.1.node = .ofNat
        (((ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          child.occurrence.1.node).numerator) := by
  rw [arm_child_atomic c l r left child present]
  rfl

theorem arm_root_atomic (c l r : TetrahedralInputParity) (left : Bool) :
    (ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
      (armCursor c l r left).occurrence.1.node = .ofNat 6 := by
  rw [arm_cursor_node, MoleculeGraph.exactOfficialRule1aObservation_rootFromEdge,
    converted_atomic_number (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r),
    armAtom_index]
  have value : (raw c l r).atomZAt (armIndex left) = 6 := by
    cases left <;> cases c <;> cases l <;> cases r <;> decide +kernel
  rw [value]

theorem arm_child_rule1b (c l r : TetrahedralInputParity) (left : Bool)
    (child : (ownSource (raw c l r)).AromaticCanonicalRerootCursor 1)
    (present : child ∈ armChildren c l r left) :
    child.occurrence.1.node.rule1bRootDistance = 2 := by
  have member := (arm_children_nodes c l r left).mem_iff.mp
    (List.mem_map.mpr ⟨child, present, rfl⟩)
  rw [converted_official_edge_children (raw c l r) (ownSource (raw c l r))
    (raw_semantic_conversion c l r) (armAtom c l r left) (armDomain c l r left)
    (sourceCenter c l r).1] at member
  obtain ⟨neighbor, _, nodeEq⟩ := List.mem_map.mp member
  obtain ⟨_, _, real, _⟩ := arm_child_real c l r left child present
  simp only [OfficialCIPNode.rule1bRootDistance, real]
  rw [← nodeEq]
  rfl

theorem arm_root_rule1b (c l r : TetrahedralInputParity) (left : Bool) :
    (armCursor c l r left).occurrence.1.node.rule1bRootDistance = 1 := by
  rw [arm_cursor_node]
  rfl

theorem arm_child_rule2 (c l r : TetrahedralInputParity) (left : Bool)
    (child : (ownSource (raw c l r)).AromaticCanonicalRerootCursor 1)
    (present : child ∈ armChildren c l r left) :
    (ofLex ((ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel
      child.occurrence.1.node)).2 = massAtAtomicNumber
        (((ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.exactOfficialRule1aObservation
          child.occurrence.1.node).numerator) := by
  obtain ⟨atom, current, real, _⟩ := arm_child_real c l r left child present
  rw [real_node_mass _ _ atom current real,
    converted_mass_without_isotope (raw c l r) (ownSource (raw c l r))
      (raw_semantic_conversion c l r) (raw_isotope_free c l r),
    real_node_atomic _ _ atom current real,
    converted_atomic_number (raw c l r) (ownSource (raw c l r)) (raw_semantic_conversion c l r)]
  rfl

theorem arm_root_rule2 (c l r : TetrahedralInputParity) (left : Bool) :
    (ofLex ((ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel
      (armCursor c l r left).occurrence.1.node)).2 = massAtAtomicNumber 6 := by
  have real : (armCursor c l r left).occurrence.1.node.provenance = .realAtom := by
    rw [arm_cursor_node]; rfl
  have current : (armCursor c l r left).occurrence.1.node.current? = some (armAtom c l r left) := by
    rw [arm_cursor_node]; rfl
  have atomic := arm_root_atomic c l r left
  rw [real_node_atomic _ _ (armAtom c l r left) current real,
    converted_atomic_number (raw c l r) (ownSource (raw c l r))
      (raw_semantic_conversion c l r)] at atomic
  have value : (raw c l r).atomZAt (armAtom c l r left).val = 6 :=
    congrArg DeclarativeCIP.ExactAtomicNumber.numerator atomic
  rw [real_node_mass _ _ (armAtom c l r left) current real,
    converted_mass_without_isotope (raw c l r) (ownSource (raw c l r))
      (raw_semantic_conversion c l r) (raw_isotope_free c l r), value]

private theorem production_branch_of_three_children (source : AuthoritativeChemicalInput)
    {carrierFuel : Nat} (target : source.AromaticCanonicalOccurrence carrierFuel)
    (view : source.AromaticCanonicalDependencyView target) (fuel : Nat)
    (frame : source.AromaticCanonicalOccurrenceFourLigandFrame carrierFuel)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame carrierFuel)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?
      target view fuel frame.roots = some keys) (slot : Fin 4)
    (count : (source.aromaticCanonicalRerootChildren (frame.cursorAt slot)).length = 3) :
    SourceKeyBranch source keys.rule3Frame.excluded fuel (frame.cursorAt slot)
      (keys.keyAt slot).rule3 := by
  apply production_keyFrame_branch source target view fuel frame keys computed slot
  intro empty
  have emptyLength := congrArg List.length empty
  rw [count] at emptyLength
  contradiction

theorem arm_key_branch (c l r : TetrahedralInputParity) (left : Bool) :
    SourceKeyBranch (ownSource (raw c l r)) (centralKeys c l r).rule3Frame.excluded 4
      (armCursor c l r left) ((centralKeys c l r).keyAt (armSlot c l r left)).rule3 := by
  exact production_branch_of_three_children (ownSource (raw c l r)) (centralTarget c l r)
    (centralView c l r) 4 (sourceFrame c l r) (centralKeys c l r)
    (central_keys_computed c l r) (armSlot c l r left) (arm_children_length c l r left)

theorem arm_key_rule1a (c l r : TetrahedralInputParity) (left : Bool) :
    ExactOfficialRuleMajorKey.exactRule1aLayers
      (ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph
      ((centralKeys c l r).keyAt (armSlot c l r left)).rule3.constitutional.sourceNodes =
      [[([], .ofNat 6)], [([0], .ofNat 17), ([1], .ofNat 9), ([2], .ofNat 1)]] := by
  exact source_three_leaf_projection (ownSource (raw c l r)) (sourceCenter c l r)
    (armCursor c l r left) (arm_cursor_present c l r left)
    (by rw [arm_cursor_node]; rfl)
    ((centralKeys c l r).keyAt (armSlot c l r left)).rule3
    (centralKeys c l r).rule3Frame.excluded 4 (arm_key_branch c l r left)
    6 17 9 1 (arm_root_atomic c l r left) (arm_children_atomic_numbers c l r left)
    (arm_child_atomic_natural c l r left) (by decide +kernel)

theorem arm_key_rule1b (c l r : TetrahedralInputParity) (left : Bool) :
    ExactOfficialRuleMajorKey.rule1bLayers
      ((centralKeys c l r).keyAt (armSlot c l r left)).rule3.constitutional.sourceNodes =
      [[([], 1)], [([0], 2), ([1], 2), ([2], 2)]] := by
  have projected := source_three_leaf_observed_projection (ownSource (raw c l r))
    (sourceCenter c l r) (armCursor c l r left) (arm_cursor_present c l r left)
    (by rw [arm_cursor_node]; rfl)
    ((centralKeys c l r).keyAt (armSlot c l r left)).rule3
    (centralKeys c l r).rule3Frame.excluded 4 (arm_key_branch c l r left)
    17 9 1 (arm_children_atomic_numbers c l r left) (arm_child_atomic_natural c l r left)
    (by decide +kernel) OfficialCIPNode.rule1bRootDistance (fun _ => 2)
    (fun child present => arm_child_rule1b c l r left child present)
  simpa only [arm_root_rule1b] using projected

theorem arm_key_rule2 (c l r : TetrahedralInputParity) (left : Bool) :
    ExactOfficialRuleMajorKey.rule2Layers
      (ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph
      ((centralKeys c l r).keyAt (armSlot c l r left)).rule3.constitutional.sourceNodes =
      [[([], massAtAtomicNumber 6)],
        [([0], massAtAtomicNumber 17), ([1], massAtAtomicNumber 9), ([2], massAtAtomicNumber 1)]] := by
  have projected := source_three_leaf_observed_projection (ownSource (raw c l r))
    (sourceCenter c l r) (armCursor c l r left) (arm_cursor_present c l r left)
    (by rw [arm_cursor_node]; rfl)
    ((centralKeys c l r).keyAt (armSlot c l r left)).rule3
    (centralKeys c l r).rule3Frame.excluded 4 (arm_key_branch c l r left)
    17 9 1 (arm_children_atomic_numbers c l r left) (arm_child_atomic_natural c l r left)
    (by decide +kernel)
    (fun node => (ofLex ((ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph.officialNodeAtomLabel node)).2)
    massAtAtomicNumber (fun child present => arm_child_rule2 c l r left child present)
  simpa only [arm_root_rule2] using projected

/-- The complete comparator-visible constitution ties, not just the first carbon atomic number. -/
theorem central_arms_constitutional_tie (c l r : TetrahedralInputParity) :
    ExactOfficialRuleMajorKey.compare (ownSource (raw c l r)).molecule.toLocalizedMoleculeGraph
      ((centralKeys c l r).keyAt (armSlot c l r true)).rule3.constitutional
      ((centralKeys c l r).keyAt (armSlot c l r false)).rule3.constitutional = .eq := by
  unfold ExactOfficialRuleMajorKey.compare ExactOfficialRuleMajorKey.compareAddressedSources
  simp only [compareLex, Ordering.byKey, arm_key_rule1a, arm_key_rule1b, arm_key_rule2]
  decide +kernel

end TetraStereo.UniversalProof.NextFrontier.ParsedParityCentralConstitutional
