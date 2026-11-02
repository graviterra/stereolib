import TetraStereo.OneCenter.LocalizedCompoundParentNoninterference
import TetraStereo.OneCenter.LocalizedUniversalReferencePipeline
import TetraStereo.OneCenter.LocalizedConstitutionalRootSeparation
import TetraStereo.OneCenter.LocalizedConstitutionalExecutable
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
















































namespace TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput.WholeStateCumulativeLabels

/-! ## Elements, atoms, bonds, and the labelled source -/

def periodicElement (atomicNumber : Nat) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : PeriodicElement :=
  { atomicNumber := atomicNumber, positive := positive, atMost118 := bounded }

def carbon : PeriodicElement := periodicElement 6 (by decide) (by decide)
def hydrogen : PeriodicElement := periodicElement 1 (by decide) (by decide)
def fluorine : PeriodicElement := periodicElement 9 (by decide) (by decide)
def chlorine : PeriodicElement := periodicElement 17 (by decide) (by decide)
def bromine : PeriodicElement := periodicElement 35 (by decide) (by decide)
def iodine : PeriodicElement := periodicElement 53 (by decide) (by decide)

def atom (element : PeriodicElement) : SemanticAtom := { element := element }

/-- A carbon atom carrying the explicit isotope mass number `mass`. -/
def labelledCarbon (mass : Nat) : SemanticAtom :=
  { atom carbon with isotopeMassNumber? := some mass }

def singleBond (left right : Nat) : SemanticInteraction :=
  { participants := [left, right], kind := .covalent 1 }

/-- Eleven-atom fixture: `0` central carbon; `1 = 12C`, `2 = 13C` the two carbon arms;
`3 = H`, `4 = F`, `5 = Cl` on arm `1`; `6 = H`, `7 = F`, `8 = Cl` on arm `2`;
`9 = Br`, `10 = I` on the center. -/
def source : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms :=
          [atom carbon, labelledCarbon 12, labelledCarbon 13, atom hydrogen, atom fluorine,
            atom chlorine, atom hydrogen, atom fluorine, atom chlorine, atom bromine,
            atom iodine]
        interactions :=
          [singleBond 0 1, singleBond 0 2, singleBond 0 9, singleBond 0 10,
            singleBond 1 3, singleBond 1 4, singleBond 1 5,
            singleBond 2 6, singleBond 2 7, singleBond 2 8] }
    spatial? := some { positions :=
      [{ x := 0, y := 0, z := 0 },
       { x := 1, y := 0, z := 0 },
       { x := -1, y := 0, z := 0 },
       { x := 2, y := 1, z := 0 },
       { x := 2, y := 0, z := 1 },
       { x := 2, y := -1, z := -1 },
       { x := -2, y := 1, z := 0 },
       { x := -2, y := 0, z := 1 },
       { x := -2, y := -1, z := -1 },
       { x := 0, y := 1, z := 1 },
       { x := 0, y := -1, z := 1 }] } }

/-! ## Actual admission -/

theorem source_structurallyWellFormed :
    source.structurallyWellFormed? = true := by
  decide +kernel

theorem source_localizedGraphReady :
    source.molecule.localizedCIPGraphReady? = true := by
  decide +kernel

theorem source_noDoubleTest :
    source.molecule.noLocalizedDoubleBondRecords? = true := by
  decide +kernel

theorem source_noDoubleRecords :
    source.molecule.NoLocalizedDoubleBondRecords :=
  (source.molecule.noLocalizedDoubleBondRecords?_eq_true_iff).mp source_noDoubleTest

def certifiedSource : CertifiedAuthoritativeChemicalInput :=
  { input := source
    structurallyWellFormed :=
      (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp
        source_structurallyWellFormed }

def localizedSource : CertifiedLocalizedCIPInput :=
  { certified := certifiedSource
    graphReady :=
      (certifiedSource.input.molecule.localizedCIPGraphReady?_eq_true_iff).mp
        source_localizedGraphReady }

/-- The actual runtime input. -/
def input : LocalizedUniversalReference.Input :=
  { certified := localizedSource }

/-- **Admission.**  The actual `admitSource?` pipeline returns exactly the constructed input. -/
theorem admission : LocalizedUniversalReference.admitSource? source = some input := rfl

/-! ## The certified graph and its atom indices -/

abbrev Atom : Type := input.certified.Atom

abbrev graph : MoleculeGraph Atom := input.certified.moleculeGraph

def atom0 : Atom := ⟨0, by decide⟩
def atom1 : Atom := ⟨1, by decide⟩
def atom2 : Atom := ⟨2, by decide⟩
def atom3 : Atom := ⟨3, by decide⟩
def atom4 : Atom := ⟨4, by decide⟩
def atom5 : Atom := ⟨5, by decide⟩
def atom6 : Atom := ⟨6, by decide⟩
def atom7 : Atom := ⟨7, by decide⟩
def atom8 : Atom := ⟨8, by decide⟩
def atom9 : Atom := ⟨9, by decide⟩
def atom10 : Atom := ⟨10, by decide⟩

/-- The carrier fuel actually used by the pipeline for this 11-atom source. -/
abbrev fuel : Nat := LocalizedUniversalReference.carrierFuel input

theorem fuel_eq : fuel = 12 := rfl

theorem atomCount_eq : input.certified.certified.input.molecule.atomCount = 11 := rfl

/-! ## Exact single-bond orders

`Finset.sort` is `Multiset.sort`, a `Quot.liftOn` over the well-founded `mergeSort`; the kernel
does not unfold it.  As in `LocalizedActualReferencePositiveWitness`, every executable occurrence
enumeration is therefore rewritten through an explicit sorted list proved via the sort-free
`List.toFinset_sort`.  The bond orders themselves are ordinary finite computations. -/

@[simp] theorem bond_atom0_atom1 : graph.bond atom0 atom1 = 1 := by decide +kernel
@[simp] theorem bond_atom0_atom2 : graph.bond atom0 atom2 = 1 := by decide +kernel
@[simp] theorem bond_atom0_atom9 : graph.bond atom0 atom9 = 1 := by decide +kernel
@[simp] theorem bond_atom0_atom10 : graph.bond atom0 atom10 = 1 := by decide +kernel

@[simp] theorem bond_atom1_atom0 : graph.bond atom1 atom0 = 1 := by decide +kernel
@[simp] theorem bond_atom1_atom3 : graph.bond atom1 atom3 = 1 := by decide +kernel
@[simp] theorem bond_atom1_atom4 : graph.bond atom1 atom4 = 1 := by decide +kernel
@[simp] theorem bond_atom1_atom5 : graph.bond atom1 atom5 = 1 := by decide +kernel

@[simp] theorem bond_atom2_atom0 : graph.bond atom2 atom0 = 1 := by decide +kernel
@[simp] theorem bond_atom2_atom6 : graph.bond atom2 atom6 = 1 := by decide +kernel
@[simp] theorem bond_atom2_atom7 : graph.bond atom2 atom7 = 1 := by decide +kernel
@[simp] theorem bond_atom2_atom8 : graph.bond atom2 atom8 = 1 := by decide +kernel

/-- If a duplicate-free list is sorted ascending and has the right neighbour set, it is the
executable sorted neighbour enumeration. -/
theorem sort_of_toFinset_eq (a : Atom) (l : List Atom)
    (hset : l.toFinset = graph.neighborFinset a)
    (hnd : l.Nodup) (hpw : l.Pairwise (· ≤ ·)) :
    (graph.neighborFinset a).sort (· ≤ ·) = l := by
  rw [← hset]
  exact (List.toFinset_sort (r := (· ≤ ·)) (l := l) hnd).mpr hpw

/-- The sorted neighbour list of every atom of the fixture.  The right-hand side is a `match` on
the atom value, so it rewrites uniformly at every atom occurrence in an executable term. -/
theorem neighborSort_eq (a : Atom) :
    (graph.neighborFinset a).sort (· ≤ ·) =
      match a.val with
      | 0 => [atom1, atom2, atom9, atom10]
      | 1 => [atom0, atom3, atom4, atom5]
      | 2 => [atom0, atom6, atom7, atom8]
      | 3 => [atom1]
      | 4 => [atom1]
      | 5 => [atom1]
      | 6 => [atom2]
      | 7 => [atom2]
      | 8 => [atom2]
      | 9 => [atom0]
      | _ => [atom0] := by
  fin_cases a
  · exact sort_of_toFinset_eq atom0 [atom1, atom2, atom9, atom10]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq atom1 [atom0, atom3, atom4, atom5]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq atom2 [atom0, atom6, atom7, atom8]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq atom3 [atom1]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq atom4 [atom1]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq atom5 [atom1]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq atom6 [atom2]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq atom7 [atom2]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq atom8 [atom2]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq atom9 [atom0]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)
  · exact sort_of_toFinset_eq atom10 [atom0]
      (by ext y; fin_cases y <;> decide) (by decide) (by decide)

/-! ## Concrete occurrence coordinates

The target occurrence is the center `0` at address `[0]` under original root `1`; the actual
parent occurrence is the original root `1` at address `[]`; the outward occurrence is the second
carbon arm `2` at address `[0,0]`.  All three are genuine members of the shared finite carrier,
and the two reroot cursors below are path-valid. -/

def rootNode : OfficialCIPNode Atom := OfficialCIPNode.root atom1

def targetNode : OfficialCIPNode Atom := rootNode.extend atom0 0

def outwardNode : OfficialCIPNode Atom := targetNode.extend atom2 0

def node3 : OfficialCIPNode Atom := rootNode.extend atom3 0
def node4 : OfficialCIPNode Atom := rootNode.extend atom4 0
def node5 : OfficialCIPNode Atom := rootNode.extend atom5 0

def node9 : OfficialCIPNode Atom := targetNode.extend atom9 0
def node10 : OfficialCIPNode Atom := targetNode.extend atom10 0

def node6 : OfficialCIPNode Atom := outwardNode.extend atom6 0
def node7 : OfficialCIPNode Atom := outwardNode.extend atom7 0
def node8 : OfficialCIPNode Atom := outwardNode.extend atom8 0

/-- The executable official children of the original-root node: the center and the three
single-bond ligands of arm `1`, in canonical ascending atom order. -/
theorem children_rootNode :
    input.certified.executableOfficialCIPChildren rootNode =
      [targetNode, node3, node4, node5] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    rootNode, OfficialCIPNode.root, OfficialCIPNode.isDuplicateLeaf,
    OfficialCIPNodeProvenance.isDuplicateLeaf, OfficialCIPNode.parent?,
    neighborSort_eq, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.range_one, List.flatMap_singleton, List.filter_cons, List.filter_nil,
    Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

/-- The executable official children of the target center: the outward arm `2` plus `Br` and `I`,
with the incoming parent `1` cut. -/
theorem children_targetNode :
    input.certified.executableOfficialCIPChildren targetNode =
      [outwardNode, node9, node10] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    targetNode, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

/-- The executable official children of the outward-carbon node: its three ligands, with the
incoming target `0` cut. -/
theorem children_outwardNode :
    input.certified.executableOfficialCIPChildren outwardNode =
      [node6, node7, node8] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    outwardNode, targetNode, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

def rootFrame : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom1, address := [], node := rootNode, remaining := fuel + 1 }

def targetFrame : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom1, address := [0], node := targetNode, remaining := fuel }

def outwardFrame : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom1, address := [0, 0], node := outwardNode, remaining := fuel - 1 }

/-! ## Actual carrier membership, derived declaratively

The carrier is enumerated by the opaque `Finset.sort`; membership is therefore established
through its exact declarative characterization, using the child enumerations proved above. -/

theorem rootFrame_mem : rootFrame ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom1 [] (fuel + 1) rootNode
    rootFrame
  simpa [rootFrame] using
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
      (input := input.certified) (root := atom1) (path := []) (fuel := fuel + 1)
      (node := rootNode))

theorem targetFrame_mem : targetFrame ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom1 [] (fuel + 1) rootNode
    targetFrame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode)
    (child := targetNode) (slot := 0) (occurrence := targetFrame) ?_ ?_
  · rw [children_rootNode]
    simp
  · simpa [targetFrame] using
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
        (input := input.certified) (root := atom1) (path := [0]) (fuel := fuel)
        (node := targetNode))

theorem outwardFrame_mem : outwardFrame ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom1 [] (fuel + 1) rootNode
    outwardFrame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode)
    (child := targetNode) (slot := 0) (occurrence := outwardFrame) ?_ ?_
  · rw [children_rootNode]
    simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [0]) (fuel := fuel - 1) (node := targetNode)
      (child := outwardNode) (slot := 0) (occurrence := outwardFrame) ?_ ?_
    · rw [children_targetNode]
      simp
    · simpa [outwardFrame] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := input.certified) (root := atom1) (path := [0, 0]) (fuel := fuel - 1)
          (node := outwardNode))

def rootOcc : input.certified.LocalizedCIPOccurrence fuel := ⟨rootFrame, rootFrame_mem⟩
def targetOcc : input.certified.LocalizedCIPOccurrence fuel := ⟨targetFrame, targetFrame_mem⟩
def outwardOcc : input.certified.LocalizedCIPOccurrence fuel := ⟨outwardFrame, outwardFrame_mem⟩

/-- The actual parent cursor: original-root occurrence `1` reached from the target `0`. -/
def parentCursor : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := rootOcc, previous? := some targetOcc }

/-- The actual outward cursor: carbon arm `2` reached from the target `0`. -/
def outwardCursor : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := outwardOcc, previous? := some targetOcc }

/-- The target cursor from which both compared cursors are reached. -/
def targetCursor : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := targetOcc, previous? := some rootOcc }

theorem carrierTreeAdjacent_root_target :
    input.certified.LocalizedCarrierTreeAdjacent rootFrame targetFrame := by
  refine ⟨rfl, Or.inl ⟨?_, rfl⟩⟩
  decide +kernel

theorem carrierTreeAdjacent_outward_target :
    input.certified.LocalizedCarrierTreeAdjacent outwardFrame targetFrame := by
  refine ⟨rfl, Or.inr ⟨?_, rfl⟩⟩
  decide +kernel

theorem parentCursor_valid : input.certified.LocalizedRerootCursorValid parentCursor := by
  unfold LocalizedRerootCursorValid
  simp only [parentCursor]
  exact (input.certified.mem_localizedRerootNeighborFrames_iff targetFrame rootFrame).mpr
    ⟨rootFrame_mem, carrierTreeAdjacent_root_target⟩

theorem outwardCursor_valid : input.certified.LocalizedRerootCursorValid outwardCursor := by
  unfold LocalizedRerootCursorValid
  simp only [outwardCursor]
  exact (input.certified.mem_localizedRerootNeighborFrames_iff targetFrame outwardFrame).mpr
    ⟨outwardFrame_mem, carrierTreeAdjacent_outward_target⟩

/-! ## Actual parent-frame certificate and target activity -/

def targetActive : targetOcc.1.node.ActiveSimple := ⟨rfl, by decide⟩

def parentCertificate : input.certified.LocalizedParentFrameHistory targetOcc :=
  { parent := rootOcc
    parent_root := rfl
    parent_address := rfl
    parent_remaining := rfl
    parent_active := ⟨rfl, by decide⟩
    parent_extend := ⟨atom0, 0, rfl⟩
    current := atom0
    current_eq := rfl
    history_eq := rfl
    nonroot := by decide }

/-- The outward frame is an intended child of the target cursor: it is a tree neighbour of the
target frame and its address differs from the cut parent address. -/
theorem outwardFrame_mem_intended :
    outwardFrame ∈ input.certified.intendedLocalizedRerootChildFrames targetCursor := by
  unfold intendedLocalizedRerootChildFrames
  have notDuplicate : targetCursor.occurrence.1.node.isDuplicateLeaf = false := rfl
  rw [notDuplicate]
  simp only [Bool.false_eq_true, ↓reduceIte, targetCursor]
  rw [List.mem_filter]
  refine ⟨?neighbor, ?address⟩
  · exact (input.certified.mem_localizedRerootNeighborFrames_iff targetFrame outwardFrame).mpr
      ⟨outwardFrame_mem, carrierTreeAdjacent_outward_target⟩
  · decide +kernel

/-- The outward cursor is an actual executable child of the target cursor. -/
theorem outwardCursor_mem :
    outwardCursor ∈ input.certified.executableLocalizedRerootChildren targetCursor := by
  unfold executableLocalizedRerootChildren
  rw [List.mem_map]
  refine ⟨⟨outwardFrame, outwardFrame_mem_intended⟩, List.mem_attach _ _, ?_⟩
  apply LocalizedRerootCursor.ext input.certified
  · exact Subtype.ext rfl
  · rfl

theorem outwardCursor_address :
    outwardCursor.occurrence.1.address = targetOcc.1.address ++ [0] := rfl

/-! ## The actual ligand children

Each ligand occurrence is terminal under rerooting: its only physical neighbour is the incoming
parent cut.  We first record the exact official child lists and the declarative carrier
membership of every ligand frame. -/

theorem children_node3 :
    input.certified.executableOfficialCIPChildren node3 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node3, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

theorem children_node4 :
    input.certified.executableOfficialCIPChildren node4 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node4, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

theorem children_node5 :
    input.certified.executableOfficialCIPChildren node5 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node5, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

theorem children_node6 :
    input.certified.executableOfficialCIPChildren node6 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node6, outwardNode, targetNode, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

theorem children_node7 :
    input.certified.executableOfficialCIPChildren node7 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node7, outwardNode, targetNode, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

theorem children_node8 :
    input.certified.executableOfficialCIPChildren node8 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    node8, outwardNode, targetNode, rootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

def f3 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom1, address := [1], node := node3, remaining := fuel }

def f4 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom1, address := [2], node := node4, remaining := fuel }

def f5 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom1, address := [3], node := node5, remaining := fuel }

def f6 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom1, address := [0, 0, 0], node := node6, remaining := fuel - 2 }

def f7 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom1, address := [0, 0, 1], node := node7, remaining := fuel - 2 }

def f8 : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom1, address := [0, 0, 2], node := node8, remaining := fuel - 2 }

theorem f3_mem : f3 ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom1 [] (fuel + 1) rootNode f3
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode)
    (child := node3) (slot := 1) (occurrence := f3) ?_ ?_
  · rw [children_rootNode]; simp
  · simpa [f3] using
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
        (input := input.certified) (root := atom1) (path := [1]) (fuel := fuel)
        (node := node3))

theorem f4_mem : f4 ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom1 [] (fuel + 1) rootNode f4
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode)
    (child := node4) (slot := 2) (occurrence := f4) ?_ ?_
  · rw [children_rootNode]; simp
  · simpa [f4] using
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
        (input := input.certified) (root := atom1) (path := [2]) (fuel := fuel)
        (node := node4))

theorem f5_mem : f5 ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom1 [] (fuel + 1) rootNode f5
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode)
    (child := node5) (slot := 3) (occurrence := f5) ?_ ?_
  · rw [children_rootNode]; simp
  · simpa [f5] using
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
        (input := input.certified) (root := atom1) (path := [3]) (fuel := fuel)
        (node := node5))

theorem f6_mem : f6 ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom1 [] (fuel + 1) rootNode f6
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode)
    (child := targetNode) (slot := 0) (occurrence := f6) ?_ ?_
  · rw [children_rootNode]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [0]) (fuel := fuel - 1) (node := targetNode)
      (child := outwardNode) (slot := 0) (occurrence := f6) ?_ ?_
    · rw [children_targetNode]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (path := [0, 0]) (fuel := fuel - 2) (node := outwardNode)
        (child := node6) (slot := 0) (occurrence := f6) ?_ ?_
      · rw [children_outwardNode]; simp
      · simpa [f6] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (input := input.certified) (root := atom1) (path := [0, 0, 0])
            (fuel := fuel - 2) (node := node6))

theorem f7_mem : f7 ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom1 [] (fuel + 1) rootNode f7
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode)
    (child := targetNode) (slot := 0) (occurrence := f7) ?_ ?_
  · rw [children_rootNode]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [0]) (fuel := fuel - 1) (node := targetNode)
      (child := outwardNode) (slot := 0) (occurrence := f7) ?_ ?_
    · rw [children_targetNode]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (path := [0, 0]) (fuel := fuel - 2) (node := outwardNode)
        (child := node7) (slot := 1) (occurrence := f7) ?_ ?_
      · rw [children_outwardNode]; simp
      · simpa [f7] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (input := input.certified) (root := atom1) (path := [0, 0, 1])
            (fuel := fuel - 2) (node := node7))

theorem f8_mem : f8 ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom1 [] (fuel + 1) rootNode f8
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode)
    (child := targetNode) (slot := 0) (occurrence := f8) ?_ ?_
  · rw [children_rootNode]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [0]) (fuel := fuel - 1) (node := targetNode)
      (child := outwardNode) (slot := 0) (occurrence := f8) ?_ ?_
    · rw [children_targetNode]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (path := [0, 0]) (fuel := fuel - 2) (node := outwardNode)
        (child := node8) (slot := 2) (occurrence := f8) ?_ ?_
      · rw [children_outwardNode]; simp
      · simpa [f8] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (input := input.certified) (root := atom1) (path := [0, 0, 2])
            (fuel := fuel - 2) (node := node8))

def f3Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨f3, f3_mem⟩
def f4Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨f4, f4_mem⟩
def f5Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨f5, f5_mem⟩
def f6Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨f6, f6_mem⟩
def f7Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨f7, f7_mem⟩
def f8Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨f8, f8_mem⟩

/-- The first ligand child cursor of the original root, reached from the target center. -/
def c3 : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := f3Occ, previous? := some rootOcc }

def c4 : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := f4Occ, previous? := some rootOcc }

def c5 : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := f5Occ, previous? := some rootOcc }


def c6 : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := f6Occ, previous? := some outwardOcc }

def c7 : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := f7Occ, previous? := some outwardOcc }

def c8 : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := f8Occ, previous? := some outwardOcc }

/-- A reroot cursor whose official node is a leaf and whose incoming cut is exactly the carrier
parent has no intended children: parent frames are removed by the cut and outward frames are
refuted by the empty official child list. -/
theorem intended_eq_nil_of_leaf_cut
    (cursor : input.certified.LocalizedRerootCursor fuel)
    (prev : input.certified.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some prev)
    (cutParent : prev.1.address = cursor.occurrence.1.address.dropLast)
    (leaf : input.certified.executableOfficialCIPChildren cursor.occurrence.1.node = []) :
    input.certified.intendedLocalizedRerootChildFrames cursor = [] := by
  unfold intendedLocalizedRerootChildFrames
  by_cases duplicate : cursor.occurrence.1.node.isDuplicateLeaf
  · simp [duplicate]
  · simp only [duplicate, Bool.false_eq_true, ↓reduceIte, previousEq]
    rw [List.eq_nil_iff_forall_not_mem]
    intro g gPresent
    rw [List.mem_filter] at gPresent
    rcases gPresent with ⟨gNeighbor, gAddressNe⟩
    rw [localizedRerootNeighborFrames, List.mem_append] at gNeighbor
    rcases gNeighbor with parentPresent | childPresent
    · rw [localizedCarrierParentFrames, List.mem_filter] at parentPresent
      rcases parentPresent with ⟨_gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have sameAddress : g.address = prev.1.address := by
        rw [conditions.2, cutParent]
      simp [sameAddress] at gAddressNe
    · rw [localizedCarrierOutwardChildFrames, List.mem_filter] at childPresent
      rcases childPresent with ⟨gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have gRoot : g.root = cursor.occurrence.1.root := conditions.1.1
      have gLength : g.address.length = cursor.occurrence.1.address.length + 1 :=
        conditions.1.2
      have gDrop : g.address.dropLast = cursor.occurrence.1.address := conditions.2
      have gNonempty : g.address ≠ [] := by
        intro empty
        rw [empty] at gLength
        simp at gLength
      let slot := g.address.getLast gNonempty
      have addressEq : g.address = cursor.occurrence.1.address ++ [slot] := by
        have := List.dropLast_append_getLast gNonempty
        rw [gDrop] at this
        exact this.symm
      have gDerived :=
        (input.certified.mem_localizedOccurrences_iff fuel g).mp gCarrier
      have sourceDerived :=
        (input.certified.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp
          cursor.occurrence.2
      obtain ⟨child, childAtSlot, _occurrenceEq⟩ :=
        input.certified.declarativeLocalizedOccurrence_immediate_child
          sourceDerived gDerived gRoot slot addressEq
      rw [leaf] at childAtSlot
      simp at childAtSlot

theorem c3_intended_nil :
    input.certified.intendedLocalizedRerootChildFrames c3 = [] :=
  intended_eq_nil_of_leaf_cut c3 rootOcc rfl (by decide +kernel) children_node3

theorem c4_intended_nil :
    input.certified.intendedLocalizedRerootChildFrames c4 = [] :=
  intended_eq_nil_of_leaf_cut c4 rootOcc rfl (by decide +kernel) children_node4

theorem c5_intended_nil :
    input.certified.intendedLocalizedRerootChildFrames c5 = [] :=
  intended_eq_nil_of_leaf_cut c5 rootOcc rfl (by decide +kernel) children_node5

theorem c6_intended_nil :
    input.certified.intendedLocalizedRerootChildFrames c6 = [] :=
  intended_eq_nil_of_leaf_cut c6 outwardOcc rfl (by decide +kernel) children_node6

theorem c7_intended_nil :
    input.certified.intendedLocalizedRerootChildFrames c7 = [] :=
  intended_eq_nil_of_leaf_cut c7 outwardOcc rfl (by decide +kernel) children_node7

theorem c8_intended_nil :
    input.certified.intendedLocalizedRerootChildFrames c8 = [] :=
  intended_eq_nil_of_leaf_cut c8 outwardOcc rfl (by decide +kernel) children_node8

/-- At a cursor with no intended children every declarative derivation is the terminal root key. -/
theorem declarativeKey_eq_rootKey_of_intended_nil
    {dFuel : Nat} {cursor : input.certified.LocalizedRerootCursor fuel}
    {key : OfficialRuleMajorKey Atom}
    (empty : input.certified.intendedLocalizedRerootChildFrames cursor = [])
    (derived : input.certified.DeclarativeLocalizedRerootRuleMajorKey dFuel cursor key) :
    key = graph.officialRuleMajorRootKey cursor.occurrence.1.node true := by
  cases derived with
  | terminal _frame _empty => rfl
  | @branch _ _ children _childKeys _sorted frame nonempty _childDerivations
      _ranking _descending =>
      have mapEmpty :
          (children.map (fun child => child.occurrence.1)) = [] := by
        rw [frame.1, empty]
      have childrenEmpty : children = [] := List.map_eq_nil_iff.mp mapEmpty
      exact absurd childrenEmpty nonempty

/-! ## Exact intended-child sets of the two compared cursors

The parent cursor has exactly the three H/F/Cl ligands of arm `1`; the outward cursor has
exactly the three H/F/Cl ligands of arm `2`.  These are set-level characterizations of the
actual cut neighbourhood, derived from the actual carrier relation and the actual official child
lists. -/

theorem parentNotDuplicate : parentCursor.occurrence.1.node.isDuplicateLeaf = false := by
  decide +kernel

theorem outwardNotDuplicate : outwardCursor.occurrence.1.node.isDuplicateLeaf = false := by
  decide +kernel

theorem rootNodeNotDuplicate : rootNode.isDuplicateLeaf = false := by
  decide +kernel

theorem outwardNodeNotDuplicate : outwardNode.isDuplicateLeaf = false := by
  decide +kernel

/-- After unfolding the cursor, the duplicate test appears at the occurrence's own node. -/
theorem rootOccNotDuplicate : rootOcc.1.node.isDuplicateLeaf = false := by
  decide +kernel

theorem outwardOccNotDuplicate : outwardOcc.1.node.isDuplicateLeaf = false := by
  decide +kernel

/-- The intended children of the parent cursor are exactly the three arm-`1` ligands. -/
theorem mem_intended_parentCursor_iff
    (g : input.certified.LocalizedCIPOccurrenceFrame) :
    g ∈ input.certified.intendedLocalizedRerootChildFrames parentCursor ↔
      g = f3 ∨ g = f4 ∨ g = f5 := by
  constructor
  · intro present
    simp only [intendedLocalizedRerootChildFrames, parentNotDuplicate, rootOccNotDuplicate,
      Bool.false_eq_true, ↓reduceIte, parentCursor, List.mem_filter] at present
    rcases present with ⟨neighbor, addressNe⟩
    rw [localizedRerootNeighborFrames, List.mem_append] at neighbor
    rcases neighbor with parentMem | childMem
    · rw [localizedCarrierParentFrames, List.mem_filter] at parentMem
      rcases parentMem with ⟨_gCarrier, cond⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at cond
      have parentLength : rootOcc.1.address.length = 0 := by decide +kernel
      omega
    · rw [localizedCarrierOutwardChildFrames, List.mem_filter] at childMem
      rcases childMem with ⟨gCarrier, cond⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at cond
      have gRoot : g.root = atom1 := by simpa [rootFrame] using cond.1.1
      have gLength : g.address.length = 1 := by simpa [rootFrame] using cond.1.2
      have gDrop : g.address.dropLast = [] := by simpa [rootFrame] using cond.2
      have addressNe' : g.address ≠ targetOcc.1.address := by
        intro equal
        rw [equal] at addressNe
        simp at addressNe
      have gNonempty : g.address ≠ [] := by
        intro empty
        rw [empty] at gLength
        simp at gLength
      let slot := g.address.getLast gNonempty
      have addressEq : g.address = rootFrame.address ++ [slot] := by
        have := List.dropLast_append_getLast gNonempty
        rw [gDrop] at this
        simpa [rootFrame] using this.symm
      have gDerived :=
        (input.certified.mem_localizedOccurrences_iff fuel g).mp gCarrier
      have sourceDerived :=
        (input.certified.mem_localizedOccurrences_iff fuel rootFrame).mp rootFrame_mem
      obtain ⟨child, childAtSlot, gEq⟩ :=
        input.certified.declarativeLocalizedOccurrence_immediate_child
          sourceDerived gDerived (by simpa [rootFrame] using gRoot) slot addressEq
      rw [show rootFrame.node = rootNode from rfl] at childAtSlot
      rw [children_rootNode] at childAtSlot
      have childCases : (child, slot) = (targetNode, 0) ∨
          (child, slot) = (node3, 1) ∨ (child, slot) = (node4, 2) ∨
          (child, slot) = (node5, 3) := by
        simpa using childAtSlot
      have slotNe : slot ≠ 0 := by
        intro zero
        apply addressNe'
        rw [gEq]
        simp [rootFrame, targetOcc, targetFrame, zero]
      rcases childCases with identity | identity | identity | identity
      · exact absurd (congrArg Prod.snd identity) slotNe
      · left
        injection identity with childEq slotEq
        rw [childEq, slotEq] at gEq
        rw [gEq]
        rfl
      · right; left
        injection identity with childEq slotEq
        rw [childEq, slotEq] at gEq
        rw [gEq]
        rfl
      · right; right
        injection identity with childEq slotEq
        rw [childEq, slotEq] at gEq
        rw [gEq]
        rfl
  · rintro (rfl | rfl | rfl)
    · simp only [intendedLocalizedRerootChildFrames, parentNotDuplicate, rootOccNotDuplicate,
        Bool.false_eq_true, ↓reduceIte, parentCursor, List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨f3_mem, by simp [f3, rootOcc, rootFrame]⟩
      · simp [f3, targetOcc, targetFrame]
    · simp only [intendedLocalizedRerootChildFrames, parentNotDuplicate, rootOccNotDuplicate,
        Bool.false_eq_true, ↓reduceIte, parentCursor, List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨f4_mem, by simp [f4, rootOcc, rootFrame]⟩
      · simp [f4, targetOcc, targetFrame]
    · simp only [intendedLocalizedRerootChildFrames, parentNotDuplicate, rootOccNotDuplicate,
        Bool.false_eq_true, ↓reduceIte, parentCursor, List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨f5_mem, by simp [f5, rootOcc, rootFrame]⟩
      · simp [f5, targetOcc, targetFrame]

/-- The intended children of the outward cursor are exactly the three arm-`2` ligands. -/
theorem mem_intended_outwardCursor_iff
    (g : input.certified.LocalizedCIPOccurrenceFrame) :
    g ∈ input.certified.intendedLocalizedRerootChildFrames outwardCursor ↔
      g = f6 ∨ g = f7 ∨ g = f8 := by
  constructor
  · intro present
    simp only [intendedLocalizedRerootChildFrames, outwardNotDuplicate, outwardOccNotDuplicate,
      Bool.false_eq_true, ↓reduceIte, outwardCursor, List.mem_filter] at present
    rcases present with ⟨neighbor, addressNe⟩
    rw [localizedRerootNeighborFrames, List.mem_append] at neighbor
    rcases neighbor with parentMem | childMem
    · rw [localizedCarrierParentFrames, List.mem_filter] at parentMem
      rcases parentMem with ⟨_gCarrier, cond⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at cond
      have sameAddress : g.address = targetOcc.1.address := by
        rw [cond.2]
        simp [outwardOcc, outwardFrame, targetOcc, targetFrame]
      rw [sameAddress] at addressNe
      simp at addressNe
    · rw [localizedCarrierOutwardChildFrames, List.mem_filter] at childMem
      rcases childMem with ⟨gCarrier, cond⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at cond
      have gRoot : g.root = atom1 := by simpa [outwardFrame] using cond.1.1
      have gLength : g.address.length = 3 := by simpa [outwardFrame] using cond.1.2
      have gDrop : g.address.dropLast = [0, 0] := by simpa [outwardFrame] using cond.2
      have gNonempty : g.address ≠ [] := by
        intro empty
        rw [empty] at gLength
        simp at gLength
      let slot := g.address.getLast gNonempty
      have addressEq : g.address = outwardFrame.address ++ [slot] := by
        have := List.dropLast_append_getLast gNonempty
        rw [gDrop] at this
        simpa [outwardFrame] using this.symm
      have gDerived :=
        (input.certified.mem_localizedOccurrences_iff fuel g).mp gCarrier
      have sourceDerived :=
        (input.certified.mem_localizedOccurrences_iff fuel outwardFrame).mp outwardFrame_mem
      obtain ⟨child, childAtSlot, gEq⟩ :=
        input.certified.declarativeLocalizedOccurrence_immediate_child
          sourceDerived gDerived (by simpa [outwardFrame] using gRoot) slot addressEq
      rw [show outwardFrame.node = outwardNode from rfl] at childAtSlot
      rw [children_outwardNode] at childAtSlot
      have childCases : (child, slot) = (node6, 0) ∨
          (child, slot) = (node7, 1) ∨ (child, slot) = (node8, 2) := by
        simpa using childAtSlot
      rcases childCases with identity | identity | identity
      · left
        injection identity with childEq slotEq
        rw [childEq, slotEq] at gEq
        rw [gEq]
        rfl
      · right; left
        injection identity with childEq slotEq
        rw [childEq, slotEq] at gEq
        rw [gEq]
        rfl
      · right; right
        injection identity with childEq slotEq
        rw [childEq, slotEq] at gEq
        rw [gEq]
        rfl
  · rintro (rfl | rfl | rfl)
    · simp only [intendedLocalizedRerootChildFrames, outwardNotDuplicate,
        outwardOccNotDuplicate, Bool.false_eq_true, ↓reduceIte, outwardCursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨f6_mem, by simp [f6, outwardOcc, outwardFrame]⟩
      · simp [f6, targetOcc, targetFrame]
    · simp only [intendedLocalizedRerootChildFrames, outwardNotDuplicate,
        outwardOccNotDuplicate, Bool.false_eq_true, ↓reduceIte, outwardCursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨f7_mem, by simp [f7, outwardOcc, outwardFrame]⟩
      · simp [f7, targetOcc, targetFrame]
    · simp only [intendedLocalizedRerootChildFrames, outwardNotDuplicate,
        outwardOccNotDuplicate, Bool.false_eq_true, ↓reduceIte, outwardCursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨f8_mem, by simp [f8, outwardOcc, outwardFrame]⟩
      · simp [f8, targetOcc, targetFrame]

theorem f3_intended : f3 ∈ input.certified.intendedLocalizedRerootChildFrames parentCursor :=
  (mem_intended_parentCursor_iff f3).mpr (Or.inl rfl)

theorem f4_intended : f4 ∈ input.certified.intendedLocalizedRerootChildFrames parentCursor :=
  (mem_intended_parentCursor_iff f4).mpr (Or.inr (Or.inl rfl))

theorem f5_intended : f5 ∈ input.certified.intendedLocalizedRerootChildFrames parentCursor :=
  (mem_intended_parentCursor_iff f5).mpr (Or.inr (Or.inr rfl))

theorem f6_intended : f6 ∈ input.certified.intendedLocalizedRerootChildFrames outwardCursor :=
  (mem_intended_outwardCursor_iff f6).mpr (Or.inl rfl)

theorem f7_intended : f7 ∈ input.certified.intendedLocalizedRerootChildFrames outwardCursor :=
  (mem_intended_outwardCursor_iff f7).mpr (Or.inr (Or.inl rfl))

theorem f8_intended : f8 ∈ input.certified.intendedLocalizedRerootChildFrames outwardCursor :=
  (mem_intended_outwardCursor_iff f8).mpr (Or.inr (Or.inr rfl))

/-- A frame in the intended cut-neighbourhood gives an actual executable child cursor. -/
theorem mem_executable_of_mem_intended
    (cursor : input.certified.LocalizedRerootCursor fuel)
    (frame : input.certified.LocalizedCIPOccurrenceFrame)
    (present : frame ∈ input.certified.intendedLocalizedRerootChildFrames cursor) :
    ({ occurrence :=
         ⟨frame,
           input.certified.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames
             cursor frame present⟩
       previous? := some cursor.occurrence } :
        input.certified.LocalizedRerootCursor fuel) ∈
      input.certified.executableLocalizedRerootChildren cursor := by
  unfold executableLocalizedRerootChildren
  rw [List.mem_map]
  exact ⟨⟨frame, present⟩, List.mem_attach _ _, rfl⟩

theorem c3_mem : c3 ∈ input.certified.executableLocalizedRerootChildren parentCursor := by
  have h := mem_executable_of_mem_intended parentCursor f3 f3_intended
  unfold executableLocalizedRerootChildren at h ⊢
  rw [List.mem_map] at h ⊢
  rcases h with ⟨frame, frameMem, equality⟩
  exact ⟨frame, frameMem, by
    rw [equality]
    apply LocalizedRerootCursor.ext input.certified
    · apply Subtype.ext rfl
    · rfl⟩

theorem c4_mem : c4 ∈ input.certified.executableLocalizedRerootChildren parentCursor := by
  have h := mem_executable_of_mem_intended parentCursor f4 f4_intended
  unfold executableLocalizedRerootChildren at h ⊢
  rw [List.mem_map] at h ⊢
  rcases h with ⟨frame, frameMem, equality⟩
  exact ⟨frame, frameMem, by
    rw [equality]
    apply LocalizedRerootCursor.ext input.certified
    · apply Subtype.ext rfl
    · rfl⟩

theorem c5_mem : c5 ∈ input.certified.executableLocalizedRerootChildren parentCursor := by
  have h := mem_executable_of_mem_intended parentCursor f5 f5_intended
  unfold executableLocalizedRerootChildren at h ⊢
  rw [List.mem_map] at h ⊢
  rcases h with ⟨frame, frameMem, equality⟩
  exact ⟨frame, frameMem, by
    rw [equality]
    apply LocalizedRerootCursor.ext input.certified
    · apply Subtype.ext rfl
    · rfl⟩

theorem c6_mem : c6 ∈ input.certified.executableLocalizedRerootChildren outwardCursor := by
  have h := mem_executable_of_mem_intended outwardCursor f6 f6_intended
  unfold executableLocalizedRerootChildren at h ⊢
  rw [List.mem_map] at h ⊢
  rcases h with ⟨frame, frameMem, equality⟩
  exact ⟨frame, frameMem, by
    rw [equality]
    apply LocalizedRerootCursor.ext input.certified
    · apply Subtype.ext rfl
    · rfl⟩

theorem c7_mem : c7 ∈ input.certified.executableLocalizedRerootChildren outwardCursor := by
  have h := mem_executable_of_mem_intended outwardCursor f7 f7_intended
  unfold executableLocalizedRerootChildren at h ⊢
  rw [List.mem_map] at h ⊢
  rcases h with ⟨frame, frameMem, equality⟩
  exact ⟨frame, frameMem, by
    rw [equality]
    apply LocalizedRerootCursor.ext input.certified
    · apply Subtype.ext rfl
    · rfl⟩

theorem c8_mem : c8 ∈ input.certified.executableLocalizedRerootChildren outwardCursor := by
  have h := mem_executable_of_mem_intended outwardCursor f8 f8_intended
  unfold executableLocalizedRerootChildren at h ⊢
  rw [List.mem_map] at h ⊢
  rcases h with ⟨frame, frameMem, equality⟩
  exact ⟨frame, frameMem, by
    rw [equality]
    apply LocalizedRerootCursor.ext input.certified
    · apply Subtype.ext rfl
    · rfl⟩

/-! ## Exact auxiliary keys and declarative branch derivations

The three ligand children of each compared cursor are terminated by the actual empty official
child lists proved above, so their keys are the actual root keys of their actual provenance
nodes.  The two compared cursor keys are therefore the literal assembled keys below; no key is
fabricated and no sort is assumed beyond the proved descending order of the actual Z values. -/

/-- The official root key of one actual carrier frame's provenance node, marked complete. -/
def frameKey (frame : input.certified.LocalizedCIPOccurrenceFrame) :
    OfficialRuleMajorKey Atom :=
  graph.officialRuleMajorRootKey frame.node true

def k3 : OfficialRuleMajorKey Atom := frameKey f3
def k4 : OfficialRuleMajorKey Atom := frameKey f4
def k5 : OfficialRuleMajorKey Atom := frameKey f5
def k6 : OfficialRuleMajorKey Atom := frameKey f6
def k7 : OfficialRuleMajorKey Atom := frameKey f7
def k8 : OfficialRuleMajorKey Atom := frameKey f8

/-- The actual parent-side auxiliary key: a nonterminal root over the descending arm-`1` leaves. -/
def parentAuxKey : OfficialRuleMajorKey Atom :=
  OfficialRuleMajorKey.assemble (graph.officialRuleMajorRootKey rootNode false) [k5, k4, k3]

/-- The actual outward-side auxiliary key: a nonterminal root over the descending arm-`2` leaves. -/
def outwardAuxKey : OfficialRuleMajorKey Atom :=
  OfficialRuleMajorKey.assemble (graph.officialRuleMajorRootKey outwardNode false) [k8, k7, k6]

theorem f3_ne_f4 : f3 ≠ f4 := by
  intro h
  have := congrArg (fun frame => frame.address) h
  simp [f3, f4] at this

theorem f3_ne_f5 : f3 ≠ f5 := by
  intro h
  have := congrArg (fun frame => frame.address) h
  simp [f3, f5] at this

theorem f4_ne_f5 : f4 ≠ f5 := by
  intro h
  have := congrArg (fun frame => frame.address) h
  simp [f4, f5] at this

theorem f6_ne_f7 : f6 ≠ f7 := by
  intro h
  have := congrArg (fun frame => frame.address) h
  simp [f6, f7] at this

theorem f6_ne_f8 : f6 ≠ f8 := by
  intro h
  have := congrArg (fun frame => frame.address) h
  simp [f6, f8] at this

theorem f7_ne_f8 : f7 ≠ f8 := by
  intro h
  have := congrArg (fun frame => frame.address) h
  simp [f7, f8] at this

theorem nodup_three : [f3, f4, f5].Nodup := by
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · rw [List.mem_cons]
    rintro (h | h)
    · exact f3_ne_f4 h
    · rw [List.mem_singleton] at h
      exact f3_ne_f5 h
  · rw [List.nodup_cons]
    exact ⟨by simpa using f4_ne_f5, by simp⟩

theorem nodup_three_out : [f6, f7, f8].Nodup := by
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · rw [List.mem_cons]
    rintro (h | h)
    · exact f6_ne_f7 h
    · rw [List.mem_singleton] at h
      exact f6_ne_f8 h
  · rw [List.nodup_cons]
    exact ⟨by simpa using f7_ne_f8, by simp⟩

theorem mem_three_iff (g : input.certified.LocalizedCIPOccurrenceFrame) :
    g ∈ [f3, f4, f5] ↔ g = f3 ∨ g = f4 ∨ g = f5 := by
  simp

theorem mem_three_out_iff (g : input.certified.LocalizedCIPOccurrenceFrame) :
    g ∈ [f6, f7, f8] ↔ g = f6 ∨ g = f7 ∨ g = f8 := by
  simp

theorem intended_parentCursor_perm :
    (input.certified.intendedLocalizedRerootChildFrames parentCursor).Perm [f3, f4, f5] :=
  (List.perm_ext_iff_of_nodup
    (input.certified.intendedLocalizedRerootChildFrames_nodup parentCursor) nodup_three).mpr
    (fun g => by rw [mem_intended_parentCursor_iff g, mem_three_iff g])

theorem intended_outwardCursor_perm :
    (input.certified.intendedLocalizedRerootChildFrames outwardCursor).Perm [f6, f7, f8] :=
  (List.perm_ext_iff_of_nodup
    (input.certified.intendedLocalizedRerootChildFrames_nodup outwardCursor) nodup_three_out).mpr
    (fun g => by rw [mem_intended_outwardCursor_iff g, mem_three_out_iff g])

/-- The actual strict-Z descending order of the arm-`1` leaves: Cl, then F, then H. -/
theorem perm_sort_parent : [k5, k4, k3].Perm [k3, k4, k5] := by
  have h45 : [k5, k4].Perm [k4, k5] := List.perm_append_comm (l₁ := [k5]) (l₂ := [k4])
  exact (List.perm_append_comm (l₁ := [k5, k4]) (l₂ := [k3])).trans (h45.cons k3)

/-- The actual strict-Z descending order of the arm-`2` leaves: Cl, then F, then H. -/
theorem perm_sort_outward : [k8, k7, k6].Perm [k6, k7, k8] := by
  have h67 : [k8, k7].Perm [k7, k8] := List.perm_append_comm (l₁ := [k8]) (l₂ := [k7])
  exact (List.perm_append_comm (l₁ := [k8, k7]) (l₂ := [k6])).trans (h67.cons k6)

theorem childKeys_parent_eq :
    (input.certified.executableLocalizedRerootChildren parentCursor).map
        (fun c => frameKey c.occurrence.1) =
      (input.certified.intendedLocalizedRerootChildFrames parentCursor).map frameKey := by
  change List.map (frameKey ∘ fun c => c.occurrence.1)
      (input.certified.executableLocalizedRerootChildren parentCursor) =
    List.map frameKey (input.certified.intendedLocalizedRerootChildFrames parentCursor)
  rw [← List.map_map]
  rw [input.certified.executableLocalizedRerootChildren_map parentCursor]

theorem childKeys_outward_eq :
    (input.certified.executableLocalizedRerootChildren outwardCursor).map
        (fun c => frameKey c.occurrence.1) =
      (input.certified.intendedLocalizedRerootChildFrames outwardCursor).map frameKey := by
  change List.map (frameKey ∘ fun c => c.occurrence.1)
      (input.certified.executableLocalizedRerootChildren outwardCursor) =
    List.map frameKey (input.certified.intendedLocalizedRerootChildFrames outwardCursor)
  rw [← List.map_map]
  rw [input.certified.executableLocalizedRerootChildren_map outwardCursor]

theorem ranking_parent :
    [k5, k4, k3].Perm
      ((input.certified.executableLocalizedRerootChildren parentCursor).map
        (fun c => frameKey c.occurrence.1)) := by
  rw [childKeys_parent_eq]
  have hmap := intended_parentCursor_perm.map frameKey
  have hthree : List.map frameKey [f3, f4, f5] = [k3, k4, k5] := rfl
  rw [hthree] at hmap
  exact perm_sort_parent.trans hmap.symm

theorem ranking_outward :
    [k8, k7, k6].Perm
      ((input.certified.executableLocalizedRerootChildren outwardCursor).map
        (fun c => frameKey c.occurrence.1)) := by
  rw [childKeys_outward_eq]
  have hmap := intended_outwardCursor_perm.map frameKey
  have hthree : List.map frameKey [f6, f7, f8] = [k6, k7, k8] := rfl
  rw [hthree] at hmap
  exact perm_sort_outward.trans hmap.symm

/-- An empty intended cut-neighbourhood makes the executable child list itself empty. -/
theorem executableChildren_eq_nil_of_intended_eq_nil
    (cursor : input.certified.LocalizedRerootCursor fuel)
    (empty : input.certified.intendedLocalizedRerootChildFrames cursor = []) :
    input.certified.executableLocalizedRerootChildren cursor = [] := by
  have mapEq := input.certified.executableLocalizedRerootChildren_map cursor
  rw [empty] at mapEq
  exact List.map_eq_nil_iff.mp mapEq

/-- A list of terminal leaf children contributes exactly its own root keys. -/
theorem declarativeList_of_terminal (dFuel : Nat)
    (cs : List (input.certified.LocalizedRerootCursor fuel))
    (empty : ∀ c ∈ cs, input.certified.intendedLocalizedRerootChildFrames c = []) :
    input.certified.DeclarativeLocalizedRerootRuleMajorKeyList dFuel cs
      (cs.map (fun c => frameKey c.occurrence.1)) := by
  induction cs with
  | nil => exact DeclarativeLocalizedRerootRuleMajorKeyList.nil dFuel
  | cons c cs ih =>
      exact DeclarativeLocalizedRerootRuleMajorKeyList.cons
        (DeclarativeLocalizedRerootRuleMajorKey.terminal
          (input.certified.executableLocalizedRerootChildren_declarative c)
          (executableChildren_eq_nil_of_intended_eq_nil c (empty c (by simp))))
        (ih (fun c' hc' => empty c' (by simp [hc'])))

theorem parentChildren_empty :
    ∀ c ∈ input.certified.executableLocalizedRerootChildren parentCursor,
      input.certified.intendedLocalizedRerootChildFrames c = [] := by
  intro c hc
  have frameMem : c.occurrence.1 ∈
      input.certified.intendedLocalizedRerootChildFrames parentCursor := by
    rw [← input.certified.executableLocalizedRerootChildren_map parentCursor]
    exact List.mem_map_of_mem (f := fun child => child.occurrence.1) hc
  rcases (mem_intended_parentCursor_iff c.occurrence.1).mp frameMem with h3 | h4 | h5
  · have cursorEq : c = c3 := by
      apply LocalizedRerootCursor.ext input.certified
      · apply Subtype.ext h3
      · rw [input.certified.executableLocalizedRerootChildren_previous parentCursor c hc]
        simp [parentCursor, c3]
    rw [cursorEq]
    exact c3_intended_nil
  · have cursorEq : c = c4 := by
      apply LocalizedRerootCursor.ext input.certified
      · apply Subtype.ext h4
      · rw [input.certified.executableLocalizedRerootChildren_previous parentCursor c hc]
        simp [parentCursor, c4]
    rw [cursorEq]
    exact c4_intended_nil
  · have cursorEq : c = c5 := by
      apply LocalizedRerootCursor.ext input.certified
      · apply Subtype.ext h5
      · rw [input.certified.executableLocalizedRerootChildren_previous parentCursor c hc]
        simp [parentCursor, c5]
    rw [cursorEq]
    exact c5_intended_nil

theorem outwardChildren_empty :
    ∀ c ∈ input.certified.executableLocalizedRerootChildren outwardCursor,
      input.certified.intendedLocalizedRerootChildFrames c = [] := by
  intro c hc
  have frameMem : c.occurrence.1 ∈
      input.certified.intendedLocalizedRerootChildFrames outwardCursor := by
    rw [← input.certified.executableLocalizedRerootChildren_map outwardCursor]
    exact List.mem_map_of_mem (f := fun child => child.occurrence.1) hc
  rcases (mem_intended_outwardCursor_iff c.occurrence.1).mp frameMem with h6 | h7 | h8
  · have cursorEq : c = c6 := by
      apply LocalizedRerootCursor.ext input.certified
      · apply Subtype.ext h6
      · rw [input.certified.executableLocalizedRerootChildren_previous outwardCursor c hc]
        simp [outwardCursor, c6]
    rw [cursorEq]
    exact c6_intended_nil
  · have cursorEq : c = c7 := by
      apply LocalizedRerootCursor.ext input.certified
      · apply Subtype.ext h7
      · rw [input.certified.executableLocalizedRerootChildren_previous outwardCursor c hc]
        simp [outwardCursor, c7]
    rw [cursorEq]
    exact c7_intended_nil
  · have cursorEq : c = c8 := by
      apply LocalizedRerootCursor.ext input.certified
      · apply Subtype.ext h8
      · rw [input.certified.executableLocalizedRerootChildren_previous outwardCursor c hc]
        simp [outwardCursor, c8]
    rw [cursorEq]
    exact c8_intended_nil

theorem parentChildren_nonempty :
    input.certified.executableLocalizedRerootChildren parentCursor ≠ [] := by
  intro h
  have intendedNil :
      input.certified.intendedLocalizedRerootChildFrames parentCursor = [] := by
    rw [← input.certified.executableLocalizedRerootChildren_map parentCursor, h]
    rfl
  have mem := f3_intended
  rw [intendedNil] at mem
  simp at mem

theorem outwardChildren_nonempty :
    input.certified.executableLocalizedRerootChildren outwardCursor ≠ [] := by
  intro h
  have intendedNil :
      input.certified.intendedLocalizedRerootChildFrames outwardCursor = [] := by
    rw [← input.certified.executableLocalizedRerootChildren_map outwardCursor, h]
    rfl
  have mem := f6_intended
  rw [intendedNil] at mem
  simp at mem

/-- One-step declarative derivation of the actual parent-side auxiliary key. -/
theorem declarative_parentAux (dFuel : Nat) :
    input.certified.DeclarativeLocalizedRerootRuleMajorKey (dFuel + 1) parentCursor
      parentAuxKey := by
  exact DeclarativeLocalizedRerootRuleMajorKey.branch
    (input.certified.executableLocalizedRerootChildren_declarative parentCursor)
    parentChildren_nonempty
    (declarativeList_of_terminal dFuel
      (input.certified.executableLocalizedRerootChildren parentCursor) parentChildren_empty)
    ranking_parent
    (by
      unfold OfficialRuleMajorKey.Descending
      decide +kernel)

/-- One-step declarative derivation of the actual outward-side auxiliary key. -/
theorem declarative_outwardAux (dFuel : Nat) :
    input.certified.DeclarativeLocalizedRerootRuleMajorKey (dFuel + 1) outwardCursor
      outwardAuxKey := by
  exact DeclarativeLocalizedRerootRuleMajorKey.branch
    (input.certified.executableLocalizedRerootChildren_declarative outwardCursor)
    outwardChildren_nonempty
    (declarativeList_of_terminal dFuel
      (input.certified.executableLocalizedRerootChildren outwardCursor) outwardChildren_empty)
    ranking_outward
    (by
      unfold OfficialRuleMajorKey.Descending
      decide +kernel)

/-- The parent-side auxiliary derivation at any positive budget, the form in which the shared
parametric builder states its own derivation. -/
theorem declarative_parentAux_any (f : Nat) (positive : 0 < f) :
    input.certified.DeclarativeLocalizedRerootRuleMajorKey f parentCursor parentAuxKey := by
  cases f with
  | zero => exact absurd positive (Nat.lt_irrefl 0)
  | succ d => simpa [Nat.succ_eq_add_one] using declarative_parentAux d

/-- The outward-side auxiliary derivation at any positive budget. -/
theorem declarative_outwardAux_any (f : Nat) (positive : 0 < f) :
    input.certified.DeclarativeLocalizedRerootRuleMajorKey f outwardCursor outwardAuxKey := by
  cases f with
  | zero => exact absurd positive (Nat.lt_irrefl 0)
  | succ d => simpa [Nat.succ_eq_add_one] using declarative_outwardAux d

/-! ## The actual auxiliary Rule-1a tables

Both auxiliary keys describe the same physical centre carbon `0` with three leaf ligands whose
atomic numbers are `Cl = 17`, `F = 9`, `H = 1` in the proved strict-Z sibling order.  The root
sphere carries the centre's atomic number `6`; the first child sphere carries the descending
ligand entries with slot addresses `[0]`, `[1]`, `[2]`. -/

theorem parentAuxKey_rule1a :
    parentAuxKey.rule1a = [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]] := by
  decide +kernel

theorem outwardAuxKey_rule1a :
    outwardAuxKey.rule1a = [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]] := by
  decide +kernel

/-- The original root `1` is the root of the shared auxiliary digraph: total Rule-1b distance
`0`. -/
theorem rootNode_rule1bRootDistance : rootNode.rule1bRootDistance = 0 := by
  decide +kernel

/-- The outward arm `2` is two edges from the original root: total Rule-1b distance `2`. -/
theorem outwardNode_rule1bRootDistance : outwardNode.rule1bRootDistance = 2 := by
  decide +kernel

theorem parentCursor_node : parentCursor.occurrence.1.node = rootNode := rfl

theorem outwardCursor_node : outwardCursor.occurrence.1.node = outwardNode := rfl

/-! ## Every reader compiles the same auxiliary Rule-1a table

The two `Built` fields of any comparison witness feed the shared parametric soundness lemma, and
the concrete auxiliary derivations above feed `declarative_constitutional_observable_unique`.
Hence the first constitutional projection is pinned for an *arbitrary* label reader and an
arbitrary dependency view.  Only the proof-relevant cursor and the two builder successes are used. -/

theorem parentKey_constitutional_rule1a
    {view : input.certified.LocalizedDependencyView targetOcc}
    {readLabel : input.certified.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    (w : ParentOutwardComparisonWitness input.certified .rule4a readLabel targetOcc view
      parentCursor outwardCursor) :
    w.parentKey.constitutional.rule1a =
      [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]] := by
  have declared :=
    input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
      .rule4a readLabel (2 * (fuel + 1)) parentCursor w.parentKey w.parentBuilt
  have auxDerived := declarative_parentAux_any (2 * (fuel + 1))
    (by omega)
  have observable :=
    input.certified.declarative_constitutional_observable_unique (2 * (fuel + 1))
      (2 * (fuel + 1)) parentCursor w.parentKey.constitutional parentAuxKey declared auxDerived
  have rule1aEq := congrArg LocalizedConstitutionalObservable.rule1a observable
  simp only [constitutionalObservable] at rule1aEq
  exact rule1aEq.trans parentAuxKey_rule1a

theorem childKey_constitutional_rule1a
    {view : input.certified.LocalizedDependencyView targetOcc}
    {readLabel : input.certified.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    (w : ParentOutwardComparisonWitness input.certified .rule4a readLabel targetOcc view
      parentCursor outwardCursor) :
    w.childKey.constitutional.rule1a =
      [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]] := by
  have declared :=
    input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead?_constitutional_declarative
      .rule4a readLabel (2 * (fuel + 1)) outwardCursor w.childKey w.childBuilt
  have auxDerived := declarative_outwardAux_any (2 * (fuel + 1))
    (by omega)
  have observable :=
    input.certified.declarative_constitutional_observable_unique (2 * (fuel + 1))
      (2 * (fuel + 1)) outwardCursor w.childKey.constitutional outwardAuxKey declared auxDerived
  have rule1aEq := congrArg LocalizedConstitutionalObservable.rule1a observable
  simp only [constitutionalObservable] at rule1aEq
  exact rule1aEq.trans outwardAuxKey_rule1a

theorem parentChild_rule1a_compare_eq
    {view : input.certified.LocalizedDependencyView targetOcc}
    {readLabel : input.certified.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    (w : ParentOutwardComparisonWitness input.certified .rule4a readLabel targetOcc view
      parentCursor outwardCursor) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      w.parentKey.constitutional.rule1a w.childKey.constitutional.rule1a =
        Ordering.eq := by
  rw [parentKey_constitutional_rule1a w, childKey_constitutional_rule1a w]
  decide +kernel

/-- **Every reader gives the strict parent-first auxiliary outcome.**

Whatever the reader and the dependency view, the two compared auxiliary keys have the same
Rule-1a table, and the parent sphere is `0` while the outward sphere is `2`, so Rule 1b decides
`gt` (nearer duplicate root first) even though the outward carbon is the heavier isotope. -/
theorem everyReader_parentChild_compare_gt
    {view : input.certified.LocalizedDependencyView targetOcc}
    {readLabel : input.certified.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    (w : ParentOutwardComparisonWitness input.certified .rule4a readLabel targetOcc view
      parentCursor outwardCursor) :
    OfficialRuleMajorKey.compare w.parentKey.constitutional w.childKey.constitutional =
      Ordering.gt := by
  have parentHead : w.parentKey.constitutional.rule1b.head? = some [([], 0)] := by
    have h := w.parentHead
    rw [parentCursor_node, rootNode_rule1bRootDistance] at h
    exact h
  have childHead : w.childKey.constitutional.rule1b.head? = some [([], 2)] := by
    have h := w.childHead
    rw [outwardCursor_node, outwardNode_rule1bRootDistance] at h
    exact h
  exact OfficialRuleMajorKey.compare_eq_gt_of_rule1a_eq_of_head_lt
    (parentChild_rule1a_compare_eq w) parentHead childHead (by decide)

/-- The shipped restricted-view keys have the same strict outcome as every arbitrary reader. -/
theorem everyReader_actual_compare_gt
    {view : input.certified.LocalizedDependencyView targetOcc}
    {readLabel : input.certified.LocalizedRerootCursor fuel → Option LocalizedAuxiliaryLabel}
    (w : ParentOutwardComparisonWitness input.certified .rule4a readLabel targetOcc view
      parentCursor outwardCursor) :
    OfficialRuleMajorKey.compare w.actualParentKey.constitutional
      w.actualChildKey.constitutional = Ordering.gt := by
  rw [← w.constitutionalCompare_eq_actual]
  exact everyReader_parentChild_compare_gt w

/-! ## The independently specified fresh-root comparison at the centre carbon

The auxiliary comparison above is computed on the *shared* digraph rooted at the original root
`1`, so its Rule 1b values are distances from that root.  The fresh-root specification instead
places the root at the centre carbon `0` and compares the two physical arms as rooted branches.
The branch nodes below are the same actual atoms of the same actual graph; only the rooting is
independent. -/

def freshRootNode : OfficialCIPNode Atom := OfficialCIPNode.root atom0

def freshBranch1 : OfficialCIPNode Atom := freshRootNode.extend atom1 0

def freshBranch2 : OfficialCIPNode Atom := freshRootNode.extend atom2 0

def freshLeaf3 : OfficialCIPNode Atom := freshBranch1.extend atom3 0
def freshLeaf4 : OfficialCIPNode Atom := freshBranch1.extend atom4 0
def freshLeaf5 : OfficialCIPNode Atom := freshBranch1.extend atom5 0

def freshLeaf6 : OfficialCIPNode Atom := freshBranch2.extend atom6 0
def freshLeaf7 : OfficialCIPNode Atom := freshBranch2.extend atom7 0
def freshLeaf8 : OfficialCIPNode Atom := freshBranch2.extend atom8 0

/-- Fresh-root branch through the `12C` arm `1`, with its `H`/`F`/`Cl` leaves in descending Z
slot order. -/
def freshBranch1Key : OfficialRuleMajorKey Atom :=
  OfficialRuleMajorKey.assemble (graph.officialRuleMajorRootKey freshBranch1 false)
    [graph.officialRuleMajorRootKey freshLeaf5 true,
     graph.officialRuleMajorRootKey freshLeaf4 true,
     graph.officialRuleMajorRootKey freshLeaf3 true]

/-- Fresh-root branch through the `13C` arm `2`, with its `H`/`F`/`Cl` leaves in descending Z
slot order. -/
def freshBranch2Key : OfficialRuleMajorKey Atom :=
  OfficialRuleMajorKey.assemble (graph.officialRuleMajorRootKey freshBranch2 false)
    [graph.officialRuleMajorRootKey freshLeaf8 true,
     graph.officialRuleMajorRootKey freshLeaf7 true,
     graph.officialRuleMajorRootKey freshLeaf6 true]

theorem freshBranch1_rule1bRootDistance : freshBranch1.rule1bRootDistance = 1 := by
  decide +kernel

theorem freshBranch2_rule1bRootDistance : freshBranch2.rule1bRootDistance = 1 := by
  decide +kernel

/-- Equal Rule-1a tables: both branches are a `6` centre over `Cl`, `F`, `H` leaves. -/
theorem freshBranch1Key_rule1a :
    freshBranch1Key.rule1a = [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]] := by
  decide +kernel

theorem freshBranch2Key_rule1a :
    freshBranch2Key.rule1a = [[([], 6)], [([0], 17), ([1], 9), ([2], 1)]] := by
  decide +kernel

/-- Equal Rule-1b tables: both branch roots sit at the common fresh-root distance `1` and both
leaf spheres at distance `2` in the same sibling slots. -/
theorem freshBranch1Key_rule1b :
    freshBranch1Key.rule1b = [[([], 1)], [([0], 2), ([1], 2), ([2], 2)]] := by
  decide +kernel

theorem freshBranch2Key_rule1b :
    freshBranch2Key.rule1b = [[([], 1)], [([0], 2), ([1], 2), ([2], 2)]] := by
  decide +kernel

theorem freshBranch1Key_rule2_head :
    freshBranch1Key.rule2.head? = some [([], graph.atomMass atom1)] := by
  decide +kernel

theorem freshBranch2Key_rule2_head :
    freshBranch2Key.rule2.head? = some [([], graph.atomMass atom2)] := by
  decide +kernel

/-- The `12C` label carries smaller Rule-2 mass than the `13C` label. -/
theorem atomMass_atom1_lt_atom2 : graph.atomMass atom1 < graph.atomMass atom2 := by
  decide +kernel

theorem freshBranch_rule1a_compare_eq :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      freshBranch1Key.rule1a freshBranch2Key.rule1a = Ordering.eq := by
  rw [freshBranch1Key_rule1a, freshBranch2Key_rule1a]
  decide +kernel

theorem freshBranch_rule1b_compare_eq :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
      freshBranch1Key.rule1b freshBranch2Key.rule1b = Ordering.eq := by
  rw [freshBranch1Key_rule1b, freshBranch2Key_rule1b]
  decide +kernel

theorem freshBranch_rule2_compare_lt :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      freshBranch1Key.rule2 freshBranch2Key.rule2 = Ordering.lt := by
  decide +kernel

/-- Once Rules 1a and 1b tie, the comparator is exactly the Rule-2 comparison. -/
theorem compare_eq_rule2_of_rule1a_eq_of_rule1b_eq {V : Type*}
    {left right : OfficialRuleMajorKey V}
    (rule1aEq : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a = Ordering.eq)
    (rule1bEq : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
      left.rule1b right.rule1b = Ordering.eq) :
    OfficialRuleMajorKey.compare left right =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        left.rule2 right.rule2 := by
  unfold OfficialRuleMajorKey.compare
  have firstEq : (Ordering.byKey OfficialRuleMajorKey.rule1a
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
      left right = Ordering.eq := by
    simpa [Ordering.byKey] using rule1aEq
  rw [ConstitutionalLexAlgebra.compareLex_eq_second_of_first_eq _ _ left right firstEq]
  have secondEq : (Ordering.byKey OfficialRuleMajorKey.rule1b
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
      left right = Ordering.eq := by
    simpa [Ordering.byKey] using rule1bEq
  rw [ConstitutionalLexAlgebra.compareLex_eq_second_of_first_eq _ _ left right secondEq]
  rfl

/-- **The fresh-root-at-`0` comparison is `lt`.**  The branches have equal Rule-1a and Rule-1b
tables, so the `12C` versus `13C` Rule-2 mass decides in favour of the lighter arm.  This is the
opposite outcome to the same-digraph auxiliary comparison above. -/
theorem freshRoot_compare_lt :
    OfficialRuleMajorKey.compare freshBranch1Key freshBranch2Key = Ordering.lt := by
  rw [compare_eq_rule2_of_rule1a_eq_of_rule1b_eq freshBranch_rule1a_compare_eq
    freshBranch_rule1b_compare_eq]
  exact freshBranch_rule2_compare_lt

/-! ## The generated reference state and its through-Rule-5 record

The state is the actual generated reference state of the admitted input, not a chosen one.  The
whole-state reader and the dependency view it induces are the pipeline's own. -/

/-- The actual generated reference state of the admitted fixture. -/
abbrev referenceState : input.certified.LocalizedAuxiliaryState fuel :=
  LocalizedUniversalReference.referenceState input

/-- The pipeline's own whole-state comparison witness at the concrete parent/outward pair. -/
theorem referenceState_parentChild_witness :
    Nonempty (ParentOutwardComparisonWitness input.certified .rule4a
      (wholeStateLabel input.certified referenceState) targetOcc
      (input.certified.localizedDependencyView referenceState targetOcc)
      parentCursor outwardCursor) :=
  wholeState_parentSide_outwardChild_comparison_noninterference input.certified
    targetOcc targetActive parentCertificate .rule4a referenceState outwardCursor 0
    outwardCursor_mem outwardCursor_address

/-- **The reference state's through-Rule-5 comparison is strictly parent-first and non-pseudo.**

The two compound keys are produced by the shipped compound builder at its own bounded budget on
the actual reference state.  Their through-Rule-5 record is exactly `ordering := gt`,
`pseudo := false`; every Rule-4b/4c and Rule-5 reading in the keys is irrelevant. -/
theorem referenceState_compoundThroughRule5_gt :
    ∃ parentCompound childCompound : input.certified.LocalizedRerootCompoundRule45Key,
      input.certified.buildLocalizedRerootCompoundRule45Key? targetOcc
          (input.certified.localizedDependencyView referenceState targetOcc)
          (2 * (fuel + 1)) parentCursor = some parentCompound ∧
      input.certified.buildLocalizedRerootCompoundRule45Key? targetOcc
          (input.certified.localizedDependencyView referenceState targetOcc)
          (2 * (fuel + 1)) outwardCursor = some childCompound ∧
      input.certified.compareLocalizedRerootCompoundThroughRule5 parentCompound childCompound =
        { ordering := Ordering.gt, pseudo := false } := by
  obtain ⟨w⟩ := referenceState_parentChild_witness
  have compareGt := everyReader_actual_compare_gt w
  obtain ⟨parentCompound, parentComputed⟩ :=
    input.certified.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
      targetOcc (input.certified.localizedDependencyView referenceState targetOcc)
      parentCursor parentCursor_valid
  obtain ⟨childCompound, childComputed⟩ :=
    input.certified.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
      targetOcc (input.certified.localizedDependencyView referenceState targetOcc)
      outwardCursor outwardCursor_valid
  refine ⟨parentCompound, childCompound, parentComputed, childComputed, ?_⟩
  rw [input.certified.builtCompoundKeys_throughRule5_constitutional_record
    targetOcc (input.certified.localizedDependencyView referenceState targetOcc)
    w parentCompound childCompound parentComputed childComputed, compareGt]

end TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness

/-! ## Kernel-authority guards for every public declaration -/

assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.source_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.source_localizedGraphReady
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.source_noDoubleTest
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.admission
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.bond_atom0_atom1
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.bond_atom0_atom2
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.bond_atom0_atom9
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.bond_atom0_atom10
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.bond_atom1_atom0
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.bond_atom1_atom3
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.bond_atom1_atom4
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.bond_atom1_atom5
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.bond_atom2_atom0
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.bond_atom2_atom6
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.bond_atom2_atom7
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.bond_atom2_atom8
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.neighborSort_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.children_rootNode
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.children_targetNode
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.children_outwardNode
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.rootFrame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.targetFrame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardFrame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.parentCursor_valid
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardCursor_valid
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardFrame_mem_intended
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardCursor_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.periodicElement
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.carbon
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.hydrogen
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.fluorine
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.chlorine
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.bromine
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.iodine
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atom
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.labelledCarbon
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.singleBond
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.source
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.source_noDoubleRecords
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.certifiedSource
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.localizedSource
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.input
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.Atom
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.graph
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atom0
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atom1
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atom2
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atom3
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atom4
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atom5
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atom6
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atom7
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atom8
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atom9
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atom10
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.fuel
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.fuel_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atomCount_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.sort_of_toFinset_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.rootNode
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.targetNode
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardNode
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.node3
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.node4
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.node5
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.node9
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.node10
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.node6
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.node7
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.node8
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.rootFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.targetFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.rootOcc
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.targetOcc
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardOcc
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.parentCursor
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardCursor
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.targetCursor
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.carrierTreeAdjacent_root_target
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.carrierTreeAdjacent_outward_target
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.targetActive
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.parentCertificate
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardCursor_address
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.children_node3
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.children_node4
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.children_node5
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.children_node6
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.children_node7
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.children_node8
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f3
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f4
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f5
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f6
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f7
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f8
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f3_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f4_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f5_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f6_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f7_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f8_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f3Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f4Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f5Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f6Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f7Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f8Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c3
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c4
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c5
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c6
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c7
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c8
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.intended_eq_nil_of_leaf_cut
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c3_intended_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c4_intended_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c5_intended_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c6_intended_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c7_intended_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c8_intended_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.declarativeKey_eq_rootKey_of_intended_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.parentNotDuplicate
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardNotDuplicate
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.rootNodeNotDuplicate
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardNodeNotDuplicate
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.rootOccNotDuplicate
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardOccNotDuplicate
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.mem_intended_parentCursor_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.mem_intended_outwardCursor_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f3_intended
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f4_intended
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f5_intended
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f6_intended
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f7_intended
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f8_intended
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.mem_executable_of_mem_intended
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c3_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c4_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c5_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c6_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c7_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.c8_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.frameKey
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.k3
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.k4
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.k5
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.k6
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.k7
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.k8
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.parentAuxKey
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardAuxKey
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f3_ne_f4
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f3_ne_f5
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f4_ne_f5
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f6_ne_f7
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f6_ne_f8
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.f7_ne_f8
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.nodup_three
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.nodup_three_out
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.mem_three_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.mem_three_out_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.intended_parentCursor_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.intended_outwardCursor_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.perm_sort_parent
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.perm_sort_outward
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.childKeys_parent_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.childKeys_outward_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.ranking_parent
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.ranking_outward
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.executableChildren_eq_nil_of_intended_eq_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.declarativeList_of_terminal
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.parentChildren_empty
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardChildren_empty
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.parentChildren_nonempty
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardChildren_nonempty
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.declarative_parentAux
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.declarative_outwardAux
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.declarative_parentAux_any
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.declarative_outwardAux_any
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.parentAuxKey_rule1a
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardAuxKey_rule1a
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.rootNode_rule1bRootDistance
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardNode_rule1bRootDistance
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.parentCursor_node
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.outwardCursor_node
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.parentKey_constitutional_rule1a
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.childKey_constitutional_rule1a
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.parentChild_rule1a_compare_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.everyReader_parentChild_compare_gt
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.everyReader_actual_compare_gt
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshRootNode
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch1
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch2
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshLeaf3
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshLeaf4
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshLeaf5
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshLeaf6
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshLeaf7
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshLeaf8
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch1Key
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch2Key
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch1_rule1bRootDistance
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch2_rule1bRootDistance
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch1Key_rule1a
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch2Key_rule1a
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch1Key_rule1b
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch2Key_rule1b
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch1Key_rule2_head
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch2Key_rule2_head
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.atomMass_atom1_lt_atom2
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch_rule1a_compare_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch_rule1b_compare_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshBranch_rule2_compare_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.compare_eq_rule2_of_rule1a_eq_of_rule1b_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.freshRoot_compare_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.referenceState
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.referenceState_parentChild_witness
assert_kernel_only TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness.referenceState_compoundThroughRule5_gt
