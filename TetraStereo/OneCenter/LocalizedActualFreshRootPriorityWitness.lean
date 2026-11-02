import TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false









































namespace TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedAuxiliaryFreshRootPriorityWitness

/-! ## Actual fresh-root carrier frames

The fresh root is the centre carbon `atom0`.  All frames below are ordinary frames of the shared
finite occurrence carrier `input.certified.localizedOccurrences fuel`; only their root and address
coordinates are the fresh-root ones. -/

def root0Frame : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [], node := freshRootNode, remaining := fuel + 1 }

def branch1Frame : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [0], node := freshBranch1, remaining := fuel }

def branch2Frame : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [1], node := freshBranch2, remaining := fuel }

def leaf3Frame : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [0, 0], node := freshLeaf3, remaining := fuel - 1 }

def leaf4Frame : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [0, 1], node := freshLeaf4, remaining := fuel - 1 }

def leaf5Frame : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [0, 2], node := freshLeaf5, remaining := fuel - 1 }

def leaf6Frame : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [1, 0], node := freshLeaf6, remaining := fuel - 1 }

def leaf7Frame : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [1, 1], node := freshLeaf7, remaining := fuel - 1 }

def leaf8Frame : input.certified.LocalizedCIPOccurrenceFrame :=
  { root := atom0, address := [1, 2], node := freshLeaf8, remaining := fuel - 1 }

/-! ## Exact executable child lists of the fresh-root nodes -/

theorem children_freshRootNode :
    input.certified.executableOfficialCIPChildren freshRootNode =
      [freshBranch1, freshBranch2, freshRootNode.extend atom9 0,
        freshRootNode.extend atom10 0] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    freshRootNode, OfficialCIPNode.root, OfficialCIPNode.isDuplicateLeaf,
    OfficialCIPNodeProvenance.isDuplicateLeaf, OfficialCIPNode.parent?,
    neighborSort_eq, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.range_one, List.flatMap_singleton, List.filter_cons, List.filter_nil,
    Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

theorem children_freshBranch1 :
    input.certified.executableOfficialCIPChildren freshBranch1 =
      [freshLeaf3, freshLeaf4, freshLeaf5] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    freshBranch1, freshRootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

theorem children_freshBranch2 :
    input.certified.executableOfficialCIPChildren freshBranch2 =
      [freshLeaf6, freshLeaf7, freshLeaf8] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    freshBranch2, freshRootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

theorem children_freshLeaf3 :
    input.certified.executableOfficialCIPChildren freshLeaf3 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    freshLeaf3, freshBranch1, freshRootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

theorem children_freshLeaf4 :
    input.certified.executableOfficialCIPChildren freshLeaf4 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    freshLeaf4, freshBranch1, freshRootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

theorem children_freshLeaf5 :
    input.certified.executableOfficialCIPChildren freshLeaf5 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    freshLeaf5, freshBranch1, freshRootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

theorem children_freshLeaf6 :
    input.certified.executableOfficialCIPChildren freshLeaf6 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    freshLeaf6, freshBranch2, freshRootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

theorem children_freshLeaf7 :
    input.certified.executableOfficialCIPChildren freshLeaf7 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    freshLeaf7, freshBranch2, freshRootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

theorem children_freshLeaf8 :
    input.certified.executableOfficialCIPChildren freshLeaf8 = [] := by
  simp only [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,
    CertifiedLocalizedCIPInput.executableOfficialChildCopies,
    CertifiedLocalizedCIPInput.executableOfficialNeighborCopies,
    freshLeaf8, freshBranch2, freshRootNode, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.isDuplicateLeaf, OfficialCIPNodeProvenance.isDuplicateLeaf,
    OfficialCIPNode.parent?, neighborSort_eq, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.range_one, List.flatMap_singleton,
    List.filter_cons, List.filter_nil, Bool.false_eq_true, Bool.true_eq_false,
    ↓reduceIte, ↓reduceDIte, List.append_nil]
  rfl

/-! ## Actual carrier membership -/

theorem root0Frame_mem : root0Frame ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (fuel + 1) freshRootNode
    root0Frame
  simpa [root0Frame] using
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
      (input := input.certified) (root := atom0) (path := []) (fuel := fuel + 1)
      (node := freshRootNode))

theorem branch1Frame_mem : branch1Frame ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (fuel + 1) freshRootNode
    branch1Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := freshRootNode)
    (child := freshBranch1) (slot := 0) (occurrence := branch1Frame) ?_ ?_
  · rw [children_freshRootNode]
    simp
  · simpa [branch1Frame] using
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
        (input := input.certified) (root := atom0) (path := [0]) (fuel := fuel)
        (node := freshBranch1))

theorem branch2Frame_mem : branch2Frame ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (fuel + 1) freshRootNode
    branch2Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := freshRootNode)
    (child := freshBranch2) (slot := 1) (occurrence := branch2Frame) ?_ ?_
  · rw [children_freshRootNode]
    simp
  · simpa [branch2Frame] using
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
        (input := input.certified) (root := atom0) (path := [1]) (fuel := fuel)
        (node := freshBranch2))

theorem leaf3Frame_mem : leaf3Frame ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (fuel + 1) freshRootNode
    leaf3Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := freshRootNode)
    (child := freshBranch1) (slot := 0) (occurrence := leaf3Frame) ?_ ?_
  · rw [children_freshRootNode]
    simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [0]) (fuel := fuel - 1) (node := freshBranch1)
      (child := freshLeaf3) (slot := 0) (occurrence := leaf3Frame) ?_ ?_
    · rw [children_freshBranch1]
      simp
    · simpa [leaf3Frame] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := input.certified) (root := atom0) (path := [0, 0]) (fuel := fuel - 1)
          (node := freshLeaf3))

theorem leaf4Frame_mem : leaf4Frame ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (fuel + 1) freshRootNode
    leaf4Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := freshRootNode)
    (child := freshBranch1) (slot := 0) (occurrence := leaf4Frame) ?_ ?_
  · rw [children_freshRootNode]
    simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [0]) (fuel := fuel - 1) (node := freshBranch1)
      (child := freshLeaf4) (slot := 1) (occurrence := leaf4Frame) ?_ ?_
    · rw [children_freshBranch1]
      simp
    · simpa [leaf4Frame] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := input.certified) (root := atom0) (path := [0, 1]) (fuel := fuel - 1)
          (node := freshLeaf4))

theorem leaf5Frame_mem : leaf5Frame ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (fuel + 1) freshRootNode
    leaf5Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := freshRootNode)
    (child := freshBranch1) (slot := 0) (occurrence := leaf5Frame) ?_ ?_
  · rw [children_freshRootNode]
    simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [0]) (fuel := fuel - 1) (node := freshBranch1)
      (child := freshLeaf5) (slot := 2) (occurrence := leaf5Frame) ?_ ?_
    · rw [children_freshBranch1]
      simp
    · simpa [leaf5Frame] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := input.certified) (root := atom0) (path := [0, 2]) (fuel := fuel - 1)
          (node := freshLeaf5))

theorem leaf6Frame_mem : leaf6Frame ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (fuel + 1) freshRootNode
    leaf6Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := freshRootNode)
    (child := freshBranch2) (slot := 1) (occurrence := leaf6Frame) ?_ ?_
  · rw [children_freshRootNode]
    simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [1]) (fuel := fuel - 1) (node := freshBranch2)
      (child := freshLeaf6) (slot := 0) (occurrence := leaf6Frame) ?_ ?_
    · rw [children_freshBranch2]
      simp
    · simpa [leaf6Frame] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := input.certified) (root := atom0) (path := [1, 0]) (fuel := fuel - 1)
          (node := freshLeaf6))

theorem leaf7Frame_mem : leaf7Frame ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (fuel + 1) freshRootNode
    leaf7Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := freshRootNode)
    (child := freshBranch2) (slot := 1) (occurrence := leaf7Frame) ?_ ?_
  · rw [children_freshRootNode]
    simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [1]) (fuel := fuel - 1) (node := freshBranch2)
      (child := freshLeaf7) (slot := 1) (occurrence := leaf7Frame) ?_ ?_
    · rw [children_freshBranch2]
      simp
    · simpa [leaf7Frame] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := input.certified) (root := atom0) (path := [1, 1]) (fuel := fuel - 1)
          (node := freshLeaf7))

theorem leaf8Frame_mem : leaf8Frame ∈ input.certified.localizedOccurrences fuel := by
  rw [input.certified.mem_localizedOccurrences_iff]
  change input.certified.DeclarativeLocalizedOccurrenceSubtree atom0 [] (fuel + 1) freshRootNode
    leaf8Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := freshRootNode)
    (child := freshBranch2) (slot := 1) (occurrence := leaf8Frame) ?_ ?_
  · rw [children_freshRootNode]
    simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (path := [1]) (fuel := fuel - 1) (node := freshBranch2)
      (child := freshLeaf8) (slot := 2) (occurrence := leaf8Frame) ?_ ?_
    · rw [children_freshBranch2]
      simp
    · simpa [leaf8Frame] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := input.certified) (root := atom0) (path := [1, 2]) (fuel := fuel - 1)
          (node := freshLeaf8))

/-! ## Actual occurrences and reroot cursors -/

def root0Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨root0Frame, root0Frame_mem⟩
def branch1Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨branch1Frame, branch1Frame_mem⟩
def branch2Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨branch2Frame, branch2Frame_mem⟩
def leaf3Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨leaf3Frame, leaf3Frame_mem⟩
def leaf4Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨leaf4Frame, leaf4Frame_mem⟩
def leaf5Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨leaf5Frame, leaf5Frame_mem⟩
def leaf6Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨leaf6Frame, leaf6Frame_mem⟩
def leaf7Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨leaf7Frame, leaf7Frame_mem⟩
def leaf8Occ : input.certified.LocalizedCIPOccurrence fuel := ⟨leaf8Frame, leaf8Frame_mem⟩

def root0Cursor : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := root0Occ, previous? := none }

def branch1Cursor : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := branch1Occ, previous? := some root0Occ }

def branch2Cursor : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := branch2Occ, previous? := some root0Occ }

def leaf3Cursor : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := leaf3Occ, previous? := some branch1Occ }

def leaf4Cursor : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := leaf4Occ, previous? := some branch1Occ }

def leaf5Cursor : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := leaf5Occ, previous? := some branch1Occ }

def leaf6Cursor : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := leaf6Occ, previous? := some branch2Occ }

def leaf7Cursor : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := leaf7Occ, previous? := some branch2Occ }

def leaf8Cursor : input.certified.LocalizedRerootCursor fuel :=
  { occurrence := leaf8Occ, previous? := some branch2Occ }

theorem carrierTreeAdjacent_branch1_root0 :
    input.certified.LocalizedCarrierTreeAdjacent branch1Frame root0Frame := by
  refine ⟨rfl, Or.inr ⟨?_, rfl⟩⟩
  decide +kernel

theorem carrierTreeAdjacent_branch2_root0 :
    input.certified.LocalizedCarrierTreeAdjacent branch2Frame root0Frame := by
  refine ⟨rfl, Or.inr ⟨?_, rfl⟩⟩
  decide +kernel

theorem root0Cursor_valid : input.certified.LocalizedRerootCursorValid root0Cursor := by
  unfold LocalizedRerootCursorValid
  simp [root0Cursor]

theorem branch1Cursor_valid : input.certified.LocalizedRerootCursorValid branch1Cursor := by
  unfold LocalizedRerootCursorValid
  simp only [branch1Cursor]
  exact (input.certified.mem_localizedRerootNeighborFrames_iff root0Frame branch1Frame).mpr
    ⟨branch1Frame_mem, carrierTreeAdjacent_branch1_root0⟩

theorem branch2Cursor_valid : input.certified.LocalizedRerootCursorValid branch2Cursor := by
  unfold LocalizedRerootCursorValid
  simp only [branch2Cursor]
  exact (input.certified.mem_localizedRerootNeighborFrames_iff root0Frame branch2Frame).mpr
    ⟨branch2Frame_mem, carrierTreeAdjacent_branch2_root0⟩

/-! ## The branch cursors are actual executable children of the fresh root cursor -/

theorem branch1Frame_mem_intended :
    branch1Frame ∈ input.certified.intendedLocalizedRerootChildFrames root0Cursor := by
  unfold intendedLocalizedRerootChildFrames
  have notDuplicate : root0Cursor.occurrence.1.node.isDuplicateLeaf = false := by
    decide +kernel
  rw [notDuplicate]
  simp only [Bool.false_eq_true, ↓reduceIte, root0Cursor]
  rw [localizedRerootNeighborFrames, List.mem_append]
  right
  rw [localizedCarrierOutwardChildFrames, List.mem_filter]
  exact ⟨branch1Frame_mem, by simp [branch1Frame, root0Occ, root0Frame]⟩

theorem branch2Frame_mem_intended :
    branch2Frame ∈ input.certified.intendedLocalizedRerootChildFrames root0Cursor := by
  unfold intendedLocalizedRerootChildFrames
  have notDuplicate : root0Cursor.occurrence.1.node.isDuplicateLeaf = false := by
    decide +kernel
  rw [notDuplicate]
  simp only [Bool.false_eq_true, ↓reduceIte, root0Cursor]
  rw [localizedRerootNeighborFrames, List.mem_append]
  right
  rw [localizedCarrierOutwardChildFrames, List.mem_filter]
  exact ⟨branch2Frame_mem, by simp [branch2Frame, root0Occ, root0Frame]⟩

theorem branch1Cursor_mem :
    branch1Cursor ∈ input.certified.executableLocalizedRerootChildren root0Cursor := by
  have h := mem_executable_of_mem_intended root0Cursor branch1Frame branch1Frame_mem_intended
  unfold executableLocalizedRerootChildren at h ⊢
  rw [List.mem_map] at h ⊢
  rcases h with ⟨frame, frameMem, equality⟩
  exact ⟨frame, frameMem, by
    rw [equality]
    apply LocalizedRerootCursor.ext input.certified
    · apply Subtype.ext rfl
    · rfl⟩

theorem branch2Cursor_mem :
    branch2Cursor ∈ input.certified.executableLocalizedRerootChildren root0Cursor := by
  have h := mem_executable_of_mem_intended root0Cursor branch2Frame branch2Frame_mem_intended
  unfold executableLocalizedRerootChildren at h ⊢
  rw [List.mem_map] at h ⊢
  rcases h with ⟨frame, frameMem, equality⟩
  exact ⟨frame, frameMem, by
    rw [equality]
    apply LocalizedRerootCursor.ext input.certified
    · apply Subtype.ext rfl
    · rfl⟩

/-! ## Exact intended child sets of the two branch cursors -/

theorem branch1NotDuplicate : branch1Frame.node.isDuplicateLeaf = false := by
  decide +kernel

theorem branch2NotDuplicate : branch2Frame.node.isDuplicateLeaf = false := by
  decide +kernel

theorem branch1OccNotDuplicate : branch1Occ.1.node.isDuplicateLeaf = false := by
  decide +kernel

theorem branch2OccNotDuplicate : branch2Occ.1.node.isDuplicateLeaf = false := by
  decide +kernel

theorem mem_intended_branch1Cursor_iff
    (g : input.certified.LocalizedCIPOccurrenceFrame) :
    g ∈ input.certified.intendedLocalizedRerootChildFrames branch1Cursor ↔
      g = leaf3Frame ∨ g = leaf4Frame ∨ g = leaf5Frame := by
  constructor
  · intro present
    simp only [intendedLocalizedRerootChildFrames, branch1NotDuplicate,
      branch1OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branch1Cursor,
      List.mem_filter] at present
    rcases present with ⟨neighbor, addressNe⟩
    rw [localizedRerootNeighborFrames, List.mem_append] at neighbor
    rcases neighbor with parentMem | childMem
    · rw [localizedCarrierParentFrames, List.mem_filter] at parentMem
      rcases parentMem with ⟨_gCarrier, cond⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at cond
      have hLen : branch1Occ.1.address.length = 1 := rfl
      have gLength : g.address.length = 0 := by
        have h := cond.1.2
        omega
      have gNil : g.address = [] := List.eq_nil_of_length_eq_zero gLength
      have addressNe' : g.address ≠ root0Occ.1.address := by
        intro equal
        rw [equal] at addressNe
        simp at addressNe
      rw [gNil] at addressNe'
      simp [root0Occ, root0Frame] at addressNe'
    · rw [localizedCarrierOutwardChildFrames, List.mem_filter] at childMem
      rcases childMem with ⟨gCarrier, cond⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at cond
      have gRoot : g.root = branch1Frame.root := by
        simpa [branch1Occ, branch1Frame] using cond.1.1
      have gLength : g.address.length = 2 := by
        simpa [branch1Occ, branch1Frame] using cond.1.2
      have gDrop : g.address.dropLast = [0] := by
        simpa [branch1Occ, branch1Frame] using cond.2
      have gNonempty : g.address ≠ [] := by
        intro empty
        rw [empty] at gLength
        simp at gLength
      let slot := g.address.getLast gNonempty
      have addressEq : g.address = branch1Frame.address ++ [slot] := by
        have := List.dropLast_append_getLast gNonempty
        rw [gDrop] at this
        simpa [branch1Frame] using this.symm
      have gDerived :=
        (input.certified.mem_localizedOccurrences_iff fuel g).mp gCarrier
      have sourceDerived :=
        (input.certified.mem_localizedOccurrences_iff fuel branch1Frame).mp
          branch1Frame_mem
      obtain ⟨child, childAtSlot, gEq⟩ :=
        input.certified.declarativeLocalizedOccurrence_immediate_child
          sourceDerived gDerived gRoot slot addressEq
      rw [show branch1Frame.node = freshBranch1 from rfl] at childAtSlot
      rw [children_freshBranch1] at childAtSlot
      have childCases : (child, slot) = (freshLeaf3, 0) ∨
          (child, slot) = (freshLeaf4, 1) ∨ (child, slot) = (freshLeaf5, 2) := by
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
    · simp only [intendedLocalizedRerootChildFrames, branch1NotDuplicate,
        branch1OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branch1Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨leaf3Frame_mem, by simp [leaf3Frame, branch1Occ, branch1Frame]⟩
      · simp [leaf3Frame, root0Occ, root0Frame]
    · simp only [intendedLocalizedRerootChildFrames, branch1NotDuplicate,
        branch1OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branch1Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨leaf4Frame_mem, by simp [leaf4Frame, branch1Occ, branch1Frame]⟩
      · simp [leaf4Frame, root0Occ, root0Frame]
    · simp only [intendedLocalizedRerootChildFrames, branch1NotDuplicate,
        branch1OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branch1Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨leaf5Frame_mem, by simp [leaf5Frame, branch1Occ, branch1Frame]⟩
      · simp [leaf5Frame, root0Occ, root0Frame]

theorem mem_intended_branch2Cursor_iff
    (g : input.certified.LocalizedCIPOccurrenceFrame) :
    g ∈ input.certified.intendedLocalizedRerootChildFrames branch2Cursor ↔
      g = leaf6Frame ∨ g = leaf7Frame ∨ g = leaf8Frame := by
  constructor
  · intro present
    simp only [intendedLocalizedRerootChildFrames, branch2NotDuplicate,
      branch2OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branch2Cursor,
      List.mem_filter] at present
    rcases present with ⟨neighbor, addressNe⟩
    rw [localizedRerootNeighborFrames, List.mem_append] at neighbor
    rcases neighbor with parentMem | childMem
    · rw [localizedCarrierParentFrames, List.mem_filter] at parentMem
      rcases parentMem with ⟨_gCarrier, cond⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at cond
      have hLen : branch2Occ.1.address.length = 1 := rfl
      have gLength : g.address.length = 0 := by
        have h := cond.1.2
        omega
      have gNil : g.address = [] := List.eq_nil_of_length_eq_zero gLength
      have addressNe' : g.address ≠ root0Occ.1.address := by
        intro equal
        rw [equal] at addressNe
        simp at addressNe
      rw [gNil] at addressNe'
      simp [root0Occ, root0Frame] at addressNe'
    · rw [localizedCarrierOutwardChildFrames, List.mem_filter] at childMem
      rcases childMem with ⟨gCarrier, cond⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at cond
      have gRoot : g.root = branch2Frame.root := by
        simpa [branch2Occ, branch2Frame] using cond.1.1
      have gLength : g.address.length = 2 := by
        simpa [branch2Occ, branch2Frame] using cond.1.2
      have gDrop : g.address.dropLast = [1] := by
        simpa [branch2Occ, branch2Frame] using cond.2
      have gNonempty : g.address ≠ [] := by
        intro empty
        rw [empty] at gLength
        simp at gLength
      let slot := g.address.getLast gNonempty
      have addressEq : g.address = branch2Frame.address ++ [slot] := by
        have := List.dropLast_append_getLast gNonempty
        rw [gDrop] at this
        simpa [branch2Frame] using this.symm
      have gDerived :=
        (input.certified.mem_localizedOccurrences_iff fuel g).mp gCarrier
      have sourceDerived :=
        (input.certified.mem_localizedOccurrences_iff fuel branch2Frame).mp
          branch2Frame_mem
      obtain ⟨child, childAtSlot, gEq⟩ :=
        input.certified.declarativeLocalizedOccurrence_immediate_child
          sourceDerived gDerived gRoot slot addressEq
      rw [show branch2Frame.node = freshBranch2 from rfl] at childAtSlot
      rw [children_freshBranch2] at childAtSlot
      have childCases : (child, slot) = (freshLeaf6, 0) ∨
          (child, slot) = (freshLeaf7, 1) ∨ (child, slot) = (freshLeaf8, 2) := by
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
    · simp only [intendedLocalizedRerootChildFrames, branch2NotDuplicate,
        branch2OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branch2Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨leaf6Frame_mem, by simp [leaf6Frame, branch2Occ, branch2Frame]⟩
      · simp [leaf6Frame, root0Occ, root0Frame]
    · simp only [intendedLocalizedRerootChildFrames, branch2NotDuplicate,
        branch2OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branch2Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨leaf7Frame_mem, by simp [leaf7Frame, branch2Occ, branch2Frame]⟩
      · simp [leaf7Frame, root0Occ, root0Frame]
    · simp only [intendedLocalizedRerootChildFrames, branch2NotDuplicate,
        branch2OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branch2Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨leaf8Frame_mem, by simp [leaf8Frame, branch2Occ, branch2Frame]⟩
      · simp [leaf8Frame, root0Occ, root0Frame]

/-! ## The leaf cursors are terminal -/

theorem leaf3_intended_nil :
    input.certified.intendedLocalizedRerootChildFrames leaf3Cursor = [] :=
  intended_eq_nil_of_leaf_cut leaf3Cursor branch1Occ rfl (by decide +kernel) children_freshLeaf3

theorem leaf4_intended_nil :
    input.certified.intendedLocalizedRerootChildFrames leaf4Cursor = [] :=
  intended_eq_nil_of_leaf_cut leaf4Cursor branch1Occ rfl (by decide +kernel) children_freshLeaf4

theorem leaf5_intended_nil :
    input.certified.intendedLocalizedRerootChildFrames leaf5Cursor = [] :=
  intended_eq_nil_of_leaf_cut leaf5Cursor branch1Occ rfl (by decide +kernel) children_freshLeaf5

theorem leaf6_intended_nil :
    input.certified.intendedLocalizedRerootChildFrames leaf6Cursor = [] :=
  intended_eq_nil_of_leaf_cut leaf6Cursor branch2Occ rfl (by decide +kernel) children_freshLeaf6

theorem leaf7_intended_nil :
    input.certified.intendedLocalizedRerootChildFrames leaf7Cursor = [] :=
  intended_eq_nil_of_leaf_cut leaf7Cursor branch2Occ rfl (by decide +kernel) children_freshLeaf7

theorem leaf8_intended_nil :
    input.certified.intendedLocalizedRerootChildFrames leaf8Cursor = [] :=
  intended_eq_nil_of_leaf_cut leaf8Cursor branch2Occ rfl (by decide +kernel) children_freshLeaf8

/-! ## Exact keys and declarative branch derivations -/

def kF3 : OfficialRuleMajorKey Atom := frameKey leaf3Frame
def kF4 : OfficialRuleMajorKey Atom := frameKey leaf4Frame
def kF5 : OfficialRuleMajorKey Atom := frameKey leaf5Frame
def kF6 : OfficialRuleMajorKey Atom := frameKey leaf6Frame
def kF7 : OfficialRuleMajorKey Atom := frameKey leaf7Frame
def kF8 : OfficialRuleMajorKey Atom := frameKey leaf8Frame

theorem leaf3_ne_leaf4 : leaf3Frame ≠ leaf4Frame := by
  intro h
  have := congrArg (fun frame => frame.address) h
  simp [leaf3Frame, leaf4Frame] at this

theorem leaf3_ne_leaf5 : leaf3Frame ≠ leaf5Frame := by
  intro h
  have := congrArg (fun frame => frame.address) h
  simp [leaf3Frame, leaf5Frame] at this

theorem leaf4_ne_leaf5 : leaf4Frame ≠ leaf5Frame := by
  intro h
  have := congrArg (fun frame => frame.address) h
  simp [leaf4Frame, leaf5Frame] at this

theorem leaf6_ne_leaf7 : leaf6Frame ≠ leaf7Frame := by
  intro h
  have := congrArg (fun frame => frame.address) h
  simp [leaf6Frame, leaf7Frame] at this

theorem leaf6_ne_leaf8 : leaf6Frame ≠ leaf8Frame := by
  intro h
  have := congrArg (fun frame => frame.address) h
  simp [leaf6Frame, leaf8Frame] at this

theorem leaf7_ne_leaf8 : leaf7Frame ≠ leaf8Frame := by
  intro h
  have := congrArg (fun frame => frame.address) h
  simp [leaf7Frame, leaf8Frame] at this

theorem nodup_leaves1 : [leaf3Frame, leaf4Frame, leaf5Frame].Nodup := by
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · rw [List.mem_cons]
    rintro (h | h)
    · exact leaf3_ne_leaf4 h
    · rw [List.mem_singleton] at h
      exact leaf3_ne_leaf5 h
  · rw [List.nodup_cons]
    exact ⟨by simpa using leaf4_ne_leaf5, by simp⟩

theorem nodup_leaves2 : [leaf6Frame, leaf7Frame, leaf8Frame].Nodup := by
  rw [List.nodup_cons]
  refine ⟨?_, ?_⟩
  · rw [List.mem_cons]
    rintro (h | h)
    · exact leaf6_ne_leaf7 h
    · rw [List.mem_singleton] at h
      exact leaf6_ne_leaf8 h
  · rw [List.nodup_cons]
    exact ⟨by simpa using leaf7_ne_leaf8, by simp⟩

theorem mem_leaves1_iff (g : input.certified.LocalizedCIPOccurrenceFrame) :
    g ∈ [leaf3Frame, leaf4Frame, leaf5Frame] ↔
      g = leaf3Frame ∨ g = leaf4Frame ∨ g = leaf5Frame := by
  simp

theorem mem_leaves2_iff (g : input.certified.LocalizedCIPOccurrenceFrame) :
    g ∈ [leaf6Frame, leaf7Frame, leaf8Frame] ↔
      g = leaf6Frame ∨ g = leaf7Frame ∨ g = leaf8Frame := by
  simp

theorem intended_branch1_perm :
    (input.certified.intendedLocalizedRerootChildFrames branch1Cursor).Perm
      [leaf3Frame, leaf4Frame, leaf5Frame] :=
  (List.perm_ext_iff_of_nodup
    (input.certified.intendedLocalizedRerootChildFrames_nodup branch1Cursor)
    nodup_leaves1).mpr
    (fun g => by rw [mem_intended_branch1Cursor_iff g, mem_leaves1_iff g])

theorem intended_branch2_perm :
    (input.certified.intendedLocalizedRerootChildFrames branch2Cursor).Perm
      [leaf6Frame, leaf7Frame, leaf8Frame] :=
  (List.perm_ext_iff_of_nodup
    (input.certified.intendedLocalizedRerootChildFrames_nodup branch2Cursor)
    nodup_leaves2).mpr
    (fun g => by rw [mem_intended_branch2Cursor_iff g, mem_leaves2_iff g])

theorem perm_sort_branch1 : [kF5, kF4, kF3].Perm [kF3, kF4, kF5] := by
  have h45 : [kF5, kF4].Perm [kF4, kF5] := List.perm_append_comm (l₁ := [kF5]) (l₂ := [kF4])
  exact (List.perm_append_comm (l₁ := [kF5, kF4]) (l₂ := [kF3])).trans (h45.cons kF3)

theorem perm_sort_branch2 : [kF8, kF7, kF6].Perm [kF6, kF7, kF8] := by
  have h67 : [kF8, kF7].Perm [kF7, kF8] := List.perm_append_comm (l₁ := [kF8]) (l₂ := [kF7])
  exact (List.perm_append_comm (l₁ := [kF8, kF7]) (l₂ := [kF6])).trans (h67.cons kF6)

theorem childKeys_branch1_eq :
    (input.certified.executableLocalizedRerootChildren branch1Cursor).map
        (fun c => frameKey c.occurrence.1) =
      (input.certified.intendedLocalizedRerootChildFrames branch1Cursor).map frameKey := by
  change List.map (frameKey ∘ fun c => c.occurrence.1)
      (input.certified.executableLocalizedRerootChildren branch1Cursor) =
    List.map frameKey (input.certified.intendedLocalizedRerootChildFrames branch1Cursor)
  rw [← List.map_map]
  rw [input.certified.executableLocalizedRerootChildren_map branch1Cursor]

theorem childKeys_branch2_eq :
    (input.certified.executableLocalizedRerootChildren branch2Cursor).map
        (fun c => frameKey c.occurrence.1) =
      (input.certified.intendedLocalizedRerootChildFrames branch2Cursor).map frameKey := by
  change List.map (frameKey ∘ fun c => c.occurrence.1)
      (input.certified.executableLocalizedRerootChildren branch2Cursor) =
    List.map frameKey (input.certified.intendedLocalizedRerootChildFrames branch2Cursor)
  rw [← List.map_map]
  rw [input.certified.executableLocalizedRerootChildren_map branch2Cursor]

theorem ranking_freshBranch1 :
    [kF5, kF4, kF3].Perm
      ((input.certified.executableLocalizedRerootChildren branch1Cursor).map
        (fun c => frameKey c.occurrence.1)) := by
  rw [childKeys_branch1_eq]
  have hmap := intended_branch1_perm.map frameKey
  have hthree : List.map frameKey [leaf3Frame, leaf4Frame, leaf5Frame] = [kF3, kF4, kF5] := rfl
  rw [hthree] at hmap
  exact perm_sort_branch1.trans hmap.symm

theorem ranking_freshBranch2 :
    [kF8, kF7, kF6].Perm
      ((input.certified.executableLocalizedRerootChildren branch2Cursor).map
        (fun c => frameKey c.occurrence.1)) := by
  rw [childKeys_branch2_eq]
  have hmap := intended_branch2_perm.map frameKey
  have hthree : List.map frameKey [leaf6Frame, leaf7Frame, leaf8Frame] = [kF6, kF7, kF8] := rfl
  rw [hthree] at hmap
  exact perm_sort_branch2.trans hmap.symm

theorem branch1Children_empty :
    ∀ c ∈ input.certified.executableLocalizedRerootChildren branch1Cursor,
      input.certified.intendedLocalizedRerootChildFrames c = [] := by
  intro c hc
  have frameMem : c.occurrence.1 ∈
      input.certified.intendedLocalizedRerootChildFrames branch1Cursor := by
    rw [← input.certified.executableLocalizedRerootChildren_map branch1Cursor]
    exact List.mem_map_of_mem (f := fun child => child.occurrence.1) hc
  rcases (mem_intended_branch1Cursor_iff c.occurrence.1).mp frameMem with h3 | h4 | h5
  · have cursorEq : c = leaf3Cursor := by
      apply LocalizedRerootCursor.ext input.certified
      · apply Subtype.ext h3
      · rw [input.certified.executableLocalizedRerootChildren_previous branch1Cursor c hc]
        simp [branch1Cursor, leaf3Cursor]
    rw [cursorEq]
    exact leaf3_intended_nil
  · have cursorEq : c = leaf4Cursor := by
      apply LocalizedRerootCursor.ext input.certified
      · apply Subtype.ext h4
      · rw [input.certified.executableLocalizedRerootChildren_previous branch1Cursor c hc]
        simp [branch1Cursor, leaf4Cursor]
    rw [cursorEq]
    exact leaf4_intended_nil
  · have cursorEq : c = leaf5Cursor := by
      apply LocalizedRerootCursor.ext input.certified
      · apply Subtype.ext h5
      · rw [input.certified.executableLocalizedRerootChildren_previous branch1Cursor c hc]
        simp [branch1Cursor, leaf5Cursor]
    rw [cursorEq]
    exact leaf5_intended_nil

theorem branch2Children_empty :
    ∀ c ∈ input.certified.executableLocalizedRerootChildren branch2Cursor,
      input.certified.intendedLocalizedRerootChildFrames c = [] := by
  intro c hc
  have frameMem : c.occurrence.1 ∈
      input.certified.intendedLocalizedRerootChildFrames branch2Cursor := by
    rw [← input.certified.executableLocalizedRerootChildren_map branch2Cursor]
    exact List.mem_map_of_mem (f := fun child => child.occurrence.1) hc
  rcases (mem_intended_branch2Cursor_iff c.occurrence.1).mp frameMem with h6 | h7 | h8
  · have cursorEq : c = leaf6Cursor := by
      apply LocalizedRerootCursor.ext input.certified
      · apply Subtype.ext h6
      · rw [input.certified.executableLocalizedRerootChildren_previous branch2Cursor c hc]
        simp [branch2Cursor, leaf6Cursor]
    rw [cursorEq]
    exact leaf6_intended_nil
  · have cursorEq : c = leaf7Cursor := by
      apply LocalizedRerootCursor.ext input.certified
      · apply Subtype.ext h7
      · rw [input.certified.executableLocalizedRerootChildren_previous branch2Cursor c hc]
        simp [branch2Cursor, leaf7Cursor]
    rw [cursorEq]
    exact leaf7_intended_nil
  · have cursorEq : c = leaf8Cursor := by
      apply LocalizedRerootCursor.ext input.certified
      · apply Subtype.ext h8
      · rw [input.certified.executableLocalizedRerootChildren_previous branch2Cursor c hc]
        simp [branch2Cursor, leaf8Cursor]
    rw [cursorEq]
    exact leaf8_intended_nil

theorem branch1Children_nonempty :
    input.certified.executableLocalizedRerootChildren branch1Cursor ≠ [] := by
  intro h
  have intendedNil :
      input.certified.intendedLocalizedRerootChildFrames branch1Cursor = [] := by
    rw [← input.certified.executableLocalizedRerootChildren_map branch1Cursor, h]
    rfl
  have mem : leaf3Frame ∈ input.certified.intendedLocalizedRerootChildFrames branch1Cursor :=
    (mem_intended_branch1Cursor_iff leaf3Frame).mpr (Or.inl rfl)
  rw [intendedNil] at mem
  simp at mem

theorem branch2Children_nonempty :
    input.certified.executableLocalizedRerootChildren branch2Cursor ≠ [] := by
  intro h
  have intendedNil :
      input.certified.intendedLocalizedRerootChildFrames branch2Cursor = [] := by
    rw [← input.certified.executableLocalizedRerootChildren_map branch2Cursor, h]
    rfl
  have mem : leaf6Frame ∈ input.certified.intendedLocalizedRerootChildFrames branch2Cursor :=
    (mem_intended_branch2Cursor_iff leaf6Frame).mpr (Or.inl rfl)
  rw [intendedNil] at mem
  simp at mem

theorem declarative_freshBranch1 (dFuel : Nat) :
    input.certified.DeclarativeLocalizedRerootRuleMajorKey (dFuel + 1) branch1Cursor
      freshBranch1Key := by
  exact DeclarativeLocalizedRerootRuleMajorKey.branch
    (input.certified.executableLocalizedRerootChildren_declarative branch1Cursor)
    branch1Children_nonempty
    (declarativeList_of_terminal dFuel
      (input.certified.executableLocalizedRerootChildren branch1Cursor)
      branch1Children_empty)
    ranking_freshBranch1
    (by
      unfold OfficialRuleMajorKey.Descending
      decide +kernel)

theorem declarative_freshBranch2 (dFuel : Nat) :
    input.certified.DeclarativeLocalizedRerootRuleMajorKey (dFuel + 1) branch2Cursor
      freshBranch2Key := by
  exact DeclarativeLocalizedRerootRuleMajorKey.branch
    (input.certified.executableLocalizedRerootChildren_declarative branch2Cursor)
    branch2Children_nonempty
    (declarativeList_of_terminal dFuel
      (input.certified.executableLocalizedRerootChildren branch2Cursor)
      branch2Children_empty)
    ranking_freshBranch2
    (by
      unfold OfficialRuleMajorKey.Descending
      decide +kernel)

/-! ## The actual reference state at the fresh root -/

/-- The pipeline's own dependency view at the actual fresh-root occurrence `0`. -/
def root0View : input.certified.LocalizedDependencyView root0Occ :=
  input.certified.localizedDependencyView referenceState root0Occ

/-- A non-`eq` constitutional comparison is decisive for the cumulative comparator. -/
theorem cumulative_compare_eq_constitutional
    (left right : input.certified.LocalizedRerootCumulativeRule45Key)
    (decisive : OfficialRuleMajorKey.compare left.constitutional right.constitutional ≠
      Ordering.eq) :
    input.certified.compareLocalizedRerootCumulativeRule45Keys left right =
      OfficialRuleMajorKey.compare left.constitutional right.constitutional := by
  unfold CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys
  exact localizedCompareLex_eq_left_of_ne decisive



theorem freshBranch1_constitutional_observable
    (fresh1Compound : input.certified.LocalizedRerootCompoundRule45Key)
    (computed : input.certified.buildLocalizedRerootCompoundRule45Key?
      root0Occ root0View (2 * (fuel + 1)) branch1Cursor = some fresh1Compound) :
    constitutionalObservable fresh1Compound.prior.rule4aKey.constitutional =
      constitutionalObservable freshBranch1Key := by
  obtain ⟨rule4aKey, built, priorEq⟩ :=
    input.certified.buildLocalizedRerootCompoundRule45Key?_rule4a_built
      root0Occ root0View (2 * (fuel + 1)) branch1Cursor fresh1Compound computed
  have sound := input.certified.buildLocalizedRerootCumulativeRule45Key?_sound
    .rule4a root0Occ root0View (2 * (fuel + 1)) branch1Cursor rule4aKey built
  have derived :=
    input.certified.DeclarativeLocalizedRerootCumulativeRule45Key_constitutional_derived
      .rule4a root0Occ root0View (2 * (fuel + 1)) branch1Cursor rule4aKey sound
  have unique := declarative_constitutional_observable_unique input.certified
    (leftFuel := 2 * (fuel + 1)) (rightFuel := 0 + 1) (cursor := branch1Cursor)
    rule4aKey.constitutional freshBranch1Key derived (declarative_freshBranch1 0)
  rw [priorEq]
  exact unique



theorem freshBranch2_constitutional_observable
    (fresh2Compound : input.certified.LocalizedRerootCompoundRule45Key)
    (computed : input.certified.buildLocalizedRerootCompoundRule45Key?
      root0Occ root0View (2 * (fuel + 1)) branch2Cursor = some fresh2Compound) :
    constitutionalObservable fresh2Compound.prior.rule4aKey.constitutional =
      constitutionalObservable freshBranch2Key := by
  obtain ⟨rule4aKey, built, priorEq⟩ :=
    input.certified.buildLocalizedRerootCompoundRule45Key?_rule4a_built
      root0Occ root0View (2 * (fuel + 1)) branch2Cursor fresh2Compound computed
  have sound := input.certified.buildLocalizedRerootCumulativeRule45Key?_sound
    .rule4a root0Occ root0View (2 * (fuel + 1)) branch2Cursor rule4aKey built
  have derived :=
    input.certified.DeclarativeLocalizedRerootCumulativeRule45Key_constitutional_derived
      .rule4a root0Occ root0View (2 * (fuel + 1)) branch2Cursor rule4aKey sound
  have unique := declarative_constitutional_observable_unique input.certified
    (leftFuel := 2 * (fuel + 1)) (rightFuel := 0 + 1) (cursor := branch2Cursor)
    rule4aKey.constitutional freshBranch2Key derived (declarative_freshBranch2 0)
  rw [priorEq]
  exact unique

/-- **The actual fresh-root through-Rule-5 record is `lt` and non-pseudo.**  For any keys the
shipped compound builder actually produces at the two branch cursors from the generated reference
state, the Rule-4a cumulative components compare `lt`: Rules 1a and 1b tie, and the actual Rule-2
mass of `13C` at atom `2` beats that of `12C` at atom `1`. -/
theorem freshRoot_actual_compare_lt
    (fresh1Compound fresh2Compound : input.certified.LocalizedRerootCompoundRule45Key)
    (firstComputed : input.certified.buildLocalizedRerootCompoundRule45Key?
      root0Occ root0View (2 * (fuel + 1)) branch1Cursor = some fresh1Compound)
    (secondComputed : input.certified.buildLocalizedRerootCompoundRule45Key?
      root0Occ root0View (2 * (fuel + 1)) branch2Cursor = some fresh2Compound) :
    input.certified.compareLocalizedRerootCompoundThroughRule5
        fresh1Compound fresh2Compound =
      { ordering := Ordering.lt, pseudo := false } := by
  have observable1 := freshBranch1_constitutional_observable fresh1Compound firstComputed
  have observable2 := freshBranch2_constitutional_observable fresh2Compound secondComputed
  have compareEq : OfficialRuleMajorKey.compare
      fresh1Compound.prior.rule4aKey.constitutional
      fresh2Compound.prior.rule4aKey.constitutional =
      OfficialRuleMajorKey.compare freshBranch1Key freshBranch2Key :=
    ruleMajor_compare_congr _ _ _ _ observable1 observable2
  have compareLt : OfficialRuleMajorKey.compare
      fresh1Compound.prior.rule4aKey.constitutional
      fresh2Compound.prior.rule4aKey.constitutional = Ordering.lt := by
    rw [compareEq]
    exact freshRoot_compare_lt
  have cumulativeLt : input.certified.compareLocalizedRerootCumulativeRule45Keys
      fresh1Compound.prior.rule4aKey fresh2Compound.prior.rule4aKey = Ordering.lt := by
    rw [cumulative_compare_eq_constitutional _ _ (by rw [compareLt]; decide)]
    exact compareLt
  exact input.certified.compareLocalizedRerootCompoundThroughRule5_eq_lt_of_rule4a_lt
    fresh1Compound fresh2Compound cumulativeLt

/-- The shipped compound builder produces keys at both actual branch cursors of the generated
reference state. -/
theorem referenceState_freshRootCompound_exists :
    ∃ fresh1Compound fresh2Compound : input.certified.LocalizedRerootCompoundRule45Key,
      input.certified.buildLocalizedRerootCompoundRule45Key?
          root0Occ root0View (2 * (fuel + 1)) branch1Cursor = some fresh1Compound ∧
      input.certified.buildLocalizedRerootCompoundRule45Key?
          root0Occ root0View (2 * (fuel + 1)) branch2Cursor = some fresh2Compound := by
  obtain ⟨first, firstComputed⟩ :=
    input.certified.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
      root0Occ root0View branch1Cursor branch1Cursor_valid
  obtain ⟨second, secondComputed⟩ :=
    input.certified.exists_buildLocalizedRerootCompoundRule45Key?_at_twice
      root0Occ root0View branch2Cursor branch2Cursor_valid
  exact ⟨first, second, firstComputed, secondComputed⟩

/-- **Ordering opposition on one actual input.**  On the same admitted 11-atom source and the same
generated reference state, the shipped compound builder yields, at the shared auxiliary cursors,
a through-Rule-5 record `gt`, and at the actual fresh-root branch cursors, a through-Rule-5
record `lt`.  Both records are non-pseudo.  This is the permitted difference between two outer
root contexts under the explicitly totalized Rule-1b profile; it is neither a chemical bug nor a
final descriptor claim. -/
theorem referenceState_compoundThroughRule5_opposition :
    ∃ parentCompound childCompound fresh1Compound fresh2Compound :
        input.certified.LocalizedRerootCompoundRule45Key,
      input.certified.buildLocalizedRerootCompoundRule45Key? targetOcc
          (input.certified.localizedDependencyView referenceState targetOcc)
          (2 * (fuel + 1)) parentCursor = some parentCompound ∧
      input.certified.buildLocalizedRerootCompoundRule45Key? targetOcc
          (input.certified.localizedDependencyView referenceState targetOcc)
          (2 * (fuel + 1)) outwardCursor = some childCompound ∧
      input.certified.buildLocalizedRerootCompoundRule45Key?
          root0Occ root0View (2 * (fuel + 1)) branch1Cursor = some fresh1Compound ∧
      input.certified.buildLocalizedRerootCompoundRule45Key?
          root0Occ root0View (2 * (fuel + 1)) branch2Cursor = some fresh2Compound ∧
      input.certified.compareLocalizedRerootCompoundThroughRule5
          parentCompound childCompound = { ordering := Ordering.gt, pseudo := false } ∧
      input.certified.compareLocalizedRerootCompoundThroughRule5
          fresh1Compound fresh2Compound = { ordering := Ordering.lt, pseudo := false } := by
  obtain ⟨parentCompound, childCompound, parentComputed, childComputed, parentGt⟩ :=
    referenceState_compoundThroughRule5_gt
  obtain ⟨fresh1Compound, fresh2Compound, firstComputed, secondComputed⟩ :=
    referenceState_freshRootCompound_exists
  exact ⟨parentCompound, childCompound, fresh1Compound, fresh2Compound,
    parentComputed, childComputed, firstComputed, secondComputed, parentGt,
    freshRoot_actual_compare_lt fresh1Compound fresh2Compound firstComputed secondComputed⟩

end TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness

/-! ## Kernel-authority guards for every public declaration -/

assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.root0Frame
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch1Frame
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch2Frame
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf3Frame
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf4Frame
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf5Frame
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf6Frame
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf7Frame
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf8Frame
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.children_freshRootNode
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.children_freshBranch1
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.children_freshBranch2
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.children_freshLeaf3
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.children_freshLeaf4
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.children_freshLeaf5
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.children_freshLeaf6
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.children_freshLeaf7
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.children_freshLeaf8
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.root0Frame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch1Frame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch2Frame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf3Frame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf4Frame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf5Frame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf6Frame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf7Frame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf8Frame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.root0Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch1Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch2Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf3Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf4Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf5Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf6Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf7Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf8Occ
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.root0Cursor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch1Cursor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch2Cursor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf3Cursor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf4Cursor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf5Cursor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf6Cursor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf7Cursor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf8Cursor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.carrierTreeAdjacent_branch1_root0
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.carrierTreeAdjacent_branch2_root0
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.root0Cursor_valid
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch1Cursor_valid
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch2Cursor_valid
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch1Frame_mem_intended
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch2Frame_mem_intended
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch1Cursor_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch2Cursor_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch1NotDuplicate
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch2NotDuplicate
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch1OccNotDuplicate
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch2OccNotDuplicate
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.mem_intended_branch1Cursor_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.mem_intended_branch2Cursor_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf3_intended_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf4_intended_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf5_intended_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf6_intended_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf7_intended_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf8_intended_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.kF3
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.kF4
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.kF5
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.kF6
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.kF7
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.kF8
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf3_ne_leaf4
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf3_ne_leaf5
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf4_ne_leaf5
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf6_ne_leaf7
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf6_ne_leaf8
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.leaf7_ne_leaf8
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.nodup_leaves1
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.nodup_leaves2
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.mem_leaves1_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.mem_leaves2_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.intended_branch1_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.intended_branch2_perm
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.perm_sort_branch1
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.perm_sort_branch2
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.childKeys_branch1_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.childKeys_branch2_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.ranking_freshBranch1
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.ranking_freshBranch2
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch1Children_empty
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch2Children_empty
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch1Children_nonempty
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.branch2Children_nonempty
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.declarative_freshBranch1
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.declarative_freshBranch2
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.root0View
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.cumulative_compare_eq_constitutional
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.freshBranch1_constitutional_observable
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.freshBranch2_constitutional_observable
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.freshRoot_actual_compare_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.referenceState_freshRootCompound_exists
assert_kernel_only TetraStereo.OneCenter.LocalizedActualFreshRootPriorityWitness.referenceState_compoundThroughRule5_opposition
