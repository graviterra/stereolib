import TetraStereo.OneCenter.LocalizedActualEarlierRuleRankWitness
import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableUnique
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false









































namespace TetraStereo.OneCenter.ActualEarlierRuleRankCounterexample

open TetraStereo.OneCenter
open TetraStereo.OneCenter.DeclarativeCIP
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.EarlierRuleRankWitness

/-! ## The supplied descriptor map and the actual dependency context -/

/-- Supplied descriptor values: `R` at the branch-A root `1` and its methyl `2`, at the branch-B
methyls `12` and `13`; `S` at the branch-B root `11`; `none` elsewhere.  This is explicit supplied
map data.  It is not the physical reference state of the molecule. -/
def suppliedDescriptor (atom : Atom) : Option Descriptor :=
  match atom.val with
  | 1 => some .R
  | 2 => some .R
  | 11 => some .S
  | 12 => some .R
  | 13 => some .R
  | _ => none

/-- The supplied `DescriptorMap` on the actual detected-occurrence inventory. -/
def fixtureMap (occurrence : DetectedOccurrence input.moleculeGraph) : Option Descriptor :=
  suppliedDescriptor occurrence.1.atom

/-- One-step unfolding of the molecular view at a concrete occurrence frame. -/
def readOfFrame (frame : input.LocalizedCIPOccurrenceFrame) : Option LocalizedAuxiliaryLabel :=
  if frame.node.provenance = OfficialCIPNodeProvenance.realAtom then
    if _detected : IsDetectedCenter input.moleculeGraph (input.molecularFrameUnit frame).atom then
      (suppliedDescriptor (input.molecularFrameUnit frame).atom).bind Descriptor.toLocalizedLabel
    else none
  else none

/-- The carrier fuel used by the actual final original-root cursors: `atomCount + 1 = 24`. -/
abbrev carrierFuel : Nat := input.certified.input.molecule.atomCount + 1

/-- The actual centre-`0` top target: the distinguished centre-root occurrence. -/
noncomputable def centerOcc : input.LocalizedCIPOccurrence carrierFuel :=
  input.localizedAtomRootOccurrence carrierFuel center.1

/-- The shipped molecular reader's view at the actual centre-`0` top target. -/
noncomputable def topView : input.LocalizedDependencyView centerOcc :=
  input.molecularView fixtureMap centerOcc

theorem molecularView_eq_readOfFrame {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (cursor : input.LocalizedRerootCursor fuel)
    (dependency : input.LocalizedDepthDependency cursor.occurrence target) :
    input.molecularView fixtureMap target cursor.occurrence dependency =
      readOfFrame cursor.occurrence.1 :=
  rfl

theorem localizedDependencyLabel_eq_readOfFrame {fuel : Nat}
    (target : input.LocalizedCIPOccurrence fuel)
    (cursor : input.LocalizedRerootCursor fuel)
    (dependency : input.LocalizedDepthDependency cursor.occurrence target) :
    input.localizedDependencyLabel target (input.molecularView fixtureMap target) cursor =
      readOfFrame cursor.occurrence.1 := by
  unfold CertifiedLocalizedCIPInput.localizedDependencyLabel
  rw [dif_pos dependency]
  exact molecularView_eq_readOfFrame target cursor dependency

/-! ## The exact carrier frames below the centre-`0` root -/

def branchAFrame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [0], node := node1, remaining := 24 }

def branchBFrame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [1], node := node11, remaining := 24 }

def methyl2Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [0, 0], node := node2, remaining := 23 }

def methyl3Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [0, 1], node := node3, remaining := 23 }

def methyl12Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [1, 0], node := node12, remaining := 23 }

def methyl13Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [1, 1], node := node13, remaining := 23 }

def h5Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [0, 0, 0], node := node5, remaining := 22 }

def h6Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [0, 0, 1], node := node6, remaining := 22 }

def h7Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [0, 0, 2], node := node7, remaining := 22 }

def h8Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [0, 1, 0], node := node8, remaining := 22 }

def h9Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [0, 1, 1], node := node9, remaining := 22 }

def h10Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [0, 1, 2], node := node10, remaining := 22 }

def h15Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [1, 0, 0], node := node15, remaining := 22 }

def h16Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [1, 0, 1], node := node16, remaining := 22 }

def h17Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [1, 0, 2], node := node17, remaining := 22 }

def h18Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [1, 1, 0], node := node18, remaining := 22 }

def h19Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [1, 1, 1], node := node19, remaining := 22 }

def h20Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [1, 1, 2], node := node20, remaining := 22 }

def h4Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [0, 2], node := node4, remaining := 23 }

def h14Frame : input.LocalizedCIPOccurrenceFrame :=
  { root := a0, address := [1, 2], node := node14, remaining := 23 }

/-! ## Actual carrier membership of every frame -/

theorem branchAFrame_mem : branchAFrame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel branchAFrame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 branchAFrame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node1) (slot := 0)
    (occurrence := branchAFrame) ?_ ?_
  · rw [children_node0]; simp
  · simpa [branchAFrame] using
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
        (root := a0) (input := input) (path :=[0]) (fuel := 24) (node := node1))

theorem branchBFrame_mem : branchBFrame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel branchBFrame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 branchBFrame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node11) (slot := 1)
    (occurrence := branchBFrame) ?_ ?_
  · rw [children_node0]; simp
  · simpa [branchBFrame] using
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
        (root := a0) (input := input) (path :=[1]) (fuel := 24) (node := node11))

theorem methyl2Frame_mem : methyl2Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel methyl2Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 methyl2Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node1) (slot := 0)
    (occurrence := methyl2Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[0]) (fuel := 23) (node := node1) (child := node2) (slot := 0)
      (occurrence := methyl2Frame) ?_ ?_
    · rw [children_node1]; simp
    · simpa [methyl2Frame] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (root := a0) (input := input) (path :=[0, 0]) (fuel := 23) (node := node2))

theorem methyl3Frame_mem : methyl3Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel methyl3Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 methyl3Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node1) (slot := 0)
    (occurrence := methyl3Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[0]) (fuel := 23) (node := node1) (child := node3) (slot := 1)
      (occurrence := methyl3Frame) ?_ ?_
    · rw [children_node1]; simp
    · simpa [methyl3Frame] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (root := a0) (input := input) (path :=[0, 1]) (fuel := 23) (node := node3))

theorem methyl12Frame_mem : methyl12Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel methyl12Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 methyl12Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node11) (slot := 1)
    (occurrence := methyl12Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[1]) (fuel := 23) (node := node11) (child := node12) (slot := 0)
      (occurrence := methyl12Frame) ?_ ?_
    · rw [children_node11]; simp
    · simpa [methyl12Frame] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (root := a0) (input := input) (path :=[1, 0]) (fuel := 23) (node := node12))

theorem methyl13Frame_mem : methyl13Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel methyl13Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 methyl13Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node11) (slot := 1)
    (occurrence := methyl13Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[1]) (fuel := 23) (node := node11) (child := node13) (slot := 1)
      (occurrence := methyl13Frame) ?_ ?_
    · rw [children_node11]; simp
    · simpa [methyl13Frame] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (root := a0) (input := input) (path :=[1, 1]) (fuel := 23) (node := node13))

theorem h5Frame_mem : h5Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h5Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h5Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node1) (slot := 0)
    (occurrence := h5Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[0]) (fuel := 23) (node := node1) (child := node2) (slot := 0)
      (occurrence := h5Frame) ?_ ?_
    · rw [children_node1]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := input) (path :=[0, 0]) (fuel := 22) (node := node2) (child := node5) (slot := 0)
        (occurrence := h5Frame) ?_ ?_
      · rw [children_node2]; simp
      · simpa [h5Frame] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (root := a0) (input := input) (path :=[0, 0, 0]) (fuel := 22) (node := node5))

theorem h6Frame_mem : h6Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h6Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h6Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node1) (slot := 0)
    (occurrence := h6Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[0]) (fuel := 23) (node := node1) (child := node2) (slot := 0)
      (occurrence := h6Frame) ?_ ?_
    · rw [children_node1]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := input) (path :=[0, 0]) (fuel := 22) (node := node2) (child := node6) (slot := 1)
        (occurrence := h6Frame) ?_ ?_
      · rw [children_node2]; simp
      · simpa [h6Frame] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (root := a0) (input := input) (path :=[0, 0, 1]) (fuel := 22) (node := node6))

theorem h7Frame_mem : h7Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h7Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h7Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node1) (slot := 0)
    (occurrence := h7Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[0]) (fuel := 23) (node := node1) (child := node2) (slot := 0)
      (occurrence := h7Frame) ?_ ?_
    · rw [children_node1]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := input) (path :=[0, 0]) (fuel := 22) (node := node2) (child := node7) (slot := 2)
        (occurrence := h7Frame) ?_ ?_
      · rw [children_node2]; simp
      · simpa [h7Frame] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (root := a0) (input := input) (path :=[0, 0, 2]) (fuel := 22) (node := node7))

theorem h8Frame_mem : h8Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h8Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h8Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node1) (slot := 0)
    (occurrence := h8Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[0]) (fuel := 23) (node := node1) (child := node3) (slot := 1)
      (occurrence := h8Frame) ?_ ?_
    · rw [children_node1]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := input) (path :=[0, 1]) (fuel := 22) (node := node3) (child := node8) (slot := 0)
        (occurrence := h8Frame) ?_ ?_
      · rw [children_node3]; simp
      · simpa [h8Frame] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (root := a0) (input := input) (path :=[0, 1, 0]) (fuel := 22) (node := node8))

theorem h9Frame_mem : h9Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h9Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h9Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node1) (slot := 0)
    (occurrence := h9Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[0]) (fuel := 23) (node := node1) (child := node3) (slot := 1)
      (occurrence := h9Frame) ?_ ?_
    · rw [children_node1]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := input) (path :=[0, 1]) (fuel := 22) (node := node3) (child := node9) (slot := 1)
        (occurrence := h9Frame) ?_ ?_
      · rw [children_node3]; simp
      · simpa [h9Frame] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (root := a0) (input := input) (path :=[0, 1, 1]) (fuel := 22) (node := node9))

theorem h10Frame_mem : h10Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h10Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h10Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node1) (slot := 0)
    (occurrence := h10Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[0]) (fuel := 23) (node := node1) (child := node3) (slot := 1)
      (occurrence := h10Frame) ?_ ?_
    · rw [children_node1]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := input) (path :=[0, 1]) (fuel := 22) (node := node3) (child := node10) (slot := 2)
        (occurrence := h10Frame) ?_ ?_
      · rw [children_node3]; simp
      · simpa [h10Frame] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (root := a0) (input := input) (path :=[0, 1, 2]) (fuel := 22) (node := node10))

theorem h15Frame_mem : h15Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h15Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h15Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node11) (slot := 1)
    (occurrence := h15Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[1]) (fuel := 23) (node := node11) (child := node12) (slot := 0)
      (occurrence := h15Frame) ?_ ?_
    · rw [children_node11]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := input) (path :=[1, 0]) (fuel := 22) (node := node12) (child := node15) (slot := 0)
        (occurrence := h15Frame) ?_ ?_
      · rw [children_node12]; simp
      · simpa [h15Frame] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (root := a0) (input := input) (path :=[1, 0, 0]) (fuel := 22) (node := node15))

theorem h16Frame_mem : h16Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h16Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h16Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node11) (slot := 1)
    (occurrence := h16Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[1]) (fuel := 23) (node := node11) (child := node12) (slot := 0)
      (occurrence := h16Frame) ?_ ?_
    · rw [children_node11]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := input) (path :=[1, 0]) (fuel := 22) (node := node12) (child := node16) (slot := 1)
        (occurrence := h16Frame) ?_ ?_
      · rw [children_node12]; simp
      · simpa [h16Frame] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (root := a0) (input := input) (path :=[1, 0, 1]) (fuel := 22) (node := node16))

theorem h17Frame_mem : h17Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h17Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h17Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node11) (slot := 1)
    (occurrence := h17Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[1]) (fuel := 23) (node := node11) (child := node12) (slot := 0)
      (occurrence := h17Frame) ?_ ?_
    · rw [children_node11]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := input) (path :=[1, 0]) (fuel := 22) (node := node12) (child := node17) (slot := 2)
        (occurrence := h17Frame) ?_ ?_
      · rw [children_node12]; simp
      · simpa [h17Frame] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (root := a0) (input := input) (path :=[1, 0, 2]) (fuel := 22) (node := node17))

theorem h18Frame_mem : h18Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h18Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h18Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node11) (slot := 1)
    (occurrence := h18Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[1]) (fuel := 23) (node := node11) (child := node13) (slot := 1)
      (occurrence := h18Frame) ?_ ?_
    · rw [children_node11]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := input) (path :=[1, 1]) (fuel := 22) (node := node13) (child := node18) (slot := 0)
        (occurrence := h18Frame) ?_ ?_
      · rw [children_node13]; simp
      · simpa [h18Frame] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (root := a0) (input := input) (path :=[1, 1, 0]) (fuel := 22) (node := node18))

theorem h19Frame_mem : h19Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h19Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h19Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node11) (slot := 1)
    (occurrence := h19Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[1]) (fuel := 23) (node := node11) (child := node13) (slot := 1)
      (occurrence := h19Frame) ?_ ?_
    · rw [children_node11]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := input) (path :=[1, 1]) (fuel := 22) (node := node13) (child := node19) (slot := 1)
        (occurrence := h19Frame) ?_ ?_
      · rw [children_node13]; simp
      · simpa [h19Frame] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (root := a0) (input := input) (path :=[1, 1, 1]) (fuel := 22) (node := node19))

theorem h20Frame_mem : h20Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h20Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h20Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path :=[]) (fuel := 24) (node := node0) (child := node11) (slot := 1)
    (occurrence := h20Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path :=[1]) (fuel := 23) (node := node11) (child := node13) (slot := 1)
      (occurrence := h20Frame) ?_ ?_
    · rw [children_node11]; simp
    · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := input) (path :=[1, 1]) (fuel := 22) (node := node13) (child := node20) (slot := 2)
        (occurrence := h20Frame) ?_ ?_
      · rw [children_node13]; simp
      · simpa [h20Frame] using
          (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
            (root := a0) (input := input) (path :=[1, 1, 2]) (fuel := 22) (node := node20))

theorem h4Frame_mem : h4Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h4Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h4Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path := []) (fuel := 24) (node := node0) (child := node1) (slot := 0)
    (occurrence := h4Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path := [0]) (fuel := 23) (node := node1) (child := node4) (slot := 2)
      (occurrence := h4Frame) ?_ ?_
    · rw [children_node1]; simp
    · simpa [h4Frame] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (root := a0) (input := input) (path := [0, 2]) (fuel := 23) (node := node4))

theorem h14Frame_mem : h14Frame ∈ input.localizedOccurrences carrierFuel := by
  rw [input.mem_localizedOccurrences_iff carrierFuel h14Frame]
  change input.DeclarativeLocalizedOccurrenceSubtree a0 [] 25 node0 h14Frame
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := input) (path := []) (fuel := 24) (node := node0) (child := node11) (slot := 1)
    (occurrence := h14Frame) ?_ ?_
  · rw [children_node0]; simp
  · refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := input) (path := [1]) (fuel := 23) (node := node11) (child := node14) (slot := 2)
      (occurrence := h14Frame) ?_ ?_
    · rw [children_node11]; simp
    · simpa [h14Frame] using
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (root := a0) (input := input) (path := [1, 2]) (fuel := 23) (node := node14))

/-! ## Actual occurrences and reroot cursors -/

def branchAOcc : input.LocalizedCIPOccurrence carrierFuel := ⟨branchAFrame, branchAFrame_mem⟩
def branchBOcc : input.LocalizedCIPOccurrence carrierFuel := ⟨branchBFrame, branchBFrame_mem⟩
def methyl2Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨methyl2Frame, methyl2Frame_mem⟩
def methyl3Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨methyl3Frame, methyl3Frame_mem⟩
def methyl12Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨methyl12Frame, methyl12Frame_mem⟩
def methyl13Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨methyl13Frame, methyl13Frame_mem⟩
def h5Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h5Frame, h5Frame_mem⟩
def h6Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h6Frame, h6Frame_mem⟩
def h7Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h7Frame, h7Frame_mem⟩
def h8Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h8Frame, h8Frame_mem⟩
def h9Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h9Frame, h9Frame_mem⟩
def h10Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h10Frame, h10Frame_mem⟩
def h15Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h15Frame, h15Frame_mem⟩
def h16Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h16Frame, h16Frame_mem⟩
def h17Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h17Frame, h17Frame_mem⟩
def h18Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h18Frame, h18Frame_mem⟩
def h19Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h19Frame, h19Frame_mem⟩
def h20Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h20Frame, h20Frame_mem⟩
def h4Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h4Frame, h4Frame_mem⟩
def h14Occ : input.LocalizedCIPOccurrence carrierFuel := ⟨h14Frame, h14Frame_mem⟩

noncomputable def branchACursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := branchAOcc, previous? := some centerOcc }

noncomputable def branchBCursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := branchBOcc, previous? := some centerOcc }

def methyl2Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := methyl2Occ, previous? := some branchAOcc }

def methyl3Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := methyl3Occ, previous? := some branchAOcc }

def methyl12Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := methyl12Occ, previous? := some branchBOcc }

def methyl13Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := methyl13Occ, previous? := some branchBOcc }

def h5Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h5Occ, previous? := some methyl2Occ }

def h6Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h6Occ, previous? := some methyl2Occ }

def h7Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h7Occ, previous? := some methyl2Occ }

def h8Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h8Occ, previous? := some methyl3Occ }

def h9Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h9Occ, previous? := some methyl3Occ }

def h10Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h10Occ, previous? := some methyl3Occ }

def h15Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h15Occ, previous? := some methyl12Occ }

def h16Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h16Occ, previous? := some methyl12Occ }

def h17Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h17Occ, previous? := some methyl12Occ }

def h18Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h18Occ, previous? := some methyl13Occ }

def h19Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h19Occ, previous? := some methyl13Occ }

def h20Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h20Occ, previous? := some methyl13Occ }

def h4Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h4Occ, previous? := some branchAOcc }

def h14Cursor : input.LocalizedRerootCursor carrierFuel :=
  { occurrence := h14Occ, previous? := some branchBOcc }

/-! ## The two branch cursors are the shipped canonical ligand-root cursors -/

theorem ligandRootNode_zero : input.localizedLigandRootNode center 0 = node1 := by
  rw [CertifiedLocalizedCIPInput.localizedLigandRootNode, canonicalLigandAtom_center_zero]
  rfl

theorem ligandRootNode_one : input.localizedLigandRootNode center 1 = node11 := by
  rw [CertifiedLocalizedCIPInput.localizedLigandRootNode, canonicalLigandAtom_center_one]
  rfl

theorem ligandRootSlot_zero : input.localizedLigandRootSlot center 0 = 0 := by
  rw [CertifiedLocalizedCIPInput.localizedLigandRootSlot, ligandRootNode_zero]
  change List.idxOf node1 (input.executableOfficialCIPChildren node0) = 0
  rw [children_node0]
  decide +kernel

theorem ligandRootSlot_one : input.localizedLigandRootSlot center 1 = 1 := by
  rw [CertifiedLocalizedCIPInput.localizedLigandRootSlot, ligandRootNode_one]
  change List.idxOf node11 (input.executableOfficialCIPChildren node0) = 1
  rw [children_node0]
  decide +kernel

theorem ligandRootOccurrence_zero :
    (input.localizedLigandRootCursor center 0).occurrence.1 =
      ({ root := a0, address := [0], node := node1, remaining := 24 } :
        input.LocalizedCIPOccurrenceFrame) := by
  rw [show (input.localizedLigandRootCursor center 0).occurrence.1 =
      ({ root := center.1, address := [input.localizedLigandRootSlot center 0],
         node := input.localizedLigandRootNode center 0,
         remaining := input.certified.input.molecule.atomCount + 1 } :
        input.LocalizedCIPOccurrenceFrame) from rfl]
  rw [center_val, ligandRootSlot_zero, ligandRootNode_zero]
  rfl

theorem ligandRootOccurrence_one :
    (input.localizedLigandRootCursor center 1).occurrence.1 =
      ({ root := a0, address := [1], node := node11, remaining := 24 } :
        input.LocalizedCIPOccurrenceFrame) := by
  rw [show (input.localizedLigandRootCursor center 1).occurrence.1 =
      ({ root := center.1, address := [input.localizedLigandRootSlot center 1],
         node := input.localizedLigandRootNode center 1,
         remaining := input.certified.input.molecule.atomCount + 1 } :
        input.LocalizedCIPOccurrenceFrame) from rfl]
  rw [center_val, ligandRootSlot_one, ligandRootNode_one]
  rfl

theorem branchACursor_eq_ligandRoot :
    branchACursor = input.localizedLigandRootCursor center 0 := by
  apply LocalizedRerootCursor.ext input
  · apply Subtype.ext
    rw [ligandRootOccurrence_zero]
    rfl
  · rfl

theorem branchBCursor_eq_ligandRoot :
    branchBCursor = input.localizedLigandRootCursor center 1 := by
  apply LocalizedRerootCursor.ext input
  · apply Subtype.ext
    rw [ligandRootOccurrence_one]
    rfl
  · rfl

/-! ## Actual label readings at the concrete cursors -/

theorem branchACursor_dependency :
    input.LocalizedDepthDependency branchACursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [branchACursor, branchAOcc, branchAFrame, centerOcc, carrierFuel]

theorem branchBCursor_dependency :
    input.LocalizedDepthDependency branchBCursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [branchBCursor, branchBOcc, branchBFrame, centerOcc, carrierFuel]

theorem methyl2Cursor_dependency :
    input.LocalizedDepthDependency methyl2Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [methyl2Cursor, methyl2Occ, methyl2Frame, centerOcc, carrierFuel]

theorem methyl3Cursor_dependency :
    input.LocalizedDepthDependency methyl3Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [methyl3Cursor, methyl3Occ, methyl3Frame, centerOcc, carrierFuel]

theorem methyl12Cursor_dependency :
    input.LocalizedDepthDependency methyl12Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [methyl12Cursor, methyl12Occ, methyl12Frame, centerOcc, carrierFuel]

theorem methyl13Cursor_dependency :
    input.LocalizedDepthDependency methyl13Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [methyl13Cursor, methyl13Occ, methyl13Frame, centerOcc, carrierFuel]

theorem h5Cursor_dependency :
    input.LocalizedDepthDependency h5Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h5Cursor, h5Occ, h5Frame, centerOcc, carrierFuel]

theorem h6Cursor_dependency :
    input.LocalizedDepthDependency h6Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h6Cursor, h6Occ, h6Frame, centerOcc, carrierFuel]

theorem h7Cursor_dependency :
    input.LocalizedDepthDependency h7Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h7Cursor, h7Occ, h7Frame, centerOcc, carrierFuel]

theorem h8Cursor_dependency :
    input.LocalizedDepthDependency h8Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h8Cursor, h8Occ, h8Frame, centerOcc, carrierFuel]

theorem h9Cursor_dependency :
    input.LocalizedDepthDependency h9Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h9Cursor, h9Occ, h9Frame, centerOcc, carrierFuel]

theorem h10Cursor_dependency :
    input.LocalizedDepthDependency h10Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h10Cursor, h10Occ, h10Frame, centerOcc, carrierFuel]

theorem h15Cursor_dependency :
    input.LocalizedDepthDependency h15Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h15Cursor, h15Occ, h15Frame, centerOcc, carrierFuel]

theorem h16Cursor_dependency :
    input.LocalizedDepthDependency h16Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h16Cursor, h16Occ, h16Frame, centerOcc, carrierFuel]

theorem h17Cursor_dependency :
    input.LocalizedDepthDependency h17Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h17Cursor, h17Occ, h17Frame, centerOcc, carrierFuel]

theorem h18Cursor_dependency :
    input.LocalizedDepthDependency h18Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h18Cursor, h18Occ, h18Frame, centerOcc, carrierFuel]

theorem h19Cursor_dependency :
    input.LocalizedDepthDependency h19Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h19Cursor, h19Occ, h19Frame, centerOcc, carrierFuel]

theorem h20Cursor_dependency :
    input.LocalizedDepthDependency h20Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h20Cursor, h20Occ, h20Frame, centerOcc, carrierFuel]

theorem h4Cursor_dependency :
    input.LocalizedDepthDependency h4Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h4Cursor, h4Occ, h4Frame, centerOcc, carrierFuel]

theorem h14Cursor_dependency :
    input.LocalizedDepthDependency h14Cursor.occurrence centerOcc := by
  refine ⟨rfl, ?_⟩
  simp [h14Cursor, h14Occ, h14Frame, centerOcc, carrierFuel]

theorem read_branchA :
    input.localizedDependencyLabel centerOcc topView branchACursor =
      some (.chiral RS.R) := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      branchACursor = some (.chiral RS.R)
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc branchACursor branchACursor_dependency]
  decide +kernel

theorem read_branchB :
    input.localizedDependencyLabel centerOcc topView branchBCursor =
      some (.chiral RS.S) := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      branchBCursor = some (.chiral RS.S)
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc branchBCursor branchBCursor_dependency]
  decide +kernel

theorem read_methyl2 :
    input.localizedDependencyLabel centerOcc topView methyl2Cursor =
      some (.chiral RS.R) := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      methyl2Cursor = some (.chiral RS.R)
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc methyl2Cursor methyl2Cursor_dependency]
  decide +kernel

theorem read_methyl3 :
    input.localizedDependencyLabel centerOcc topView methyl3Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      methyl3Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc methyl3Cursor methyl3Cursor_dependency]
  decide +kernel

theorem read_methyl12 :
    input.localizedDependencyLabel centerOcc topView methyl12Cursor =
      some (.chiral RS.R) := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      methyl12Cursor = some (.chiral RS.R)
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc methyl12Cursor methyl12Cursor_dependency]
  decide +kernel

theorem read_methyl13 :
    input.localizedDependencyLabel centerOcc topView methyl13Cursor =
      some (.chiral RS.R) := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      methyl13Cursor = some (.chiral RS.R)
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc methyl13Cursor methyl13Cursor_dependency]
  decide +kernel

theorem read_h5 : input.localizedDependencyLabel centerOcc topView h5Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h5Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h5Cursor h5Cursor_dependency]
  decide +kernel

theorem read_h6 : input.localizedDependencyLabel centerOcc topView h6Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h6Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h6Cursor h6Cursor_dependency]
  decide +kernel

theorem read_h7 : input.localizedDependencyLabel centerOcc topView h7Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h7Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h7Cursor h7Cursor_dependency]
  decide +kernel

theorem read_h8 : input.localizedDependencyLabel centerOcc topView h8Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h8Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h8Cursor h8Cursor_dependency]
  decide +kernel

theorem read_h9 : input.localizedDependencyLabel centerOcc topView h9Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h9Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h9Cursor h9Cursor_dependency]
  decide +kernel

theorem read_h10 : input.localizedDependencyLabel centerOcc topView h10Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h10Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h10Cursor h10Cursor_dependency]
  decide +kernel

theorem read_h15 : input.localizedDependencyLabel centerOcc topView h15Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h15Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h15Cursor h15Cursor_dependency]
  decide +kernel

theorem read_h16 : input.localizedDependencyLabel centerOcc topView h16Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h16Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h16Cursor h16Cursor_dependency]
  decide +kernel

theorem read_h17 : input.localizedDependencyLabel centerOcc topView h17Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h17Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h17Cursor h17Cursor_dependency]
  decide +kernel

theorem read_h18 : input.localizedDependencyLabel centerOcc topView h18Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h18Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h18Cursor h18Cursor_dependency]
  decide +kernel

theorem read_h19 : input.localizedDependencyLabel centerOcc topView h19Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h19Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h19Cursor h19Cursor_dependency]
  decide +kernel

theorem read_h20 : input.localizedDependencyLabel centerOcc topView h20Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h20Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h20Cursor h20Cursor_dependency]
  decide +kernel

theorem read_h4 : input.localizedDependencyLabel centerOcc topView h4Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h4Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h4Cursor h4Cursor_dependency]
  decide +kernel

theorem read_h14 : input.localizedDependencyLabel centerOcc topView h14Cursor = none := by
  change input.localizedDependencyLabel centerOcc (input.molecularView fixtureMap centerOcc)
      h14Cursor = none
  rw [localizedDependencyLabel_eq_readOfFrame centerOcc h14Cursor h14Cursor_dependency]
  decide +kernel

/-! ## Generic expansion facts -/

/-- Every intended child frame corresponds to an executable child cursor. -/
theorem mem_executable_of_mem_intended {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (frame : input.LocalizedCIPOccurrenceFrame)
    (present : frame ∈ input.intendedLocalizedRerootChildFrames cursor) :
    ({ occurrence :=
         ⟨frame,
           input.mem_localizedOccurrences_of_mem_intendedLocalizedRerootChildFrames
             cursor frame present⟩
       previous? := some cursor.occurrence } :
        input.LocalizedRerootCursor fuel) ∈
      input.executableLocalizedRerootChildren cursor := by
  unfold CertifiedLocalizedCIPInput.executableLocalizedRerootChildren
  rw [List.mem_map]
  exact ⟨⟨frame, present⟩, List.mem_attach _ _, rfl⟩

/-- A cursor whose node is a cut leaf has no intended children. -/
theorem intended_eq_nil_of_leaf_cut {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (prev : input.LocalizedCIPOccurrence fuel)
    (previousEq : cursor.previous? = some prev)
    (cutParent : prev.1.address = cursor.occurrence.1.address.dropLast)
    (leaf : input.executableOfficialCIPChildren cursor.occurrence.1.node = []) :
    input.intendedLocalizedRerootChildFrames cursor = [] := by
  unfold CertifiedLocalizedCIPInput.intendedLocalizedRerootChildFrames
  by_cases duplicate : cursor.occurrence.1.node.isDuplicateLeaf
  · simp [duplicate]
  · simp only [duplicate, Bool.false_eq_true, ↓reduceIte, previousEq]
    rw [List.eq_nil_iff_forall_not_mem]
    intro g gPresent
    rw [List.mem_filter] at gPresent
    rcases gPresent with ⟨gNeighbor, gAddressNe⟩
    rw [CertifiedLocalizedCIPInput.localizedRerootNeighborFrames, List.mem_append] at gNeighbor
    rcases gNeighbor with parentPresent | childPresent
    · rw [CertifiedLocalizedCIPInput.localizedCarrierParentFrames, List.mem_filter] at parentPresent
      rcases parentPresent with ⟨_gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have sameAddress : g.address = prev.1.address := by
        rw [conditions.2, cutParent]
      simp [sameAddress] at gAddressNe
    · rw [CertifiedLocalizedCIPInput.localizedCarrierOutwardChildFrames, List.mem_filter]
        at childPresent
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
        have split := List.dropLast_append_getLast gNonempty
        rw [gDrop] at split
        exact split.symm
      have gDerived := (input.mem_localizedOccurrences_iff fuel g).mp gCarrier
      have sourceDerived :=
        (input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp cursor.occurrence.2
      obtain ⟨child, childAtSlot, _occurrenceEq⟩ :=
        input.declarativeLocalizedOccurrence_immediate_child
          sourceDerived gDerived gRoot slot addressEq
      rw [leaf] at childAtSlot
      simp at childAtSlot

/-- The executable child frame list of a cut leaf is empty. -/
theorem executableChildren_eq_nil_of_intended_eq_nil {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (intendedNil : input.intendedLocalizedRerootChildFrames cursor = []) :
    (input.executableLocalizedRerootChildren cursor).map (fun c => c.occurrence.1) = [] := by
  rw [input.executableLocalizedRerootChildren_map cursor, intendedNil]

/-- The executable child cursor list of a cut leaf is empty. -/
theorem executableCursors_eq_nil_of_intended_eq_nil {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (intendedNil : input.intendedLocalizedRerootChildFrames cursor = []) :
    input.executableLocalizedRerootChildren cursor = [] := by
  have mappedNil := executableChildren_eq_nil_of_intended_eq_nil cursor intendedNil
  cases computed : input.executableLocalizedRerootChildren cursor with
  | nil => rfl
  | cons head tail =>
      rw [computed] at mappedNil
      simp at mappedNil

/-- The executable child cursor list is nonempty when its frame projection is. -/
theorem executableCursors_ne_nil_of_intended_ne_nil {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (intendedNe : input.intendedLocalizedRerootChildFrames cursor ≠ []) :
    input.executableLocalizedRerootChildren cursor ≠ [] := by
  intro empty
  apply intendedNe
  rw [← input.executableLocalizedRerootChildren_map cursor, empty]
  rfl

/-! ## Nondeduplicate nodes of the branching cursors -/

theorem branchANotDuplicate : branchAFrame.node.isDuplicateLeaf = false := by
  decide +kernel
theorem branchAOccNotDuplicate : branchAOcc.1.node.isDuplicateLeaf = false := by
  decide +kernel
theorem branchBNotDuplicate : branchBFrame.node.isDuplicateLeaf = false := by
  decide +kernel
theorem branchBOccNotDuplicate : branchBOcc.1.node.isDuplicateLeaf = false := by
  decide +kernel
theorem methyl2NotDuplicate : methyl2Frame.node.isDuplicateLeaf = false := by
  decide +kernel
theorem methyl2OccNotDuplicate : methyl2Occ.1.node.isDuplicateLeaf = false := by
  decide +kernel
theorem methyl3NotDuplicate : methyl3Frame.node.isDuplicateLeaf = false := by
  decide +kernel
theorem methyl3OccNotDuplicate : methyl3Occ.1.node.isDuplicateLeaf = false := by
  decide +kernel
theorem methyl12NotDuplicate : methyl12Frame.node.isDuplicateLeaf = false := by
  decide +kernel
theorem methyl12OccNotDuplicate : methyl12Occ.1.node.isDuplicateLeaf = false := by
  decide +kernel
theorem methyl13NotDuplicate : methyl13Frame.node.isDuplicateLeaf = false := by
  decide +kernel
theorem methyl13OccNotDuplicate : methyl13Occ.1.node.isDuplicateLeaf = false := by
  decide +kernel

/-! ## Intended children of the two branch cursors -/

theorem mem_intended_branchACursor_iff (g : input.LocalizedCIPOccurrenceFrame) :
    g ∈ input.intendedLocalizedRerootChildFrames branchACursor ↔
      g = methyl2Frame ∨ g = methyl3Frame ∨ g = h4Frame := by
  constructor
  · intro present
    simp only [intendedLocalizedRerootChildFrames, branchANotDuplicate,
      branchAOccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branchACursor,
      List.mem_filter] at present
    rcases present with ⟨neighbor, addressNe⟩
    rw [localizedRerootNeighborFrames, List.mem_append] at neighbor
    rcases neighbor with parentMem | childMem
    · rw [localizedCarrierParentFrames, List.mem_filter] at parentMem
      rcases parentMem with ⟨_gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have addressNe' : g.address ≠ centerOcc.1.address := by
        intro equal
        rw [equal] at addressNe
        simp at addressNe
      exact absurd (by rw [conditions.2]; rfl) addressNe'
    · rw [localizedCarrierOutwardChildFrames, List.mem_filter] at childMem
      rcases childMem with ⟨gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have gRoot : g.root = branchAFrame.root := conditions.1.1
      have gLength : g.address.length = branchAFrame.address.length + 1 := conditions.1.2
      have gDrop : g.address.dropLast = branchAFrame.address := conditions.2
      have gNonempty : g.address ≠ [] := by
        intro empty
        rw [empty] at gLength
        simp at gLength
      let slot := g.address.getLast gNonempty
      have addressEq : g.address = branchAFrame.address ++ [slot] := by
        have split := List.dropLast_append_getLast gNonempty
        rw [gDrop] at split
        exact split.symm
      have gDerived := (input.mem_localizedOccurrences_iff carrierFuel g).mp gCarrier
      have sourceDerived :=
        (input.mem_localizedOccurrences_iff carrierFuel branchAFrame).mp branchAFrame_mem
      obtain ⟨child, childAtSlot, gEq⟩ :=
        input.declarativeLocalizedOccurrence_immediate_child
          sourceDerived gDerived gRoot slot addressEq
      rw [show branchAFrame.node = node1 from rfl, children_node1] at childAtSlot
      have childCases : (child, slot) = (node2, 0) ∨ (child, slot) = (node3, 1) ∨
          (child, slot) = (node4, 2) := by
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
    · simp only [intendedLocalizedRerootChildFrames, branchANotDuplicate,
        branchAOccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branchACursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨methyl2Frame_mem, by simp [methyl2Frame, branchAOcc, branchAFrame]⟩
      · simp [methyl2Frame, branchAOcc, branchAFrame, centerOcc]
    · simp only [intendedLocalizedRerootChildFrames, branchANotDuplicate,
        branchAOccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branchACursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨methyl3Frame_mem, by simp [methyl3Frame, branchAOcc, branchAFrame]⟩
      · simp [methyl3Frame, branchAOcc, branchAFrame, centerOcc]
    · simp only [intendedLocalizedRerootChildFrames, branchANotDuplicate,
        branchAOccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branchACursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h4Frame_mem, by simp [h4Frame, branchAOcc, branchAFrame]⟩
      · simp [h4Frame, branchAOcc, branchAFrame, centerOcc]

theorem mem_intended_branchBCursor_iff (g : input.LocalizedCIPOccurrenceFrame) :
    g ∈ input.intendedLocalizedRerootChildFrames branchBCursor ↔
      g = methyl12Frame ∨ g = methyl13Frame ∨ g = h14Frame := by
  constructor
  · intro present
    simp only [intendedLocalizedRerootChildFrames, branchBNotDuplicate,
      branchBOccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branchBCursor,
      List.mem_filter] at present
    rcases present with ⟨neighbor, addressNe⟩
    rw [localizedRerootNeighborFrames, List.mem_append] at neighbor
    rcases neighbor with parentMem | childMem
    · rw [localizedCarrierParentFrames, List.mem_filter] at parentMem
      rcases parentMem with ⟨_gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have addressNe' : g.address ≠ centerOcc.1.address := by
        intro equal
        rw [equal] at addressNe
        simp at addressNe
      exact absurd (by rw [conditions.2]; rfl) addressNe'
    · rw [localizedCarrierOutwardChildFrames, List.mem_filter] at childMem
      rcases childMem with ⟨gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have gRoot : g.root = branchBFrame.root := conditions.1.1
      have gLength : g.address.length = branchBFrame.address.length + 1 := conditions.1.2
      have gDrop : g.address.dropLast = branchBFrame.address := conditions.2
      have gNonempty : g.address ≠ [] := by
        intro empty
        rw [empty] at gLength
        simp at gLength
      let slot := g.address.getLast gNonempty
      have addressEq : g.address = branchBFrame.address ++ [slot] := by
        have split := List.dropLast_append_getLast gNonempty
        rw [gDrop] at split
        exact split.symm
      have gDerived := (input.mem_localizedOccurrences_iff carrierFuel g).mp gCarrier
      have sourceDerived :=
        (input.mem_localizedOccurrences_iff carrierFuel branchBFrame).mp branchBFrame_mem
      obtain ⟨child, childAtSlot, gEq⟩ :=
        input.declarativeLocalizedOccurrence_immediate_child
          sourceDerived gDerived gRoot slot addressEq
      rw [show branchBFrame.node = node11 from rfl, children_node11] at childAtSlot
      have childCases : (child, slot) = (node12, 0) ∨ (child, slot) = (node13, 1) ∨
          (child, slot) = (node14, 2) := by
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
    · simp only [intendedLocalizedRerootChildFrames, branchBNotDuplicate,
        branchBOccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branchBCursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨methyl12Frame_mem, by simp [methyl12Frame, branchBOcc, branchBFrame]⟩
      · simp [methyl12Frame, branchBOcc, branchBFrame, centerOcc]
    · simp only [intendedLocalizedRerootChildFrames, branchBNotDuplicate,
        branchBOccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branchBCursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨methyl13Frame_mem, by simp [methyl13Frame, branchBOcc, branchBFrame]⟩
      · simp [methyl13Frame, branchBOcc, branchBFrame, centerOcc]
    · simp only [intendedLocalizedRerootChildFrames, branchBNotDuplicate,
        branchBOccNotDuplicate, Bool.false_eq_true, ↓reduceIte, branchBCursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h14Frame_mem, by simp [h14Frame, branchBOcc, branchBFrame]⟩
      · simp [h14Frame, branchBOcc, branchBFrame, centerOcc]

/-! ## Intended children of the four methyl cursors -/

theorem mem_intended_methyl2Cursor_iff (g : input.LocalizedCIPOccurrenceFrame) :
    g ∈ input.intendedLocalizedRerootChildFrames methyl2Cursor ↔
      g = h5Frame ∨ g = h6Frame ∨ g = h7Frame := by
  constructor
  · intro present
    simp only [intendedLocalizedRerootChildFrames, methyl2NotDuplicate,
      methyl2OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl2Cursor,
      List.mem_filter] at present
    rcases present with ⟨neighbor, addressNe⟩
    rw [localizedRerootNeighborFrames, List.mem_append] at neighbor
    rcases neighbor with parentMem | childMem
    · rw [localizedCarrierParentFrames, List.mem_filter] at parentMem
      rcases parentMem with ⟨_gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have addressNe' : g.address ≠ branchAOcc.1.address := by
        intro equal
        rw [equal] at addressNe
        simp at addressNe
      exact absurd (by rw [conditions.2]; rfl) addressNe'
    · rw [localizedCarrierOutwardChildFrames, List.mem_filter] at childMem
      rcases childMem with ⟨gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have gRoot : g.root = methyl2Frame.root := conditions.1.1
      have gLength : g.address.length = methyl2Frame.address.length + 1 := conditions.1.2
      have gDrop : g.address.dropLast = methyl2Frame.address := conditions.2
      have gNonempty : g.address ≠ [] := by
        intro empty
        rw [empty] at gLength
        simp at gLength
      let slot := g.address.getLast gNonempty
      have addressEq : g.address = methyl2Frame.address ++ [slot] := by
        have split := List.dropLast_append_getLast gNonempty
        rw [gDrop] at split
        exact split.symm
      have gDerived := (input.mem_localizedOccurrences_iff carrierFuel g).mp gCarrier
      have sourceDerived :=
        (input.mem_localizedOccurrences_iff carrierFuel methyl2Frame).mp methyl2Frame_mem
      obtain ⟨child, childAtSlot, gEq⟩ :=
        input.declarativeLocalizedOccurrence_immediate_child
          sourceDerived gDerived gRoot slot addressEq
      rw [show methyl2Frame.node = node2 from rfl, children_node2] at childAtSlot
      have childCases : (child, slot) = (node5, 0) ∨ (child, slot) = (node6, 1) ∨
          (child, slot) = (node7, 2) := by
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
    · simp only [intendedLocalizedRerootChildFrames, methyl2NotDuplicate,
        methyl2OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl2Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h5Frame_mem, by simp [h5Frame, methyl2Occ, methyl2Frame]⟩
      · simp [h5Frame, methyl2Occ, methyl2Frame, branchAOcc, branchAFrame]
    · simp only [intendedLocalizedRerootChildFrames, methyl2NotDuplicate,
        methyl2OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl2Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h6Frame_mem, by simp [h6Frame, methyl2Occ, methyl2Frame]⟩
      · simp [h6Frame, methyl2Occ, methyl2Frame, branchAOcc, branchAFrame]
    · simp only [intendedLocalizedRerootChildFrames, methyl2NotDuplicate,
        methyl2OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl2Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h7Frame_mem, by simp [h7Frame, methyl2Occ, methyl2Frame]⟩
      · simp [h7Frame, methyl2Occ, methyl2Frame, branchAOcc, branchAFrame]

theorem mem_intended_methyl3Cursor_iff (g : input.LocalizedCIPOccurrenceFrame) :
    g ∈ input.intendedLocalizedRerootChildFrames methyl3Cursor ↔
      g = h8Frame ∨ g = h9Frame ∨ g = h10Frame := by
  constructor
  · intro present
    simp only [intendedLocalizedRerootChildFrames, methyl3NotDuplicate,
      methyl3OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl3Cursor,
      List.mem_filter] at present
    rcases present with ⟨neighbor, addressNe⟩
    rw [localizedRerootNeighborFrames, List.mem_append] at neighbor
    rcases neighbor with parentMem | childMem
    · rw [localizedCarrierParentFrames, List.mem_filter] at parentMem
      rcases parentMem with ⟨_gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have addressNe' : g.address ≠ branchAOcc.1.address := by
        intro equal
        rw [equal] at addressNe
        simp at addressNe
      exact absurd (by rw [conditions.2]; rfl) addressNe'
    · rw [localizedCarrierOutwardChildFrames, List.mem_filter] at childMem
      rcases childMem with ⟨gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have gRoot : g.root = methyl3Frame.root := conditions.1.1
      have gLength : g.address.length = methyl3Frame.address.length + 1 := conditions.1.2
      have gDrop : g.address.dropLast = methyl3Frame.address := conditions.2
      have gNonempty : g.address ≠ [] := by
        intro empty
        rw [empty] at gLength
        simp at gLength
      let slot := g.address.getLast gNonempty
      have addressEq : g.address = methyl3Frame.address ++ [slot] := by
        have split := List.dropLast_append_getLast gNonempty
        rw [gDrop] at split
        exact split.symm
      have gDerived := (input.mem_localizedOccurrences_iff carrierFuel g).mp gCarrier
      have sourceDerived :=
        (input.mem_localizedOccurrences_iff carrierFuel methyl3Frame).mp methyl3Frame_mem
      obtain ⟨child, childAtSlot, gEq⟩ :=
        input.declarativeLocalizedOccurrence_immediate_child
          sourceDerived gDerived gRoot slot addressEq
      rw [show methyl3Frame.node = node3 from rfl, children_node3] at childAtSlot
      have childCases : (child, slot) = (node8, 0) ∨ (child, slot) = (node9, 1) ∨
          (child, slot) = (node10, 2) := by
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
    · simp only [intendedLocalizedRerootChildFrames, methyl3NotDuplicate,
        methyl3OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl3Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h8Frame_mem, by simp [h8Frame, methyl3Occ, methyl3Frame]⟩
      · simp [h8Frame, methyl3Occ, methyl3Frame, branchAOcc, branchAFrame]
    · simp only [intendedLocalizedRerootChildFrames, methyl3NotDuplicate,
        methyl3OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl3Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h9Frame_mem, by simp [h9Frame, methyl3Occ, methyl3Frame]⟩
      · simp [h9Frame, methyl3Occ, methyl3Frame, branchAOcc, branchAFrame]
    · simp only [intendedLocalizedRerootChildFrames, methyl3NotDuplicate,
        methyl3OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl3Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h10Frame_mem, by simp [h10Frame, methyl3Occ, methyl3Frame]⟩
      · simp [h10Frame, methyl3Occ, methyl3Frame, branchAOcc, branchAFrame]

theorem mem_intended_methyl12Cursor_iff (g : input.LocalizedCIPOccurrenceFrame) :
    g ∈ input.intendedLocalizedRerootChildFrames methyl12Cursor ↔
      g = h15Frame ∨ g = h16Frame ∨ g = h17Frame := by
  constructor
  · intro present
    simp only [intendedLocalizedRerootChildFrames, methyl12NotDuplicate,
      methyl12OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl12Cursor,
      List.mem_filter] at present
    rcases present with ⟨neighbor, addressNe⟩
    rw [localizedRerootNeighborFrames, List.mem_append] at neighbor
    rcases neighbor with parentMem | childMem
    · rw [localizedCarrierParentFrames, List.mem_filter] at parentMem
      rcases parentMem with ⟨_gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have addressNe' : g.address ≠ branchBOcc.1.address := by
        intro equal
        rw [equal] at addressNe
        simp at addressNe
      exact absurd (by rw [conditions.2]; rfl) addressNe'
    · rw [localizedCarrierOutwardChildFrames, List.mem_filter] at childMem
      rcases childMem with ⟨gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have gRoot : g.root = methyl12Frame.root := conditions.1.1
      have gLength : g.address.length = methyl12Frame.address.length + 1 := conditions.1.2
      have gDrop : g.address.dropLast = methyl12Frame.address := conditions.2
      have gNonempty : g.address ≠ [] := by
        intro empty
        rw [empty] at gLength
        simp at gLength
      let slot := g.address.getLast gNonempty
      have addressEq : g.address = methyl12Frame.address ++ [slot] := by
        have split := List.dropLast_append_getLast gNonempty
        rw [gDrop] at split
        exact split.symm
      have gDerived := (input.mem_localizedOccurrences_iff carrierFuel g).mp gCarrier
      have sourceDerived :=
        (input.mem_localizedOccurrences_iff carrierFuel methyl12Frame).mp methyl12Frame_mem
      obtain ⟨child, childAtSlot, gEq⟩ :=
        input.declarativeLocalizedOccurrence_immediate_child
          sourceDerived gDerived gRoot slot addressEq
      rw [show methyl12Frame.node = node12 from rfl, children_node12] at childAtSlot
      have childCases : (child, slot) = (node15, 0) ∨ (child, slot) = (node16, 1) ∨
          (child, slot) = (node17, 2) := by
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
    · simp only [intendedLocalizedRerootChildFrames, methyl12NotDuplicate,
        methyl12OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl12Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h15Frame_mem, by simp [h15Frame, methyl12Occ, methyl12Frame]⟩
      · simp [h15Frame, methyl12Occ, methyl12Frame, branchBOcc, branchBFrame]
    · simp only [intendedLocalizedRerootChildFrames, methyl12NotDuplicate,
        methyl12OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl12Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h16Frame_mem, by simp [h16Frame, methyl12Occ, methyl12Frame]⟩
      · simp [h16Frame, methyl12Occ, methyl12Frame, branchBOcc, branchBFrame]
    · simp only [intendedLocalizedRerootChildFrames, methyl12NotDuplicate,
        methyl12OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl12Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h17Frame_mem, by simp [h17Frame, methyl12Occ, methyl12Frame]⟩
      · simp [h17Frame, methyl12Occ, methyl12Frame, branchBOcc, branchBFrame]

theorem mem_intended_methyl13Cursor_iff (g : input.LocalizedCIPOccurrenceFrame) :
    g ∈ input.intendedLocalizedRerootChildFrames methyl13Cursor ↔
      g = h18Frame ∨ g = h19Frame ∨ g = h20Frame := by
  constructor
  · intro present
    simp only [intendedLocalizedRerootChildFrames, methyl13NotDuplicate,
      methyl13OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl13Cursor,
      List.mem_filter] at present
    rcases present with ⟨neighbor, addressNe⟩
    rw [localizedRerootNeighborFrames, List.mem_append] at neighbor
    rcases neighbor with parentMem | childMem
    · rw [localizedCarrierParentFrames, List.mem_filter] at parentMem
      rcases parentMem with ⟨_gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have addressNe' : g.address ≠ branchBOcc.1.address := by
        intro equal
        rw [equal] at addressNe
        simp at addressNe
      exact absurd (by rw [conditions.2]; rfl) addressNe'
    · rw [localizedCarrierOutwardChildFrames, List.mem_filter] at childMem
      rcases childMem with ⟨gCarrier, conditions⟩
      simp only [Bool.and_eq_true, beq_iff_eq] at conditions
      have gRoot : g.root = methyl13Frame.root := conditions.1.1
      have gLength : g.address.length = methyl13Frame.address.length + 1 := conditions.1.2
      have gDrop : g.address.dropLast = methyl13Frame.address := conditions.2
      have gNonempty : g.address ≠ [] := by
        intro empty
        rw [empty] at gLength
        simp at gLength
      let slot := g.address.getLast gNonempty
      have addressEq : g.address = methyl13Frame.address ++ [slot] := by
        have split := List.dropLast_append_getLast gNonempty
        rw [gDrop] at split
        exact split.symm
      have gDerived := (input.mem_localizedOccurrences_iff carrierFuel g).mp gCarrier
      have sourceDerived :=
        (input.mem_localizedOccurrences_iff carrierFuel methyl13Frame).mp methyl13Frame_mem
      obtain ⟨child, childAtSlot, gEq⟩ :=
        input.declarativeLocalizedOccurrence_immediate_child
          sourceDerived gDerived gRoot slot addressEq
      rw [show methyl13Frame.node = node13 from rfl, children_node13] at childAtSlot
      have childCases : (child, slot) = (node18, 0) ∨ (child, slot) = (node19, 1) ∨
          (child, slot) = (node20, 2) := by
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
    · simp only [intendedLocalizedRerootChildFrames, methyl13NotDuplicate,
        methyl13OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl13Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h18Frame_mem, by simp [h18Frame, methyl13Occ, methyl13Frame]⟩
      · simp [h18Frame, methyl13Occ, methyl13Frame, branchBOcc, branchBFrame]
    · simp only [intendedLocalizedRerootChildFrames, methyl13NotDuplicate,
        methyl13OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl13Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h19Frame_mem, by simp [h19Frame, methyl13Occ, methyl13Frame]⟩
      · simp [h19Frame, methyl13Occ, methyl13Frame, branchBOcc, branchBFrame]
    · simp only [intendedLocalizedRerootChildFrames, methyl13NotDuplicate,
        methyl13OccNotDuplicate, Bool.false_eq_true, ↓reduceIte, methyl13Cursor,
        List.mem_filter]
      refine ⟨?_, ?_⟩
      · rw [localizedRerootNeighborFrames, List.mem_append]
        right
        rw [localizedCarrierOutwardChildFrames, List.mem_filter]
        exact ⟨h20Frame_mem, by simp [h20Frame, methyl13Occ, methyl13Frame]⟩
      · simp [h20Frame, methyl13Occ, methyl13Frame, branchBOcc, branchBFrame]

/-! ## The cut leaves -/

theorem h4Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h4Cursor = [] :=
  intended_eq_nil_of_leaf_cut h4Cursor branchAOcc rfl (by rfl) children_node4

theorem h14Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h14Cursor = [] :=
  intended_eq_nil_of_leaf_cut h14Cursor branchBOcc rfl (by rfl) children_node14

theorem h5Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h5Cursor = [] :=
  intended_eq_nil_of_leaf_cut h5Cursor methyl2Occ rfl (by rfl) children_node5

theorem h6Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h6Cursor = [] :=
  intended_eq_nil_of_leaf_cut h6Cursor methyl2Occ rfl (by rfl) children_node6

theorem h7Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h7Cursor = [] :=
  intended_eq_nil_of_leaf_cut h7Cursor methyl2Occ rfl (by rfl) children_node7

theorem h8Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h8Cursor = [] :=
  intended_eq_nil_of_leaf_cut h8Cursor methyl3Occ rfl (by rfl) children_node8

theorem h9Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h9Cursor = [] :=
  intended_eq_nil_of_leaf_cut h9Cursor methyl3Occ rfl (by rfl) children_node9

theorem h10Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h10Cursor = [] :=
  intended_eq_nil_of_leaf_cut h10Cursor methyl3Occ rfl (by rfl) children_node10

theorem h15Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h15Cursor = [] :=
  intended_eq_nil_of_leaf_cut h15Cursor methyl12Occ rfl (by rfl) children_node15

theorem h16Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h16Cursor = [] :=
  intended_eq_nil_of_leaf_cut h16Cursor methyl12Occ rfl (by rfl) children_node16

theorem h17Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h17Cursor = [] :=
  intended_eq_nil_of_leaf_cut h17Cursor methyl12Occ rfl (by rfl) children_node17

theorem h18Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h18Cursor = [] :=
  intended_eq_nil_of_leaf_cut h18Cursor methyl13Occ rfl (by rfl) children_node18

theorem h19Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h19Cursor = [] :=
  intended_eq_nil_of_leaf_cut h19Cursor methyl13Occ rfl (by rfl) children_node19

theorem h20Cursor_intended_nil :
    input.intendedLocalizedRerootChildFrames h20Cursor = [] :=
  intended_eq_nil_of_leaf_cut h20Cursor methyl13Occ rfl (by rfl) children_node20

/-! ## Nonemptiness of the six branching cursors -/

theorem branchAChildren_nonempty :
    input.intendedLocalizedRerootChildFrames branchACursor ≠ [] := by
  intro empty
  have present : methyl2Frame ∈ input.intendedLocalizedRerootChildFrames branchACursor :=
    (mem_intended_branchACursor_iff methyl2Frame).mpr (Or.inl rfl)
  rw [empty] at present
  simp at present

theorem branchBChildren_nonempty :
    input.intendedLocalizedRerootChildFrames branchBCursor ≠ [] := by
  intro empty
  have present : methyl12Frame ∈ input.intendedLocalizedRerootChildFrames branchBCursor :=
    (mem_intended_branchBCursor_iff methyl12Frame).mpr (Or.inl rfl)
  rw [empty] at present
  simp at present

theorem methyl2Children_nonempty :
    input.intendedLocalizedRerootChildFrames methyl2Cursor ≠ [] := by
  intro empty
  have present : h5Frame ∈ input.intendedLocalizedRerootChildFrames methyl2Cursor :=
    (mem_intended_methyl2Cursor_iff h5Frame).mpr (Or.inl rfl)
  rw [empty] at present
  simp at present

theorem methyl3Children_nonempty :
    input.intendedLocalizedRerootChildFrames methyl3Cursor ≠ [] := by
  intro empty
  have present : h8Frame ∈ input.intendedLocalizedRerootChildFrames methyl3Cursor :=
    (mem_intended_methyl3Cursor_iff h8Frame).mpr (Or.inl rfl)
  rw [empty] at present
  simp at present

theorem methyl12Children_nonempty :
    input.intendedLocalizedRerootChildFrames methyl12Cursor ≠ [] := by
  intro empty
  have present : h15Frame ∈ input.intendedLocalizedRerootChildFrames methyl12Cursor :=
    (mem_intended_methyl12Cursor_iff h15Frame).mpr (Or.inl rfl)
  rw [empty] at present
  simp at present

theorem methyl13Children_nonempty :
    input.intendedLocalizedRerootChildFrames methyl13Cursor ≠ [] := by
  intro empty
  have present : h18Frame ∈ input.intendedLocalizedRerootChildFrames methyl13Cursor :=
    (mem_intended_methyl13Cursor_iff h18Frame).mpr (Or.inl rfl)
  rw [empty] at present
  simp at present

/-! ## Exact cumulative keys of the actual cursors

All key terms below are built from the *actual* official construction: the actual
`officialRuleMajorRootKey` at every node, the actual `OfficialRuleMajorKey.assemble`, and the actual
descriptor/label/ranked-label merges over an explicitly descending child list.  They are therefore
definitionally the keys that the declarative `.terminal`/`.branch` constructors produce. -/

/-- The comparison-visible cumulative key type of the actual input. -/
abbrev Key := input.LocalizedRerootCumulativeRule45Key

/-- The terminal cumulative key at one node with one observed label. -/
def terminalKey (stage : LocalizedCumulativeRule45Stage)
    (node : OfficialCIPNode Atom) (label : Option LocalizedAuxiliaryLabel) : Key :=
  { constitutional := input.moleculeGraph.officialRuleMajorRootKey node true
    descriptor := [[([], localizedCumulativeRule45Priority stage label)]]
    labels := [[([], label)]]
    rankedLabels := [[([], label)]] }

/-- The branching cumulative key at one node with one label and one explicitly sorted child list. -/
def branchKey (stage : LocalizedCumulativeRule45Stage)
    (node : OfficialCIPNode Atom) (label : Option LocalizedAuxiliaryLabel)
    (sorted : List Key) : Key :=
  { constitutional := OfficialRuleMajorKey.assemble
      (input.moleculeGraph.officialRuleMajorRootKey node false)
      (sorted.map fun child => child.constitutional)
    descriptor := [[([], localizedCumulativeRule45Priority stage label)]] ++
      input.mergeLocalizedRerootDescriptorChildren sorted
    labels := [[([], label)]] ++
      input.mergeLocalizedRerootLabelChildren sorted
    rankedLabels := [[([], label)]] ++
      input.mergeLocalizedRerootRankedLabelChildren sorted }

section LeafKeys

def h5Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node5 none
def h6Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node6 none
def h7Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node7 none
def h8Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node8 none
def h9Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node9 none
def h10Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node10 none
def h15Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node15 none
def h16Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node16 none
def h17Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node17 none
def h18Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node18 none
def h19Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node19 none
def h20Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node20 none
def h4Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node4 none
def h14Key (stage : LocalizedCumulativeRule45Stage) : Key := terminalKey stage node14 none

end LeafKeys

def methyl2Key (stage : LocalizedCumulativeRule45Stage) : Key :=
  branchKey stage node2 (some (.chiral RS.R)) [h5Key stage, h6Key stage, h7Key stage]

def methyl3Key (stage : LocalizedCumulativeRule45Stage) : Key :=
  branchKey stage node3 none [h8Key stage, h9Key stage, h10Key stage]

def methyl12Key (stage : LocalizedCumulativeRule45Stage) : Key :=
  branchKey stage node12 (some (.chiral RS.R)) [h15Key stage, h16Key stage, h17Key stage]

def methyl13Key (stage : LocalizedCumulativeRule45Stage) : Key :=
  branchKey stage node13 (some (.chiral RS.R)) [h18Key stage, h19Key stage, h20Key stage]

def branchAKey (stage : LocalizedCumulativeRule45Stage) : Key :=
  branchKey stage node1 (some (.chiral RS.R)) [methyl2Key stage, methyl3Key stage, h4Key stage]

def branchBKey (stage : LocalizedCumulativeRule45Stage) : Key :=
  branchKey stage node11 (some (.chiral RS.S)) [methyl12Key stage, methyl13Key stage, h14Key stage]

/-! ## Terminal derivations -/

theorem declarative_terminal_of_nil {fuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (stage : LocalizedCumulativeRule45Stage)
    (label : Option LocalizedAuxiliaryLabel)
    (intendedNil : input.intendedLocalizedRerootChildFrames cursor = [])
    (labelEq : input.localizedDependencyLabel centerOcc topView cursor = label) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel cursor
      (terminalKey stage cursor.occurrence.1.node label) := by
  have frame : input.DeclarativeLocalizedRerootChildren cursor [] :=
    ⟨intendedNil.symm, by simp⟩
  have observed : input.DeclarativeLocalizedDependencyLabel centerOcc topView cursor label :=
    (input.localizedDependencyLabel_eq_iff centerOcc topView cursor label).mp labelEq
  exact DeclarativeLocalizedRerootCumulativeRule45Key.terminal frame rfl observed

theorem declarative_h4 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h4Cursor
      (h4Key stage) :=
  declarative_terminal_of_nil h4Cursor stage none h4Cursor_intended_nil read_h4

theorem declarative_h14 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h14Cursor
      (h14Key stage) :=
  declarative_terminal_of_nil h14Cursor stage none h14Cursor_intended_nil read_h14

theorem declarative_h5 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h5Cursor
      (h5Key stage) :=
  declarative_terminal_of_nil h5Cursor stage none h5Cursor_intended_nil read_h5

theorem declarative_h6 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h6Cursor
      (h6Key stage) :=
  declarative_terminal_of_nil h6Cursor stage none h6Cursor_intended_nil read_h6

theorem declarative_h7 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h7Cursor
      (h7Key stage) :=
  declarative_terminal_of_nil h7Cursor stage none h7Cursor_intended_nil read_h7

theorem declarative_h8 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h8Cursor
      (h8Key stage) :=
  declarative_terminal_of_nil h8Cursor stage none h8Cursor_intended_nil read_h8

theorem declarative_h9 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h9Cursor
      (h9Key stage) :=
  declarative_terminal_of_nil h9Cursor stage none h9Cursor_intended_nil read_h9

theorem declarative_h10 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h10Cursor
      (h10Key stage) :=
  declarative_terminal_of_nil h10Cursor stage none h10Cursor_intended_nil read_h10

theorem declarative_h15 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h15Cursor
      (h15Key stage) :=
  declarative_terminal_of_nil h15Cursor stage none h15Cursor_intended_nil read_h15

theorem declarative_h16 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h16Cursor
      (h16Key stage) :=
  declarative_terminal_of_nil h16Cursor stage none h16Cursor_intended_nil read_h16

theorem declarative_h17 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h17Cursor
      (h17Key stage) :=
  declarative_terminal_of_nil h17Cursor stage none h17Cursor_intended_nil read_h17

theorem declarative_h18 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h18Cursor
      (h18Key stage) :=
  declarative_terminal_of_nil h18Cursor stage none h18Cursor_intended_nil read_h18

theorem declarative_h19 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h19Cursor
      (h19Key stage) :=
  declarative_terminal_of_nil h19Cursor stage none h19Cursor_intended_nil read_h19

theorem declarative_h20 (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel h20Cursor
      (h20Key stage) :=
  declarative_terminal_of_nil h20Cursor stage none h20Cursor_intended_nil read_h20

/-! ## Child-key maps and the exact intended child permutations -/

def methyl2ChildKey (stage : LocalizedCumulativeRule45Stage)
    (frame : input.LocalizedCIPOccurrenceFrame) : Key :=
  match frame.address with
  | [0, 0, 0] => h5Key stage
  | [0, 0, 1] => h6Key stage
  | _ => h7Key stage

theorem methyl2ChildKey_h5 (stage : LocalizedCumulativeRule45Stage) :
    methyl2ChildKey stage h5Frame = h5Key stage := rfl
theorem methyl2ChildKey_h6 (stage : LocalizedCumulativeRule45Stage) :
    methyl2ChildKey stage h6Frame = h6Key stage := rfl
theorem methyl2ChildKey_h7 (stage : LocalizedCumulativeRule45Stage) :
    methyl2ChildKey stage h7Frame = h7Key stage := rfl

def methyl3ChildKey (stage : LocalizedCumulativeRule45Stage)
    (frame : input.LocalizedCIPOccurrenceFrame) : Key :=
  match frame.address with
  | [0, 1, 0] => h8Key stage
  | [0, 1, 1] => h9Key stage
  | _ => h10Key stage

theorem methyl3ChildKey_h8 (stage : LocalizedCumulativeRule45Stage) :
    methyl3ChildKey stage h8Frame = h8Key stage := rfl
theorem methyl3ChildKey_h9 (stage : LocalizedCumulativeRule45Stage) :
    methyl3ChildKey stage h9Frame = h9Key stage := rfl
theorem methyl3ChildKey_h10 (stage : LocalizedCumulativeRule45Stage) :
    methyl3ChildKey stage h10Frame = h10Key stage := rfl

def methyl12ChildKey (stage : LocalizedCumulativeRule45Stage)
    (frame : input.LocalizedCIPOccurrenceFrame) : Key :=
  match frame.address with
  | [1, 0, 0] => h15Key stage
  | [1, 0, 1] => h16Key stage
  | _ => h17Key stage

theorem methyl12ChildKey_h15 (stage : LocalizedCumulativeRule45Stage) :
    methyl12ChildKey stage h15Frame = h15Key stage := rfl
theorem methyl12ChildKey_h16 (stage : LocalizedCumulativeRule45Stage) :
    methyl12ChildKey stage h16Frame = h16Key stage := rfl
theorem methyl12ChildKey_h17 (stage : LocalizedCumulativeRule45Stage) :
    methyl12ChildKey stage h17Frame = h17Key stage := rfl

def methyl13ChildKey (stage : LocalizedCumulativeRule45Stage)
    (frame : input.LocalizedCIPOccurrenceFrame) : Key :=
  match frame.address with
  | [1, 1, 0] => h18Key stage
  | [1, 1, 1] => h19Key stage
  | _ => h20Key stage

theorem methyl13ChildKey_h18 (stage : LocalizedCumulativeRule45Stage) :
    methyl13ChildKey stage h18Frame = h18Key stage := rfl
theorem methyl13ChildKey_h19 (stage : LocalizedCumulativeRule45Stage) :
    methyl13ChildKey stage h19Frame = h19Key stage := rfl
theorem methyl13ChildKey_h20 (stage : LocalizedCumulativeRule45Stage) :
    methyl13ChildKey stage h20Frame = h20Key stage := rfl

def branchAChildKey (stage : LocalizedCumulativeRule45Stage)
    (frame : input.LocalizedCIPOccurrenceFrame) : Key :=
  match frame.address with
  | [0, 0] => methyl2Key stage
  | [0, 1] => methyl3Key stage
  | _ => h4Key stage

theorem branchAChildKey_methyl2 (stage : LocalizedCumulativeRule45Stage) :
    branchAChildKey stage methyl2Frame = methyl2Key stage := rfl
theorem branchAChildKey_methyl3 (stage : LocalizedCumulativeRule45Stage) :
    branchAChildKey stage methyl3Frame = methyl3Key stage := rfl
theorem branchAChildKey_h4 (stage : LocalizedCumulativeRule45Stage) :
    branchAChildKey stage h4Frame = h4Key stage := rfl

def branchBChildKey (stage : LocalizedCumulativeRule45Stage)
    (frame : input.LocalizedCIPOccurrenceFrame) : Key :=
  match frame.address with
  | [1, 0] => methyl12Key stage
  | [1, 1] => methyl13Key stage
  | _ => h14Key stage

theorem branchBChildKey_methyl12 (stage : LocalizedCumulativeRule45Stage) :
    branchBChildKey stage methyl12Frame = methyl12Key stage := rfl
theorem branchBChildKey_methyl13 (stage : LocalizedCumulativeRule45Stage) :
    branchBChildKey stage methyl13Frame = methyl13Key stage := rfl
theorem branchBChildKey_h14 (stage : LocalizedCumulativeRule45Stage) :
    branchBChildKey stage h14Frame = h14Key stage := rfl

theorem intended_perm_methyl2 :
    (input.intendedLocalizedRerootChildFrames methyl2Cursor).Perm
      [h5Frame, h6Frame, h7Frame] := by
  refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
  · exact input.intendedLocalizedRerootChildFrames_nodup methyl2Cursor
  · decide +kernel
  · intro g
    rw [mem_intended_methyl2Cursor_iff g]
    simp [List.mem_cons]

theorem intended_perm_methyl3 :
    (input.intendedLocalizedRerootChildFrames methyl3Cursor).Perm
      [h8Frame, h9Frame, h10Frame] := by
  refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
  · exact input.intendedLocalizedRerootChildFrames_nodup methyl3Cursor
  · decide +kernel
  · intro g
    rw [mem_intended_methyl3Cursor_iff g]
    simp [List.mem_cons]

theorem intended_perm_methyl12 :
    (input.intendedLocalizedRerootChildFrames methyl12Cursor).Perm
      [h15Frame, h16Frame, h17Frame] := by
  refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
  · exact input.intendedLocalizedRerootChildFrames_nodup methyl12Cursor
  · decide +kernel
  · intro g
    rw [mem_intended_methyl12Cursor_iff g]
    simp [List.mem_cons]

theorem intended_perm_methyl13 :
    (input.intendedLocalizedRerootChildFrames methyl13Cursor).Perm
      [h18Frame, h19Frame, h20Frame] := by
  refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
  · exact input.intendedLocalizedRerootChildFrames_nodup methyl13Cursor
  · decide +kernel
  · intro g
    rw [mem_intended_methyl13Cursor_iff g]
    simp [List.mem_cons]

theorem intended_perm_branchA :
    (input.intendedLocalizedRerootChildFrames branchACursor).Perm
      [methyl2Frame, methyl3Frame, h4Frame] := by
  refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
  · exact input.intendedLocalizedRerootChildFrames_nodup branchACursor
  · decide +kernel
  · intro g
    rw [mem_intended_branchACursor_iff g]
    simp [List.mem_cons]

theorem intended_perm_branchB :
    (input.intendedLocalizedRerootChildFrames branchBCursor).Perm
      [methyl12Frame, methyl13Frame, h14Frame] := by
  refine (List.perm_ext_iff_of_nodup ?_ ?_).mpr ?_
  · exact input.intendedLocalizedRerootChildFrames_nodup branchBCursor
  · decide +kernel
  · intro g
    rw [mem_intended_branchBCursor_iff g]
    simp [List.mem_cons]

theorem childKeysPerm_methyl2 (stage : LocalizedCumulativeRule45Stage) :
    ((input.executableLocalizedRerootChildren methyl2Cursor).map
      (fun child => methyl2ChildKey stage child.occurrence.1)).Perm
      [h5Key stage, h6Key stage, h7Key stage] := by
  have hmap :
      (input.executableLocalizedRerootChildren methyl2Cursor).map
          (fun child => methyl2ChildKey stage child.occurrence.1) =
        (input.intendedLocalizedRerootChildFrames methyl2Cursor).map
          (methyl2ChildKey stage) := by
    change ((input.executableLocalizedRerootChildren methyl2Cursor).map
        ((methyl2ChildKey stage) ∘ (fun child => child.occurrence.1))) =
      (input.intendedLocalizedRerootChildFrames methyl2Cursor).map (methyl2ChildKey stage)
    rw [← List.map_map, input.executableLocalizedRerootChildren_map methyl2Cursor]
  rw [hmap]
  have mapped := intended_perm_methyl2.map (methyl2ChildKey stage)
  simpa [methyl2ChildKey_h5, methyl2ChildKey_h6, methyl2ChildKey_h7] using mapped

theorem childKeysPerm_methyl3 (stage : LocalizedCumulativeRule45Stage) :
    ((input.executableLocalizedRerootChildren methyl3Cursor).map
      (fun child => methyl3ChildKey stage child.occurrence.1)).Perm
      [h8Key stage, h9Key stage, h10Key stage] := by
  have hmap :
      (input.executableLocalizedRerootChildren methyl3Cursor).map
          (fun child => methyl3ChildKey stage child.occurrence.1) =
        (input.intendedLocalizedRerootChildFrames methyl3Cursor).map
          (methyl3ChildKey stage) := by
    change ((input.executableLocalizedRerootChildren methyl3Cursor).map
        ((methyl3ChildKey stage) ∘ (fun child => child.occurrence.1))) =
      (input.intendedLocalizedRerootChildFrames methyl3Cursor).map (methyl3ChildKey stage)
    rw [← List.map_map, input.executableLocalizedRerootChildren_map methyl3Cursor]
  rw [hmap]
  have mapped := intended_perm_methyl3.map (methyl3ChildKey stage)
  simpa [methyl3ChildKey_h8, methyl3ChildKey_h9, methyl3ChildKey_h10] using mapped

theorem childKeysPerm_methyl12 (stage : LocalizedCumulativeRule45Stage) :
    ((input.executableLocalizedRerootChildren methyl12Cursor).map
      (fun child => methyl12ChildKey stage child.occurrence.1)).Perm
      [h15Key stage, h16Key stage, h17Key stage] := by
  have hmap :
      (input.executableLocalizedRerootChildren methyl12Cursor).map
          (fun child => methyl12ChildKey stage child.occurrence.1) =
        (input.intendedLocalizedRerootChildFrames methyl12Cursor).map
          (methyl12ChildKey stage) := by
    change ((input.executableLocalizedRerootChildren methyl12Cursor).map
        ((methyl12ChildKey stage) ∘ (fun child => child.occurrence.1))) =
      (input.intendedLocalizedRerootChildFrames methyl12Cursor).map (methyl12ChildKey stage)
    rw [← List.map_map, input.executableLocalizedRerootChildren_map methyl12Cursor]
  rw [hmap]
  have mapped := intended_perm_methyl12.map (methyl12ChildKey stage)
  simpa [methyl12ChildKey_h15, methyl12ChildKey_h16, methyl12ChildKey_h17] using mapped

theorem childKeysPerm_methyl13 (stage : LocalizedCumulativeRule45Stage) :
    ((input.executableLocalizedRerootChildren methyl13Cursor).map
      (fun child => methyl13ChildKey stage child.occurrence.1)).Perm
      [h18Key stage, h19Key stage, h20Key stage] := by
  have hmap :
      (input.executableLocalizedRerootChildren methyl13Cursor).map
          (fun child => methyl13ChildKey stage child.occurrence.1) =
        (input.intendedLocalizedRerootChildFrames methyl13Cursor).map
          (methyl13ChildKey stage) := by
    change ((input.executableLocalizedRerootChildren methyl13Cursor).map
        ((methyl13ChildKey stage) ∘ (fun child => child.occurrence.1))) =
      (input.intendedLocalizedRerootChildFrames methyl13Cursor).map (methyl13ChildKey stage)
    rw [← List.map_map, input.executableLocalizedRerootChildren_map methyl13Cursor]
  rw [hmap]
  have mapped := intended_perm_methyl13.map (methyl13ChildKey stage)
  simpa [methyl13ChildKey_h18, methyl13ChildKey_h19, methyl13ChildKey_h20] using mapped

theorem childKeysPerm_branchA (stage : LocalizedCumulativeRule45Stage) :
    ((input.executableLocalizedRerootChildren branchACursor).map
      (fun child => branchAChildKey stage child.occurrence.1)).Perm
      [methyl2Key stage, methyl3Key stage, h4Key stage] := by
  have hmap :
      (input.executableLocalizedRerootChildren branchACursor).map
          (fun child => branchAChildKey stage child.occurrence.1) =
        (input.intendedLocalizedRerootChildFrames branchACursor).map
          (branchAChildKey stage) := by
    change ((input.executableLocalizedRerootChildren branchACursor).map
        ((branchAChildKey stage) ∘ (fun child => child.occurrence.1))) =
      (input.intendedLocalizedRerootChildFrames branchACursor).map (branchAChildKey stage)
    rw [← List.map_map, input.executableLocalizedRerootChildren_map branchACursor]
  rw [hmap]
  have mapped := intended_perm_branchA.map (branchAChildKey stage)
  simpa [branchAChildKey_methyl2, branchAChildKey_methyl3, branchAChildKey_h4] using mapped

theorem childKeysPerm_branchB (stage : LocalizedCumulativeRule45Stage) :
    ((input.executableLocalizedRerootChildren branchBCursor).map
      (fun child => branchBChildKey stage child.occurrence.1)).Perm
      [methyl12Key stage, methyl13Key stage, h14Key stage] := by
  have hmap :
      (input.executableLocalizedRerootChildren branchBCursor).map
          (fun child => branchBChildKey stage child.occurrence.1) =
        (input.intendedLocalizedRerootChildFrames branchBCursor).map
          (branchBChildKey stage) := by
    change ((input.executableLocalizedRerootChildren branchBCursor).map
        ((branchBChildKey stage) ∘ (fun child => child.occurrence.1))) =
      (input.intendedLocalizedRerootChildFrames branchBCursor).map (branchBChildKey stage)
    rw [← List.map_map, input.executableLocalizedRerootChildren_map branchBCursor]
  rw [hmap]
  have mapped := intended_perm_branchB.map (branchBChildKey stage)
  simpa [branchBChildKey_methyl12, branchBChildKey_methyl13, branchBChildKey_h14] using mapped

/-! ## Pointwise derivation lists -/

/-- Pointwise derivations lift through an explicit key map on the exact cursor list. -/
theorem declarativeList_map (stage : LocalizedCumulativeRule45Stage) (fuel : Nat) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keyOf : input.LocalizedRerootCursor carrierFuel → Key),
      (∀ cursor ∈ cursors,
        input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView fuel cursor
          (keyOf cursor)) →
      input.DeclarativeLocalizedRerootCumulativeRule45KeyList stage centerOcc topView fuel cursors
        (cursors.map keyOf)
  | [], _keyOf, _pointwise => DeclarativeLocalizedRerootCumulativeRule45KeyList.nil fuel
  | cursor :: cursors, keyOf, pointwise =>
      DeclarativeLocalizedRerootCumulativeRule45KeyList.cons
        (pointwise cursor (by simp))
        (declarativeList_map stage fuel cursors keyOf
          (fun other present => pointwise other (by simp [present])))

/-! ## Child derivations of branch A -/

theorem branchAChild_declarative (stage : LocalizedCumulativeRule45Stage)
    (methyl2Decl : input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView
      (48 + 1) methyl2Cursor (methyl2Key stage))
    (methyl3Decl : input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView
      (48 + 1) methyl3Cursor (methyl3Key stage)) :
    ∀ cursor ∈ input.executableLocalizedRerootChildren branchACursor,
      input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView (48 + 1)
        cursor (branchAChildKey stage cursor.occurrence.1) := by
  intro cursor present
  have occPresent : cursor.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames branchACursor := by
    have mapped : cursor.occurrence.1 ∈
        (input.executableLocalizedRerootChildren branchACursor).map
          (fun child => child.occurrence.1) := List.mem_map_of_mem present
    rw [input.executableLocalizedRerootChildren_map branchACursor] at mapped
    exact mapped
  have previousEq :=
    input.executableLocalizedRerootChildren_previous branchACursor cursor present
  rcases (mem_intended_branchACursor_iff cursor.occurrence.1).mp occPresent with
    frameEq | frameEq | frameEq
  · have cursorEq : cursor = methyl2Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show methyl2Cursor.occurrence.1 = methyl2Frame from rfl,
      branchAChildKey_methyl2]
    exact methyl2Decl
  · have cursorEq : cursor = methyl3Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show methyl3Cursor.occurrence.1 = methyl3Frame from rfl,
      branchAChildKey_methyl3]
    exact methyl3Decl
  · have cursorEq : cursor = h4Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h4Cursor.occurrence.1 = h4Frame from rfl, branchAChildKey_h4]
    exact declarative_h4 stage (48 + 1)

theorem declarativeChildren_branchA (stage : LocalizedCumulativeRule45Stage)
    (methyl2Decl : input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView
      (48 + 1) methyl2Cursor (methyl2Key stage))
    (methyl3Decl : input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView
      (48 + 1) methyl3Cursor (methyl3Key stage)) :
    input.DeclarativeLocalizedRerootCumulativeRule45KeyList stage centerOcc topView (48 + 1)
      (input.executableLocalizedRerootChildren branchACursor)
      ((input.executableLocalizedRerootChildren branchACursor).map
        (fun cursor => branchAChildKey stage cursor.occurrence.1)) :=
  declarativeList_map stage (48 + 1) (input.executableLocalizedRerootChildren branchACursor)
    (fun cursor => branchAChildKey stage cursor.occurrence.1)
    (branchAChild_declarative stage methyl2Decl methyl3Decl)

theorem declarative_branchA (stage : LocalizedCumulativeRule45Stage)
    (methyl2Decl : input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView
      (48 + 1) methyl2Cursor (methyl2Key stage))
    (methyl3Decl : input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView
      (48 + 1) methyl3Cursor (methyl3Key stage))
    (descending : input.LocalizedRerootCumulativeRule45KeysDescending
      [methyl2Key stage, methyl3Key stage, h4Key stage]) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView (48 + 1 + 1)
      branchACursor (branchAKey stage) := by
  refine DeclarativeLocalizedRerootCumulativeRule45Key.branch
    (children := input.executableLocalizedRerootChildren branchACursor)
    (label := some (.chiral RS.R))
    (childKeys := (input.executableLocalizedRerootChildren branchACursor).map
      (fun cursor => branchAChildKey stage cursor.occurrence.1))
    (sorted := [methyl2Key stage, methyl3Key stage, h4Key stage])
    (input.executableLocalizedRerootChildren_declarative branchACursor)
    (executableCursors_ne_nil_of_intended_ne_nil branchACursor branchAChildren_nonempty)
    ((input.localizedDependencyLabel_eq_iff centerOcc topView branchACursor _).mp read_branchA)
    (declarativeChildren_branchA stage methyl2Decl methyl3Decl)
    (childKeysPerm_branchA stage).symm
    descending

/-! ## Child derivations of branch B -/

theorem branchBChild_declarative (stage : LocalizedCumulativeRule45Stage)
    (methyl12Decl : input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView
      (48 + 1) methyl12Cursor (methyl12Key stage))
    (methyl13Decl : input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView
      (48 + 1) methyl13Cursor (methyl13Key stage)) :
    ∀ cursor ∈ input.executableLocalizedRerootChildren branchBCursor,
      input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView (48 + 1)
        cursor (branchBChildKey stage cursor.occurrence.1) := by
  intro cursor present
  have occPresent : cursor.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames branchBCursor := by
    have mapped : cursor.occurrence.1 ∈
        (input.executableLocalizedRerootChildren branchBCursor).map
          (fun child => child.occurrence.1) := List.mem_map_of_mem present
    rw [input.executableLocalizedRerootChildren_map branchBCursor] at mapped
    exact mapped
  have previousEq :=
    input.executableLocalizedRerootChildren_previous branchBCursor cursor present
  rcases (mem_intended_branchBCursor_iff cursor.occurrence.1).mp occPresent with
    frameEq | frameEq | frameEq
  · have cursorEq : cursor = methyl12Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show methyl12Cursor.occurrence.1 = methyl12Frame from rfl,
      branchBChildKey_methyl12]
    exact methyl12Decl
  · have cursorEq : cursor = methyl13Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show methyl13Cursor.occurrence.1 = methyl13Frame from rfl,
      branchBChildKey_methyl13]
    exact methyl13Decl
  · have cursorEq : cursor = h14Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h14Cursor.occurrence.1 = h14Frame from rfl, branchBChildKey_h14]
    exact declarative_h14 stage (48 + 1)

theorem declarativeChildren_branchB (stage : LocalizedCumulativeRule45Stage)
    (methyl12Decl : input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView
      (48 + 1) methyl12Cursor (methyl12Key stage))
    (methyl13Decl : input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView
      (48 + 1) methyl13Cursor (methyl13Key stage)) :
    input.DeclarativeLocalizedRerootCumulativeRule45KeyList stage centerOcc topView (48 + 1)
      (input.executableLocalizedRerootChildren branchBCursor)
      ((input.executableLocalizedRerootChildren branchBCursor).map
        (fun cursor => branchBChildKey stage cursor.occurrence.1)) :=
  declarativeList_map stage (48 + 1) (input.executableLocalizedRerootChildren branchBCursor)
    (fun cursor => branchBChildKey stage cursor.occurrence.1)
    (branchBChild_declarative stage methyl12Decl methyl13Decl)

theorem declarative_branchB (stage : LocalizedCumulativeRule45Stage)
    (methyl12Decl : input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView
      (48 + 1) methyl12Cursor (methyl12Key stage))
    (methyl13Decl : input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView
      (48 + 1) methyl13Cursor (methyl13Key stage))
    (descending : input.LocalizedRerootCumulativeRule45KeysDescending
      [methyl12Key stage, methyl13Key stage, h14Key stage]) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView (48 + 1 + 1)
      branchBCursor (branchBKey stage) := by
  refine DeclarativeLocalizedRerootCumulativeRule45Key.branch
    (children := input.executableLocalizedRerootChildren branchBCursor)
    (label := some (.chiral RS.S))
    (childKeys := (input.executableLocalizedRerootChildren branchBCursor).map
      (fun cursor => branchBChildKey stage cursor.occurrence.1))
    (sorted := [methyl12Key stage, methyl13Key stage, h14Key stage])
    (input.executableLocalizedRerootChildren_declarative branchBCursor)
    (executableCursors_ne_nil_of_intended_ne_nil branchBCursor branchBChildren_nonempty)
    ((input.localizedDependencyLabel_eq_iff centerOcc topView branchBCursor _).mp read_branchB)
    (declarativeChildren_branchB stage methyl12Decl methyl13Decl)
    (childKeysPerm_branchB stage).symm
    descending

/-! ## Child derivations of the four methyl cursors -/

theorem methyl2Child_declarative (stage : LocalizedCumulativeRule45Stage) :
    ∀ cursor ∈ input.executableLocalizedRerootChildren methyl2Cursor,
      input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView 48
        cursor (methyl2ChildKey stage cursor.occurrence.1) := by
  intro cursor present
  have occPresent : cursor.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames methyl2Cursor := by
    have mapped : cursor.occurrence.1 ∈
        (input.executableLocalizedRerootChildren methyl2Cursor).map
          (fun child => child.occurrence.1) := List.mem_map_of_mem present
    rw [input.executableLocalizedRerootChildren_map methyl2Cursor] at mapped
    exact mapped
  have previousEq :=
    input.executableLocalizedRerootChildren_previous methyl2Cursor cursor present
  rcases (mem_intended_methyl2Cursor_iff cursor.occurrence.1).mp occPresent with
    frameEq | frameEq | frameEq
  · have cursorEq : cursor = h5Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h5Cursor.occurrence.1 = h5Frame from rfl, methyl2ChildKey_h5]
    exact declarative_h5 stage 48
  · have cursorEq : cursor = h6Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h6Cursor.occurrence.1 = h6Frame from rfl, methyl2ChildKey_h6]
    exact declarative_h6 stage 48
  · have cursorEq : cursor = h7Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h7Cursor.occurrence.1 = h7Frame from rfl, methyl2ChildKey_h7]
    exact declarative_h7 stage 48

theorem declarativeChildren_methyl2 (stage : LocalizedCumulativeRule45Stage) :
    input.DeclarativeLocalizedRerootCumulativeRule45KeyList stage centerOcc topView 48
      (input.executableLocalizedRerootChildren methyl2Cursor)
      ((input.executableLocalizedRerootChildren methyl2Cursor).map
        (fun cursor => methyl2ChildKey stage cursor.occurrence.1)) :=
  declarativeList_map stage 48 (input.executableLocalizedRerootChildren methyl2Cursor)
    (fun cursor => methyl2ChildKey stage cursor.occurrence.1)
    (methyl2Child_declarative stage)

theorem declarative_methyl2 (stage : LocalizedCumulativeRule45Stage)
    (descending : input.LocalizedRerootCumulativeRule45KeysDescending
      [h5Key stage, h6Key stage, h7Key stage]) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView (48 + 1)
      methyl2Cursor (methyl2Key stage) := by
  refine DeclarativeLocalizedRerootCumulativeRule45Key.branch
    (children := input.executableLocalizedRerootChildren methyl2Cursor)
    (label := some (.chiral RS.R))
    (childKeys := (input.executableLocalizedRerootChildren methyl2Cursor).map
      (fun cursor => methyl2ChildKey stage cursor.occurrence.1))
    (sorted := [h5Key stage, h6Key stage, h7Key stage])
    (input.executableLocalizedRerootChildren_declarative methyl2Cursor)
    (executableCursors_ne_nil_of_intended_ne_nil methyl2Cursor methyl2Children_nonempty)
    ((input.localizedDependencyLabel_eq_iff centerOcc topView methyl2Cursor _).mp read_methyl2)
    (declarativeChildren_methyl2 stage)
    (childKeysPerm_methyl2 stage).symm
    descending

theorem methyl3Child_declarative (stage : LocalizedCumulativeRule45Stage) :
    ∀ cursor ∈ input.executableLocalizedRerootChildren methyl3Cursor,
      input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView 48
        cursor (methyl3ChildKey stage cursor.occurrence.1) := by
  intro cursor present
  have occPresent : cursor.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames methyl3Cursor := by
    have mapped : cursor.occurrence.1 ∈
        (input.executableLocalizedRerootChildren methyl3Cursor).map
          (fun child => child.occurrence.1) := List.mem_map_of_mem present
    rw [input.executableLocalizedRerootChildren_map methyl3Cursor] at mapped
    exact mapped
  have previousEq :=
    input.executableLocalizedRerootChildren_previous methyl3Cursor cursor present
  rcases (mem_intended_methyl3Cursor_iff cursor.occurrence.1).mp occPresent with
    frameEq | frameEq | frameEq
  · have cursorEq : cursor = h8Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h8Cursor.occurrence.1 = h8Frame from rfl, methyl3ChildKey_h8]
    exact declarative_h8 stage 48
  · have cursorEq : cursor = h9Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h9Cursor.occurrence.1 = h9Frame from rfl, methyl3ChildKey_h9]
    exact declarative_h9 stage 48
  · have cursorEq : cursor = h10Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h10Cursor.occurrence.1 = h10Frame from rfl, methyl3ChildKey_h10]
    exact declarative_h10 stage 48

theorem declarativeChildren_methyl3 (stage : LocalizedCumulativeRule45Stage) :
    input.DeclarativeLocalizedRerootCumulativeRule45KeyList stage centerOcc topView 48
      (input.executableLocalizedRerootChildren methyl3Cursor)
      ((input.executableLocalizedRerootChildren methyl3Cursor).map
        (fun cursor => methyl3ChildKey stage cursor.occurrence.1)) :=
  declarativeList_map stage 48 (input.executableLocalizedRerootChildren methyl3Cursor)
    (fun cursor => methyl3ChildKey stage cursor.occurrence.1)
    (methyl3Child_declarative stage)

theorem declarative_methyl3 (stage : LocalizedCumulativeRule45Stage)
    (descending : input.LocalizedRerootCumulativeRule45KeysDescending
      [h8Key stage, h9Key stage, h10Key stage]) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView (48 + 1)
      methyl3Cursor (methyl3Key stage) := by
  refine DeclarativeLocalizedRerootCumulativeRule45Key.branch
    (children := input.executableLocalizedRerootChildren methyl3Cursor)
    (label := none)
    (childKeys := (input.executableLocalizedRerootChildren methyl3Cursor).map
      (fun cursor => methyl3ChildKey stage cursor.occurrence.1))
    (sorted := [h8Key stage, h9Key stage, h10Key stage])
    (input.executableLocalizedRerootChildren_declarative methyl3Cursor)
    (executableCursors_ne_nil_of_intended_ne_nil methyl3Cursor methyl3Children_nonempty)
    ((input.localizedDependencyLabel_eq_iff centerOcc topView methyl3Cursor _).mp read_methyl3)
    (declarativeChildren_methyl3 stage)
    (childKeysPerm_methyl3 stage).symm
    descending

theorem methyl12Child_declarative (stage : LocalizedCumulativeRule45Stage) :
    ∀ cursor ∈ input.executableLocalizedRerootChildren methyl12Cursor,
      input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView 48
        cursor (methyl12ChildKey stage cursor.occurrence.1) := by
  intro cursor present
  have occPresent : cursor.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames methyl12Cursor := by
    have mapped : cursor.occurrence.1 ∈
        (input.executableLocalizedRerootChildren methyl12Cursor).map
          (fun child => child.occurrence.1) := List.mem_map_of_mem present
    rw [input.executableLocalizedRerootChildren_map methyl12Cursor] at mapped
    exact mapped
  have previousEq :=
    input.executableLocalizedRerootChildren_previous methyl12Cursor cursor present
  rcases (mem_intended_methyl12Cursor_iff cursor.occurrence.1).mp occPresent with
    frameEq | frameEq | frameEq
  · have cursorEq : cursor = h15Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h15Cursor.occurrence.1 = h15Frame from rfl, methyl12ChildKey_h15]
    exact declarative_h15 stage 48
  · have cursorEq : cursor = h16Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h16Cursor.occurrence.1 = h16Frame from rfl, methyl12ChildKey_h16]
    exact declarative_h16 stage 48
  · have cursorEq : cursor = h17Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h17Cursor.occurrence.1 = h17Frame from rfl, methyl12ChildKey_h17]
    exact declarative_h17 stage 48

theorem declarativeChildren_methyl12 (stage : LocalizedCumulativeRule45Stage) :
    input.DeclarativeLocalizedRerootCumulativeRule45KeyList stage centerOcc topView 48
      (input.executableLocalizedRerootChildren methyl12Cursor)
      ((input.executableLocalizedRerootChildren methyl12Cursor).map
        (fun cursor => methyl12ChildKey stage cursor.occurrence.1)) :=
  declarativeList_map stage 48 (input.executableLocalizedRerootChildren methyl12Cursor)
    (fun cursor => methyl12ChildKey stage cursor.occurrence.1)
    (methyl12Child_declarative stage)

theorem declarative_methyl12 (stage : LocalizedCumulativeRule45Stage)
    (descending : input.LocalizedRerootCumulativeRule45KeysDescending
      [h15Key stage, h16Key stage, h17Key stage]) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView (48 + 1)
      methyl12Cursor (methyl12Key stage) := by
  refine DeclarativeLocalizedRerootCumulativeRule45Key.branch
    (children := input.executableLocalizedRerootChildren methyl12Cursor)
    (label := some (.chiral RS.R))
    (childKeys := (input.executableLocalizedRerootChildren methyl12Cursor).map
      (fun cursor => methyl12ChildKey stage cursor.occurrence.1))
    (sorted := [h15Key stage, h16Key stage, h17Key stage])
    (input.executableLocalizedRerootChildren_declarative methyl12Cursor)
    (executableCursors_ne_nil_of_intended_ne_nil methyl12Cursor methyl12Children_nonempty)
    ((input.localizedDependencyLabel_eq_iff centerOcc topView methyl12Cursor _).mp read_methyl12)
    (declarativeChildren_methyl12 stage)
    (childKeysPerm_methyl12 stage).symm
    descending

theorem methyl13Child_declarative (stage : LocalizedCumulativeRule45Stage) :
    ∀ cursor ∈ input.executableLocalizedRerootChildren methyl13Cursor,
      input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView 48
        cursor (methyl13ChildKey stage cursor.occurrence.1) := by
  intro cursor present
  have occPresent : cursor.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames methyl13Cursor := by
    have mapped : cursor.occurrence.1 ∈
        (input.executableLocalizedRerootChildren methyl13Cursor).map
          (fun child => child.occurrence.1) := List.mem_map_of_mem present
    rw [input.executableLocalizedRerootChildren_map methyl13Cursor] at mapped
    exact mapped
  have previousEq :=
    input.executableLocalizedRerootChildren_previous methyl13Cursor cursor present
  rcases (mem_intended_methyl13Cursor_iff cursor.occurrence.1).mp occPresent with
    frameEq | frameEq | frameEq
  · have cursorEq : cursor = h18Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h18Cursor.occurrence.1 = h18Frame from rfl, methyl13ChildKey_h18]
    exact declarative_h18 stage 48
  · have cursorEq : cursor = h19Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h19Cursor.occurrence.1 = h19Frame from rfl, methyl13ChildKey_h19]
    exact declarative_h19 stage 48
  · have cursorEq : cursor = h20Cursor := by
      apply LocalizedRerootCursor.ext input
      · exact Subtype.ext frameEq
      · exact previousEq
    rw [cursorEq, show h20Cursor.occurrence.1 = h20Frame from rfl, methyl13ChildKey_h20]
    exact declarative_h20 stage 48

theorem declarativeChildren_methyl13 (stage : LocalizedCumulativeRule45Stage) :
    input.DeclarativeLocalizedRerootCumulativeRule45KeyList stage centerOcc topView 48
      (input.executableLocalizedRerootChildren methyl13Cursor)
      ((input.executableLocalizedRerootChildren methyl13Cursor).map
        (fun cursor => methyl13ChildKey stage cursor.occurrence.1)) :=
  declarativeList_map stage 48 (input.executableLocalizedRerootChildren methyl13Cursor)
    (fun cursor => methyl13ChildKey stage cursor.occurrence.1)
    (methyl13Child_declarative stage)

theorem declarative_methyl13 (stage : LocalizedCumulativeRule45Stage)
    (descending : input.LocalizedRerootCumulativeRule45KeysDescending
      [h18Key stage, h19Key stage, h20Key stage]) :
    input.DeclarativeLocalizedRerootCumulativeRule45Key stage centerOcc topView (48 + 1)
      methyl13Cursor (methyl13Key stage) := by
  refine DeclarativeLocalizedRerootCumulativeRule45Key.branch
    (children := input.executableLocalizedRerootChildren methyl13Cursor)
    (label := some (.chiral RS.R))
    (childKeys := (input.executableLocalizedRerootChildren methyl13Cursor).map
      (fun cursor => methyl13ChildKey stage cursor.occurrence.1))
    (sorted := [h18Key stage, h19Key stage, h20Key stage])
    (input.executableLocalizedRerootChildren_declarative methyl13Cursor)
    (executableCursors_ne_nil_of_intended_ne_nil methyl13Cursor methyl13Children_nonempty)
    ((input.localizedDependencyLabel_eq_iff centerOcc topView methyl13Cursor _).mp read_methyl13)
    (declarativeChildren_methyl13 stage)
    (childKeysPerm_methyl13 stage).symm
    descending

/-! ## Concrete stage instantiations

The reversal is witnessed at the two stages whose order it separates: the earlier Rule-4a stage and
the later Rule-4b stage at reference `R`.  Every descending premise below is a closed proposition
about the actual official keys, so each is discharged in the kernel by computation. -/

/-- The later stage compared by the witness: Rule 4b at reference `R`. -/
abbrev rule4bR : LocalizedCumulativeRule45Stage := .rule4b RS.R

theorem descending_methyl2_rule4a :
    input.LocalizedRerootCumulativeRule45KeysDescending
      [h5Key .rule4a, h6Key .rule4a, h7Key .rule4a] := by
  unfold CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45KeysDescending
  decide +kernel

theorem descending_methyl3_rule4a :
    input.LocalizedRerootCumulativeRule45KeysDescending
      [h8Key .rule4a, h9Key .rule4a, h10Key .rule4a] := by
  unfold CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45KeysDescending
  decide +kernel

theorem descending_methyl12_rule4a :
    input.LocalizedRerootCumulativeRule45KeysDescending
      [h15Key .rule4a, h16Key .rule4a, h17Key .rule4a] := by
  unfold CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45KeysDescending
  decide +kernel

theorem descending_methyl13_rule4a :
    input.LocalizedRerootCumulativeRule45KeysDescending
      [h18Key .rule4a, h19Key .rule4a, h20Key .rule4a] := by
  unfold CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45KeysDescending
  decide +kernel

theorem descending_branchA_rule4a :
    input.LocalizedRerootCumulativeRule45KeysDescending
      [methyl2Key .rule4a, methyl3Key .rule4a, h4Key .rule4a] := by
  unfold CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45KeysDescending
  decide +kernel

theorem descending_branchB_rule4a :
    input.LocalizedRerootCumulativeRule45KeysDescending
      [methyl12Key .rule4a, methyl13Key .rule4a, h14Key .rule4a] := by
  unfold CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45KeysDescending
  decide +kernel

theorem descending_methyl2_rule4bR :
    input.LocalizedRerootCumulativeRule45KeysDescending
      [h5Key rule4bR, h6Key rule4bR, h7Key rule4bR] := by
  unfold CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45KeysDescending
  decide +kernel

theorem descending_methyl3_rule4bR :
    input.LocalizedRerootCumulativeRule45KeysDescending
      [h8Key rule4bR, h9Key rule4bR, h10Key rule4bR] := by
  unfold CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45KeysDescending
  decide +kernel

theorem descending_methyl12_rule4bR :
    input.LocalizedRerootCumulativeRule45KeysDescending
      [h15Key rule4bR, h16Key rule4bR, h17Key rule4bR] := by
  unfold CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45KeysDescending
  decide +kernel

theorem descending_methyl13_rule4bR :
    input.LocalizedRerootCumulativeRule45KeysDescending
      [h18Key rule4bR, h19Key rule4bR, h20Key rule4bR] := by
  unfold CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45KeysDescending
  decide +kernel

theorem descending_branchA_rule4bR :
    input.LocalizedRerootCumulativeRule45KeysDescending
      [methyl2Key rule4bR, methyl3Key rule4bR, h4Key rule4bR] := by
  unfold CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45KeysDescending
  decide +kernel

theorem descending_branchB_rule4bR :
    input.LocalizedRerootCumulativeRule45KeysDescending
      [methyl12Key rule4bR, methyl13Key rule4bR, h14Key rule4bR] := by
  unfold CertifiedLocalizedCIPInput.LocalizedRerootCumulativeRule45KeysDescending
  decide +kernel

/-! ### Derivations at the earlier Rule-4a stage -/

theorem declarative_methyl2_rule4a :
    input.DeclarativeLocalizedRerootCumulativeRule45Key .rule4a centerOcc topView (48 + 1)
      methyl2Cursor (methyl2Key .rule4a) :=
  declarative_methyl2 .rule4a descending_methyl2_rule4a

theorem declarative_methyl3_rule4a :
    input.DeclarativeLocalizedRerootCumulativeRule45Key .rule4a centerOcc topView (48 + 1)
      methyl3Cursor (methyl3Key .rule4a) :=
  declarative_methyl3 .rule4a descending_methyl3_rule4a

theorem declarative_methyl12_rule4a :
    input.DeclarativeLocalizedRerootCumulativeRule45Key .rule4a centerOcc topView (48 + 1)
      methyl12Cursor (methyl12Key .rule4a) :=
  declarative_methyl12 .rule4a descending_methyl12_rule4a

theorem declarative_methyl13_rule4a :
    input.DeclarativeLocalizedRerootCumulativeRule45Key .rule4a centerOcc topView (48 + 1)
      methyl13Cursor (methyl13Key .rule4a) :=
  declarative_methyl13 .rule4a descending_methyl13_rule4a

theorem declarative_branchA_rule4a :
    input.DeclarativeLocalizedRerootCumulativeRule45Key .rule4a centerOcc topView (48 + 1 + 1)
      branchACursor (branchAKey .rule4a) :=
  declarative_branchA .rule4a declarative_methyl2_rule4a declarative_methyl3_rule4a
    descending_branchA_rule4a

theorem declarative_branchB_rule4a :
    input.DeclarativeLocalizedRerootCumulativeRule45Key .rule4a centerOcc topView (48 + 1 + 1)
      branchBCursor (branchBKey .rule4a) :=
  declarative_branchB .rule4a declarative_methyl12_rule4a declarative_methyl13_rule4a
    descending_branchB_rule4a

/-! ### Derivations at the later Rule-4b (`R`) stage -/

theorem declarative_methyl2_rule4bR :
    input.DeclarativeLocalizedRerootCumulativeRule45Key rule4bR centerOcc topView (48 + 1)
      methyl2Cursor (methyl2Key rule4bR) :=
  declarative_methyl2 rule4bR descending_methyl2_rule4bR

theorem declarative_methyl3_rule4bR :
    input.DeclarativeLocalizedRerootCumulativeRule45Key rule4bR centerOcc topView (48 + 1)
      methyl3Cursor (methyl3Key rule4bR) :=
  declarative_methyl3 rule4bR descending_methyl3_rule4bR

theorem declarative_methyl12_rule4bR :
    input.DeclarativeLocalizedRerootCumulativeRule45Key rule4bR centerOcc topView (48 + 1)
      methyl12Cursor (methyl12Key rule4bR) :=
  declarative_methyl12 rule4bR descending_methyl12_rule4bR

theorem declarative_methyl13_rule4bR :
    input.DeclarativeLocalizedRerootCumulativeRule45Key rule4bR centerOcc topView (48 + 1)
      methyl13Cursor (methyl13Key rule4bR) :=
  declarative_methyl13 rule4bR descending_methyl13_rule4bR

theorem declarative_branchA_rule4bR :
    input.DeclarativeLocalizedRerootCumulativeRule45Key rule4bR centerOcc topView (48 + 1 + 1)
      branchACursor (branchAKey rule4bR) :=
  declarative_branchA rule4bR declarative_methyl2_rule4bR declarative_methyl3_rule4bR
    descending_branchA_rule4bR

theorem declarative_branchB_rule4bR :
    input.DeclarativeLocalizedRerootCumulativeRule45Key rule4bR centerOcc topView (48 + 1 + 1)
      branchBCursor (branchBKey rule4bR) :=
  declarative_branchB rule4bR declarative_methyl12_rule4bR declarative_methyl13_rule4bR
    descending_branchB_rule4bR

/-! ## The actual positive atomic numbers

The witness keeps the actual periodic-table atomic numbers of the certified input: both ligand
roots and the centre are carbon.  These are the atomic numbers that `officialRuleMajorRootKey`
projects into the constitutional Rule-1a layers of every key below. -/

theorem atomZ_actual :
    input.moleculeGraph.atomZ a0 = 6 ∧
      input.moleculeGraph.atomZ a1 = 6 ∧ input.moleculeGraph.atomZ a11 = 6 := by
  decide +kernel

/-! ## The four actual stage builds

Each build below is the production reader build of the actual ligand-root cursor, paired with the
official declarative builder at the same fuel for the branch cursor.  Both equations hold for the
*same* key. -/

/-- The actual build fuel shared by all four stage builds: `2 * (atomCount + 1 + 1) = 50`. -/
abbrev buildFuel : Nat := 2 * (input.certified.input.molecule.atomCount + 1 + 1)

/-- The production reader reads `R` at the actual branch-A ligand root. -/
theorem molecularReader_branchA :
    input.molecularReader fixtureMap centerOcc branchACursor = some (.chiral RS.R) := by
  change input.localizedDependencyLabel centerOcc topView branchACursor = some (.chiral RS.R)
  exact read_branchA

/-- The production reader reads `S` at the actual branch-B ligand root. -/
theorem molecularReader_branchB :
    input.molecularReader fixtureMap centerOcc branchBCursor = some (.chiral RS.S) := by
  change input.localizedDependencyLabel centerOcc topView branchBCursor = some (.chiral RS.S)
  exact read_branchB

theorem branchA_build_rule4a :
    ∃ key : Key,
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
          (input.molecularReader fixtureMap centerOcc) buildFuel
          (input.localizedLigandRootCursor center 0) = some key ∧
      input.buildLocalizedRerootCumulativeRule45Key? .rule4a centerOcc topView buildFuel
          branchACursor = some key := by
  obtain ⟨key, built, _⟩ :=
    input.molecularReader_ligandRoot_build fixtureMap centerOcc center 0 .rule4a
  refine ⟨key, built, ?_⟩
  rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
    .rule4a centerOcc topView buildFuel branchACursor]
  rw [branchACursor_eq_ligandRoot]
  exact built

theorem branchB_build_rule4a :
    ∃ key : Key,
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
          (input.molecularReader fixtureMap centerOcc) buildFuel
          (input.localizedLigandRootCursor center 1) = some key ∧
      input.buildLocalizedRerootCumulativeRule45Key? .rule4a centerOcc topView buildFuel
          branchBCursor = some key := by
  obtain ⟨key, built, _⟩ :=
    input.molecularReader_ligandRoot_build fixtureMap centerOcc center 1 .rule4a
  refine ⟨key, built, ?_⟩
  rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
    .rule4a centerOcc topView buildFuel branchBCursor]
  rw [branchBCursor_eq_ligandRoot]
  exact built

theorem branchA_build_rule4bR :
    ∃ key : Key,
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? rule4bR
          (input.molecularReader fixtureMap centerOcc) buildFuel
          (input.localizedLigandRootCursor center 0) = some key ∧
      input.buildLocalizedRerootCumulativeRule45Key? rule4bR centerOcc topView buildFuel
          branchACursor = some key := by
  obtain ⟨key, built, _⟩ :=
    input.molecularReader_ligandRoot_build fixtureMap centerOcc center 0 rule4bR
  refine ⟨key, built, ?_⟩
  rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
    rule4bR centerOcc topView buildFuel branchACursor]
  rw [branchACursor_eq_ligandRoot]
  exact built

theorem branchB_build_rule4bR :
    ∃ key : Key,
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? rule4bR
          (input.molecularReader fixtureMap centerOcc) buildFuel
          (input.localizedLigandRootCursor center 1) = some key ∧
      input.buildLocalizedRerootCumulativeRule45Key? rule4bR centerOcc topView buildFuel
          branchBCursor = some key := by
  obtain ⟨key, built, _⟩ :=
    input.molecularReader_ligandRoot_build fixtureMap centerOcc center 1 rule4bR
  refine ⟨key, built, ?_⟩
  rw [← input.buildLocalizedRerootCumulativeRule45KeyWithRead?_eq_localizedDependencyLabel
    rule4bR centerOcc topView buildFuel branchBCursor]
  rw [branchBCursor_eq_ligandRoot]
  exact built

/-! ## Comparisons and constitutional ties at the two stages -/

/-- The closed reference comparison at the earlier Rule-4a stage is `lt`. -/
theorem compare_derived_rule4a :
    input.compareLocalizedRerootCumulativeRule45Keys (branchAKey .rule4a) (branchBKey .rule4a) =
      Ordering.lt := by
  rw [input.compareLocalizedRerootCumulativeRule45Keys_eq_compareObservable]
  decide +kernel

/-- The closed reference comparison at the later Rule-4b (`R`) stage is `gt`. -/
theorem compare_derived_rule4bR :
    input.compareLocalizedRerootCumulativeRule45Keys (branchAKey rule4bR) (branchBKey rule4bR) =
      Ordering.gt := by
  rw [input.compareLocalizedRerootCumulativeRule45Keys_eq_compareObservable]
  decide +kernel

/-- The constitutional projections of the two Rule-4a reference keys tie exactly. -/
theorem constitutional_tie_derived_rule4a :
    OfficialRuleMajorKey.compare (branchAKey .rule4a).constitutional
      (branchBKey .rule4a).constitutional = Ordering.eq := by
  rw [officialRuleMajorKey_compare_eq_iff]
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- The constitutional projections of the two Rule-4b (`R`) reference keys tie exactly. -/
theorem constitutional_tie_derived_rule4bR :
    OfficialRuleMajorKey.compare (branchAKey rule4bR).constitutional
      (branchBKey rule4bR).constitutional = Ordering.eq := by
  rw [officialRuleMajorKey_compare_eq_iff]
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel

/-- Every compiled Rule-4a key compares exactly as its derived reference key. -/
theorem compare_rule4a {keyA keyB : Key}
    (builtA : input.buildLocalizedRerootCumulativeRule45Key? .rule4a centerOcc topView buildFuel
      branchACursor = some keyA)
    (builtB : input.buildLocalizedRerootCumulativeRule45Key? .rule4a centerOcc topView buildFuel
      branchBCursor = some keyB) :
    input.compareLocalizedRerootCumulativeRule45Keys keyA keyB = Ordering.lt := by
  have hA := input.compiled_cumulative_key_observable_eq_derived .rule4a centerOcc topView buildFuel
    branchACursor keyA (branchAKey .rule4a) builtA declarative_branchA_rule4a
  have hB := input.compiled_cumulative_key_observable_eq_derived .rule4a centerOcc topView buildFuel
    branchBCursor keyB (branchBKey .rule4a) builtB declarative_branchB_rule4a
  rw [input.compareLocalizedRerootCumulativeRule45Keys_eq_compareObservable, hA, hB]
  decide +kernel

/-- Every compiled Rule-4b (`R`) key compares exactly as its derived reference key. -/
theorem compare_rule4bR {keyA keyB : Key}
    (builtA : input.buildLocalizedRerootCumulativeRule45Key? rule4bR centerOcc topView buildFuel
      branchACursor = some keyA)
    (builtB : input.buildLocalizedRerootCumulativeRule45Key? rule4bR centerOcc topView buildFuel
      branchBCursor = some keyB) :
    input.compareLocalizedRerootCumulativeRule45Keys keyA keyB = Ordering.gt := by
  have hA := input.compiled_cumulative_key_observable_eq_derived rule4bR centerOcc topView buildFuel
    branchACursor keyA (branchAKey rule4bR) builtA declarative_branchA_rule4bR
  have hB := input.compiled_cumulative_key_observable_eq_derived rule4bR centerOcc topView buildFuel
    branchBCursor keyB (branchBKey rule4bR) builtB declarative_branchB_rule4bR
  rw [input.compareLocalizedRerootCumulativeRule45Keys_eq_compareObservable, hA, hB]
  decide +kernel

/-- The compiled Rule-4a keys tie constitutionally: the official assembly is what decides the
comparison, and it is a tie at Rules 1a/1b/2. -/
theorem constitutional_tie_rule4a {keyA keyB : Key}
    (builtA : input.buildLocalizedRerootCumulativeRule45Key? .rule4a centerOcc topView buildFuel
      branchACursor = some keyA)
    (builtB : input.buildLocalizedRerootCumulativeRule45Key? .rule4a centerOcc topView buildFuel
      branchBCursor = some keyB) :
    OfficialRuleMajorKey.compare keyA.constitutional keyB.constitutional = Ordering.eq := by
  have hA := input.compiled_cumulative_key_observable_eq_derived .rule4a centerOcc topView buildFuel
    branchACursor keyA (branchAKey .rule4a) builtA declarative_branchA_rule4a
  have hB := input.compiled_cumulative_key_observable_eq_derived .rule4a centerOcc topView buildFuel
    branchBCursor keyB (branchBKey .rule4a) builtB declarative_branchB_rule4a
  have hA1a : keyA.constitutional.rule1a = (branchAKey .rule4a).constitutional.rule1a := by
    simpa using congrArg LocalizedCumulativeRule45Observable.rule1a hA
  have hB1a : keyB.constitutional.rule1a = (branchBKey .rule4a).constitutional.rule1a := by
    simpa using congrArg LocalizedCumulativeRule45Observable.rule1a hB
  have hA1b : keyA.constitutional.rule1b = (branchAKey .rule4a).constitutional.rule1b := by
    simpa using congrArg LocalizedCumulativeRule45Observable.rule1b hA
  have hB1b : keyB.constitutional.rule1b = (branchBKey .rule4a).constitutional.rule1b := by
    simpa using congrArg LocalizedCumulativeRule45Observable.rule1b hB
  have hA2 : keyA.constitutional.rule2 = (branchAKey .rule4a).constitutional.rule2 := by
    simpa using congrArg LocalizedCumulativeRule45Observable.rule2 hA
  have hB2 : keyB.constitutional.rule2 = (branchBKey .rule4a).constitutional.rule2 := by
    simpa using congrArg LocalizedCumulativeRule45Observable.rule2 hB
  have derived := (officialRuleMajorKey_compare_eq_iff _ _).mp constitutional_tie_derived_rule4a
  exact (officialRuleMajorKey_compare_eq_iff _ _).mpr
    ⟨hA1a.trans (derived.1.trans hB1a.symm),
      hA1b.trans (derived.2.1.trans hB1b.symm),
      hA2.trans (derived.2.2.trans hB2.symm)⟩

/-- The compiled Rule-4b (`R`) keys tie constitutionally as well. -/
theorem constitutional_tie_rule4bR {keyA keyB : Key}
    (builtA : input.buildLocalizedRerootCumulativeRule45Key? rule4bR centerOcc topView buildFuel
      branchACursor = some keyA)
    (builtB : input.buildLocalizedRerootCumulativeRule45Key? rule4bR centerOcc topView buildFuel
      branchBCursor = some keyB) :
    OfficialRuleMajorKey.compare keyA.constitutional keyB.constitutional = Ordering.eq := by
  have hA := input.compiled_cumulative_key_observable_eq_derived rule4bR centerOcc topView buildFuel
    branchACursor keyA (branchAKey rule4bR) builtA declarative_branchA_rule4bR
  have hB := input.compiled_cumulative_key_observable_eq_derived rule4bR centerOcc topView buildFuel
    branchBCursor keyB (branchBKey rule4bR) builtB declarative_branchB_rule4bR
  have hA1a : keyA.constitutional.rule1a = (branchAKey rule4bR).constitutional.rule1a := by
    simpa using congrArg LocalizedCumulativeRule45Observable.rule1a hA
  have hB1a : keyB.constitutional.rule1a = (branchBKey rule4bR).constitutional.rule1a := by
    simpa using congrArg LocalizedCumulativeRule45Observable.rule1a hB
  have hA1b : keyA.constitutional.rule1b = (branchAKey rule4bR).constitutional.rule1b := by
    simpa using congrArg LocalizedCumulativeRule45Observable.rule1b hA
  have hB1b : keyB.constitutional.rule1b = (branchBKey rule4bR).constitutional.rule1b := by
    simpa using congrArg LocalizedCumulativeRule45Observable.rule1b hB
  have hA2 : keyA.constitutional.rule2 = (branchAKey rule4bR).constitutional.rule2 := by
    simpa using congrArg LocalizedCumulativeRule45Observable.rule2 hA
  have hB2 : keyB.constitutional.rule2 = (branchBKey rule4bR).constitutional.rule2 := by
    simpa using congrArg LocalizedCumulativeRule45Observable.rule2 hB
  have derived := (officialRuleMajorKey_compare_eq_iff _ _).mp constitutional_tie_derived_rule4bR
  exact (officialRuleMajorKey_compare_eq_iff _ _).mpr
    ⟨hA1a.trans (derived.1.trans hB1a.symm),
      hA1b.trans (derived.2.1.trans hB1b.symm),
      hA2.trans (derived.2.2.trans hB2.symm)⟩

/-! ## The two stage witnesses -/

/-- The actual Rule-4a stage witness: both production ligand-root builds succeed, the official
builder agrees on the same keys, the comparison is strict ascending, and the constitutional
projection ties. -/
theorem stage_builds_rule4a :
    ∃ keyA keyB : Key,
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
          (input.molecularReader fixtureMap centerOcc) buildFuel
          (input.localizedLigandRootCursor center 0) = some keyA ∧
        input.buildLocalizedRerootCumulativeRule45Key? .rule4a centerOcc topView buildFuel
          branchACursor = some keyA) ∧
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
          (input.molecularReader fixtureMap centerOcc) buildFuel
          (input.localizedLigandRootCursor center 1) = some keyB ∧
        input.buildLocalizedRerootCumulativeRule45Key? .rule4a centerOcc topView buildFuel
          branchBCursor = some keyB) ∧
      input.compareLocalizedRerootCumulativeRule45Keys keyA keyB = Ordering.lt ∧
      OfficialRuleMajorKey.compare keyA.constitutional keyB.constitutional = Ordering.eq := by
  obtain ⟨keyA, readerA, builtA⟩ := branchA_build_rule4a
  obtain ⟨keyB, readerB, builtB⟩ := branchB_build_rule4a
  exact ⟨keyA, keyB, ⟨readerA, builtA⟩, ⟨readerB, builtB⟩, compare_rule4a builtA builtB,
    constitutional_tie_rule4a builtA builtB⟩

/-- The actual later Rule-4b (`R`) stage witness: the same two ligand-root builds compare strictly
descending, so the earlier ascending order is reversed, while the constitutional projection still
ties. -/
theorem stage_builds_rule4bR :
    ∃ keyA keyB : Key,
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead? rule4bR
          (input.molecularReader fixtureMap centerOcc) buildFuel
          (input.localizedLigandRootCursor center 0) = some keyA ∧
        input.buildLocalizedRerootCumulativeRule45Key? rule4bR centerOcc topView buildFuel
          branchACursor = some keyA) ∧
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead? rule4bR
          (input.molecularReader fixtureMap centerOcc) buildFuel
          (input.localizedLigandRootCursor center 1) = some keyB ∧
        input.buildLocalizedRerootCumulativeRule45Key? rule4bR centerOcc topView buildFuel
          branchBCursor = some keyB) ∧
      input.compareLocalizedRerootCumulativeRule45Keys keyA keyB = Ordering.gt ∧
      OfficialRuleMajorKey.compare keyA.constitutional keyB.constitutional = Ordering.eq := by
  obtain ⟨keyA, readerA, builtA⟩ := branchA_build_rule4bR
  obtain ⟨keyB, readerB, builtB⟩ := branchB_build_rule4bR
  exact ⟨keyA, keyB, ⟨readerA, builtA⟩, ⟨readerB, builtB⟩, compare_rule4bR builtA builtB,
    constitutional_tie_rule4bR builtA builtB⟩

/-! ## Final export -/

/-- **Actual supplied-map stage rank reversal.**

On the single actual certified 23-atom input of the frozen witness, at the same centre-`0` top
target and dependency context, with the same supplied descriptor map and its production reader,
the two canonical ligand cursors of slots `0` and `1` build successfully at all four actual stage
instances, tie exactly under the official constitutional assembly at Rules 1a/1b/2, and yet
compare strictly ascending at `rule4a` and strictly descending at `rule4b R`.

The keys are the actual official keys: `officialRuleMajorRootKey` over the actual positive atomic
numbers (`atomZ_actual`), `OfficialRuleMajorKey.assemble`, and the actual descriptor merges.  No
uniform or empty key is substituted.  The supplied map is supplied data, not a physically generated
reference state. -/
theorem actual_stage_rank_reversal :
    input.certified.input.molecule.atomCount = 23 ∧
      center.1 = a0 ∧
      (input.tetrahedralCenterSet : Finset Atom) = {a0, a1, a2, a3, a11, a12, a13} ∧
      centerOcc.1.root = a0 ∧
      centerOcc.1.address = [] ∧
      topView = input.molecularView fixtureMap centerOcc ∧
      branchACursor = input.localizedLigandRootCursor center 0 ∧
      branchBCursor = input.localizedLigandRootCursor center 1 ∧
      input.molecularReader fixtureMap centerOcc branchACursor = some (.chiral RS.R) ∧
      input.molecularReader fixtureMap centerOcc branchBCursor = some (.chiral RS.S) ∧
      (∃ keyA keyB : Key,
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
            (input.molecularReader fixtureMap centerOcc) buildFuel
            (input.localizedLigandRootCursor center 0) = some keyA ∧
          input.buildLocalizedRerootCumulativeRule45Key? .rule4a centerOcc topView buildFuel
            branchACursor = some keyA) ∧
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a
            (input.molecularReader fixtureMap centerOcc) buildFuel
            (input.localizedLigandRootCursor center 1) = some keyB ∧
          input.buildLocalizedRerootCumulativeRule45Key? .rule4a centerOcc topView buildFuel
            branchBCursor = some keyB) ∧
        input.compareLocalizedRerootCumulativeRule45Keys keyA keyB = Ordering.lt ∧
        OfficialRuleMajorKey.compare keyA.constitutional keyB.constitutional = Ordering.eq) ∧
      (∃ keyA keyB : Key,
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead? rule4bR
            (input.molecularReader fixtureMap centerOcc) buildFuel
            (input.localizedLigandRootCursor center 0) = some keyA ∧
          input.buildLocalizedRerootCumulativeRule45Key? rule4bR centerOcc topView buildFuel
            branchACursor = some keyA) ∧
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead? rule4bR
            (input.molecularReader fixtureMap centerOcc) buildFuel
            (input.localizedLigandRootCursor center 1) = some keyB ∧
          input.buildLocalizedRerootCumulativeRule45Key? rule4bR centerOcc topView buildFuel
            branchBCursor = some keyB) ∧
        input.compareLocalizedRerootCumulativeRule45Keys keyA keyB = Ordering.gt ∧
        OfficialRuleMajorKey.compare keyA.constitutional keyB.constitutional = Ordering.eq) := by
  refine ⟨input_atomCount, center_val, tetrahedralCenterSet_eq, rfl, rfl, rfl,
    branchACursor_eq_ligandRoot, branchBCursor_eq_ligandRoot, molecularReader_branchA,
    molecularReader_branchB, stage_builds_rule4a, stage_builds_rule4bR⟩

/-- A putative generic Rule-4a order-preservation law for actual stage builds over arbitrary
supplied maps is false already at the actual certified input: instantiate any such law here and
contradict `stage_builds_rule4bR`. -/
theorem rule4a_order_preservation_fails :
    ¬ ∀ (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
        (target : input.LocalizedCIPOccurrence carrierFuel)
        (left right : input.LocalizedRerootCursor carrierFuel)
        (keyA4a keyB4a keyA4b keyB4b : Key),
        input.buildLocalizedRerootCumulativeRule45Key? .rule4a target
            (input.molecularView descriptorMap target) buildFuel left = some keyA4a →
        input.buildLocalizedRerootCumulativeRule45Key? .rule4a target
            (input.molecularView descriptorMap target) buildFuel right = some keyB4a →
        input.buildLocalizedRerootCumulativeRule45Key? rule4bR target
            (input.molecularView descriptorMap target) buildFuel left = some keyA4b →
        input.buildLocalizedRerootCumulativeRule45Key? rule4bR target
            (input.molecularView descriptorMap target) buildFuel right = some keyB4b →
        input.compareLocalizedRerootCumulativeRule45Keys keyA4a keyB4a = Ordering.lt →
        input.compareLocalizedRerootCumulativeRule45Keys keyA4b keyB4b = Ordering.lt := by
  intro universal
  obtain ⟨keyA4a, keyB4a, ⟨_, builtA4a⟩, ⟨_, builtB4a⟩, compared4a, _tie4a⟩ :=
    stage_builds_rule4a
  obtain ⟨keyA4b, keyB4b, ⟨_, builtA4b⟩, ⟨_, builtB4b⟩, compared4b, _tie4b⟩ :=
    stage_builds_rule4bR
  have claimed := universal fixtureMap centerOcc branchACursor branchBCursor
    keyA4a keyB4a keyA4b keyB4b builtA4a builtB4a builtA4b builtB4b compared4a
  rw [compared4b] at claimed
  exact absurd claimed (by decide +kernel)

/-! ## Kernel-authority guards -/

assert_kernel_only descending_methyl2_rule4a
assert_kernel_only descending_methyl3_rule4a
assert_kernel_only descending_methyl12_rule4a
assert_kernel_only descending_methyl13_rule4a
assert_kernel_only descending_branchA_rule4a
assert_kernel_only descending_branchB_rule4a
assert_kernel_only descending_methyl2_rule4bR
assert_kernel_only descending_methyl3_rule4bR
assert_kernel_only descending_methyl12_rule4bR
assert_kernel_only descending_methyl13_rule4bR
assert_kernel_only descending_branchA_rule4bR
assert_kernel_only descending_branchB_rule4bR
assert_kernel_only declarative_methyl2_rule4a
assert_kernel_only declarative_methyl3_rule4a
assert_kernel_only declarative_methyl12_rule4a
assert_kernel_only declarative_methyl13_rule4a
assert_kernel_only declarative_methyl2_rule4bR
assert_kernel_only declarative_methyl3_rule4bR
assert_kernel_only declarative_methyl12_rule4bR
assert_kernel_only declarative_methyl13_rule4bR
assert_kernel_only declarative_branchA_rule4a
assert_kernel_only declarative_branchB_rule4a
assert_kernel_only declarative_branchA_rule4bR
assert_kernel_only declarative_branchB_rule4bR
assert_kernel_only molecularReader_branchA
assert_kernel_only molecularReader_branchB
assert_kernel_only atomZ_actual
assert_kernel_only branchA_build_rule4a
assert_kernel_only branchB_build_rule4a
assert_kernel_only branchA_build_rule4bR
assert_kernel_only branchB_build_rule4bR
assert_kernel_only compare_derived_rule4a
assert_kernel_only compare_derived_rule4bR
assert_kernel_only constitutional_tie_derived_rule4a
assert_kernel_only constitutional_tie_derived_rule4bR
assert_kernel_only compare_rule4a
assert_kernel_only compare_rule4bR
assert_kernel_only constitutional_tie_rule4a
assert_kernel_only constitutional_tie_rule4bR
assert_kernel_only stage_builds_rule4a
assert_kernel_only stage_builds_rule4bR
assert_kernel_only actual_stage_rank_reversal
assert_kernel_only rule4a_order_preservation_fails

end TetraStereo.OneCenter.ActualEarlierRuleRankCounterexample
