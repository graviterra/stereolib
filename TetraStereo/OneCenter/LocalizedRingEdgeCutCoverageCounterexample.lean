import TetraStereo.UniversalProof.NextFrontier.NativeRingSourceInput
import TetraStereo.OneCenter.LocalizedOccurrenceRerootFrame
import TetraStereo.OneCenter.LocalizedAcyclicAutomorphismCursorTransport
import TetraStereo.OneCenter.LocalizedPublicChildEnumeration
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000


































namespace TetraStereo.OneCenter.RingEdgeCut

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.NativeRingSourceInput

/-! ## The actual production fixture and its admission -/

/-- The actual production physical fixture: the explicit-hydrogen expansion of `ringRaw 0`. -/
abbrev RingExpanded : RawMolecule :=
  expanded 0 TetrahedralInputParity.anticlockwise

/-- The actual production source produced by the existing converter on `RingExpanded`. -/
abbrev RingSource : AuthoritativeChemicalInput :=
  ringSource 0 TetrahedralInputParity.anticlockwise

/-- The actual production source passes its own executable structural check. -/
theorem ringSource_structurallyWellFormed : RingSource.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff RingSource).mp (by
    decide +kernel)

/-- The actual production source passes its own executable localized-graph readiness check. -/
theorem ringSource_graphReady : RingSource.molecule.LocalizedCIPGraphReady :=
  (SemanticMolecule.localizedCIPGraphReady?_eq_true_iff RingSource.molecule).mp (by
    decide +kernel)

/-- The actual certified localized CIP input built from the production source. -/
def actualRingCIPInput : CertifiedLocalizedCIPInput where
  certified :=
    { input := RingSource
      structurallyWellFormed := ringSource_structurallyWellFormed }
  graphReady := ringSource_graphReady

/-- Its carrier atom type has exactly nine atoms. -/
theorem actualRingCIPInput_atomCount :
    actualRingCIPInput.certified.input.molecule.atomCount = 9 := by
  have converted :
      RingExpanded.toSemanticMolecule? =
        some actualRingCIPInput.certified.input.molecule := by
    simpa [actualRingCIPInput, RingSource, RingExpanded] using
      (ring_annotation_agreement 0 TetrahedralInputParity.anticlockwise).1
  have count :=
    RawMolecule.toSemanticMolecule?_atomCount RingExpanded _ converted
  have expandedCount : RingExpanded.atomCount = 9 := by
    simpa [RingExpanded] using
      expanded_atom_count 0 TetrahedralInputParity.anticlockwise
  rwa [expandedCount] at count

/-- An atom of the actual input, named by a literal index below nine.  The definitional
unfolding of `atomCount` is not assumed: the proof transports `Fin 9` across the proved count. -/
def atom (index : Fin 9) : actualRingCIPInput.Atom :=
  Fin.cast actualRingCIPInput_atomCount.symm index

@[simp] theorem atom_val (index : Fin 9) : (atom index).val = index.val := rfl

def A0 : actualRingCIPInput.Atom := atom ⟨0, by decide⟩
def A1 : actualRingCIPInput.Atom := atom ⟨1, by decide⟩
def A2 : actualRingCIPInput.Atom := atom ⟨2, by decide⟩
def A3 : actualRingCIPInput.Atom := atom ⟨3, by decide⟩
def A4 : actualRingCIPInput.Atom := atom ⟨4, by decide⟩
def A5 : actualRingCIPInput.Atom := atom ⟨5, by decide⟩
def A6 : actualRingCIPInput.Atom := atom ⟨6, by decide⟩
def A7 : actualRingCIPInput.Atom := atom ⟨7, by decide⟩
def A8 : actualRingCIPInput.Atom := atom ⟨8, by decide⟩

/-! ## The concrete official occurrence nodes and frames at fuel `2` -/

def rootNode : OfficialCIPNode actualRingCIPInput.Atom :=
  OfficialCIPNode.root A0

/-- The original-root child at atom `1` (fluorine), present in the physical graph. -/
def node1 : OfficialCIPNode actualRingCIPInput.Atom :=
  rootNode.extend A1 0

/-- The arm start child at real atom `2`. -/
def node2 : OfficialCIPNode actualRingCIPInput.Atom :=
  rootNode.extend A2 0

/-- The original-root child at atom `4`; not the arm node, which has parent atom `2`. -/
def node4RootChild : OfficialCIPNode actualRingCIPInput.Atom :=
  rootNode.extend A4 0

/-- The original-root hydrogen child at atom `5`. -/
def node5 : OfficialCIPNode actualRingCIPInput.Atom :=
  rootNode.extend A5 0

/-- The chlorine child of arm atom `2`. -/
def node3 : OfficialCIPNode actualRingCIPInput.Atom :=
  node2.extend A3 0

/-- The arm carbon at atom `4`, whose parent is arm atom `2`. -/
def node4 : OfficialCIPNode actualRingCIPInput.Atom :=
  node2.extend A4 0

/-- The hydrogen child of arm atom `2`. -/
def node6 : OfficialCIPNode actualRingCIPInput.Atom :=
  node2.extend A6 0

/-- The ring duplicate of original root atom `0` sighted along the arm `0 - 2 - 4 - 0`. -/
def duplicateNode : OfficialCIPNode actualRingCIPInput.Atom :=
  node4.extend A0 0

def node7 : OfficialCIPNode actualRingCIPInput.Atom :=
  node4.extend A7 0

def node8 : OfficialCIPNode actualRingCIPInput.Atom :=
  node4.extend A8 0

@[simp] theorem rootNode_current : rootNode.current? = some A0 := rfl
@[simp] theorem node2_current : node2.current? = some A2 := rfl
@[simp] theorem node3_current : node3.current? = some A3 := rfl
@[simp] theorem node4_current : node4.current? = some A4 := rfl
@[simp] theorem node6_current : node6.current? = some A6 := rfl
@[simp] theorem duplicateNode_current : duplicateNode.current? = some A0 := rfl
@[simp] theorem node7_current : node7.current? = some A7 := rfl
@[simp] theorem node8_current : node8.current? = some A8 := rfl

def rootFrame : actualRingCIPInput.LocalizedCIPOccurrenceFrame :=
  { root := A0, address := [], node := rootNode, remaining := 3 }

def startFrame : actualRingCIPInput.LocalizedCIPOccurrenceFrame :=
  { root := A0, address := [1], node := node2, remaining := 2 }

def threeFrame : actualRingCIPInput.LocalizedCIPOccurrenceFrame :=
  { root := A0, address := [1, 0], node := node3, remaining := 1 }

def fourFrame : actualRingCIPInput.LocalizedCIPOccurrenceFrame :=
  { root := A0, address := [1, 1], node := node4, remaining := 1 }

def sixFrame : actualRingCIPInput.LocalizedCIPOccurrenceFrame :=
  { root := A0, address := [1, 2], node := node6, remaining := 1 }

def duplicateFrame : actualRingCIPInput.LocalizedCIPOccurrenceFrame :=
  { root := A0, address := [1, 1, 0], node := duplicateNode, remaining := 0 }

def sevenFrame : actualRingCIPInput.LocalizedCIPOccurrenceFrame :=
  { root := A0, address := [1, 1, 1], node := node7, remaining := 0 }

def eightFrame : actualRingCIPInput.LocalizedCIPOccurrenceFrame :=
  { root := A0, address := [1, 1, 2], node := node8, remaining := 0 }

/-! ## Exact executable child lists

The production executable enumeration uses `Finset.sort`, which does not reduce in the kernel.  We
use the existing exact public/localized child-enumeration bridge
`aromaticCanonicalOfficialCIPChildrenAt_eq_executableOfficialCIPChildren`; the public side is a
plain `List.finRange` computation and therefore kernel-reduces.  This is a proof step on the actual
definitions, not a compiled or assumed constant. -/

theorem rootChildren_eq :
    actualRingCIPInput.executableOfficialCIPChildren rootNode =
      [node1, node2, node4RootChild, node5] := by
  rw [← actualRingCIPInput.aromaticCanonicalOfficialCIPChildrenAt_eq_executableOfficialCIPChildren]
  decide +kernel

theorem node2Children_eq :
    actualRingCIPInput.executableOfficialCIPChildren node2 =
      [node3, node4, node6] := by
  rw [← actualRingCIPInput.aromaticCanonicalOfficialCIPChildrenAt_eq_executableOfficialCIPChildren]
  decide +kernel

theorem node4Children_eq :
    actualRingCIPInput.executableOfficialCIPChildren node4 =
      [duplicateNode, node7, node8] := by
  rw [← actualRingCIPInput.aromaticCanonicalOfficialCIPChildrenAt_eq_executableOfficialCIPChildren]
  decide +kernel

theorem node3Children_eq :
    actualRingCIPInput.executableOfficialCIPChildren node3 = [] := by
  rw [← actualRingCIPInput.aromaticCanonicalOfficialCIPChildrenAt_eq_executableOfficialCIPChildren]
  decide +kernel

theorem node6Children_eq :
    actualRingCIPInput.executableOfficialCIPChildren node6 = [] := by
  rw [← actualRingCIPInput.aromaticCanonicalOfficialCIPChildrenAt_eq_executableOfficialCIPChildren]
  decide +kernel

theorem node7Children_eq :
    actualRingCIPInput.executableOfficialCIPChildren node7 = [] := by
  rw [← actualRingCIPInput.aromaticCanonicalOfficialCIPChildrenAt_eq_executableOfficialCIPChildren]
  decide +kernel

theorem node8Children_eq :
    actualRingCIPInput.executableOfficialCIPChildren node8 = [] := by
  rw [← actualRingCIPInput.aromaticCanonicalOfficialCIPChildrenAt_eq_executableOfficialCIPChildren]
  decide +kernel

theorem duplicateChildren_eq :
    actualRingCIPInput.executableOfficialCIPChildren duplicateNode = [] := by
  rw [← actualRingCIPInput.aromaticCanonicalOfficialCIPChildrenAt_eq_executableOfficialCIPChildren]
  decide +kernel

theorem duplicate_is_terminal : duplicateNode.isDuplicateLeaf = true := by
  decide +kernel

/-! ## Concrete sibling slots -/

theorem childAtRoot_arm :
    (node2, 1) ∈
      (actualRingCIPInput.executableOfficialCIPChildren rootNode).zipIdx := by
  rw [rootChildren_eq]
  decide +kernel

theorem childAtArm_three :
    (node3, 0) ∈
      (actualRingCIPInput.executableOfficialCIPChildren node2).zipIdx := by
  rw [node2Children_eq]
  decide +kernel

theorem childAtArm_four :
    (node4, 1) ∈
      (actualRingCIPInput.executableOfficialCIPChildren node2).zipIdx := by
  rw [node2Children_eq]
  decide +kernel

theorem childAtArm_six :
    (node6, 2) ∈
      (actualRingCIPInput.executableOfficialCIPChildren node2).zipIdx := by
  rw [node2Children_eq]
  decide +kernel

theorem childAtFour_duplicate :
    (duplicateNode, 0) ∈
      (actualRingCIPInput.executableOfficialCIPChildren node4).zipIdx := by
  rw [node4Children_eq]
  decide +kernel

theorem childAtFour_seven :
    (node7, 1) ∈
      (actualRingCIPInput.executableOfficialCIPChildren node4).zipIdx := by
  rw [node4Children_eq]
  decide +kernel

theorem childAtFour_eight :
    (node8, 2) ∈
      (actualRingCIPInput.executableOfficialCIPChildren node4).zipIdx := by
  rw [node4Children_eq]
  decide +kernel

/-! ## Actual carrier membership by the independent declarative relation -/

theorem rootFrame_declarative :
    actualRingCIPInput.DeclarativeLocalizedOccurrence 2 rootFrame := by
  change actualRingCIPInput.DeclarativeLocalizedOccurrenceSubtree A0 [] 3 rootNode rootFrame
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
    (input := actualRingCIPInput) (root := A0) (path := []) (fuel := 3) (node := rootNode)

theorem startFrame_declarative :
    actualRingCIPInput.DeclarativeLocalizedOccurrence 2 startFrame := by
  change actualRingCIPInput.DeclarativeLocalizedOccurrenceSubtree A0 [] 3 rootNode startFrame
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := actualRingCIPInput) (root := A0)
    (path := []) (fuel := 2) (node := rootNode) (child := node2) (slot := 1)
    (occurrence := startFrame)
    childAtRoot_arm
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
      (input := actualRingCIPInput) (root := A0) (path := [1]) (fuel := 2) (node := node2))

theorem threeFrame_declarative :
    actualRingCIPInput.DeclarativeLocalizedOccurrence 2 threeFrame := by
  change actualRingCIPInput.DeclarativeLocalizedOccurrenceSubtree A0 [] 3 rootNode threeFrame
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := actualRingCIPInput) (root := A0)
    (path := []) (fuel := 2) (node := rootNode) (child := node2) (slot := 1)
    (occurrence := threeFrame)
    childAtRoot_arm
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := actualRingCIPInput) (root := A0)
      (path := [1]) (fuel := 1) (node := node2) (child := node3) (slot := 0)
      (occurrence := threeFrame)
      childAtArm_three
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
        (input := actualRingCIPInput) (root := A0) (path := [1, 0]) (fuel := 1)
        (node := node3)))

theorem fourFrame_declarative :
    actualRingCIPInput.DeclarativeLocalizedOccurrence 2 fourFrame := by
  change actualRingCIPInput.DeclarativeLocalizedOccurrenceSubtree A0 [] 3 rootNode fourFrame
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := actualRingCIPInput) (root := A0)
    (path := []) (fuel := 2) (node := rootNode) (child := node2) (slot := 1)
    (occurrence := fourFrame)
    childAtRoot_arm
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := actualRingCIPInput) (root := A0)
      (path := [1]) (fuel := 1) (node := node2) (child := node4) (slot := 1)
      (occurrence := fourFrame)
      childAtArm_four
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
        (input := actualRingCIPInput) (root := A0) (path := [1, 1]) (fuel := 1)
        (node := node4)))

theorem sixFrame_declarative :
    actualRingCIPInput.DeclarativeLocalizedOccurrence 2 sixFrame := by
  change actualRingCIPInput.DeclarativeLocalizedOccurrenceSubtree A0 [] 3 rootNode sixFrame
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := actualRingCIPInput) (root := A0)
    (path := []) (fuel := 2) (node := rootNode) (child := node2) (slot := 1)
    (occurrence := sixFrame)
    childAtRoot_arm
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := actualRingCIPInput) (root := A0)
      (path := [1]) (fuel := 1) (node := node2) (child := node6) (slot := 2)
      (occurrence := sixFrame)
      childAtArm_six
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
        (input := actualRingCIPInput) (root := A0) (path := [1, 2]) (fuel := 1)
        (node := node6)))

theorem duplicateFrame_declarative :
    actualRingCIPInput.DeclarativeLocalizedOccurrence 2 duplicateFrame := by
  change actualRingCIPInput.DeclarativeLocalizedOccurrenceSubtree A0 [] 3 rootNode duplicateFrame
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := actualRingCIPInput) (root := A0)
    (path := []) (fuel := 2) (node := rootNode) (child := node2) (slot := 1)
    (occurrence := duplicateFrame)
    childAtRoot_arm
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := actualRingCIPInput) (root := A0)
      (path := [1]) (fuel := 1) (node := node2) (child := node4) (slot := 1)
      (occurrence := duplicateFrame)
      childAtArm_four
      (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := actualRingCIPInput) (root := A0)
        (path := [1, 1]) (fuel := 0) (node := node4) (child := duplicateNode) (slot := 0)
        (occurrence := duplicateFrame)
        childAtFour_duplicate
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := actualRingCIPInput) (root := A0) (path := [1, 1, 0]) (fuel := 0)
          (node := duplicateNode))))

theorem sevenFrame_declarative :
    actualRingCIPInput.DeclarativeLocalizedOccurrence 2 sevenFrame := by
  change actualRingCIPInput.DeclarativeLocalizedOccurrenceSubtree A0 [] 3 rootNode sevenFrame
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := actualRingCIPInput) (root := A0)
    (path := []) (fuel := 2) (node := rootNode) (child := node2) (slot := 1)
    (occurrence := sevenFrame)
    childAtRoot_arm
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := actualRingCIPInput) (root := A0)
      (path := [1]) (fuel := 1) (node := node2) (child := node4) (slot := 1)
      (occurrence := sevenFrame)
      childAtArm_four
      (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := actualRingCIPInput) (root := A0)
        (path := [1, 1]) (fuel := 0) (node := node4) (child := node7) (slot := 1)
        (occurrence := sevenFrame)
        childAtFour_seven
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := actualRingCIPInput) (root := A0) (path := [1, 1, 1]) (fuel := 0)
          (node := node7))))

theorem eightFrame_declarative :
    actualRingCIPInput.DeclarativeLocalizedOccurrence 2 eightFrame := by
  change actualRingCIPInput.DeclarativeLocalizedOccurrenceSubtree A0 [] 3 rootNode eightFrame
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (input := actualRingCIPInput) (root := A0)
    (path := []) (fuel := 2) (node := rootNode) (child := node2) (slot := 1)
    (occurrence := eightFrame)
    childAtRoot_arm
    (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
      (input := actualRingCIPInput) (root := A0)
      (path := [1]) (fuel := 1) (node := node2) (child := node4) (slot := 1)
      (occurrence := eightFrame)
      childAtArm_four
      (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
        (input := actualRingCIPInput) (root := A0)
        (path := [1, 1]) (fuel := 0) (node := node4) (child := node8) (slot := 2)
        (occurrence := eightFrame)
        childAtFour_eight
        (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
          (input := actualRingCIPInput) (root := A0) (path := [1, 1, 2]) (fuel := 0)
          (node := node8))))

theorem rootFrame_mem :
    rootFrame ∈ actualRingCIPInput.localizedOccurrences 2 :=
  (actualRingCIPInput.mem_localizedOccurrences_iff 2 rootFrame).mpr rootFrame_declarative

theorem startFrame_mem :
    startFrame ∈ actualRingCIPInput.localizedOccurrences 2 :=
  (actualRingCIPInput.mem_localizedOccurrences_iff 2 startFrame).mpr startFrame_declarative

theorem threeFrame_mem :
    threeFrame ∈ actualRingCIPInput.localizedOccurrences 2 :=
  (actualRingCIPInput.mem_localizedOccurrences_iff 2 threeFrame).mpr threeFrame_declarative

theorem fourFrame_mem :
    fourFrame ∈ actualRingCIPInput.localizedOccurrences 2 :=
  (actualRingCIPInput.mem_localizedOccurrences_iff 2 fourFrame).mpr fourFrame_declarative

theorem sixFrame_mem :
    sixFrame ∈ actualRingCIPInput.localizedOccurrences 2 :=
  (actualRingCIPInput.mem_localizedOccurrences_iff 2 sixFrame).mpr sixFrame_declarative

theorem duplicateFrame_mem :
    duplicateFrame ∈ actualRingCIPInput.localizedOccurrences 2 :=
  (actualRingCIPInput.mem_localizedOccurrences_iff 2 duplicateFrame).mpr
    duplicateFrame_declarative

theorem sevenFrame_mem :
    sevenFrame ∈ actualRingCIPInput.localizedOccurrences 2 :=
  (actualRingCIPInput.mem_localizedOccurrences_iff 2 sevenFrame).mpr sevenFrame_declarative

theorem eightFrame_mem :
    eightFrame ∈ actualRingCIPInput.localizedOccurrences 2 :=
  (actualRingCIPInput.mem_localizedOccurrences_iff 2 eightFrame).mpr eightFrame_declarative

/-! ## Actual bundled occurrences and the fixed-origin start cursor -/

def occRoot : actualRingCIPInput.LocalizedCIPOccurrence 2 :=
  ⟨rootFrame, rootFrame_mem⟩

def occStart : actualRingCIPInput.LocalizedCIPOccurrence 2 :=
  ⟨startFrame, startFrame_mem⟩

def occThree : actualRingCIPInput.LocalizedCIPOccurrence 2 :=
  ⟨threeFrame, threeFrame_mem⟩

def occFour : actualRingCIPInput.LocalizedCIPOccurrence 2 :=
  ⟨fourFrame, fourFrame_mem⟩

def occSix : actualRingCIPInput.LocalizedCIPOccurrence 2 :=
  ⟨sixFrame, sixFrame_mem⟩

def occDuplicate : actualRingCIPInput.LocalizedCIPOccurrence 2 :=
  ⟨duplicateFrame, duplicateFrame_mem⟩

def occSeven : actualRingCIPInput.LocalizedCIPOccurrence 2 :=
  ⟨sevenFrame, sevenFrame_mem⟩

def occEight : actualRingCIPInput.LocalizedCIPOccurrence 2 :=
  ⟨eightFrame, eightFrame_mem⟩

/-- The actual arm start: real atom `2`, with the real original root `0` as the cut predecessor. -/
def startCursor : actualRingCIPInput.LocalizedRerootCursor 2 :=
  { occurrence := occStart, previous? := some occRoot }

theorem startCursor_previous :
    startCursor.previous? = some occRoot := rfl

/-- The general `occurrence_current_exists` API applies to the actual start occurrence without any
acyclicity or single-bond premise. -/
theorem startCursor_current_exists :
    ∃ atom : actualRingCIPInput.Atom,
      startCursor.occurrence.1.node.current? = some atom :=
  CertifiedLocalizedCIPInput.occurrence_current_exists (input := actualRingCIPInput)
    startCursor.occurrence

/-! ## The actual reroot transition relation and its closure invariant -/

/-- One successful production reroot expansion step. -/
noncomputable def CursorStep {fuel : Nat}
    (cursor next : actualRingCIPInput.LocalizedRerootCursor fuel) : Prop :=
  ∃ children,
    actualRingCIPInput.localizedRerootChildren? cursor = some children ∧
      next ∈ children

/-- Actual finite reachability from the fixed-origin start cursor. -/
inductive ArmReachable : actualRingCIPInput.LocalizedRerootCursor 2 → Prop where
  | start : ArmReachable startCursor
  | step {cursor next} :
      ArmReachable cursor → CursorStep cursor next → ArmReachable next

/-- Actual finite production reachability from an arbitrary start cursor at an arbitrary carrier
fuel. -/
inductive ReachableFrom {fuel : Nat}
    (start : actualRingCIPInput.LocalizedRerootCursor fuel) :
    actualRingCIPInput.LocalizedRerootCursor fuel → Prop where
  | refl : ReachableFrom start start
  | step {cursor next} :
      ReachableFrom start cursor → CursorStep cursor next → ReachableFrom start next

/-- The exact node set reached by the outward arm.  Atom `1` is deliberately absent. -/
def NodeInArm (node : OfficialCIPNode actualRingCIPInput.Atom) : Prop :=
  node = node2 ∨ node = node3 ∨ node = node4 ∨ node = node6 ∨
    node = duplicateNode ∨ node = node7 ∨ node = node8

/-- Every reachable cursor keeps the immediate carrier parent as its recorded incoming cut. -/
def CutInvariant {fuel : Nat}
    (cursor : actualRingCIPInput.LocalizedRerootCursor fuel) : Prop :=
  ∃ previous,
    cursor.previous? = some previous ∧
      previous.1.address = cursor.occurrence.1.address.dropLast

/-- If a list has the drop-last of a shorter list and is exactly one longer, it is that list with
one appended slot. -/
theorem eq_append_singleton_of_dropLast_eq_of_length_eq
    {address base : List Nat}
    (dropLastEq : address.dropLast = base)
    (lengthEq : address.length = base.length + 1) :
    ∃ slot, address = base ++ [slot] := by
  have nonempty : address ≠ [] := by
    intro empty
    rw [empty] at lengthEq
    simp at lengthEq
  refine ⟨address.getLast nonempty, ?_⟩
  calc
    address = address.dropLast ++ [address.getLast nonempty] :=
      (List.dropLast_concat_getLast nonempty).symm
    _ = base ++ [address.getLast nonempty] := by rw [dropLastEq]

theorem start_cut : CutInvariant startCursor := by
  refine ⟨occRoot, rfl, ?_⟩
  rfl

theorem start_node : NodeInArm startCursor.occurrence.1.node :=
  Or.inl rfl

/-- One actual production step preserves the node-set invariant and the incoming-cut invariant.
The proof uses only the exact production child enumeration and the address grading of the reroot
neighbour list; it does not assume that the intended list equals any displayed list. -/
theorem arm_step {fuel : Nat}
    {cursor next : actualRingCIPInput.LocalizedRerootCursor fuel}
    (nodeInArm : NodeInArm cursor.occurrence.1.node)
    (cutInvariant : CutInvariant cursor)
    (step : CursorStep cursor next) :
    NodeInArm next.occurrence.1.node ∧ CutInvariant next := by
  obtain ⟨children, computed, nextPresent⟩ := step
  have derived :=
    actualRingCIPInput.localizedRerootChildren?_sound cursor children computed
  have nextPrevious : next.previous? = some cursor.occurrence :=
    derived.2 next nextPresent
  have framePresent :
      next.occurrence.1 ∈
        actualRingCIPInput.intendedLocalizedRerootChildFrames cursor := by
    rw [← derived.1]
    exact List.mem_map.mpr ⟨next, nextPresent, rfl⟩
  obtain ⟨previous, cursorPrevious, previousAddress⟩ := cutInvariant
  by_cases duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true
  · simp only [CertifiedLocalizedCIPInput.intendedLocalizedRerootChildFrames] at framePresent
    simp [duplicate] at framePresent
  · have notDuplicate : cursor.occurrence.1.node.isDuplicateLeaf = false := by
      simpa using duplicate
    simp only [CertifiedLocalizedCIPInput.intendedLocalizedRerootChildFrames] at framePresent
    simp only [notDuplicate, Bool.false_eq_true, ↓reduceIte] at framePresent
    cases cursorPreviousCase : cursor.previous? with
    | none =>
        rw [cursorPreviousCase] at cursorPrevious
        simp at cursorPrevious
    | some incoming =>
        have incomingEq : incoming = previous :=
          Option.some.inj (cursorPreviousCase.symm.trans cursorPrevious)
        subst incoming
        rw [cursorPreviousCase, List.mem_filter] at framePresent
        obtain ⟨neighborPresent, awayFromIncoming⟩ := framePresent
        have addressDifferent :
            next.occurrence.1.address ≠ previous.1.address := by
          simpa using awayFromIncoming
        simp only [CertifiedLocalizedCIPInput.localizedRerootNeighborFrames] at neighborPresent
        rw [List.mem_append] at neighborPresent
        rcases neighborPresent with parentPresent | outwardPresent
        · simp only [CertifiedLocalizedCIPInput.localizedCarrierParentFrames] at parentPresent
          rw [List.mem_filter] at parentPresent
          obtain ⟨_parentInCarrier, parentConditions⟩ := parentPresent
          simp only [Bool.and_eq_true, beq_iff_eq] at parentConditions
          have parentAddress :
              next.occurrence.1.address = previous.1.address :=
            parentConditions.2.trans previousAddress.symm
          exact absurd parentAddress addressDifferent
        · simp only [CertifiedLocalizedCIPInput.localizedCarrierOutwardChildFrames] at outwardPresent
          rw [List.mem_filter] at outwardPresent
          obtain ⟨nextInCarrier, outwardConditions⟩ := outwardPresent
          simp only [Bool.and_eq_true, beq_iff_eq] at outwardConditions
          have sameRoot : next.occurrence.1.root = cursor.occurrence.1.root :=
            outwardConditions.1.1
          have addressLength :
              next.occurrence.1.address.length =
                cursor.occurrence.1.address.length + 1 :=
            outwardConditions.1.2
          have dropLastAddress :
              next.occurrence.1.address.dropLast = cursor.occurrence.1.address :=
            outwardConditions.2
          obtain ⟨slot, addressEq⟩ :=
            eq_append_singleton_of_dropLast_eq_of_length_eq
              dropLastAddress addressLength
          have sourceDerived :
              actualRingCIPInput.DeclarativeLocalizedOccurrence fuel cursor.occurrence.1 :=
            (actualRingCIPInput.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp
              cursor.occurrence.2
          have nextDerived :
              actualRingCIPInput.DeclarativeLocalizedOccurrence fuel next.occurrence.1 :=
            (actualRingCIPInput.mem_localizedOccurrences_iff fuel next.occurrence.1).mp
              nextInCarrier
          obtain ⟨child, childAtSlot, childFrameEq⟩ :=
            actualRingCIPInput.declarativeLocalizedOccurrence_immediate_child
              sourceDerived nextDerived sameRoot slot addressEq
          have nextNode : next.occurrence.1.node = child := by
            rw [childFrameEq]
          have nextAddress :
              next.occurrence.1.address = cursor.occurrence.1.address ++ [slot] := by
            rw [childFrameEq]
          have nextCut : CutInvariant next := by
            refine ⟨cursor.occurrence, nextPrevious, ?_⟩
            rw [nextAddress, List.dropLast_concat]
          refine ⟨?_, nextCut⟩
          rw [nextNode]
          rcases nodeInArm with atStart | atThree | atFour | atSix | atDuplicate | atSeven | atEight
          · rw [atStart] at childAtSlot
            rw [node2Children_eq] at childAtSlot
            simp only [List.zipIdx_cons, List.zipIdx_nil, List.mem_cons, List.not_mem_nil,
              or_false, Prod.mk.injEq] at childAtSlot
            rcases childAtSlot with ⟨sameNode, _⟩ | ⟨sameNode, _⟩ | ⟨sameNode, _⟩
            · rw [sameNode]
              exact Or.inr (Or.inl rfl)
            · rw [sameNode]
              exact Or.inr (Or.inr (Or.inl rfl))
            · rw [sameNode]
              exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · rw [atThree] at childAtSlot
            rw [node3Children_eq] at childAtSlot
            simp at childAtSlot
          · rw [atFour] at childAtSlot
            rw [node4Children_eq] at childAtSlot
            simp only [List.zipIdx_cons, List.zipIdx_nil, List.mem_cons, List.not_mem_nil,
              or_false, Prod.mk.injEq] at childAtSlot
            rcases childAtSlot with ⟨sameNode, _⟩ | ⟨sameNode, _⟩ | ⟨sameNode, _⟩
            · rw [sameNode]
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
            · rw [sameNode]
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
            · rw [sameNode]
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
          · rw [atSix] at childAtSlot
            rw [node6Children_eq] at childAtSlot
            simp at childAtSlot
          · rw [atDuplicate] at childAtSlot
            rw [duplicateChildren_eq] at childAtSlot
            simp at childAtSlot
          · rw [atSeven] at childAtSlot
            rw [node7Children_eq] at childAtSlot
            simp at childAtSlot
          · rw [atEight] at childAtSlot
            rw [node8Children_eq] at childAtSlot
            simp at childAtSlot

/-- The closure invariant holds at every actually reachable arm position. -/
theorem reachable_invariant
    {cursor : actualRingCIPInput.LocalizedRerootCursor 2}
    (reachable : ArmReachable cursor) :
    NodeInArm cursor.occurrence.1.node ∧ CutInvariant cursor := by
  induction reachable with
  | start => exact ⟨start_node, start_cut⟩
  | step _ stepInvariant inductionHypothesis =>
      exact arm_step inductionHypothesis.1 inductionHypothesis.2 stepInvariant

/-- Every renderable arm node has one of the seven arm atoms as its current physical atom. -/
theorem NodeInArm.current_mem
    {node : OfficialCIPNode actualRingCIPInput.Atom}
    (inArm : NodeInArm node) :
    node.current? = some A2 ∨ node.current? = some A3 ∨
      node.current? = some A4 ∨ node.current? = some A6 ∨
      node.current? = some A0 ∨ node.current? = some A7 ∨
      node.current? = some A8 := by
  rcases inArm with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-- Every node in the seven-node arm set carries one of the seven arm atoms, never fluorine. -/
theorem NodeInArm.current_ne_F
    {node : OfficialCIPNode actualRingCIPInput.Atom}
    (inArm : NodeInArm node) :
    node.current? ≠ some A1 := by
  intro fluorine
  rcases inArm with atStart | atThree | atFour | atSix | atDuplicate | atSeven | atEight
  · rw [atStart, node2_current] at fluorine
    exact (by decide +kernel : A2 ≠ A1) (Option.some.inj fluorine)
  · rw [atThree, node3_current] at fluorine
    exact (by decide +kernel : A3 ≠ A1) (Option.some.inj fluorine)
  · rw [atFour, node4_current] at fluorine
    exact (by decide +kernel : A4 ≠ A1) (Option.some.inj fluorine)
  · rw [atSix, node6_current] at fluorine
    exact (by decide +kernel : A6 ≠ A1) (Option.some.inj fluorine)
  · rw [atDuplicate, duplicateNode_current] at fluorine
    exact (by decide +kernel : A0 ≠ A1) (Option.some.inj fluorine)
  · rw [atSeven, node7_current] at fluorine
    exact (by decide +kernel : A7 ≠ A1) (Option.some.inj fluorine)
  · rw [atEight, node8_current] at fluorine
    exact (by decide +kernel : A8 ≠ A1) (Option.some.inj fluorine)

/-- No actual reachable fuel-`2` arm position carries the fluorine atom `1`. -/
theorem arm_current_ne_F
    {cursor : actualRingCIPInput.LocalizedRerootCursor 2}
    (reachable : ArmReachable cursor) :
    cursor.occurrence.1.node.current? ≠ some A1 :=
  NodeInArm.current_ne_F (reachable_invariant reachable).1

/-! ## Positive actual reachability of the recipe nodes -/

/-- Every executable official child away from the incoming cut yields an actual next cursor in the
production zipper expansion. -/
theorem reachable_executable_child
    (cursor : actualRingCIPInput.LocalizedRerootCursor 2)
    (reachable : ArmReachable cursor)
    (nonduplicate : cursor.occurrence.1.node.isDuplicateLeaf = false)
    (positive : 0 < cursor.occurrence.1.remaining)
    (child : OfficialCIPNode actualRingCIPInput.Atom) (slot : Nat)
    (childAtSlot : (child, slot) ∈
      (actualRingCIPInput.executableOfficialCIPChildren cursor.occurrence.1.node).zipIdx)
    (notIncoming : ∀ previous,
      cursor.previous? = some previous →
        cursor.occurrence.1.address ++ [slot] ≠ previous.1.address) :
    ∃ next,
      ArmReachable next ∧
        next.occurrence.1 =
          { root := cursor.occurrence.1.root
            address := cursor.occurrence.1.address ++ [slot]
            node := child
            remaining := cursor.occurrence.1.remaining - 1 } ∧
        next.previous? = some cursor.occurrence := by
  obtain ⟨children, next, computed, nextPresent, nextFrame⟩ :=
    actualRingCIPInput.exists_mem_localizedRerootChildren_of_executable_child
      cursor nonduplicate positive child slot childAtSlot notIncoming
  have derived :=
    actualRingCIPInput.localizedRerootChildren?_sound cursor children computed
  exact ⟨next, ArmReachable.step reachable ⟨children, computed, nextPresent⟩,
    nextFrame, derived.2 next nextPresent⟩

/-- The same executable-child step at arbitrary carrier fuel and for any start cursor. -/
theorem reachable_executable_child_at {fuel : Nat}
    {start : actualRingCIPInput.LocalizedRerootCursor fuel}
    (cursor : actualRingCIPInput.LocalizedRerootCursor fuel)
    (reachable : ReachableFrom start cursor)
    (nonduplicate : cursor.occurrence.1.node.isDuplicateLeaf = false)
    (positive : 0 < cursor.occurrence.1.remaining)
    (child : OfficialCIPNode actualRingCIPInput.Atom) (slot : Nat)
    (childAtSlot : (child, slot) ∈
      (actualRingCIPInput.executableOfficialCIPChildren cursor.occurrence.1.node).zipIdx)
    (notIncoming : ∀ previous,
      cursor.previous? = some previous →
        cursor.occurrence.1.address ++ [slot] ≠ previous.1.address) :
    ∃ next,
      ReachableFrom start next ∧
        next.occurrence.1 =
          { root := cursor.occurrence.1.root
            address := cursor.occurrence.1.address ++ [slot]
            node := child
            remaining := cursor.occurrence.1.remaining - 1 } ∧
        next.previous? = some cursor.occurrence := by
  obtain ⟨children, next, computed, nextPresent, nextFrame⟩ :=
    actualRingCIPInput.exists_mem_localizedRerootChildren_of_executable_child
      cursor nonduplicate positive child slot childAtSlot notIncoming
  have derived :=
    actualRingCIPInput.localizedRerootChildren?_sound cursor children computed
  exact ⟨next, ReachableFrom.step reachable ⟨children, computed, nextPresent⟩,
    nextFrame, derived.2 next nextPresent⟩

theorem arm_reaches_cl3 :
    ∃ cursor : actualRingCIPInput.LocalizedRerootCursor 2,
      ArmReachable cursor ∧ cursor.occurrence.1.node.current? = some A3 := by
  obtain ⟨next, reachable, nextFrame, _nextPrevious⟩ :=
    reachable_executable_child startCursor ArmReachable.start
      (by decide +kernel) (by decide +kernel) node3 0 childAtArm_three
      (by
        intro previous previousEq
        have previousIdentity : previous = occRoot := by
          have same : some previous = some occRoot := previousEq.symm.trans startCursor_previous
          exact Option.some.inj same
        subst previous
        decide +kernel)
  refine ⟨next, reachable, ?_⟩
  rw [nextFrame]
  rfl

theorem arm_reaches_c4 :
    ∃ cursor : actualRingCIPInput.LocalizedRerootCursor 2,
      ArmReachable cursor ∧ cursor.occurrence.1.node.current? = some A4 := by
  obtain ⟨next, reachable, nextFrame, _nextPrevious⟩ :=
    reachable_executable_child startCursor ArmReachable.start
      (by decide +kernel) (by decide +kernel) node4 1 childAtArm_four
      (by
        intro previous previousEq
        have previousIdentity : previous = occRoot := by
          have same : some previous = some occRoot := previousEq.symm.trans startCursor_previous
          exact Option.some.inj same
        subst previous
        decide +kernel)
  refine ⟨next, reachable, ?_⟩
  rw [nextFrame]
  rfl

theorem arm_reaches_h6 :
    ∃ cursor : actualRingCIPInput.LocalizedRerootCursor 2,
      ArmReachable cursor ∧ cursor.occurrence.1.node.current? = some A6 := by
  obtain ⟨next, reachable, nextFrame, _nextPrevious⟩ :=
    reachable_executable_child startCursor ArmReachable.start
      (by decide +kernel) (by decide +kernel) node6 2 childAtArm_six
      (by
        intro previous previousEq
        have previousIdentity : previous = occRoot := by
          have same : some previous = some occRoot := previousEq.symm.trans startCursor_previous
          exact Option.some.inj same
        subst previous
        decide +kernel)
  refine ⟨next, reachable, ?_⟩
  rw [nextFrame]
  rfl

/-- The arm `2 -> 4` continues to the duplicate of original root atom `0`. -/
theorem arm_reaches_duplicate0 :
    ∃ cursor : actualRingCIPInput.LocalizedRerootCursor 2,
      ArmReachable cursor ∧ cursor.occurrence.1.node.current? = some A0 := by
  obtain ⟨four, fourReachable, fourFrame, fourPrevious⟩ :=
    reachable_executable_child startCursor ArmReachable.start
      (by decide +kernel) (by decide +kernel) node4 1 childAtArm_four
      (by
        intro previous previousEq
        have previousIdentity : previous = occRoot := by
          have same : some previous = some occRoot := previousEq.symm.trans startCursor_previous
          exact Option.some.inj same
        subst previous
        decide +kernel)
  obtain ⟨next, reachable, nextFrame, _nextPrevious⟩ :=
    reachable_executable_child four fourReachable
      (by rw [fourFrame]; decide +kernel)
      (by rw [fourFrame]; decide +kernel)
      duplicateNode 0
      (by
        rw [fourFrame]
        exact childAtFour_duplicate)
      (by
        intro previous previousEq
        have previousIdentity : previous = occStart := by
          have same : some previous = some occStart := previousEq.symm.trans fourPrevious
          exact Option.some.inj same
        subst previous
        rw [fourFrame]
        decide +kernel)
  refine ⟨next, reachable, ?_⟩
  rw [nextFrame]
  rfl

/-- The duplicate of atom `0` is a production terminal node. -/
theorem arm_duplicate_terminal :
    actualRingCIPInput.executableOfficialCIPChildren duplicateNode = [] :=
  duplicateChildren_eq

/-! ## Intrinsic closure of the arm, independent of carrier fuel

The step invariant does not rely on the carrier running out of depth at the leaves.  Every listed
arm node has a complete intrinsic production child list: the two internal nodes `node2` and `node4`
have exactly the listed nonempty children (and those children lie in the arm set), while all five
remaining-zero nodes have intrinsically empty child lists.  Hence no fuel increase can add a new
arm child. -/

theorem node2_children_in_arm
    (child : OfficialCIPNode actualRingCIPInput.Atom) (slot : Nat)
    (present :
      (child, slot) ∈
        (actualRingCIPInput.executableOfficialCIPChildren node2).zipIdx) :
    NodeInArm child := by
  rw [node2Children_eq] at present
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at present
  rcases present with ⟨sameNode, _⟩ | ⟨sameNode, _⟩ | ⟨sameNode, _⟩
  · rw [sameNode]
    exact Or.inr (Or.inl rfl)
  · rw [sameNode]
    exact Or.inr (Or.inr (Or.inl rfl))
  · rw [sameNode]
    exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))

theorem node4_children_in_arm
    (child : OfficialCIPNode actualRingCIPInput.Atom) (slot : Nat)
    (present :
      (child, slot) ∈
        (actualRingCIPInput.executableOfficialCIPChildren node4).zipIdx) :
    NodeInArm child := by
  rw [node4Children_eq] at present
  simp only [List.zipIdx_cons, List.zipIdx_nil, List.mem_cons, List.not_mem_nil,
    or_false, Prod.mk.injEq] at present
  rcases present with ⟨sameNode, _⟩ | ⟨sameNode, _⟩ | ⟨sameNode, _⟩
  · rw [sameNode]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  · rw [sameNode]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  · rw [sameNode]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))

/-- Complete intrinsic production closure of every listed arm node.  The internal nodes have no
child outside the arm set, and the five remaining-zero nodes are genuine terminal leaves (the
duplicate node additionally being an actual duplicate leaf). -/
theorem arm_intrinsic_closure :
    (∀ (child : OfficialCIPNode actualRingCIPInput.Atom) (slot : Nat),
        (child, slot) ∈
            (actualRingCIPInput.executableOfficialCIPChildren node2).zipIdx →
          NodeInArm child) ∧
      (∀ (child : OfficialCIPNode actualRingCIPInput.Atom) (slot : Nat),
          (child, slot) ∈
              (actualRingCIPInput.executableOfficialCIPChildren node4).zipIdx →
            NodeInArm child) ∧
      actualRingCIPInput.executableOfficialCIPChildren node3 = [] ∧
      actualRingCIPInput.executableOfficialCIPChildren node6 = [] ∧
      actualRingCIPInput.executableOfficialCIPChildren node7 = [] ∧
      actualRingCIPInput.executableOfficialCIPChildren node8 = [] ∧
      actualRingCIPInput.executableOfficialCIPChildren duplicateNode = [] ∧
      duplicateNode.isDuplicateLeaf = true :=
  ⟨node2_children_in_arm, node4_children_in_arm, node3Children_eq, node6Children_eq,
    node7Children_eq, node8Children_eq, duplicateChildren_eq, duplicate_is_terminal⟩

/-! ## The physical edge-avoiding walk -/

/-- A physical walk from `start` to `target` whose every consecutive edge is a positive graph
adjacency and avoids the unordered cut edge `{forbiddenLeft, forbiddenRight}`. -/
def WalkAvoiding
    (forbiddenLeft forbiddenRight start target : actualRingCIPInput.Atom)
    (path : List actualRingCIPInput.Atom) : Prop :=
  path.head? = some start ∧
    path.getLast? = some target ∧
    List.IsChain
      (fun left right =>
        actualRingCIPInput.moleculeGraph.Adj left right ∧
          ¬ ((left = forbiddenLeft ∧ right = forbiddenRight) ∨
             (left = forbiddenRight ∧ right = forbiddenLeft)))
      path

/-- With the incoming edge `{0,2}` deleted, atom `1` remains physically reachable from the arm
start atom `2` by the walk `2 - 4 - 0 - 1`. -/
theorem physical_walk_avoids_cut :
    WalkAvoiding A0 A2 A2 A1 [A2, A4, A0, A1] := by
  refine ⟨rfl, rfl, ?_⟩
  exact List.IsChain.cons_cons (by decide +kernel)
    (List.IsChain.cons_cons (by decide +kernel)
      (List.IsChain.cons_cons (by decide +kernel) (List.IsChain.singleton A1)))

/-! ## The edge-cut surjectivity proposition is false -/

/-- Prospective coverage statement: every physical target reachable from the arm start after
deleting the incoming edge is the current atom of some actual reachable reroot cursor. -/
def EdgeCutCoverage
    (start previous : actualRingCIPInput.Atom) : Prop :=
  ∀ target,
    (∃ path, WalkAvoiding previous start start target path) →
      ∃ cursor,
        ArmReachable cursor ∧ cursor.occurrence.1.node.current? = some target

/-- **The proposed edge-cut surjectivity is false on the actual production fixture.** -/
theorem edgeCutCoverage_false :
    ¬ EdgeCutCoverage A2 A0 := by
  intro coverage
  obtain ⟨cursor, reachable, fluorine⟩ :=
    coverage A1 ⟨[A2, A4, A0, A1], physical_walk_avoids_cut⟩
  exact arm_current_ne_F reachable fluorine

/-! ## The same counterexample at an arbitrary carrier fuel

The concrete development above uses carrier fuel `2`.  To rule out a small-fuel truncation artifact,
the same start frame, cut invariant, closure step, and exclusion argument are repeated at an
arbitrary fuel.  The child enumerations are the intrinsic production enumerations proved above, so
the only fuel-dependent data are the `remaining` counters; the arm's official unfolding height is
at most three and every branch terminates in an intrinsically childless node.  In particular the
counterexample holds at the global adequate fuel `atomCount = 9`, and indeed at every fuel. -/

def rootFrameAt (fuel : Nat) :
    actualRingCIPInput.LocalizedCIPOccurrenceFrame :=
  { root := A0, address := [], node := rootNode, remaining := fuel + 1 }

def startFrameAt (fuel : Nat) :
    actualRingCIPInput.LocalizedCIPOccurrenceFrame :=
  { root := A0, address := [1], node := node2, remaining := fuel }

theorem rootFrameAt_declarative (fuel : Nat) :
    actualRingCIPInput.DeclarativeLocalizedOccurrence fuel (rootFrameAt fuel) := by
  change actualRingCIPInput.DeclarativeLocalizedOccurrenceSubtree A0 [] (fuel + 1)
    rootNode (rootFrameAt fuel)
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [] (fuel + 1) rootNode

theorem startFrameAt_declarative (fuel : Nat) :
    actualRingCIPInput.DeclarativeLocalizedOccurrence fuel (startFrameAt fuel) := by
  change actualRingCIPInput.DeclarativeLocalizedOccurrenceSubtree A0 [] (fuel + 1)
    rootNode (startFrameAt fuel)
  exact DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := fuel) (node := rootNode) (child := node2) (slot := 1)
    childAtRoot_arm
    (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot [1] fuel node2)

theorem rootFrameAt_mem (fuel : Nat) :
    rootFrameAt fuel ∈ actualRingCIPInput.localizedOccurrences fuel :=
  (actualRingCIPInput.mem_localizedOccurrences_iff fuel (rootFrameAt fuel)).mpr
    (rootFrameAt_declarative fuel)

theorem startFrameAt_mem (fuel : Nat) :
    startFrameAt fuel ∈ actualRingCIPInput.localizedOccurrences fuel :=
  (actualRingCIPInput.mem_localizedOccurrences_iff fuel (startFrameAt fuel)).mpr
    (startFrameAt_declarative fuel)

def occRootAt (fuel : Nat) : actualRingCIPInput.LocalizedCIPOccurrence fuel :=
  ⟨rootFrameAt fuel, rootFrameAt_mem fuel⟩

def occStartAt (fuel : Nat) : actualRingCIPInput.LocalizedCIPOccurrence fuel :=
  ⟨startFrameAt fuel, startFrameAt_mem fuel⟩

/-- The same real start atom `2` with real previous root `0`, at arbitrary carrier fuel. -/
def startCursorAt (fuel : Nat) :
    actualRingCIPInput.LocalizedRerootCursor fuel :=
  { occurrence := occStartAt fuel, previous? := some (occRootAt fuel) }

theorem startCursorAt_previous (fuel : Nat) :
    (startCursorAt fuel).previous? = some (occRootAt fuel) :=
  rfl

theorem startCursorAt_node (fuel : Nat) :
    NodeInArm (startCursorAt fuel).occurrence.1.node :=
  Or.inl rfl

theorem startCursorAt_cut (fuel : Nat) : CutInvariant (startCursorAt fuel) := by
  refine ⟨occRootAt fuel, rfl, ?_⟩
  rfl

theorem startCursorAt_nonduplicate (fuel : Nat) :
    (startCursorAt fuel).occurrence.1.node.isDuplicateLeaf = false := by
  simpa [startCursorAt, occStartAt, startFrameAt] using
    (by decide +kernel : node2.isDuplicateLeaf = false)

theorem startCursorAt_positive (fuel : Nat) (positive : 0 < fuel) :
    0 < (startCursorAt fuel).occurrence.1.remaining := by
  simpa [startCursorAt, occStartAt, startFrameAt] using positive

/-- At the lifted start cursor the recorded incoming address is the empty root address, so every
outward child address differs from it. -/
theorem startCursorAt_notIncoming (fuel slot : Nat) :
    ∀ previous,
      (startCursorAt fuel).previous? = some previous →
        (startCursorAt fuel).occurrence.1.address ++ [slot] ≠ previous.1.address := by
  intro previous previousEq
  have previousIdentity : previous = occRootAt fuel := by
    have same : some previous = some (occRootAt fuel) :=
      previousEq.symm.trans (startCursorAt_previous fuel)
    exact Option.some.inj same
  subst previous
  change ([1] : List Nat) ++ [slot] ≠ []
  simp

/-- At every positive carrier fuel the lifted start cursor still actually reaches the chlorine
`Cl3` through the production reroot expansion. -/
theorem arm_reaches_cl3_at (fuel : Nat) (positive : 0 < fuel) :
    ∃ cursor : actualRingCIPInput.LocalizedRerootCursor fuel,
      ReachableFrom (startCursorAt fuel) cursor ∧
        cursor.occurrence.1.node.current? = some A3 := by
  obtain ⟨next, reachable, nextFrame, _nextPrevious⟩ :=
    reachable_executable_child_at (startCursorAt fuel) ReachableFrom.refl
      (startCursorAt_nonduplicate fuel) (startCursorAt_positive fuel positive)
      node3 0 childAtArm_three (startCursorAt_notIncoming fuel 0)
  refine ⟨next, reachable, ?_⟩
  rw [nextFrame]
  rfl

/-- At every positive carrier fuel the lifted arm actually reaches the ring carbon `C4`. -/
theorem arm_reaches_c4_at (fuel : Nat) (positive : 0 < fuel) :
    ∃ cursor : actualRingCIPInput.LocalizedRerootCursor fuel,
      ReachableFrom (startCursorAt fuel) cursor ∧
        cursor.occurrence.1.node.current? = some A4 := by
  obtain ⟨next, reachable, nextFrame, _nextPrevious⟩ :=
    reachable_executable_child_at (startCursorAt fuel) ReachableFrom.refl
      (startCursorAt_nonduplicate fuel) (startCursorAt_positive fuel positive)
      node4 1 childAtArm_four (startCursorAt_notIncoming fuel 1)
  refine ⟨next, reachable, ?_⟩
  rw [nextFrame]
  rfl

/-- At every positive carrier fuel the lifted arm actually reaches the hydrogen `H6`. -/
theorem arm_reaches_h6_at (fuel : Nat) (positive : 0 < fuel) :
    ∃ cursor : actualRingCIPInput.LocalizedRerootCursor fuel,
      ReachableFrom (startCursorAt fuel) cursor ∧
        cursor.occurrence.1.node.current? = some A6 := by
  obtain ⟨next, reachable, nextFrame, _nextPrevious⟩ :=
    reachable_executable_child_at (startCursorAt fuel) ReachableFrom.refl
      (startCursorAt_nonduplicate fuel) (startCursorAt_positive fuel positive)
      node6 2 childAtArm_six (startCursorAt_notIncoming fuel 2)
  refine ⟨next, reachable, ?_⟩
  rw [nextFrame]
  rfl

/-- At every carrier fuel above one the lifted arm actually reaches the duplicate of original
root atom `0`. -/
theorem arm_reaches_duplicate0_at (fuel : Nat) (enough : 1 < fuel) :
    ∃ cursor : actualRingCIPInput.LocalizedRerootCursor fuel,
      ReachableFrom (startCursorAt fuel) cursor ∧
        cursor.occurrence.1.node.current? = some A0 := by
  have positive : 0 < fuel := by omega
  obtain ⟨four, fourReachable, fourFrame, fourPrevious⟩ :=
    reachable_executable_child_at (startCursorAt fuel) ReachableFrom.refl
      (startCursorAt_nonduplicate fuel) (startCursorAt_positive fuel positive)
      node4 1 childAtArm_four (startCursorAt_notIncoming fuel 1)
  have fourNonduplicate : four.occurrence.1.node.isDuplicateLeaf = false := by
    rw [fourFrame]
    change node4.isDuplicateLeaf = false
    decide +kernel
  have fourPositive : 0 < four.occurrence.1.remaining := by
    rw [fourFrame]
    show 0 < fuel - 1
    omega
  obtain ⟨next, reachable, nextFrame, _nextPrevious⟩ :=
    reachable_executable_child_at four fourReachable fourNonduplicate fourPositive
      duplicateNode 0
      (by
        rw [fourFrame]
        exact childAtFour_duplicate)
      (by
        intro previous previousEq
        have previousIdentity : previous = occStartAt fuel := by
          have same : some previous = some (occStartAt fuel) :=
            previousEq.symm.trans fourPrevious
          exact Option.some.inj same
        subst previous
        rw [fourFrame]
        intro addressEq
        have lengthEq := congrArg List.length addressEq
        simp [startCursorAt, occStartAt, startFrameAt] at lengthEq)
  refine ⟨next, reachable, ?_⟩
  rw [nextFrame]
  rfl

/-- The closure invariant holds at every position reachable from any start cursor satisfying the
start node-set and cut invariants, at any carrier fuel. -/
theorem reachableFrom_invariant {fuel : Nat}
    {start : actualRingCIPInput.LocalizedRerootCursor fuel}
    (startNode : NodeInArm start.occurrence.1.node)
    (startCut : CutInvariant start)
    {cursor : actualRingCIPInput.LocalizedRerootCursor fuel}
    (reachable : ReachableFrom start cursor) :
    NodeInArm cursor.occurrence.1.node ∧ CutInvariant cursor := by
  induction reachable with
  | refl => exact ⟨startNode, startCut⟩
  | step _ stepInvariant inductionHypothesis =>
      exact arm_step inductionHypothesis.1 inductionHypothesis.2 stepInvariant

/-- No actual reachable arm position carries the fluorine atom `1`, at any carrier fuel. -/
theorem reachableFrom_current_ne_F {fuel : Nat}
    {start : actualRingCIPInput.LocalizedRerootCursor fuel}
    (startNode : NodeInArm start.occurrence.1.node)
    (startCut : CutInvariant start)
    {cursor : actualRingCIPInput.LocalizedRerootCursor fuel}
    (reachable : ReachableFrom start cursor) :
    cursor.occurrence.1.node.current? ≠ some A1 :=
  NodeInArm.current_ne_F (reachableFrom_invariant startNode startCut reachable).1

/-- Fuel-parametric edge-cut coverage proposition for the fixed-origin outward arm. -/
def EdgeCutCoverageAt {fuel : Nat}
    (start : actualRingCIPInput.LocalizedRerootCursor fuel)
    (startAtom previous : actualRingCIPInput.Atom) : Prop :=
  ∀ target,
    (∃ path, WalkAvoiding previous startAtom startAtom target path) →
      ∃ cursor,
        ReachableFrom start cursor ∧ cursor.occurrence.1.node.current? = some target

/-- **The proposed edge-cut surjectivity fails at every carrier fuel.**  The physical walk
`2 - 4 - 0 - 1` avoids the cut edge `{0,2}`, but no reachable outward arm position carries atom
`1`, independently of how much carrier fuel is supplied. -/
theorem edgeCutCoverageAt_false (fuel : Nat) :
    ¬ EdgeCutCoverageAt (startCursorAt fuel) A2 A0 := by
  intro coverage
  obtain ⟨cursor, reachable, fluorine⟩ :=
    coverage A1 ⟨[A2, A4, A0, A1], physical_walk_avoids_cut⟩
  exact reachableFrom_current_ne_F (startCursorAt_node fuel) (startCursorAt_cut fuel)
    reachable fluorine

/-- The actual global carrier fuel, taken to be the molecule's atom count. -/
def globalCarrierFuel : Nat :=
  actualRingCIPInput.certified.input.molecule.atomCount

theorem globalCarrierFuel_eq : globalCarrierFuel = 9 :=
  actualRingCIPInput_atomCount

/-- The counterexample at the global adequate fuel `9`, strictly above the arm's unfolding height
three. -/
theorem edgeCutCoverage_false_global :
    ¬ EdgeCutCoverageAt (startCursorAt globalCarrierFuel) A2 A0 :=
  edgeCutCoverageAt_false globalCarrierFuel

/-- The counterexample at the concrete carrier fuel `2` used by the displayed frames. -/
theorem edgeCutCoverageAt_false_two :
    ¬ EdgeCutCoverageAt (startCursorAt 2) A2 A0 :=
  edgeCutCoverageAt_false 2

theorem globalCarrierFuel_positive : 0 < globalCarrierFuel := by
  rw [globalCarrierFuel_eq]
  decide +kernel

theorem globalCarrierFuel_gt_one : 1 < globalCarrierFuel := by
  rw [globalCarrierFuel_eq]
  decide +kernel

/-- At the global fuel `9`, the actual outward arm reaches the chlorine `Cl3`. -/
theorem arm_global_reaches_cl3 :
    ∃ cursor : actualRingCIPInput.LocalizedRerootCursor globalCarrierFuel,
      ReachableFrom (startCursorAt globalCarrierFuel) cursor ∧
        cursor.occurrence.1.node.current? = some A3 :=
  arm_reaches_cl3_at globalCarrierFuel globalCarrierFuel_positive

/-- At the global fuel `9`, the actual outward arm reaches the ring carbon `C4`. -/
theorem arm_global_reaches_c4 :
    ∃ cursor : actualRingCIPInput.LocalizedRerootCursor globalCarrierFuel,
      ReachableFrom (startCursorAt globalCarrierFuel) cursor ∧
        cursor.occurrence.1.node.current? = some A4 :=
  arm_reaches_c4_at globalCarrierFuel globalCarrierFuel_positive

/-- At the global fuel `9`, the actual outward arm reaches the hydrogen `H6`. -/
theorem arm_global_reaches_h6 :
    ∃ cursor : actualRingCIPInput.LocalizedRerootCursor globalCarrierFuel,
      ReachableFrom (startCursorAt globalCarrierFuel) cursor ∧
        cursor.occurrence.1.node.current? = some A6 :=
  arm_reaches_h6_at globalCarrierFuel globalCarrierFuel_positive

/-- At the global fuel `9`, the actual outward arm reaches the duplicate of original root atom
`0`; the duplicate is intrinsically terminal. -/
theorem arm_global_reaches_duplicate0 :
    ∃ cursor : actualRingCIPInput.LocalizedRerootCursor globalCarrierFuel,
      ReachableFrom (startCursorAt globalCarrierFuel) cursor ∧
        cursor.occurrence.1.node.current? = some A0 :=
  arm_reaches_duplicate0_at globalCarrierFuel globalCarrierFuel_gt_one

end TetraStereo.OneCenter.RingEdgeCut

assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.ringSource_structurallyWellFormed
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.ringSource_graphReady
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.actualRingCIPInput_atomCount
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.atom_val
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.rootNode_current
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node2_current
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node3_current
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node4_current
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node6_current
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.duplicateNode_current
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node7_current
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node8_current
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.rootChildren_eq
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node2Children_eq
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node4Children_eq
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node3Children_eq
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node6Children_eq
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node7Children_eq
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node8Children_eq
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.duplicateChildren_eq
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.duplicate_is_terminal
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.childAtRoot_arm
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.childAtArm_three
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.childAtArm_four
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.childAtArm_six
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.childAtFour_duplicate
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.childAtFour_seven
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.childAtFour_eight
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.rootFrame_declarative
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startFrame_declarative
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.threeFrame_declarative
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.fourFrame_declarative
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.sixFrame_declarative
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.duplicateFrame_declarative
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.sevenFrame_declarative
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.eightFrame_declarative
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.rootFrame_mem
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startFrame_mem
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.threeFrame_mem
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.fourFrame_mem
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.sixFrame_mem
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.duplicateFrame_mem
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.sevenFrame_mem
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.eightFrame_mem
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startCursor_previous
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startCursor_current_exists
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.eq_append_singleton_of_dropLast_eq_of_length_eq
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.start_cut
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.start_node
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_step
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.reachable_invariant
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.NodeInArm.current_mem
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.NodeInArm.current_ne_F
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_current_ne_F
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.reachable_executable_child
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_reaches_cl3
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_reaches_c4
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_reaches_h6
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_reaches_duplicate0
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_duplicate_terminal
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node2_children_in_arm
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node4_children_in_arm
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_intrinsic_closure
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.physical_walk_avoids_cut
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.edgeCutCoverage_false
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.rootFrameAt_declarative
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startFrameAt_declarative
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.rootFrameAt_mem
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startFrameAt_mem
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startCursorAt_previous
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startCursorAt_node
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startCursorAt_cut
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.reachableFrom_invariant
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.reachableFrom_current_ne_F
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.edgeCutCoverageAt_false
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.globalCarrierFuel_eq
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.edgeCutCoverage_false_global
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.edgeCutCoverageAt_false_two
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.reachable_executable_child_at
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startCursorAt_nonduplicate
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startCursorAt_positive
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startCursorAt_notIncoming
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_reaches_cl3_at
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_reaches_c4_at
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_reaches_h6_at
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_reaches_duplicate0_at
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.globalCarrierFuel_positive
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.globalCarrierFuel_gt_one
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_global_reaches_cl3
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_global_reaches_c4
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_global_reaches_h6
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.arm_global_reaches_duplicate0
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.RingExpanded
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.RingSource
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.actualRingCIPInput
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.atom
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.A0
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.A1
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.A2
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.A3
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.A4
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.A5
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.A6
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.A7
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.A8
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.rootNode
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node1
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node2
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node4RootChild
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node5
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node3
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node4
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node6
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.duplicateNode
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node7
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.node8
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.rootFrame
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startFrame
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.threeFrame
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.fourFrame
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.sixFrame
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.duplicateFrame
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.sevenFrame
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.eightFrame
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.occRoot
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.occStart
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.occThree
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.occFour
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.occSix
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.occDuplicate
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.occSeven
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.occEight
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startCursor
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.CursorStep
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.ArmReachable
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.ReachableFrom
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.NodeInArm
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.CutInvariant
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.WalkAvoiding
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.EdgeCutCoverage
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.rootFrameAt
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startFrameAt
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.occRootAt
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.occStartAt
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.startCursorAt
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.EdgeCutCoverageAt
assert_kernel_only
  TetraStereo.OneCenter.RingEdgeCut.globalCarrierFuel
