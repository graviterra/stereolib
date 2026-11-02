import TetraStereo.OneCenter.LocalizedAcyclicBranchCarrier
import Mathlib.Data.Fintype.Card
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Injectivity of the physical carrier occurrence coordinate at a fixed root

This module proves the central uniqueness statement for the actual finite localized CIP
occurrence carrier on the honest chemical domain: a certified localized CIP input whose positive
bond orders are all one (`MoleculeGraph.SimpleBonded`) and whose underlying simple graph is
acyclic (`MoleculeGraph.Acyclic`).

The occurrence carrier intentionally spans several original roots: the same physical atom can
occur below different final centers, in different sibling addresses, or with different histories.
Consequently no global injectivity statement on atoms is true or claimed here.  The exact result
proved below is rooted:

* `localizedCIPOccurrence_current_injective_at_fixedRoot`: two actual carrier occurrences at the
  same fuel with the same stored original root and the same physical `current?` atom are equal.

The proof is built on the F137B physical branch result `carrierOccurrence_realPath` (hash
`89715dbf2aa4fecac702ce545084fe17106730320a4d34472375e5b13f652c7f`): every actual carrier
occurrence at any fuel is a real simple physical path whose reversed walk support is exactly its
stored `history`.  We reuse that theorem rather than repeat its real-path induction.

The only additional graph-theoretic input is `MoleculeGraph.acyclic_path_unique`, which makes the
reversed support, hence the whole stored `history`, determined by the root and the final physical
atom.  Sibling address uniqueness is obtained from the deterministic executable child list and
the single executable copy slot of each physical edge; it is proved locally along the two
occurrence derivations rather than assumed as an address certificate.  No noduplicate-children
hypothesis and no completeness/surjectivity hypothesis is used.

What is deliberately *not* claimed here: full physical coverage/surjectivity of the carrier, any
directed cut or reroot correspondence, and any cardinal-fuel completeness statement.  Those remain
the responsibility of the F137B coverage development.  This module only establishes injectivity at
a fixed original root and the immediate finite consequences of that injectivity.

The public declarations are kernel-authority guarded at the end of the file.
-/

namespace TetraStereo
namespace OneCenter

namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-- The part of `RealPathNode` needed for history uniqueness: an actual simple physical walk from
the root whose reversed support is the stored history, together with real provenance.  This is a
deliberately weaker predicate than `RealPathNode`; the stored parent condition is not needed for
the uniqueness argument. -/
def RealRootedPath (root : input.Atom) (node : OfficialCIPNode input.Atom) : Prop :=
  ∃ (current : input.Atom)
      (path : input.moleculeGraph.underlyingSimpleGraph.Walk root current),
    node.current? = some current ∧
      node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      path.IsPath ∧
      path.support.reverse = node.history

/-- The root node is a real empty physical path. -/
theorem realRootedPath_root (root : input.Atom) :
    input.RealRootedPath root (OfficialCIPNode.root root) := by
  refine ⟨root, SimpleGraph.Walk.nil, rfl, rfl, by simp, ?_⟩
  simp [OfficialCIPNode.root]

/-- Every `RealPathNode` is in particular a rooted real simple path. -/
theorem realPathNode_to_rooted
    {root : input.Atom} {node : OfficialCIPNode input.Atom}
    (real : input.RealPathNode root node) :
    input.RealRootedPath root node := by
  obtain ⟨current, path, observed, _head, provenance, isPath, support, _penultimate⟩ := real
  exact ⟨current, path, observed, provenance, isPath, support⟩

/-- The provenance of a real path node is real. -/
theorem realPathNode_provenance
    {root : input.Atom} {node : OfficialCIPNode input.Atom}
    (real : input.RealPathNode root node) :
    node.provenance = OfficialCIPNodeProvenance.realAtom := by
  obtain ⟨_current, _path, _observed, _head, provenance, _isPath, _support, _penultimate⟩ := real
  exact provenance

/-- **A rooted physical atom determines the stored history.**  In an acyclic graph there is at
most one simple path between two vertices; hence two real rooted simple paths ending at the same
physical atom have the same reversed support and therefore the same stored history. -/
theorem realRootedPath_history_eq_of_current_eq
    (acyclic : input.moleculeGraph.Acyclic)
    {root : input.Atom} {left right : OfficialCIPNode input.Atom}
    (leftReal : input.RealRootedPath root left)
    (rightReal : input.RealRootedPath root right)
    (sameCurrent : left.current? = right.current?) :
    left.history = right.history := by
  obtain ⟨leftCurrent, leftPath, leftObserved, _leftProvenance, leftSimple,
    leftSupport⟩ := leftReal
  obtain ⟨rightCurrent, rightPath, rightObserved, _rightProvenance, rightSimple,
    rightSupport⟩ := rightReal
  have sameAtom : leftCurrent = rightCurrent :=
    Option.some.inj (leftObserved.symm.trans (sameCurrent.trans rightObserved))
  subst rightCurrent
  have pathEq : leftPath = rightPath := by
    have packageEq :
        (⟨leftPath, leftSimple⟩ :
            input.moleculeGraph.underlyingSimpleGraph.Path root leftCurrent) =
          ⟨rightPath, rightSimple⟩ :=
      MoleculeGraph.acyclic_path_unique input.moleculeGraph acyclic _ _
    exact congrArg Subtype.val packageEq
  rw [← leftSupport, ← rightSupport, pathEq]

/-- `RealPathNode` version of rooted history uniqueness. -/
theorem realPathNode_history_eq_of_current_eq
    (acyclic : input.moleculeGraph.Acyclic)
    {root : input.Atom} {left right : OfficialCIPNode input.Atom}
    (leftReal : input.RealPathNode root left)
    (rightReal : input.RealPathNode root right)
    (sameCurrent : left.current? = right.current?) :
    left.history = right.history :=
  input.realRootedPath_history_eq_of_current_eq acyclic
    (input.realPathNode_to_rooted leftReal)
    (input.realPathNode_to_rooted rightReal) sameCurrent

/-- Along a declarative occurrence subtree the starting history is a suffix of the occurrence
history.  Each executable child step prepends exactly the child's physical atom to the stored
history. -/
theorem declarativeLocalizedOccurrenceSubtree_history_suffix
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence) :
    node.history <:+ occurrence.node.history := by
  induction derived with
  | subtreeRoot => exact List.suffix_rfl
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot descendant ih =>
      have childPresent : child ∈ input.executableOfficialCIPChildren node :=
        List.fst_mem_of_mem_zipIdx childAtSlot
      have step : node.history <:+ child.history := by
        by_cases duplicate : node.isDuplicateLeaf = true
        · have empty : input.executableOfficialCIPChildren node = [] := by
            simp [executableOfficialCIPChildren, duplicate]
          rw [empty] at childPresent
          simp at childPresent
        · unfold executableOfficialCIPChildren at childPresent
          rw [if_neg duplicate, List.mem_map] at childPresent
          obtain ⟨copy, _copyPresent, childIdentity⟩ := childPresent
          obtain ⟨next, copyIndex⟩ := copy
          change node.extend next copyIndex = child at childIdentity
          rw [← childIdentity, OfficialCIPNode.extend_history]
          exact List.suffix_cons next node.history
      exact step.trans ih

/-- Exact history length grading along a declarative occurrence subtree.  If the subtree root's
history length is one more than its address length, then the same relation holds at every
executable descendant.  This does not use simplicity of the graph: every child step, including a
duplicate step, prepends exactly one atom. -/
theorem declarativeLocalizedOccurrenceSubtree_history_length
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence)
    (aligned : node.history.length = path.length + 1) :
    occurrence.node.history.length = occurrence.address.length + 1 := by
  induction derived with
  | subtreeRoot => exact aligned
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot descendant ih =>
      have childPresent : child ∈ input.executableOfficialCIPChildren node :=
        List.fst_mem_of_mem_zipIdx childAtSlot
      have childLength : child.history.length = node.history.length + 1 :=
        input.executableOfficialCIPChildren_history_length node child childPresent
      apply ih
      rw [childLength, aligned]
      simp only [List.length_append, List.length_singleton]

/-- A child of a real-rooted declarative occurrence is itself real whenever the occurrence below it
is a real path node, or whenever that child has any executable child at all.  The only obstruction
would be duplicate provenance, which makes the executable child list empty; the occurrence being a
real path node rules out that obstruction at a leaf. -/
theorem childProvenance_real_of_descendant
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node child : OfficialCIPNode input.Atom} {slot : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (childAtSlot : (child, slot) ∈
      (input.executableOfficialCIPChildren node).zipIdx)
    (descendant : input.DeclarativeLocalizedOccurrenceSubtree root
      (path ++ [slot]) fuel child occurrence)
    (occProvenance : occurrence.node.provenance =
      OfficialCIPNodeProvenance.realAtom) :
    child.provenance = OfficialCIPNodeProvenance.realAtom := by
  cases descendant with
  | subtreeRoot =>
      simpa using occProvenance
  | @subtreeDescendant _ _ _ grandchild grandSlot _ grandAtSlot _ =>
      have grandPresent : grandchild ∈ input.executableOfficialCIPChildren child :=
        List.fst_mem_of_mem_zipIdx grandAtSlot
      have childPresent : child ∈ input.executableOfficialCIPChildren node :=
        List.fst_mem_of_mem_zipIdx childAtSlot
      have notNodeDuplicate : node.isDuplicateLeaf = false := by
        cases duplicate : node.isDuplicateLeaf with
        | false => rfl
        | true =>
            have empty : input.executableOfficialCIPChildren node = [] := by
              simp [executableOfficialCIPChildren, duplicate]
            rw [empty] at childPresent
            simp at childPresent
      unfold executableOfficialCIPChildren at childPresent
      rw [if_neg (by simpa using notNodeDuplicate), List.mem_map] at childPresent
      obtain ⟨copy, _copyPresent, childIdentity⟩ := childPresent
      obtain ⟨next, copyIndex⟩ := copy
      change node.extend next copyIndex = child at childIdentity
      rw [← childIdentity, OfficialCIPNode.extend_provenance]
      by_cases positive : copyIndex = 0
      · subst copyIndex
        by_cases visited : next ∈ node.history
        · rw [OfficialCIPNode.childProvenance_ring_duplicate node next visited]
          exfalso
          have childDuplicate : child.isDuplicateLeaf = true := by
            rw [OfficialCIPNode.isDuplicateLeaf, ← childIdentity,
              OfficialCIPNode.extend_provenance,
              OfficialCIPNode.childProvenance_ring_duplicate node next visited]
            rfl
          have empty : input.executableOfficialCIPChildren child = [] := by
            simp [executableOfficialCIPChildren, childDuplicate]
          rw [empty] at grandPresent
          simp at grandPresent
        · exact OfficialCIPNode.childProvenance_real node next visited
      · rw [OfficialCIPNode.childProvenance_copy_pos node next positive]
        exfalso
        have childDuplicate : child.isDuplicateLeaf = true := by
          rw [OfficialCIPNode.isDuplicateLeaf, ← childIdentity,
            OfficialCIPNode.extend_provenance,
            OfficialCIPNode.childProvenance_copy_pos node next positive]
          rfl
        have empty : input.executableOfficialCIPChildren child = [] := by
          simp [executableOfficialCIPChildren, childDuplicate]
        rw [empty] at grandPresent
        simp at grandPresent

/-- A strictly deeper occurrence in the same rooted subtree cannot have the same physical
`current?` atom as the subtree root.  Its history strictly extends the root history by the exact
history grading, while acyclicity forces equal histories at equal physical atoms. -/
theorem descendant_current_ne_root
    (acyclic : input.moleculeGraph.Acyclic)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (rooted : input.RealRootedPath root node)
    (aligned : node.history.length = path.length + 1)
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence)
    (descended : path.length < occurrence.address.length)
    (real : input.RealPathNode root occurrence.node)
    (sameCurrent : node.current? = occurrence.node.current?) :
    False := by
  have occurrenceLength :=
    input.declarativeLocalizedOccurrenceSubtree_history_length derived aligned
  have strict : node.history.length < occurrence.node.history.length := by
    rw [aligned, occurrenceLength]
    omega
  have historiesEq : node.history = occurrence.node.history :=
    input.realRootedPath_history_eq_of_current_eq acyclic rooted
      (input.realPathNode_to_rooted real) sameCurrent
  rw [historiesEq] at strict
  exact absurd strict (Nat.lt_irrefl _)

/-- **Rooted occurrence determination.**  Two declarative actual occurrences at the same subtree
root, the same fuel, the same stored root atom and the same physical `current?` atom are equal.
The induction follows the two simultaneous derivations.  At every simultaneous step the physical
`current?` is the same, so acyclicity makes the two occurrence histories equal; history grading
then makes the two immediate child histories equal, hence their extended nodes and their executable
sibling slots are equal, and the induction hypothesis applies below the common child.

The provenance hypotheses `leftReal`/`rightReal` are the F137B real-path facts for the two final
occurrence nodes.  They are used only to exclude the empty duplicate-leaf branches. -/
theorem declarativeLocalizedOccurrenceSubtree_determined_of_current
    (acyclic : input.moleculeGraph.Acyclic)
    {root : input.Atom} :
    ∀ {fuel : Nat} {path : List Nat} {node : OfficialCIPNode input.Atom}
      {left right : input.LocalizedCIPOccurrenceFrame},
      input.RealRootedPath root node →
      node.history.length = path.length + 1 →
      input.DeclarativeLocalizedOccurrenceSubtree root path fuel node left →
      input.DeclarativeLocalizedOccurrenceSubtree root path fuel node right →
      input.RealPathNode root left.node →
      input.RealPathNode root right.node →
      left.node.current? = right.node.current? →
      left = right := by
  intro fuel
  induction fuel with
  | zero =>
      intro path node left right rooted aligned leftDerived rightDerived
        leftReal rightReal sameCurrent
      cases leftDerived with
      | subtreeRoot =>
          cases rightDerived with
          | subtreeRoot => rfl
  | succ fuel ih =>
      intro path node left right rooted aligned leftDerived rightDerived
        leftReal rightReal sameCurrent
      cases leftDerived with
      | subtreeRoot =>
          cases rightDerived with
          | subtreeRoot => rfl
          | @subtreeDescendant _ _ _ rightChild rightSlot _ rightAtSlot rightBelow =>
              exfalso
              have pathPrefix :=
                input.declarativeLocalizedOccurrenceSubtree_addressPrefix rightBelow
              have descended : path.length < right.address.length := by
                have lengthLe := pathPrefix.length_le
                simp only [List.length_append, List.length_singleton] at lengthLe
                omega
              exact input.descendant_current_ne_root acyclic rooted aligned
                (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
                  rightAtSlot rightBelow)
                descended rightReal sameCurrent
      | @subtreeDescendant _ _ _ leftChild leftSlot _ leftAtSlot leftBelow =>
          cases rightDerived with
          | subtreeRoot =>
              exfalso
              have pathPrefix :=
                input.declarativeLocalizedOccurrenceSubtree_addressPrefix leftBelow
              have descended : path.length < left.address.length := by
                have lengthLe := pathPrefix.length_le
                simp only [List.length_append, List.length_singleton] at lengthLe
                omega
              exact input.descendant_current_ne_root acyclic rooted aligned
                (DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
                  leftAtSlot leftBelow)
                descended leftReal sameCurrent.symm
          | @subtreeDescendant _ _ _ rightChild rightSlot _ rightAtSlot rightBelow =>
              obtain ⟨nodeCurrent, nodeWalk, nodeCurrentObserved, _nodeProvenance,
                nodeWalkIsPath, nodeSupport⟩ := rooted
              have leftPresent : leftChild ∈
                  input.executableOfficialCIPChildren node :=
                List.fst_mem_of_mem_zipIdx leftAtSlot
              have rightPresent : rightChild ∈
                  input.executableOfficialCIPChildren node :=
                List.fst_mem_of_mem_zipIdx rightAtSlot
              have leftOccurrenceProvenance :
                  left.node.provenance = OfficialCIPNodeProvenance.realAtom :=
                input.realPathNode_provenance leftReal
              have rightOccurrenceProvenance :
                  right.node.provenance = OfficialCIPNodeProvenance.realAtom :=
                input.realPathNode_provenance rightReal
              have leftChildReal :
                  leftChild.provenance = OfficialCIPNodeProvenance.realAtom :=
                input.childProvenance_real_of_descendant leftAtSlot leftBelow
                  leftOccurrenceProvenance
              have rightChildReal :
                  rightChild.provenance = OfficialCIPNodeProvenance.realAtom :=
                input.childProvenance_real_of_descendant rightAtSlot rightBelow
                  rightOccurrenceProvenance
              obtain ⟨leftNext, leftEq, _leftNotParent⟩ :=
                input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
                  node leftChild leftPresent (Or.inl leftChildReal)
              obtain ⟨rightNext, rightEq, _rightNotParent⟩ :=
                input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
                  node rightChild rightPresent (Or.inl rightChildReal)
              have leftAdjacent : input.moleculeGraph.Adj nodeCurrent leftNext :=
                input.adj_of_mem_executableOfficialCIPChildren node leftChild
                  nodeCurrent leftNext nodeCurrentObserved (by rw [leftEq]; rfl)
                  leftPresent
              have leftChildHistoryEq : leftChild.history = leftNext :: node.history := by
                rw [leftEq, OfficialCIPNode.extend_history]
              have rightChildHistoryEq : rightChild.history = rightNext :: node.history := by
                rw [rightEq, OfficialCIPNode.extend_history]
              have leftSuffix : leftChild.history <:+ left.node.history :=
                input.declarativeLocalizedOccurrenceSubtree_history_suffix leftBelow
              have rightSuffix : rightChild.history <:+ right.node.history :=
                input.declarativeLocalizedOccurrenceSubtree_history_suffix rightBelow
              have historiesEq : left.node.history = right.node.history :=
                input.realPathNode_history_eq_of_current_eq acyclic leftReal rightReal
                  sameCurrent
              have leftChildLength :
                  leftChild.history.length = node.history.length + 1 :=
                input.executableOfficialCIPChildren_history_length node leftChild
                  leftPresent
              have rightChildLength :
                  rightChild.history.length = node.history.length + 1 :=
                input.executableOfficialCIPChildren_history_length node rightChild
                  rightPresent
              have childHistoriesEq : leftChild.history = rightChild.history := by
                have leftDrop := List.suffix_iff_eq_drop.mp leftSuffix
                have rightDrop := List.suffix_iff_eq_drop.mp rightSuffix
                calc leftChild.history
                    = left.node.history.drop
                        (left.node.history.length - leftChild.history.length) :=
                      leftDrop
                  _ = right.node.history.drop
                        (right.node.history.length - rightChild.history.length) := by
                      rw [historiesEq, leftChildLength, rightChildLength]
                  _ = rightChild.history := rightDrop.symm
              have nextEq : leftNext = rightNext := by
                have consEq : leftNext :: node.history = rightNext :: node.history := by
                  rw [← leftChildHistoryEq, ← rightChildHistoryEq]
                  exact childHistoriesEq
                exact (List.cons.inj consEq).1
              have childEq : leftChild = rightChild := by
                rw [leftEq, rightEq, nextEq]
              have rightAtSlot' : (leftChild, rightSlot) ∈
                  (input.executableOfficialCIPChildren node).zipIdx := by
                simpa [childEq] using rightAtSlot
              have slotEq : leftSlot = rightSlot :=
                input.physical_executableOfficialCIPChild_slot_unique node leftChild
                  leftSlot rightSlot leftAtSlot rightAtSlot' (Or.inl leftChildReal)
              have leftChildProvenance :
                  node.childProvenance leftNext 0 =
                    OfficialCIPNodeProvenance.realAtom := by
                have real := leftChildReal
                rwa [leftEq, OfficialCIPNode.extend_provenance] at real
              have leftRooted : input.RealRootedPath root leftChild := by
                refine ⟨leftNext, nodeWalk.concat leftAdjacent, ?_, ?_, ?_, ?_⟩
                · rw [leftEq]
                  rfl
                · rw [leftEq, OfficialCIPNode.extend_provenance]
                  exact leftChildProvenance
                · refine nodeWalkIsPath.concat ?_ leftAdjacent
                  intro present
                  have memHistory : leftNext ∈ node.history := by
                    rw [← nodeSupport]
                    exact List.mem_reverse.mpr present
                  have ring :=
                    OfficialCIPNode.childProvenance_ring_duplicate node leftNext
                      memHistory
                  rw [ring] at leftChildProvenance
                  simp at leftChildProvenance
                · simp [SimpleGraph.Walk.support_concat, nodeSupport,
                    leftChildHistoryEq]
              have alignedNew :
                  leftChild.history.length = (path ++ [leftSlot]).length + 1 := by
                rw [leftChildLength, aligned]
                simp only [List.length_append, List.length_singleton]
              rw [← slotEq, ← childEq] at rightBelow
              exact ih leftRooted alignedNew leftBelow rightBelow leftReal rightReal
                sameCurrent

/-- **Actual carrier occurrence uniqueness at a fixed original root.**  Two actual finite
occurrences at the same fuel with the same stored original root and the same physical `current?`
atom are the same occurrence.

Root equality is essential: the carrier quantifies over occurrences below all original roots, and
the same atom genuinely occurs at different rooted coordinates.  No global atom injectivity is
claimed. -/
theorem localizedCIPOccurrence_current_injective_at_fixedRoot
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (a b : input.LocalizedCIPOccurrence fuel)
    (sameRoot : a.1.root = b.1.root)
    (sameCurrent : a.1.node.current? = b.1.node.current?) :
    a = b := by
  rcases a with ⟨⟨aRoot, aAddress, aNode, aRemaining⟩, aMember⟩
  rcases b with ⟨⟨bRoot, bAddress, bNode, bRemaining⟩, bMember⟩
  cases sameRoot
  have aDerived : input.DeclarativeLocalizedOccurrenceSubtree aRoot [] (fuel + 1)
      (OfficialCIPNode.root aRoot)
      { root := aRoot, address := aAddress, node := aNode, remaining := aRemaining } :=
    (input.mem_localizedOccurrences_iff fuel
      { root := aRoot, address := aAddress, node := aNode, remaining := aRemaining }).mp
      aMember
  have bDerived : input.DeclarativeLocalizedOccurrenceSubtree aRoot [] (fuel + 1)
      (OfficialCIPNode.root aRoot)
      { root := aRoot, address := bAddress, node := bNode, remaining := bRemaining } :=
    (input.mem_localizedOccurrences_iff fuel
      { root := aRoot, address := bAddress, node := bNode, remaining := bRemaining }).mp
      bMember
  have frameEq :
      ({ root := aRoot, address := aAddress, node := aNode, remaining := aRemaining } :
        input.LocalizedCIPOccurrenceFrame) =
        ({ root := aRoot, address := bAddress, node := bNode, remaining := bRemaining } :
          input.LocalizedCIPOccurrenceFrame) :=
    input.declarativeLocalizedOccurrenceSubtree_determined_of_current acyclic
      (fuel := fuel + 1) (path := []) (node := OfficialCIPNode.root aRoot)
      (left := { root := aRoot, address := aAddress, node := aNode, remaining := aRemaining })
      (right := { root := aRoot, address := bAddress, node := bNode, remaining := bRemaining })
      (input.realRootedPath_root aRoot)
      (by simp [OfficialCIPNode.root])
      aDerived bDerived
      (input.carrierOccurrence_realPath singleBonded acyclic
        ⟨{ root := aRoot, address := aAddress, node := aNode, remaining := aRemaining },
          aMember⟩)
      (input.carrierOccurrence_realPath singleBonded acyclic
        ⟨{ root := aRoot, address := bAddress, node := bNode, remaining := bRemaining },
          bMember⟩)
      sameCurrent
  exact Subtype.ext frameEq

/-- Occurrence identity from equality of the stored original root and of the whole official node.
This is the node-level form of the fixed-root injectivity theorem. -/
theorem localizedCIPOccurrence_node_injective_at_fixedRoot
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (a b : input.LocalizedCIPOccurrence fuel)
    (sameRoot : a.1.root = b.1.root)
    (sameNode : a.1.node = b.1.node) :
    a = b := by
  apply input.localizedCIPOccurrence_current_injective_at_fixedRoot singleBonded
    acyclic a b sameRoot
  rw [sameNode]

/-- At a fixed original root, the actual carrier is injectively coded by the physical
`current?` atom on the fixed-root subtype.  This is the finite-coordinate form of the uniqueness
theorem; it makes no surjectivity claim onto all physical atoms. -/
theorem localizedCIPOccurrence_current_injective_at_root
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {fuel : Nat} (root : input.Atom) :
    Function.Injective
      (fun occurrence :
          {o : input.LocalizedCIPOccurrence fuel // o.1.root = root} =>
        occurrence.1.1.node.current?) := by
  intro left right sameCurrent
  exact Subtype.ext
    (input.localizedCIPOccurrence_current_injective_at_fixedRoot singleBonded acyclic
      left.1 right.1 (left.2.trans right.2.symm) sameCurrent)

/-- Finite cardinal consequence: at a fixed original root there are at most as many actual
carrier occurrences as there are physical atom codes (`Option` because `current?` is optional).
This is a genuine bound proved from injectivity, not a completeness statement. -/
theorem localizedCIPOccurrence_card_le_option_at_root
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    (fuel : Nat) (root : input.Atom) :
    Fintype.card
        {occurrence : input.LocalizedCIPOccurrence fuel // occurrence.1.root = root} ≤
      Fintype.card (Option input.Atom) := by
  classical
  exact Fintype.card_le_of_injective
    (fun occurrence :
        {o : input.LocalizedCIPOccurrence fuel // o.1.root = root} =>
      occurrence.1.1.node.current?)
    (input.localizedCIPOccurrence_current_injective_at_root
      (fuel := fuel) singleBonded acyclic root)

end CertifiedLocalizedCIPInput

end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RealRootedPath
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realRootedPath_root
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realPathNode_to_rooted
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realPathNode_provenance
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realRootedPath_history_eq_of_current_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realPathNode_history_eq_of_current_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedOccurrenceSubtree_history_suffix
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedOccurrenceSubtree_history_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.childProvenance_real_of_descendant
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.descendant_current_ne_root
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedOccurrenceSubtree_determined_of_current
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCIPOccurrence_current_injective_at_fixedRoot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCIPOccurrence_node_injective_at_fixedRoot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCIPOccurrence_current_injective_at_root
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCIPOccurrence_card_le_option_at_root
