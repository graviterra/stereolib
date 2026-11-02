import TetraStereo.OneCenter.LocalizedRetainedArmExpansion
import TetraStereo.OneCenter.LocalizedRerootChildrenExecutable
import TetraStereo.OneCenter.MultiCenterDetection
import TetraStereo.KernelOnly
import Mathlib.GroupTheory.Perm.Sign

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# Occurrence transport along one molecular automorphism

Same certified input. `e : MoleculeGraph.Aut` preserves atomic number, mass, formal charge, and
bond order, and is applied to every atom of an official history. The image address is rebuilt with
`executableOfficialChildCopySlot` because neighbor copies are sorted by `≤`. Address length and
prefix shape transport; slot values are the locality gap.

`LocalizedDepthDependency` is every strictly deeper occurrence under the same root. Focus and
incoming IDs are `occurrenceCarrierNode`. Frame parity is the sign of the induced ligand
reindexing and is not a CIP letter. No acyclicity, no `descriptorMap`, no `RootedDigraph.Iso`.
-/

namespace TetraStereo.OneCenter

noncomputable section

/-- Image of one official node under a single atom permutation. Current atom and every history
atom use that same permutation, so repeated occurrences stay consistent. Provenance is copied. -/
def mapOfficialNode {V : Type*} [DecidableEq V] (e : Equiv.Perm V) (node : OfficialCIPNode V) :
    OfficialCIPNode V where
  current? := node.current?.map e
  history := node.history.map e
  provenance := node.provenance

@[simp] theorem mapOfficialNode_root {V : Type*} [DecidableEq V] (e : Equiv.Perm V) (atom : V) :
    mapOfficialNode e (OfficialCIPNode.root atom) = OfficialCIPNode.root (e atom) := by
  simp [mapOfficialNode, OfficialCIPNode.root]

theorem mapOfficialNode_mem_history {V : Type*} [DecidableEq V] (e : Equiv.Perm V)
    (node : OfficialCIPNode V) (atom : V) :
    e atom ∈ (mapOfficialNode e node).history ↔ atom ∈ node.history := by
  constructor
  · intro present
    obtain ⟨other, otherPresent, otherEq⟩ := List.mem_map.mp present
    exact (Equiv.injective e otherEq) ▸ otherPresent
  · intro present
    exact List.mem_map.mpr ⟨atom, present, rfl⟩

theorem firstIndexOf?_map {V : Type*} [DecidableEq V] (e : Equiv.Perm V) (target : V) :
    ∀ atoms : List V, firstIndexOf? (e target) (atoms.map e) = firstIndexOf? target atoms
  | [] => by simp [firstIndexOf?]
  | atom :: atoms => by
      by_cases same : atom = target
      · subst same
        simp [firstIndexOf?]
      · have distinct : e atom ≠ e target := fun equal => same (Equiv.injective e equal)
        simp [firstIndexOf?, same, distinct, firstIndexOf?_map e target atoms]

theorem duplicateRootDistance_map {V : Type*} [DecidableEq V] (e : Equiv.Perm V)
    (node : OfficialCIPNode V) (atom : V) :
    (mapOfficialNode e node).duplicateRootDistance (e atom) =
      node.duplicateRootDistance atom := by
  simp only [OfficialCIPNode.duplicateRootDistance, mapOfficialNode, OfficialCIPNode.depth,
    List.length_map]
  have reversed : (node.history.map e).reverse = node.history.reverse.map e := by
    simp [List.map_reverse]
  rw [reversed, firstIndexOf?_map]

@[simp] theorem mapOfficialNode_parent? {V : Type*} [DecidableEq V] (e : Equiv.Perm V)
    (node : OfficialCIPNode V) :
    (mapOfficialNode e node).parent? = node.parent?.map e := by
  cases historyShape : node.history with
  | nil => simp [mapOfficialNode, OfficialCIPNode.parent?, historyShape]
  | cons current older =>
      cases older with
      | nil => simp [mapOfficialNode, OfficialCIPNode.parent?, historyShape]
      | cons parent rest => simp [mapOfficialNode, OfficialCIPNode.parent?, historyShape]

theorem mapOfficialNode_parent?_ne {V : Type*} [DecidableEq V] (e : Equiv.Perm V)
    {node : OfficialCIPNode V} {next : V} (notParent : node.parent? ≠ some next) :
    (mapOfficialNode e node).parent? ≠ some (e next) := by
  intro imageParent
  rw [mapOfficialNode_parent?] at imageParent
  cases parentShape : node.parent? with
  | none => simp [parentShape] at imageParent
  | some parent =>
      have parentEq : e parent = e next := by simpa [parentShape] using imageParent
      exact notParent (parentShape ▸ congrArg some (Equiv.injective e parentEq))

theorem mapOfficialNode_childProvenance {V : Type*} [DecidableEq V] (e : Equiv.Perm V)
    (node : OfficialCIPNode V) (next : V) (copyIndex : Nat) :
    (mapOfficialNode e node).childProvenance (e next) copyIndex =
      node.childProvenance next copyIndex := by
  by_cases zeroCopy : copyIndex = 0
  · subst zeroCopy
    by_cases seen : next ∈ node.history
    · have seenImage : e next ∈ (mapOfficialNode e node).history :=
        (mapOfficialNode_mem_history e node next).2 seen
      calc
        (mapOfficialNode e node).childProvenance (e next) 0
          = OfficialCIPNodeProvenance.ringDuplicate
              ((mapOfficialNode e node).duplicateRootDistance (e next)) :=
            OfficialCIPNode.childProvenance_ring_duplicate _ _ seenImage
        _ = OfficialCIPNodeProvenance.ringDuplicate (node.duplicateRootDistance next) := by
            simp [duplicateRootDistance_map]
        _ = node.childProvenance next 0 :=
            (OfficialCIPNode.childProvenance_ring_duplicate node next seen).symm
    · have unseenImage : e next ∉ (mapOfficialNode e node).history :=
        fun present => seen ((mapOfficialNode_mem_history e node next).1 present)
      calc
        (mapOfficialNode e node).childProvenance (e next) 0 =
            OfficialCIPNodeProvenance.realAtom :=
          OfficialCIPNode.childProvenance_real _ _ unseenImage
        _ = node.childProvenance next 0 :=
          (OfficialCIPNode.childProvenance_real node next seen).symm
  · calc
      (mapOfficialNode e node).childProvenance (e next) copyIndex =
          OfficialCIPNodeProvenance.multipleBondDuplicate (mapOfficialNode e node).depth :=
        OfficialCIPNode.childProvenance_copy_pos _ _ zeroCopy
      _ = OfficialCIPNodeProvenance.multipleBondDuplicate node.depth := by
          simp [OfficialCIPNode.depth, mapOfficialNode]
      _ = node.childProvenance next copyIndex :=
          (OfficialCIPNode.childProvenance_copy_pos node next zeroCopy).symm

@[simp] theorem mapOfficialNode_extend {V : Type*} [DecidableEq V] (e : Equiv.Perm V)
    (node : OfficialCIPNode V) (next : V) (copyIndex : Nat) :
    mapOfficialNode e (node.extend next copyIndex) =
      (mapOfficialNode e node).extend (e next) copyIndex := by
  let imageNode : OfficialCIPNode V :=
    ⟨some (e next), e next :: node.history.map e, node.childProvenance next copyIndex⟩
  have leftEq : mapOfficialNode e (node.extend next copyIndex) = imageNode := by
    simp [imageNode, mapOfficialNode, OfficialCIPNode.extend, List.map_cons, Option.map_some]
  have rightEq : (mapOfficialNode e node).extend (e next) copyIndex =
      ⟨some (e next), e next :: node.history.map e,
        (mapOfficialNode e node).childProvenance (e next) copyIndex⟩ := by
    simp [mapOfficialNode, OfficialCIPNode.extend]
  rw [leftEq, rightEq]
  exact congrArg
    (fun provenance =>
      (⟨some (e next), e next :: node.history.map e, provenance⟩ : OfficialCIPNode V))
    (mapOfficialNode_childProvenance e node next copyIndex).symm

/-- Root-first extension by real or ring-duplicate steps. The copy index is zero. -/
def foldExtend {V : Type*} [DecidableEq V] (node : OfficialCIPNode V) : List V → OfficialCIPNode V
  | [] => node
  | next :: rest => foldExtend (node.extend next 0) rest

@[simp] theorem foldExtend_nil {V : Type*} [DecidableEq V] (node : OfficialCIPNode V) :
    foldExtend node [] = node := rfl

@[simp] theorem foldExtend_cons {V : Type*} [DecidableEq V] (node : OfficialCIPNode V)
    (next : V) (rest : List V) :
    foldExtend node (next :: rest) = foldExtend (node.extend next 0) rest := rfl

theorem foldExtend_append_singleton {V : Type*} [DecidableEq V] (node : OfficialCIPNode V)
    (atoms : List V) (next : V) :
    foldExtend node (atoms ++ [next]) = (foldExtend node atoms).extend next 0 := by
  induction atoms generalizing node with
  | nil => simp
  | cons atom rest ih => simp [ih]

theorem mapOfficialNode_foldExtend {V : Type*} [DecidableEq V] (e : Equiv.Perm V)
    (node : OfficialCIPNode V) (atoms : List V) :
    mapOfficialNode e (foldExtend node atoms) =
      foldExtend (mapOfficialNode e node) (atoms.map e) := by
  induction atoms generalizing node with
  | nil => simp
  | cons atom rest ih => simp [ih, mapOfficialNode_extend]

theorem mapOfficialNode_symm_apply {V : Type*} [DecidableEq V] (e : Equiv.Perm V)
    (node : OfficialCIPNode V) :
    mapOfficialNode e.symm (mapOfficialNode e node) = node := by
  cases node with
  | mk current history provenance =>
      have currentRound : (current.map e).map e.symm = current := by
        cases current with
        | none => rfl
        | some atom => simp [Option.map_some, Equiv.symm_apply_apply]
      have historyRound : (history.map e).map e.symm = history := by
        simp [List.map_map]
      simp [mapOfficialNode, currentRound, historyRound]

namespace CertifiedLocalizedCIPInput

open DeclarativeCIP.RetainedOccurrenceCarrier

variable (input : CertifiedLocalizedCIPInput)

/-- Slots of a root-first continuation. Each slot is recomputed on the node built so far. -/
def foldSlots (node : OfficialCIPNode input.Atom) : List input.Atom → List Nat
  | [] => []
  | next :: rest =>
      input.executableOfficialChildCopySlot node next 0 ::
        foldSlots (node.extend next 0) rest

@[simp] theorem foldSlots_nil (node : OfficialCIPNode input.Atom) :
    input.foldSlots node [] = [] := rfl

@[simp] theorem foldSlots_cons (node : OfficialCIPNode input.Atom) (next : input.Atom)
    (rest : List input.Atom) :
    input.foldSlots node (next :: rest) =
      input.executableOfficialChildCopySlot node next 0 ::
        input.foldSlots (node.extend next 0) rest := rfl

theorem foldSlots_length (node : OfficialCIPNode input.Atom) (atoms : List input.Atom) :
    (input.foldSlots node atoms).length = atoms.length := by
  induction atoms generalizing node with
  | nil => simp
  | cons atom rest ih => simp [ih]

theorem foldSlots_append_singleton (node : OfficialCIPNode input.Atom) (atoms : List input.Atom)
    (next : input.Atom) :
    input.foldSlots node (atoms ++ [next]) =
      input.foldSlots node atoms ++
        [input.executableOfficialChildCopySlot (foldExtend node atoms) next 0] := by
  induction atoms generalizing node with
  | nil => simp
  | cons atom rest ih =>
      simp [ih, List.cons_append]

/-- Address read off a node by walking its reversed history after the root. -/
def canonicalAddress (root : input.Atom) (node : OfficialCIPNode input.Atom) : List Nat :=
  input.foldSlots (OfficialCIPNode.root root) node.history.reverse.tail

/-- Address of the image node. The root is `e root`; each later atom is `e` of the source atom.
Slots are the image node's executable slots, not the source slot numbers. -/
def transportedAddress (e : input.moleculeGraph.Aut) (root : input.Atom)
    (node : OfficialCIPNode input.Atom) : List Nat :=
  input.foldSlots (OfficialCIPNode.root ((e : Equiv.Perm input.Atom) root))
    (node.history.reverse.tail.map (e : Equiv.Perm input.Atom))

private theorem reverse_eq_cons {α : Type*} {atoms : List α} {root : α}
    (headEq : atoms.head? = some root) : atoms = root :: atoms.tail := by
  cases atoms with
  | nil => simp at headEq
  | cons atom rest =>
      simp at headEq
      subst headEq
      rfl

private theorem dropLast_append_singleton {α : Type*} (atoms : List α) (last : α) :
    (atoms ++ [last]).dropLast = atoms := by
  induction atoms with
  | nil => simp
  | cons atom rest _ih =>
      cases rest with
      | nil => simp
      | cons head tail => simp [List.dropLast]

private theorem getLast?_append_singleton {α : Type*} (atoms : List α) (last : α) :
    (atoms ++ [last]).getLast? = some last := by
  induction atoms with
  | nil => simp
  | cons atom rest _ih =>
      cases rest with
      | nil => simp
      | cons head tail => simp [List.getLast?]

/-- Image of one simple path. The address field is the recomputed image address. -/
structure SimpleImage (e : input.moleculeGraph.Aut) (root : input.Atom)
    (node : OfficialCIPNode input.Atom) (address : List Nat) : Prop where
  reverse_head : node.history.reverse.head? = some root
  node_fold : node = foldExtend (OfficialCIPNode.root root) node.history.reverse.tail
  address_fold : address = input.canonicalAddress root node
  image_path : SimpleOccurrencePath input ((e : Equiv.Perm input.Atom) root)
    (mapOfficialNode (e : Equiv.Perm input.Atom) node)
    (input.transportedAddress e root node)

/-- One extension, source and image. The image slot is recomputed on the image node. -/
structure ExtendFacts (e : input.moleculeGraph.Aut) (root : input.Atom)
    (node : OfficialCIPNode input.Atom) (address : List Nat) (next : input.Atom) : Prop where
  head : (node.extend next 0).history.reverse.head? = some root
  folded : node.extend next 0 =
    foldExtend (OfficialCIPNode.root root) (node.extend next 0).history.reverse.tail
  addressed : address ++ [input.executableOfficialChildCopySlot node next 0] =
    input.canonicalAddress root (node.extend next 0)
  nodeEq : mapOfficialNode (e : Equiv.Perm input.Atom) (node.extend next 0) =
    (mapOfficialNode (e : Equiv.Perm input.Atom) node).extend
      ((e : Equiv.Perm input.Atom) next) 0
  imageAddressEq : input.transportedAddress e root (node.extend next 0) =
    input.transportedAddress e root node ++
      [input.executableOfficialChildCopySlot
        (mapOfficialNode (e : Equiv.Perm input.Atom) node)
        ((e : Equiv.Perm input.Atom) next) 0]

private theorem extendFacts (e : input.moleculeGraph.Aut) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (head : node.history.reverse.head? = some root)
    (folded : node = foldExtend (OfficialCIPNode.root root) node.history.reverse.tail)
    (addressed : address = input.canonicalAddress root node) (next : input.Atom) :
    input.ExtendFacts e root node address next := by
  let perm := (e : Equiv.Perm input.Atom)
  have parentRev : node.history.reverse = root :: node.history.reverse.tail :=
    reverse_eq_cons head
  have childRev : (node.extend next 0).history.reverse = node.history.reverse ++ [next] := by
    simp [OfficialCIPNode.extend_history, List.reverse_cons]
  have childTail : (node.extend next 0).history.reverse.tail =
      node.history.reverse.tail ++ [next] := by
    rw [childRev, parentRev]
    simp
  have childHead : (node.extend next 0).history.reverse.head? = some root := by
    rw [childRev, parentRev]
    simp
  have foldChild : node.extend next 0 =
      foldExtend (OfficialCIPNode.root root) (node.extend next 0).history.reverse.tail := by
    rw [childTail, foldExtend_append_singleton, ← folded]
  have addressChild : address ++ [input.executableOfficialChildCopySlot node next 0] =
      input.canonicalAddress root (node.extend next 0) := by
    symm
    rw [canonicalAddress, childTail, input.foldSlots_append_singleton, ← folded]
    rw [canonicalAddress] at addressed
    rw [addressed]
  have nodeEq : mapOfficialNode perm (node.extend next 0) =
      (mapOfficialNode perm node).extend (perm next) 0 := by
    simp [mapOfficialNode_extend]
  have foldMap : foldExtend (OfficialCIPNode.root (perm root))
      (node.history.reverse.tail.map perm) = mapOfficialNode perm node := by
    rw [← mapOfficialNode_root, ← mapOfficialNode_foldExtend, ← folded]
  have imageAddressEq : input.transportedAddress e root (node.extend next 0) =
      input.transportedAddress e root node ++
        [input.executableOfficialChildCopySlot (mapOfficialNode perm node) (perm next) 0] := by
    rw [transportedAddress, transportedAddress, childTail, List.map_append, List.map_singleton,
      input.foldSlots_append_singleton, foldMap]
  exact ⟨childHead, foldChild, addressChild, nodeEq, imageAddressEq⟩

theorem simpleOccurrencePath_image (e : input.moleculeGraph.Aut) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) :
    input.SimpleImage e root node address := by
  induction path with
  | root =>
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp [OfficialCIPNode.root]
      · simp [OfficialCIPNode.root]
      · simp [canonicalAddress, OfficialCIPNode.root]
      · simpa [mapOfficialNode_root, transportedAddress, OfficialCIPNode.root] using
          (SimpleOccurrencePath.root (root := (e : Equiv.Perm input.Atom) root))
  | @step node address current next path currentObserved adjacent notParent fresh ih =>
      let perm := (e : Equiv.Perm input.Atom)
      have facts := input.extendFacts e ih.reverse_head ih.node_fold ih.address_fold next
      have currentImage : (mapOfficialNode perm node).current? = some (perm current) := by
        simp [mapOfficialNode, currentObserved]
      have adjacentImage : input.moleculeGraph.Adj (perm current) (perm next) :=
        (MoleculeGraph.Aut.adj_iff input.moleculeGraph e current next).2 adjacent
      have notParentImage := mapOfficialNode_parent?_ne perm notParent
      have freshImage : perm next ∉ (mapOfficialNode perm node).history :=
        fun present => fresh ((mapOfficialNode_mem_history perm node next).1 present)
      have stepped := SimpleOccurrencePath.step ih.image_path currentImage adjacentImage
        notParentImage freshImage
      have imagePath : SimpleOccurrencePath input (perm root)
          (mapOfficialNode perm (node.extend next 0))
          (input.transportedAddress e root (node.extend next 0)) := by
        rw [← facts.nodeEq, ← facts.imageAddressEq] at stepped
        exact stepped
      exact ⟨facts.head, facts.folded, facts.addressed, imagePath⟩

/-- Image of one legitimate occurrence. The multiple-bond constructor is impossible when every
positive bond has order one. -/
structure LegitimateTransport (e : input.moleculeGraph.Aut) (root : input.Atom)
    (node : OfficialCIPNode input.Atom) (address : List Nat) : Prop where
  sourceAddress : address = input.canonicalAddress root node
  sourceHead : node.history.reverse.head? = some root
  image : LegitimateOccurrence input ((e : Equiv.Perm input.Atom) root)
    (mapOfficialNode (e : Equiv.Perm input.Atom) node)
    (input.transportedAddress e root node)

theorem legitimateOccurrence_transport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut)
    {root : input.Atom} {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) :
    input.LegitimateTransport e root node address := by
  let perm := (e : Equiv.Perm input.Atom)
  cases occ with
  | simple path =>
      have packed := input.simpleOccurrencePath_image e path
      exact ⟨packed.address_fold, packed.reverse_head,
        LegitimateOccurrence.simple packed.image_path⟩
  | @ring prefixNode _prefixAddress current next path currentObserved adjacent notParent visited =>
      have packed := input.simpleOccurrencePath_image e path
      have facts := input.extendFacts e packed.reverse_head packed.node_fold
        packed.address_fold next
      have currentImage : (mapOfficialNode perm prefixNode).current? = some (perm current) := by
        simp [mapOfficialNode, currentObserved]
      have adjacentImage : input.moleculeGraph.Adj (perm current) (perm next) :=
        (MoleculeGraph.Aut.adj_iff input.moleculeGraph e current next).2 adjacent
      have notParentImage := mapOfficialNode_parent?_ne perm notParent
      have visitedImage : perm next ∈ (mapOfficialNode perm prefixNode).history :=
        (mapOfficialNode_mem_history perm prefixNode next).2 visited
      have imageOcc := LegitimateOccurrence.ring packed.image_path currentImage adjacentImage
        notParentImage visitedImage
      have imageLegit : LegitimateOccurrence input (perm root)
          (mapOfficialNode perm (prefixNode.extend next 0))
          (input.transportedAddress e root (prefixNode.extend next 0)) := by
        rw [← facts.nodeEq, ← facts.imageAddressEq] at imageOcc
        exact imageOcc
      exact ⟨facts.addressed, facts.head, imageLegit⟩
  | @multiple _prefixNode _prefixAddress current next copyIndex _path _currentObserved adjacent
      bound positive =>
      have bondOne : input.moleculeGraph.bond current next = 1 :=
        singleBonded current next adjacent
      exact absurd (Nat.lt_one_iff.mp (by simpa [bondOne] using bound)) positive

/-- Source terminal slot, read from the source node's executable list. -/
theorem canonicalTerminalSlot {root : input.Atom} {node : OfficialCIPNode input.Atom}
    {address : List Nat} (path : SimpleOccurrencePath input root node address)
    (next : input.Atom) :
    (input.canonicalAddress root (node.extend next 0)).getLast? =
      some (input.executableOfficialChildCopySlot node next 0) := by
  have packed := input.simpleOccurrencePath_image (1 : input.moleculeGraph.Aut) path
  have facts := input.extendFacts (1 : input.moleculeGraph.Aut) packed.reverse_head
    packed.node_fold packed.address_fold next
  rw [← facts.addressed, packed.address_fold, getLast?_append_singleton]

/-- Locality gap: the image terminal slot is recomputed by `executableOfficialChildCopySlot` on
the image node. Neighbor copies are sorted by `≤`, so this need not equal `canonicalTerminalSlot`. -/
theorem recomputedTerminalSlot (e : input.moleculeGraph.Aut) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) (next : input.Atom) :
    (input.transportedAddress e root (node.extend next 0)).getLast? =
      some (input.executableOfficialChildCopySlot
        (mapOfficialNode (e : Equiv.Perm input.Atom) node)
        ((e : Equiv.Perm input.Atom) next) 0) := by
  have packed := input.simpleOccurrencePath_image e path
  have facts := input.extendFacts e packed.reverse_head packed.node_fold packed.address_fold next
  rw [facts.imageAddressEq, getLast?_append_singleton]

/-- The image of a one-step extension drops back to the image of the prefix. -/
theorem transportedAddress_extend_dropLast (e : input.moleculeGraph.Aut) {root : input.Atom}
    {node : OfficialCIPNode input.Atom} {address : List Nat}
    (path : SimpleOccurrencePath input root node address) (next : input.Atom) :
    (input.transportedAddress e root (node.extend next 0)).dropLast =
      input.transportedAddress e root node := by
  have packed := input.simpleOccurrencePath_image e path
  have facts := input.extendFacts e packed.reverse_head packed.node_fold packed.address_fold next
  rw [facts.imageAddressEq, dropLast_append_singleton]

theorem legitimateOccurrence_mem_localizedOccurrences_of_length
    {root : input.Atom} {node : OfficialCIPNode input.Atom} {address : List Nat}
    (occ : LegitimateOccurrence input root node address) {fuel : Nat}
    (enough : address.length ≤ fuel + 1) :
    { root := root, address := address, node := node,
      remaining := fuel + 1 - address.length } ∈ input.localizedOccurrences fuel := by
  have reachable := input.legitimateOccurrence_unbounded occ
  have covered := input.mem_localizedOccurrenceSubtree_of_unbounded
    (root := root) (fuel := fuel + 1) (path := []) reachable enough
  have rooted :
      { root := root, address := address, node := node,
        remaining := fuel + 1 - address.length } ∈ input.localizedOccurrencesAtAtom fuel root := by
    simpa [localizedOccurrencesAtAtom] using covered
  unfold localizedOccurrences
  rw [List.mem_dedup, List.mem_flatMap]
  exact ⟨root, by simp, rooted⟩

def transportFrame (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) : input.LocalizedCIPOccurrenceFrame where
  root := (e : Equiv.Perm input.Atom) occ.1.root
  address := input.transportedAddress e occ.1.root occ.1.node
  node := mapOfficialNode (e : Equiv.Perm input.Atom) occ.1.node
  remaining := fuel + 1 - (input.transportedAddress e occ.1.root occ.1.node).length

theorem transportFrame_address_length
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    (input.transportFrame e occ).address.length = occ.1.address.length := by
  have packed := input.legitimateOccurrence_transport singleBonded e
    (input.carrierOccurrence_legitimate singleBonded occ)
  simp [transportFrame, transportedAddress, canonicalAddress, foldSlots_length, List.length_map,
    packed.sourceAddress]

theorem transportFrame_mem
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    input.transportFrame e occ ∈ input.localizedOccurrences fuel := by
  have packed := input.legitimateOccurrence_transport singleBonded e
    (input.carrierOccurrence_legitimate singleBonded occ)
  have enough : (input.transportedAddress e occ.1.root occ.1.node).length ≤ fuel + 1 := by
    have grade := input.localizedCIPOccurrence_depthGrade occ
    have lengthEq := input.transportFrame_address_length singleBonded e occ
    simp [transportFrame] at lengthEq
    omega
  have imageOcc : LegitimateOccurrence input ((e : Equiv.Perm input.Atom) occ.1.root)
      (mapOfficialNode (e : Equiv.Perm input.Atom) occ.1.node)
      (input.transportedAddress e occ.1.root occ.1.node) := packed.image
  have member := input.legitimateOccurrence_mem_localizedOccurrences_of_length imageOcc enough
  simpa [transportFrame] using member

def transportOccurrence
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) : input.LocalizedCIPOccurrence fuel :=
  ⟨input.transportFrame e occ, input.transportFrame_mem singleBonded e occ⟩

@[simp] theorem transportOccurrence_root
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    (input.transportOccurrence singleBonded e occ).1.root =
      (e : Equiv.Perm input.Atom) occ.1.root := rfl

@[simp] theorem transportOccurrence_node
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    (input.transportOccurrence singleBonded e occ).1.node =
      mapOfficialNode (e : Equiv.Perm input.Atom) occ.1.node := rfl

@[simp] theorem transportOccurrence_address
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    (input.transportOccurrence singleBonded e occ).1.address =
      input.transportedAddress e occ.1.root occ.1.node := rfl

theorem transportOccurrence_address_length
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    (input.transportOccurrence singleBonded e occ).1.address.length = occ.1.address.length := by
  simp [transportOccurrence, input.transportFrame_address_length singleBonded e occ]

theorem transportOccurrence_remaining
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    (input.transportOccurrence singleBonded e occ).1.remaining = occ.1.remaining := by
  have grade := input.localizedCIPOccurrence_depthGrade occ
  have lengthEq := input.transportOccurrence_address_length singleBonded e occ
  simp [transportOccurrence, transportFrame] at lengthEq ⊢
  omega

/-- Every deeper occurrence under the same root, preserved and reflected. The comparison is
address length, so the locality gap in slot values does not enter. -/
theorem localizedDepthDependency_transport_iff
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (source target : input.LocalizedCIPOccurrence fuel) :
    input.LocalizedDepthDependency source target ↔
      input.LocalizedDepthDependency (input.transportOccurrence singleBonded e source)
        (input.transportOccurrence singleBonded e target) := by
  constructor
  · intro related
    refine ⟨?_, ?_⟩
    · simpa [transportOccurrence_root] using congrArg (e : Equiv.Perm input.Atom) related.1
    · rw [input.transportOccurrence_address_length singleBonded e target,
        input.transportOccurrence_address_length singleBonded e source]
      exact related.2
  · intro related
    refine ⟨?_, ?_⟩
    · exact Equiv.injective (e : Equiv.Perm input.Atom)
        (by simpa [transportOccurrence_root] using related.1)
    · rw [← input.transportOccurrence_address_length singleBonded e target,
        ← input.transportOccurrence_address_length singleBonded e source]
      exact related.2

/-- Carrier-node image. One permutation on the root-first path and, for a ring, on the closure. -/
def mapCarrierNode (e : Equiv.Perm input.Atom) : CarrierNode input.Atom → CarrierNode input.Atom
  | .real path => .real (path.map e)
  | .ring path atom => .ring (path.map e) (e atom)

theorem occurrenceCarrierNode_transport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (occ : input.LocalizedCIPOccurrence fuel) :
    input.mapCarrierNode (e : Equiv.Perm input.Atom)
        (input.occurrenceCarrierNode singleBonded occ) =
      input.occurrenceCarrierNode singleBonded
        (input.transportOccurrence singleBonded e occ) := by
  let perm := (e : Equiv.Perm input.Atom)
  have legit := input.carrierOccurrence_legitimate singleBonded occ
  generalize rootDef : occ.1.root = root at legit
  generalize addressDef : occ.1.address = address at legit
  generalize nodeDef : occ.1.node = node at legit
  cases legit with
  | simple path =>
      have prov := input.simpleOccurrencePath_provenance path
      have provOcc : occ.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
        rw [nodeDef]; exact prov
      have imageProv : (input.transportOccurrence singleBonded e occ).1.node.provenance =
          OfficialCIPNodeProvenance.realAtom := by
        rw [transportOccurrence_node, nodeDef, mapOfficialNode]
        exact prov
      rw [occurrenceCarrierNode, if_pos provOcc, occurrenceCarrierNode, if_pos imageProv]
      simp [mapCarrierNode, transportOccurrence_node, nodeDef, mapOfficialNode, List.map_reverse]
  | @ring prefixNode _prefixAddress _current next _path _currentObserved _adjacent _notParent
      visited =>
      have prov := input.legitimateOccurrence_ring_provenance visited
      have notReal : occ.1.node.provenance ≠ OfficialCIPNodeProvenance.realAtom := by
        rw [nodeDef, prov]
        intro bad
        cases bad
      have imageNode : (input.transportOccurrence singleBonded e occ).1.node =
          (mapOfficialNode perm prefixNode).extend (perm next) 0 := by
        rw [transportOccurrence_node, nodeDef, mapOfficialNode_extend]
      have imageNotReal :
          (input.transportOccurrence singleBonded e occ).1.node.provenance ≠
            OfficialCIPNodeProvenance.realAtom := by
        rw [imageNode, OfficialCIPNode.extend_provenance, mapOfficialNode_childProvenance,
          ← OfficialCIPNode.extend_provenance, prov]
        intro bad
        cases bad
      rw [occurrenceCarrierNode, if_neg notReal, occurrenceCarrierNode, if_neg imageNotReal]
      have sourceHistory : occ.1.node.history = next :: prefixNode.history := by
        rw [nodeDef, OfficialCIPNode.extend_history]
      have mappedHistory :
          (mapOfficialNode (e : Equiv.Perm input.Atom) occ.1.node).history =
            (e : Equiv.Perm input.Atom) next ::
              prefixNode.history.map (e : Equiv.Perm input.Atom) := by
        rw [nodeDef, mapOfficialNode_extend, OfficialCIPNode.extend_history]
        simp [mapOfficialNode]
      simp [sourceHistory, mappedHistory, mapCarrierNode, transportOccurrence_node,
        List.tail_cons, List.head_cons, List.map_reverse]
  | @multiple _prefixNode _prefixAddress current next _copyIndex _path _currentObserved adjacent
      bound positive =>
      have bondOne : input.moleculeGraph.bond current next = 1 :=
        singleBonded current next adjacent
      exact absurd (Nat.lt_one_iff.mp (by simpa [bondOne] using bound)) positive

def transportCursor
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) : input.LocalizedRerootCursor fuel where
  occurrence := input.transportOccurrence singleBonded e cursor.occurrence
  previous? := cursor.previous?.map (input.transportOccurrence singleBonded e)

@[simp] theorem transportCursor_occurrence
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.transportCursor singleBonded e cursor).occurrence =
      input.transportOccurrence singleBonded e cursor.occurrence := rfl

@[simp] theorem transportCursor_previous?
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    (input.transportCursor singleBonded e cursor).previous? =
      cursor.previous?.map (input.transportOccurrence singleBonded e) := rfl

/-- Focus and incoming of a cursor whose `previous?` stores the incoming occurrence. -/
theorem cursor_focus_incoming_transport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) (target : input.LocalizedCIPOccurrence fuel)
    (incoming : cursor.previous? = some target) :
    input.mapCarrierNode (e : Equiv.Perm input.Atom)
        (input.occurrenceCarrierNode singleBonded cursor.occurrence) =
      input.occurrenceCarrierNode singleBonded
        (input.transportCursor singleBonded e cursor).occurrence ∧
    input.mapCarrierNode (e : Equiv.Perm input.Atom)
        (input.occurrenceCarrierNode singleBonded target) =
      input.occurrenceCarrierNode singleBonded (input.transportOccurrence singleBonded e target) ∧
    (input.transportCursor singleBonded e cursor).previous? =
      some (input.transportOccurrence singleBonded e target) := by
  refine ⟨?_, input.occurrenceCarrierNode_transport singleBonded e target, ?_⟩
  · simpa [transportCursor] using
      input.occurrenceCarrierNode_transport singleBonded e cursor.occurrence
  · simp [incoming]

/-- Executable child cut. The incoming occurrence is derived from the executable list, and both
carrier nodes transport. -/
theorem executableChild_cut_transport
    (singleBonded : input.moleculeGraph.SimpleBonded) (e : input.moleculeGraph.Aut) {fuel : Nat}
    (cursor child : input.LocalizedRerootCursor fuel)
    (present : child ∈ input.executableLocalizedRerootChildren cursor) :
    child.previous? = some cursor.occurrence ∧
      (input.transportCursor singleBonded e child).previous? =
        some (input.transportCursor singleBonded e cursor).occurrence ∧
      input.mapCarrierNode (e : Equiv.Perm input.Atom)
          (input.occurrenceCarrierNode singleBonded child.occurrence) =
        input.occurrenceCarrierNode singleBonded
          (input.transportOccurrence singleBonded e child.occurrence) ∧
      input.mapCarrierNode (e : Equiv.Perm input.Atom)
          (input.occurrenceCarrierNode singleBonded cursor.occurrence) =
        input.occurrenceCarrierNode singleBonded
          (input.transportOccurrence singleBonded e cursor.occurrence) := by
  have incoming := input.executableLocalizedRerootChildren_previous cursor child present
  refine ⟨incoming, ?_, input.occurrenceCarrierNode_transport singleBonded e child.occurrence,
    input.occurrenceCarrierNode_transport singleBonded e cursor.occurrence⟩
  simp [incoming]

/-- Neighbor reindexing. Transparent so the ligand atom, not only the equiv, is identified. -/
def neighborTransport (e : input.moleculeGraph.Aut) (center : input.Atom) :
    input.moleculeGraph.Neighbor center ≃
      input.moleculeGraph.Neighbor ((e : Equiv.Perm input.Atom) center) :=
  Equiv.ofBijective
    (fun neighbor => ⟨(e : Equiv.Perm input.Atom) neighbor.1,
      (MoleculeGraph.Aut.adj_iff input.moleculeGraph e center neighbor.1).2 neighbor.2⟩)
    (by
      constructor
      · intro left right equal
        apply Subtype.ext
        exact Equiv.injective (e : Equiv.Perm input.Atom) (congrArg Subtype.val equal)
      · intro image
        refine ⟨⟨(e : Equiv.Perm input.Atom)⁻¹ image.1, ?_⟩, ?_⟩
        · have imageAdj :=
            (MoleculeGraph.Aut.adj_iff input.moleculeGraph
              (e⁻¹ : input.moleculeGraph.Aut)
              ((e : Equiv.Perm input.Atom) center) image.1).2 image.2
          simpa [Equiv.symm_apply_apply] using imageAdj
        · apply Subtype.ext
          simp)

/-- Ligand reindexing of one tetrahedral center. Its sign is `frameParity`, not a CIP letter. -/
def framePerm (e : input.moleculeGraph.Aut) (center : input.Atom)
    (tetrahedral : input.moleculeGraph.IsTetrahedralCenter center) : Equiv.Perm (Fin 4) :=
  let perm := (e : Equiv.Perm input.Atom)
  let imageTetrahedral :=
    (input.moleculeGraph.isTetrahedralCenter_apply_aut_iff e center).2 tetrahedral
  let source := input.moleculeGraph.ligandEquivOfIsTetrahedralCenter center tetrahedral
  let image := input.moleculeGraph.ligandEquivOfIsTetrahedralCenter (perm center) imageTetrahedral
  (source.trans (input.neighborTransport e center)).trans image.symm

def frameParity (e : input.moleculeGraph.Aut) (center : input.Atom)
    (tetrahedral : input.moleculeGraph.IsTetrahedralCenter center) : ℤˣ :=
  Equiv.Perm.sign (input.framePerm e center tetrahedral)

theorem framePerm_ligand (e : input.moleculeGraph.Aut) (center : input.Atom)
    (tetrahedral : input.moleculeGraph.IsTetrahedralCenter center) (index : Fin 4) :
    ((input.moleculeGraph.ligandEquivOfIsTetrahedralCenter
        ((e : Equiv.Perm input.Atom) center)
        ((input.moleculeGraph.isTetrahedralCenter_apply_aut_iff e center).2 tetrahedral))
      (input.framePerm e center tetrahedral index)).1 =
      (e : Equiv.Perm input.Atom)
        ((input.moleculeGraph.ligandEquivOfIsTetrahedralCenter center tetrahedral) index).1 := by
  let perm := (e : Equiv.Perm input.Atom)
  let imageTetrahedral :=
    (input.moleculeGraph.isTetrahedralCenter_apply_aut_iff e center).2 tetrahedral
  let source := input.moleculeGraph.ligandEquivOfIsTetrahedralCenter center tetrahedral
  let image := input.moleculeGraph.ligandEquivOfIsTetrahedralCenter (perm center) imageTetrahedral
  have transported : image (input.framePerm e center tetrahedral index) =
      input.neighborTransport e center (source index) := by
    simp only [framePerm, Equiv.trans_apply]
    exact image.apply_symm_apply _
  have valueEq : (input.neighborTransport e center (source index)).1 = perm (source index).1 := by
    unfold neighborTransport
    rw [Equiv.ofBijective_apply]
  rw [transported, valueEq]

def transportTetrahedralCenter (e : input.moleculeGraph.Aut) (center : input.TetrahedralCenter) :
    input.TetrahedralCenter :=
  ⟨(e : Equiv.Perm input.Atom) center.1,
    (input.moleculeGraph.mem_tetrahedralCenterSet_apply_aut_iff e center.1).mp center.2⟩

@[simp] theorem transportTetrahedralCenter_val (e : input.moleculeGraph.Aut)
    (center : input.TetrahedralCenter) :
    (input.transportTetrahedralCenter e center).1 = (e : Equiv.Perm input.Atom) center.1 := rfl

theorem atomZ_transport (e : input.moleculeGraph.Aut) (atom : input.Atom) :
    input.moleculeGraph.atomZ ((e : Equiv.Perm input.Atom) atom) =
      input.moleculeGraph.atomZ atom :=
  MoleculeGraph.Aut.atomZ_eq input.moleculeGraph e atom

theorem atomMass_transport (e : input.moleculeGraph.Aut) (atom : input.Atom) :
    input.moleculeGraph.atomMass ((e : Equiv.Perm input.Atom) atom) =
      input.moleculeGraph.atomMass atom :=
  MoleculeGraph.Aut.atomMass_eq input.moleculeGraph e atom

theorem formalCharge_transport (e : input.moleculeGraph.Aut) (atom : input.Atom) :
    input.moleculeGraph.formalCharge ((e : Equiv.Perm input.Atom) atom) =
      input.moleculeGraph.formalCharge atom :=
  MoleculeGraph.Aut.formalCharge_eq input.moleculeGraph e atom

theorem bond_transport (e : input.moleculeGraph.Aut) (left right : input.Atom) :
    input.moleculeGraph.bond ((e : Equiv.Perm input.Atom) left)
        ((e : Equiv.Perm input.Atom) right) =
      input.moleculeGraph.bond left right :=
  MoleculeGraph.Aut.bond_eq input.moleculeGraph e left right

theorem adj_transport_iff (e : input.moleculeGraph.Aut) (left right : input.Atom) :
    input.moleculeGraph.Adj ((e : Equiv.Perm input.Atom) left)
        ((e : Equiv.Perm input.Atom) right) ↔
      input.moleculeGraph.Adj left right :=
  MoleculeGraph.Aut.adj_iff input.moleculeGraph e left right

end CertifiedLocalizedCIPInput

end

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.mapOfficialNode_root
assert_kernel_only TetraStereo.OneCenter.mapOfficialNode_mem_history
assert_kernel_only TetraStereo.OneCenter.firstIndexOf?_map
assert_kernel_only TetraStereo.OneCenter.duplicateRootDistance_map
assert_kernel_only TetraStereo.OneCenter.mapOfficialNode_parent?
assert_kernel_only TetraStereo.OneCenter.mapOfficialNode_parent?_ne
assert_kernel_only TetraStereo.OneCenter.mapOfficialNode_childProvenance
assert_kernel_only TetraStereo.OneCenter.mapOfficialNode_extend
assert_kernel_only TetraStereo.OneCenter.foldExtend_append_singleton
assert_kernel_only TetraStereo.OneCenter.mapOfficialNode_foldExtend
assert_kernel_only TetraStereo.OneCenter.mapOfficialNode_symm_apply
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.foldSlots_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.foldSlots_append_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.simpleOccurrencePath_image
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.canonicalTerminalSlot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.recomputedTerminalSlot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportedAddress_extend_dropLast
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.legitimateOccurrence_mem_localizedOccurrences_of_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportFrame_address_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportFrame_mem
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportOccurrence_root
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportOccurrence_node
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportOccurrence_address
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportOccurrence_address_length
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportOccurrence_remaining
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedDepthDependency_transport_iff
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.occurrenceCarrierNode_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportCursor_occurrence
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportCursor_previous?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.cursor_focus_incoming_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableChild_cut_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.framePerm_ligand
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.transportTetrahedralCenter_val
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.atomZ_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.atomMass_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.formalCharge_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.bond_transport
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.adj_transport_iff
