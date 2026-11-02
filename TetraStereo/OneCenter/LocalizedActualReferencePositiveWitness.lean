import TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity
import TetraStereo.OneCenter.LocalizedAcyclicPhysicalPseudoFidelity
import TetraStereo.OneCenter.LocalizedTetrahedralRootDoubleBondBound
import TetraStereo.OneCenter.LocalizedRootZAutomorphismLabelCovariance
import Mathlib.Data.List.Dedup
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

/-!
# Positive actual reference-state witness on the five-atom halomethane fixture

This module instantiates the physical-frame readback theorem
`referenceState_reader_eq_chiral_of_physicalFrame` on the concrete admitted
bromochlorofluoroiodomethane input of `LocalizedWholeStateModelNonvacuity`.

The witness is built from the actual carrier: the four ligand occurrences are
the immediate official children of the final center root, their spatial points
are read from the admitted rational coordinates, and their parity is the exact
rational determinant of those coordinates.  No desired label, supplied model,
or descriptor agreement is assumed.
-/

namespace TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.LocalizedWholeStateModelNonvacuity

/-! ## Small list lemmas -/

/-- A cons filter with a definitely true Boolean head. -/
theorem filter_cons_of_pos_bool {α : Type*} (p : α → Bool) (a : α) (l : List α)
    (h : p a = true) : (a :: l).filter p = a :: l.filter p := by
  rw [List.filter_cons, if_pos h]

/-- A cons filter with a definitely false Boolean head. -/
theorem filter_cons_of_neg_bool {α : Type*} (p : α → Bool) (a : α) (l : List α)
    (h : p a = false) : (a :: l).filter p = l.filter p := by
  rw [List.filter_cons, if_neg (by simp [h])]

/-- Filtering a deduplicated list of values is the same as deduplicating the filtered list.
The predicate is a function of the value, so every occurrence of a value receives the same
decision. -/
theorem filter_dedup_eq {α : Type*} [DecidableEq α] (l : List α) (p : α → Bool) :
    l.dedup.filter p = (l.filter p).dedup := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      by_cases ha : a ∈ l
      · rw [List.dedup_cons_of_mem ha]
        rw [List.filter_cons]
        by_cases hp : p a = true
        · rw [if_pos hp, ih, List.dedup_cons_of_mem]
          exact List.mem_filter.mpr ⟨ha, hp⟩
        · rw [if_neg hp, ih]
      · rw [List.dedup_cons_of_notMem ha]
        rw [List.filter_cons]
        by_cases hp : p a = true
        · rw [if_pos hp, ih, List.filter_cons, if_pos hp, List.dedup_cons_of_notMem]
          intro present
          exact ha (List.mem_of_mem_filter present)
        · rw [if_neg hp, ih, List.filter_cons, if_neg hp]

/-- A flat map whose every term is killed by the filter is empty. -/
theorem flatMap_filter_eq_nil {α β : Type*} :
    ∀ (l : List α) (f : α → List β) (p : β → Bool),
      (∀ a ∈ l, (f a).filter p = []) →
      l.flatMap (fun a => (f a).filter p) = [] := by
  intro l
  induction l with
  | nil => intro f p _; rfl
  | cons a l ih =>
      intro f p h
      rw [List.flatMap_cons, h a (by simp),
        ih f p (fun b hb => h b (List.mem_cons_of_mem a hb))]
      rfl

/-- For a duplicate-free list, the flat map of filtered terms is the single surviving term at
the unique occurrence of the distinguished member. -/
theorem flatMap_filter_eq_of_mem_of_ne {α β : Type*} :
    ∀ (l : List α) (a : α) (f : α → List β) (p : β → Bool),
      l.Nodup → a ∈ l →
      (∀ b ∈ l, b ≠ a → (f b).filter p = []) →
      l.flatMap (fun b => (f b).filter p) = (f a).filter p := by
  intro l
  induction l with
  | nil => intro a f p _ ha _; cases ha
  | cons x xs ih =>
      intro a f p nodup ha hne
      rw [List.flatMap_cons]
      by_cases hx : x = a
      · subst a
        have notMem : x ∉ xs := (List.nodup_cons.mp nodup).1
        have tailEmpty : xs.flatMap (fun b => (f b).filter p) = [] :=
          flatMap_filter_eq_nil xs f p
            (fun b hb => hne b (List.mem_cons_of_mem x hb)
              (fun hbx => notMem (hbx ▸ hb)))
        rw [tailEmpty, List.append_nil]
      · have headEmpty : (f x).filter p = [] := hne x (by simp) hx
        rw [headEmpty, List.nil_append]
        apply ih a f p (List.nodup_cons.mp nodup).2
        · rcases List.mem_cons.mp ha with same | below
          · exact absurd same.symm hx
          · exact below
        · intro b hb
          exact hne b (List.mem_cons_of_mem x hb)

/-- Pointwise equality of the term functions gives equality of the flat maps. -/
theorem flatMap_congr_left {α β : Type*} :
    ∀ (l : List α) (f g : α → List β),
      (∀ a ∈ l, f a = g a) → l.flatMap f = l.flatMap g := by
  intro l
  induction l with
  | nil => intro f g _; rfl
  | cons a l ih =>
      intro f g h
      rw [List.flatMap_cons, List.flatMap_cons, h a (by simp),
        ih f g (fun b hb => h b (List.mem_cons_of_mem a hb))]

/-- A flat map of singleton images is the corresponding map. -/
theorem flatMap_singleton_eq_map {α β : Type*} :
    ∀ (l : List α) (f : α → β), l.flatMap (fun a => [f a]) = l.map f := by
  intro l
  induction l with
  | nil => intro f; rfl
  | cons a l ih =>
      intro f
      rw [List.flatMap_cons, ih]
      rfl

/-! ## The fixture and its four ligand slots -/


abbrev fixture : LocalizedUniversalReference.Input :=
  LocalizedWholeStateModelNonvacuity.input

/-- The four ligand atoms, in the canonical official child order. -/
def ligandAtom (i : Fin 4) : fixture.certified.Atom :=
  match i.val with
  | 0 => ⟨1, by decide⟩
  | 1 => ⟨2, by decide⟩
  | 2 => ⟨3, by decide⟩
  | _ => ⟨4, by decide⟩

/-- The official child node reached from the final center root by one real bond copy. -/
def ligandNode (i : Fin 4) : OfficialCIPNode fixture.certified.Atom :=
  (OfficialCIPNode.root centerAtom).extend (ligandAtom i) 0

/-- The carrier frame of one immediate ligand. -/
def ligandFrame (i : Fin 4) : fixture.certified.LocalizedCIPOccurrenceFrame where
  root := centerAtom
  address := [i.val]
  node := ligandNode i
  remaining := 6

theorem localizedOccurrenceSubtree_zero
    (atom : fixture.certified.Atom) (path : List Nat)
    (node : OfficialCIPNode fixture.certified.Atom) :
    fixture.certified.localizedOccurrenceSubtree atom 0 path node =
      [{ root := atom, address := path, node := node, remaining := 0 }] := rfl

theorem localizedOccurrenceSubtree_succ
    (atom : fixture.certified.Atom) (fuel : Nat) (path : List Nat)
    (node : OfficialCIPNode fixture.certified.Atom) :
    fixture.certified.localizedOccurrenceSubtree atom (fuel + 1) path node =
      { root := atom, address := path, node := node, remaining := fuel + 1 } ::
        ((fixture.certified.executableOfficialCIPChildren node).zipIdx.flatMap
          (fun child => fixture.certified.localizedOccurrenceSubtree atom fuel
            (path ++ [child.2]) child.1)) := rfl

/-- Filtering a subtree by the exact root depth keeps precisely the subtree root. -/
theorem subtree_filter_length_eq_self
    (atom : fixture.certified.Atom) (fuel : Nat) :
    ∀ (path : List Nat) (node : OfficialCIPNode fixture.certified.Atom),
      (fixture.certified.localizedOccurrenceSubtree atom fuel path node).filter
        (fun occurrence => occurrence.address.length == path.length) =
      [{ root := atom, address := path, node := node, remaining := fuel }] := by
  induction fuel with
  | zero =>
      intro path node
      rw [localizedOccurrenceSubtree_zero]
      simp
  | succ fuel ih =>
      intro path node
      rw [localizedOccurrenceSubtree_succ]
      have headKept :
          (fun occurrence : fixture.certified.LocalizedCIPOccurrenceFrame =>
              occurrence.address.length == path.length)
              { root := atom, address := path, node := node, remaining := fuel + 1 } =
            true := by
        simp
      rw [filter_cons_of_pos_bool
        (p := fun occurrence => occurrence.address.length == path.length)
        (a := { root := atom, address := path, node := node, remaining := fuel + 1 })
        (l := (fixture.certified.executableOfficialCIPChildren node).zipIdx.flatMap
          (fun child => fixture.certified.localizedOccurrenceSubtree atom fuel
            (path ++ [child.2]) child.1)) headKept]
      have tailEmpty :
          ((fixture.certified.executableOfficialCIPChildren node).zipIdx.flatMap
            (fun child => fixture.certified.localizedOccurrenceSubtree atom fuel
              (path ++ [child.2]) child.1)).filter
            (fun occurrence => occurrence.address.length == path.length) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro occurrence present kept
        rw [List.mem_flatMap] at present
        obtain ⟨child, _childPresent, below⟩ := present
        have derived := (fixture.certified.mem_localizedOccurrenceSubtree_iff atom fuel
          (path ++ [child.2]) child.1 occurrence).mp below
        have addressPrefix :=
          fixture.certified.declarativeLocalizedOccurrenceSubtree_addressPrefix derived
        have lengthLe := addressPrefix.length_le
        rw [List.length_append, List.length_singleton] at lengthLe
        have addressEq : occurrence.address.length = path.length := beq_iff_eq.mp kept
        omega
      rw [tailEmpty]

/-- Filtering a successor subtree by depth exactly one below its root keeps precisely the
immediate executable official children, in their executable sibling order. -/
theorem subtree_filter_children
    (atom : fixture.certified.Atom) (fuel : Nat) (path : List Nat)
    (node : OfficialCIPNode fixture.certified.Atom) :
    (fixture.certified.localizedOccurrenceSubtree atom (fuel + 1) path node).filter
      (fun occurrence => occurrence.address.length == path.length + 1) =
      (fixture.certified.executableOfficialCIPChildren node).zipIdx.map
        (fun child =>
          { root := atom
            address := path ++ [child.2]
            node := child.1
            remaining := fuel }) := by
  rw [localizedOccurrenceSubtree_succ]
  have headDropped :
      (fun occurrence : fixture.certified.LocalizedCIPOccurrenceFrame =>
          occurrence.address.length == path.length + 1)
          { root := atom, address := path, node := node, remaining := fuel + 1 } =
        false := by
    have notEqual : path.length ≠ path.length + 1 := by omega
    simp [notEqual]
  rw [filter_cons_of_neg_bool
    (p := fun occurrence => occurrence.address.length == path.length + 1)
    (a := { root := atom, address := path, node := node, remaining := fuel + 1 })
    (l := (fixture.certified.executableOfficialCIPChildren node).zipIdx.flatMap
      (fun child => fixture.certified.localizedOccurrenceSubtree atom fuel
        (path ++ [child.2]) child.1)) headDropped]
  rw [List.filter_flatMap]
  trans (fixture.certified.executableOfficialCIPChildren node).zipIdx.flatMap
      (fun child => (fixture.certified.localizedOccurrenceSubtree atom fuel
        (path ++ [child.2]) child.1).filter
        (fun occurrence => occurrence.address.length == (path ++ [child.2]).length))
  · apply flatMap_congr_left
    intro child _childPresent
    apply List.filter_congr
    intro occurrence _occurrencePresent
    rw [List.length_append, List.length_singleton]
  · simp only [subtree_filter_length_eq_self, flatMap_singleton_eq_map]

/-! ## Concrete bonds and the executable official children of the center root -/

@[simp] theorem bond_center_one :
    fixture.certified.moleculeGraph.bond centerAtom
      (⟨1, by decide⟩ : fixture.certified.Atom) = 1 := by
  decide +kernel

@[simp] theorem bond_center_two :
    fixture.certified.moleculeGraph.bond centerAtom
      (⟨2, by decide⟩ : fixture.certified.Atom) = 1 := by
  decide +kernel

@[simp] theorem bond_center_three :
    fixture.certified.moleculeGraph.bond centerAtom
      (⟨3, by decide⟩ : fixture.certified.Atom) = 1 := by
  decide +kernel

@[simp] theorem bond_center_four :
    fixture.certified.moleculeGraph.bond centerAtom
      (⟨4, by decide⟩ : fixture.certified.Atom) = 1 := by
  decide +kernel

@[simp] theorem root_current (atom : fixture.certified.Atom) :
    (OfficialCIPNode.root atom).current? = some atom := rfl

@[simp] theorem root_parent (atom : fixture.certified.Atom) :
    (OfficialCIPNode.root atom).parent? = none := rfl

@[simp] theorem root_isDuplicateLeaf (atom : fixture.certified.Atom) :
    (OfficialCIPNode.root atom).isDuplicateLeaf = false := rfl

/-- The executable official children of the final center root are exactly the four ligand
nodes, in the canonical index order. -/
theorem executableOfficialCIPChildren_root :
    fixture.certified.executableOfficialCIPChildren (OfficialCIPNode.root centerAtom) =
      [ligandNode 0, ligandNode 1, ligandNode 2, ligandNode 3] := by
  simp only [executableOfficialCIPChildren, executableOfficialChildCopies,
    executableOfficialNeighborCopies, root_current, root_parent, root_isDuplicateLeaf,
    Bool.false_eq_true, ↓reduceIte]
  rw [neighborSort_eq centerAtom]
  simp only [bond_center_one, bond_center_two, bond_center_three, bond_center_four,
    ligandNode, ligandAtom]
  rfl

/-- Each immediate ligand frame is an actual member of the finite occurrence carrier. -/
theorem ligandFrame_mem (i : Fin 4) :
    ligandFrame i ∈ fixture.certified.localizedOccurrences
      (LocalizedUniversalReference.carrierFuel fixture) := by
  rw [fixture.certified.mem_localizedOccurrences_iff]
  change fixture.certified.DeclarativeLocalizedOccurrenceSubtree centerAtom [] 7
    (OfficialCIPNode.root centerAtom) (ligandFrame i)
  refine DeclarativeLocalizedOccurrenceSubtree.subtreeDescendant
    (path := []) (fuel := 6) (node := OfficialCIPNode.root centerAtom)
    (child := ligandNode i) (slot := i.val) (occurrence := ligandFrame i) ?_ ?_
  · rw [executableOfficialCIPChildren_root]
    fin_cases i <;> simp [ligandNode]
  · simpa [ligandFrame] using
      (DeclarativeLocalizedOccurrenceSubtree.subtreeRoot
        (input := fixture.certified) (root := centerAtom)
        (path := [i.val]) (fuel := 6) (node := ligandNode i))

/-- The reroot cursor of one ligand, carrying the target as its incoming cut. -/
def ligandCursor (i : Fin 4) :
    fixture.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel fixture) where
  occurrence := ⟨ligandFrame i, ligandFrame_mem i⟩
  previous? := some target

/-- The actual four-ligand frame: the four immediate children of the final center root. -/
def frame : fixture.certified.LocalizedOccurrenceFourLigandFrame
    (LocalizedUniversalReference.carrierFuel fixture) where
  cursors := [ligandCursor 0, ligandCursor 1, ligandCursor 2, ligandCursor 3]
  length_eq := rfl

@[simp] theorem frame_cursorAt_zero : frame.cursorAt 0 = ligandCursor 0 := by
  simp [LocalizedOccurrenceFourLigandFrame.cursorAt, frame]

@[simp] theorem frame_cursorAt_one : frame.cursorAt 1 = ligandCursor 1 := by
  simp [LocalizedOccurrenceFourLigandFrame.cursorAt, frame]

@[simp] theorem frame_cursorAt_two : frame.cursorAt 2 = ligandCursor 2 := by
  simp [LocalizedOccurrenceFourLigandFrame.cursorAt, frame]

@[simp] theorem frame_cursorAt_three : frame.cursorAt 3 = ligandCursor 3 := by
  simp [LocalizedOccurrenceFourLigandFrame.cursorAt, frame]

/-- Indexed access to the explicit frame is the corresponding ligand cursor. -/
@[simp] theorem frame_cursorAt (i : Fin 4) : frame.cursorAt i = ligandCursor i := by
  fin_cases i
  · exact frame_cursorAt_zero
  · exact frame_cursorAt_one
  · exact frame_cursorAt_two
  · exact frame_cursorAt_three

/-! ## The actual outward carrier children -/

@[simp] theorem target_frame_root : target.1.root = centerAtom := by
  simp [target, center]

@[simp] theorem target_frame_address : target.1.address = [] := by
  simp [target, center]

/-- The outward-child Boolean condition used by the reroot carrier. -/
def outwardPredicate
    (candidate : fixture.certified.LocalizedCIPOccurrenceFrame) : Bool :=
  candidate.root == centerAtom &&
    candidate.address.length == 1 &&
    candidate.address.dropLast == []

/-- A subtree rooted away from the center has no outward child of the center. -/
theorem subtree_filter_outward_eq_nil
    (atom : fixture.certified.Atom) (different : atom ≠ centerAtom)
    (fuel : Nat) (path : List Nat)
    (node : OfficialCIPNode fixture.certified.Atom) :
    (fixture.certified.localizedOccurrenceSubtree atom fuel path node).filter
      outwardPredicate = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro candidate present kept
  rw [outwardPredicate, Bool.and_eq_true, Bool.and_eq_true] at kept
  have rootEquality : candidate.root = atom :=
    fixture.certified.declarativeLocalizedOccurrenceSubtree_root_eq
      ((fixture.certified.mem_localizedOccurrenceSubtree_iff atom fuel path node
        candidate).mp present)
  exact different (rootEquality.symm.trans (beq_iff_eq.mp kept.1.1))

/-- The carrier enumerates exactly the five fixture atoms. -/
theorem localizedOccurrences_fixture :
    fixture.certified.localizedOccurrences 6 =
      ((List.finRange 5).flatMap
        (fun atom => fixture.certified.localizedOccurrencesAtAtom 6 atom)).dedup := rfl

/-- The center subtree contributes exactly the four ligand children. -/
theorem center_filter_eq_children :
    (fixture.certified.localizedOccurrencesAtAtom 6 centerAtom).filter outwardPredicate =
      [ligandFrame 0, ligandFrame 1, ligandFrame 2, ligandFrame 3] := by
  trans (fixture.certified.localizedOccurrencesAtAtom 6 centerAtom).filter
      (fun candidate => candidate.address.length == 1)
  · apply List.filter_congr
    intro candidate present
    rw [Bool.eq_iff_iff]
    constructor
    · intro kept
      rw [outwardPredicate, Bool.and_eq_true, Bool.and_eq_true] at kept
      exact kept.1.2
    · intro lengthOne
      rw [outwardPredicate, Bool.and_eq_true, Bool.and_eq_true]
      have present' : candidate ∈ fixture.certified.localizedOccurrenceSubtree
          centerAtom 7 [] (OfficialCIPNode.root centerAtom) := present
      have rootEquality : candidate.root = centerAtom :=
        fixture.certified.declarativeLocalizedOccurrenceSubtree_root_eq
          ((fixture.certified.mem_localizedOccurrenceSubtree_iff centerAtom 7 []
            (OfficialCIPNode.root centerAtom) candidate).mp present')
      refine ⟨⟨beq_iff_eq.mpr rootEquality, lengthOne⟩, ?_⟩
      obtain ⟨value, addressEq⟩ :=
        List.length_eq_one_iff.mp (beq_iff_eq.mp lengthOne)
      rw [addressEq]
      simp
  · change (fixture.certified.localizedOccurrenceSubtree centerAtom (6 + 1) []
      (OfficialCIPNode.root centerAtom)).filter
      (fun candidate => candidate.address.length == ([] : List Nat).length + 1) =
        [ligandFrame 0, ligandFrame 1, ligandFrame 2, ligandFrame 3]
    rw [subtree_filter_children centerAtom 6 [] (OfficialCIPNode.root centerAtom),
      executableOfficialCIPChildren_root]
    simp [ligandFrame, ligandNode, ligandAtom]

/-- **The actual outward child frames of the root target are the four ligand frames.** -/
theorem outwardChildFrames_target :
    fixture.certified.localizedCarrierOutwardChildFrames
      (fuel := LocalizedUniversalReference.carrierFuel fixture) target.1 =
      [ligandFrame 0, ligandFrame 1, ligandFrame 2, ligandFrame 3] := by
  rw [CertifiedLocalizedCIPInput.localizedCarrierOutwardChildFrames]
  simp only [target_frame_root, target_frame_address, List.length_nil, Nat.zero_add,
    List.dropLast_nil]
  change (fixture.certified.localizedOccurrences 6).filter outwardPredicate = _
  rw [localizedOccurrences_fixture, filter_dedup_eq, List.filter_flatMap]
  have survivor := flatMap_filter_eq_of_mem_of_ne (List.finRange 5) centerAtom
    (fixture.certified.localizedOccurrencesAtAtom 6) outwardPredicate
    (List.nodup_finRange 5) (List.mem_finRange centerAtom)
    (by
      intro atom _atomPresent different
      exact subtree_filter_outward_eq_nil atom different 7 [] (OfficialCIPNode.root atom))
  trans (List.filter outwardPredicate
      (fixture.certified.localizedOccurrencesAtAtom 6 centerAtom)).dedup
  · exact congrArg List.dedup survivor
  · rw [center_filter_eq_children, List.dedup_eq_self]
    decide +kernel

/-- **The actual four-ligand frame is declaratively derived from the target.** -/
theorem frame_declarative :
    fixture.certified.DeclarativeLocalizedOccurrenceFourLigandFrame target frame := by
  unfold CertifiedLocalizedCIPInput.DeclarativeLocalizedOccurrenceFourLigandFrame
  constructor
  · unfold CertifiedLocalizedCIPInput.DeclarativeLocalizedRerootChildren
    constructor
    · rw [intendedLocalizedRerootChildFrames_eq_outwardChildFrames_of_address_nil
        fixture.certified target target_frame_address, outwardChildFrames_target]
      simp [frame, ligandCursor]
    · intro child present
      simp [frame] at present
      rcases present with rfl | rfl | rfl | rfl <;> rfl
  · rfl

/-! ## Primitive atom, atomic-number, and coordinate facts -/

theorem ligandNode_current (i : Fin 4) :
    (ligandNode i).current? = some (ligandAtom i) := rfl

theorem ligandNode_provenance (i : Fin 4) :
    (ligandNode i).provenance = OfficialCIPNodeProvenance.realAtom := by
  rw [ligandNode, OfficialCIPNode.extend_provenance]
  apply OfficialCIPNode.childProvenance_real
  fin_cases i <;> decide +kernel

/-- The graph atomic numbers of the four ligand atoms, in slot order. -/
theorem atomZ_ligand (i : Fin 4) :
    fixture.certified.moleculeGraph.atomZ (ligandAtom i) =
      match i.val with
      | 0 => 9
      | 1 => 17
      | 2 => 35
      | _ => 53 := by
  rw [CertifiedLocalizedCIPInput.moleculeGraph,
    SemanticMolecule.toLocalizedMoleculeGraph_atomZ]
  fin_cases i <;> rfl

@[simp] theorem atomZ_ligand_zero :
    fixture.certified.moleculeGraph.atomZ (ligandAtom 0) = 9 := by
  rw [atomZ_ligand]

@[simp] theorem atomZ_ligand_one :
    fixture.certified.moleculeGraph.atomZ (ligandAtom 1) = 17 := by
  rw [atomZ_ligand]

@[simp] theorem atomZ_ligand_two :
    fixture.certified.moleculeGraph.atomZ (ligandAtom 2) = 35 := by
  rw [atomZ_ligand]

@[simp] theorem atomZ_ligand_three :
    fixture.certified.moleculeGraph.atomZ (ligandAtom 3) = 53 := by
  rw [atomZ_ligand]

/-- A real ligand cursor reads its root atomic number from the molecular graph. -/
theorem rootAtomicNumberAt_ligand (i : Fin 4) :
    frame.rootAtomicNumberAt fixture.certified i =
      fixture.certified.moleculeGraph.atomZ (ligandAtom i) := by
  apply rootAtomicNumberAt_eq_atomZ_of_real
  · simpa [frame_cursorAt, ligandCursor, ligandFrame] using ligandNode_provenance i
  · simpa [frame_cursorAt, ligandCursor, ligandFrame] using ligandNode_current i

@[simp] theorem rootAtomicNumberAt_zero :
    frame.rootAtomicNumberAt fixture.certified 0 = 9 := by
  rw [rootAtomicNumberAt_ligand, atomZ_ligand_zero]

@[simp] theorem rootAtomicNumberAt_one :
    frame.rootAtomicNumberAt fixture.certified 1 = 17 := by
  rw [rootAtomicNumberAt_ligand, atomZ_ligand_one]

@[simp] theorem rootAtomicNumberAt_two :
    frame.rootAtomicNumberAt fixture.certified 2 = 35 := by
  rw [rootAtomicNumberAt_ligand, atomZ_ligand_two]

@[simp] theorem rootAtomicNumberAt_three :
    frame.rootAtomicNumberAt fixture.certified 3 = 53 := by
  rw [rootAtomicNumberAt_ligand, atomZ_ligand_three]

/-- The four ligand slots carry pairwise distinct atomic numbers. -/
theorem frame_separated :
    fixture.certified.ConstitutionallyAtomicNumberSeparatedFrame frame := by
  intro left right different
  fin_cases left <;> fin_cases right <;> simp_all

/-- The exact rational ligand coordinates read from the admitted fixture, in slot order. -/
def pointsAt (i : Fin 4) : CartesianPoint3 :=
  match i.val with
  | 0 => { x := -1, y := -1, z := 1 }
  | 1 => { x := -1, y := 1, z := -1 }
  | 2 => { x := 1, y := -1, z := -1 }
  | _ => { x := 1, y := 1, z := 1 }

/-- Every ligand cursor reads its actual admitted rational position. -/
theorem frame_spatial (i : Fin 4) :
    fixture.certified.localizedRerootCursorSpatialPoint? (frame.cursorAt i) =
      some (pointsAt i) := by
  fin_cases i <;>
    simp [CertifiedLocalizedCIPInput.localizedRerootCursorSpatialPoint?,
      CertifiedLocalizedCIPInput.spatialPointAt?, frame_cursorAt, ligandCursor,
      ligandFrame, ligandNode, ligandAtom, pointsAt, fixture, SemanticMolecule.atomCount,
      LocalizedWholeStateModelNonvacuity.input,
      LocalizedWholeStateModelNonvacuity.localizedSource,
      LocalizedWholeStateModelNonvacuity.certifiedSource,
      LocalizedWholeStateModelNonvacuity.halomethaneSource]

/-- The written slot order has positive exact oriented volume, hence anticlockwise parity. -/
theorem writtenParity :
    AuthoritativeChemicalInput.RationalTetrahedralInputParity
      [pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3]
      TetrahedralInputParity.anticlockwise := by
  refine ⟨pointsAt 0, pointsAt 1, pointsAt 2, pointsAt 3, rfl, ?_⟩
  norm_num [CartesianPoint3.orientedVolume, pointsAt]

/-! ## The actual positive reference-state witness -/

/-- The tracked priority order produced by the constitutional normalization is the descending
atomic-number order `[3, 2, 1, 0]` on the four ligand slots.  This is forced by the actual
comparison relation, not assumed: the four atomic numbers `9, 17, 35, 53` form a strict total
order, and any permutation of the four slots that is pairwise decreasing in those numbers must
be exactly the slot order `[3, 2, 1, 0]`. -/
theorem trackedOrder_eq_three_two_one_zero
    (tracked : TrackedLocalizedLigandOrder)
    (perm : tracked.highestFirst.Perm (List.finRange 4))
    (pairwise : tracked.highestFirst.Pairwise (fun left right =>
      frame.rootAtomicNumberAt fixture.certified right <
        frame.rootAtomicNumberAt fixture.certified left)) :
    tracked.highestFirst = [3, 2, 1, 0] := by
  have reversedPerm : ([3, 2, 1, 0] : List (Fin 4)).Perm (List.finRange 4) := by
    decide +kernel
  have rightPairwise :
      ([3, 2, 1, 0] : List (Fin 4)).Pairwise (fun left right =>
        frame.rootAtomicNumberAt fixture.certified right <
          frame.rootAtomicNumberAt fixture.certified left) := by
    simp [List.forall_mem_cons, rootAtomicNumberAt_zero, rootAtomicNumberAt_one,
      rootAtomicNumberAt_two, rootAtomicNumberAt_three]
  exact List.Perm.eq_of_pairwise
    (fun a b _ _ forward backward => by
      fin_cases a <;> fin_cases b <;>
        simp [rootAtomicNumberAt_zero, rootAtomicNumberAt_one, rootAtomicNumberAt_two,
          rootAtomicNumberAt_three] at forward backward ⊢)
    pairwise rightPairwise (perm.trans reversedPerm.symm)

/-- **The actual generated reference state is chiral `S` at the final center occurrence.**
The label is not assumed: it is the one returned by the physical-frame readback theorem after
identifying the actual tracked priority order with `[3, 2, 1, 0]`. -/
theorem referenceState_target_eq_chiral_S :
    LocalizedUniversalReference.referenceState fixture target = some (.chiral .S) := by
  obtain ⟨tracked, hTracked, _hPseudo, hReader⟩ :=
    referenceState_reader_eq_chiral_of_physicalFrame fixture
      LocalizedWholeStateModelNonvacuity.input_noDoubleRecords target frame
      frame_declarative frame_separated center target_realCenterNode pointsAt
      frame_spatial TetrahedralInputParity.anticlockwise writtenParity
  obtain ⟨trackedConstitutional, hConstitutional, hPerm, hPairwise, _hPseudoConstitutional⟩ :=
    exists_localizedConstitutionalFrame_trackedOrder fixture.certified target
      (fixture.certified.localizedDependencyView
        (LocalizedUniversalReference.referenceState fixture) target)
      frame frame_declarative frame_separated
  have hEqualTracked : tracked = trackedConstitutional :=
    Option.some_inj.mp (hTracked.symm.trans hConstitutional)
  have hHighest : tracked.highestFirst = [3, 2, 1, 0] := by
    rw [hEqualTracked]
    exact trackedOrder_eq_three_two_one_zero trackedConstitutional hPerm hPairwise
  have hEven : RawMolecule.permutationIsEven
      (tracked.highestFirst.map Fin.val) = true := by
    rw [hHighest]
    decide +kernel
  rw [hReader, hEven]
  rfl

/-- **Nonvacuity of the actual generated reference state on the admitted fixture**: the state is
a positive chiral `some` value at the root target, not `none` and not an existential model. -/
theorem exists_referenceState_target_eq_chiral :
    ∃ rs, LocalizedUniversalReference.referenceState fixture target = some (.chiral rs) :=
  ⟨_, referenceState_target_eq_chiral_S⟩

end TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.filter_cons_of_pos_bool
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.filter_cons_of_neg_bool
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.filter_dedup_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.flatMap_filter_eq_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.flatMap_filter_eq_of_mem_of_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.flatMap_congr_left
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.flatMap_singleton_eq_map
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.fixture
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.ligandAtom
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.ligandNode
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.ligandFrame
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.localizedOccurrenceSubtree_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.localizedOccurrenceSubtree_succ
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.subtree_filter_length_eq_self
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.subtree_filter_children
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.bond_center_one
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.bond_center_two
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.bond_center_three
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.bond_center_four
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.root_current
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.root_parent
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.root_isDuplicateLeaf
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.executableOfficialCIPChildren_root
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.ligandFrame_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.ligandCursor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.frame
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.frame_cursorAt_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.frame_cursorAt_one
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.frame_cursorAt_two
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.frame_cursorAt_three
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.frame_cursorAt
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.target_frame_root
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.target_frame_address
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.outwardPredicate
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.subtree_filter_outward_eq_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.localizedOccurrences_fixture
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.center_filter_eq_children
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.outwardChildFrames_target
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.frame_declarative
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.ligandNode_current
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.ligandNode_provenance
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.atomZ_ligand
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.atomZ_ligand_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.atomZ_ligand_one
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.atomZ_ligand_two
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.atomZ_ligand_three
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.rootAtomicNumberAt_ligand
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.rootAtomicNumberAt_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.rootAtomicNumberAt_one
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.rootAtomicNumberAt_two
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.rootAtomicNumberAt_three
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.frame_separated
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.pointsAt
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.frame_spatial
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.writtenParity
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.trackedOrder_eq_three_two_one_zero
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.referenceState_target_eq_chiral_S
assert_kernel_only TetraStereo.OneCenter.LocalizedActualReferencePositiveWitness.exists_referenceState_target_eq_chiral
