import TetraStereo.OneCenter.LocalizedMultipleBondShapeRoleRecovery
import TetraStereo.OneCenter.AuthoritativeLocalizedRule1bConformance
import TetraStereo.OneCenter.Rule1bSourceProfileFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false


















































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-! ## The ring duplicate distance bound

The only new geometric input is the following bound.  It uses the actual carrier occurrence of the
real cursor (to read the stored history head as the current atom), the executable child
enumeration (to exclude the stored parent), and positive-bond adjacency (to exclude the current
atom).  No acyclicity is used. -/

/-- **Ring duplicate distance bound at a real actual cursor.**

If a real actual carrier cursor emits a ring-duplicate executable child at represented distance
`distance`, then `distance + 1` is strictly below the cursor's visible Rule-1b distance.

The ring target occurs on the stored reversed history.  Its first index cannot be the current
atom (`distance = depth`) because adjacency is loopless, and it cannot be the stored immediate
parent (`distance = depth - 1`) because the executable copy list removes the zero-copy back edge.
The first reversed-history index is therefore at most `depth - 2`. -/
theorem executableRingChild_distance_add_one_lt_parent
    (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (cursorReal : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (child : OfficialCIPNode input.Atom) (distance : Nat)
    (present : child ∈ input.executableOfficialCIPChildren cursor.occurrence.1.node)
    (ring : child.provenance = OfficialCIPNodeProvenance.ringDuplicate distance) :
    distance + 1 < cursor.occurrence.1.node.rule1bRootDistance := by
  obtain ⟨current, _path, currentObserved, headObserved, _provenance, _pathIsPath,
    _supportReverse, _penultimateEq⟩ :=
    input.carrierOccurrence_realPath_of_provenance_real cursor.occurrence cursorReal
  obtain ⟨next, childEqual, notParent⟩ :=
    input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
      cursor.occurrence.1.node child present (Or.inr ⟨distance, ring⟩)
  have childCurrent : child.current? = some next := by
    rw [childEqual]
    rfl
  have adjacent : input.moleculeGraph.Adj current next :=
    input.adj_of_mem_executableOfficialCIPChildren cursor.occurrence.1.node child
      current next currentObserved childCurrent present
  have firstIndex :
      firstIndexOf? next cursor.occurrence.1.node.history.reverse = some distance :=
    input.executableOfficialCIPChildren_ringDuplicate_firstIndex
      cursor.occurrence.1.node child present next distance childCurrent ring
  have historyGet :
      cursor.occurrence.1.node.history.reverse[distance]? = some next :=
    Rule1bSourceProfile.firstIndexOf?_eq_some_imp_getElem?
      next cursor.occurrence.1.node.history.reverse distance firstIndex
  have parentDistance : cursor.occurrence.1.node.rule1bRootDistance =
      cursor.occurrence.1.node.history.length - 1 := by
    simp [OfficialCIPNode.rule1bRootDistance, OfficialCIPNode.depth, cursorReal]
  have loopFalse : ¬ input.moleculeGraph.Adj current current := by
    simp [MoleculeGraph.Adj, input.moleculeGraph.bond_self]
  obtain ⟨historyTail, historyEq⟩ := List.head?_eq_some_iff.mp headObserved
  cases historyTail with
  | nil =>
      -- The root history is the singleton current atom; the ring target would be current.
      have historySingleton : cursor.occurrence.1.node.history = [current] := by
        simp [historyEq]
      have getSingleton :
          ([current] : List input.Atom)[distance]? = some next := by
        simpa [historySingleton] using historyGet
      have distanceZero : distance = 0 := by
        have bound := (List.getElem?_eq_some_iff.mp getSingleton).1
        simp only [List.length_singleton] at bound
        omega
      have getZero : ([current] : List input.Atom)[0]? = some next := by
        simpa [distanceZero] using getSingleton
      have nextEq : next = current := by
        have someEq : (some current : Option input.Atom) = some next := by
          simpa using getZero
        exact (Option.some.inj someEq).symm
      exact absurd (by simpa [nextEq] using adjacent) loopFalse
  | cons parent tail =>
      -- The history is `current :: parent :: tail`; the reversed history ends in
      -- `parent, current`.  The ring index is below the tail length.
      have historyShape : cursor.occurrence.1.node.history =
          current :: parent :: tail := by
        simp [historyEq]
      have parentObserved : cursor.occurrence.1.node.parent? = some parent := by
        simp [historyShape, OfficialCIPNode.parent?]
      have nextNeParent : next ≠ parent := by
        intro same
        exact notParent (by rw [same]; exact parentObserved)
      have reversedShape : cursor.occurrence.1.node.history.reverse =
          tail.reverse ++ [parent, current] := by
        simp [historyShape]
      have appendedGet :
          (tail.reverse ++ [parent, current])[distance]? = some next := by
        simpa [reversedShape] using historyGet
      have bound : distance < tail.length + 2 := by
        have raw := (List.getElem?_eq_some_iff.mp appendedGet).1
        simpa using raw
      have historyLength : cursor.occurrence.1.node.history.length =
          tail.length + 2 := by
        simp [historyShape]
      by_cases small : distance < tail.length
      · rw [parentDistance, historyLength]
        omega
      · have large : tail.length ≤ distance := Nat.le_of_not_lt small
        have largeReverse : tail.reverse.length ≤ distance := by
          simpa using large
        have tailGet :
            [parent, current][distance - tail.length]? = some next := by
          have split := List.getElem?_append_right
            (l₁ := tail.reverse) (l₂ := [parent, current]) (i := distance)
            largeReverse
          rw [split] at appendedGet
          simpa using appendedGet
        have indexSmall : distance - tail.length < 2 := by omega
        have casesIndex : distance - tail.length = 0 ∨
            distance - tail.length = 1 := by omega
        rcases casesIndex with atParent | atCurrent
        · have observedParent :
              ([parent, current] : List input.Atom)[distance - tail.length]? =
                some parent := by
            simp [atParent]
          rw [observedParent] at tailGet
          have nextEqParent : next = parent :=
            (Option.some.inj tailGet).symm
          exact absurd nextEqParent nextNeParent
        · have observedCurrent :
              ([parent, current] : List input.Atom)[distance - tail.length]? =
                some current := by
            simp [atCurrent]
          rw [observedCurrent] at tailGet
          have nextEqCurrent : next = current :=
            (Option.some.inj tailGet).symm
          exact absurd (by simpa [nextEqCurrent] using adjacent) loopFalse

/-- The child-facing form of the ring bound: the emitted child's own visible Rule-1b distance is
strictly more than one below the real parent cursor's distance. -/
theorem executableRingChild_rule1bRootDistance_add_one_lt_parent
    (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (cursorReal : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (child : OfficialCIPNode input.Atom) (distance : Nat)
    (present : child ∈ input.executableOfficialCIPChildren cursor.occurrence.1.node)
    (ring : child.provenance = OfficialCIPNodeProvenance.ringDuplicate distance) :
    child.rule1bRootDistance + 1 < cursor.occurrence.1.node.rule1bRootDistance := by
  have bound := input.executableRingChild_distance_add_one_lt_parent
    cursor cursorReal child distance present ring
  have childDistance : child.rule1bRootDistance = distance := by
    simp [OfficialCIPNode.rule1bRootDistance, ring]
  rw [childDistance]
  exact bound

/-! ## Ring-aware local role recovery

The accepted three-way classification had only an outward real child, an outward multiple-bond
duplicate and the actual reverse carrier parent; the ring branch was eliminated by acyclicity.
Here the ring branch is retained as a fourth possibility, and the two real branches are grouped by
their visible distance relation. -/

/-- **Ring-aware child role recovery at a real reroot cursor.**

Every intended child frame of a real cursor is exactly one of:

1. a real-provenance child with `childD = parentD + 1` (outward real child) or
   `childD + 1 = parentD` (actual reverse carrier parent), and non-duplicate;
2. an outward multiple-bond duplicate with `childD = parentD` and duplicate flag;
3. an outward ring duplicate with `childD + 1 < parentD` and duplicate flag.

The first case deliberately groups the outward real child and the actual reverse carrier parent:
both are real atoms, and only the successor direction differs.  This is the form that is visible
from the erased shape. -/
theorem child_role_recovery_of_real_cursor_ringAware
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (cursorReal : cursor.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (frame : input.LocalizedCIPOccurrenceFrame)
    (framePresent : frame ∈ input.intendedLocalizedRerootChildFrames cursor) :
    (frame.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
        (frame.node.rule1bRootDistance =
            cursor.occurrence.1.node.rule1bRootDistance + 1 ∨
          frame.node.rule1bRootDistance + 1 =
            cursor.occurrence.1.node.rule1bRootDistance) ∧
        frame.node.isDuplicateLeaf = false) ∨
      (∃ distance, frame.node.provenance =
          OfficialCIPNodeProvenance.multipleBondDuplicate distance ∧
        frame.node.rule1bRootDistance =
          cursor.occurrence.1.node.rule1bRootDistance ∧
        frame.node.isDuplicateLeaf = true) ∨
      (∃ distance, frame.node.provenance =
          OfficialCIPNodeProvenance.ringDuplicate distance ∧
        frame.node.rule1bRootDistance + 1 <
          cursor.occurrence.1.node.rule1bRootDistance ∧
        frame.node.isDuplicateLeaf = true) := by
  have cursorNotDup : cursor.occurrence.1.node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real _ cursorReal
  have cursorDistance : cursor.occurrence.1.node.rule1bRootDistance =
      cursor.occurrence.1.address.length :=
    input.rule1bRootDistance_eq_address_length_of_real cursor.occurrence cursorReal
  have neighborPresent :
      frame ∈ input.localizedRerootNeighborFrames (fuel := carrierFuel)
        cursor.occurrence.1 := by
    unfold intendedLocalizedRerootChildFrames at framePresent
    rw [if_neg (by simpa using cursorNotDup)] at framePresent
    cases previousEq : cursor.previous? with
    | none => simpa only [previousEq] using framePresent
    | some previous =>
        exact List.mem_of_mem_filter (by
          simpa only [previousEq] using framePresent)
  rw [localizedRerootNeighborFrames, List.mem_append] at neighborPresent
  rcases neighborPresent with parentMem | outwardMem
  · -- The actual reverse carrier parent: real, one sphere above the cursor.
    rw [localizedCarrierParentFrames, List.mem_filter] at parentMem
    obtain ⟨frameCarrier, conditions⟩ := parentMem
    simp only [Bool.and_eq_true, beq_iff_eq] at conditions
    obtain ⟨⟨frameRoot, frameLength⟩, frameDrop⟩ := conditions
    have cursorNonroot : cursor.occurrence.1.address ≠ [] := by
      intro empty
      rw [empty] at frameLength
      simp at frameLength
    obtain ⟨parent, parentPresent, parentRoot, parentAddress, _parentRemaining,
      parentActive, ⟨_next, _copyIndex, _cursorExtend⟩, _parentCurrent⟩ :=
      input.exists_parentFrame_of_mem_localizedOccurrences
        (fuel := carrierFuel) cursor.occurrence.2 cursorNonroot
    have frameDerived : input.DeclarativeLocalizedOccurrence carrierFuel frame :=
      (input.mem_localizedOccurrences_iff carrierFuel frame).mp frameCarrier
    have parentDerived : input.DeclarativeLocalizedOccurrence carrierFuel parent :=
      (input.mem_localizedOccurrences_iff carrierFuel parent).mp parentPresent
    have sameRoot : frame.root = parent.root := by
      rw [frameRoot, parentRoot]
    have sameAddress : frame.address = parent.address := by
      rw [frameDrop, parentAddress]
    have frameEqParent : frame = parent :=
      input.declarativeLocalizedOccurrence_functional_at_root_address
        frameDerived parentDerived sameRoot sameAddress
    have frameReal : frame.node.provenance =
        OfficialCIPNodeProvenance.realAtom := by
      rw [frameEqParent]
      exact parentActive.1
    have frameDistance : frame.node.rule1bRootDistance =
        frame.address.length :=
      input.rule1bRootDistance_eq_address_length_of_real
        ⟨frame, frameCarrier⟩ frameReal
    refine Or.inl ⟨frameReal, Or.inr ?_, ?_⟩
    · omega
    · exact input.isDuplicateLeaf_eq_false_of_provenance_real _ frameReal
  · -- An outward executable child.
    rw [localizedCarrierOutwardChildFrames, List.mem_filter] at outwardMem
    obtain ⟨frameCarrier, conditions⟩ := outwardMem
    simp only [Bool.and_eq_true, beq_iff_eq] at conditions
    obtain ⟨⟨frameRoot, frameLength⟩, frameDrop⟩ := conditions
    have frameNonempty : frame.address ≠ [] := by
      intro empty
      rw [empty] at frameLength
      simp at frameLength
    have cursorDerived :
        input.DeclarativeLocalizedOccurrence carrierFuel cursor.occurrence.1 :=
      (input.mem_localizedOccurrences_iff carrierFuel cursor.occurrence.1).mp
        cursor.occurrence.2
    have frameDerived : input.DeclarativeLocalizedOccurrence carrierFuel frame :=
      (input.mem_localizedOccurrences_iff carrierFuel frame).mp frameCarrier
    have frameAddress : frame.address =
        cursor.occurrence.1.address ++ [frame.address.getLast frameNonempty] := by
      calc frame.address
          = frame.address.dropLast ++ [frame.address.getLast frameNonempty] :=
              (List.dropLast_concat_getLast frameNonempty).symm
        _ = cursor.occurrence.1.address ++
              [frame.address.getLast frameNonempty] := by
              rw [frameDrop]
    obtain ⟨child, childAtSlot, childFrameEq⟩ :=
      input.declarativeLocalizedOccurrence_immediate_child cursorDerived frameDerived
        frameRoot (frame.address.getLast frameNonempty) frameAddress
    have childPresent :
        child ∈ input.executableOfficialCIPChildren cursor.occurrence.1.node :=
      List.fst_mem_of_mem_zipIdx childAtSlot
    have frameNode : frame.node = child := by
      simpa using congrArg
        (fun frame : input.LocalizedCIPOccurrenceFrame => frame.node) childFrameEq
    obtain ⟨next, copyIndex, childExtend⟩ :=
      input.mem_executableOfficialCIPChildren_extend cursor.occurrence.1.node child
        childPresent
    by_cases zero : copyIndex = 0
    · subst copyIndex
      by_cases visited : next ∈ cursor.occurrence.1.node.history
      · -- Outward ring duplicate: the new distance bound, with no acyclicity.
        have ringProvenance : child.provenance =
            OfficialCIPNodeProvenance.ringDuplicate
              (cursor.occurrence.1.node.duplicateRootDistance next) := by
          rw [childExtend, OfficialCIPNode.extend_provenance]
          exact OfficialCIPNode.childProvenance_ring_duplicate _ _ visited
        have ringBound := input.executableRingChild_distance_add_one_lt_parent
          cursor cursorReal child
          (cursor.occurrence.1.node.duplicateRootDistance next)
          childPresent ringProvenance
        have frameProvenance : frame.node.provenance =
            OfficialCIPNodeProvenance.ringDuplicate
              (cursor.occurrence.1.node.duplicateRootDistance next) := by
          rw [frameNode]
          exact ringProvenance
        have frameDistance : frame.node.rule1bRootDistance =
            cursor.occurrence.1.node.duplicateRootDistance next := by
          simp [OfficialCIPNode.rule1bRootDistance, frameProvenance]
        refine Or.inr (Or.inr ⟨_, frameProvenance, ?_, ?_⟩)
        · rw [frameDistance]
          exact ringBound
        · simp [OfficialCIPNode.isDuplicateLeaf, frameProvenance]
      · -- Outward real zero-copy child: one sphere below in address, one above in distance.
        have realProvenance : child.provenance =
            OfficialCIPNodeProvenance.realAtom := by
          rw [childExtend, OfficialCIPNode.extend_provenance]
          exact OfficialCIPNode.childProvenance_real _ _ visited
        have frameReal : frame.node.provenance =
            OfficialCIPNodeProvenance.realAtom := by
          rw [frameNode]
          exact realProvenance
        have frameDistance : frame.node.rule1bRootDistance =
            frame.address.length :=
          input.rule1bRootDistance_eq_address_length_of_real
            ⟨frame, frameCarrier⟩ frameReal
        refine Or.inl ⟨frameReal, Or.inl ?_, ?_⟩
        · omega
        · exact input.isDuplicateLeaf_eq_false_of_provenance_real _ frameReal
    · -- Outward positive-copy multiple-bond duplicate.
      have duplicateProvenance : child.provenance =
          OfficialCIPNodeProvenance.multipleBondDuplicate
            cursor.occurrence.1.node.depth := by
        rw [childExtend, OfficialCIPNode.extend_provenance]
        exact OfficialCIPNode.childProvenance_copy_pos _ _ zero
      have frameProvenance : frame.node.provenance =
          OfficialCIPNodeProvenance.multipleBondDuplicate
            cursor.occurrence.1.node.depth := by
        rw [frameNode]
        exact duplicateProvenance
      have frameDistance : frame.node.rule1bRootDistance =
          cursor.occurrence.1.node.rule1bRootDistance := by
        simp [OfficialCIPNode.rule1bRootDistance, frameProvenance, cursorReal]
      refine Or.inr (Or.inl ⟨cursor.occurrence.1.node.depth, frameProvenance,
        frameDistance, ?_⟩)
      simp [OfficialCIPNode.isDuplicateLeaf, frameProvenance]

end CertifiedLocalizedCIPInput

/-! ## Ring-aware shape-side role masks

The comparison-visible duplicate bit must now also cover the ring case.  A real child has visible
distance `parentD + 1`, the reverse carrier parent has `parentD - 1`, and a multiple-bond
duplicate has `parentD`; only the ring duplicate has `childD + 1 < parentD`.  Hence the
shape-computable bit is

`ringAwareDuplicateWithParent parentD childD = (childD == parentD) || (childD + 1 < parentD)`.

The root is made real by comparing its distance with the impossible parent distance `rootD + 1`. -/

namespace LocalizedCumulativeBranchShape

/-- Shape-computable duplicate role bit, including the ring-duplicate case. -/
def ringAwareDuplicateWithParent (parentDistance distance : Nat) : Bool :=
  (distance == parentDistance) || decide (distance + 1 < parentDistance)

/-- A child whose visible distance equals its parent's is a duplicate. -/
theorem ringAwareDuplicateWithParent_true_of_eq (parentDistance distance : Nat)
    (equal : distance = parentDistance) :
    ringAwareDuplicateWithParent parentDistance distance = true := by
  have same : (distance == parentDistance) = true := by
    rw [equal]
    exact beq_self_eq_true parentDistance
  rw [ringAwareDuplicateWithParent, same]
  rfl

/-- A child whose visible distance is more than one below its parent's is a ring duplicate. -/
theorem ringAwareDuplicateWithParent_true_of_succ_lt (parentDistance distance : Nat)
    (less : distance + 1 < parentDistance) :
    ringAwareDuplicateWithParent parentDistance distance = true := by
  have strict : decide (distance + 1 < parentDistance) = true :=
    decide_eq_true less
  rw [ringAwareDuplicateWithParent, strict]
  simp

/-- An outward real child, one step below in address and one step above in visible distance, is
not a duplicate. -/
theorem ringAwareDuplicateWithParent_false_of_eq_succ (parentDistance distance : Nat)
    (equal : distance = parentDistance + 1) :
    ringAwareDuplicateWithParent parentDistance distance = false := by
  have different : (distance == parentDistance) = false := by
    rw [equal]
    exact beq_eq_false_iff_ne.mpr (by omega)
  have notStrict : decide (distance + 1 < parentDistance) = false := by
    rw [equal]
    exact decide_eq_false_iff_not.mpr (by omega)
  rw [ringAwareDuplicateWithParent, different, notStrict]
  rfl

/-- The actual reverse carrier parent, one step above in address and one step below in visible
distance, is not a duplicate. -/
theorem ringAwareDuplicateWithParent_false_of_succ_eq (parentDistance distance : Nat)
    (equal : distance + 1 = parentDistance) :
    ringAwareDuplicateWithParent parentDistance distance = false := by
  have different : (distance == parentDistance) = false := by
    rw [← equal]
    exact beq_eq_false_iff_ne.mpr (by omega)
  have notStrict : decide (distance + 1 < parentDistance) = false := by
    rw [← equal]
    exact decide_eq_false_iff_not.mpr (by omega)
  rw [ringAwareDuplicateWithParent, different, notStrict]
  rfl

/-- A canonical root is never marked as a duplicate. -/
theorem ringAwareDuplicateWithParent_self_succ (distance : Nat) :
    ringAwareDuplicateWithParent (distance + 1) distance = false :=
  ringAwareDuplicateWithParent_false_of_succ_eq (distance + 1) distance rfl

mutual
  /-- Ring-aware preorder role mask of one shape, relative to its parent's visible distance. -/
  def ringAwareDuplicateRoleMaskWithParent (parentDistance : Nat) :
      LocalizedCumulativeBranchShape → List Bool
    | ⟨_atomicNumber, rule1bDistance, _isotopeMass, children⟩ =>
        ringAwareDuplicateWithParent parentDistance rule1bDistance ::
          ringAwareDuplicateRoleMaskListWithParent rule1bDistance children
    termination_by shape => sizeOf shape
    decreasing_by
      simp_wf

  /-- Ring-aware preorder role mask of a sibling list. -/
  def ringAwareDuplicateRoleMaskListWithParent (parentDistance : Nat) :
      List LocalizedCumulativeBranchShape → List Bool
    | [] => []
    | shape :: shapes =>
        ringAwareDuplicateRoleMaskWithParent parentDistance shape ++
          ringAwareDuplicateRoleMaskListWithParent parentDistance shapes
    termination_by shapes => sizeOf shapes
    decreasing_by
      all_goals (simp_wf <;> omega)
end

/-- Canonical ring-aware mask of a shape viewed as a real root. -/
def ringAwareDuplicateRoleMask (shape : LocalizedCumulativeBranchShape) : List Bool :=
  ringAwareDuplicateRoleMaskWithParent (shape.rule1bDistance + 1) shape

/-- Unfolding equation at one shape node. -/
theorem ringAwareDuplicateRoleMaskWithParent_mk (parentDistance : Nat)
    (atomicNumber rule1bDistance isotopeMass : Nat)
    (children : List LocalizedCumulativeBranchShape) :
    ringAwareDuplicateRoleMaskWithParent parentDistance
      { atomicNumber := atomicNumber
        rule1bDistance := rule1bDistance
        isotopeMass := isotopeMass
        children := children } =
      ringAwareDuplicateWithParent parentDistance rule1bDistance ::
        ringAwareDuplicateRoleMaskListWithParent rule1bDistance children := by
  rw [ringAwareDuplicateRoleMaskWithParent]

/-- Unfolding equation at the empty sibling list. -/
theorem ringAwareDuplicateRoleMaskListWithParent_nil (parentDistance : Nat) :
    ringAwareDuplicateRoleMaskListWithParent parentDistance
      ([] : List LocalizedCumulativeBranchShape) = [] := by
  rw [ringAwareDuplicateRoleMaskListWithParent]

/-- Unfolding equation at a nonempty sibling list. -/
theorem ringAwareDuplicateRoleMaskListWithParent_cons (parentDistance : Nat)
    (shape : LocalizedCumulativeBranchShape)
    (shapes : List LocalizedCumulativeBranchShape) :
    ringAwareDuplicateRoleMaskListWithParent parentDistance (shape :: shapes) =
      ringAwareDuplicateRoleMaskWithParent parentDistance shape ++
        ringAwareDuplicateRoleMaskListWithParent parentDistance shapes := by
  rw [ringAwareDuplicateRoleMaskListWithParent]

end LocalizedCumulativeBranchShape

open LocalizedCumulativeDecoratedTree
open LocalizedCumulativeBranchShape

namespace CertifiedLocalizedCIPInput

/-- **Child classification at a realized real root, ring-aware.**  Every child of a realized tree
with a real source root has generated provenance, and its actual `isDuplicateLeaf` bit is exactly
the ring-aware visible comparison of its Rule-1b distance with the parent's. -/
theorem realized_child_isDuplicateLeaf_classification_ringAware
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (present : child ∈ tree.children) :
    OfficialGeneratedProvenance child.source.occurrence.1.node.provenance ∧
      (child.source.occurrence.1.node.isDuplicateLeaf =
        ringAwareDuplicateWithParent
          tree.source.occurrence.1.node.rule1bRootDistance
          child.source.occurrence.1.node.rule1bRootDistance) := by
  have childIntended :=
    (realized_child_realizes_and_intended realizes present).2
  cases realizes with
  | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
      simp only [localizedRootTree] at childIntended rootReal ⊢
      rcases input.child_role_recovery_of_real_cursor_ringAware cursor rootReal
        child.source.occurrence.1 childIntended with
        ⟨real, relation, notDuplicate⟩ |
          ⟨d, provenanceEq, distanceEq, duplicateChild⟩ |
          ⟨d, provenanceEq, ringBound, duplicateChild⟩
      · refine ⟨?_, ?_⟩
        · rw [real]
          exact OfficialGeneratedProvenance.realAtom
        · rw [notDuplicate]
          rcases relation with outward | reverse
          · exact (ringAwareDuplicateWithParent_false_of_eq_succ _ _ outward).symm
          · exact (ringAwareDuplicateWithParent_false_of_succ_eq _ _ reverse).symm
      · refine ⟨?_, ?_⟩
        · rw [provenanceEq]
          exact OfficialGeneratedProvenance.multipleBondDuplicate d
        · rw [duplicateChild]
          exact (ringAwareDuplicateWithParent_true_of_eq _ _ distanceEq).symm
      · refine ⟨?_, ?_⟩
        · rw [provenanceEq]
          exact OfficialGeneratedProvenance.ringDuplicate d
        · rw [duplicateChild]
          exact (ringAwareDuplicateWithParent_true_of_succ_lt _ _ ringBound).symm

/-- **Node-level ring-aware shape/role bridge.**  For a realized tree whose source cursor carries
generated provenance, and whose root `isDuplicateLeaf` bit agrees with the ring-aware visible
comparison against an external parent distance, the actual preorder `isDuplicateLeaf` mask equals
the ring-aware shape-computed mask.  Every child role is recovered by the local ring-aware
classification; duplicate nodes are terminal. -/
theorem actualDuplicateRoleMask_eq_ringAwareDuplicateRoleMaskWithParent
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (parentDistance : Nat)
    (generated : OfficialGeneratedProvenance tree.source.occurrence.1.node.provenance)
    (interface : tree.source.occurrence.1.node.isDuplicateLeaf =
      ringAwareDuplicateWithParent parentDistance
        tree.source.occurrence.1.node.rule1bRootDistance) :
    actualDuplicateRoleMask tree =
      ringAwareDuplicateRoleMaskWithParent parentDistance (shape tree) := by
  have main : ∀ bound : Nat,
      ∀ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
        height tree ≤ bound →
        LocalizedCumulativeTreeRealizes input read tree →
        ∀ parentDistance : Nat,
          OfficialGeneratedProvenance tree.source.occurrence.1.node.provenance →
          tree.source.occurrence.1.node.isDuplicateLeaf =
            ringAwareDuplicateWithParent parentDistance
              tree.source.occurrence.1.node.rule1bRootDistance →
          actualDuplicateRoleMask tree =
            ringAwareDuplicateRoleMaskWithParent parentDistance (shape tree) := by
    intro bound
    refine Nat.strong_induction_on bound ?_
    intro k ih tree treeBound realizes parentDistance generated interface
    cases realizes with
    | mk cursor children sortedChildren childrenComputed sourcePerm childrenRealize =>
        have declarativeChildren :=
          input.localizedRerootChildren?_sound cursor children childrenComputed
        simp only [localizedRootTree] at interface generated ⊢
        rw [actualDuplicateRoleMask, table_shape_mk, ringAwareDuplicateRoleMaskWithParent]
        rw [interface]
        refine congrArg
          (List.cons
            (ringAwareDuplicateWithParent parentDistance
              cursor.occurrence.1.node.rule1bRootDistance)) ?_
        by_cases duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true
        · -- Duplicate nodes are terminal: the intended and sorted child lists are empty.
          have intendedNil : input.intendedLocalizedRerootChildFrames cursor = [] := by
            unfold intendedLocalizedRerootChildFrames
            rw [if_pos duplicate]
          have childrenNil : children = [] := by
            have mapNil : children.map (fun child => child.occurrence.1) = [] := by
              rw [declarativeChildren.1, intendedNil]
            exact List.map_eq_nil_iff.mp mapNil
          have sortedNil : sortedChildren = [] := by
            have mapNil : sortedChildren.map (fun child => child.source) = [] := by
              have permNil :
                  (sortedChildren.map (fun child => child.source)).Perm children :=
                sourcePerm
              rw [childrenNil] at permNil
              exact permNil.eq_nil
            exact List.map_eq_nil_iff.mp mapNil
          rw [sortedNil, shapeList, actualDuplicateRoleMaskList,
            ringAwareDuplicateRoleMaskListWithParent]
        · have cursorNotDup : cursor.occurrence.1.node.isDuplicateLeaf = false :=
            Bool.eq_false_iff.mpr duplicate
          have cursorReal : cursor.occurrence.1.node.provenance =
              OfficialCIPNodeProvenance.realAtom :=
            OfficialGeneratedProvenance.real_of_isDuplicateLeaf_eq_false
              generated cursorNotDup
          have childIntended : ∀ child ∈ sortedChildren,
              child.source.occurrence.1 ∈
                input.intendedLocalizedRerootChildFrames cursor := by
            intro child childPresent
            have memMap :
                child.source ∈ sortedChildren.map (fun tree => tree.source) :=
              List.mem_map.mpr ⟨child, childPresent, rfl⟩
            have memChildren : child.source ∈ children :=
              sourcePerm.mem_iff.mp memMap
            have mapped : child.source.occurrence.1 ∈
                children.map (fun child => child.occurrence.1) :=
              List.mem_map.mpr ⟨child.source, memChildren, rfl⟩
            rwa [declarativeChildren.1] at mapped
          have childFacts : ∀ child ∈ sortedChildren,
              OfficialGeneratedProvenance child.source.occurrence.1.node.provenance ∧
              (child.source.occurrence.1.node.isDuplicateLeaf =
                ringAwareDuplicateWithParent
                  cursor.occurrence.1.node.rule1bRootDistance
                  child.source.occurrence.1.node.rule1bRootDistance) := by
            intro child childPresent
            rcases input.child_role_recovery_of_real_cursor_ringAware cursor cursorReal
              child.source.occurrence.1 (childIntended child childPresent) with
              ⟨real, relation, notDuplicate⟩ |
                ⟨d, provenanceEq, distanceEq, duplicateChild⟩ |
                ⟨d, provenanceEq, ringBound, duplicateChild⟩
            · refine ⟨?_, ?_⟩
              · rw [real]
                exact OfficialGeneratedProvenance.realAtom
              · rw [notDuplicate]
                rcases relation with outward | reverse
                · exact (ringAwareDuplicateWithParent_false_of_eq_succ _ _ outward).symm
                · exact (ringAwareDuplicateWithParent_false_of_succ_eq _ _ reverse).symm
            · refine ⟨?_, ?_⟩
              · rw [provenanceEq]
                exact OfficialGeneratedProvenance.multipleBondDuplicate d
              · rw [duplicateChild]
                exact (ringAwareDuplicateWithParent_true_of_eq _ _ distanceEq).symm
            · refine ⟨?_, ?_⟩
              · rw [provenanceEq]
                exact OfficialGeneratedProvenance.ringDuplicate d
              · rw [duplicateChild]
                exact (ringAwareDuplicateWithParent_true_of_succ_lt _ _ ringBound).symm
          have childHeight : ∀ child ∈ sortedChildren, height child < k := by
            intro child childPresent
            have smaller := height_lt_height_of_mem
              (localizedRootTree input cursor (read cursor) sortedChildren) childPresent
            omega
          have listEq :
              ∀ list : List (LocalizedCumulativeDecoratedTree input carrierFuel),
                (∀ child ∈ list, height child < k) →
                (∀ child ∈ list, LocalizedCumulativeTreeRealizes input read child) →
                (∀ child ∈ list, child.source.occurrence.1 ∈
                  input.intendedLocalizedRerootChildFrames cursor) →
                (∀ child ∈ list,
                  OfficialGeneratedProvenance child.source.occurrence.1.node.provenance ∧
                  (child.source.occurrence.1.node.isDuplicateLeaf =
                    ringAwareDuplicateWithParent
                      cursor.occurrence.1.node.rule1bRootDistance
                      child.source.occurrence.1.node.rule1bRootDistance)) →
                actualDuplicateRoleMaskList list =
                  ringAwareDuplicateRoleMaskListWithParent
                    cursor.occurrence.1.node.rule1bRootDistance (shapeList list) := by
            intro list
            induction list with
            | nil =>
                intro _ _ _ _
                rw [actualDuplicateRoleMaskList, shapeList,
                  ringAwareDuplicateRoleMaskListWithParent]
            | cons child rest ihList =>
                intro bounds realizesList intendedList facts
                rw [actualDuplicateRoleMaskList, shapeList,
                  ringAwareDuplicateRoleMaskListWithParent]
                rw [ihList (fun tree present => bounds tree (by simp [present]))
                  (fun tree present => realizesList tree (by simp [present]))
                  (fun tree present => intendedList tree (by simp [present]))
                  (fun tree present => facts tree (by simp [present]))]
                have childEq := ih (height child) (bounds child (by simp)) child le_rfl
                  (realizesList child (by simp))
                  cursor.occurrence.1.node.rule1bRootDistance
                  (facts child (by simp)).1 (facts child (by simp)).2
                rw [childEq]
          exact listEq sortedChildren childHeight childrenRealize childIntended childFacts
  exact main (height tree) tree le_rfl realizes parentDistance generated interface

/-- **Root-level ring-aware bridge.**  A realized tree with real root provenance has actual role
mask exactly the canonical ring-aware shape mask. -/
theorem actualDuplicateRoleMask_eq_ringAwareDuplicateRoleMask
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom) :
    actualDuplicateRoleMask tree = ringAwareDuplicateRoleMask (shape tree) := by
  have storedDistance : tree.rule1bDistance =
      tree.source.occurrence.1.node.rule1bRootDistance :=
    tree_rule1bDistance_eq_source realizes
  have rootNotDup : tree.source.occurrence.1.node.isDuplicateLeaf = false :=
    input.isDuplicateLeaf_eq_false_of_provenance_real _ rootReal
  have interface : tree.source.occurrence.1.node.isDuplicateLeaf =
      ringAwareDuplicateWithParent
        (tree.source.occurrence.1.node.rule1bRootDistance + 1)
        tree.source.occurrence.1.node.rule1bRootDistance := by
    rw [rootNotDup]
    exact (ringAwareDuplicateWithParent_self_succ _).symm
  have generated : OfficialGeneratedProvenance
      tree.source.occurrence.1.node.provenance := by
    rw [rootReal]
    exact OfficialGeneratedProvenance.realAtom
  rw [actualDuplicateRoleMask_eq_ringAwareDuplicateRoleMaskWithParent tree realizes
    (tree.source.occurrence.1.node.rule1bRootDistance + 1)
    generated interface,
    ringAwareDuplicateRoleMask, table_shape_rule1bDistance tree, storedDistance]

/-- **Equal erased shape preserves ring-aware real-versus-duplicate positions.**  Two realized
trees at real roots with the same comparison-visible shape have the same actual preorder
duplicate-role mask. -/
theorem actualDuplicateRoleMask_eq_of_shape_eq_ringAware
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (leftRealizes : LocalizedCumulativeTreeRealizes input read left)
    (rightRealizes : LocalizedCumulativeTreeRealizes input read right)
    (leftRootReal : left.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightRootReal : right.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (sameShape : shape left = shape right) :
    actualDuplicateRoleMask left = actualDuplicateRoleMask right := by
  rw [actualDuplicateRoleMask_eq_ringAwareDuplicateRoleMask left leftRealizes leftRootReal,
    actualDuplicateRoleMask_eq_ringAwareDuplicateRoleMask right rightRealizes rightRootReal,
    sameShape]

/-- **Equal erased shape preserves ring-aware positions for independently read trees.** -/
theorem actualDuplicateRoleMask_eq_of_shape_eq_independent_readers_ringAware
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {readRight : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (leftRealizes : LocalizedCumulativeTreeRealizes input read left)
    (rightRealizes : LocalizedCumulativeTreeRealizes input readRight right)
    (leftRootReal : left.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightRootReal : right.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (sameShape : shape left = shape right) :
    actualDuplicateRoleMask left = actualDuplicateRoleMask right := by
  rw [actualDuplicateRoleMask_eq_ringAwareDuplicateRoleMask left leftRealizes leftRootReal,
    actualDuplicateRoleMask_eq_ringAwareDuplicateRoleMask right rightRealizes rightRootReal,
    sameShape]

/-- Positional form: at every preorder slot the two ring-aware masks agree. -/
theorem actualDuplicateRoleMask_getElem?_eq_of_shape_eq_ringAware
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (leftRealizes : LocalizedCumulativeTreeRealizes input read left)
    (rightRealizes : LocalizedCumulativeTreeRealizes input read right)
    (leftRootReal : left.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightRootReal : right.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (sameShape : shape left = shape right) (slot : Nat) :
    (actualDuplicateRoleMask left)[slot]? =
      (actualDuplicateRoleMask right)[slot]? := by
  rw [actualDuplicateRoleMask_eq_of_shape_eq_ringAware left right leftRealizes
    rightRealizes leftRootReal rightRootReal sameShape]

/-- **Equal addressed tables preserve ring-aware real-versus-duplicate positions.** -/
theorem actualDuplicateRoleMask_eq_of_tables_eq_ringAware
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (stage : LocalizedCumulativeRule45Stage)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (leftRealizes : LocalizedCumulativeTreeRealizes input read left)
    (rightRealizes : LocalizedCumulativeTreeRealizes input read right)
    (leftRootReal : left.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightRootReal : right.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (sameTables : tables stage left = tables stage right) :
    actualDuplicateRoleMask left = actualDuplicateRoleMask right :=
  actualDuplicateRoleMask_eq_of_shape_eq_ringAware left right leftRealizes
    rightRealizes leftRootReal rightRootReal
    (table_shape_eq_of_tables_eq stage left right sameTables)

/-- **Column-wise tables preserve ring-aware real-versus-duplicate positions.** -/
theorem actualDuplicateRoleMask_eq_of_columns_eq_ringAware
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (stageLeft stageRight : LocalizedCumulativeRule45Stage)
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (leftRealizes : LocalizedCumulativeTreeRealizes input read left)
    (rightRealizes : LocalizedCumulativeTreeRealizes input read right)
    (leftRootReal : left.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightRootReal : right.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (sameRule1a : (tables stageLeft left).rule1a = (tables stageRight right).rule1a)
    (sameRule1b : (tables stageLeft left).rule1b = (tables stageRight right).rule1b)
    (sameRule2 : (tables stageLeft left).rule2 = (tables stageRight right).rule2) :
    actualDuplicateRoleMask left = actualDuplicateRoleMask right :=
  actualDuplicateRoleMask_eq_of_shape_eq_ringAware left right leftRealizes
    rightRealizes leftRootReal rightRootReal
    (table_shape_eq_of_columns_eq stageLeft stageRight left right
      sameRule1a sameRule1b sameRule2)

/-! ## Same-address ring-aware provenance recovery under equal shape

The preorder mask result compares the two trees as lists.  The endpoint compares the two trees at
the same shared address (`subtreeAt?`).  The recursion uses the ring-aware child classification;
duplicate nodes remain terminal, so a successful child lookup proves that the node itself is real.
The two sides keep independent auxiliary-label readers throughout. -/

/-- **Address induction for ring-aware same-address provenance recovery.** -/
theorem provenance_real_iff_at_address_of_shape_eq_aux_ringAware
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {readRight : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (leftRealizes : LocalizedCumulativeTreeRealizes input read left)
    (rightRealizes : LocalizedCumulativeTreeRealizes input readRight right)
    (sameShape : shape left = shape right)
    (parentDistance : Nat)
    (leftFlag : left.source.occurrence.1.node.isDuplicateLeaf =
      ringAwareDuplicateWithParent parentDistance
        left.source.occurrence.1.node.rule1bRootDistance)
    (rightFlag : right.source.occurrence.1.node.isDuplicateLeaf =
      ringAwareDuplicateWithParent parentDistance
        right.source.occurrence.1.node.rule1bRootDistance)
    (address : List Nat) :
    ∀ {leftNode rightNode : LocalizedCumulativeDecoratedTree input carrierFuel},
      subtreeAt? left address = some leftNode →
      subtreeAt? right address = some rightNode →
        (leftNode.source.occurrence.1.node.provenance =
            OfficialCIPNodeProvenance.realAtom ↔
          rightNode.source.occurrence.1.node.provenance =
            OfficialCIPNodeProvenance.realAtom) := by
  induction address generalizing left right leftRealizes rightRealizes sameShape
    parentDistance leftFlag rightFlag with
  | nil =>
      intro leftNode rightNode leftAt rightAt
      simp only [subtreeAt?_nil, Option.some.injEq] at leftAt rightAt
      subst leftNode
      subst rightNode
      have visibleDistance :=
        visible_rule1bRootDistance_eq_of_shape_eq leftRealizes rightRealizes sameShape
      have flagEq : left.source.occurrence.1.node.isDuplicateLeaf =
          right.source.occurrence.1.node.isDuplicateLeaf := by
        rw [leftFlag, rightFlag, visibleDistance]
      have leftGenerated :=
        input.carrierOccurrence_generatedProvenance left.source.occurrence
      have rightGenerated :=
        input.carrierOccurrence_generatedProvenance right.source.occurrence
      constructor
      · intro real
        have notDuplicate :=
          input.isDuplicateLeaf_eq_false_of_provenance_real _ real
        have rightNotDuplicate :
            right.source.occurrence.1.node.isDuplicateLeaf = false := by
          rw [← flagEq]
          exact notDuplicate
        exact OfficialGeneratedProvenance.real_of_isDuplicateLeaf_eq_false
          rightGenerated rightNotDuplicate
      · intro real
        have notDuplicate :=
          input.isDuplicateLeaf_eq_false_of_provenance_real _ real
        have leftNotDuplicate :
            left.source.occurrence.1.node.isDuplicateLeaf = false := by
          rw [flagEq]
          exact notDuplicate
        exact OfficialGeneratedProvenance.real_of_isDuplicateLeaf_eq_false
          leftGenerated leftNotDuplicate
  | cons slot rest inductionHypothesis =>
      intro leftNode rightNode leftAt rightAt
      obtain ⟨leftChild, leftChildAt, leftRestAt⟩ :=
        subtreeAt?_cons_eq_some_iff.mp leftAt
      obtain ⟨rightChild, rightChildAt, rightRestAt⟩ :=
        subtreeAt?_cons_eq_some_iff.mp rightAt
      have slotShapeEq : (shape left).children[slot]? = (shape right).children[slot]? :=
        congrArg (fun erased => erased.children[slot]?) sameShape
      have childShapeEq : shape leftChild = shape rightChild := by
        have transported := slotShapeEq
        rw [table_shape_children_getElem? left slot,
          table_shape_children_getElem? right slot, leftChildAt, rightChildAt] at transported
        exact Option.some.inj (by simpa using transported)
      have parentVisibleDistance :=
        visible_rule1bRootDistance_eq_of_shape_eq leftRealizes rightRealizes sameShape
      have leftRootReal : left.source.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.realAtom := by
        by_cases duplicate : left.source.occurrence.1.node.isDuplicateLeaf = true
        · have childrenNil :=
            children_eq_nil_of_isDuplicateLeaf_true leftRealizes duplicate
          rw [childrenNil] at leftChildAt
          exact absurd leftChildAt (by simp)
        · have notDuplicate : left.source.occurrence.1.node.isDuplicateLeaf = false :=
            Bool.eq_false_iff.mpr duplicate
          exact OfficialGeneratedProvenance.real_of_isDuplicateLeaf_eq_false
            (input.carrierOccurrence_generatedProvenance left.source.occurrence)
            notDuplicate
      have rightRootReal : right.source.occurrence.1.node.provenance =
          OfficialCIPNodeProvenance.realAtom := by
        by_cases duplicate : right.source.occurrence.1.node.isDuplicateLeaf = true
        · have childrenNil :=
            children_eq_nil_of_isDuplicateLeaf_true rightRealizes duplicate
          rw [childrenNil] at rightChildAt
          exact absurd rightChildAt (by simp)
        · have notDuplicate : right.source.occurrence.1.node.isDuplicateLeaf = false :=
            Bool.eq_false_iff.mpr duplicate
          exact OfficialGeneratedProvenance.real_of_isDuplicateLeaf_eq_false
            (input.carrierOccurrence_generatedProvenance right.source.occurrence)
            notDuplicate
      have leftChildFacts :=
        realized_child_isDuplicateLeaf_classification_ringAware leftRealizes leftRootReal
          (List.mem_of_getElem? leftChildAt)
      have rightChildFacts :=
        realized_child_isDuplicateLeaf_classification_ringAware rightRealizes rightRootReal
          (List.mem_of_getElem? rightChildAt)
      have rightChildFlag : rightChild.source.occurrence.1.node.isDuplicateLeaf =
          ringAwareDuplicateWithParent
            left.source.occurrence.1.node.rule1bRootDistance
            rightChild.source.occurrence.1.node.rule1bRootDistance := by
        rw [rightChildFacts.2, ← parentVisibleDistance]
      exact inductionHypothesis leftChild rightChild
        (realized_child_realizes_and_intended leftRealizes
          (List.mem_of_getElem? leftChildAt)).1
        (realized_child_realizes_and_intended rightRealizes
          (List.mem_of_getElem? rightChildAt)).1
        childShapeEq
        left.source.occurrence.1.node.rule1bRootDistance
        leftChildFacts.2 rightChildFlag
        leftRestAt rightRestAt

/-- **Same-address ring-aware real-versus-duplicate role preservation.**  Two actually realized
trees with equal comparison-visible shape and real source roots have real provenance at the same
successful address on one side exactly when they have it on the other.  The two trees may be read
by independent auxiliary-label readers; no Acyclic hypothesis is used. -/
theorem provenance_real_iff_at_same_address_of_shape_eq_noAcyclic
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {readRight : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (left right : LocalizedCumulativeDecoratedTree input carrierFuel)
    (leftRealizes : LocalizedCumulativeTreeRealizes input read left)
    (rightRealizes : LocalizedCumulativeTreeRealizes input readRight right)
    (leftRootReal : left.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (rightRootReal : right.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (sameShape : shape left = shape right)
    {address : List Nat}
    {leftNode rightNode : LocalizedCumulativeDecoratedTree input carrierFuel}
    (leftAt : subtreeAt? left address = some leftNode)
    (rightAt : subtreeAt? right address = some rightNode) :
    (leftNode.source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom ↔
      rightNode.source.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom) := by
  have visibleDistance :=
    visible_rule1bRootDistance_eq_of_shape_eq leftRealizes rightRealizes sameShape
  have leftFlag : left.source.occurrence.1.node.isDuplicateLeaf =
      ringAwareDuplicateWithParent
        (left.source.occurrence.1.node.rule1bRootDistance + 1)
        left.source.occurrence.1.node.rule1bRootDistance := by
    rw [input.isDuplicateLeaf_eq_false_of_provenance_real _ leftRootReal]
    exact (ringAwareDuplicateWithParent_self_succ _).symm
  have rightFlag : right.source.occurrence.1.node.isDuplicateLeaf =
      ringAwareDuplicateWithParent
        (left.source.occurrence.1.node.rule1bRootDistance + 1)
        right.source.occurrence.1.node.rule1bRootDistance := by
    rw [input.isDuplicateLeaf_eq_false_of_provenance_real _ rightRootReal,
      visibleDistance]
    exact (ringAwareDuplicateWithParent_self_succ _).symm
  exact provenance_real_iff_at_address_of_shape_eq_aux_ringAware left right leftRealizes
    rightRealizes sameShape (left.source.occurrence.1.node.rule1bRootDistance + 1)
    leftFlag rightFlag address leftAt rightAt

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableRingChild_distance_add_one_lt_parent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.executableRingChild_rule1bRootDistance_add_one_lt_parent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.child_role_recovery_of_real_cursor_ringAware
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape.ringAwareDuplicateWithParent
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape.ringAwareDuplicateWithParent_true_of_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape.ringAwareDuplicateWithParent_true_of_succ_lt
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape.ringAwareDuplicateWithParent_false_of_eq_succ
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape.ringAwareDuplicateWithParent_false_of_succ_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape.ringAwareDuplicateWithParent_self_succ
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape.ringAwareDuplicateRoleMaskWithParent
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape.ringAwareDuplicateRoleMaskListWithParent
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape.ringAwareDuplicateRoleMask
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape.ringAwareDuplicateRoleMaskWithParent_mk
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape.ringAwareDuplicateRoleMaskListWithParent_nil
assert_kernel_only TetraStereo.OneCenter.LocalizedCumulativeBranchShape.ringAwareDuplicateRoleMaskListWithParent_cons
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realized_child_isDuplicateLeaf_classification_ringAware
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualDuplicateRoleMask_eq_ringAwareDuplicateRoleMaskWithParent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualDuplicateRoleMask_eq_ringAwareDuplicateRoleMask
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualDuplicateRoleMask_eq_of_shape_eq_ringAware
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualDuplicateRoleMask_eq_of_shape_eq_independent_readers_ringAware
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualDuplicateRoleMask_getElem?_eq_of_shape_eq_ringAware
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualDuplicateRoleMask_eq_of_tables_eq_ringAware
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualDuplicateRoleMask_eq_of_columns_eq_ringAware
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.provenance_real_iff_at_address_of_shape_eq_aux_ringAware
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.provenance_real_iff_at_same_address_of_shape_eq_noAcyclic
