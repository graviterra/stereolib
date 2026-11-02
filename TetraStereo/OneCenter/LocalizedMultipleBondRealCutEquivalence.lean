import TetraStereo.OneCenter.LocalizedMultipleBondRealSpine
import TetraStereo.OneCenter.LocalizedAcyclicGeneralCutCorrespondence
import TetraStereo.OneCenter.LocalizedRealizedTreeCutEquivalence
import TetraStereo.KernelOnly

set_option autoImplicit false










































namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-! ## The real-provenance physical cut state -/

/-- **Real physical-cut state.**  A cursor reached from an actual incoming physical edge
`pAtom - oAtom` carries a recorded previous occurrence and current atom, a simple physical walk
from `oAtom` to its current atom avoiding `pAtom`, whose penultimate after prepending the incoming
edge is the current atom of the recorded previous occurrence, together with the two real-provenance
witnesses required by the local real-spine correspondence: the cursor's own node and its recorded
incoming occurrence.

No address comparison occurs: the state applies equally to inward and outward actual steps. -/
def RealActualCutWalkState (input : CertifiedLocalizedCIPInput) {oAtom pAtom : input.Atom}
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∃ (previous : input.LocalizedCIPOccurrence carrierFuel)
    (current incoming : input.Atom)
    (walk : (input.molecularSimpleGraph).Walk oAtom current),
    cursor.previous? = some previous ∧
      cursor.occurrence.1.node.current? = some current ∧
      previous.1.node.current? = some incoming ∧
      input.LocalizedRerootCursorValid cursor ∧
      cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom ∧
      walk.IsPath ∧
      pAtom ∉ walk.support ∧
      (SimpleGraph.Walk.cons incomingEdge walk).penultimate = incoming

/-- **Base real physical-cut state.**  The incoming physical edge itself is the initial simple
walk; the start occurrence and the recorded incoming occurrence are the two real witnesses. -/
theorem realActualCutWalkState_start
    {oAtom pAtom : input.Atom}
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    {carrierFuel : Nat}
    {start : input.LocalizedRerootCursor carrierFuel}
    {previous : input.LocalizedCIPOccurrence carrierFuel}
    (previousEq : start.previous? = some previous)
    (validStart : input.LocalizedRerootCursorValid start)
    (startReal : start.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (oObserved : start.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom) :
    input.RealActualCutWalkState incomingEdge start := by
  have oNeP : pAtom ≠ oAtom := by
    intro same
    exact input.molecularSimpleGraph.irrefl (same.symm ▸ incomingEdge)
  refine ⟨previous, oAtom, pAtom, SimpleGraph.Walk.nil, previousEq, oObserved,
    pObserved, validStart, startReal, previousReal, SimpleGraph.Walk.IsPath.nil, ?_, ?_⟩
  · simpa [SimpleGraph.Walk.support_nil] using oNeP
  · simp [SimpleGraph.Walk.penultimate_cons_nil]

/-- **One real executable step preserves the real physical-cut state.**  The local real-spine
correspondence supplies physical adjacency for the new current atom and excludes the recorded
incoming atom.  Acyclicity then makes the new atom fresh along the stored simple walk (it is not
the deleted atom and not already visited), so the walk extends and the penultimate equation
transports.  Neither the source's address nor the target's provenance direction is compared. -/
theorem realActualCutWalkState_step
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {oAtom pAtom : input.Atom}
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    {b c : input.LocalizedRerootCursor carrierFuel}
    (stateB : input.RealActualCutWalkState incomingEdge b)
    (step : E input b c)
    (cReal : c.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {w : input.Atom}
    (wObserved : c.occurrence.1.node.current? = some w) :
    input.RealActualCutWalkState incomingEdge c := by
  unfold RealActualCutWalkState at stateB
  obtain ⟨previousB, x, z, walkB, previousEqB, xObserved, zObserved, validB, bReal,
    previousBReal, simpleB, avoidsB, penultimateB⟩ := stateB
  have validNeighbor : b.occurrence.1 ∈ input.localizedRerootNeighborFrames
      (fuel := carrierFuel) previousB.1 := by
    unfold LocalizedRerootCursorValid at validB
    rw [previousEqB] at validB
    change b.occurrence.1 ∈ input.localizedRerootNeighborFrames
      (fuel := carrierFuel) previousB.1 at validB
    exact validB
  have sameRootB : b.occurrence.1.root = previousB.1.root :=
    ((input.mem_localizedRerootNeighborFrames_iff previousB.1
      b.occurrence.1).mp validNeighbor).2.1
  have localIff :=
    input.localizedRerootChildren?_realChild_exists_iff_adjacent (acyclic := acyclic)
      (enough := enough) (cursor := b) (previous := previousB) previousEqB sameRootB.symm
      (input.carrierOccurrence_realPath_of_provenance_real b.occurrence bReal)
      (input.carrierOccurrence_realPath_of_provenance_real previousB previousBReal)
      xObserved zObserved (input.executableLocalizedRerootChildren b)
      (input.localizedRerootChildren?_eq_some_executable b)
  obtain ⟨adjacent, wNeIncoming⟩ := (localIff w).mp ⟨c, step, cReal, wObserved⟩
  have fullPath : (SimpleGraph.Walk.cons incomingEdge walkB).IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff incomingEdge walkB).2 ⟨simpleB, avoidsB⟩
  have fresh := MoleculeGraph.Acyclic.not_mem_support_of_adj_ne_penultimate
    input.moleculeGraph acyclic fullPath penultimateB adjacent wNeIncoming
  have fresh' : ¬ (w = pAtom ∨ w ∈ walkB.support) := by
    simpa only [SimpleGraph.Walk.support_cons, List.mem_cons] using fresh
  have wNeP : w ≠ pAtom := fun same => fresh' (Or.inl same)
  have wNotWalk : w ∉ walkB.support := fun present => fresh' (Or.inr present)
  have adjacentG : (input.molecularSimpleGraph).Adj x w := adjacent
  let newWalk : (input.molecularSimpleGraph).Walk oAtom w := walkB.concat adjacentG
  have newSimple : newWalk.IsPath := simpleB.concat wNotWalk adjacentG
  have newAvoid : pAtom ∉ newWalk.support := by
    intro present
    have present' : pAtom ∈ walkB.support ∨ pAtom = w := by
      simpa [newWalk, List.mem_append] using present
    rcases present' with old | last
    · exact avoidsB old
    · exact wNeP last.symm
  have newNotNil : ¬ newWalk.Nil := by
    rw [SimpleGraph.Walk.nil_iff_length_eq]
    simp [newWalk]
  have newPenultimate : (SimpleGraph.Walk.cons incomingEdge newWalk).penultimate = x := by
    rw [SimpleGraph.Walk.penultimate_cons_of_not_nil incomingEdge newWalk newNotNil]
    simp [newWalk]
  have childDerived : input.DeclarativeLocalizedRerootChildren b
      (input.executableLocalizedRerootChildren b) :=
    input.executableLocalizedRerootChildren_declarative b
  have childPrevious : c.previous? = some b.occurrence := childDerived.2 c step
  have childValid : input.LocalizedRerootCursorValid c :=
    input.localizedRerootChild_valid b c
      (input.executableLocalizedRerootChildren b) childDerived step
  exact ⟨b.occurrence, w, x, newWalk, childPrevious, wObserved, xObserved, childValid,
    cReal, bReal, newSimple, newAvoid, newPenultimate⟩

/-! ## The invariant along real reachability -/

/-- **Real path invariant.**  Along every actual executable path whose every target has real
provenance, starting from a real start cursor with a genuine incoming physical edge, the reached
cursor satisfies the real physical-cut state.  No address-length comparison is used. -/
theorem realReachable_realActualCutWalkState
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : start.previous? = some previous)
    (validStart : input.LocalizedRerootCursorValid start)
    (startReal : start.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : start.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (target : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen
      (fun left right : input.LocalizedRerootCursor carrierFuel =>
        CertifiedLocalizedCIPInput.E input left right ∧
          right.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
      start target) :
    input.RealActualCutWalkState incomingEdge target := by
  induction reachable with
  | refl =>
      exact input.realActualCutWalkState_start incomingEdge previousEq validStart
        startReal previousReal oObserved pObserved
  | @tail b c _path step ih =>
      obtain ⟨edge, cReal⟩ := step
      have targetDerived :
          input.DeclarativeLocalizedOccurrence carrierFuel c.occurrence.1 :=
        (input.mem_localizedOccurrences_iff carrierFuel c.occurrence.1).mp
          c.occurrence.2
      obtain ⟨w, wObserved⟩ := Option.isSome_iff_exists.mp
        (input.declarativeLocalizedOccurrence_node_current_isSome targetDerived)
      exact input.realActualCutWalkState_step acyclic enough incomingEdge ih edge cReal
        wObserved

/-- **Forward direction.**  Every current atom of a real-reachable cursor lies in the physical cut
branch of `oAtom` after deleting `pAtom`.  The witness is the real invariant's simple walk. -/
theorem realReachable_current_mem_cutBranch
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : start.previous? = some previous)
    (validStart : input.LocalizedRerootCursorValid start)
    (startReal : start.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : start.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (target : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen
      (fun left right : input.LocalizedRerootCursor carrierFuel =>
        CertifiedLocalizedCIPInput.E input left right ∧
          right.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
      start target)
    {w : input.Atom}
    (observed : target.occurrence.1.node.current? = some w) :
    w ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom := by
  have state :=
    input.realReachable_realActualCutWalkState acyclic enough start previous
      previousEq validStart startReal previousReal oObserved pObserved incomingEdge
      target reachable
  unfold RealActualCutWalkState at state
  obtain ⟨_previousT, current, _incomingT, walkT, _previousEqT, currentObserved,
    _incomingObservedT, _validT, _targetReal, _previousRealT, _simpleT, avoidsT,
    _penultimateT⟩ := state
  have sameCurrent : w = current :=
    Option.some.inj (observed.symm.trans currentObserved)
  rw [sameCurrent]
  exact ⟨walkT, avoidsT⟩

/-! ## The general real-slice correspondence -/













theorem realChildReachable_current_iff_cutBranch_general
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : start.previous? = some previous)
    (sameRootStart : start.occurrence.1.root = previous.1.root)
    (validStart : input.LocalizedRerootCursorValid start)
    (startReal : start.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : start.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (w : input.Atom) :
    (∃ target : input.LocalizedRerootCursor carrierFuel,
      input.RealChildReachable start target ∧
        target.occurrence.1.node.current? = some w) ↔
      w ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom := by
  constructor
  · rintro ⟨target, reachable, observed⟩
    exact input.realReachable_current_mem_cutBranch acyclic enough start previous
      previousEq validStart startReal previousReal oObserved pObserved incomingEdge
      target reachable observed
  · intro branchMem
    obtain ⟨walk, avoids⟩ := branchMem
    let path : input.moleculeGraph.underlyingSimpleGraph.Path oAtom w := walk.toPath
    let simpleWalk : input.moleculeGraph.underlyingSimpleGraph.Walk oAtom w := path.1
    have simple : simpleWalk.IsPath := path.2
    have simpleAvoid : pAtom ∉ simpleWalk.support :=
      fun present => avoids (SimpleGraph.Walk.support_toPath_subset walk present)
    let rest := simpleWalk.support.tail
    have supportCons : simpleWalk.support = oAtom :: rest := by
      simpa [rest] using SimpleGraph.Walk.support_eq_cons simpleWalk
    have nodup : (oAtom :: rest).Nodup := by
      simpa [supportCons] using simple.support_nodup
    have chain : (oAtom :: rest).IsChain
        (fun a b => input.moleculeGraph.Adj a b) := by
      simpa [supportCons] using SimpleGraph.Walk.isChain_adj_support simpleWalk
    have avoidCons : pAtom ∉ oAtom :: rest := by
      simpa [supportCons] using simpleAvoid
    have lastEq : (oAtom :: rest).getLast? = some w := by
      rw [← supportCons]
      rw [List.getLast?_eq_getLast_of_ne_nil
        (SimpleGraph.Walk.support_ne_nil simpleWalk)]
      exact congrArg some (SimpleGraph.Walk.getLast_support simpleWalk)
    obtain ⟨target, reachable, targetObserved⟩ :=
      input.realChildReachable_of_simple_chain acyclic enough rest
        start previous oAtom pAtom previousEq sameRootStart startReal previousReal
        oObserved pObserved nodup chain avoidCons
    exact ⟨target, reachable, by rw [targetObserved, lastEq]⟩

end CertifiedLocalizedCIPInput








open CertifiedLocalizedCIPInput

section RealPositionAdapter

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
variable {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}

/-- The current atom of an actual carrier occurrence.  Existence is not assumed: every carrier
occurrence is a declarative occurrence, whose node has a current atom. -/
def occurrenceCurrent (occurrence : input.LocalizedCIPOccurrence carrierFuel) : input.Atom :=
  (occurrence.1.node.current?).get (by
    have derived : input.DeclarativeLocalizedOccurrence carrierFuel occurrence.1 :=
      (input.mem_localizedOccurrences_iff carrierFuel occurrence.1).mp occurrence.2
    have someCurrent : (occurrence.1.node.current?).isSome = true :=
      input.declarativeLocalizedOccurrence_node_current_isSome derived
    exact Option.isSome_iff_exists.mpr (Option.isSome_iff_exists.mp someCurrent))

/-- The defining equation of `occurrenceCurrent`. -/
theorem occurrenceCurrent_spec (occurrence : input.LocalizedCIPOccurrence carrierFuel) :
    occurrence.1.node.current? = some (occurrenceCurrent occurrence) :=
  Option.eq_some_of_isSome _

/-- An occurrence observing a given atom carries that atom. -/
theorem occurrenceCurrent_eq_of_observed {occurrence : input.LocalizedCIPOccurrence carrierFuel}
    {atom : input.Atom} (observed : occurrence.1.node.current? = some atom) :
    occurrenceCurrent occurrence = atom :=
  Option.some.inj ((occurrenceCurrent_spec occurrence).symm.trans observed)

/-- The current atom of the source cursor of an actual decorated node. -/
def nodeCurrent (node : LocalizedCumulativeDecoratedTree input carrierFuel) : input.Atom :=
  occurrenceCurrent node.source.occurrence

/-- The defining equation of `nodeCurrent`. -/
theorem nodeCurrent_spec (node : LocalizedCumulativeDecoratedTree input carrierFuel) :
    node.source.occurrence.1.node.current? = some (nodeCurrent node) :=
  occurrenceCurrent_spec node.source.occurrence

/-- The current atom of the source cursor of an actual position. -/
def positionCurrent {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) : input.Atom :=
  nodeCurrent (positionNode p)

/-- The defining equation of `positionCurrent`. -/
theorem positionCurrent_spec {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) :
    (positionSource p).occurrence.1.node.current? = some (positionCurrent p) :=
  nodeCurrent_spec (positionNode p)

/-- A position is **real** when its source occurrence has `realAtom` provenance.  Multiple-bond
and ring duplicate leaves fall outside this predicate, as do placeholder frames. -/
def PositionReal {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : Position tree) : Prop :=
  (positionNode p).source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom

/-- The finite subtype of real positions of an actual decorated tree. -/
abbrev RealPosition (tree : LocalizedCumulativeDecoratedTree input carrierFuel) : Type :=
  {p : Position tree // PositionReal p}

/-- The physical atom of a real position. -/
def realPositionAtom {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : RealPosition tree) : input.Atom :=
  positionCurrent p.1

/-- The defining equation of `realPositionAtom`. -/
theorem realPositionAtom_spec {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : RealPosition tree) :
    (positionSource p.1).occurrence.1.node.current? = some (realPositionAtom p) :=
  positionCurrent_spec p.1

/-- The actual source cursor of a real position. -/
def realPositionSource {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (p : RealPosition tree) : input.LocalizedRerootCursor carrierFuel :=
  positionSource p.1

/-! ## Carrier provenance of executable children

A cursor whose executable child list is nonempty cannot be a duplicate leaf, and carrier
occurrences never carry placeholder provenance.  Hence such a cursor is real. -/

/-- A derived occurrence subtree never carries placeholder provenance, provided its top node does
not.  Generated children are `node.extend next copyIndex`, whose provenance is a
`childProvenance`, and `childProvenance` is only ever real, ring-duplicate or
multiple-bond-duplicate. -/
theorem DeclarativeLocalizedOccurrenceSubtree_provenance_ne_placeholder
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence)
    (nodeNonplaceholder : ∀ kind distance,
      node.provenance ≠ OfficialCIPNodeProvenance.placeholder kind distance) :
    ∀ kind distance,
      occurrence.node.provenance ≠ OfficialCIPNodeProvenance.placeholder kind distance := by
  induction derived with
  | subtreeRoot => exact nodeNonplaceholder
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot descendant ih =>
      intro kind distance
      apply ih
      obtain ⟨next, copyIndex, childIdentity⟩ :=
        input.mem_executableOfficialCIPChildren_extend node child
          (List.fst_mem_of_mem_zipIdx childAtSlot)
      intro otherKind otherDistance equality
      rw [childIdentity, OfficialCIPNode.extend_provenance] at equality
      simp only [OfficialCIPNode.childProvenance] at equality
      split at equality <;> (try split at equality) <;> simp at equality

/-- Molecule-wide carrier provenance is never a placeholder, because every carrier occurrence is
rooted at the real `OfficialCIPNode.root` of its stored root atom. -/
theorem declarativeLocalizedOccurrence_provenance_ne_placeholder
    {fuel : Nat} {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrence fuel occurrence) :
    ∀ kind distance,
      occurrence.node.provenance ≠ OfficialCIPNodeProvenance.placeholder kind distance := by
  have rooted := input.declarativeLocalizedOccurrence_as_rootSubtree derived
  exact DeclarativeLocalizedOccurrenceSubtree_provenance_ne_placeholder rooted
    (by simp [OfficialCIPNode.root])

/-- **A cursor with an executable child is real.**  The intended cut-neighborhood of a duplicate
leaf is empty, so a child forces non-duplicate provenance; placeholders are unreachable from the
carrier, hence the provenance is `realAtom`. -/
theorem provenance_real_of_executableChild
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (child : input.LocalizedRerootCursor carrierFuel)
    (childPresent : child ∈ input.executableLocalizedRerootChildren cursor) :
    cursor.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  have notDuplicate : cursor.occurrence.1.node.isDuplicateLeaf = false := by
    by_cases duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true
    · have empty : input.executableLocalizedRerootChildren cursor = [] := by
        simp [executableLocalizedRerootChildren,
          intendedLocalizedRerootChildFrames, duplicate]
      rw [empty] at childPresent
      simp at childPresent
    · exact Bool.eq_false_of_not_eq_true duplicate
  have notPlaceholder := declarativeLocalizedOccurrence_provenance_ne_placeholder
    ((input.mem_localizedOccurrences_iff carrierFuel cursor.occurrence.1).mp cursor.occurrence.2)
  cases provenance : cursor.occurrence.1.node.provenance with
  | realAtom => rfl
  | multipleBondDuplicate distance =>
      simp [OfficialCIPNode.isDuplicateLeaf, provenance] at notDuplicate
  | ringDuplicate distance =>
      simp [OfficialCIPNode.isDuplicateLeaf, provenance] at notDuplicate
  | placeholder kind distance =>
      exact absurd provenance (notPlaceholder kind distance)

/-! ## Real positions are realized by actual real-child paths -/

/-- **The source of a realized subtree is real as soon as a position inside it is real.**  A
nonempty path exposes an actual executable child of the source, and a cursor with an executable
child is real. -/
theorem tree_source_real_of_real_subtree
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {path : List Nat} {node : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : subtreeAt? tree path = some node)
    (nodeReal : node.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom) :
    tree.source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  cases path with
  | nil =>
      rw [subtreeAt?_nil] at lookup
      have nodeEq : node = tree := (Option.some.inj lookup).symm
      rw [← nodeEq]
      exact nodeReal
  | cons slot rest =>
      obtain ⟨child, childLookup, _restLookup⟩ :=
        (subtreeAt?_cons_eq_some_iff).mp lookup
      exact provenance_real_of_executableChild tree.source child.source
        (mem_executable_of_child realizes childLookup)




theorem realChildReachable_of_subtree_real
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    ∀ {path : List Nat} {node : LocalizedCumulativeDecoratedTree input carrierFuel},
      subtreeAt? tree path = some node →
      node.source.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom →
      input.RealChildReachable tree.source node.source := by
  intro path
  induction path generalizing tree with
  | nil =>
      intro node lookup nodeReal
      rw [subtreeAt?_nil] at lookup
      have nodeEq : node = tree := (Option.some.inj lookup).symm
      rw [nodeEq]
      exact Relation.ReflTransGen.refl
  | cons slot rest ih =>
      intro node lookup nodeReal
      obtain ⟨child, childLookup, restLookup⟩ :=
        (subtreeAt?_cons_eq_some_iff).mp lookup
      have childReal := tree_source_real_of_real_subtree
        (realizes_of_child realizes childLookup) restLookup nodeReal
      have single : input.RealChildReachable tree.source child.source :=
        Relation.ReflTransGen.tail Relation.ReflTransGen.refl
          ⟨mem_executable_of_child realizes childLookup, childReal⟩
      exact single.trans
        (ih (tree := child) (realizes_of_child realizes childLookup) restLookup nodeReal)

/-- **Every real position is real-child-reachable from the tree source.** -/
theorem realPosition_source_realChildReachable
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p : RealPosition tree) :
    input.RealChildReachable tree.source (positionSource p.1) :=
  realChildReachable_of_subtree_real realizes (positionNode_spec p.1) p.2

/-- **The target of a real-child path is real.**  The zero-step case uses the real start, and every
actual tail step records the real provenance of its target. -/
theorem realChildReachable_target_real
    {start target : input.LocalizedRerootCursor carrierFuel}
    (startReal : start.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    (reachable : Relation.ReflTransGen
      (fun left right : input.LocalizedRerootCursor carrierFuel =>
        CertifiedLocalizedCIPInput.E input left right ∧
          right.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
      start target) :
    target.occurrence.1.node.provenance = OfficialCIPNodeProvenance.realAtom := by
  induction reachable with
  | refl => exact startReal
  | tail _path step _ih => exact step.2

/-! ## Membership in the physical cut branch -/

/-- **Cut membership of a real position.**  Forward real reachability plus the real projection
place every real position's atom in the physical branch of the attachment atom. -/
theorem realPositionAtom_mem_cutBranch
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p : RealPosition tree) :
    realPositionAtom p ∈
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom :=
  input.realReachable_current_mem_cutBranch acyclic enough tree.source previous
    previousEq valid startReal previousReal oObserved pObserved incomingEdge
    (positionSource p.1) (realPosition_source_realChildReachable realizes p)
    (realPositionAtom_spec p)

/-- **Parent/child atoms of an actual child are physically adjacent.**  This is the
provenance-free adjacency of every emitted child (`localizedRerootChildren?_child_current_adjacent`)
applied to the actual executable child supplied by realization. -/
theorem nodeCurrent_adjacent_of_child
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child) :
    input.moleculeGraph.Adj (nodeCurrent tree) (nodeCurrent child) :=
  input.localizedRerootChildren?_child_current_adjacent tree.source
    (input.executableLocalizedRerootChildren tree.source)
    (input.localizedRerootChildren?_eq_some_executable tree.source)
    (nodeCurrent_spec tree) child.source
    (mem_executable_of_child realizes lookup) (nodeCurrent_spec child)

/-- **Cut membership inside a child branch.**  A real position of an actual child lies in the
physical branch of the child atom after deleting the parent atom.  Both endpoint realness
witnesses are derived from actual data: the parent source is real because it has an executable
child, and the child source is real because it contains the real position `q`. -/
theorem realPositionAtom_mem_child_cutBranch
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {slot : Nat} {child : LocalizedCumulativeDecoratedTree input carrierFuel}
    (lookup : tree.children[slot]? = some child)
    (q : RealPosition child) :
    realPositionAtom q ∈
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph
        (nodeCurrent tree) (nodeCurrent child) := by
  have childRealizes : LocalizedCumulativeTreeRealizes input read child :=
    realizes_of_child realizes lookup
  have childSourceReal : child.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom :=
    tree_source_real_of_real_subtree childRealizes (positionNode_spec q.1) q.2
  have treeSourceReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom :=
    provenance_real_of_executableChild tree.source child.source
      (mem_executable_of_child realizes lookup)
  have adjacent : input.moleculeGraph.Adj (nodeCurrent tree) (nodeCurrent child) :=
    nodeCurrent_adjacent_of_child realizes lookup
  exact realPositionAtom_mem_cutBranch acyclic enough childRealizes
    (tree.source.occurrence) (child_previous_of_child realizes lookup)
    (child_valid_of_child realizes lookup) childSourceReal treeSourceReal
    (nodeCurrent_spec child) (nodeCurrent_spec tree) adjacent q

/-! ## Injectivity of the real atom projection -/





theorem child_current_injective
    (acyclic : input.moleculeGraph.Acyclic)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {i j : Nat} (hi : i < tree.children.length) (hj : j < tree.children.length)
    (realI : tree.children[i].source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (realJ : tree.children[j].source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (same : nodeCurrent tree.children[i] = nodeCurrent tree.children[j]) :
    i = j := by
  obtain ⟨children, computed, perm⟩ := exists_sourcePerm realizes
  have hci : tree.children[i]? = some tree.children[i] := List.getElem?_eq_getElem hi
  have hcj : tree.children[j]? = some tree.children[j] := List.getElem?_eq_getElem hj
  have memI : tree.children[i].source ∈ children :=
    perm.mem_iff.mp (List.mem_map.mpr ⟨tree.children[i], List.mem_of_getElem? hci, rfl⟩)
  have memJ : tree.children[j].source ∈ children :=
    perm.mem_iff.mp (List.mem_map.mpr ⟨tree.children[j], List.mem_of_getElem? hcj, rfl⟩)
  have sameCurrent : tree.children[i].source.occurrence.1.node.current? =
      tree.children[j].source.occurrence.1.node.current? := by
    rw [nodeCurrent_spec tree.children[i], nodeCurrent_spec tree.children[j], same]
  have sourcesEq := input.localizedRerootChildren?_realChild_unique acyclic tree.source
    children computed tree.children[i].source memI tree.children[j].source memJ realI realJ
    sameCurrent
  have childrenNodup : children.Nodup := by
    have executable := input.localizedRerootChildren?_eq_some_executable tree.source
    have childrenEq : children = input.executableLocalizedRerootChildren tree.source :=
      Option.some.inj (computed.symm.trans executable)
    rw [childrenEq]
    exact input.executableLocalizedRerootChildren_nodup tree.source
  have mappedNodup : (tree.children.map (fun t => t.source)).Nodup :=
    perm.nodup_iff.mpr childrenNodup
  have mappedInjective := List.nodup_iff_injective_getElem.mp mappedNodup
  have hi' : i < (tree.children.map (fun t => t.source)).length := by simpa using hi
  have hj' : j < (tree.children.map (fun t => t.source)).length := by simpa using hj
  have finEq : (⟨i, hi'⟩ : Fin (tree.children.map (fun t => t.source)).length) =
      ⟨j, hj'⟩ := by
    apply mappedInjective
    simpa using sourcesEq
  exact congrArg Fin.val finEq

/-- **Real position injectivity, by total slot-path length.**  Distinct real positions of one
actual realized tree carry distinct physical atoms.  The proof recurses on the sum of the two
path lengths and uses disjointness of the physical branches of distinct real children; no
`SimpleBonded` hypothesis and no supplied position bijection is used. -/
theorem realPosition_injective_aux
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (bound : Nat) :
    ∀ (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
      (_realizes : LocalizedCumulativeTreeRealizes input read tree)
      (p q : RealPosition tree),
      p.1.val.length + q.1.val.length ≤ bound →
        realPositionAtom p = realPositionAtom q → p = q := by
  induction bound using Nat.strong_induction_on with
  | _ bound ih =>
    intro tree realizes p q hbound hatom
    obtain ⟨⟨pPath, pProp⟩, pReal⟩ := p
    obtain ⟨⟨qPath, qProp⟩, qReal⟩ := q
    cases pPath with
    | nil =>
        cases qPath with
        | nil => rfl
        | cons qSlot qRest =>
            exfalso
            have pAtomEq : realPositionAtom
                (⟨⟨[], pProp⟩, pReal⟩ : RealPosition tree) = nodeCurrent tree := by
              change nodeCurrent (positionNode (⟨[], pProp⟩ : Position tree)) =
                nodeCurrent tree
              rw [positionNode_eq_tree_of_val_eq_nil rfl]
            have qAtomEqTree : realPositionAtom
                (⟨⟨qSlot :: qRest, qProp⟩, qReal⟩ : RealPosition tree) =
                  nodeCurrent tree := by
              rw [← pAtomEq]
              exact hatom.symm
            obtain ⟨childQ, lookupQ, qChild, _qVal, nodeEqQ⟩ :=
              exists_child_of_position_cons
                (p := (⟨qSlot :: qRest, qProp⟩ : Position tree)) rfl
            let q' : RealPosition childQ :=
              ⟨qChild, by
                show (positionNode qChild).source.occurrence.1.node.provenance =
                  OfficialCIPNodeProvenance.realAtom
                rw [← nodeEqQ]
                exact qReal⟩
            have qEq : realPositionAtom
                (⟨⟨qSlot :: qRest, qProp⟩, qReal⟩ : RealPosition tree) =
                  realPositionAtom q' := by
              change nodeCurrent
                (positionNode (⟨qSlot :: qRest, qProp⟩ : Position tree)) =
                  nodeCurrent (positionNode q'.1)
              rw [nodeEqQ]
            have q'AtomTree : realPositionAtom q' = nodeCurrent tree :=
              qEq.symm.trans qAtomEqTree
            have mem := realPositionAtom_mem_child_cutBranch
              (acyclic := acyclic) (enough := enough) realizes lookupQ q'
            rw [q'AtomTree] at mem
            exact AcyclicCutBranchAutomorphism.center_not_mem_cutBranch
              input.moleculeGraph (nodeCurrent tree) (nodeCurrent childQ) mem
    | cons pSlot pRest =>
        cases qPath with
        | nil =>
            exfalso
            have qAtomEq : realPositionAtom
                (⟨⟨[], qProp⟩, qReal⟩ : RealPosition tree) = nodeCurrent tree := by
              change nodeCurrent (positionNode (⟨[], qProp⟩ : Position tree)) =
                nodeCurrent tree
              rw [positionNode_eq_tree_of_val_eq_nil rfl]
            have pAtomEqTree : realPositionAtom
                (⟨⟨pSlot :: pRest, pProp⟩, pReal⟩ : RealPosition tree) =
                  nodeCurrent tree := by
              rw [← qAtomEq]
              exact hatom
            obtain ⟨childP, lookupP, pChild, _pVal, nodeEqP⟩ :=
              exists_child_of_position_cons
                (p := (⟨pSlot :: pRest, pProp⟩ : Position tree)) rfl
            let p' : RealPosition childP :=
              ⟨pChild, by
                show (positionNode pChild).source.occurrence.1.node.provenance =
                  OfficialCIPNodeProvenance.realAtom
                rw [← nodeEqP]
                exact pReal⟩
            have pEq : realPositionAtom
                (⟨⟨pSlot :: pRest, pProp⟩, pReal⟩ : RealPosition tree) =
                  realPositionAtom p' := by
              change nodeCurrent
                (positionNode (⟨pSlot :: pRest, pProp⟩ : Position tree)) =
                  nodeCurrent (positionNode p'.1)
              rw [nodeEqP]
            have p'AtomTree : realPositionAtom p' = nodeCurrent tree :=
              pEq.symm.trans pAtomEqTree
            have mem := realPositionAtom_mem_child_cutBranch
              (acyclic := acyclic) (enough := enough) realizes lookupP p'
            rw [p'AtomTree] at mem
            exact AcyclicCutBranchAutomorphism.center_not_mem_cutBranch
              input.moleculeGraph (nodeCurrent tree) (nodeCurrent childP) mem
        | cons qSlot qRest =>
            by_cases hslot : pSlot = qSlot
            · subst hslot
              obtain ⟨childP, lookupP, pChild, pValChild, nodeEqP⟩ :=
                exists_child_of_position_cons
                  (p := (⟨pSlot :: pRest, pProp⟩ : Position tree)) rfl
              obtain ⟨childQ, lookupQ, qChild, qValChild, nodeEqQ⟩ :=
                exists_child_of_position_cons
                  (p := (⟨pSlot :: qRest, qProp⟩ : Position tree)) rfl
              have childEq : childP = childQ :=
                Option.some.inj (lookupP.symm.trans lookupQ)
              subst childEq
              let p' : RealPosition childP :=
                ⟨pChild, by
                  show (positionNode pChild).source.occurrence.1.node.provenance =
                    OfficialCIPNodeProvenance.realAtom
                  rw [← nodeEqP]
                  exact pReal⟩
              let q' : RealPosition childP :=
                ⟨qChild, by
                  show (positionNode qChild).source.occurrence.1.node.provenance =
                    OfficialCIPNodeProvenance.realAtom
                  rw [← nodeEqQ]
                  exact qReal⟩
              have pEq : realPositionAtom
                  (⟨⟨pSlot :: pRest, pProp⟩, pReal⟩ : RealPosition tree) =
                    realPositionAtom p' := by
                change nodeCurrent
                  (positionNode (⟨pSlot :: pRest, pProp⟩ : Position tree)) =
                    nodeCurrent (positionNode p'.1)
                rw [nodeEqP]
              have qEq : realPositionAtom
                  (⟨⟨pSlot :: qRest, qProp⟩, qReal⟩ : RealPosition tree) =
                    realPositionAtom q' := by
                change nodeCurrent
                  (positionNode (⟨pSlot :: qRest, qProp⟩ : Position tree)) =
                    nodeCurrent (positionNode q'.1)
                rw [nodeEqQ]
              have hatom' : realPositionAtom p' = realPositionAtom q' :=
                pEq.symm.trans (hatom.trans qEq)
              have hb : (pRest.length + 1) + (qRest.length + 1) ≤ bound := by
                simpa using hbound
              have hsmall : pRest.length + qRest.length < bound := by omega
              have hle : p'.1.val.length + q'.1.val.length ≤
                  pRest.length + qRest.length := by
                have hp : p'.1.val = pRest := pValChild
                have hq : q'.1.val = qRest := qValChild
                rw [hp, hq]
              have hpq : p' = q' :=
                ih (pRest.length + qRest.length) hsmall childP
                  (realizes_of_child realizes lookupP) p' q' hle hatom'
              have restEq : pRest = qRest := by
                have posEq : p'.1 = q'.1 :=
                  congrArg (fun r : RealPosition childP => r.1) hpq
                calc pRest = p'.1.val := pValChild.symm
                  _ = q'.1.val := congrArg (fun x : Position childP => x.val) posEq
                  _ = qRest := qValChild
              apply Subtype.ext
              apply position_ext
              change pSlot :: pRest = pSlot :: qRest
              rw [restEq]
            · exfalso
              obtain ⟨childP, lookupP, pChild, _pValChild, nodeEqP⟩ :=
                exists_child_of_position_cons
                  (p := (⟨pSlot :: pRest, pProp⟩ : Position tree)) rfl
              obtain ⟨childQ, lookupQ, qChild, _qValChild, nodeEqQ⟩ :=
                exists_child_of_position_cons
                  (p := (⟨qSlot :: qRest, qProp⟩ : Position tree)) rfl
              let p' : RealPosition childP :=
                ⟨pChild, by
                  show (positionNode pChild).source.occurrence.1.node.provenance =
                    OfficialCIPNodeProvenance.realAtom
                  rw [← nodeEqP]
                  exact pReal⟩
              let q' : RealPosition childQ :=
                ⟨qChild, by
                  show (positionNode qChild).source.occurrence.1.node.provenance =
                    OfficialCIPNodeProvenance.realAtom
                  rw [← nodeEqQ]
                  exact qReal⟩
              have pEq : realPositionAtom
                  (⟨⟨pSlot :: pRest, pProp⟩, pReal⟩ : RealPosition tree) =
                    realPositionAtom p' := by
                change nodeCurrent
                  (positionNode (⟨pSlot :: pRest, pProp⟩ : Position tree)) =
                    nodeCurrent (positionNode p'.1)
                rw [nodeEqP]
              have qEq : realPositionAtom
                  (⟨⟨qSlot :: qRest, qProp⟩, qReal⟩ : RealPosition tree) =
                    realPositionAtom q' := by
                change nodeCurrent
                  (positionNode (⟨qSlot :: qRest, qProp⟩ : Position tree)) =
                    nodeCurrent (positionNode q'.1)
                rw [nodeEqQ]
              have hatom' : realPositionAtom p' = realPositionAtom q' :=
                pEq.symm.trans (hatom.trans qEq)
              obtain ⟨hiP, hvalP⟩ := List.getElem_of_getElem? lookupP
              obtain ⟨hiQ, hvalQ⟩ := List.getElem_of_getElem? lookupQ
              have childPReal : childP.source.occurrence.1.node.provenance =
                  OfficialCIPNodeProvenance.realAtom :=
                tree_source_real_of_real_subtree
                  (realizes_of_child realizes lookupP) (positionNode_spec p'.1) p'.2
              have childQReal : childQ.source.occurrence.1.node.provenance =
                  OfficialCIPNodeProvenance.realAtom :=
                tree_source_real_of_real_subtree
                  (realizes_of_child realizes lookupQ) (positionNode_spec q'.1) q'.2
              have childPReal' :
                  tree.children[pSlot].source.occurrence.1.node.provenance =
                    OfficialCIPNodeProvenance.realAtom := by
                rw [hvalP]
                exact childPReal
              have childQReal' :
                  tree.children[qSlot].source.occurrence.1.node.provenance =
                    OfficialCIPNodeProvenance.realAtom := by
                rw [hvalQ]
                exact childQReal
              have distinct : nodeCurrent childP ≠ nodeCurrent childQ := by
                intro same
                apply hslot
                apply child_current_injective acyclic realizes hiP hiQ childPReal' childQReal'
                calc nodeCurrent tree.children[pSlot]
                    = nodeCurrent childP := by rw [hvalP]
                  _ = nodeCurrent childQ := same
                  _ = nodeCurrent tree.children[qSlot] := by rw [hvalQ]
              have memP := realPositionAtom_mem_child_cutBranch
                (acyclic := acyclic) (enough := enough) realizes lookupP p'
              have memQ := realPositionAtom_mem_child_cutBranch
                (acyclic := acyclic) (enough := enough) realizes lookupQ q'
              rw [hatom'] at memP
              have adjP : input.moleculeGraph.Adj
                  (nodeCurrent tree) (nodeCurrent childP) :=
                nodeCurrent_adjacent_of_child realizes lookupP
              have adjQ : input.moleculeGraph.Adj
                  (nodeCurrent tree) (nodeCurrent childQ) :=
                nodeCurrent_adjacent_of_child realizes lookupQ
              exact distinct (AcyclicCutBranchAutomorphism.cutBranch_disjoint_of_acyclic
                input.moleculeGraph acyclic adjP adjQ memP memQ)

/-- **Real position injectivity.** -/
theorem realPosition_injective
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p q : RealPosition tree)
    (atomEq : realPositionAtom p = realPositionAtom q) :
    p = q :=
  realPosition_injective_aux acyclic enough
    (p.1.val.length + q.1.val.length) tree realizes p q le_rfl atomEq

/-! ## Surjectivity onto the physical cut branch -/






theorem exists_realPosition_of_mem_cutBranch
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    {w : input.Atom}
    (mem : w ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
    ∃ p : RealPosition tree, realPositionAtom p = w := by
  obtain ⟨target, reachable, targetObserved⟩ :=
    (input.realChildReachable_current_iff_cutBranch_general acyclic enough tree.source
      previous previousEq sameRoot valid startReal previousReal oObserved pObserved
      incomingEdge w).mpr mem
  have targetReal := realChildReachable_target_real startReal reachable
  have actual : input.ActualChildReachable tree.source target :=
    Relation.ReflTransGen.mono (fun _ _ step => step.1) reachable
  obtain ⟨p, hp⟩ := exists_position_of_actualChildReachable realizes actual
  have pReal : PositionReal p := by
    change (positionSource p).occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom
    rw [hp]
    exact targetReal
  refine ⟨⟨p, pReal⟩, ?_⟩
  have observed := realPositionAtom_spec (⟨p, pReal⟩ : RealPosition tree)
  rw [hp] at observed
  exact Option.some.inj (observed.symm.trans targetObserved)

/-! ## The actual real-position/cut-branch equivalence -/

/-- **The actual bijection between real positions and the physical cut branch.**

The forward map is the real position's physical atom; membership is
`realPositionAtom_mem_cutBranch`, injectivity is `realPosition_injective`, and surjectivity is
`exists_realPosition_of_mem_cutBranch`.  Neither the bijection nor coverage is supplied as an
assumption: both halves are derived from the realized tree, the actual executable child lists and
the physical cut correspondence. -/
noncomputable def realPositionCutEquiv
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom) :
    RealPosition tree ≃
      AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom :=
  Equiv.ofBijective
    (fun p : RealPosition tree =>
      ⟨realPositionAtom p,
        realPositionAtom_mem_cutBranch acyclic enough realizes previous previousEq valid
          startReal previousReal oObserved pObserved incomingEdge p⟩)
    ⟨fun p q imageEq =>
        realPosition_injective acyclic enough realizes p q (congrArg Subtype.val imageEq),
      fun a => by
        obtain ⟨p, hp⟩ :=
          exists_realPosition_of_mem_cutBranch acyclic enough realizes previous previousEq
            sameRoot valid startReal previousReal oObserved pObserved incomingEdge a.property
        exact ⟨p, Subtype.ext hp⟩⟩

/-- The forward map of `realPositionCutEquiv` is exactly the physical atom of the position. -/
@[simp] theorem realPositionCutEquiv_apply_coe
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p : RealPosition tree) :
    ((realPositionCutEquiv acyclic enough realizes previous previousEq sameRoot valid
        startReal previousReal oObserved pObserved incomingEdge p :
          AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
        input.Atom) =
      realPositionAtom p :=
  rfl

/-- **The root real position maps to the attachment atom.** -/
theorem realPositionCutEquiv_rootPosition
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom) :
    realPositionCutEquiv acyclic enough realizes previous previousEq sameRoot valid
        startReal previousReal oObserved pObserved incomingEdge
        (⟨rootPosition tree, startReal⟩ : RealPosition tree) =
      ⟨oAtom,
        AcyclicCutBranchAutomorphism.cutBranch_mem_self input.moleculeGraph incomingEdge⟩ := by
  apply Subtype.ext
  change realPositionAtom (⟨rootPosition tree, startReal⟩ : RealPosition tree) = oAtom
  have spec := realPositionAtom_spec (⟨rootPosition tree, startReal⟩ : RealPosition tree)
  have spec' : tree.source.occurrence.1.node.current? =
      some (realPositionAtom (⟨rootPosition tree, startReal⟩ : RealPosition tree)) := by
    simpa using spec
  exact Option.some.inj (spec'.symm.trans oObserved)

/-! ## Adjacency where available -/

/-- **A real position and the real position one slot deeper project to adjacent atoms.**  The
child may be any actual child; realness of both positions is the hypothesis, matching the fact
that duplicate children are not real positions. -/
theorem realPositionAtom_adjacent_of_positionChild
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (p q : RealPosition tree) {slot : Nat}
    (valEq : q.1.val = p.1.val ++ [slot]) :
    input.moleculeGraph.Adj (realPositionAtom p) (realPositionAtom q) := by
  have qSpec : subtreeAt? tree (p.1.val ++ [slot]) = some (positionNode q.1) := by
    rw [← valEq]
    exact positionNode_spec q.1
  have lookup : (positionNode p.1).children[slot]? = some (positionNode q.1) := by
    have h := subtreeAt?_append_singleton p.1.val tree slot
    rw [positionNode_spec p.1, qSpec] at h
    simpa using h.symm
  have adjacent := nodeCurrent_adjacent_of_child
    (realizes_of_subtree realizes (positionNode_spec p.1)) lookup
  simpa only [realPositionAtom, positionCurrent] using adjacent

/-- **Adjacency faithfulness of `realPositionCutEquiv` along actual position children.**  This is
the available one-way adjacency statement on the real slice: tree-child positions correspond to
physically adjacent branch atoms.  The converse (physical adjacency of branch atoms forces
position adjacency) is not claimed here. -/
theorem realPositionCutEquiv_adj_of_positionChild
    (acyclic : input.moleculeGraph.Acyclic)
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    (valid : input.LocalizedRerootCursorValid tree.source)
    (startReal : tree.source.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.realAtom)
    (previousReal : previous.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
    {oAtom pAtom : input.Atom}
    (oObserved : tree.source.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (p q : RealPosition tree) {slot : Nat}
    (valEq : q.1.val = p.1.val ++ [slot]) :
    input.moleculeGraph.Adj
      ((realPositionCutEquiv acyclic enough realizes previous previousEq sameRoot valid
          startReal previousReal oObserved pObserved incomingEdge p :
            AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
          input.Atom)
      ((realPositionCutEquiv acyclic enough realizes previous previousEq sameRoot valid
          startReal previousReal oObserved pObserved incomingEdge q :
            AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom) :
          input.Atom) := by
  rw [realPositionCutEquiv_apply_coe, realPositionCutEquiv_apply_coe]
  exact realPositionAtom_adjacent_of_positionChild realizes p q valEq

end RealPositionAdapter

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.RealActualCutWalkState
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realActualCutWalkState_start
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realActualCutWalkState_step
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realReachable_realActualCutWalkState
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realReachable_current_mem_cutBranch
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.realChildReachable_current_iff_cutBranch_general
assert_kernel_only TetraStereo.OneCenter.occurrenceCurrent
assert_kernel_only TetraStereo.OneCenter.occurrenceCurrent_spec
assert_kernel_only TetraStereo.OneCenter.occurrenceCurrent_eq_of_observed
assert_kernel_only TetraStereo.OneCenter.nodeCurrent
assert_kernel_only TetraStereo.OneCenter.nodeCurrent_spec
assert_kernel_only TetraStereo.OneCenter.positionCurrent
assert_kernel_only TetraStereo.OneCenter.positionCurrent_spec
assert_kernel_only TetraStereo.OneCenter.PositionReal
assert_kernel_only TetraStereo.OneCenter.RealPosition
assert_kernel_only TetraStereo.OneCenter.realPositionAtom
assert_kernel_only TetraStereo.OneCenter.realPositionAtom_spec
assert_kernel_only TetraStereo.OneCenter.realPositionSource
assert_kernel_only TetraStereo.OneCenter.DeclarativeLocalizedOccurrenceSubtree_provenance_ne_placeholder
assert_kernel_only TetraStereo.OneCenter.declarativeLocalizedOccurrence_provenance_ne_placeholder
assert_kernel_only TetraStereo.OneCenter.provenance_real_of_executableChild
assert_kernel_only TetraStereo.OneCenter.tree_source_real_of_real_subtree
assert_kernel_only TetraStereo.OneCenter.realChildReachable_of_subtree_real
assert_kernel_only TetraStereo.OneCenter.realPosition_source_realChildReachable
assert_kernel_only TetraStereo.OneCenter.realChildReachable_target_real
assert_kernel_only TetraStereo.OneCenter.realPositionAtom_mem_cutBranch
assert_kernel_only TetraStereo.OneCenter.nodeCurrent_adjacent_of_child
assert_kernel_only TetraStereo.OneCenter.realPositionAtom_mem_child_cutBranch
assert_kernel_only TetraStereo.OneCenter.child_current_injective
assert_kernel_only TetraStereo.OneCenter.realPosition_injective_aux
assert_kernel_only TetraStereo.OneCenter.realPosition_injective
assert_kernel_only TetraStereo.OneCenter.exists_realPosition_of_mem_cutBranch
assert_kernel_only TetraStereo.OneCenter.realPositionCutEquiv
assert_kernel_only TetraStereo.OneCenter.realPositionCutEquiv_apply_coe
assert_kernel_only TetraStereo.OneCenter.realPositionCutEquiv_rootPosition
assert_kernel_only TetraStereo.OneCenter.realPositionAtom_adjacent_of_positionChild
assert_kernel_only TetraStereo.OneCenter.realPositionCutEquiv_adj_of_positionChild
