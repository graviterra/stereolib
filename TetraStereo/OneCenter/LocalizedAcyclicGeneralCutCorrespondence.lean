import TetraStereo.OneCenter.LocalizedAcyclicRerootNeighborCorrespondence
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# General physical cut correspondence for the actual acyclic reroot cursor

This module removes the outward-only restriction of
`actualChildReachable_current_iff_cutBranch` in
`LocalizedAcyclicRerootNeighborCorrespondence`.  That theorem assumes that the incoming
coordinate of the start cursor is the genuine address parent, i.e. that its address is strictly
shorter than the start address (`parentShorter`).  On a non-root four-frame the incoming physical
edge can instead point *inward* (towards the parent side of the occurrence tree), so the
restriction excludes a genuine chemical case.

The central result here is
`actualChildReachable_current_iff_cutBranch_general`:

> let `start` be an actual reroot cursor whose incoming coordinate `previous` is a real occurrence
> with the same original carrier root, whose current atom is `oAtom`, whose incoming atom is
> `pAtom`, and such that `pAtom` is physically adjacent to `oAtom`.  Then, for **any** such
> incoming physical edge and any valid path start, an atom `w` is the current atom of some cursor
> reached through the actual executable child lists exactly when `w` belongs to the physical cut
> branch of `oAtom` after deleting `pAtom`.

The proof does not assume any desired neighbor bisection, child totality, frame agreement or
physical cut bijection, and it does not replace the original-root carrier by a separately re-rooted
`rootFromEdge` tree.  Every step is an actual member of `executableLocalizedRerootChildren`.

## Proof route

The forward direction is driven by the *general actual path invariant*
`actualReachable_actualCutWalkState`.  Starting from the incoming physical edge `pAtom - oAtom`,
every actually reachable cursor is accompanied by

* a simple physical walk from `oAtom` to its current atom that avoids `pAtom`, and
* the equation that prepending the incoming edge makes the penultimate vertex of that walk the
  current atom of the cursor's recorded previous occurrence.

The local correspondence `localizedRerootChildren?_current_iff_adjacent_of_previous` supplies
exactly `Adj current w` together with `w ≠ penultimate`.  Acyclicity via
`MoleculeGraph.Acyclic.not_mem_support_of_adj_ne_penultimate` then guarantees that the next atom
is fresh, so appending the edge preserves simplicity and cannot revisit the initial deleted atom
`pAtom`.  The penultimate equation is transported through
`SimpleGraph.Walk.penultimate_cons_of_not_nil` and `SimpleGraph.Walk.penultimate_concat`.

The backward direction is exactly the simple-chain lifting engine
`actualReachable_of_simple_chain` of the previous module, which never used `parentShorter`: the
chain excluded at each step is the single incoming atom, and duplicate-freedom of the simple
physical walk supplies the freshness hypothesis.

The original occurrence root is preserved along the actual edges; no cursor is re-rooted.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

variable (input : CertifiedLocalizedCIPInput)

/-! ## The physical simple graph and the general actual walk state -/

/-- The underlying simple graph of the certified molecular graph, with its type-spine named so
that the physical walk types of the invariant are written without relying on unfolding. -/
abbrev molecularSimpleGraph (input : CertifiedLocalizedCIPInput) :
    SimpleGraph input.Atom :=
  input.moleculeGraph.underlyingSimpleGraph

/-- **General actual physical-cut state.**  A cursor reached from an actual incoming physical
edge `pAtom - oAtom` carries a recorded previous occurrence, its current and incoming physical
atoms, and a simple physical walk from `oAtom` to its current atom that avoids the deleted atom
`pAtom`; prepending the incoming edge makes the penultimate vertex of that walk the current atom
of the recorded previous occurrence.

The state is purely physical: it records no address length comparison, so it applies equally to
inward (parent-side) and outward (child-side) actual steps.  It is a `Prop` (all witnesses are
existential) so that it can be proved by induction over the `Prop`-valued actual reachability
relation. -/
def ActualCutWalkState (input : CertifiedLocalizedCIPInput)
    {oAtom pAtom : input.Atom}
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel) : Prop :=
  ∃ (previous : input.LocalizedCIPOccurrence carrierFuel)
    (current : input.Atom) (incoming : input.Atom)
    (walk : (input.molecularSimpleGraph).Walk oAtom current),
    cursor.previous? = some previous ∧
      cursor.occurrence.1.node.current? = some current ∧
      previous.1.node.current? = some incoming ∧
      input.LocalizedRerootCursorValid cursor ∧
      walk.IsPath ∧
      pAtom ∉ walk.support ∧
      (SimpleGraph.Walk.cons incomingEdge walk).penultimate = incoming

/-! ## Base state and actual step -/

/-- **Base state.**  The incoming physical edge itself is the initial simple physical walk: its
endpoint is the start cursor's current atom and its penultimate vertex is the incoming atom. -/
theorem actualCutWalkState_start
    {oAtom pAtom : input.Atom}
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    {carrierFuel : Nat}
    {start : input.LocalizedRerootCursor carrierFuel}
    {previous : input.LocalizedCIPOccurrence carrierFuel}
    (previousEq : start.previous? = some previous)
    (validStart : input.LocalizedRerootCursorValid start)
    (oObserved : start.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom) :
    ActualCutWalkState input incomingEdge start := by
  have oNeP : pAtom ≠ oAtom := by
    intro same
    exact input.molecularSimpleGraph.irrefl (same.symm ▸ incomingEdge)
  refine ⟨previous, oAtom, pAtom, SimpleGraph.Walk.nil, previousEq, oObserved,
    pObserved, validStart, SimpleGraph.Walk.IsPath.nil, ?_, ?_⟩
  · simpa [SimpleGraph.Walk.support_nil] using oNeP
  · simp [SimpleGraph.Walk.penultimate_cons_nil]

/-- **One actual step preserves the general physical-cut state.**  The local correspondence of
`LocalizedAcyclicRerootNeighborCorrespondence` gives the physical adjacency for the new current
atom and excludes the recorded incoming atom.  Acyclicity then shows that the new atom is fresh
along the stored simple walk, so the walk can be extended and the penultimate equation is
transported to the extended walk. -/
theorem actualCutWalkState_step
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    {oAtom pAtom : input.Atom}
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    {b c : input.LocalizedRerootCursor carrierFuel}
    (stateB : ActualCutWalkState input incomingEdge b)
    (step : E input b c)
    {w : input.Atom}
    (wObserved : c.occurrence.1.node.current? = some w) :
    ActualCutWalkState input incomingEdge c := by
  unfold ActualCutWalkState at stateB
  obtain ⟨previousB, x, z, walkB, previousEqB, xObserved, zObserved, validB,
    simpleB, avoidsB, penultimateB⟩ := stateB
  -- The state of the source cursor exposes its recorded incoming coordinate.
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
  -- The actual local cut correspondence at the source cursor.
  have localIff :=
    input.localizedRerootChildren?_current_iff_adjacent_of_previous
      singleBonded acyclic enough b previousB previousEqB sameRootB
      xObserved zObserved
      (input.executableLocalizedRerootChildren b)
      (input.localizedRerootChildren?_eq_some_executable b)
  obtain ⟨adjacent, wNeIncoming⟩ := (localIff w).mp ⟨c, step, wObserved⟩
  -- The stored walk, extended by the incoming edge, is a simple physical path.
  have fullPath : (SimpleGraph.Walk.cons incomingEdge walkB).IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff incomingEdge walkB).2 ⟨simpleB, avoidsB⟩
  have fresh := MoleculeGraph.Acyclic.not_mem_support_of_adj_ne_penultimate
    input.moleculeGraph acyclic fullPath penultimateB adjacent wNeIncoming
  have fresh' : ¬ (w = pAtom ∨ w ∈ walkB.support) := by
    simpa only [SimpleGraph.Walk.support_cons, List.mem_cons] using fresh
  have wNeP : w ≠ pAtom := fun same => fresh' (Or.inl same)
  have wNotWalk : w ∉ walkB.support := fun present => fresh' (Or.inr present)
  -- Extend the physical walk by the new physical edge.
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
  have newPenultimate :
      (SimpleGraph.Walk.cons incomingEdge newWalk).penultimate = x := by
    rw [SimpleGraph.Walk.penultimate_cons_of_not_nil incomingEdge newWalk newNotNil]
    simp [newWalk]
  -- The executable step records the source occurrence and keeps path validity.
  have childDerived : input.DeclarativeLocalizedRerootChildren b
      (input.executableLocalizedRerootChildren b) :=
    input.executableLocalizedRerootChildren_declarative b
  have childPrevious : c.previous? = some b.occurrence := childDerived.2 c step
  have childValid : input.LocalizedRerootCursorValid c :=
    input.localizedRerootChild_valid b c
      (input.executableLocalizedRerootChildren b) childDerived step
  exact ⟨b.occurrence, w, x, newWalk, childPrevious, wObserved, xObserved, childValid,
    newSimple, newAvoid, newPenultimate⟩

/-! ## The general actual path invariant -/

/-- **General actual path invariant.**  Along every actual executable child path from a start
cursor with any genuine incoming physical edge `pAtom - oAtom`, each reached cursor carries a
recorded previous occurrence, its current and incoming atoms, and a simple physical walk from
`oAtom` to its current atom avoiding `pAtom`, whose penultimate after prepending the incoming edge
is the current atom of the recorded previous occurrence.

No address-length comparison between the recorded previous and the cursor is used anywhere: the
invariant is purely physical, so it covers inward (parent-side) as well as outward steps. -/
theorem actualReachable_actualCutWalkState
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : start.previous? = some previous)
    (validStart : input.LocalizedRerootCursorValid start)
    {oAtom pAtom : input.Atom}
    (oObserved : start.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (target : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start target) :
    ActualCutWalkState input incomingEdge target := by
  induction reachable with
  | refl =>
      exact input.actualCutWalkState_start incomingEdge previousEq validStart
        oObserved pObserved
  | @tail b c stepPath step ih =>
      have targetDerived :
          input.DeclarativeLocalizedOccurrence carrierFuel c.occurrence.1 :=
        (input.mem_localizedOccurrences_iff carrierFuel c.occurrence.1).mp
          c.occurrence.2
      obtain ⟨w, wObserved⟩ := Option.isSome_iff_exists.mp
        (input.declarativeLocalizedOccurrence_node_current_isSome targetDerived)
      exact input.actualCutWalkState_step singleBonded acyclic enough incomingEdge
        ih step wObserved

/-! ## Reachability keeps the original occurrence root -/

/-- Every cursor reached through the actual executable child lists keeps the original occurrence
root of the start cursor.  No `rootFromEdge` re-rooting is introduced. -/
theorem actualReachable_root_eq_start
    {carrierFuel : Nat}
    (start target : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start target) :
    target.occurrence.1.root = start.occurrence.1.root := by
  induction reachable with
  | refl => rfl
  | @tail b c stepPath step ih =>
      exact (input.localizedRerootChildren_root_eq b c
        (input.executableLocalizedRerootChildren b)
        (input.executableLocalizedRerootChildren_declarative b) step).trans ih

/-! ## Forward direction: reachable current atoms lie in the physical cut branch -/

/-- **Forward direction.**  Every current atom of a cursor actually reached from the start lies in
the physical cut branch of `oAtom` after deleting `pAtom`.  The witness is the simple physical
walk stored by the general path invariant. -/
theorem actualReachable_current_mem_cutBranch_general
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : start.previous? = some previous)
    (validStart : input.LocalizedRerootCursorValid start)
    {oAtom pAtom : input.Atom}
    (oObserved : start.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (target : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start target)
    {w : input.Atom}
    (observed : target.occurrence.1.node.current? = some w) :
    w ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom := by
  have state :=
    input.actualReachable_actualCutWalkState singleBonded acyclic enough start previous
      previousEq validStart oObserved pObserved incomingEdge target reachable
  unfold ActualCutWalkState at state
  obtain ⟨_previousT, current, _incomingT, walkT, _previousEqT, currentObserved,
    _incomingObservedT, _validT, _simpleT, avoidsT, _penultimateT⟩ := state
  have sameCurrent : w = current :=
    Option.some.inj (observed.symm.trans currentObserved)
  rw [sameCurrent]
  exact ⟨walkT, avoidsT⟩

/-! ## The central general correspondence -/

/-- **Actual reachability is exactly the physical cut branch, for an arbitrary incoming physical
edge.**  This is the `parentShorter`-free form of
`actualChildReachable_current_iff_cutBranch`.

Let `start` be an actual reroot cursor at any carrier fuel at least `atomCount`, with a genuine
incoming physical edge `pAtom - oAtom` recorded as its previous occurrence, the same original
carrier root on both coordinates, and a valid path start.  Then an atom `w` is the current atom of
some cursor reached through the actual executable child lists (zero steps included) if and only if
`w` lies in the physical branch of `oAtom` after deleting `pAtom`.

No address-length comparison between the incoming coordinate and the start cursor is assumed, so
this covers inward/parent-side incoming coordinates on non-root four-frames as well as outward
ones.  Neither direction assumes a desired neighbor bisection, child totality, frame agreement or
physical cut bijection. -/
theorem actualChildReachable_current_iff_cutBranch_general
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (acyclic : input.moleculeGraph.Acyclic)
    {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (previous : input.LocalizedCIPOccurrence carrierFuel)
    (previousEq : start.previous? = some previous)
    (sameRootStart : start.occurrence.1.root = previous.1.root)
    (validStart : input.LocalizedRerootCursorValid start)
    {oAtom pAtom : input.Atom}
    (oObserved : start.occurrence.1.node.current? = some oAtom)
    (pObserved : previous.1.node.current? = some pAtom)
    (incomingEdge : input.moleculeGraph.Adj pAtom oAtom)
    (w : input.Atom) :
    (∃ target : input.LocalizedRerootCursor carrierFuel,
      input.ActualChildReachable start target ∧
        target.occurrence.1.node.current? = some w) ↔
      w ∈ AcyclicCutBranchAutomorphism.CutBranch input.moleculeGraph pAtom oAtom := by
  constructor
  · rintro ⟨target, reachable, observed⟩
    exact input.actualReachable_current_mem_cutBranch_general singleBonded acyclic enough
      start previous previousEq validStart oObserved pObserved incomingEdge
      target reachable observed
  · intro branchMem
    -- Backward: lift the simple physical path avoiding `pAtom` through the actual child lists.
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
      input.actualReachable_of_simple_chain singleBonded acyclic enough rest
        start previous oAtom pAtom previousEq sameRootStart oObserved pObserved
        nodup chain avoidCons
    exact ⟨target, reachable, by rw [targetObserved, lastEq]⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.molecularSimpleGraph
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualCutWalkState
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualCutWalkState_start
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualCutWalkState_step
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualReachable_actualCutWalkState
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualReachable_root_eq_start
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualReachable_current_mem_cutBranch_general
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.actualChildReachable_current_iff_cutBranch_general
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualChildReachable
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ActualCutReachableState
