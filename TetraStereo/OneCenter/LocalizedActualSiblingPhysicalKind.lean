import TetraStereo.OneCenter.LocalizedActualPhysicalReferenceObservationClosure
import TetraStereo.OneCenter.LocalizedPhysicalReferenceCovariance
import TetraStereo.OneCenter.LocalizedCutBranchSelfAutomorphism
import TetraStereo.OneCenter.LocalizedRealizedTreeCutIsomorphism
import TetraStereo.OneCenter.LocalizedGeneralRigidCalibratedRootReader
import TetraStereo.KernelOnly

set_option autoImplicit false




























































namespace TetraStereo.OneCenter

open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open AcyclicCutBranchAutomorphism

variable {input : LocalizedUniversalReference.Input}

/-! ## Incoming data along actual reachability

A cursor reached from a start cursor with genuine incoming data still records incoming data with the
same original occurrence root, still observes a real parent atom, and stays path-valid.  This is the
generalization of the setup tree's incoming data to every actually reachable tree. -/

/-- **Incoming data is preserved by actual reachability.**  If `start` records `previous` with the
same original root and a real current atom, then every cursor actually reached from `start` records
incoming data with the same root and a real current atom, and is a valid reroot cursor. -/
theorem actualReachable_incomingData
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {start target : input.LocalizedRerootCursor carrierFuel}
    (reachable : input.ActualChildReachable start target)
    {previous : input.LocalizedCIPOccurrence carrierFuel}
    (previousEq : start.previous? = some previous)
    (sameRoot : start.occurrence.1.root = previous.1.root)
    (previousObserved : ∃ atom, previous.1.node.current? = some atom)
    (validStart : input.LocalizedRerootCursorValid start) :
    ∃ previousT : input.LocalizedCIPOccurrence carrierFuel,
      target.previous? = some previousT ∧
        target.occurrence.1.root = previousT.1.root ∧
          (∃ atom, previousT.1.node.current? = some atom) ∧
            input.LocalizedRerootCursorValid target := by
  induction reachable with
  | refl => exact ⟨previous, previousEq, sameRoot, previousObserved, validStart⟩
  | @tail b c _stepPath step ih =>
      obtain ⟨_previousB, _previousEqB, _rootEqB, _observedB, _validB⟩ := ih
      have declarative : input.DeclarativeLocalizedOccurrence carrierFuel b.occurrence.1 :=
        (input.mem_localizedOccurrences_iff carrierFuel b.occurrence.1).mp b.occurrence.2
      obtain ⟨atom, atomObserved⟩ :=
        Option.isSome_iff_exists.mp
          (input.declarativeLocalizedOccurrence_node_current_isSome declarative)
      have childDerived : input.DeclarativeLocalizedRerootChildren b
          (input.executableLocalizedRerootChildren b) :=
        input.executableLocalizedRerootChildren_declarative b
      exact ⟨b.occurrence, childDerived.2 c step,
        input.localizedRerootChildren_root_eq b c
          (input.executableLocalizedRerootChildren b) childDerived step,
        ⟨atom, atomObserved⟩,
        input.localizedRerootChild_valid b c
          (input.executableLocalizedRerootChildren b) childDerived step⟩

/-! ## Actual reader values at realized positions

The label stored at a realized node is the reader value at its own source cursor.  For the actual
dependency reader this is the restricted dependency label; the dependency itself is derived from
outward reachability, never assumed. -/

/-- The root label of an actually realized decorated tree is the reader value at its source. -/
theorem label_eq_read_of_realizes
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    tree.label = read tree.source := by
  cases realizes
  rfl

/-- The label at an actual position of a realized tree is the reader value at that position's own
actual source cursor. -/
theorem position_label_eq_reader
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (p : Position tree) :
    (positionNode p).label = read (positionSource p) := by
  have h := label_eq_read_of_realizes (realizes_of_subtree realizes (positionNode_spec p))
  simpa only [positionSource] using h

/-! ## Incoming data at an arbitrary position

The physical parent atom of a position is only available from the actual incoming edge recorded at
that position.  For the root position this is the tree's own incoming data; for any other position
it is the actual child relation inside the decorated tree. -/

/-- **Positional incoming data.**  Every position of a realized tree records a genuine incoming
occurrence with the same original root and a real current atom.  The root case uses the incoming
data of the tree source (supplied, derived above from actual reachability); every other position
uses the actual decorated child relation. -/
theorem positionSource_previous_data
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {previous : input.LocalizedCIPOccurrence carrierFuel}
    (previousEq : tree.source.previous? = some previous)
    (sameRoot : tree.source.occurrence.1.root = previous.1.root)
    (previousObserved : ∃ atom, previous.1.node.current? = some atom)
    (p : Position tree) :
    ∃ previousP : input.LocalizedCIPOccurrence carrierFuel,
      (positionSource p).previous? = some previousP ∧
        (positionSource p).occurrence.1.root = previousP.1.root ∧
          (∃ atom, previousP.1.node.current? = some atom) := by
  by_cases pathNil : p.val = []
  · have nodeEq : positionNode p = tree := positionNode_eq_tree_of_val_eq_nil pathNil
    exact ⟨previous, by simpa only [positionSource, nodeEq] using previousEq,
      by simpa only [positionSource, nodeEq] using sameRoot, previousObserved⟩
  · obtain ⟨slot, lookup⟩ := positionParent_node_child p pathNil
    have realizesParent : LocalizedCumulativeTreeRealizes input read
        (positionNode (positionParent p pathNil)) :=
      realizes_of_subtree realizes (positionNode_spec (positionParent p pathNil))
    have previousDeclarative : input.DeclarativeLocalizedOccurrence carrierFuel
        (positionSource (positionParent p pathNil)).occurrence.1 :=
      (input.mem_localizedOccurrences_iff carrierFuel
        (positionSource (positionParent p pathNil)).occurrence.1).mp
        (positionSource (positionParent p pathNil)).occurrence.2
    obtain ⟨atom, atomObserved⟩ :=
      Option.isSome_iff_exists.mp
        (input.declarativeLocalizedOccurrence_node_current_isSome previousDeclarative)
    exact ⟨(positionSource (positionParent p pathNil)).occurrence,
      by simpa only [positionSource] using child_previous_of_child realizesParent lookup,
      by simpa only [positionSource] using child_root_of_child realizesParent lookup,
      ⟨atom, atomObserved⟩⟩

/-! ## Original-root exclusion from a sibling cut branch

The central physical input of the sibling theorem: the detected original root never lies in the
physical cut branch of a child of an actually reachable tree.  The proof uses both directions of the
general actual cut correspondence: the reverse direction would produce an actual cursor at the
original root inside the child branch, and the forward direction from the original setup tree then
contradicts the root's exclusion from its own slot branch. -/

/-- **The original root is outside every child cut branch of an actually reachable realized tree.**
This generalizes the setup-tree statement to arbitrary trees actually reached from the
original-root frame slot. -/
theorem reachable_root_not_mem_child_cutBranch
    (setup : ActualSlotPhysicalSetup input)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) tree)
    (reachable : input.certified.ActualChildReachable setup.tree.source tree.source)
    (p : Position tree) (slot : Nat)
    (bound : slot < (positionNode p).children.length) :
    setup.c.1 ∉ AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph
      (positionAtom setup.singleBonded setup.acyclic p)
      (positionAtom setup.singleBonded setup.acyclic (positionChild p slot bound)) := by
  intro branchMem
  have lookup : (positionNode p).children[slot]? = some (positionNode (positionChild p slot bound)) := by
    rw [positionNode_positionChild]
    exact List.getElem?_eq_getElem bound
  have realizesParent : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) (positionNode p) :=
    realizes_of_subtree realizes (positionNode_spec p)
  have childPrevious : (positionSource (positionChild p slot bound)).previous? =
      some (positionSource p).occurrence :=
    child_previous_of_child realizesParent lookup
  have childRoot : (positionSource (positionChild p slot bound)).occurrence.1.root =
      (positionSource p).occurrence.1.root :=
    child_root_of_child realizesParent lookup
  have childValid : input.certified.LocalizedRerootCursorValid
      (positionSource (positionChild p slot bound)) :=
    child_valid_of_child realizesParent lookup
  obtain ⟨treePrevious, treePreviousEq, treeSameRoot, treePreviousObserved, _treeValid⟩ :=
    actualReachable_incomingData (input := input.certified) reachable setup.tree_previousEq
      setup.tree_sameRoot
      ⟨↑setup.c, ActualReaderPhysicalBranchInverse.topTarget_current input setup.c⟩
      setup.tree_valid
  have adjacent : input.certified.moleculeGraph.Adj
      (positionAtom setup.singleBonded setup.acyclic p)
      (positionAtom setup.singleBonded setup.acyclic (positionChild p slot bound)) := by
    obtain ⟨previousP, previousEqP, sameRootP, parentAtom, parentObserved⟩ :=
      positionSource_previous_data (input := input.certified)
        (read := ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) realizes
        treePreviousEq treeSameRoot treePreviousObserved p
    exact positionAtom_adjacent_of_positionChild setup.singleBonded setup.acyclic
      (globalCarrierFuel_adequate input) realizes previousP
      (by simpa only [positionSource] using previousEqP)
      (by simpa only [positionSource] using sameRootP)
      (parentAtom := parentAtom) parentObserved
      (pathEq := positionChild_val p slot bound)
  obtain ⟨target, reachableTarget, targetObserved⟩ :=
    (input.certified.actualChildReachable_current_iff_cutBranch_general setup.singleBonded
      setup.acyclic (globalCarrierFuel_adequate input)
      (positionSource (positionChild p slot bound)) (positionSource p).occurrence
      childPrevious childRoot childValid
      (positionAtom_spec setup.singleBonded setup.acyclic (positionChild p slot bound))
      (positionAtom_spec setup.singleBonded setup.acyclic p)
      adjacent setup.c.1).mpr branchMem
  have reachChild : input.certified.ActualChildReachable setup.tree.source
      (positionSource (positionChild p slot bound)) :=
    reachable.trans (actualChildReachable_positionSource realizes (positionChild p slot bound))
  have reachTarget : input.certified.ActualChildReachable setup.tree.source target :=
    reachChild.trans reachableTarget
  have rootMem : setup.c.1 ∈ AcyclicCutBranchAutomorphism.CutBranch
      input.certified.moleculeGraph setup.c.1 setup.oAtom :=
    input.certified.actualReachable_current_mem_cutBranch_general setup.singleBonded setup.acyclic
      (globalCarrierFuel_adequate input) setup.tree.source
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c) setup.tree_previousEq
      setup.tree_valid setup.tree_oObserved
      (ActualReaderPhysicalBranchInverse.topTarget_current input setup.c)
      setup.incomingEdge target reachTarget targetObserved
  exact AcyclicCutBranchAutomorphism.center_not_mem_cutBranch input.certified.moleculeGraph
    setup.c.1 setup.oAtom rootMem









/-- **Dependency and path validity of any actually reachable cursor.**  Derived from the actual
frame first-child membership and strict depth, and the outward propagation of actual reachability. -/
theorem reachable_cursor_dependency
    (setup : ActualSlotPhysicalSetup input)
    {cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor) :
    input.certified.LocalizedDepthDependency cursor.occurrence
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c) ∧
      input.certified.LocalizedRerootCursorValid cursor := by
  have reachableFrame : input.certified.ActualChildReachable
      (setup.frame.cursorAt setup.slot) cursor := by
    rw [← setup.tree_source]
    exact reachable
  have present : setup.frame.cursorAt setup.slot ∈ setup.frame.cursors := by
    unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    exact List.get_mem _ _
  have firstChild : setup.frame.cursorAt setup.slot ∈
      input.certified.executableLocalizedRerootChildren
        ({ occurrence := ActualReaderPhysicalBranchInverse.topTarget input setup.c,
            previous? := none } :
          input.certified.LocalizedRerootCursor
            (LocalizedUniversalReference.carrierFuel input)) :=
    ActualReaderPhysicalBranchInverse.mem_executableLocalizedRerootChildren_of_frame
      input.certified (ActualReaderPhysicalBranchInverse.topTarget input setup.c) setup.frame
      setup.frameComputed (setup.frame.cursorAt setup.slot) present
  have firstDeeper :
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c).1.address.length <
        (setup.frame.cursorAt setup.slot).occurrence.1.address.length :=
    ActualReaderPhysicalBranchInverse.frame_cursor_strictlyDeeper_of_target_address_nil
      input.certified (ActualReaderPhysicalBranchInverse.topTarget input setup.c) setup.frame
      setup.frameComputed (ActualReaderPhysicalBranchInverse.topTarget_address input setup.c)
      (setup.frame.cursorAt setup.slot) present
  exact outward_reachable_dependency input.certified
    (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
    (setup.frame.cursorAt setup.slot) cursor firstChild firstDeeper reachableFrame

/-- **The actual dependency reader at any reachable cursor is the whole reference state.** -/
theorem reachable_cursor_reader_eq_state
    (setup : ActualSlotPhysicalSetup input)
    {cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor) :
    ActualReaderPhysicalBranchInverse.dependencyReader input setup.c cursor =
      LocalizedUniversalReference.referenceState input cursor.occurrence :=
  localizedDependencyLabel_eq_state_of_dependency input.certified
    (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
    (LocalizedUniversalReference.referenceState input) cursor
    (reachable_cursor_dependency setup reachable).1



theorem reachable_cursor_reader_none_or_chiral
    (setup : ActualSlotPhysicalSetup input)
    {cursor : input.certified.LocalizedRerootCursor
      (LocalizedUniversalReference.carrierFuel input)}
    (reachable : input.certified.ActualChildReachable setup.tree.source cursor) :
    ActualReaderPhysicalBranchInverse.dependencyReader input setup.c cursor = none ∨
      ∃ rs : RS,
        ActualReaderPhysicalBranchInverse.dependencyReader input setup.c cursor =
          some (.chiral rs) := by
  rw [reachable_cursor_reader_eq_state setup reachable]
  exact actualStrictDependency_referenceState_none_or_chiral_generalRigid
    (input := input) (singleBonded := setup.singleBonded) (acyclic := setup.acyclic)
    (hcharge := setup.hcharge) (noDouble := setup.noDouble)
    (cfg := input.certified.canonicalReindexConfiguration setup.cfg)
    (root := ⟨setup.c.1, setup.c.2⟩) (domain := setup.globalDomain)
    (topCenter := ⟨setup.c.1, setup.c.2⟩) (topAt := rfl) (cursor := cursor)
    (dependency := (reachable_cursor_dependency setup reachable).1)

/-! ## Actual reader classification at every reachable position

The slot frame cursor is an actual strictly deeper child of the final target, so every cursor
actually reached from it -- and hence every position of every reachable realized tree -- is a strict
depth dependency of that target.  This is the generalization of the setup-tree classification to
arbitrary reachable trees, derived from actual reachability rather than from a source equality. -/

/-- **Every position of an actually reachable realized tree is a strict dependency of the final
target, and its source cursor is valid.**  The frame cursor is an actual first child strictly deeper
than the target (its address is uncut), and reachability propagates the outward property. -/
theorem reachable_position_dependency
    (setup : ActualSlotPhysicalSetup input)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) tree)
    (reachable : input.certified.ActualChildReachable setup.tree.source tree.source)
    (p : Position tree) :
    input.certified.LocalizedDepthDependency (positionSource p).occurrence
        (ActualReaderPhysicalBranchInverse.topTarget input setup.c) ∧
      input.certified.LocalizedRerootCursorValid (positionSource p) := by
  have reachableFrame : input.certified.ActualChildReachable
      (setup.frame.cursorAt setup.slot) (positionSource p) := by
    rw [← setup.tree_source]
    exact reachable.trans (actualChildReachable_positionSource realizes p)
  have present : setup.frame.cursorAt setup.slot ∈ setup.frame.cursors := by
    unfold LocalizedOccurrenceFourLigandFrame.cursorAt
    exact List.get_mem _ _
  have firstChild : setup.frame.cursorAt setup.slot ∈
      input.certified.executableLocalizedRerootChildren
        ({ occurrence := ActualReaderPhysicalBranchInverse.topTarget input setup.c,
            previous? := none } :
          input.certified.LocalizedRerootCursor
            (LocalizedUniversalReference.carrierFuel input)) :=
    ActualReaderPhysicalBranchInverse.mem_executableLocalizedRerootChildren_of_frame
      input.certified (ActualReaderPhysicalBranchInverse.topTarget input setup.c) setup.frame
      setup.frameComputed (setup.frame.cursorAt setup.slot) present
  have firstDeeper :
      (ActualReaderPhysicalBranchInverse.topTarget input setup.c).1.address.length <
        (setup.frame.cursorAt setup.slot).occurrence.1.address.length :=
    ActualReaderPhysicalBranchInverse.frame_cursor_strictlyDeeper_of_target_address_nil
      input.certified (ActualReaderPhysicalBranchInverse.topTarget input setup.c) setup.frame
      setup.frameComputed (ActualReaderPhysicalBranchInverse.topTarget_address input setup.c)
      (setup.frame.cursorAt setup.slot) present
  exact outward_reachable_dependency input.certified
    (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
    (setup.frame.cursorAt setup.slot) (positionSource p) firstChild firstDeeper reachableFrame

/-- **The actual node label at every reachable position is the actual whole reference state at
that position's actual occurrence.**  The realized tree was built with the actual restricted
dependency reader, and the position is a derived strict dependency of the final target, so the
restricted read agrees with the unrestricted production state. -/
theorem reachable_position_label_eq_state
    (setup : ActualSlotPhysicalSetup input)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) tree)
    (reachable : input.certified.ActualChildReachable setup.tree.source tree.source)
    (p : Position tree) :
    (positionNode p).label =
      LocalizedUniversalReference.referenceState input (positionSource p).occurrence := by
  have readerEq := position_label_eq_reader realizes p
  rw [readerEq]
  exact localizedDependencyLabel_eq_state_of_dependency input.certified
    (ActualReaderPhysicalBranchInverse.topTarget input setup.c)
    (LocalizedUniversalReference.referenceState input) (positionSource p)
    (reachable_position_dependency setup realizes reachable p).1





theorem reachable_position_sparse
    (setup : ActualSlotPhysicalSetup input)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) tree)
    (reachable : input.certified.ActualChildReachable setup.tree.source tree.source)
    (p : Position tree) :
    LocalizedUniversalReference.referenceState input (positionSource p).occurrence = none ∨
      ∃ rs : RS,
        LocalizedUniversalReference.referenceState input (positionSource p).occurrence =
          some (.chiral rs) :=
  actualStrictDependency_referenceState_none_or_chiral_generalRigid
    (input := input) (singleBonded := setup.singleBonded) (acyclic := setup.acyclic)
    (hcharge := setup.hcharge) (noDouble := setup.noDouble)
    (cfg := input.certified.canonicalReindexConfiguration setup.cfg)
    (root := ⟨setup.c.1, setup.c.2⟩) (domain := setup.globalDomain)
    (topCenter := ⟨setup.c.1, setup.c.2⟩) (topAt := rfl) (cursor := positionSource p)
    (dependency := (reachable_position_dependency setup realizes reachable p).1)

/-- **Every position atom of an actually reachable tree lies in the original slot's physical cut
branch.**  The forward general cut correspondence is applied at the original setup tree; no
same-root hypothesis and no address comparison is used. -/
theorem reachable_position_atom_mem_slotBranch
    (setup : ActualSlotPhysicalSetup input)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) tree)
    (reachable : input.certified.ActualChildReachable setup.tree.source tree.source)
    (p : Position tree) :
    positionAtom setup.singleBonded setup.acyclic p ∈
      AcyclicCutBranchAutomorphism.CutBranch input.certified.moleculeGraph setup.c.1
        setup.oAtom :=
  input.certified.actualReachable_current_mem_cutBranch_general setup.singleBonded setup.acyclic
    (globalCarrierFuel_adequate input) setup.tree.source
    (ActualReaderPhysicalBranchInverse.topTarget input setup.c) setup.tree_previousEq
    setup.tree_valid setup.tree_oObserved
    (ActualReaderPhysicalBranchInverse.topTarget_current input setup.c)
    setup.incomingEdge (positionSource p)
    (reachable.trans (actualChildReachable_positionSource realizes p))
    (positionAtom_spec setup.singleBonded setup.acyclic p)





theorem reachable_position_chiral_iff_marked
    (setup : ActualSlotPhysicalSetup input)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) tree)
    (reachable : input.certified.ActualChildReachable setup.tree.source tree.source)
    (p : Position tree) :
    (∃ rs : RS,
        LocalizedUniversalReference.referenceState input (positionSource p).occurrence =
          some (.chiral rs)) ↔
      PhysicalMarkedAtom input setup.root
        (positionAtom setup.singleBonded setup.acyclic p) := by
  have rootEq : (positionSource p).occurrence.1.root = setup.c.1 :=
    ((reachable_position_dependency setup realizes reachable p).1).1.trans
      (ActualReaderPhysicalBranchInverse.topTarget_root input setup.c)
  exact referenceState_chiral_iff_physicalMarked input setup.singleBonded setup.acyclic
    setup.hcharge setup.noDouble (input.certified.canonicalReindexConfiguration setup.cfg)
    setup.c setup.globalDomain setup.incomingEdge (positionSource p).occurrence rootEq
    (positionAtom_spec setup.singleBonded setup.acyclic p)
    (reachable_position_atom_mem_slotBranch setup realizes reachable p)

/-! ## Sparse kind algebra

A sparse label -- `none` or an uppercase chiral descriptor -- is `none` exactly when it carries no
chiral descriptor.  Consequently two sparse labels with the same `none` status have the same Rule-4a
kind priority: `0` for `none`, `2` for an uppercase descriptor.  No pseudoasymmetric case arises. -/

/-- A sparse label is `none` exactly when it admits no chiral descriptor. -/
theorem option_none_iff_not_exists_chiral_of_sparse
    {σ : Option LocalizedAuxiliaryLabel}
    (sparse : σ = none ∨ ∃ rs : RS, σ = some (.chiral rs)) :
    σ = none ↔ ¬ ∃ rs : RS, σ = some (.chiral rs) := by
  constructor
  · rintro rfl ⟨rs, h⟩
    cases h
  · intro noChiral
    rcases sparse with noneEq | ⟨rs, chiralEq⟩
    · exact noneEq
    · exact absurd ⟨rs, chiralEq⟩ noChiral

/-- Two sparse labels with the same `none` status have the same Rule-4a kind priority. -/
theorem localizedRule4aPriority_eq_of_sparse
    {left right : Option LocalizedAuxiliaryLabel}
    (sparseLeft : left = none ∨ ∃ rs : RS, left = some (.chiral rs))
    (sparseRight : right = none ∨ ∃ rs : RS, right = some (.chiral rs))
    (noneIff : left = none ↔ right = none) :
    localizedRule4aPriority left = localizedRule4aPriority right := by
  rcases sparseLeft with leftNone | ⟨leftRs, leftChiral⟩
  · have rightNone : right = none := noneIff.mp leftNone
    rw [leftNone, rightNone]
  · have rightNotNone : right ≠ none := by
      intro rightNone
      have leftNone : left = none := noneIff.mpr rightNone
      rw [leftChiral] at leftNone
      cases leftNone
    rcases sparseRight with rightNone | ⟨rightRs, rightChiral⟩
    · exact absurd rightNone rightNotNone
    · rw [leftChiral, rightChiral]
      rfl











/-- **Actual sibling physical kind.**  Two successful actual dependency-reader stage builds at two
distinct children `slotL`, `slotR` of one position `p` of an actually reachable realized tree, with
constitutionally tied comparison, produce matched actual trees `tL`, `tR` with the exact source cursors,
equal erased shape, both actual table matches and both actual realizability witnesses.  At every
position of either tree the actual node label is the whole actual reference state and that state is
`none` or an uppercase chiral descriptor (no pseudoasymmetric label, no pseudo exclusion).  At every
corresponding position (under `shapePositionEquiv hshape`) the labels have the same `none` status,
the same chiral-descriptor existence status, the same Rule-4a kind priority and the same physical
markedness.  Root fixation and markedness transport are derived, not assumed. -/
theorem exists_actualSiblingPhysicalKind
    (setup : ActualSlotPhysicalSetup input)
    {tree : LocalizedCumulativeDecoratedTree input.certified
      (LocalizedUniversalReference.carrierFuel input)}
    (realizes : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) tree)
    (reachable : input.certified.ActualChildReachable setup.tree.source tree.source)
    (p : Position tree)
    {slotL slotR : Nat}
    (boundL : slotL < (positionNode p).children.length)
    (boundR : slotR < (positionNode p).children.length)
    (distinct : slotL ≠ slotR)
    (stageL stageR : LocalizedCumulativeRule45Stage)
    (fuelL fuelR : Nat)
    (keyL keyR : input.certified.LocalizedRerootCumulativeRule45Key)
    (builtL : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stageL
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) fuelL
      (positionSource (positionChild p slotL boundL)) = some keyL)
    (builtR : input.certified.buildLocalizedRerootCumulativeRule45KeyWithRead? stageR
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) fuelR
      (positionSource (positionChild p slotR boundR)) = some keyR)
    (constitutionalTie :
      OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional = .eq) :
    ∃ (tL tR : LocalizedCumulativeDecoratedTree input.certified
          (LocalizedUniversalReference.carrierFuel input))
      (hshape : shape tL = shape tR)
      (_sourceL : tL.source = positionSource (positionChild p slotL boundL))
      (_sourceR : tR.source = positionSource (positionChild p slotR boundR))
      (_matchL : LocalizedCumulativeTreeTableMatch stageL tL keyL)
      (_matchR : LocalizedCumulativeTreeTableMatch stageR tR keyR)
      (_realizesL : LocalizedCumulativeTreeRealizes input.certified
        (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) tL)
      (_realizesR : LocalizedCumulativeTreeRealizes input.certified
        (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) tR),
      (∀ pL : Position tL,
        (positionNode pL).label =
          LocalizedUniversalReference.referenceState input (positionSource pL).occurrence) ∧
      (∀ pR : Position tR,
        (positionNode pR).label =
          LocalizedUniversalReference.referenceState input (positionSource pR).occurrence) ∧
      (∀ pL : Position tL,
        LocalizedUniversalReference.referenceState input (positionSource pL).occurrence = none ∨
          ∃ rs : RS,
            LocalizedUniversalReference.referenceState input (positionSource pL).occurrence =
              some (.chiral rs)) ∧
      (∀ pR : Position tR,
        LocalizedUniversalReference.referenceState input (positionSource pR).occurrence = none ∨
          ∃ rs : RS,
            LocalizedUniversalReference.referenceState input (positionSource pR).occurrence =
              some (.chiral rs)) ∧
      (∀ pL : Position tL,
        (positionNode pL).label = none ↔
          (positionNode (shapePositionEquiv hshape pL)).label = none) ∧
      (∀ pL : Position tL,
        (∃ rs : RS, (positionNode pL).label = some (.chiral rs)) ↔
          ∃ rs : RS,
            (positionNode (shapePositionEquiv hshape pL)).label = some (.chiral rs)) ∧
      (∀ pL : Position tL,
        localizedRule4aPriority (positionNode pL).label =
          localizedRule4aPriority (positionNode (shapePositionEquiv hshape pL)).label) ∧
      (∀ pL : Position tL,
        PhysicalMarkedAtom input setup.root
            (positionAtom setup.singleBonded setup.acyclic pL) ↔
          PhysicalMarkedAtom input setup.root
            (positionAtom setup.singleBonded setup.acyclic (shapePositionEquiv hshape pL))) := by
  have ⟨rule1aEq, rule1bEq, rule2Eq⟩ :=
    (officialRuleMajorKey_compare_eq_iff keyL.constitutional keyR.constitutional).mp
      constitutionalTie
  have realizesParent : LocalizedCumulativeTreeRealizes input.certified
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) (positionNode p) :=
    realizes_of_subtree realizes (positionNode_spec p)
  have lookupL : (positionNode p).children[slotL]? =
      some (positionNode (positionChild p slotL boundL)) := by
    rw [positionNode_positionChild]
    exact List.getElem?_eq_getElem boundL
  have lookupR : (positionNode p).children[slotR]? =
      some (positionNode (positionChild p slotR boundR)) := by
    rw [positionNode_positionChild]
    exact List.getElem?_eq_getElem boundR
  have previousEqL : (positionSource (positionChild p slotL boundL)).previous? =
      some (positionSource p).occurrence :=
    child_previous_of_child realizesParent lookupL
  have sameRootL : (positionSource (positionChild p slotL boundL)).occurrence.1.root =
      (positionSource p).occurrence.1.root :=
    child_root_of_child realizesParent lookupL
  have validL : input.certified.LocalizedRerootCursorValid
      (positionSource (positionChild p slotL boundL)) :=
    child_valid_of_child realizesParent lookupL
  have previousEqR : (positionSource (positionChild p slotR boundR)).previous? =
      some (positionSource p).occurrence :=
    child_previous_of_child realizesParent lookupR
  have sameRootR : (positionSource (positionChild p slotR boundR)).occurrence.1.root =
      (positionSource p).occurrence.1.root :=
    child_root_of_child realizesParent lookupR
  have validR : input.certified.LocalizedRerootCursorValid
      (positionSource (positionChild p slotR boundR)) :=
    child_valid_of_child realizesParent lookupR
  obtain ⟨treePrevious, treePreviousEq, treeSameRoot, treePreviousObserved, _treeValid⟩ :=
    actualReachable_incomingData (input := input.certified) reachable setup.tree_previousEq
      setup.tree_sameRoot
      ⟨↑setup.c, ActualReaderPhysicalBranchInverse.topTarget_current input setup.c⟩
      setup.tree_valid
  have treeDeclarative : input.certified.DeclarativeLocalizedOccurrence
      (LocalizedUniversalReference.carrierFuel input) tree.source.occurrence.1 :=
    (input.certified.mem_localizedOccurrences_iff (LocalizedUniversalReference.carrierFuel input)
      tree.source.occurrence.1).mp tree.source.occurrence.2
  obtain ⟨treeAtom, treeAtomObserved⟩ :=
    Option.isSome_iff_exists.mp
      (input.certified.declarativeLocalizedOccurrence_node_current_isSome treeDeclarative)
  have huv : positionAtom setup.singleBonded setup.acyclic (positionChild p slotL boundL) ≠
      positionAtom setup.singleBonded setup.acyclic (positionChild p slotR boundR) := by
    intro atomEq
    have positionsEq : positionChild p slotL boundL = positionChild p slotR boundR :=
      positionAtom_injective setup.singleBonded setup.acyclic (globalCarrierFuel_adequate input)
        realizes treePrevious treePreviousEq treeSameRoot treeAtomObserved
        treePreviousObserved.choose_spec
        (positionChild p slotL boundL) (positionChild p slotR boundR) atomEq
    have valEq : p.val ++ [slotL] = p.val ++ [slotR] := by
      have := congrArg (fun q : Position tree => q.val) positionsEq
      simpa only [positionChild_val] using this
    have slotsEq : slotL = slotR := by
      have := List.append_cancel_left valEq
      simpa using this
    exact distinct slotsEq
  have hcu : input.certified.moleculeGraph.Adj
      (positionAtom setup.singleBonded setup.acyclic p)
      (positionAtom setup.singleBonded setup.acyclic (positionChild p slotL boundL)) := by
    obtain ⟨previousP, previousEqP, sameRootP, parentAtom, parentObserved⟩ :=
      positionSource_previous_data (input := input.certified)
        (read := ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) realizes
        treePreviousEq treeSameRoot treePreviousObserved p
    exact positionAtom_adjacent_of_positionChild setup.singleBonded setup.acyclic
      (globalCarrierFuel_adequate input) realizes previousP
      (by simpa only [positionSource] using previousEqP)
      (by simpa only [positionSource] using sameRootP)
      (parentAtom := parentAtom) parentObserved
      (pathEq := positionChild_val p slotL boundL)
  have hcv : input.certified.moleculeGraph.Adj
      (positionAtom setup.singleBonded setup.acyclic p)
      (positionAtom setup.singleBonded setup.acyclic (positionChild p slotR boundR)) := by
    obtain ⟨previousP, previousEqP, sameRootP, parentAtom, parentObserved⟩ :=
      positionSource_previous_data (input := input.certified)
        (read := ActualReaderPhysicalBranchInverse.dependencyReader input setup.c) realizes
        treePreviousEq treeSameRoot treePreviousObserved p
    exact positionAtom_adjacent_of_positionChild setup.singleBonded setup.acyclic
      (globalCarrierFuel_adequate input) realizes previousP
      (by simpa only [positionSource] using previousEqP)
      (by simpa only [positionSource] using sameRootP)
      (parentAtom := parentAtom) parentObserved
      (pathEq := positionChild_val p slotR boundR)
  obtain ⟨tL, tR, hshape, sourceL, sourceR, matchL, matchR, realizesL, realizesR, swapLaw⟩ :=
    exists_rootedCutBranchIso_of_buildWithRead input.certified
      (singleBonded := setup.singleBonded) (acyclic := setup.acyclic)
      (enough := globalCarrierFuel_adequate input)
      stageL stageR
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c)
      (ActualReaderPhysicalBranchInverse.dependencyReader input setup.c)
      fuelL fuelR
      (positionSource (positionChild p slotL boundL))
      (positionSource (positionChild p slotR boundR))
      keyL keyR builtL builtR rule1aEq rule1bEq rule2Eq
      (c := positionAtom setup.singleBonded setup.acyclic p)
      (u := positionAtom setup.singleBonded setup.acyclic (positionChild p slotL boundL))
      (v := positionAtom setup.singleBonded setup.acyclic (positionChild p slotR boundR))
      previousEqL validL sameRootL previousEqR validR sameRootR
      (positionAtom_spec setup.singleBonded setup.acyclic (positionChild p slotL boundL))
      (positionAtom_spec setup.singleBonded setup.acyclic p)
      (positionAtom_spec setup.singleBonded setup.acyclic (positionChild p slotR boundR))
      (positionAtom_spec setup.singleBonded setup.acyclic p)
      hcu hcv setup.acyclic huv setup.singleBonded setup.hcharge
  let φ := rootedCutBranchIso_of_shapeMatch (singleBonded := setup.singleBonded)
    (acyclic := setup.acyclic) (globalCarrierFuel_adequate input) hshape realizesL realizesR
    (sourceL ▸ previousEqL) (sourceL ▸ validL) (sourceL ▸ sameRootL)
    (sourceR ▸ previousEqR) (sourceR ▸ validR) (sourceR ▸ sameRootR)
    (sourceL ▸ positionAtom_spec setup.singleBonded setup.acyclic
      (positionChild p slotL boundL))
    (positionAtom_spec setup.singleBonded setup.acyclic p)
    (sourceR ▸ positionAtom_spec setup.singleBonded setup.acyclic
      (positionChild p slotR boundR))
    (positionAtom_spec setup.singleBonded setup.acyclic p) hcu hcv
  let e := detectedCutBranchSwapAut input.certified.moleculeGraph
    (positionAtom setup.singleBonded setup.acyclic p)
    (positionAtom setup.singleBonded setup.acyclic (positionChild p slotL boundL))
    (positionAtom setup.singleBonded setup.acyclic (positionChild p slotR boundR))
    setup.acyclic hcu hcv huv setup.singleBonded setup.hcharge φ
  have eApplyRoot : (e : Equiv.Perm input.certified.Atom) setup.root.1 = setup.root.1 := by
    change ((detectedCutBranchSwapAut input.certified.moleculeGraph
      (positionAtom setup.singleBonded setup.acyclic p)
      (positionAtom setup.singleBonded setup.acyclic (positionChild p slotL boundL))
      (positionAtom setup.singleBonded setup.acyclic (positionChild p slotR boundR))
      setup.acyclic hcu hcv huv setup.singleBonded setup.hcharge φ :
        input.certified.moleculeGraph.detectedMultiCenterMolecule.Aut) :
      Equiv.Perm input.certified.Atom) setup.root.1 = setup.root.1
    rw [detectedCutBranchSwapAut_apply, cutBranchSwap_apply]
    exact cutBranchSwapFun_of_not_mem input.certified.moleculeGraph
      (positionAtom setup.singleBonded setup.acyclic p)
      (positionAtom setup.singleBonded setup.acyclic (positionChild p slotL boundL))
      (positionAtom setup.singleBonded setup.acyclic (positionChild p slotR boundR))
      φ
      (reachable_root_not_mem_child_cutBranch setup realizes reachable p slotL boundL)
      (reachable_root_not_mem_child_cutBranch setup realizes reachable p slotR boundR)
  have hcenter :
      input.certified.detectedMultiCenterMolecule.centerPerm e setup.root = setup.root :=
    LocalizedCutBranchSelfAutomorphism.centerPerm_eq_self_of_apply_eq
      input.certified.detectedMultiCenterMolecule e setup.root eApplyRoot
  have markedAt : ∀ q : Position tL,
      PhysicalMarkedAtom input setup.root
          (positionAtom setup.singleBonded setup.acyclic q) ↔
        PhysicalMarkedAtom input setup.root
          (positionAtom setup.singleBonded setup.acyclic (shapePositionEquiv hshape q)) := by
    intro q
    have imageEq : (e : Equiv.Perm input.certified.Atom)
        (positionAtom setup.singleBonded setup.acyclic q) =
        positionAtom setup.singleBonded setup.acyclic (shapePositionEquiv hshape q) := by
      change ((detectedCutBranchSwapAut input.certified.moleculeGraph
        (positionAtom setup.singleBonded setup.acyclic p)
        (positionAtom setup.singleBonded setup.acyclic (positionChild p slotL boundL))
        (positionAtom setup.singleBonded setup.acyclic (positionChild p slotR boundR))
        setup.acyclic hcu hcv huv setup.singleBonded setup.hcharge φ :
          input.certified.moleculeGraph.detectedMultiCenterMolecule.Aut) :
        Equiv.Perm input.certified.Atom)
          (positionAtom setup.singleBonded setup.acyclic q) =
        positionAtom setup.singleBonded setup.acyclic (shapePositionEquiv hshape q)
      simpa only [detectedCutBranchSwapAut_apply, cutBranchSwapAut_apply] using swapLaw q
    have transport := LocalizedPhysicalReferenceCovariance.physicalBranchMarked_transport
      input.certified input.certified.detectedMultiCenterMolecule e hcenter
      (positionAtom setup.singleBonded setup.acyclic q)
    rw [imageEq] at transport
    exact (LocalizedPhysicalReferenceCovariance.physicalBranchMarked_iff_physicalMarkedAtom
        input setup.root (positionAtom setup.singleBonded setup.acyclic q)).symm.trans
      (transport.symm.trans
        (LocalizedPhysicalReferenceCovariance.physicalBranchMarked_iff_physicalMarkedAtom
          input setup.root
          (positionAtom setup.singleBonded setup.acyclic (shapePositionEquiv hshape q))))
  have reachableL : input.certified.ActualChildReachable setup.tree.source tL.source := by
    rw [sourceL]
    exact reachable.trans
      (actualChildReachable_positionSource realizes (positionChild p slotL boundL))
  have reachableR : input.certified.ActualChildReachable setup.tree.source tR.source := by
    rw [sourceR]
    exact reachable.trans
      (actualChildReachable_positionSource realizes (positionChild p slotR boundR))
  refine ⟨tL, tR, hshape, sourceL, sourceR, matchL, matchR, realizesL, realizesR,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro pL
    exact reachable_position_label_eq_state setup realizesL reachableL pL
  · intro pR
    exact reachable_position_label_eq_state setup realizesR reachableR pR
  · intro pL
    exact reachable_position_sparse setup realizesL reachableL pL
  · intro pR
    exact reachable_position_sparse setup realizesR reachableR pR
  · intro pL
    have stateL := reachable_position_label_eq_state setup realizesL reachableL pL
    have stateR := reachable_position_label_eq_state setup realizesR reachableR
      (shapePositionEquiv hshape pL)
    have sparseL := reachable_position_sparse setup realizesL reachableL pL
    have sparseR := reachable_position_sparse setup realizesR reachableR
      (shapePositionEquiv hshape pL)
    have chiralL := reachable_position_chiral_iff_marked setup realizesL reachableL pL
    have chiralR := reachable_position_chiral_iff_marked setup realizesR reachableR
      (shapePositionEquiv hshape pL)
    rw [stateL, stateR]
    exact (option_none_iff_not_exists_chiral_of_sparse sparseL).trans
      ((not_iff_not.mpr (chiralL.trans ((markedAt pL).trans chiralR.symm))).trans
        (option_none_iff_not_exists_chiral_of_sparse sparseR).symm)
  · intro pL
    have stateL := reachable_position_label_eq_state setup realizesL reachableL pL
    have stateR := reachable_position_label_eq_state setup realizesR reachableR
      (shapePositionEquiv hshape pL)
    have chiralL := reachable_position_chiral_iff_marked setup realizesL reachableL pL
    have chiralR := reachable_position_chiral_iff_marked setup realizesR reachableR
      (shapePositionEquiv hshape pL)
    rw [stateL, stateR]
    exact chiralL.trans ((markedAt pL).trans chiralR.symm)
  · intro pL
    have stateL := reachable_position_label_eq_state setup realizesL reachableL pL
    have stateR := reachable_position_label_eq_state setup realizesR reachableR
      (shapePositionEquiv hshape pL)
    have sparseL := reachable_position_sparse setup realizesL reachableL pL
    have sparseR := reachable_position_sparse setup realizesR reachableR
      (shapePositionEquiv hshape pL)
    have chiralL := reachable_position_chiral_iff_marked setup realizesL reachableL pL
    have chiralR := reachable_position_chiral_iff_marked setup realizesR reachableR
      (shapePositionEquiv hshape pL)
    rw [stateL, stateR]
    exact localizedRule4aPriority_eq_of_sparse sparseL sparseR
      ((option_none_iff_not_exists_chiral_of_sparse sparseL).trans
        ((not_iff_not.mpr (chiralL.trans ((markedAt pL).trans chiralR.symm))).trans
          (option_none_iff_not_exists_chiral_of_sparse sparseR).symm))
  · intro pL
    exact markedAt pL

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.actualReachable_incomingData
assert_kernel_only TetraStereo.OneCenter.label_eq_read_of_realizes
assert_kernel_only TetraStereo.OneCenter.position_label_eq_reader
assert_kernel_only TetraStereo.OneCenter.positionSource_previous_data
assert_kernel_only TetraStereo.OneCenter.reachable_root_not_mem_child_cutBranch
assert_kernel_only TetraStereo.OneCenter.reachable_cursor_dependency
assert_kernel_only TetraStereo.OneCenter.reachable_cursor_reader_eq_state
assert_kernel_only TetraStereo.OneCenter.reachable_cursor_reader_none_or_chiral
assert_kernel_only TetraStereo.OneCenter.reachable_position_dependency
assert_kernel_only TetraStereo.OneCenter.reachable_position_label_eq_state
assert_kernel_only TetraStereo.OneCenter.reachable_position_sparse
assert_kernel_only TetraStereo.OneCenter.reachable_position_atom_mem_slotBranch
assert_kernel_only TetraStereo.OneCenter.reachable_position_chiral_iff_marked
assert_kernel_only TetraStereo.OneCenter.option_none_iff_not_exists_chiral_of_sparse
assert_kernel_only TetraStereo.OneCenter.localizedRule4aPriority_eq_of_sparse
assert_kernel_only TetraStereo.OneCenter.exists_actualSiblingPhysicalKind
