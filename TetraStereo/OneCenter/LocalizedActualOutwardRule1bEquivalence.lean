import TetraStereo.OneCenter.LocalizedOutwardRule1bObserverEquivalence
import TetraStereo.OneCenter.LocalizedAllRootUniversalDepth
import TetraStereo.OneCenter.LocalizedOutwardDecoratedSourceFaithfulness
import TetraStereo.OneCenter.LocalizedRuleMajorCumulativeTrace
import TetraStereo.OneCenter.OfficialRuleMajorObservation
import TetraStereo.OneCenter.LocalizedRetainedConstitutionalReaderIndependence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0

/-! # Actual outward Rule 1b comparison

Two actual child cursors of one actual reroot target share one carrier address depth. Carrier
membership and the exact one-slot address extension derive their official outward rank and the
remaining finite expansion budget. This includes a ring-duplicate child, whose official expansion
is terminal.

The revised rule-major cumulative builder is linked to the official compiler at such cursors.
`ruleMajorSortTrace_constitutional_declarative` turns an actual revised trace, at any stage and
reader, into a declarative reroot derivation. Below a cursor that arrived from its carrier parent,
every actual frame carries the executable official children with multiplicity. The derivation and
the official compiler therefore have the same Rule-1a, Rule-1b and Rule-2 tables
(`outwardDeclarative_constitutional_eq_official`).

Only those tables are identified. A stereo tie refinement can order constitutionally tied siblings
differently, so the source nodes and sibling addresses of the two sorted trees are not compared.
The actual and hybrid Rule 1b numbers differ; only their comparison outcomes agree.
-/

namespace TetraStereo.OneCenter
namespace LocalizedActualOutwardRule1bEquivalence

open CertifiedLocalizedCIPInput
open OutwardRule1bObserverEquivalence
open OfficialCIPNode OfficialRuleMajorKey
open MoleculeGraph
open LocalizedCumulativeDecoratedTree

/-- Exact actual outward sibling evidence. Both children are carrier cursors at one real target,
with one-slot extensions of the same address. -/
structure ActualOutwardSiblingPair (input : CertifiedLocalizedCIPInput) (carrierFuel : Nat) where
  target : input.LocalizedRerootCursor carrierFuel
  left : input.LocalizedRerootCursor carrierFuel
  right : input.LocalizedRerootCursor carrierFuel
  leftPrevious : left.previous? = some target.occurrence
  rightPrevious : right.previous? = some target.occurrence
  leftRoot : left.occurrence.1.root = target.occurrence.1.root
  rightRoot : right.occurrence.1.root = target.occurrence.1.root
  leftSlot : Nat
  rightSlot : Nat
  leftAddress : left.occurrence.1.address = target.occurrence.1.address ++ [leftSlot]
  rightAddress : right.occurrence.1.address = target.occurrence.1.address ++ [rightSlot]

private theorem cursor_rank_depth
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    OutwardRanked cursor.occurrence.1.node ∧
      cursor.occurrence.1.node.depth = cursor.occurrence.1.address.length := by
  apply OutwardRule1bObserverEquivalence.carrierOccurrence_ranked_depth
  exact (input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp cursor.occurrence.2

private theorem cursor_reachable
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    input.UnboundedOfficialSubtree (OfficialCIPNode.root cursor.occurrence.1.root)
      cursor.occurrence.1.address cursor.occurrence.1.node := by
  have derived := (input.mem_localizedOccurrences_iff fuel cursor.occurrence.1).mp
    cursor.occurrence.2
  have rooted := input.declarativeLocalizedOccurrence_as_rootSubtree derived
  obtain ⟨address, eqAddress, reachable⟩ :=
    input.declarativeLocalizedOccurrenceSubtree_unbounded rooted
  simpa [eqAddress] using reachable

private theorem cursor_complete
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel) :
    ∃ residual, cursor.occurrence.1.node.depth + residual =
      input.certified.input.molecule.atomCount + 1 ∧
      MoleculeGraph.OfficialExpansionCompleteWithin input.executableOfficialCIPChildren
        residual cursor.occurrence.1.node := by
  have ranked := cursor_rank_depth input cursor
  have reachable := cursor_reachable input cursor
  let whole := input.executableOfficialExpansionCompleteWithin_root_default
    cursor.occurrence.1.root
  have remaining := input.unboundedOfficialSubtree_complete_of_complete
    (input.certified.input.molecule.atomCount + 1) whole reachable
  have bound := input.unboundedOfficialSubtree_address_length_le_of_complete
    (input.certified.input.molecule.atomCount + 1) whole reachable
  have depthBound : cursor.occurrence.1.node.depth ≤
      input.certified.input.molecule.atomCount + 1 := by
    rw [ranked.2]
    exact bound
  refine ⟨input.certified.input.molecule.atomCount + 1 - cursor.occurrence.1.node.depth,
    Nat.add_sub_of_le depthBound, ?_⟩
  simpa [ranked.2] using remaining

private theorem pair_left_valid
    (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (pair : ActualOutwardSiblingPair input carrierFuel) :
    input.LocalizedRerootCursorValid pair.left := by
  apply input.localizedRerootCursorValid_of_incoming pair.left
  refine ⟨pair.target.occurrence, pair.leftPrevious, pair.leftRoot.symm, ?_, ?_⟩
  · rw [pair.leftAddress]
    simp
  · rw [pair.leftAddress]
    simp

private theorem pair_right_valid
    (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat}
    (pair : ActualOutwardSiblingPair input carrierFuel) :
    input.LocalizedRerootCursorValid pair.right := by
  apply input.localizedRerootCursorValid_of_incoming pair.right
  refine ⟨pair.target.occurrence, pair.rightPrevious, pair.rightRoot.symm, ?_, ?_⟩
  · rw [pair.rightAddress]
    simp
  · rw [pair.rightAddress]
    simp

/-- The revised whole-rule cumulative builder succeeds on both actual outward cursors at its
standard twice-carrier budget, and its actual recursive traces and table matches are recovered.
The only inputs are the actual carrier sibling cursors; no successful-key or trace premise is
assumed. -/
theorem actual_siblings_revised_builds
    (input : CertifiedLocalizedCIPInput)
    {read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel}
    (pair : ActualOutwardSiblingPair input (input.certified.input.molecule.atomCount + 1)) :
    ∃ keyLeft keyRight treeLeft treeRight,
      input.buildRuleMajorCumulativeWithRead? .rule4a read
        (2 * (input.certified.input.molecule.atomCount + 1 + 1)) pair.left = some keyLeft ∧
      input.buildRuleMajorCumulativeWithRead? .rule4a read
        (2 * (input.certified.input.molecule.atomCount + 1 + 1)) pair.right = some keyRight ∧
      treeLeft.source = pair.left ∧ treeRight.source = pair.right ∧
      LocalizedRuleMajorSortTrace input .rule4a read
        (2 * (input.certified.input.molecule.atomCount + 1 + 1)) treeLeft keyLeft ∧
      LocalizedRuleMajorSortTrace input .rule4a read
        (2 * (input.certified.input.molecule.atomCount + 1 + 1)) treeRight keyRight ∧
      LocalizedCumulativeTreeTableMatch .rule4a treeLeft keyLeft ∧
      LocalizedCumulativeTreeTableMatch .rule4a treeRight keyRight := by
  obtain ⟨treeLeft, keyLeft, sourceLeft, builtLeft, traceLeft⟩ :=
    exists_ruleMajorTrace_at_twice input .rule4a read pair.left
      (pair_left_valid input pair)
  obtain ⟨treeRight, keyRight, sourceRight, builtRight, traceRight⟩ :=
    exists_ruleMajorTrace_at_twice input .rule4a read pair.right
      (pair_right_valid input pair)
  exact ⟨keyLeft, keyRight, treeLeft, treeRight, builtLeft, builtRight,
    sourceLeft, sourceRight, traceLeft, traceRight,
    LocalizedRuleMajorSortTrace.fullMatch_of_trace traceLeft |>.tableMatch,
    LocalizedRuleMajorSortTrace.fullMatch_of_trace traceRight |>.tableMatch⟩

/-- Actual outward siblings' official Rule 1b observations compare exactly as the independent
hybrid duplicate-priority observer. Every rank, depth, completion proof, and both successful
observer builds are constructed; the caller supplies only the two actual cursors' common-target
outward address evidence. -/
theorem actual_siblings_official_compare_eq_hybrid
    (input : CertifiedLocalizedCIPInput)
    (pair : ActualOutwardSiblingPair input (input.certified.input.molecule.atomCount + 1)) :
    ∃ n fuel actualLeft hybridLeft actualRight hybridRight,
      pair.left.occurrence.1.node.depth = n ∧
      pair.right.occurrence.1.node.depth = n ∧
      n + fuel = input.certified.input.molecule.atomCount + 1 ∧
      buildOfficialRuleMajorKeyWith rule1bRootDistance input.moleculeGraph
          input.executableOfficialCIPChildren
          fuel pair.left.occurrence.1.node =
        some actualLeft ∧
      buildOfficialRuleMajorKeyWith (hybridDuplicatePriority
          (input.certified.input.molecule.atomCount + 2)) input.moleculeGraph
          input.executableOfficialCIPChildren
          fuel pair.left.occurrence.1.node =
        some hybridLeft ∧
      buildOfficialRuleMajorKeyWith rule1bRootDistance input.moleculeGraph
          input.executableOfficialCIPChildren
          fuel pair.right.occurrence.1.node =
        some actualRight ∧
      buildOfficialRuleMajorKeyWith (hybridDuplicatePriority
          (input.certified.input.molecule.atomCount + 2)) input.moleculeGraph
          input.executableOfficialCIPChildren
          fuel pair.right.occurrence.1.node =
        some hybridRight ∧
      compare actualLeft actualRight = compare hybridLeft hybridRight := by
  have leftRank := cursor_rank_depth input pair.left
  have rightRank := cursor_rank_depth input pair.right
  have leftAddressLength : pair.left.occurrence.1.address.length =
      pair.target.occurrence.1.address.length + 1 := by
    rw [pair.leftAddress]
    simp
  have rightAddressLength : pair.right.occurrence.1.address.length =
      pair.target.occurrence.1.address.length + 1 := by
    rw [pair.rightAddress]
    simp
  have commonDepth : pair.left.occurrence.1.node.depth =
      pair.right.occurrence.1.node.depth := by
    rw [leftRank.2, rightRank.2, leftAddressLength, rightAddressLength]
  let n := pair.left.occurrence.1.node.depth
  have leftDepth : pair.left.occurrence.1.node.depth = n := rfl
  have rightDepth : pair.right.occurrence.1.node.depth = n := commonDepth.symm.trans rfl
  obtain ⟨leftFuel, leftFuelEq, leftComplete⟩ := cursor_complete input pair.left
  obtain ⟨rightFuel, rightFuelEq, rightComplete⟩ := cursor_complete input pair.right
  have fuelsEq : leftFuel = rightFuel := by
    omega
  subst rightFuel
  have sentinelBound : n + leftFuel < input.certified.input.molecule.atomCount + 2 := by
    omega
  obtain ⟨actualLeft, hybridLeft, actualRight, hybridRight, leftBuilt, leftHybridBuilt,
    rightBuilt, rightHybridBuilt, compared, _, _⟩ :=
    outwardArm_compare_eq_hybrid input (input.certified.input.molecule.atomCount + 2)
      leftFuel n pair.left.occurrence.1.node pair.right.occurrence.1.node
      leftRank.1 rightRank.1 leftDepth rightDepth sentinelBound leftComplete rightComplete
  exact ⟨n, leftFuel, actualLeft, hybridLeft, actualRight, hybridRight,
    leftDepth, rightDepth, by omega, leftBuilt, leftHybridBuilt, rightBuilt,
    rightHybridBuilt, compared⟩

/-! ## Revised constitutional tables are the official compiler's -/

private theorem outwardMapM_forall₂ {α β : Type*} (f : α → Option β) :
    ∀ (values : List α) (results : List β), values.mapM f = some results →
      List.Forall₂ (fun value result => f value = some result) values results
  | [], results, computed => by
      simp at computed
      subst results
      exact List.Forall₂.nil
  | value :: values, results, computed => by
      rw [List.mapM_cons] at computed
      cases head : f value with
      | none => simp [head] at computed
      | some result =>
          cases tail : values.mapM f with
          | none => simp [head, tail] at computed
          | some rest =>
              simp [head, tail] at computed
              subst results
              exact List.Forall₂.cons head (outwardMapM_forall₂ f values rest tail)

private theorem pair_left_incoming
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (pair : ActualOutwardSiblingPair input carrierFuel) :
    LocalizedRerootCursorIncomingParent input pair.left := by
  refine ⟨pair.target.occurrence, pair.leftPrevious, pair.leftRoot.symm, ?_, ?_⟩
  · rw [pair.leftAddress]
    simp
  · rw [pair.leftAddress]
    simp

private theorem pair_right_incoming
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (pair : ActualOutwardSiblingPair input carrierFuel) :
    LocalizedRerootCursorIncomingParent input pair.right := by
  refine ⟨pair.target.occurrence, pair.rightPrevious, pair.rightRoot.symm, ?_, ?_⟩
  · rw [pair.rightAddress]
    simp
  · rw [pair.rightAddress]
    simp

/-- An actual child of a cursor that arrived from its carrier parent also arrived from its
carrier parent, namely that cursor. -/
private theorem outwardChild_incoming
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (incoming : LocalizedRerootCursorIncomingParent input cursor)
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    (frame : input.DeclarativeLocalizedRerootChildren cursor children)
    {child : input.LocalizedRerootCursor carrierFuel} (present : child ∈ children) :
    LocalizedRerootCursorIncomingParent input child := by
  have computed := (input.localizedRerootChildren?_eq_some_iff cursor children).mpr frame
  rw [input.localizedRerootChildren?_eq_some_executable cursor] at computed
  have childrenEq : input.executableLocalizedRerootChildren cursor = children :=
    Option.some.inj computed
  have edge : child ∈ input.executableLocalizedRerootChildren cursor := by
    rw [childrenEq]
    exact present
  have valid : input.LocalizedRerootCursorValid cursor :=
    input.localizedRerootCursorValid_of_incoming cursor incoming
  rcases incoming with ⟨previous, previousEq, previousRoot, previousAddress, previousLength⟩
  have parentShorter : previous.1.address.length < cursor.occurrence.1.address.length := by
    omega
  rcases input.outward_edge cursor child valid previous previousEq parentShorter edge with
    ⟨childDropLast, childLength, childRoot, childPrevious, _childValid⟩
  exact ⟨cursor.occurrence, childPrevious, childRoot.symm, childDropLast.symm,
    childLength.symm⟩

/-- The actual frame of a cursor that arrived from its carrier parent carries exactly the
executable official children, with multiplicity. A duplicate leaf has neither. -/
theorem outwardChildren_nodes_perm_executable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (incoming : LocalizedRerootCursorIncomingParent input cursor)
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    (frame : input.DeclarativeLocalizedRerootChildren cursor children) :
    (children.map (fun child => child.occurrence.1.node)).Perm
      (input.executableOfficialCIPChildren cursor.occurrence.1.node) := by
  have nodes : children.map (fun child => child.occurrence.1.node) =
      (input.intendedLocalizedRerootChildFrames cursor).map (fun frame => frame.node) := by
    rw [← frame.1, List.map_map]
    rfl
  rw [nodes]
  by_cases duplicate : cursor.occurrence.1.node.isDuplicateLeaf = true
  · have intendedNil : input.intendedLocalizedRerootChildFrames cursor = [] := by
      simp [intendedLocalizedRerootChildFrames, duplicate]
    have executableNil :
        input.executableOfficialCIPChildren cursor.occurrence.1.node = [] := by
      simp [executableOfficialCIPChildren, duplicate]
    rw [intendedNil, executableNil]
    simp
  · have nonDuplicate : cursor.occurrence.1.node.isDuplicateLeaf = false := by
      cases h : cursor.occurrence.1.node.isDuplicateLeaf
      · rfl
      · exact absurd h duplicate
    rcases incoming with ⟨previous, previousEq, previousRoot, previousAddress, previousLength⟩
    exact input.intendedLocalizedRerootChildFrames_nodes_perm_executable cursor
      ((input.mem_localizedOccurrences_iff carrierFuel cursor.occurrence.1).mp
        cursor.occurrence.2)
      previous previousEq previousRoot previousAddress previousLength nonDuplicate
      (input.localizedOccurrences_remaining_pos_of_atomCount_le enough cursor.occurrence.1
        cursor.occurrence.2)

/-- A terminal derivation and any official build at the same node have one observable. The
official budget is irrelevant: the root observation does not read the completeness flag. -/
private theorem outwardTerminal_observable_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (incoming : LocalizedRerootCursorIncomingParent input cursor)
    {children : List (input.LocalizedRerootCursor carrierFuel)}
    (frame : input.DeclarativeLocalizedRerootChildren cursor children)
    (empty : children = [])
    (officialFuel : Nat) (official : OfficialRuleMajorKey input.Atom)
    (built : input.moleculeGraph.buildOfficialRuleMajorKey input.executableOfficialCIPChildren
      officialFuel cursor.occurrence.1.node = some official) :
    constitutionalObservable
        (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true) =
      constitutionalObservable official := by
  have perm := outwardChildren_nodes_perm_executable input enough cursor incoming frame
  rw [empty, List.map_nil] at perm
  have executableNil : input.executableOfficialCIPChildren cursor.occurrence.1.node = [] :=
    perm.nil_eq.symm
  cases officialFuel with
  | zero =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey] at built
      subst built
      rfl
  | succ officialFuel =>
      simp [MoleculeGraph.buildOfficialRuleMajorKey, executableNil] at built
      subst built
      rfl

private theorem outwardDeclarativeList_observables_eq
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel officialFuel : Nat} :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys officialKeys : List (OfficialRuleMajorKey input.Atom)),
      (∀ cursor ∈ cursors, ∀ (key official : OfficialRuleMajorKey input.Atom),
        input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key →
        input.moleculeGraph.buildOfficialRuleMajorKey input.executableOfficialCIPChildren
          officialFuel cursor.occurrence.1.node = some official →
        constitutionalObservable key = constitutionalObservable official) →
      input.DeclarativeLocalizedRerootRuleMajorKeyList fuel cursors keys →
      List.Forall₂ (fun cursor official =>
        input.moleculeGraph.buildOfficialRuleMajorKey input.executableOfficialCIPChildren
          officialFuel cursor.occurrence.1.node = some official) cursors officialKeys →
      keys.map constitutionalObservable = officialKeys.map constitutionalObservable
  | [], keys, officialKeys, _pointwise, derived, built => by
      cases derived
      cases built
      rfl
  | cursor :: cursors, keys, officialKeys, pointwise, derived, built => by
      cases derived with
      | cons head tail =>
          cases built with
          | cons headBuilt tailBuilt =>
              simp only [List.map_cons]
              rw [pointwise cursor (by simp) _ _ head headBuilt,
                outwardDeclarativeList_observables_eq input cursors _ _
                  (fun child present => pointwise child (by simp [present])) tail tailBuilt]

/-- **Declarative reroot keys read the official compiler's tables.** Let a cursor arrive from its
carrier parent, at a carrier at least the atom count. Then any declarative reroot derivation and
any official executable build at its node that completes the expansion have the same
Rule-1a/1b/2 observable. The two budgets are independent.

At a branch the actual frame nodes are the executable children with multiplicity. Each child
again arrived from its carrier parent and is complete at the smaller official budget. The child
observables therefore form one multiset, and both descending orders read it as the same sequence.
A duplicate leaf is terminal on both sides. -/
theorem outwardDeclarative_constitutional_eq_official
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
      (key : OfficialRuleMajorKey input.Atom) (officialFuel : Nat)
      (official : OfficialRuleMajorKey input.Atom),
      LocalizedRerootCursorIncomingParent input cursor →
      input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key →
      MoleculeGraph.OfficialExpansionCompleteWithin input.executableOfficialCIPChildren
        officialFuel cursor.occurrence.1.node →
      input.moleculeGraph.buildOfficialRuleMajorKey input.executableOfficialCIPChildren
        officialFuel cursor.occurrence.1.node = some official →
      constitutionalObservable key = constitutionalObservable official := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor key officialFuel official incoming derived _complete built
      cases derived with
      | @terminal _ cursor children frame empty =>
          exact outwardTerminal_observable_eq input enough cursor incoming frame empty
            officialFuel official built
  | succ fuel ih =>
      intro cursor key officialFuel official incoming derived complete built
      cases derived with
      | @terminal _ cursor children frame empty =>
          exact outwardTerminal_observable_eq input enough cursor incoming frame empty
            officialFuel official built
      | @branch _ cursor children childKeys sorted frame nonempty childDerivations ranking
          descending =>
          have perm := outwardChildren_nodes_perm_executable input enough cursor incoming frame
          have executableNonnil :
              input.executableOfficialCIPChildren cursor.occurrence.1.node ≠ [] := by
            intro empty
            rw [empty] at perm
            exact nonempty (List.map_eq_nil_iff.mp perm.eq_nil)
          cases officialFuel with
          | zero =>
              have noChildren :
                  input.executableOfficialCIPChildren cursor.occurrence.1.node = [] := by
                simpa [MoleculeGraph.OfficialExpansionCompleteWithin] using complete
              exact absurd noChildren executableNonnil
          | succ officialFuel =>
              have executableNonempty :
                  ¬ (input.executableOfficialCIPChildren
                    cursor.occurrence.1.node).isEmpty = true := by
                rw [List.isEmpty_iff]
                exact executableNonnil
              unfold MoleculeGraph.buildOfficialRuleMajorKey at built
              dsimp only at built
              rw [if_neg executableNonempty] at built
              cases officialChildrenComputed :
                  (input.executableOfficialCIPChildren cursor.occurrence.1.node).mapM
                    (input.moleculeGraph.buildOfficialRuleMajorKey
                      input.executableOfficialCIPChildren officialFuel) with
              | none => simp [officialChildrenComputed] at built
              | some officialChildKeys =>
                  cases officialSortedComputed :
                      OfficialRuleMajorKey.sort? officialChildKeys with
                  | none => simp [officialChildrenComputed, officialSortedComputed] at built
                  | some officialSorted =>
                      simp [officialChildrenComputed, officialSortedComputed] at built
                      subst built
                      obtain ⟨reorderedKeys, reorderedBuilt, reorderedPerm⟩ :=
                        List.perm_comp_forall₂ perm
                          (outwardMapM_forall₂ _ _ _ officialChildrenComputed)
                      have childBuilt : List.Forall₂ (fun child official =>
                          input.moleculeGraph.buildOfficialRuleMajorKey
                            input.executableOfficialCIPChildren officialFuel
                            child.occurrence.1.node = some official) children reorderedKeys :=
                        List.forall₂_map_left_iff.mp reorderedBuilt
                      have childObservables :
                          childKeys.map constitutionalObservable =
                            reorderedKeys.map constitutionalObservable :=
                        outwardDeclarativeList_observables_eq input children childKeys
                          reorderedKeys
                          (fun child present childKey childOfficial childDerived
                              childComputed =>
                            ih child childKey officialFuel childOfficial
                              (outwardChild_incoming input cursor incoming frame present)
                              childDerived
                              (complete child.occurrence.1.node
                                (perm.mem_iff.mp (List.mem_map.mpr ⟨child, present, rfl⟩)))
                              childComputed)
                          childDerivations childBuilt
                      have observedPerm :
                          (sorted.map constitutionalObservable).Perm
                            (officialSorted.map constitutionalObservable) :=
                        (ranking.map constitutionalObservable).trans
                          ((List.Perm.of_eq childObservables).trans
                            ((reorderedPerm.map constitutionalObservable).trans
                              ((OfficialRuleMajorKey.sort?_perm officialChildKeys
                                officialSorted officialSortedComputed).map
                                  constitutionalObservable).symm))
                      exact assembled_constitutional_observable_eq _ _ _
                        (constitutional_observables_eq_of_perm _ _ observedPerm descending
                          (OfficialRuleMajorKey.sort?_descending officialChildKeys
                            officialSorted officialSortedComputed))

/-- **Revised constitutional fields.** A successful revised rule-major build, at any stage,
reader and fuel, at a cursor that arrived from its carrier parent has the observable of the
official executable compiler at the cursor's node, at every official budget that completes the
expansion. The sibling orders of the two keys are not identified. -/
theorem incomingCursor_revised_constitutional_eq_official
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (enough : input.certified.input.molecule.atomCount ≤ carrierFuel)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    {fuel : Nat} {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (incoming : LocalizedRerootCursorIncomingParent input cursor)
    (built : input.buildRuleMajorCumulativeWithRead? stage read fuel cursor = some key)
    {officialFuel : Nat} {official : OfficialRuleMajorKey input.Atom}
    (complete : MoleculeGraph.OfficialExpansionCompleteWithin
      input.executableOfficialCIPChildren officialFuel cursor.occurrence.1.node)
    (officialBuilt : input.moleculeGraph.buildOfficialRuleMajorKey
      input.executableOfficialCIPChildren officialFuel cursor.occurrence.1.node = some official) :
    constitutionalObservable key.constitutional = constitutionalObservable official := by
  obtain ⟨tree, source, trace⟩ :=
    exists_ruleMajorTrace_of_buildWithRead input stage read fuel cursor key built
  have derived :=
    RetainedConstitutionalReaderIndependence.ruleMajorSortTrace_constitutional_declarative
      fuel trace
  rw [source] at derived
  exact outwardDeclarative_constitutional_eq_official input enough fuel cursor
    key.constitutional officialFuel official incoming derived complete officialBuilt

/-- **Actual revised outward Rule 1b comparison.** For two actual outward sibling cursors, any
stage and any label reader, the revised builder succeeds at its standard budget on both cursors.
Its constitutional keys have the observables of the official compiler at one common completing
budget. Their comparison equals the comparison of the independent hybrid duplicate-priority
builds, which also succeed. Each official build and its hybrid build are expansion twins: one
source tree, source-aligned under their own observers, depth- and address-graded, and complete.

The only input is the sibling evidence. Builds, completeness, the official budget, alignment and
every observable equality are derived. The hybrid and actual Rule 1b values are different
numbers; only the comparison outcome is shared. -/
theorem actual_siblings_revised_compare_eq_hybrid
    (input : CertifiedLocalizedCIPInput)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (pair : ActualOutwardSiblingPair input (input.certified.input.molecule.atomCount + 1)) :
    ∃ n fuel keyLeft keyRight actualLeft actualRight hybridLeft hybridRight,
      pair.left.occurrence.1.node.depth = n ∧
      pair.right.occurrence.1.node.depth = n ∧
      n + fuel = input.certified.input.molecule.atomCount + 1 ∧
      input.buildRuleMajorCumulativeWithRead? stage read
        (2 * (input.certified.input.molecule.atomCount + 1 + 1)) pair.left = some keyLeft ∧
      input.buildRuleMajorCumulativeWithRead? stage read
        (2 * (input.certified.input.molecule.atomCount + 1 + 1)) pair.right = some keyRight ∧
      input.moleculeGraph.buildOfficialRuleMajorKey input.executableOfficialCIPChildren
        fuel pair.left.occurrence.1.node = some actualLeft ∧
      input.moleculeGraph.buildOfficialRuleMajorKey input.executableOfficialCIPChildren
        fuel pair.right.occurrence.1.node = some actualRight ∧
      buildOfficialRuleMajorKeyWith (hybridDuplicatePriority
          (input.certified.input.molecule.atomCount + 2)) input.moleculeGraph
          input.executableOfficialCIPChildren
          fuel pair.left.occurrence.1.node =
        some hybridLeft ∧
      buildOfficialRuleMajorKeyWith (hybridDuplicatePriority
          (input.certified.input.molecule.atomCount + 2)) input.moleculeGraph
          input.executableOfficialCIPChildren
          fuel pair.right.occurrence.1.node =
        some hybridRight ∧
      ExpansionTwin input (input.certified.input.molecule.atomCount + 2) fuel n
        actualLeft hybridLeft ∧
      ExpansionTwin input (input.certified.input.molecule.atomCount + 2) fuel n
        actualRight hybridRight ∧
      constitutionalObservable keyLeft.constitutional = constitutionalObservable actualLeft ∧
      constitutionalObservable keyRight.constitutional = constitutionalObservable actualRight ∧
      OfficialRuleMajorKey.compare keyLeft.constitutional keyRight.constitutional =
        OfficialRuleMajorKey.compare hybridLeft hybridRight := by
  have leftRank := cursor_rank_depth input pair.left
  have rightRank := cursor_rank_depth input pair.right
  have leftAddressLength : pair.left.occurrence.1.address.length =
      pair.target.occurrence.1.address.length + 1 := by
    rw [pair.leftAddress]
    simp
  have rightAddressLength : pair.right.occurrence.1.address.length =
      pair.target.occurrence.1.address.length + 1 := by
    rw [pair.rightAddress]
    simp
  have commonDepth : pair.left.occurrence.1.node.depth =
      pair.right.occurrence.1.node.depth := by
    rw [leftRank.2, rightRank.2, leftAddressLength, rightAddressLength]
  obtain ⟨leftFuel, leftFuelEq, leftComplete⟩ := cursor_complete input pair.left
  obtain ⟨rightFuel, rightFuelEq, rightComplete⟩ := cursor_complete input pair.right
  have fuelsEq : leftFuel = rightFuel := by
    omega
  subst rightFuel
  have sentinelBound : pair.left.occurrence.1.node.depth + leftFuel <
      input.certified.input.molecule.atomCount + 2 := by
    omega
  obtain ⟨actualLeft, hybridLeft, actualRight, hybridRight, leftBuilt, leftHybridBuilt,
    rightBuilt, rightHybridBuilt, compared, leftTwin, rightTwin⟩ :=
    outwardArm_compare_eq_hybrid input (input.certified.input.molecule.atomCount + 2)
      leftFuel pair.left.occurrence.1.node.depth pair.left.occurrence.1.node
      pair.right.occurrence.1.node leftRank.1 rightRank.1 rfl commonDepth.symm sentinelBound
      leftComplete rightComplete
  have leftOfficial : input.moleculeGraph.buildOfficialRuleMajorKey
      input.executableOfficialCIPChildren leftFuel pair.left.occurrence.1.node =
        some actualLeft :=
    (MoleculeGraph.buildOfficialRuleMajorKey_eq_rule1bRootDistance input.moleculeGraph
      input.executableOfficialCIPChildren leftFuel pair.left.occurrence.1.node).trans leftBuilt
  have rightOfficial : input.moleculeGraph.buildOfficialRuleMajorKey
      input.executableOfficialCIPChildren leftFuel pair.right.occurrence.1.node =
        some actualRight :=
    (MoleculeGraph.buildOfficialRuleMajorKey_eq_rule1bRootDistance input.moleculeGraph
      input.executableOfficialCIPChildren leftFuel pair.right.occurrence.1.node).trans rightBuilt
  obtain ⟨_, keyLeft, _, builtLeft, _⟩ :=
    exists_ruleMajorTrace_at_twice input stage read pair.left (pair_left_valid input pair)
  obtain ⟨_, keyRight, _, builtRight, _⟩ :=
    exists_ruleMajorTrace_at_twice input stage read pair.right (pair_right_valid input pair)
  have enough : input.certified.input.molecule.atomCount ≤
      input.certified.input.molecule.atomCount + 1 :=
    Nat.le_succ _
  have leftObservable :=
    incomingCursor_revised_constitutional_eq_official input enough stage read
      (pair_left_incoming input pair) builtLeft leftComplete leftOfficial
  have rightObservable :=
    incomingCursor_revised_constitutional_eq_official input enough stage read
      (pair_right_incoming input pair) builtRight rightComplete rightOfficial
  refine ⟨pair.left.occurrence.1.node.depth, leftFuel, keyLeft, keyRight, actualLeft,
    actualRight, hybridLeft, hybridRight, rfl, commonDepth.symm, leftFuelEq, builtLeft,
    builtRight, leftOfficial, rightOfficial, leftHybridBuilt, rightHybridBuilt, leftTwin,
    rightTwin, leftObservable, rightObservable, ?_⟩
  exact (ruleMajor_compare_congr _ _ _ _ leftObservable rightObservable).trans compared

/-! ## Sibling evidence from actual frame children -/

private theorem outwardChild_slot
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (child : input.LocalizedRerootCursor carrierFuel)
    (present : child ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (deeper : target.1.address.length < child.occurrence.1.address.length) :
    ∃ slot, child.occurrence.1.address = target.1.address ++ [slot] := by
  have intended : child.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames
      ({ occurrence := target, previous? := none } :
        input.LocalizedRerootCursor carrierFuel) := by
    rw [← input.executableLocalizedRerootChildren_map]
    exact List.mem_map.mpr ⟨child, present, rfl⟩
  have neighbor := input.mem_localizedRerootNeighborFrames_of_mem_intended _
    child.occurrence.1 intended
  rcases ((input.mem_localizedRerootNeighborFrames_iff target.1 child.occurrence.1).mp
      neighbor).2 with ⟨_sameRoot, ⟨shorter, _⟩ | ⟨_longer, parentAddress⟩⟩
  · omega
  · have nonempty : child.occurrence.1.address ≠ [] := by
      intro empty
      rw [empty] at deeper
      simp at deeper
    refine ⟨child.occurrence.1.address.getLast nonempty, ?_⟩
    rw [parentAddress]
    exact (List.dropLast_append_getLast nonempty).symm

/-- Two strictly deeper executable children of a target-start cursor are actual outward siblings.
The target's carrier parent is its only shorter neighbour, so depth excludes it. -/
theorem exists_actualOutwardSiblingPair_of_children
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (left right : input.LocalizedRerootCursor carrierFuel)
    (leftChild : left ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (rightChild : right ∈ input.executableLocalizedRerootChildren
      { occurrence := target, previous? := none })
    (leftDeeper : target.1.address.length < left.occurrence.1.address.length)
    (rightDeeper : target.1.address.length < right.occurrence.1.address.length) :
    ∃ pair : ActualOutwardSiblingPair input carrierFuel,
      pair.target = { occurrence := target, previous? := none } ∧
        pair.left = left ∧ pair.right = right := by
  obtain ⟨leftSlot, leftAddress⟩ := outwardChild_slot input target left leftChild leftDeeper
  obtain ⟨rightSlot, rightAddress⟩ :=
    outwardChild_slot input target right rightChild rightDeeper
  exact ⟨{ target := { occurrence := target, previous? := none }
           left := left
           right := right
           leftPrevious := input.executableLocalizedRerootChildren_previous _ left leftChild
           rightPrevious := input.executableLocalizedRerootChildren_previous _ right rightChild
           leftRoot := input.localizedRerootChildren_root_eq _ left _
             (input.executableLocalizedRerootChildren_declarative _) leftChild
           rightRoot := input.localizedRerootChildren_root_eq _ right _
             (input.executableLocalizedRerootChildren_declarative _) rightChild
           leftSlot := leftSlot
           rightSlot := rightSlot
           leftAddress := leftAddress
           rightAddress := rightAddress }, rfl, rfl, rfl⟩

end LocalizedActualOutwardRule1bEquivalence
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair
assert_kernel_only TetraStereo.OneCenter.LocalizedActualOutwardRule1bEquivalence.actual_siblings_revised_builds
assert_kernel_only TetraStereo.OneCenter.LocalizedActualOutwardRule1bEquivalence.actual_siblings_official_compare_eq_hybrid
assert_kernel_only TetraStereo.OneCenter.LocalizedActualOutwardRule1bEquivalence.outwardChildren_nodes_perm_executable
assert_kernel_only TetraStereo.OneCenter.LocalizedActualOutwardRule1bEquivalence.outwardDeclarative_constitutional_eq_official
assert_kernel_only TetraStereo.OneCenter.LocalizedActualOutwardRule1bEquivalence.incomingCursor_revised_constitutional_eq_official
assert_kernel_only TetraStereo.OneCenter.LocalizedActualOutwardRule1bEquivalence.actual_siblings_revised_compare_eq_hybrid
assert_kernel_only TetraStereo.OneCenter.LocalizedActualOutwardRule1bEquivalence.exists_actualOutwardSiblingPair_of_children
