import TetraStereo.OneCenter.LocalizedMonocyclicDoubleBondPerception
import TetraStereo.OneCenter.LocalizedParentFrameHistory
import TetraStereo.OneCenter.LocalizedCarrierRealCenterActiveSimple
import TetraStereo.OneCenter.LocalizedRule3CumulatedChain
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.OneCenter.LocalizedHistoryInducedCycle
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Actual monocyclic fallback exclusion for eager required-monocycle Rule 3

The localized Rule-3 axis classifier reports a `ringClosure` entry when a physical order-two
continuation of the axis cursor is a zero-copy ring duplicate.  This module extracts, from an
*actual* carrier occurrence `O` and an actual declarative `ringClosure` entry, the concrete
cycle obstruction:

* `O` is a non-root carrier occurrence, so it has an actual carrier parent `P` whose stored
  history is duplicate-free, begins at `O`'s parent atom `initial.left`, and is a positive-bond
  path;
* the ring-closure cursor is a carrier-tree neighbour of `P`; it cannot be `P`'s parent (carrier
  parents have real provenance, ring duplicates do not), so it is an executable child of `P`;
* that child is the zero-copy extension of `P` by an atom `X` already stored in `P.history`,
  with a physical order-two bond `initial.left - X`;
* consequently the history prefix ending at `X`, closed by the `initial.left - X` double bond,
  is a bonded duplicate-free list with a nonconsecutive closing pair, so the generic chordless
  reduction `exists_inducedSimpleCycle_of_bonded_list` produces a certified simple cycle vertex
  set contained in `P.history` and in the covalent component of `initial.left`, avoiding the
  fresh atom `initial.right`.

Any ordinary monocyclic double-bond carrier for the oriented bond `initial.left, initial.right`
must, by the uniqueness clause of `DeclarativeLocalizedMonocyclicDoubleBond`, coincide with that
vertex set, and would therefore have to contain the fresh atom `initial.right`.  This is
impossible, so exact monocycle perception returns `none`.
-/

namespace CertifiedLocalizedCIPInput

/-! ## Executable children require an observed current atom -/

/-- A node with an executable official child always has an observed current atom: the child
enumeration is built from the current atom's neighbour copies, and a node without a current atom
has no children at all. -/
theorem exists_current?_of_mem_executableOfficialCIPChildren
    (input : CertifiedLocalizedCIPInput)
    {node child : OfficialCIPNode input.Atom}
    (present : child ∈ input.executableOfficialCIPChildren node) :
    ∃ current, node.current? = some current := by
  unfold executableOfficialCIPChildren at present
  split at present
  · simp at present
  · unfold executableOfficialChildCopies at present
    cases observed : node.current? with
    | none =>
        rw [observed] at present
        simp at present
    | some current => exact ⟨current, rfl⟩

/-! ## Histories of derived occurrences are positive-bond paths -/

/-- The stored history of a derived occurrence is a positive-bond chain and starts at the node's
current atom, provided the subtree root has both properties.  Every official `extend` step
prepends the new current atom, and the new edge is a positive molecular bond. -/
theorem DeclarativeLocalizedOccurrenceSubtree.node_history_chain_and_head
    (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {path : List Nat} {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrenceSubtree root path fuel node occurrence) :
    node.history.head? = node.current? →
      node.history.IsChain (fun a b => input.moleculeGraph.Adj a b) →
      occurrence.node.history.IsChain (fun a b => input.moleculeGraph.Adj a b) ∧
        occurrence.node.history.head? = occurrence.node.current? := by
  induction derived with
  | subtreeRoot path fuel node => intro head chain; exact ⟨chain, head⟩
  | @subtreeDescendant path fuel node child slot occurrence childAtSlot below ih =>
      intro parentHead parentChain
      obtain ⟨next, copyIndex, childExtend⟩ :=
        input.mem_executableOfficialCIPChildren_extend node child
          (List.fst_mem_of_mem_zipIdx childAtSlot)
      obtain ⟨parentAtom, parentCurrent⟩ :=
        input.exists_current?_of_mem_executableOfficialCIPChildren
          (List.fst_mem_of_mem_zipIdx childAtSlot)
      have childCurrent : child.current? = some next := by
        rw [childExtend]
        rfl
      have adjacent : input.moleculeGraph.Adj parentAtom next :=
        input.adj_of_mem_executableOfficialCIPChildren node child parentAtom next
          parentCurrent childCurrent (List.fst_mem_of_mem_zipIdx childAtSlot)
      have childHead : child.history.head? = child.current? := by
        rw [childExtend, OfficialCIPNode.extend_history]
        simp
      have childChain : child.history.IsChain (fun a b => input.moleculeGraph.Adj a b) := by
        rw [childExtend, OfficialCIPNode.extend_history]
        refine List.IsChain.cons parentChain ?_
        intro y hy
        have headSome : node.history.head? = some y := hy
        rw [parentHead, parentCurrent] at headSome
        have yEq : parentAtom = y := Option.some.inj headSome
        rw [← yEq]
        exact (input.moleculeGraph.adj_symm).mpr adjacent
      exact ih childHead childChain

/-- Every molecule-wide carrier occurrence stores a positive-bond chain as its history. -/
theorem declarativeLocalizedOccurrence_node_history_chain
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {occurrence : input.LocalizedCIPOccurrenceFrame}
    (derived : input.DeclarativeLocalizedOccurrence fuel occurrence) :
    occurrence.node.history.IsChain (fun a b => input.moleculeGraph.Adj a b) := by
  have rooted := input.declarativeLocalizedOccurrence_as_rootSubtree derived
  exact (DeclarativeLocalizedOccurrenceSubtree.node_history_chain_and_head input rooted
    (by simp [OfficialCIPNode.root]) (by simp [OfficialCIPNode.root])).1

/-- Every atom stored along a bonded history headed by `root` is reachable from `root` in the
positive-bond component. -/
private theorem reachable_of_history_chain_aux
    (input : CertifiedLocalizedCIPInput) :
    ∀ (atoms : List input.Atom) (root : input.Atom),
      atoms.head? = some root →
        atoms.IsChain (fun a b => input.moleculeGraph.Adj a b) →
          ∀ atom, atom ∈ atoms →
            input.moleculeGraph.underlyingSimpleGraph.Reachable root atom := by
  intro atoms
  induction atoms with
  | nil =>
      intro root head
      simp at head
  | cons a l ih =>
      intro root head chain atom hatom
      have haRoot : a = root := by simpa using head
      rw [← haRoot]
      rw [List.mem_cons] at hatom
      rcases hatom with hEq | hatom
      · rw [hEq]
      · cases l with
        | nil => simp at hatom
        | cons b rest =>
            have relation : input.moleculeGraph.Adj a b := chain.rel_head
            have tailChain : (b :: rest).IsChain
                (fun x y => input.moleculeGraph.Adj x y) := chain.tail
            exact SimpleGraph.Reachable.trans (SimpleGraph.Adj.reachable relation)
              (ih b rfl tailChain atom hatom)

theorem reachable_of_history_chain
    (input : CertifiedLocalizedCIPInput) {atoms : List input.Atom} {root : input.Atom}
    (head : atoms.head? = some root)
    (chain : atoms.IsChain (fun a b => input.moleculeGraph.Adj a b)) :
    ∀ atom, atom ∈ atoms →
      input.moleculeGraph.underlyingSimpleGraph.Reachable root atom :=
  reachable_of_history_chain_aux input atoms root head chain

/-! ## The ring-closure cursor is an executable outward child of the parent occurrence -/

/-- A ring-closure continuation of a cursor is a tree neighbour of the cursor occurrence.  The
declarative continuation frame lists exactly the intended reroot children, and every intended
child is a carrier neighbour in the uncut zipper frame. -/
theorem ringClosure_carrierTreeAdjacent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {cursor closure : input.LocalizedRerootCursor carrierFuel}
    (derived : input.DeclarativeLocalizedRule3AxisTopology cursor (.ringClosure closure)) :
    input.LocalizedCarrierTreeAdjacent closure.occurrence.1 cursor.occurrence.1 := by
  cases derived with
  | ringClosure frame ring =>
      rcases frame with ⟨children, computed, exactChildren, membership⟩
      have hmem : closure ∈ children := ((membership closure).mp (by simp)).1
      have mapped : closure.occurrence.1 ∈ children.map (fun child => child.occurrence.1) :=
        List.mem_map.mpr ⟨closure, hmem, rfl⟩
      have intended : closure.occurrence.1 ∈ input.intendedLocalizedRerootChildFrames cursor := by
        rw [← exactChildren.1]
        exact mapped
      have neighbor : closure.occurrence.1 ∈
          input.localizedRerootNeighborFrames (fuel := carrierFuel) cursor.occurrence.1 :=
        input.mem_localizedRerootNeighborFrames_of_mem_intended cursor _ intended
      exact (input.mem_localizedRerootNeighborFrames_iff cursor.occurrence.1 _).mp neighbor |>.2

/-- The physical endpoint occurrence of a declarative Rule-3 endpoint frame is never the root
occurrence: its node has a stored parent atom, while the root node has none. -/
theorem ringClosure_occurrence_nonroot
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {O : input.LocalizedCIPOccurrence carrierFuel}
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    (topology : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial) :
    O.1.address ≠ [] := by
  intro hnil
  have derived := (input.mem_localizedOccurrences_iff carrierFuel O.1).mp O.2
  have rootFrame := input.declarativeLocalizedOccurrence_eq_root_of_address_nil derived hnil
  have parentSome := topology.2.2.1
  rw [rootFrame] at parentSome
  simp [OfficialCIPNode.root, OfficialCIPNode.parent?] at parentSome

/-- The left endpoint cursor occurrence of a declarative Rule-3 endpoint frame is exactly the
actual carrier parent of the endpoint occurrence.  The certified carrier-parent list of a
non-root occurrence is the singleton of its actual parent. -/
theorem ringClosure_leftCursor_val_eq_parent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {O : input.LocalizedCIPOccurrence carrierFuel}
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    (topology : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (certificate : input.LocalizedParentFrameHistory O) :
    initial.leftCursor.occurrence.1 = certificate.parent.1 := by
  have mem : initial.leftCursor.occurrence.1 ∈
      input.localizedCarrierParentFrames (fuel := carrierFuel) O.1 := topology.2.2.2.2.1
  have singleton := certificate.carrierParentFrames_eq_singleton input
  have memSingleton : initial.leftCursor.occurrence.1 ∈ [certificate.parent.1] := by
    rw [← singleton]
    exact mem
  simpa using memSingleton

/-! ## The ring-closure child is a zero-copy extension by a stored history atom -/

/-- **Ring-closure child extraction.**  The closure cursor is a neighbour of the parent occurrence.
If it were the parent of `P`, it would be the unique carrier parent of `P` and would carry real
provenance, contradicting its ring-duplicate provenance.  Hence it is an executable outward child
of `P`, and the physical continuation identifies it with `P.extend X 0` for an atom `X` that is
already stored in `P.history`, joined to `initial.left` by an order-two bond and different from
`initial.left`. -/
theorem ringClosure_child_extension
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {O : input.LocalizedCIPOccurrence carrierFuel}
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    (certificate : input.LocalizedParentFrameHistory O)
    (leftEq : initial.leftCursor.occurrence.1 = certificate.parent.1)
    (topology : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (adjacent : input.LocalizedCarrierTreeAdjacent
      closure.occurrence.1 initial.leftCursor.occurrence.1)
    (continuation : input.LocalizedRule3AxisPhysicalContinuation initial.leftCursor closure)
    (ringProv : ∃ distance, closure.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance) :
    ∃ X,
      closure.occurrence.1.node = certificate.parent.1.node.extend X 0 ∧
      certificate.parent.1.node.parent? ≠ some X ∧
      X ∈ certificate.parent.1.node.history ∧
      input.moleculeGraph.bond initial.left X = 2 ∧
      X ≠ initial.left := by
  have adjP : input.LocalizedCarrierTreeAdjacent
      closure.occurrence.1 certificate.parent.1 := by
    simpa [leftEq] using adjacent
  rcases adjP with ⟨sameRoot, hdir⟩
  rcases hdir with hparent | houtward
  · -- The closure cursor is the carrier parent of `P`: impossible for a ring duplicate.
    obtain ⟨hLen, hAddr⟩ := hparent
    have pNonroot : certificate.parent.1.address ≠ [] := by
      intro hnil
      rw [hnil] at hLen
      simp at hLen
    have closureInParents : closure.occurrence.1 ∈
        input.localizedCarrierParentFrames (fuel := carrierFuel) certificate.parent.1 := by
      rw [localizedCarrierParentFrames, List.mem_filter]
      refine ⟨closure.occurrence.2, ?_⟩
      simp only [Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨sameRoot, hLen⟩, hAddr⟩
    obtain ⟨parentCertificate⟩ :=
      input.exists_localizedParentFrameHistory certificate.parent pNonroot
    have memSingleton : closure.occurrence.1 ∈ [parentCertificate.parent.1] := by
      rw [← parentCertificate.carrierParentFrames_eq_singleton input]
      exact closureInParents
    have closureEq : closure.occurrence.1 = parentCertificate.parent.1 := by
      simpa using memSingleton
    obtain ⟨distance, ringEq⟩ := ringProv
    have realProv : closure.occurrence.1.node.provenance =
        OfficialCIPNodeProvenance.realAtom := by
      rw [closureEq]
      exact parentCertificate.parent_provenance input
    rw [realProv] at ringEq
    exact (by cases ringEq)
  · -- Outward: the closure cursor is an executable child of `P`.
    obtain ⟨hLen, hAddr⟩ := houtward
    have closureNonroot : closure.occurrence.1.address ≠ [] := by
      intro hnil
      rw [hnil] at hLen
      simp at hLen
    have addressForm : closure.occurrence.1.address =
        certificate.parent.1.address ++
          [closure.occurrence.1.address.getLast closureNonroot] := by
      have hlast := List.dropLast_append_getLast closureNonroot
      rw [← hAddr] at hlast
      exact hlast.symm
    obtain ⟨child, childAtSlot, closureFrame⟩ :=
      input.declarativeLocalizedOccurrence_immediate_child
        ((input.mem_localizedOccurrences_iff carrierFuel certificate.parent.1).mp
          certificate.parent.2)
        ((input.mem_localizedOccurrences_iff carrierFuel closure.occurrence.1).mp
          closure.occurrence.2)
        sameRoot (closure.occurrence.1.address.getLast closureNonroot) addressForm
    have closureNode : closure.occurrence.1.node = child := by
      rw [closureFrame]
    have childPresent : child ∈ input.executableOfficialCIPChildren certificate.parent.1.node :=
      List.fst_mem_of_mem_zipIdx childAtSlot
    obtain ⟨distance, ringEq⟩ := ringProv
    have childRing : child.provenance = OfficialCIPNodeProvenance.ringDuplicate distance := by
      rw [← closureNode]
      exact ringEq
    obtain ⟨X, childExtend, notParent⟩ :=
      input.eq_extend_zero_and_not_parent_of_mem_executableOfficialCIPChildren
        certificate.parent.1.node child childPresent (Or.inr ⟨distance, childRing⟩)
    have closureCurrent : closure.occurrence.1.node.current? = some X := by
      rw [closureNode, childExtend]
      rfl
    have parentCurrent : certificate.parent.1.node.current? = some initial.left := by
      rw [← leftEq]
      exact topology.2.2.2.2.2.1
    have cursorCurrent : initial.leftCursor.occurrence.1.node.current? = some initial.left := by
      rw [leftEq]
      exact parentCurrent
    have bondEq : input.moleculeGraph.bond initial.left X = 2 := by
      have hcont := continuation.2.2
      simpa only [cursorCurrent, closureCurrent] using hcont
    have provenanceAt : certificate.parent.1.node.childProvenance X 0 =
        OfficialCIPNodeProvenance.ringDuplicate distance := by
      have := childRing
      rw [childExtend, OfficialCIPNode.extend_provenance] at this
      exact this
    have Xmem : X ∈ certificate.parent.1.node.history := by
      by_contra hnot
      have real := OfficialCIPNode.childProvenance_real certificate.parent.1.node X hnot
      rw [real] at provenanceAt
      cases provenanceAt
    have Xne : X ≠ initial.left := by
      intro hX
      have hb : (2 : ℕ) = 0 := by
        rw [← bondEq, hX]
        exact input.moleculeGraph.bond_self initial.left
      omega
    exact ⟨X, closureNode.trans childExtend, notParent, Xmem, bondEq, Xne⟩

/-! ## The induced cycle avoiding the fresh atom -/

/-- **Cycle extraction.**  From the actual ring-closure child data, a certified simple cycle
vertex set exists inside the parent history, inside the covalent component of `initial.left`, and
avoiding the fresh atom `initial.right`. -/
theorem ringClosure_cycle_avoiding_fresh
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {O : input.LocalizedCIPOccurrence carrierFuel}
    {initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel}
    {closure : input.LocalizedRerootCursor carrierFuel}
    (certificate : input.LocalizedParentFrameHistory O)
    (leftEq : initial.leftCursor.occurrence.1 = certificate.parent.1)
    (topology : input.DeclarativeLocalizedRule3PhysicalEndpointCursorFrame O initial)
    (adjacent : input.LocalizedCarrierTreeAdjacent
      closure.occurrence.1 initial.leftCursor.occurrence.1)
    (continuation : input.LocalizedRule3AxisPhysicalContinuation initial.leftCursor closure)
    (ringProv : ∃ distance, closure.occurrence.1.node.provenance =
      OfficialCIPNodeProvenance.ringDuplicate distance) :
    ∃ cycle : Finset input.Atom,
      cycle ⊆ certificate.parent.1.node.history.toFinset ∧
        cycle ⊆ input.localizedCovalentComponentAtoms initial.left ∧
          input.DeclarativeLocalizedSimpleCycleVertexSet cycle ∧
            initial.right ∉ cycle := by
  obtain ⟨X, closureNode, notParent, Xmem, bondEq, Xne⟩ :=
    ringClosure_child_extension input certificate leftEq topology adjacent continuation ringProv
  have parentDerived :=
    (input.mem_localizedOccurrences_iff carrierFuel certificate.parent.1).mp certificate.parent.2
  have parentNodup := certificate.parent_history_nodup input
  have parentChain := input.declarativeLocalizedOccurrence_node_history_chain parentDerived
  have parentHeadEq :=
    input.declarativeLocalizedOccurrence_node_history_head_eq_current parentDerived
  have parentCurrent : certificate.parent.1.node.current? = some initial.left := by
    rw [← leftEq]
    exact topology.2.2.2.2.2.1
  have parentHead : certificate.parent.1.node.history.head? = some initial.left := by
    rw [parentHeadEq]
    exact parentCurrent
  -- The fresh atom of the endpoint occurrence is absent from the parent history.
  have active := input.localizedCIPOccurrence_activeSimple_of_provenance_real O topology.1
  have freshRight : initial.right ∉ certificate.parent.1.node.history := by
    have nodupHistory := active.2
    rw [certificate.history_eq] at nodupHistory
    have rightEq : initial.right = certificate.current :=
      Option.some.inj (topology.2.1.symm.trans certificate.current_eq)
    rw [rightEq]
    exact (List.nodup_cons.mp nodupHistory).1
  -- Position of the stored closing atom.
  obtain ⟨Xidx, hXidxLt, hXidxEq⟩ := List.mem_iff_getElem.mp Xmem
  have hpos : 0 < certificate.parent.1.node.history.length :=
    List.length_pos_iff.mpr (List.ne_nil_of_mem Xmem)
  have historyHead? : certificate.parent.1.node.history[0]? = some initial.left := by
    rw [← List.head?_eq_getElem?]
    exact parentHead
  have historyHead : ∀ (h : 0 < certificate.parent.1.node.history.length),
      certificate.parent.1.node.history[0]'h = initial.left := by
    intro h
    obtain ⟨h', he⟩ := List.getElem?_eq_some_iff.mp historyHead?
    simpa using he
  have historyGet : ∀ (h : Xidx < certificate.parent.1.node.history.length),
      certificate.parent.1.node.history[Xidx]'h = X := by
    intro h
    simpa using hXidxEq
  have XidxZero : Xidx ≠ 0 := by
    intro hzero
    subst hzero
    exact Xne (hXidxEq.symm.trans (historyHead _))
  have XidxOpt : certificate.parent.1.node.history[Xidx]? = some X :=
    List.getElem?_eq_some_iff.mpr ⟨hXidxLt, hXidxEq⟩
  have XidxOne : Xidx ≠ 1 := by
    intro hone
    apply notParent
    rw [hone] at XidxOpt
    obtain ⟨tail, htail⟩ := List.head?_eq_some_iff.mp parentHead
    have hsome : (initial.left :: tail)[1]? = some X := by
      simpa [htail] using XidxOpt
    cases tail with
    | nil => simp at hsome
    | cons second rest =>
        have hsecond : second = X := by
          have hsome' : some second = some X := by simpa using hsome
          exact Option.some.inj hsome'
        simp [OfficialCIPNode.parent?, htail, hsecond]
  have XidxTwo : 2 ≤ Xidx := by omega
  -- The history prefix ending at the closing atom.
  set vertices : List input.Atom :=
    certificate.parent.1.node.history.take (Xidx + 1) with hVdef
  have hVLen : vertices.length = Xidx + 1 := by
    rw [hVdef, List.length_take, Nat.min_eq_left]
    omega
  have hVnodup : vertices.Nodup :=
    (List.take_sublist (Xidx + 1) certificate.parent.1.node.history).nodup parentNodup
  have hVchain : vertices.IsChain (fun a b => input.moleculeGraph.Adj a b) := by
    rw [hVdef]
    exact parentChain.take (Xidx + 1)
  have hzeroV : 0 < vertices.length := by omega
  have hkV : Xidx < vertices.length := by omega
  have hgetZero : vertices.get ⟨0, hzeroV⟩ = initial.left := by
    show (certificate.parent.1.node.history.take (Xidx + 1)).get
      ⟨0, hzeroV⟩ = initial.left
    rw [List.get_eq_getElem]
    simp only [List.getElem_take]
    exact historyHead _
  have hgetLast : vertices.get ⟨Xidx, hkV⟩ = X := by
    show (certificate.parent.1.node.history.take (Xidx + 1)).get
      ⟨Xidx, hkV⟩ = X
    rw [List.get_eq_getElem]
    simp only [List.getElem_take]
    exact historyGet _
  have hbondAdj : input.moleculeGraph.Adj initial.left X := by
    show 0 < input.moleculeGraph.bond initial.left X
    rw [bondEq]
    norm_num
  have hclosing : ∃ i j : Fin vertices.length,
      i.val + 2 ≤ j.val ∧
        input.moleculeGraph.Adj (vertices.get i) (vertices.get j) := by
    refine ⟨⟨0, hzeroV⟩, ⟨Xidx, hkV⟩, ?_, ?_⟩
    · simpa using XidxTwo
    · rw [hgetZero, hgetLast]
      exact hbondAdj
  obtain ⟨cycle, hcycleSubV, hcycle⟩ :=
    input.exists_inducedSimpleCycle_of_bonded_list vertices hVnodup hVchain hclosing
  have hcycleHistory : cycle ⊆ certificate.parent.1.node.history.toFinset := by
    intro atom hatom
    have hatomV : atom ∈ vertices := List.mem_toFinset.mp (hcycleSubV hatom)
    rw [hVdef] at hatomV
    exact List.mem_toFinset.mpr
      ((List.take_sublist (Xidx + 1) certificate.parent.1.node.history).subset hatomV)
  have hreach := reachable_of_history_chain input parentHead parentChain
  have hcycleComponent : cycle ⊆ input.localizedCovalentComponentAtoms initial.left := by
    intro atom hatom
    rw [input.mem_localizedCovalentComponentAtoms_iff]
    exact hreach atom (List.mem_toFinset.mp (hcycleHistory hatom))
  have hfresh : initial.right ∉ cycle := by
    intro hmem
    exact freshRight (List.mem_toFinset.mp (hcycleHistory hmem))
  exact ⟨cycle, hcycleHistory, hcycleComponent, hcycle, hfresh⟩

/-! ## Actual Rule-3 ring-closure entries exclude monocyclic perception -/

/-- **Main theorem.**  For an actual carrier occurrence `O` and an actual declarative Rule-3
cumulated-axis entry whose topology is a ring closure of the physical endpoint cursor, exact
ordinary-monocycle perception at the endpoint double bond `initial.left, initial.right` returns
`none`.

The extracted history cycle proves that the component contains a simple cycle avoiding the fresh
atom `initial.right`.  The uniqueness clause of `DeclarativeLocalizedMonocyclicDoubleBond` forces
every perceived carrier to be that cycle, while the carrier must also contain `initial.right`.
No pair-frame totality or exact pair-frame support assumption is used. -/
theorem localizedMonocyclicDoubleBondAt?_eq_none_of_declarativeRingClosure
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (O : input.LocalizedCIPOccurrence carrierFuel)
    (initial : input.LocalizedRule3PhysicalEndpointCursorFrame carrierFuel)
    (closure : input.LocalizedRerootCursor carrierFuel)
    (entry : input.DeclarativeLocalizedRule3CumulatedAxisEntry O (.ringClosure initial closure)) :
    input.localizedMonocyclicDoubleBondAt? initial.left initial.right = none := by
  cases entry with
  | ringClosure topology closureTopology =>
      have physical :=
        DeclarativeLocalizedRule3AxisTopology.ringClosure_physical input closureTopology
      have adjacent := ringClosure_carrierTreeAdjacent input closureTopology
      have nonroot := ringClosure_occurrence_nonroot input topology
      obtain ⟨certificate⟩ := input.exists_localizedParentFrameHistory O nonroot
      have leftEq := ringClosure_leftCursor_val_eq_parent input topology certificate
      obtain ⟨cycle, _hcycleHistory, hcycleComponent, hcycle, hfresh⟩ :=
        ringClosure_cycle_avoiding_fresh input certificate leftEq topology adjacent
          physical.1 physical.2
      rw [input.localizedMonocyclicDoubleBondAt?_eq_none_iff]
      intro carrier derived
      have unique := derived.2.2.2.2.2.1 cycle hcycle hcycleComponent
      have rightIn : initial.right ∈ carrier.ring := derived.2.2.1
      rw [← unique] at rightIn
      exact hfresh rightIn

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.exists_current?_of_mem_executableOfficialCIPChildren
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.DeclarativeLocalizedOccurrenceSubtree.node_history_chain_and_head
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.declarativeLocalizedOccurrence_node_history_chain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.reachable_of_history_chain
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ringClosure_carrierTreeAdjacent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ringClosure_occurrence_nonroot
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ringClosure_leftCursor_val_eq_parent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ringClosure_child_extension
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.ringClosure_cycle_avoiding_fresh
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedMonocyclicDoubleBondAt?_eq_none_of_declarativeRingClosure
