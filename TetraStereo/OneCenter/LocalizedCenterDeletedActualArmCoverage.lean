









































import TetraStereo.OneCenter.LocalizedCenterDeletedTreeRingReconstruction
import TetraStereo.OneCenter.LocalizedOutwardDecoratedSourceFaithfulness
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace LocalizedCenterDeletedActualArmCoverage

open CertifiedLocalizedCIPInput

/-! ## Generic list and walk helpers -/

section Generic

variable {X : Type*}

/-- The head of a list is one of its elements. -/
theorem mem_of_head?_eq_some {l : List X} {a : X} (h : l.head? = some a) : a ∈ l :=
  List.mem_of_mem_head? (by rw [h]; simp)

/-- The last element of a list is one of its elements. -/
theorem mem_of_getLast?_eq_some {l : List X} {a : X} (h : l.getLast? = some a) : a ∈ l :=
  List.mem_of_mem_getLast? (by rw [h]; simp)

/-- A chain with observed head and last vertices is exactly the support of an actual walk between
them.  The walk is built directly from the chain, so its support is the chain itself. -/
theorem exists_walk_of_isChain {G : SimpleGraph X} {l : List X} {a b : X}
    (hhead : l.head? = some a) (hlast : l.getLast? = some b)
    (hchain : l.IsChain G.Adj) : ∃ w : G.Walk a b, w.support = l := by
  induction l generalizing a with
  | nil => simp at hhead
  | cons x rest ih =>
      cases rest with
      | nil =>
          simp only [List.head?_cons, Option.some.injEq] at hhead
          rw [List.getLast?_singleton, Option.some.injEq] at hlast
          subst a
          subst b
          exact ⟨SimpleGraph.Walk.nil, rfl⟩
      | cons y ys =>
          rw [List.isChain_cons_cons] at hchain
          obtain ⟨hxy, hchain'⟩ := hchain
          simp only [List.head?_cons, Option.some.injEq] at hhead
          subst a
          rw [List.getLast?_cons_cons] at hlast
          obtain ⟨w, hw⟩ := ih rfl hlast hchain'
          exact ⟨SimpleGraph.Walk.cons hxy w, by
            rw [SimpleGraph.Walk.support_cons, hw]⟩

/-- A chain in the ambient graph lifts to a chain of subtypes, provided the subtype relation is
implied by the ambient relation. -/
theorem isChain_attachWith_of_isChain {p : X → Prop}
    {R : {x // p x} → {x // p x} → Prop} {S : X → X → Prop}
    (hRS : ∀ x hx y hy, S x y → R ⟨x, hx⟩ ⟨y, hy⟩) :
    ∀ {l : List X} (H : ∀ x ∈ l, p x), l.IsChain S → (l.attachWith p H).IsChain R
  | [], _, _ => by simp
  | [_], _, _ => by simp
  | x :: y :: rest, H, hchain => by
      rw [List.isChain_cons_cons] at hchain
      obtain ⟨hxy, hchain'⟩ := hchain
      rw [List.attachWith_cons, List.attachWith_cons, List.isChain_cons_cons]
      exact ⟨hRS x _ y _ hxy,
        isChain_attachWith_of_isChain hRS
          (fun z hz => H z (List.mem_cons_of_mem x hz)) hchain'⟩

/-- A nodup list stays nodup after attaching subtype proofs. -/
theorem nodup_attachWith {p : X → Prop} {l : List X} (H : ∀ x ∈ l, p x)
    (h : l.Nodup) : (l.attachWith p H).Nodup :=
  List.Nodup.of_map Subtype.val (by
    rw [List.attachWith_map_subtype_val]
    exact h)

/-- The head of the subtype-attached list is the head atom with its membership proof. -/
theorem head?_attachWith_of_head? {p : X → Prop} {l : List X}
    (H : ∀ x ∈ l, p x) {a : X} (h : l.head? = some a) :
    (l.attachWith p H).head? = some ⟨a, H a (mem_of_head?_eq_some h)⟩ := by
  cases l with
  | nil => simp at h
  | cons x xs =>
      simp only [List.head?_cons, Option.some.injEq] at h
      obtain rfl : a = x := h.symm
      rw [List.attachWith_cons]
      exact congrArg some (Subtype.ext rfl)

/-- The last element of the subtype-attached list is the last atom with its membership proof. -/
theorem getLast?_attachWith_of_getLast? {p : X → Prop} :
    ∀ {l : List X} (H : ∀ x ∈ l, p x) {a : X} (h : l.getLast? = some a),
      (l.attachWith p H).getLast? = some ⟨a, H a (mem_of_getLast?_eq_some h)⟩
  | [], _, _, h => by simp at h
  | [x], H, a, h => by
      simp only [List.getLast?_singleton, Option.some.injEq] at h
      obtain rfl : a = x := h.symm
      rw [List.attachWith_cons]
      exact congrArg some (Subtype.ext rfl)
  | x :: y :: rest, H, a, h => by
      rw [List.getLast?_cons_cons] at h
      rw [List.attachWith_cons, List.attachWith_cons, List.getLast?_cons_cons]
      exact (getLast?_attachWith_of_getLast?
        (fun z hz => H z (List.mem_cons_of_mem x hz)) h).trans
        (congrArg some (Subtype.ext rfl))

end Generic

/-! ## Real arm occurrences and the physical carrier -/

/-- **The physical centre-deleted arm carrier.**  Atoms other than the centre that are connected to
the fixed canonical ligand inside `centerDeletedGraph input.moleculeGraph center.1`, i.e. by a
physical walk that never visits the centre.  This is the honest physical component of the ligand
after deleting the centre; it is a set of actual atoms, not an address shape. -/
def centerDeletedArmCarrier (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    Set {v : input.Atom // v ≠ center.1} :=
  fun w => Nonempty
    ((CertifiedLocalizedCIPInput.centerDeletedGraph input.moleculeGraph center.1).Walk
      ⟨input.canonicalLigandAtom center index,
        input.canonicalLigandAtom_ne_center center index⟩ w)

/-- **A real arm occurrence.**  The node is a real official node whose stored history is a simple
physical path from the original centre (`RealPathNode`) still ending in the fixed ligand/centre
pair.  These are exactly the positions the actual outward expansion reproduces physically. -/
def RealArmNode (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (node : OfficialCIPNode input.Atom) : Prop :=
  input.RealPathNode center.1 node ∧
    [input.canonicalLigandAtom center index, center.1] <:+ node.history

/-- A real arm occurrence with its observed current atom made explicit, so that the atom-level
projection used by the carrier equivalence is a genuine function of the data. -/
structure RealArmOccurrence (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) where
  /-- The real official node. -/
  node : OfficialCIPNode input.Atom
  /-- The physical atom observed at the node. -/
  current : input.Atom
  /-- The observation equation. -/
  currentObserved : node.current? = some current
  /-- The node is a real arm occurrence. -/
  real : RealArmNode input center index node

/-- The stored history of a real path node is duplicate-free. -/
theorem realPathNode_history_nodup (input : CertifiedLocalizedCIPInput)
    {root : input.Atom} {node : OfficialCIPNode input.Atom}
    (real : input.RealPathNode root node) : node.history.Nodup := by
  obtain ⟨_current, path, _observed, _head, _provenance, simple, supportReverse,
    _penultimate⟩ := real
  rw [← supportReverse]
  exact List.nodup_reverse.mpr simple.support_nodup

/-- The actual root of the canonical ligand arm is a real arm occurrence: its stored history is
exactly the two-atom chain through the fixed ligand. -/
theorem realArmNode_rootFromEdge (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    RealArmNode input center index
      (OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index)) := by
  refine ⟨⟨input.canonicalLigandAtom center index,
    SimpleGraph.Walk.cons (input.canonicalLigandAtom_adj center index) SimpleGraph.Walk.nil,
    rfl, rfl, rfl, ?_, ?_, ?_⟩, ⟨[], by simp [OfficialCIPNode.rootFromEdge]⟩⟩
  · rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_cons,
      SimpleGraph.Walk.support_nil]
    refine List.nodup_cons.mpr ⟨?_, by simp⟩
    simp only [List.mem_singleton]
    exact fun same => input.canonicalLigandAtom_ne_center center index same.symm
  · simp [OfficialCIPNode.rootFromEdge]
  · intro parent observed
    rw [OfficialCIPNode.parent?_rootFromEdge] at observed
    have parentEq : parent = center.1 := (Option.some.inj observed).symm
    rw [parentEq]
    rfl

/-- **Real extension without any acyclicity hypothesis.**  Appending an unvisited physical
neighbour to a real path node yields a real path node at the extended history.  The new walk is
the old simple walk concatenated with the fresh edge, so this uses only the freshness of the new
atom on the branch, replacing the global-acyclicity step of the earlier carrier arguments. -/
theorem realPathNode_extend_zero (input : CertifiedLocalizedCIPInput)
    {node : OfficialCIPNode input.Atom} {root current next : input.Atom}
    (real : input.RealPathNode root node)
    (currentObserved : node.current? = some current)
    (fresh : next ∉ node.history)
    (adjacent : input.moleculeGraph.Adj current next) :
    input.RealPathNode root (node.extend next 0) := by
  obtain ⟨observedAtom, path, observed, head, _provenance, simple, supportReverse,
    penultimate⟩ := real
  have atomEq : observedAtom = current := Option.some.inj (observed.symm.trans currentObserved)
  subst observedAtom
  have nextNotSupport : next ∉ path.support := by
    intro present
    exact fresh (by
      have : next ∈ path.support.reverse := List.mem_reverse.mpr present
      rwa [supportReverse] at this)
  have parentValue : (node.extend next 0).parent? = some current := by
    cases historyEq : node.history with
    | nil => simp [historyEq] at head
    | cons first rest =>
        have firstEq : first = current := by simpa [historyEq] using head
        rw [OfficialCIPNode.parent?, OfficialCIPNode.extend_history, historyEq]
        simp [firstEq]
  have extendedProvenance : (node.extend next 0).provenance =
      OfficialCIPNodeProvenance.realAtom := by
    rw [OfficialCIPNode.extend_provenance,
      OfficialCIPNode.childProvenance_real node next fresh]
  refine ⟨next, path.concat adjacent, rfl, rfl, extendedProvenance,
    simple.concat nextNotSupport adjacent, ?_, ?_⟩
  · simp [OfficialCIPNode.extend, supportReverse]
  · intro parent observed
    have parentEq : parent = current := by
      rw [parentValue] at observed
      exact (Option.some.inj observed).symm
    rw [parentEq]
    simp

/-- The current atom of a real arm occurrence is not the deleted centre.  The stored history is a
duplicate-free list beginning with the current atom and ending in the fixed ligand/centre pair, so
the current atom cannot be the centre. -/
theorem realArmOccurrence_current_ne_center (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {node : OfficialCIPNode input.Atom} {current : input.Atom}
    (real : input.RealPathNode center.1 node)
    (suffixHist : [input.canonicalLigandAtom center index, center.1] <:+ node.history)
    (currentObserved : node.current? = some current) :
    current ≠ center.1 := by
  obtain ⟨observedAtom, path, observed, head, _provenance, simple, supportReverse,
    _penultimate⟩ := real
  have atomEq : observedAtom = current := Option.some.inj (observed.symm.trans currentObserved)
  subst observedAtom
  have nodup : node.history.Nodup := by
    rw [← supportReverse]
    exact List.nodup_reverse.mpr simple.support_nodup
  obtain ⟨pre, hpre⟩ := suffixHist
  intro currentCenter
  cases pre with
  | nil =>
      rw [← hpre] at head
      simp only [List.nil_append, List.head?_cons, Option.some.injEq] at head
      exact input.canonicalLigandAtom_ne_center center index (head.trans currentCenter)
  | cons a pre' =>
      rw [← hpre] at head nodup
      simp only [List.cons_append, List.head?_cons, Option.some.injEq] at head
      have aCenter : a = center.1 := by rw [head, currentCenter]
      have hmem : a ∈ pre' ++ [input.canonicalLigandAtom center index, center.1] := by
        rw [aCenter]
        simp
      exact (List.nodup_cons.mp nodup).1 hmem

/-! ## Source-tree positions of real arm occurrences -/

mutual
  /-- All source nodes of an official source tree, in preorder.  A real position of the actual
  expansion is a node of this list whose node is a real arm occurrence. -/
  def sourceNodes {V : Type*} : OfficialCIPSourceTree V → List (OfficialCIPNode V)
    | .node source children => source :: sourceNodesList children

  /-- All source nodes of a recursive sibling forest, in the stored order. -/
  def sourceNodesList {V : Type*} :
      List (OfficialCIPSourceTree V) → List (OfficialCIPNode V)
    | [] => []
    | tree :: trees => sourceNodes tree ++ sourceNodesList trees
end

/-- A node occurring in one subtree of a forest occurs in the whole forest. -/
theorem mem_sourceNodesList_of_mem {V : Type*} {subtree : OfficialCIPSourceTree V}
    {children : List (OfficialCIPSourceTree V)} (hmem : subtree ∈ children)
    {node : OfficialCIPNode V} (present : node ∈ sourceNodes subtree) :
    node ∈ sourceNodesList children := by
  induction children with
  | nil => simp at hmem
  | cons c cs ih =>
      change node ∈ sourceNodes c ++ sourceNodesList cs
      rcases List.mem_cons.mp hmem with rfl | later
      · exact List.mem_append.mpr (Or.inl present)
      · exact List.mem_append.mpr (Or.inr (ih later))

/-- **Unbounded executable reachability lands on an actual source position.**  Every node reached
from the root of a generated official source tree by the actual executable child enumerator occurs
as a source node of that tree. -/
theorem mem_sourceNodes_of_unbounded (input : CertifiedLocalizedCIPInput)
    {start node : OfficialCIPNode input.Atom} {address : List Nat}
    (reachable : input.UnboundedOfficialSubtree start address node) :
    ∀ {tree : OfficialCIPSourceTree input.Atom}, tree.source = start →
      tree.GeneratedBy input.executableOfficialCIPChildren → node ∈ sourceNodes tree := by
  induction reachable with
  | refl startNode =>
      intro tree rootEq _generated
      cases tree with
      | node source children =>
          have same : startNode = source := rootEq.symm
          rw [same]
          exact List.mem_cons_self
  | @step node child inner descendant slot childAtSlot rest ih =>
      intro tree rootEq generated
      cases tree with
      | node source children =>
          have childMem : child ∈ input.executableOfficialCIPChildren node :=
            List.fst_mem_of_mem_zipIdx childAtSlot
          have childMemSource : child ∈ input.executableOfficialCIPChildren source := by
            have present := childMem
            rwa [← rootEq] at present
          have inMap : child ∈ children.map OfficialCIPSourceTree.source :=
            (generated.1).mem_iff.mpr childMemSource
          obtain ⟨subtree, subtreeMem, subtreeSource⟩ := List.mem_map.mp inMap
          have subtreeGenerated : subtree.GeneratedBy input.executableOfficialCIPChildren :=
            (OfficialCIPSourceTree.forestGeneratedBy_iff_forall
              input.executableOfficialCIPChildren children).1 generated.2 subtree subtreeMem
          exact List.mem_cons_of_mem source
            (mem_sourceNodesList_of_mem subtreeMem (ih subtreeSource subtreeGenerated))

/-! ## Chain extension along the physical arm with real-path invariants -/

/-- **Real chain extension along an actual arm.**  Starting from an actual executable node that is
a real arm occurrence, follow a physical adjacency chain whose tail avoids the stored history.
The result is an actual executable descendant at the chain's last atom which is again a real arm
occurrence.  No global acyclicity is used: freshness is the explicit disjointness hypothesis, and
`realPathNode_extend_zero` supplies the simple-path invariant. -/
theorem exists_realArmDescendant_of_chain
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter) (index : Fin 4)
    {start : OfficialCIPNode input.Atom} {root : input.Atom} :
    ∀ (current : input.Atom) (rest : List input.Atom)
      (node : OfficialCIPNode input.Atom) (address : List Nat),
      input.UnboundedOfficialSubtree start address node →
      node.current? = some current →
      node.provenance = OfficialCIPNodeProvenance.realAtom →
      input.RealPathNode root node →
      [input.canonicalLigandAtom center index, center.1] <:+ node.history →
      (current :: rest).Nodup →
      (current :: rest).IsChain (fun a b => input.moleculeGraph.Adj a b) →
      (∀ x ∈ node.history, x ∉ rest) →
      ∃ finalNode suffix,
        input.UnboundedOfficialSubtree start (address ++ suffix) finalNode ∧
        suffix.length = rest.length ∧
        finalNode.current? = (current :: rest).getLast? ∧
        finalNode.provenance = OfficialCIPNodeProvenance.realAtom ∧
        input.RealPathNode root finalNode ∧
        [input.canonicalLigandAtom center index, center.1] <:+ finalNode.history := by
  intro current rest
  induction rest generalizing current with
  | nil =>
      intro node address reachable currentObserved provenance nodeReal nodeSuffix _nodup _chain
        _disjoint
      exact ⟨node, [], by simpa using reachable, rfl, by simpa using currentObserved, provenance,
        nodeReal, nodeSuffix⟩
  | cons next tail inductionHypothesis =>
      intro node address reachable currentObserved provenance nodeReal nodeSuffix nodup chain
        disjoint
      have nodupTail : (next :: tail).Nodup := (List.nodup_cons.mp nodup).2
      have nextNotTail : next ∉ tail := (List.nodup_cons.mp nodupTail).1
      have adjacent : input.moleculeGraph.Adj current next := chain.rel_head
      have fresh : next ∉ node.history := by
        intro present
        exact disjoint next present List.mem_cons_self
      have notParent : node.parent? ≠ some next := by
        intro parentObserved
        exact disjoint next (input.parent_mem_history_of_parent? parentObserved)
          List.mem_cons_self
      have copyPresent := input.mem_executableOfficialChildCopies_of_adjacent node current next 0
        currentObserved adjacent adjacent (Or.inr notParent)
      have nonduplicate := input.isDuplicateLeaf_eq_false_of_provenance_real node provenance
      have atSlot := input.executableOfficialChildCopySlot_mem node next 0 nonduplicate copyPresent
      have extendedReach := input.unboundedOfficialSubtree_append_last reachable atSlot
      have extendedProvenance : (node.extend next 0).provenance =
          OfficialCIPNodeProvenance.realAtom := by
        rw [OfficialCIPNode.extend_provenance,
          OfficialCIPNode.childProvenance_real node next fresh]
      have extendedReal : input.RealPathNode root (node.extend next 0) :=
        realPathNode_extend_zero input nodeReal currentObserved fresh adjacent
      have extendedSuffix :
          [input.canonicalLigandAtom center index, center.1] <:+ (node.extend next 0).history := by
        obtain ⟨pre, hpre⟩ := nodeSuffix
        exact ⟨next :: pre, by rw [OfficialCIPNode.extend_history]; simp [hpre]⟩
      have nextDisjoint : ∀ x ∈ (node.extend next 0).history, x ∉ tail := by
        intro x present inTail
        rw [OfficialCIPNode.extend_history] at present
        rcases List.mem_cons.mp present with same | earlier
        · subst same
          exact nextNotTail inTail
        · exact disjoint x earlier (List.mem_cons_of_mem next inTail)
      obtain ⟨finalNode, suffix, finalReach, suffixLength, finalObserved, finalProvenance,
        finalReal, finalSuffix⟩ :=
        inductionHypothesis next (node.extend next 0)
          (address ++ [input.executableOfficialChildCopySlot node next 0])
          extendedReach rfl extendedProvenance extendedReal extendedSuffix nodupTail chain.tail
          nextDisjoint
      refine ⟨finalNode, input.executableOfficialChildCopySlot node next 0 :: suffix, ?_, ?_,
        ?_, finalProvenance, finalReal, finalSuffix⟩
      · have addressEq : address ++
            (input.executableOfficialChildCopySlot node next 0 :: suffix) =
            (address ++ [input.executableOfficialChildCopySlot node next 0]) ++ suffix := by
          simp [List.append_assoc]
        rw [addressEq]
        exact finalReach
      · simpa using congrArg Nat.succ suffixLength
      · rw [List.getLast?_cons_cons]
        exact finalObserved

/-! ## The physical walk carried by a real arm occurrence -/

/-- A centre-deleted walk maps to an actual physical walk with the same list of atoms. -/
theorem exists_atomWalk_of_centerDeletedWalk {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (center : V) {u v : {x : V // x ≠ center}}
    (walk : (CertifiedLocalizedCIPInput.centerDeletedGraph m center).Walk u v) :
    ∃ path : m.underlyingSimpleGraph.Walk u.1 v.1,
      path.support = walk.support.map Subtype.val := by
  induction walk with
  | nil => exact ⟨SimpleGraph.Walk.nil, by simp⟩
  | cons h p ih =>
      obtain ⟨path, supportEq⟩ := ih
      exact ⟨SimpleGraph.Walk.cons h path, by simp [supportEq]⟩

/-- A walk lying in the centre-deleted subtype graph never visits the centre. -/
theorem center_not_mem_support_of_centerDeletedWalk {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V) (center : V) {u v : {x : V // x ≠ center}}
    (walk : (CertifiedLocalizedCIPInput.centerDeletedGraph m center).Walk u v)
    {path : m.underlyingSimpleGraph.Walk u.1 v.1}
    (supportEq : path.support = walk.support.map Subtype.val) :
    center ∉ path.support := by
  rw [supportEq, List.mem_map]
  rintro ⟨w, _present, wEq⟩
  exact w.2 wEq

/-- **Every real arm occurrence carries an actual centre-avoiding physical walk from the fixed
ligand.**  The stored history ends in the ligand/centre pair, so deleting that first step leaves a
centre-avoiding chain from the ligand to the observed atom; the chain lifts into the centre-deleted
graph. -/
theorem exists_carrierWalk_of_realArmOccurrence (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {node : OfficialCIPNode input.Atom} {current : input.Atom}
    (real : input.RealPathNode center.1 node)
    (suffixHist : [input.canonicalLigandAtom center index, center.1] <:+ node.history)
    (currentObserved : node.current? = some current) :
    ∃ hc : current ≠ center.1,
      Nonempty
        ((CertifiedLocalizedCIPInput.centerDeletedGraph input.moleculeGraph center.1).Walk
          ⟨input.canonicalLigandAtom center index,
            input.canonicalLigandAtom_ne_center center index⟩ ⟨current, hc⟩) := by
  obtain ⟨observedAtom, path, observed, head, _provenance, simple, supportReverse,
    _penultimate⟩ := real
  have atomEq : observedAtom = current := Option.some.inj (observed.symm.trans currentObserved)
  rw [atomEq] at observed head
  obtain ⟨pre, hpre⟩ := suffixHist
  have hsupport : path.support =
      center.1 :: (input.canonicalLigandAtom center index :: pre.reverse) := by
    have hnode : node.history =
        pre ++ [input.canonicalLigandAtom center index, center.1] := hpre.symm
    calc
      path.support = node.history.reverse := by
        rw [← supportReverse, List.reverse_reverse]
      _ = (pre ++ [input.canonicalLigandAtom center index, center.1]).reverse := by
        rw [hnode]
      _ = center.1 :: (input.canonicalLigandAtom center index :: pre.reverse) := by
        simp [List.reverse_append]
  have hnodup : (center.1 :: (input.canonicalLigandAtom center index :: pre.reverse)).Nodup := by
    rw [← hsupport]
    exact simple.support_nodup
  have hnotcenter : center.1 ∉ (input.canonicalLigandAtom center index :: pre.reverse) :=
    (List.nodup_cons.mp hnodup).1
  have hchain : (input.canonicalLigandAtom center index :: pre.reverse).IsChain
      (fun a b => input.moleculeGraph.Adj a b) := by
    have supportChain := SimpleGraph.Walk.isChain_adj_support path
    rw [hsupport] at supportChain
    exact supportChain.tail
  have hlast : (input.canonicalLigandAtom center index :: pre.reverse).getLast? =
      some current := by
    have hget : path.support.getLast? = some current := by
      rw [← List.head?_reverse, supportReverse]
      exact head
    rw [hsupport, List.getLast?_cons_cons] at hget
    exact hget
  have hattach : ∀ x ∈ (input.canonicalLigandAtom center index :: pre.reverse),
      x ≠ center.1 := by
    intro x present same
    exact hnotcenter (same ▸ present)
  let attached := (input.canonicalLigandAtom center index :: pre.reverse).attachWith
    (fun x => x ≠ center.1) hattach
  have attachedChain : attached.IsChain
      (CertifiedLocalizedCIPInput.centerDeletedGraph input.moleculeGraph center.1).Adj :=
    isChain_attachWith_of_isChain (fun _ _ _ _ hxy => hxy) hattach hchain
  have attachedHead : attached.head? =
      some ⟨input.canonicalLigandAtom center index,
        input.canonicalLigandAtom_ne_center center index⟩ :=
    head?_attachWith_of_head? hattach rfl
  have attachedLast : attached.getLast? =
      some ⟨current, hattach current (mem_of_getLast?_eq_some hlast)⟩ :=
    getLast?_attachWith_of_getLast? hattach hlast
  refine ⟨hattach current (mem_of_getLast?_eq_some hlast), ?_⟩
  obtain ⟨walk, _walkSupport⟩ := exists_walk_of_isChain attachedHead attachedLast attachedChain
  exact ⟨walk⟩

/-! ## Coverage of the physical carrier by actual real positions -/

/-- **Coverage.**  Every physical atom of the centre-deleted ligand component is the current atom
of an actual real position of any actual executable tree rooted at the canonical ligand edge.  The
witness is produced by the actual executable expansion itself; no desired atom map is assumed. -/
theorem exists_realArmOccurrence_of_mem_carrier (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : OfficialCIPSourceTree input.Atom}
    (rootEq : tree.source = OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index))
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (w : {v : input.Atom // v ≠ center.1})
    (carrier : w ∈ centerDeletedArmCarrier input center index) :
    ∃ occ : RealArmOccurrence input center index,
      occ.node ∈ sourceNodes tree ∧ occ.current = w.1 := by
  obtain ⟨walk⟩ := carrier
  obtain ⟨path, supportEq⟩ :=
    exists_atomWalk_of_centerDeletedWalk input.moleculeGraph center.1 walk
  have avoids : center.1 ∉ path.support :=
    center_not_mem_support_of_centerDeletedWalk input.moleculeGraph center.1 walk supportEq
  let simplePath := path.toPath
  have simple : simplePath.1.IsPath := simplePath.2
  have avoidsPath : center.1 ∉ simplePath.1.support := by
    intro present
    exact avoids (SimpleGraph.Walk.support_toPath_subset path present)
  let ligand := input.canonicalLigandAtom center index
  have supportForm : simplePath.1.support = ligand :: simplePath.1.support.tail :=
    SimpleGraph.Walk.support_eq_cons simplePath.1
  have nodup : (ligand :: simplePath.1.support.tail).Nodup := by
    rw [← supportForm]
    exact simple.support_nodup
  have chain : (ligand :: simplePath.1.support.tail).IsChain
      (fun a b => input.moleculeGraph.Adj a b) := by
    rw [← supportForm]
    exact SimpleGraph.Walk.isChain_adj_support simplePath.1
  have disjoint : ∀ x ∈ (OfficialCIPNode.rootFromEdge center.1 ligand).history,
      x ∉ simplePath.1.support.tail := by
    intro x present
    have presentForm : x = ligand ∨ x = center.1 := by
      simpa [OfficialCIPNode.rootFromEdge, ligand] using present
    rcases presentForm with same | same
    · subst same
      exact (List.nodup_cons.mp nodup).1
    · subst same
      intro inTail
      exact avoidsPath (by
        rw [supportForm]
        exact List.mem_cons_of_mem ligand inTail)
  have lastEq : (ligand :: simplePath.1.support.tail).getLast? = some w.1 := by
    rw [← supportForm]
    rw [List.getLast?_eq_getLast_of_ne_nil (by simp)]
    exact congrArg some (SimpleGraph.Walk.getLast_support simplePath.1)
  have startReal := realArmNode_rootFromEdge input center index
  obtain ⟨finalNode, suffix, finalReach, _suffixLength, finalObserved, _finalProvenance,
    finalReal, finalSuffix⟩ :=
    exists_realArmDescendant_of_chain input center index ligand simplePath.1.support.tail
      (OfficialCIPNode.rootFromEdge center.1 ligand) [] (UnboundedOfficialSubtree.refl _)
      rfl rfl startReal.1 startReal.2 nodup chain disjoint
  have finalPosition : finalNode ∈ sourceNodes tree := by
    exact mem_sourceNodes_of_unbounded input (by simpa using finalReach) rootEq generated
  refine ⟨⟨finalNode, w.1, ?_, ⟨finalReal, finalSuffix⟩⟩, finalPosition, rfl⟩
  rw [finalObserved, lastEq]

/-! ## Injectivity of the current atom on real arm occurrences -/



theorem realArmOccurrence_eq_of_current_eq (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (domainTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {left right : RealArmOccurrence input center index}
    (sameCurrent : left.current = right.current) : left = right := by
  obtain ⟨lnode, lcurrent, lobserved, lreal⟩ := left
  obtain ⟨rnode, rcurrent, robserved, rreal⟩ := right
  obtain ⟨lrealPath, lsuffix⟩ := lreal
  obtain ⟨rrealPath, rsuffix⟩ := rreal
  have sameCurrent' : lcurrent = rcurrent := sameCurrent
  subst sameCurrent'
  have hhist : lnode.history = rnode.history :=
    input.centerArm_history_eq_of_current_eq center index domainTree lrealPath rrealPath
      lsuffix rsuffix (by rw [lobserved, robserved])
  have hnode : lnode = rnode := by
    obtain ⟨lcurrentOpt, lhistory, lprovenance⟩ := lnode
    obtain ⟨rcurrentOpt, rhistory, rprovenance⟩ := rnode
    have hcurrent : lcurrentOpt = rcurrentOpt := by
      change (OfficialCIPNode.mk lcurrentOpt lhistory lprovenance).current? =
        (OfficialCIPNode.mk rcurrentOpt rhistory rprovenance).current?
      rw [lobserved, robserved]
    have hhistory : lhistory = rhistory := hhist
    have hprovenance : lprovenance = rprovenance := by
      change (OfficialCIPNode.mk lcurrentOpt lhistory lprovenance).provenance =
        (OfficialCIPNode.mk rcurrentOpt rhistory rprovenance).provenance
      rw [input.realPathNode_provenance lrealPath, input.realPathNode_provenance rrealPath]
    rw [hcurrent, hhistory, hprovenance]
  subst hnode
  rfl

/-- A real arm occurrence is a member of the physical carrier. -/
theorem realArmOccurrence_mem_carrier (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (occ : RealArmOccurrence input center index) :
    (⟨occ.current, realArmOccurrence_current_ne_center input center index occ.real.1 occ.real.2
      occ.currentObserved⟩ : {v : input.Atom // v ≠ center.1}) ∈
      centerDeletedArmCarrier input center index := by
  obtain ⟨hc, ⟨walk⟩⟩ := exists_carrierWalk_of_realArmOccurrence input center index
    occ.real.1 occ.real.2 occ.currentObserved
  exact ⟨walk⟩

/-! ## The real-position / carrier equivalence -/

/-- A real position of an actual source tree: an actual source node which is a real arm
occurrence. -/
def RealArmPosition (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (tree : OfficialCIPSourceTree input.Atom) : Type :=
  {occ : RealArmOccurrence input center index // occ.node ∈ sourceNodes tree}

/-- The atom-level projection of a real position. -/
noncomputable def realArmPositionToCarrier (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : OfficialCIPSourceTree input.Atom}
    (position : RealArmPosition input center index tree) :
    ↥(centerDeletedArmCarrier input center index) :=
  ⟨⟨position.1.current,
    realArmOccurrence_current_ne_center input center index position.1.real.1 position.1.real.2
      position.1.currentObserved⟩,
  realArmOccurrence_mem_carrier input center index position.1⟩

/-- The actual real position covering a physical carrier atom. -/
noncomputable def realArmPositionOfCarrier (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : OfficialCIPSourceTree input.Atom}
    (rootEq : tree.source = OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index))
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (w : ↥(centerDeletedArmCarrier input center index)) :
    RealArmPosition input center index tree :=
  let chosen := Classical.choose
    (exists_realArmOccurrence_of_mem_carrier input center index rootEq generated w.1 w.2)
  ⟨chosen, (Classical.choose_spec
    (exists_realArmOccurrence_of_mem_carrier input center index rootEq generated w.1 w.2)).1⟩








noncomputable def realArmPositionEquiv (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (domainTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    (tree : OfficialCIPSourceTree input.Atom)
    (rootEq : tree.source = OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index))
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren) :
    RealArmPosition input center index tree ≃ ↥(centerDeletedArmCarrier input center index) where
  toFun := realArmPositionToCarrier input center index
  invFun := realArmPositionOfCarrier input center index rootEq generated
  left_inv := by
    intro position
    apply Subtype.ext
    apply realArmOccurrence_eq_of_current_eq input center index domainTree
    exact (Classical.choose_spec
      (exists_realArmOccurrence_of_mem_carrier input center index rootEq generated
        (realArmPositionToCarrier input center index position).1
        (realArmPositionToCarrier input center index position).2)).2
  right_inv := by
    intro w
    apply Subtype.ext
    apply Subtype.ext
    exact (Classical.choose_spec
      (exists_realArmOccurrence_of_mem_carrier input center index rootEq generated
        w.1 w.2)).2

/-! ## Root and adjacency compatibility for the successor reconstruction -/

/-- The actual root real occurrence of the canonical ligand arm: the two-atom chain through the
fixed ligand.  Its current atom is the ligand and its history is exactly `[ligand, centre]`. -/
def realArmRootOccurrence (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    RealArmOccurrence input center index where
  node := OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index)
  current := input.canonicalLigandAtom center index
  currentObserved := rfl
  real := realArmNode_rootFromEdge input center index

/-- **Root compatibility.**  Any real arm occurrence observed at the fixed ligand atom is the
actual root occurrence.  This pins the bijection at the ligand end to the actual source root. -/
theorem realArmOccurrence_eq_root_of_current_eq_ligand (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (domainTree : input.CenterDeletedComponentTreeAt center.1
      (input.canonicalLigandAtom center index))
    {occ : RealArmOccurrence input center index}
    (sameLigand : occ.current = input.canonicalLigandAtom center index) :
    occ = realArmRootOccurrence input center index := by
  apply realArmOccurrence_eq_of_current_eq input center index domainTree
    (right := realArmRootOccurrence input center index)
  simpa [realArmRootOccurrence] using sameLigand

/-- The fixed ligand atom itself lies in the centre-deleted component carrier (by the trivial walk),
so the bijection's carrier side is always inhabited. -/
theorem ligand_mem_centerDeletedArmCarrier (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    (⟨input.canonicalLigandAtom center index,
      input.canonicalLigandAtom_ne_center center index⟩ : {v : input.Atom // v ≠ center.1}) ∈
      centerDeletedArmCarrier input center index :=
  ⟨SimpleGraph.Walk.nil⟩

/-- **The actual root position of an actual ligand-rooted source tree.**  The source root is the real
root occurrence, so every actual tree rooted at the canonical ligand edge has a real position at the
fixed ligand. -/
def realArmRootPosition (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : OfficialCIPSourceTree input.Atom}
    (rootEq : tree.source = OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index)) :
    RealArmPosition input center index tree :=
  ⟨realArmRootOccurrence input center index, by
    cases tree with
    | node source children =>
        show OfficialCIPNode.rootFromEdge center.1
            (input.canonicalLigandAtom center index) ∈ source :: sourceNodesList children
        have same : source = OfficialCIPNode.rootFromEdge center.1
            (input.canonicalLigandAtom center index) := by simpa using rootEq
        rw [same]
        exact List.mem_cons_self⟩

/-- The actual root position projects to the fixed ligand atom, as required for root-attachment
preservation downstream. -/
theorem realArmPositionToCarrier_rootPosition (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : OfficialCIPSourceTree input.Atom}
    (rootEq : tree.source = OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index)) :
    (realArmPositionToCarrier input center index
      (realArmRootPosition input center index rootEq)).1.1 =
      input.canonicalLigandAtom center index := rfl

/-- **Nonvacuity of the actual position type.**  Every actual source tree rooted at the canonical
ligand edge has a real position (its root), independently of any domain hypothesis. -/
theorem nonempty_realArmPosition (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : OfficialCIPSourceTree input.Atom}
    (rootEq : tree.source = OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index)) :
    Nonempty (RealArmPosition input center index tree) :=
  ⟨realArmRootPosition input center index rootEq⟩

/-- **Adjacency compatibility with the actual source tree.**  When one real position's node is an
actual executable child of another's, the two carried atoms are physically bonded.  This lets the
successor reconstruction transport actual source-tree edges to physical edges of the carrier. -/
theorem realArmPositionToCarrier_adjacent_of_executableChild
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter) (index : Fin 4)
    {tree : OfficialCIPSourceTree input.Atom}
    (parent child : RealArmPosition input center index tree)
    (present : child.1.node ∈ input.executableOfficialCIPChildren parent.1.node) :
    input.moleculeGraph.Adj
      (realArmPositionToCarrier input center index parent).1.1
      (realArmPositionToCarrier input center index child).1.1 :=
  input.adj_of_mem_executableOfficialCIPChildren parent.1.node child.1.node
    parent.1.current child.1.current parent.1.currentObserved child.1.currentObserved present

/-! ## The final actual-build wrapper -/













theorem actualArmCarrierCoverage
    (input : CertifiedLocalizedCIPInput) (center : input.TetrahedralCenter) (index : Fin 4)
    (domain : input.CenterDeletedArmDomain center index)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel) :
    ∃ key : input.LocalizedRerootCumulativeRule45Key,
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read
          (2 * (input.certified.input.molecule.atomCount + 1 + 1))
          (input.localizedLigandRootCursor center index) = some key ∧
        ∃ tree : LocalizedCumulativeDecoratedTree input
            (input.certified.input.molecule.atomCount + 1),
          tree.source = input.localizedLigandRootCursor center index ∧
            LocalizedCumulativeTreeTableMatch stage tree key ∧
              LocalizedCumulativeTreeRealizes input read tree ∧
                (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).GeneratedBy
                    input.executableOfficialCIPChildren ∧
                  (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree).source =
                      OfficialCIPNode.rootFromEdge center.1
                        (input.canonicalLigandAtom center index) ∧
                    DeclarativeCIP.RootedDigraph.FaithfulExactExpansion input.moleculeGraph
                      center.1 (input.canonicalLigandAtom center index)
                      (LocalizedCumulativeDecoratedTree.toOfficialSourceTree
                        tree).toDeclarativeDigraph ∧
                      Nonempty (RealArmPosition input center index
                          (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree) ≃
                        ↥(centerDeletedArmCarrier input center index)) := by
  obtain ⟨key, built, tree, treeSource, tableMatch, realizes, generated, treeRoot, faithful⟩ :=
    input.localizedLigandRoot_sourceTree_faithfulExactExpansion center index stage read
  exact ⟨key, built, tree, treeSource, tableMatch, realizes, generated, treeRoot, faithful,
    ⟨realArmPositionEquiv input center index domain.tree
      (LocalizedCumulativeDecoratedTree.toOfficialSourceTree tree) treeRoot generated⟩⟩

end LocalizedCenterDeletedActualArmCoverage

end TetraStereo.OneCenter

/-! ## Direct kernel-authority guards -/

assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.mem_of_head?_eq_some
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.mem_of_getLast?_eq_some
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.exists_walk_of_isChain
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.isChain_attachWith_of_isChain
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.nodup_attachWith
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.head?_attachWith_of_head?
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.getLast?_attachWith_of_getLast?
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.centerDeletedArmCarrier
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.RealArmNode
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.RealArmOccurrence
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realPathNode_history_nodup
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realArmNode_rootFromEdge
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realPathNode_extend_zero
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realArmOccurrence_current_ne_center
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.sourceNodes
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.sourceNodesList
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.mem_sourceNodesList_of_mem
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.mem_sourceNodes_of_unbounded
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.exists_realArmDescendant_of_chain
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.exists_atomWalk_of_centerDeletedWalk
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.center_not_mem_support_of_centerDeletedWalk
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.exists_carrierWalk_of_realArmOccurrence
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.exists_realArmOccurrence_of_mem_carrier
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realArmOccurrence_eq_of_current_eq
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realArmOccurrence_mem_carrier
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.RealArmPosition
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realArmPositionToCarrier
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realArmPositionOfCarrier
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realArmPositionEquiv
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realArmRootOccurrence
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realArmOccurrence_eq_root_of_current_eq_ligand
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realArmPositionToCarrier_adjacent_of_executableChild
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.ligand_mem_centerDeletedArmCarrier
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realArmRootPosition
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.realArmPositionToCarrier_rootPosition
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.nonempty_realArmPosition
assert_kernel_only
  TetraStereo.OneCenter.LocalizedCenterDeletedActualArmCoverage.actualArmCarrierCoverage
