import TetraStereo.OneCenter.AuthoritativeLocalizedRuleMajorAnalysis
import TetraStereo.OneCenter.DeclarativeCIPConstitutional

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Independent Rule-1b conformance for authoritative localized inputs

The rule-major compiler stores an official provenance node at every parent-slot address.  Its
historical Rule-1b projection reads `OfficialCIPNode.rule1bRootDistance` directly.  This module
closes the authority boundary by translating each official provenance node into the independent
`DeclarativeCIP.NodeLabel` vocabulary and proving that every compiled observation equals
`DeclarativeCIP.nodeRule1bRootDistance` at that node's actual address.

The proof is structural.  It establishes that executable child expansion adds exactly one history
element and that addressed child merging adds exactly one address component.  It therefore covers
arbitrary finite branch width and every source node produced at the proved default depth bound.

The final pipeline theorem reifies the compiler's exact source occurrences as a finite declarative
`RootedDigraph`, proves every multiple-bond and ring duplicate satisfies
`RootedDigraph.DuplicateDistancesCorrect` under every addressing, and proves the emitted Rule-1b
layers equal the independent positional observations.  Its scope is the certified localized-CIP
domain; broader normalization and provision-complete P-92.2.2 coverage remain separate.
-/

namespace OfficialCIPNodeProvenance

/-- Representation-independent provenance corresponding to one official implementation node. -/
def toDeclarative : OfficialCIPNodeProvenance → DeclarativeCIP.NodeProvenance
  | .realAtom => .realAtom
  | .multipleBondDuplicate distance => .multipleBondDuplicate distance
  | .ringDuplicate distance => .ringDuplicate distance
  | .placeholder .phantom distance => .phantom distance
  | .placeholder .lonePair distance => .lonePair distance
  | .placeholder .auxiliary distance => .auxiliary distance

end OfficialCIPNodeProvenance

namespace OfficialCIPNode

/-- Nodes generated from molecular graph edges use real-atom or duplicate provenance.  Explicit
phantom/lone-pair/auxiliary nodes are supplied by separate descriptor contexts. -/
def GraphGenerated {V : Type*} (node : OfficialCIPNode V) : Prop :=
  match node.provenance with
  | .placeholder _ _ => False
  | _ => True

/-- Independent semantic label of an official provenance-bearing node. -/
def toDeclarativeLabel {V : Type*} (node : OfficialCIPNode V) :
    DeclarativeCIP.NodeLabel V where
  atom? := node.current?
  provenance := node.provenance.toDeclarative

/-- An official Rule-1b observation agrees with the independent positional semantics whenever
the stored history and the parent-slot address describe the same sphere. -/
theorem rule1bRootDistance_eq_independent {V : Type*} (node : OfficialCIPNode V)
    (position : List ℕ)
    (historyLength : node.history.length = position.length + 2)
    (graphGenerated : node.GraphGenerated) :
    node.rule1bRootDistance =
      DeclarativeCIP.nodeRule1bRootDistance position (some node.toDeclarativeLabel) := by
  cases provenanceObserved : node.provenance with
  | realAtom =>
      simp only [OfficialCIPNode.rule1bRootDistance, provenanceObserved,
        toDeclarativeLabel, OfficialCIPNodeProvenance.toDeclarative,
        DeclarativeCIP.nodeRule1bRootDistance, OfficialCIPNode.depth]
      omega
  | multipleBondDuplicate distance =>
      simp [OfficialCIPNode.rule1bRootDistance, provenanceObserved,
        toDeclarativeLabel, OfficialCIPNodeProvenance.toDeclarative,
        DeclarativeCIP.nodeRule1bRootDistance]
  | ringDuplicate distance =>
      simp [OfficialCIPNode.rule1bRootDistance, provenanceObserved,
        toDeclarativeLabel, OfficialCIPNodeProvenance.toDeclarative,
        DeclarativeCIP.nodeRule1bRootDistance]
  | placeholder kind distance =>
      simp [GraphGenerated, provenanceObserved] at graphGenerated

end OfficialCIPNode

namespace OfficialRuleMajorKey

/-- Rule-1b projection interpreted solely through the independent, position-sensitive semantic
function.  Unlike `rule1bLayers`, this projection does not read the implementation's cached
distance observation. -/
def independentRule1bLayers {V : Type*} (sources : AddressedSourceLayers V) :
    List (List (OfficialSparseEntry ℕ)) :=
  sources.map fun layer =>
    layer.map fun entry =>
      (entry.1, DeclarativeCIP.nodeRule1bRootDistance entry.1
        (some entry.2.toDeclarativeLabel))

/-- Every source occurrence below a root has a history extended once for every address component. -/
def SourceHistoryLengthFrom {V : Type*} (rootHistoryLength : ℕ)
    (sources : AddressedSourceLayers V) : Prop :=
  ∀ entry, entry ∈ sources.flatten →
    entry.2.history.length = rootHistoryLength + entry.1.length

/-- Every addressed source node came from molecular-graph expansion rather than an injected
placeholder context. -/
def SourceGraphGenerated {V : Type*} (sources : AddressedSourceLayers V) : Prop :=
  ∀ entry, entry ∈ sources.flatten → entry.2.GraphGenerated

private theorem mem_flatten_iff_getD
    {α : Type*} (entry : α) (layers : List (List α)) :
    entry ∈ layers.flatten ↔
      ∃ depth, depth < layers.length ∧ entry ∈ layers.getD depth [] := by
  rw [List.mem_flatten]
  constructor
  · rintro ⟨layer, layerPresent, entryPresent⟩
    obtain ⟨depth, depthLt, layerEq⟩ := List.mem_iff_getElem.mp layerPresent
    refine ⟨depth, depthLt, ?_⟩
    rw [← layerEq] at entryPresent
    simpa [List.getD, depthLt] using entryPresent
  · rintro ⟨depth, depthLt, entryPresent⟩
    refine ⟨layers[depth], List.getElem_mem .., ?_⟩
    simpa [List.getD, depthLt] using entryPresent

private theorem foldl_max_ge_initial {α : Type*} (measure : α → ℕ) :
    ∀ (values : List α) (initial : ℕ),
      initial ≤ values.foldl
        (fun longest value => max longest (measure value)) initial
  | [], _ => le_rfl
  | value :: values, initial =>
      le_trans (Nat.le_max_left initial (measure value))
        (foldl_max_ge_initial measure values (max initial (measure value)))

private theorem value_le_foldl_max_of_mem {α : Type*} (measure : α → ℕ) :
    ∀ (values : List α) (initial : ℕ) (value : α), value ∈ values →
      measure value ≤ values.foldl
        (fun longest item => max longest (measure item)) initial
  | [], _, _, present => by simp at present
  | head :: tail, initial, value, present => by
      rcases List.mem_cons.mp present with headEq | tailPresent
      · rw [headEq]
        exact le_trans (Nat.le_max_right initial (measure head))
          (foldl_max_ge_initial measure tail (max initial (measure head)))
      · exact value_le_foldl_max_of_mem measure tail
          (max initial (measure head)) value tailPresent

private theorem child_layers_length_le_count {V : Type*}
    (children : List (AddressedSourceLayers V)) (child : AddressedSourceLayers V)
    (present : child ∈ children) :
    child.length ≤ addressedChildLayerCount children := by
  exact value_le_foldl_max_of_mem (fun sources => sources.length)
    children 0 child present

/-- Flattening the ragged sphere transpose contains exactly every child occurrence prefixed by
its ranked sibling slot. -/
theorem mem_mergeAddressedChildren_flatten_iff {V : Type*}
    (children : List (AddressedSourceLayers V))
    (entry : OfficialSparseEntry (OfficialCIPNode V)) :
    entry ∈ (mergeAddressedChildren children).flatten ↔
      ∃ child ∈ children.zipIdx, ∃ source,
        source ∈ child.1.flatten ∧
          entry = (child.2 :: source.1, source.2) := by
  constructor
  · intro present
    rw [mem_flatten_iff_getD] at present
    rcases present with ⟨depth, depthLt, entryPresent⟩
    have depthLtCount : depth < addressedChildLayerCount children := by
      simpa [mergeAddressedChildren] using depthLt
    have inMerged : entry ∈ children.zipIdx.flatMap fun child =>
        prefixLayer child.2 (child.1.getD depth []) := by
      simpa [mergeAddressedChildren, List.getD, depthLtCount] using entryPresent
    simp only [List.mem_flatMap] at inMerged
    rcases inMerged with ⟨child, childPresent, inPrefix⟩
    simp only [prefixLayer, List.mem_map] at inPrefix
    rcases inPrefix with ⟨source, sourcePresent, rfl⟩
    have depthLtChild : depth < child.1.length := by
      by_contra outside
      have notLt : ¬depth < child.1.length := outside
      simp [List.getD, notLt] at sourcePresent
    have sourceFlatten : source ∈ child.1.flatten :=
      (mem_flatten_iff_getD source child.1).2
        ⟨depth, depthLtChild, sourcePresent⟩
    exact ⟨child, childPresent, source, sourceFlatten, rfl⟩
  · rintro ⟨child, childPresent, source, sourcePresent, rfl⟩
    rw [mem_flatten_iff_getD] at sourcePresent
    rcases sourcePresent with ⟨depth, depthLtChild, sourceInLayer⟩
    have childInChildren : child.1 ∈ children :=
      List.fst_mem_of_mem_zipIdx childPresent
    have depthLtCount : depth < addressedChildLayerCount children :=
      lt_of_lt_of_le depthLtChild
        (child_layers_length_le_count children child.1 childInChildren)
    rw [mem_flatten_iff_getD]
    refine ⟨depth, ?_, ?_⟩
    · simpa [mergeAddressedChildren] using depthLtCount
    · have inMerged : (child.2 :: source.1, source.2) ∈
          children.zipIdx.flatMap fun indexed =>
            prefixLayer indexed.2 (indexed.1.getD depth []) := by
        simp only [List.mem_flatMap]
        refine ⟨child, childPresent, ?_⟩
        simp only [prefixLayer, List.mem_map]
        exact ⟨source, sourceInLayer, rfl⟩
      simpa [mergeAddressedChildren, List.getD, depthLtCount] using inMerged

theorem sourceHistoryLengthFrom_root {V : Type*} (node : OfficialCIPNode V) :
    SourceHistoryLengthFrom node.history.length [[([], node)]] := by
  intro entry present
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at present
  subst entry
  simp

theorem SourceHistoryLengthFrom.append {V : Type*} {rootLength : ℕ}
    {left right : AddressedSourceLayers V}
    (leftCorrect : SourceHistoryLengthFrom rootLength left)
    (rightCorrect : SourceHistoryLengthFrom rootLength right) :
    SourceHistoryLengthFrom rootLength (left ++ right) := by
  intro entry present
  rw [List.flatten_append, List.mem_append] at present
  exact present.elim (leftCorrect entry) (rightCorrect entry)

theorem sourceGraphGenerated_root {V : Type*} (node : OfficialCIPNode V)
    (generated : node.GraphGenerated) :
    SourceGraphGenerated [[([], node)]] := by
  intro entry present
  simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at present
  subst entry
  exact generated

theorem SourceGraphGenerated.append {V : Type*}
    {left right : AddressedSourceLayers V}
    (leftGenerated : SourceGraphGenerated left)
    (rightGenerated : SourceGraphGenerated right) :
    SourceGraphGenerated (left ++ right) := by
  intro entry present
  rw [List.flatten_append, List.mem_append] at present
  exact present.elim (leftGenerated entry) (rightGenerated entry)

theorem sourceHistoryLengthFrom_merge {V : Type*} (rootLength : ℕ)
    (children : List (AddressedSourceLayers V))
    (childrenCorrect : ∀ child, child ∈ children →
      SourceHistoryLengthFrom (rootLength + 1) child) :
    SourceHistoryLengthFrom rootLength (mergeAddressedChildren children) := by
  intro entry present
  rw [mem_mergeAddressedChildren_flatten_iff] at present
  rcases present with ⟨child, childPresent, source, sourcePresent, rfl⟩
  have childPresent' : child.1 ∈ children :=
    List.fst_mem_of_mem_zipIdx childPresent
  have exactLength := childrenCorrect child.1 childPresent' source sourcePresent
  simp only [List.length_cons]
  omega

theorem sourceGraphGenerated_merge {V : Type*}
    (children : List (AddressedSourceLayers V))
    (childrenGenerated : ∀ child, child ∈ children → SourceGraphGenerated child) :
    SourceGraphGenerated (mergeAddressedChildren children) := by
  intro entry present
  rw [mem_mergeAddressedChildren_flatten_iff] at present
  rcases present with ⟨child, childPresent, source, sourcePresent, rfl⟩
  exact childrenGenerated child.1 (List.fst_mem_of_mem_zipIdx childPresent)
    source sourcePresent

/-- A history/address alignment turns every implementation Rule-1b projection into the
independent declarative projection pointwise. -/
theorem rule1bLayers_eq_independentRule1bLayers_of_sourceHistoryLength
    {V : Type*} (sources : AddressedSourceLayers V)
    (correct : SourceHistoryLengthFrom 2 sources)
    (generated : SourceGraphGenerated sources) :
    ExactOfficialRuleMajorKey.rule1bLayers sources =
      independentRule1bLayers sources := by
  unfold ExactOfficialRuleMajorKey.rule1bLayers mapSourceLayers
    independentRule1bLayers mapObservation
  apply List.map_congr_left
  intro layer layerPresent
  apply List.map_congr_left
  intro entry entryPresent
  apply Prod.ext
  · rfl
  · have flattened : entry ∈ sources.flatten := by
      rw [List.mem_flatten]
      exact ⟨layer, layerPresent, entryPresent⟩
    have historyLength : entry.2.history.length = entry.1.length + 2 := by
      have := correct entry flattened
      omega
    exact entry.2.rule1bRootDistance_eq_independent entry.1 historyLength
      (generated entry flattened)

end OfficialRuleMajorKey

/-! ## Recursive source-tree witness for the format-neutral compiler -/

/-- Recursive occurrence tree retained propositionally beside the sphere-major exact key.

The exact compiler stores addressed source nodes in sphere order because that is the order used by
the constitutional comparison.  This tree carries the same occurrences in parent/child form so
that declarative rooted-digraph properties can be stated without depending on that storage format.
-/
inductive OfficialCIPSourceTree (V : Type*) where
  | node (source : OfficialCIPNode V) (children : List (OfficialCIPSourceTree V))

namespace OfficialCIPSourceTree

variable {V : Type*}

/-- Source node at the root of a recursive occurrence tree. -/
def source : OfficialCIPSourceTree V → OfficialCIPNode V
  | .node sourceNode _ => sourceNode

/-- Immediate recursive child occurrences. -/
def children : OfficialCIPSourceTree V → List (OfficialCIPSourceTree V)
  | .node _ subtrees => subtrees

mutual
  /-- Preorder path/source occurrences of one recursive official source tree. -/
  def occurrences : OfficialCIPSourceTree V →
      List (OfficialSparseEntry (OfficialCIPNode V))
    | .node sourceNode subtrees =>
        ([], sourceNode) :: forestOccurrences subtrees 0

  /-- Preorder occurrences of sibling trees numbered from `start`. -/
  def forestOccurrences : List (OfficialCIPSourceTree V) → ℕ →
      List (OfficialSparseEntry (OfficialCIPNode V))
    | [], _ => []
    | tree :: trees, start =>
        (tree.occurrences.map fun entry => (start :: entry.1, entry.2)) ++
          forestOccurrences trees (start + 1)
end

/-- Sphere-major layers and a recursive tree contain exactly the same addressed source
occurrences. -/
def SourceLayersAligned
    (sources : OfficialRuleMajorKey.AddressedSourceLayers V)
    (tree : OfficialCIPSourceTree V) : Prop :=
  ∀ entry, entry ∈ sources.flatten ↔ entry ∈ tree.occurrences

mutual
  /-- Every recursive edge is one of the children returned by the supplied semantic enumerator,
and every enumerated child occurs exactly once up to sibling permutation. -/
  def GeneratedBy (enumerate : OfficialCIPNode V → List (OfficialCIPNode V)) :
      OfficialCIPSourceTree V → Prop
    | .node sourceNode subtrees =>
        (subtrees.map source).Perm (enumerate sourceNode) ∧
          ForestGeneratedBy enumerate subtrees

  /-- Pointwise generatedness for a recursive sibling forest. -/
  def ForestGeneratedBy (enumerate : OfficialCIPNode V → List (OfficialCIPNode V)) :
      List (OfficialCIPSourceTree V) → Prop
    | [] => True
    | tree :: trees => GeneratedBy enumerate tree ∧ ForestGeneratedBy enumerate trees
end

theorem forestGeneratedBy_iff_forall
    (enumerate : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ trees : List (OfficialCIPSourceTree V),
      ForestGeneratedBy enumerate trees ↔
        ∀ tree, tree ∈ trees → GeneratedBy enumerate tree
  | [] => by simp [ForestGeneratedBy]
  | tree :: trees => by
      rw [ForestGeneratedBy, forestGeneratedBy_iff_forall enumerate trees]
      simp only [List.mem_cons, forall_eq_or_imp]

/-- Forest generatedness is invariant under sibling permutation. -/
theorem ForestGeneratedBy.perm
    (enumerate : OfficialCIPNode V → List (OfficialCIPNode V))
    {left right : List (OfficialCIPSourceTree V)}
    (generated : ForestGeneratedBy enumerate left) (permutation : left.Perm right) :
    ForestGeneratedBy enumerate right := by
  rw [forestGeneratedBy_iff_forall] at generated ⊢
  intro tree present
  exact generated tree ((permutation.mem_iff).mpr present)

/-- Forest preorder occurrences have the corresponding sibling-slot decomposition. -/
theorem mem_forestOccurrences_iff_zipIdx :
    ∀ (trees : List (OfficialCIPSourceTree V)) (start : ℕ)
      (entry : OfficialSparseEntry (OfficialCIPNode V)),
      entry ∈ forestOccurrences trees start ↔
        ∃ indexed ∈ trees.zipIdx start, ∃ sourceEntry,
          sourceEntry ∈ indexed.1.occurrences ∧
            entry = (indexed.2 :: sourceEntry.1, sourceEntry.2)
  | [], start, entry => by simp [forestOccurrences]
  | tree :: trees, start, entry => by
      simp only [forestOccurrences, List.mem_append, List.mem_map]
      constructor
      · rintro (⟨sourceEntry, sourcePresent, rfl⟩ | tailPresent)
        · exact ⟨(tree, start), by simp [List.zipIdx],
            sourceEntry, sourcePresent, rfl⟩
        · rw [mem_forestOccurrences_iff_zipIdx trees (start + 1)] at tailPresent
          rcases tailPresent with
            ⟨indexed, indexedPresent, sourceEntry, sourcePresent, rfl⟩
          refine ⟨indexed, ?_, sourceEntry, sourcePresent, rfl⟩
          change indexed ∈ (tree, start) :: trees.zipIdx (start + 1)
          exact List.mem_cons_of_mem _ indexedPresent
      · rintro ⟨indexed, indexedPresent, sourceEntry, sourcePresent, rfl⟩
        change indexed ∈ (tree, start) :: trees.zipIdx (start + 1) at indexedPresent
        rcases List.mem_cons.mp indexedPresent with head | tail
        · subst indexed
          exact Or.inl ⟨sourceEntry, sourcePresent, rfl⟩
        · apply Or.inr
          rw [mem_forestOccurrences_iff_zipIdx trees (start + 1)]
          exact ⟨indexed, tail, sourceEntry, sourcePresent, rfl⟩

/-! ### Finite declarative rooted-digraph presentation -/

/-- Recursive lookup of the subtree at one ranked sibling address. -/
def subtreeAt? : OfficialCIPSourceTree V → List ℕ → Option (OfficialCIPSourceTree V)
  | tree, [] => some tree
  | .node _ subtrees, slot :: address =>
      match subtrees[slot]? with
      | none => none
      | some subtree => subtree.subtreeAt? address

/-- Source node at one ranked sibling address. -/
def sourceAtAddress? (tree : OfficialCIPSourceTree V) (address : List ℕ) :
    Option (OfficialCIPNode V) :=
  (tree.subtreeAt? address).map source

/-- Finite prefix closure of every recursive source occurrence address. -/
def hierarchyAddresses (tree : OfficialCIPSourceTree V) : List (List ℕ) :=
  [] :: tree.occurrences.flatMap fun entry => entry.1.inits

@[simp] theorem nil_mem_hierarchyAddresses (tree : OfficialCIPSourceTree V) :
    [] ∈ tree.hierarchyAddresses := by
  simp [hierarchyAddresses]

theorem dropLast_mem_hierarchyAddresses (tree : OfficialCIPSourceTree V)
    {address : List ℕ} (present : address ∈ tree.hierarchyAddresses) :
    address.dropLast ∈ tree.hierarchyAddresses := by
  simp only [hierarchyAddresses, List.mem_cons, List.mem_flatMap] at present ⊢
  rcases present with root | ⟨entry, entryPresent, hprefix⟩
  · subst address
    exact Or.inl rfl
  · refine Or.inr ⟨entry, entryPresent, ?_⟩
    rw [List.mem_inits] at hprefix ⊢
    exact address.dropLast_prefix.trans hprefix

/-- Declarative nodes are ranked sibling addresses in the finite recursive prefix closure. -/
abbrev HierarchyNode (tree : OfficialCIPSourceTree V) :=
  { address : List ℕ // address ∈ tree.hierarchyAddresses }

private noncomputable instance hierarchyNodeFintype (tree : OfficialCIPSourceTree V) :
    Fintype tree.HierarchyNode := by
  classical
  exact Fintype.ofList tree.hierarchyAddresses.attach (by intro node; simp)

/-- Total independent label at one recursive hierarchy address.  The phantom fallback makes the
conversion total for arbitrary hand-built trees; generated trees prove every carrier address has
a real source lookup. -/
def declarativeLabel [DecidableEq V] (tree : OfficialCIPSourceTree V)
    (node : tree.HierarchyNode) : DeclarativeCIP.NodeLabel V :=
  match tree.sourceAtAddress? node.1 with
  | some sourceNode => sourceNode.toDeclarativeLabel
  | none => ⟨none, .phantom node.1.length⟩

/-- Immediate parenthood is extension by one ranked sibling slot. -/
def HierarchyChild (tree : OfficialCIPSourceTree V)
    (parent node : tree.HierarchyNode) : Prop :=
  ∃ slot, node.1 = parent.1 ++ [slot]

theorem hierarchyReachable (tree : OfficialCIPSourceTree V)
    (address : List ℕ) (present : address ∈ tree.hierarchyAddresses) :
    Relation.ReflTransGen tree.HierarchyChild
      ⟨[], tree.nil_mem_hierarchyAddresses⟩ ⟨address, present⟩ := by
  induction address using List.reverseRecOn with
  | nil => exact .refl
  | append_singleton address slot inductionHypothesis =>
      have parentPresent : address ∈ tree.hierarchyAddresses := by
        have := tree.dropLast_mem_hierarchyAddresses present
        simpa using this
      exact (inductionHypothesis parentPresent).tail ⟨slot, rfl⟩

/-- Format-neutral finite rooted digraph carried by a recursive exact-key source tree. -/
noncomputable def toDeclarativeDigraph {V : Type} [DecidableEq V]
    (tree : OfficialCIPSourceTree V) : DeclarativeCIP.RootedDigraph V where
  Node := tree.HierarchyNode
  nodeFintype := hierarchyNodeFintype tree
  root := ⟨[], tree.nil_mem_hierarchyAddresses⟩
  child := tree.HierarchyChild
  label := tree.declarativeLabel
  depth := fun node => node.1.length
  root_depth := rfl
  child_depth := by
    rintro parent node ⟨slot, hnode⟩
    rw [hnode]
    simp
  reachable := by
    intro node
    exact tree.hierarchyReachable node.1 node.2

/-- Ranked sibling paths form the canonical addressing of the recursive source tree. -/
noncomputable def declarativeAddressing {V : Type} [DecidableEq V]
    (tree : OfficialCIPSourceTree V) : tree.toDeclarativeDigraph.Addressing where
  address := fun node => by
    change tree.HierarchyNode at node
    exact node.1
  address_injective := by
    intro first second same
    change tree.HierarchyNode at first second
    exact Subtype.val_injective same
  root_address := rfl
  child_iff := by
    intro parent node
    change tree.HierarchyChild parent node ↔ _
    rfl

/-- Every recorded occurrence is returned by recursive lookup at its stored address. -/
theorem subtreeAt?_eq_some_of_mem_occurrences [DecidableEq V] :
    ∀ (address : List ℕ) (tree : OfficialCIPSourceTree V)
      (sourceNode : OfficialCIPNode V),
      (address, sourceNode) ∈ tree.occurrences →
        ∃ subtree, tree.subtreeAt? address = some subtree ∧
          subtree.source = sourceNode
  | [], .node root subtrees, sourceNode, present => by
      simp only [occurrences, List.mem_cons] at present
      rcases present with atRoot | inForest
      · have sourceEq : sourceNode = root := (Prod.mk.inj atRoot).2
        subst sourceNode
        exact ⟨.node root subtrees, rfl, rfl⟩
      · rw [mem_forestOccurrences_iff_zipIdx] at inForest
        rcases inForest with
          ⟨indexed, _indexedPresent, sourceEntry, _sourcePresent, impossible⟩
        have addressEq := congrArg Prod.fst impossible
        simp at addressEq
  | slot :: address, .node root subtrees, sourceNode, present => by
      simp only [occurrences, List.mem_cons] at present
      rcases present with atRoot | inForest
      · have addressEq := congrArg Prod.fst atRoot
        simp at addressEq
      · rw [mem_forestOccurrences_iff_zipIdx] at inForest
        rcases inForest with
          ⟨⟨child, childSlot⟩, childPresent, ⟨childAddress, childSource⟩,
            childSourcePresent, entryEq⟩
        have addressEq := congrArg Prod.fst entryEq
        have sourceEq := congrArg Prod.snd entryEq
        simp only at addressEq sourceEq
        injection addressEq with slotEq tailEq
        subst childSlot
        subst childAddress
        subst childSource
        have slotLt : slot < subtrees.length := by
          simpa using List.snd_lt_of_mem_zipIdx childPresent
        have childGet : subtrees[slot]? = some child := by
          rw [List.getElem?_eq_getElem slotLt]
          have childEq := List.fst_eq_of_mem_zipIdx childPresent
          simpa using childEq.symm
        obtain ⟨descendant, descendantLookup, descendantSource⟩ :=
          subtreeAt?_eq_some_of_mem_occurrences
            address child sourceNode childSourcePresent
        refine ⟨descendant, ?_, descendantSource⟩
        simp [subtreeAt?, childGet, descendantLookup]

/-- Recursive lookup composes along concatenated sibling addresses. -/
theorem subtreeAt?_append (tree : OfficialCIPSourceTree V)
    (first second : List ℕ) :
    tree.subtreeAt? (first ++ second) =
      (tree.subtreeAt? first).bind fun subtree => subtree.subtreeAt? second := by
  induction first generalizing tree with
  | nil => simp [subtreeAt?]
  | cons slot first inductionHypothesis =>
      cases tree with
      | node sourceNode subtrees =>
          simp only [List.cons_append, subtreeAt?]
          cases childLookup : subtrees[slot]? with
          | none => simp
          | some child =>
              simp only
              exact inductionHypothesis child

/-- Every address in the finite prefix-closure carrier resolves to an actual recursive subtree. -/
theorem exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses [DecidableEq V]
    (tree : OfficialCIPSourceTree V) (address : List ℕ)
    (present : address ∈ tree.hierarchyAddresses) :
    ∃ subtree, tree.subtreeAt? address = some subtree := by
  simp only [hierarchyAddresses, List.mem_cons, List.mem_flatMap] at present
  rcases present with root | ⟨entry, entryPresent, hprefix⟩
  · subst address
    exact ⟨tree, rfl⟩
  · rw [List.mem_inits] at hprefix
    rcases hprefix with ⟨suffix, entryAddress⟩
    obtain ⟨descendant, descendantLookup, _descendantSource⟩ :=
      subtreeAt?_eq_some_of_mem_occurrences entry.1 tree entry.2 entryPresent
    rw [← entryAddress, tree.subtreeAt?_append] at descendantLookup
    cases prefixLookup : tree.subtreeAt? address with
    | none => simp [prefixLookup] at descendantLookup
    | some subtree => exact ⟨subtree, rfl⟩

/-- Every declarative carrier node therefore has a concrete recursive source witness. -/
theorem exists_source_lookup [DecidableEq V]
    (tree : OfficialCIPSourceTree V) (node : tree.HierarchyNode) :
    ∃ subtree, tree.subtreeAt? node.1 = some subtree ∧
      tree.sourceAtAddress? node.1 = some subtree.source := by
  obtain ⟨subtree, lookup⟩ :=
    tree.exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses node.1 node.2
  exact ⟨subtree, lookup, by simp [sourceAtAddress?, lookup]⟩

/-- Generatedness descends through every successful recursive subtree lookup. -/
theorem GeneratedBy.of_subtreeAt?
    (enumerate : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ (address : List ℕ) (tree subtree : OfficialCIPSourceTree V),
      tree.GeneratedBy enumerate → tree.subtreeAt? address = some subtree →
        subtree.GeneratedBy enumerate
  | [], tree, subtree, generated, lookup => by
      simp only [subtreeAt?] at lookup
      exact (Option.some.inj lookup) ▸ generated
  | slot :: address, .node sourceNode subtrees, subtree, generated, lookup => by
      simp only [subtreeAt?] at lookup
      cases childLookup : subtrees[slot]? with
      | none => simp [childLookup] at lookup
      | some child =>
          rw [childLookup] at lookup
          have childPresent : child ∈ subtrees :=
            List.mem_iff_getElem?.2 ⟨slot, childLookup⟩
          have forestGenerated : ForestGeneratedBy enumerate subtrees := generated.2
          have childGenerated :=
            (forestGeneratedBy_iff_forall enumerate subtrees).1
              forestGenerated child childPresent
          exact GeneratedBy.of_subtreeAt? enumerate
            address child subtree childGenerated lookup

/-- A recursive hierarchy edge is exactly an edge returned by the semantic child enumerator. -/
theorem GeneratedBy.source_mem_of_hierarchyChild [DecidableEq V]
    (tree : OfficialCIPSourceTree V)
    (enumerate : OfficialCIPNode V → List (OfficialCIPNode V))
    (generated : tree.GeneratedBy enumerate)
    (parent child : tree.HierarchyNode)
    (parentTree childTree : OfficialCIPSourceTree V)
    (parentLookup : tree.subtreeAt? parent.1 = some parentTree)
    (childLookup : tree.subtreeAt? child.1 = some childTree)
    (edge : tree.HierarchyChild parent child) :
    childTree.source ∈ enumerate parentTree.source := by
  rcases edge with ⟨slot, childAddress⟩
  have childWithin : parentTree.subtreeAt? [slot] = some childTree := by
    rw [childAddress, tree.subtreeAt?_append, parentLookup] at childLookup
    simpa using childLookup
  have parentGenerated := generated.of_subtreeAt? enumerate parent.1 tree parentTree parentLookup
  cases parentTree with
  | node parentSource subtrees =>
      simp only [subtreeAt?] at childWithin
      cases slotLookup : subtrees[slot]? with
      | none => simp [slotLookup] at childWithin
      | some selected =>
          rw [slotLookup] at childWithin
          have selectedEq : selected = childTree := Option.some.inj childWithin
          subst selected
          have childPresent : childTree ∈ subtrees :=
            List.mem_iff_getElem?.2 ⟨slot, slotLookup⟩
          have sourcePresent : childTree.source ∈ subtrees.map source := by
            exact List.mem_map.mpr ⟨childTree, childPresent, rfl⟩
          exact (parentGenerated.1.mem_iff).mp sourcePresent

/-- Successful lookup exposes the exact independent declarative label at that graph node. -/
theorem declarativeLabel_eq_of_subtreeAt? [DecidableEq V]
    (tree subtree : OfficialCIPSourceTree V) (node : tree.HierarchyNode)
    (lookup : tree.subtreeAt? node.1 = some subtree) :
    tree.declarativeLabel node = subtree.source.toDeclarativeLabel := by
  simp [declarativeLabel, sourceAtAddress?, lookup]

end OfficialCIPSourceTree

private theorem forall₂_exists_left_of_mem_right
    {α β : Type*} {relation : α → β → Prop}
    {left : List α} {right : List β}
    (related : List.Forall₂ relation left right)
    (value : β) (present : value ∈ right) :
    ∃ source, source ∈ left ∧ relation source value := by
  induction related with
  | nil => simp at present
  | cons headRelated tailRelated inductionHypothesis =>
      rcases List.mem_cons.mp present with rfl | tailPresent
      · exact ⟨_, by simp, headRelated⟩
      · obtain ⟨source, sourcePresent, sourceRelated⟩ :=
          inductionHypothesis tailPresent
        exact ⟨source, by simp [sourcePresent], sourceRelated⟩

private theorem forall₂_zipIdx_right
    {α β : Type*} {relation : α → β → Prop}
    {left : List α} {right : List β}
    (related : List.Forall₂ relation left right)
    (indexed : α × ℕ) (present : indexed ∈ left.zipIdx) :
    ∃ value, (value, indexed.2) ∈ right.zipIdx ∧
      relation indexed.1 value := by
  have leftLt : indexed.2 < left.length := by
    simpa using List.snd_lt_of_mem_zipIdx present
  have rightLt : indexed.2 < right.length := by
    rw [← related.length_eq]
    exact leftLt
  let value := right.get ⟨indexed.2, rightLt⟩
  have relatedAt := related.get leftLt rightLt
  have leftEq : left.get ⟨indexed.2, leftLt⟩ = indexed.1 := by
    have fromZip := List.fst_eq_of_mem_zipIdx present
    simpa using fromZip.symm
  rw [leftEq] at relatedAt
  refine ⟨value, ?_, relatedAt⟩
  apply List.mem_iff_getElem.mpr
  refine ⟨indexed.2, ?_, ?_⟩
  · simpa using rightLt
  · rw [List.getElem_zipIdx]
    simp [value]

private theorem mergeAddressedChildren_alignedWithForest
    {V : Type*}
    (sources : List (OfficialRuleMajorKey.AddressedSourceLayers V))
    (trees : List (OfficialCIPSourceTree V))
    (aligned : List.Forall₂ OfficialCIPSourceTree.SourceLayersAligned sources trees)
    (entry : OfficialSparseEntry (OfficialCIPNode V)) :
    entry ∈ (OfficialRuleMajorKey.mergeAddressedChildren sources).flatten ↔
      entry ∈ OfficialCIPSourceTree.forestOccurrences trees 0 := by
  rw [OfficialRuleMajorKey.mem_mergeAddressedChildren_flatten_iff,
    OfficialCIPSourceTree.mem_forestOccurrences_iff_zipIdx]
  constructor
  · rintro ⟨childSources, childPresent, sourceEntry, sourcePresent, rfl⟩
    obtain ⟨tree, treePresent, childAligned⟩ :=
      forall₂_zipIdx_right aligned childSources childPresent
    refine ⟨(tree, childSources.2), treePresent, sourceEntry, ?_, rfl⟩
    exact (childAligned sourceEntry).mp sourcePresent
  · rintro ⟨tree, treePresent, sourceEntry, sourcePresent, rfl⟩
    have flipped : List.Forall₂ (flip OfficialCIPSourceTree.SourceLayersAligned)
        trees sources :=
      List.Forall₂.flip
        (R := flip OfficialCIPSourceTree.SourceLayersAligned) aligned
    obtain ⟨childSources, childPresent, childAligned⟩ :=
      forall₂_zipIdx_right flipped tree treePresent
    refine ⟨(childSources, tree.2), childPresent, sourceEntry, ?_, rfl⟩
    exact (childAligned sourceEntry).mpr sourcePresent

private theorem collectGeneratedSourceTrees
    {V : Type*}
    (enumerate : OfficialCIPNode V → List (OfficialCIPNode V))
    {relation : OfficialCIPNode V →
      OfficialRuleMajorKey.AddressedSourceLayers V → Prop}
    {complete : OfficialCIPNode V → Prop}
    (build : ∀ child sources, relation child sources → complete child →
      ∃ tree : OfficialCIPSourceTree V,
        OfficialCIPSourceTree.SourceLayersAligned sources tree ∧
          OfficialCIPSourceTree.GeneratedBy enumerate tree ∧
          tree.source = child) :
    ∀ {children : List (OfficialCIPNode V)}
      {sources : List (OfficialRuleMajorKey.AddressedSourceLayers V)},
      List.Forall₂ relation children sources →
      (∀ child, child ∈ children → complete child) →
      ∃ trees : List (OfficialCIPSourceTree V),
        List.Forall₂
          (fun child tree => tree.source = child ∧
            OfficialCIPSourceTree.GeneratedBy enumerate tree)
          children trees ∧
        List.Forall₂ OfficialCIPSourceTree.SourceLayersAligned sources trees
  | _, _, .nil, _ => ⟨[], .nil, .nil⟩
  | _, _, .cons headRelated tailRelated, allComplete => by
      obtain ⟨tree, treeAligned, treeGenerated, treeRoot⟩ :=
        build _ _ headRelated (allComplete _ (by simp))
      obtain ⟨trees, treesGenerated, treesAligned⟩ :=
        collectGeneratedSourceTrees enumerate build tailRelated (by
          intro child present
          exact allComplete child (by simp [present]))
      exact ⟨tree :: trees,
        .cons ⟨treeRoot, treeGenerated⟩ treesGenerated,
        .cons treeAligned treesAligned⟩

private theorem map_source_eq_of_forall₂_generated
    {V : Type*}
    (enumerate : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ {nodes : List (OfficialCIPNode V)}
      {trees : List (OfficialCIPSourceTree V)},
      List.Forall₂
        (fun child tree => tree.source = child ∧
          OfficialCIPSourceTree.GeneratedBy enumerate tree)
        nodes trees →
      trees.map OfficialCIPSourceTree.source = nodes
  | _, _, .nil => rfl
  | _, _, .cons realized tail => by
      simp [realized.1, map_source_eq_of_forall₂_generated enumerate tail]

namespace ExactOfficialRuleMajorKey

/-- Independent recursive addressed expansion preserves exact node-history/address alignment when
every child enumerator result is a one-step extension. -/
theorem DeclarativeAddressedExpansion.sourceHistoryLengthFrom
    {V : Type*} [Fintype V] [DecidableEq V]
    (molecule : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V))
    (childHistory : ∀ parent child, child ∈ children parent →
      child.history.length = parent.history.length + 1) :
    ∀ fuel node sources,
      DeclarativeAddressedExpansion molecule children fuel node sources →
        OfficialRuleMajorKey.SourceHistoryLengthFrom node.history.length sources
  | 0, node, sources, expansion => by
      simp only [DeclarativeAddressedExpansion] at expansion
      subst sources
      exact OfficialRuleMajorKey.sourceHistoryLengthFrom_root node
  | fuel + 1, node, sources, expansion => by
      by_cases terminal : children node = []
      · simp [DeclarativeAddressedExpansion, terminal] at expansion
        subst sources
        exact OfficialRuleMajorKey.sourceHistoryLengthFrom_root node
      · simp only [DeclarativeAddressedExpansion, terminal, ↓reduceIte] at expansion
        rcases expansion with
          ⟨rawChildren, rankedChildren, recursivelyExpanded,
            rankedPermutation, _descending, rfl⟩
        apply OfficialRuleMajorKey.SourceHistoryLengthFrom.append
          (OfficialRuleMajorKey.sourceHistoryLengthFrom_root node)
        apply OfficialRuleMajorKey.sourceHistoryLengthFrom_merge
        intro childSources childSourcesPresent
        have rawPresent : childSources ∈ rawChildren :=
          (rankedPermutation.mem_iff).mp childSourcesPresent
        obtain ⟨child, childPresent, childExpansion⟩ :=
          forall₂_exists_left_of_mem_right recursivelyExpanded childSources rawPresent
        have recursivelyCorrect :=
          DeclarativeAddressedExpansion.sourceHistoryLengthFrom molecule children childHistory
            fuel child childSources childExpansion
        have oneLonger := childHistory node child childPresent
        simpa [oneLonger] using recursivelyCorrect

/-- The same recursive expansion contains no injected placeholder nodes when its root and every
enumerated child are graph-generated. -/
theorem DeclarativeAddressedExpansion.sourceGraphGenerated
    {V : Type*} [Fintype V] [DecidableEq V]
    (molecule : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V))
    (childGenerated : ∀ parent child, child ∈ children parent → child.GraphGenerated) :
    ∀ fuel node sources,
      node.GraphGenerated →
      DeclarativeAddressedExpansion molecule children fuel node sources →
        OfficialRuleMajorKey.SourceGraphGenerated sources
  | 0, node, sources, nodeGenerated, expansion => by
      simp only [DeclarativeAddressedExpansion] at expansion
      subst sources
      exact OfficialRuleMajorKey.sourceGraphGenerated_root node nodeGenerated
  | fuel + 1, node, sources, nodeGenerated, expansion => by
      by_cases terminal : children node = []
      · simp [DeclarativeAddressedExpansion, terminal] at expansion
        subst sources
        exact OfficialRuleMajorKey.sourceGraphGenerated_root node nodeGenerated
      · simp only [DeclarativeAddressedExpansion, terminal, ↓reduceIte] at expansion
        rcases expansion with
          ⟨rawChildren, rankedChildren, recursivelyExpanded,
            rankedPermutation, _descending, rfl⟩
        apply OfficialRuleMajorKey.SourceGraphGenerated.append
          (OfficialRuleMajorKey.sourceGraphGenerated_root node nodeGenerated)
        apply OfficialRuleMajorKey.sourceGraphGenerated_merge
        intro childSources childSourcesPresent
        have rawPresent : childSources ∈ rawChildren :=
          (rankedPermutation.mem_iff).mp childSourcesPresent
        obtain ⟨child, childPresent, childExpansion⟩ :=
          forall₂_exists_left_of_mem_right recursivelyExpanded childSources rawPresent
        exact DeclarativeAddressedExpansion.sourceGraphGenerated molecule children
          childGenerated fuel child childSources
          (childGenerated node child childPresent) childExpansion

/-- A complete declarative addressed expansion has a recursive source-tree presentation with the
same occurrences and exactly the enumerated semantic child edges.  Ranked sibling permutation
changes only slot names; it cannot fabricate, drop, or reparent a source occurrence. -/
theorem DeclarativeAddressedExpansion.generatedSourceTree
    {V : Type*} [Fintype V] [DecidableEq V]
    (molecule : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ fuel node sources,
      MoleculeGraph.OfficialExpansionCompleteWithin children fuel node →
      DeclarativeAddressedExpansion molecule children fuel node sources →
      ∃ tree : OfficialCIPSourceTree V,
        OfficialCIPSourceTree.SourceLayersAligned sources tree ∧
          OfficialCIPSourceTree.GeneratedBy children tree ∧
          tree.source = node
  | 0, sourceNode, sources, complete, expansion => by
      simp only [DeclarativeAddressedExpansion] at expansion
      subst sources
      refine ⟨.node sourceNode [], ?_, ?_, rfl⟩
      · intro entry
        simp [OfficialCIPSourceTree.occurrences,
          OfficialCIPSourceTree.forestOccurrences]
      · simp only [OfficialCIPSourceTree.GeneratedBy,
          OfficialCIPSourceTree.ForestGeneratedBy, List.map_nil]
        change children sourceNode = [] at complete
        constructor
        · simp [complete]
        · trivial
  | fuel + 1, sourceNode, sources, complete, expansion => by
      by_cases terminal : children sourceNode = []
      · simp [DeclarativeAddressedExpansion, terminal] at expansion
        subst sources
        refine ⟨.node sourceNode [], ?_, ?_, rfl⟩
        · intro entry
          simp [OfficialCIPSourceTree.occurrences,
            OfficialCIPSourceTree.forestOccurrences]
        · simp [OfficialCIPSourceTree.GeneratedBy,
            OfficialCIPSourceTree.ForestGeneratedBy, terminal]
      · simp only [DeclarativeAddressedExpansion, terminal, ↓reduceIte] at expansion
        rcases expansion with
          ⟨rawChildren, rankedChildren, recursivelyExpanded,
            rankedPermutation, _descending, rfl⟩
        have childrenComplete : ∀ child, child ∈ children sourceNode →
            MoleculeGraph.OfficialExpansionCompleteWithin children fuel child := by
          simpa only [MoleculeGraph.OfficialExpansionCompleteWithin] using complete
        obtain ⟨rawTrees, rawTreesGenerated, rawTreesAligned⟩ :=
          collectGeneratedSourceTrees children
            (fun child childSources childExpansion childComplete =>
              DeclarativeAddressedExpansion.generatedSourceTree molecule children
                fuel child childSources childComplete childExpansion)
            recursivelyExpanded childrenComplete
        obtain ⟨rankedTrees, rankedTreesAligned, rankedTreesPermutation⟩ :=
          List.perm_comp_forall₂ rankedPermutation rawTreesAligned
        have rawForestGenerated :
            OfficialCIPSourceTree.ForestGeneratedBy children rawTrees := by
          rw [OfficialCIPSourceTree.forestGeneratedBy_iff_forall]
          intro tree treePresent
          obtain ⟨child, _childPresent, realized⟩ :=
            forall₂_exists_left_of_mem_right
              rawTreesGenerated tree treePresent
          exact realized.2
        have rankedForestGenerated :
            OfficialCIPSourceTree.ForestGeneratedBy children rankedTrees :=
          rawForestGenerated.perm children rankedTreesPermutation.symm
        have rawRoots : rawTrees.map OfficialCIPSourceTree.source = children sourceNode := by
          exact map_source_eq_of_forall₂_generated children rawTreesGenerated
        have rankedRoots :
            (rankedTrees.map OfficialCIPSourceTree.source).Perm (children sourceNode) :=
          (rankedTreesPermutation.map OfficialCIPSourceTree.source).trans
            (rawRoots ▸ List.Perm.refl (children sourceNode))
        refine ⟨.node sourceNode rankedTrees, ?_, ?_, rfl⟩
        · intro entry
          change entry ∈
              ([[([], sourceNode)]] ++
                OfficialRuleMajorKey.mergeAddressedChildren rankedChildren).flatten ↔
            entry ∈ ([], sourceNode) ::
              OfficialCIPSourceTree.forestOccurrences rankedTrees 0
          rw [List.flatten_append]
          simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
            List.mem_append, List.mem_cons]
          rw [mergeAddressedChildren_alignedWithForest
            rankedChildren rankedTrees rankedTreesAligned entry]
          simp
        · exact ⟨rankedRoots, rankedForestGenerated⟩

end ExactOfficialRuleMajorKey

namespace CertifiedLocalizedCIPInput

private theorem firstIndexOf?_eq_some_of_mem
    {V : Type*} [DecidableEq V] (atom : V) :
    ∀ {values : List V}, atom ∈ values →
      ∃ index, firstIndexOf? atom values = some index
  | [], present => by simp at present
  | value :: values, present => by
      by_cases head : value = atom
      · subst value
        exact ⟨0, firstIndexOf?_cons_self atom values⟩
      · have tailPresent : atom ∈ values := by
          exact (List.mem_cons.mp present).resolve_left (Ne.symm head)
        obtain ⟨index, found⟩ := firstIndexOf?_eq_some_of_mem atom tailPresent
        exact ⟨index + 1, by simp [firstIndexOf?, head, found]⟩

private theorem firstIndexOf?_eq_some_imp_getElem?
    {V : Type*} [DecidableEq V] (atom : V) :
    ∀ (values : List V) (index : ℕ),
      firstIndexOf? atom values = some index → values[index]? = some atom
  | [], index, found => by simp [firstIndexOf?] at found
  | value :: values, index, found => by
      unfold firstIndexOf? at found
      by_cases head : value = atom
      · simp [head] at found
        subst index
        simp [head]
      · simp only [head, ↓reduceIte, Option.map_eq_some_iff] at found
        obtain ⟨tailIndex, tailFound, rfl⟩ := found
        simpa using firstIndexOf?_eq_some_imp_getElem?
          atom values tailIndex tailFound

/-- Every runtime official child extends the parent's stored branch history by exactly one atom. -/
theorem executableOfficialCIPChildren_history_length
    (input : CertifiedLocalizedCIPInput)
    (parent child : OfficialCIPNode input.Atom)
    (present : child ∈ input.executableOfficialCIPChildren parent) :
    child.history.length = parent.history.length + 1 := by
  by_cases duplicate : parent.isDuplicateLeaf = true
  · simp [executableOfficialCIPChildren, duplicate] at present
  · rw [executableOfficialCIPChildren, if_neg (by simpa using duplicate),
      List.mem_map] at present
    obtain ⟨copy, _copyPresent, rfl⟩ := present
    exact OfficialCIPNode.extend_history_length parent copy.1 copy.2

/-- Every runtime child is literally a one-step `OfficialCIPNode.extend` of its parent. -/
theorem executableOfficialCIPChildren_extension
    (input : CertifiedLocalizedCIPInput)
    (parent child : OfficialCIPNode input.Atom)
    (present : child ∈ input.executableOfficialCIPChildren parent) :
    ∃ atom copyIndex, child = parent.extend atom copyIndex := by
  by_cases duplicate : parent.isDuplicateLeaf = true
  · simp [executableOfficialCIPChildren, duplicate] at present
  · rw [executableOfficialCIPChildren, if_neg (by simpa using duplicate),
      List.mem_map] at present
    obtain ⟨copy, _copyPresent, rfl⟩ := present
    exact ⟨copy.1, copy.2, rfl⟩

/-- Runtime molecular-graph expansion never injects explicit phantom, lone-pair, or auxiliary
provenance into the constitutional hierarchy. -/
theorem executableOfficialCIPChildren_graphGenerated
    (input : CertifiedLocalizedCIPInput)
    (parent child : OfficialCIPNode input.Atom)
    (present : child ∈ input.executableOfficialCIPChildren parent) :
    child.GraphGenerated := by
  by_cases duplicate : parent.isDuplicateLeaf = true
  · simp [executableOfficialCIPChildren, duplicate] at present
  · rw [executableOfficialCIPChildren, if_neg (by simpa using duplicate),
      List.mem_map] at present
    obtain ⟨copy, _copyPresent, rfl⟩ := present
    by_cases realCopy : copy.2 = 0
    · by_cases ring : copy.1 ∈ parent.history <;>
        simp [OfficialCIPNode.GraphGenerated, OfficialCIPNode.extend,
          OfficialCIPNode.childProvenance, realCopy, ring]
    · simp [OfficialCIPNode.GraphGenerated, OfficialCIPNode.extend,
        OfficialCIPNode.childProvenance, realCopy]

/-- In a generated recursive exact-key tree, stored source-history length is exactly the
declarative address depth plus the ligand root edge's two atoms. -/
theorem generatedSourceTree_history_length
    (input : CertifiedLocalizedCIPInput)
    (tree : OfficialCIPSourceTree input.Atom)
    (center ligand : input.Atom)
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) (subtree : OfficialCIPSourceTree input.Atom)
    (lookup : tree.subtreeAt? node.1 = some subtree) :
    subtree.source.history.length = node.1.length + 2 := by
  have reachable := tree.toDeclarativeDigraph.reachable node
  change Relation.ReflTransGen tree.HierarchyChild
    ⟨[], tree.nil_mem_hierarchyAddresses⟩ node at reachable
  revert subtree
  induction reachable with
  | refl =>
      intro subtree lookup
      simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
      have same : tree = subtree := Option.some.inj lookup
      rw [← same, root]
      rfl
  | @tail parent node path edge inductionHypothesis =>
      intro childTree childLookup
      obtain ⟨parentTree, parentLookup, _parentSourceLookup⟩ :=
        tree.exists_source_lookup parent
      have childPresent := generated.source_mem_of_hierarchyChild
        tree input.executableOfficialCIPChildren parent node parentTree childTree
        parentLookup childLookup edge
      have parentLength := inductionHypothesis parentTree parentLookup
      have childLength := input.executableOfficialCIPChildren_history_length
        parentTree.source childTree.source childPresent
      rcases edge with ⟨slot, childAddress⟩
      rw [childAddress]
      simp only [List.length_append, List.length_singleton]
      omega

/-- Every stored reversed-history position in a generated source tree is realized by exactly the
external stereocenter, the current node, or a represented strict ancestor.  This is the semantic
bridge from the runtime ring-history payload to the independent rooted-digraph hierarchy. -/
theorem generatedSourceTree_history_index_realized
    (input : CertifiedLocalizedCIPInput)
    (tree : OfficialCIPSourceTree input.Atom)
    (center ligand : input.Atom)
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand)
    (node : tree.HierarchyNode) (subtree : OfficialCIPSourceTree input.Atom)
    (lookup : tree.subtreeAt? node.1 = some subtree) :
    ∀ index atom, subtree.source.history.reverse[index]? = some atom →
      (index = 0 ∧ atom = center) ∨
      (index = node.1.length + 1 ∧ subtree.source.current? = some atom) ∨
      ∃ ancestor : tree.HierarchyNode,
        Relation.TransGen tree.HierarchyChild ancestor node ∧
          (tree.declarativeLabel ancestor).atom? = some atom ∧
          index = ancestor.1.length + 1 := by
  have reachable := tree.toDeclarativeDigraph.reachable node
  change Relation.ReflTransGen tree.HierarchyChild
    ⟨[], tree.nil_mem_hierarchyAddresses⟩ node at reachable
  revert subtree
  induction reachable with
  | refl =>
      intro subtree lookup index atom observed
      simp only [OfficialCIPSourceTree.subtreeAt?] at lookup
      have same : tree = subtree := Option.some.inj lookup
      subst subtree
      rw [root] at observed
      have bound : index < 2 := by
        have := List.getElem?_eq_some_iff.mp observed
        simpa [OfficialCIPNode.rootFromEdge] using this.1
      have cases : index = 0 ∨ index = 1 := by omega
      rcases cases with rfl | rfl
      · left
        exact ⟨rfl, by simpa [OfficialCIPNode.rootFromEdge] using observed.symm⟩
      · right; left
        refine ⟨rfl, ?_⟩
        rw [root]
        simpa [OfficialCIPNode.rootFromEdge] using observed
  | @tail parent node path edge inductionHypothesis =>
      intro childTree childLookup index atom observed
      obtain ⟨parentTree, parentLookup, _parentSourceLookup⟩ :=
        tree.exists_source_lookup parent
      have childPresent := generated.source_mem_of_hierarchyChild
        tree input.executableOfficialCIPChildren parent node parentTree childTree
        parentLookup childLookup edge
      obtain ⟨next, copyIndex, childIdentity⟩ :=
        input.executableOfficialCIPChildren_extension
          parentTree.source childTree.source childPresent
      have parentLength := input.generatedSourceTree_history_length tree center ligand
        generated root parent parentTree parentLookup
      rw [childIdentity, OfficialCIPNode.extend_history, List.reverse_cons,
        List.getElem?_append] at observed
      by_cases before : index < parentTree.source.history.reverse.length
      · simp only [before, ↓reduceIte] at observed
        rcases inductionHypothesis parentTree parentLookup index atom observed with
          atCenter | atParentOrAncestor
        · exact Or.inl atCenter
        · rcases atParentOrAncestor with atParent | atAncestor
          · right; right
            refine ⟨parent, Relation.TransGen.single edge, ?_, atParent.1⟩
            rw [tree.declarativeLabel_eq_of_subtreeAt? parentTree parent parentLookup]
            simpa [OfficialCIPNode.toDeclarativeLabel] using atParent.2
          · rcases atAncestor with ⟨ancestor, ancestorPath, ancestorAtom, distance⟩
            right; right
            exact ⟨ancestor, ancestorPath.tail edge, ancestorAtom, distance⟩
      · simp only [before, ↓reduceIte] at observed
        have tailBound : index - parentTree.source.history.reverse.length < 1 :=
          (List.getElem?_eq_some_iff.mp observed).1
        have indexEq : index = parentTree.source.history.length := by
          simp only [List.length_reverse] at before tailBound
          omega
        have atomEq : atom = next := by
          subst index
          simpa using observed.symm
        right; left
        rcases edge with ⟨slot, address⟩
        constructor
        · rw [address]
          simp only [List.length_append, List.length_singleton]
          omega
        · simp [childIdentity, atomEq]

/-- Every runtime multiple-bond duplicate carries the parent node's sphere, exactly matching the
local payload clause of `DeclarativeCIP.RootedDigraph.DuplicateDistancesCorrect`. -/
theorem executableOfficialCIPChildren_multipleBondDuplicate_distance
    (input : CertifiedLocalizedCIPInput)
    (parent child : OfficialCIPNode input.Atom)
    (present : child ∈ input.executableOfficialCIPChildren parent)
    (distance : ℕ)
    (provenance : child.provenance = .multipleBondDuplicate distance) :
    distance = parent.depth := by
  by_cases duplicate : parent.isDuplicateLeaf = true
  · simp [executableOfficialCIPChildren, duplicate] at present
  · rw [executableOfficialCIPChildren, if_neg (by simpa using duplicate),
      List.mem_map] at present
    obtain ⟨copy, _copyPresent, rfl⟩ := present
    by_cases realCopy : copy.2 = 0
    · by_cases ring : copy.1 ∈ parent.history <;>
        simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
          realCopy, ring] at provenance
    · simpa [OfficialCIPNode.extend, OfficialCIPNode.childProvenance,
        realCopy] using provenance.symm

/-- Every runtime ring duplicate carries exactly the first sphere at which its atom occurred in
the reversed parent history.  This is stronger than retaining an arbitrary cached payload: it
ties the generated duplicate to the first branch-history occurrence that the declarative
strict-ancestor proof interprets. -/
theorem executableOfficialCIPChildren_ringDuplicate_firstIndex
    (input : CertifiedLocalizedCIPInput)
    (parent child : OfficialCIPNode input.Atom)
    (present : child ∈ input.executableOfficialCIPChildren parent)
    (atom : input.Atom) (distance : ℕ)
    (current : child.current? = some atom)
    (provenance : child.provenance = .ringDuplicate distance) :
    firstIndexOf? atom parent.history.reverse = some distance := by
  by_cases duplicate : parent.isDuplicateLeaf = true
  · simp [executableOfficialCIPChildren, duplicate] at present
  · rw [executableOfficialCIPChildren, if_neg (by simpa using duplicate),
      List.mem_map] at present
    obtain ⟨copy, _copyPresent, rfl⟩ := present
    rcases copy with ⟨next, copyIndex⟩
    simp only [OfficialCIPNode.extend_current?, Option.some.injEq] at current
    subst next
    by_cases realCopy : copyIndex = 0
    · subst copyIndex
      by_cases ring : atom ∈ parent.history
      · have payload : distance = parent.duplicateRootDistance atom := by
          simpa [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, ring] using
            provenance.symm
        obtain ⟨index, found⟩ := firstIndexOf?_eq_some_of_mem atom
          (List.mem_reverse.mpr ring)
        have distanceEq : distance = index := by
          rw [payload]
          simp [OfficialCIPNode.duplicateRootDistance, found]
        simpa [distanceEq] using found
      · simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, ring] at provenance
    · simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, realCopy] at provenance

/-- A generated exact-key source tree satisfies the full independent duplicate-distance
semantics under its canonical ranked-sibling addressing.  Multiple-bond copies are rooted at the
parent sphere; ring copies resolve to the external center or a strict represented ancestor. -/
theorem generatedSourceTree_duplicateDistancesCorrect
    (input : CertifiedLocalizedCIPInput)
    (tree : OfficialCIPSourceTree input.Atom)
    (center ligand : input.Atom)
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    (root : tree.source = OfficialCIPNode.rootFromEdge center ligand) :
    DeclarativeCIP.RootedDigraph.DuplicateDistancesCorrect
      tree.toDeclarativeDigraph center tree.declarativeAddressing := by
  intro parent child edge
  obtain ⟨parentTree, parentLookup, _parentSourceLookup⟩ :=
    tree.exists_source_lookup parent
  obtain ⟨childTree, childLookup, _childSourceLookup⟩ :=
    tree.exists_source_lookup child
  have childPresent := generated.source_mem_of_hierarchyChild
    tree input.executableOfficialCIPChildren parent child parentTree childTree
    parentLookup childLookup edge
  have labelIdentity :=
    tree.declarativeLabel_eq_of_subtreeAt? childTree child childLookup
  cases label : tree.toDeclarativeDigraph.label child with
  | mk atom? provenance =>
      cases provenance with
      | realAtom => trivial
      | multipleBondDuplicate distance =>
          have sourceProvenance : childTree.source.provenance =
              OfficialCIPNodeProvenance.multipleBondDuplicate distance := by
            have observed := congrArg DeclarativeCIP.NodeLabel.provenance label
            rw [show tree.toDeclarativeDigraph.label child = tree.declarativeLabel child by rfl,
              labelIdentity] at observed
            cases source : childTree.source.provenance with
            | realAtom =>
                simp [OfficialCIPNode.toDeclarativeLabel,
                  OfficialCIPNodeProvenance.toDeclarative, source] at observed
            | multipleBondDuplicate actual =>
                simp [OfficialCIPNode.toDeclarativeLabel,
                  OfficialCIPNodeProvenance.toDeclarative, source] at observed
                subst actual
                rfl
            | ringDuplicate actual =>
                simp [OfficialCIPNode.toDeclarativeLabel,
                  OfficialCIPNodeProvenance.toDeclarative, source] at observed
            | placeholder kind actual =>
                cases kind <;> simp [OfficialCIPNode.toDeclarativeLabel,
                  OfficialCIPNodeProvenance.toDeclarative, source] at observed
          have payload := input.executableOfficialCIPChildren_multipleBondDuplicate_distance
            parentTree.source childTree.source childPresent distance sourceProvenance
          have parentLength := input.generatedSourceTree_history_length tree center ligand
            generated root parent parentTree parentLookup
          change distance = parent.1.length + 1
          rw [payload]
          unfold OfficialCIPNode.depth
          omega
      | ringDuplicate distance =>
          cases atom? with
          | none =>
              have atomless := congrArg DeclarativeCIP.NodeLabel.atom? label
              rw [show tree.toDeclarativeDigraph.label child = tree.declarativeLabel child by rfl,
                labelIdentity] at atomless
              obtain ⟨next, copyIndex, childIdentity⟩ :=
                input.executableOfficialCIPChildren_extension
                  parentTree.source childTree.source childPresent
              simp [OfficialCIPNode.toDeclarativeLabel, childIdentity] at atomless
          | some atom =>
              have current : childTree.source.current? = some atom := by
                have observed := congrArg DeclarativeCIP.NodeLabel.atom? label
                rw [show tree.toDeclarativeDigraph.label child = tree.declarativeLabel child by rfl,
                  labelIdentity] at observed
                simpa [OfficialCIPNode.toDeclarativeLabel] using observed
              have sourceProvenance : childTree.source.provenance =
                  OfficialCIPNodeProvenance.ringDuplicate distance := by
                have observed := congrArg DeclarativeCIP.NodeLabel.provenance label
                rw [show tree.toDeclarativeDigraph.label child = tree.declarativeLabel child by rfl,
                  labelIdentity] at observed
                cases source : childTree.source.provenance with
                | realAtom =>
                    simp [OfficialCIPNode.toDeclarativeLabel,
                      OfficialCIPNodeProvenance.toDeclarative, source] at observed
                | multipleBondDuplicate actual =>
                    simp [OfficialCIPNode.toDeclarativeLabel,
                      OfficialCIPNodeProvenance.toDeclarative, source] at observed
                | ringDuplicate actual =>
                    simp [OfficialCIPNode.toDeclarativeLabel,
                      OfficialCIPNodeProvenance.toDeclarative, source] at observed
                    subst actual
                    rfl
                | placeholder kind actual =>
                    cases kind <;> simp [OfficialCIPNode.toDeclarativeLabel,
                      OfficialCIPNodeProvenance.toDeclarative, source] at observed
              have firstIndex := input.executableOfficialCIPChildren_ringDuplicate_firstIndex
                parentTree.source childTree.source childPresent atom distance current
                  sourceProvenance
              have historyGet := firstIndexOf?_eq_some_imp_getElem?
                atom parentTree.source.history.reverse distance firstIndex
              have realized := input.generatedSourceTree_history_index_realized tree center ligand
                generated root parent parentTree parentLookup distance atom historyGet
              rcases realized with atCenter | atParentOrAncestor
              · exact Or.inl ⟨atCenter.2, atCenter.1⟩
              · rcases atParentOrAncestor with atParent | atAncestor
                · have adjacent := input.adj_of_mem_executableOfficialCIPChildren
                    parentTree.source childTree.source atom atom atParent.2 current childPresent
                  simp [MoleculeGraph.Adj, input.moleculeGraph.bond_self] at adjacent
                · rcases atAncestor with
                    ⟨ancestor, ancestorPath, ancestorAtom, ancestorDistance⟩
                  exact Or.inr ⟨ancestor, ancestorPath, ancestorAtom, by
                    simpa [OfficialCIPSourceTree.declarativeAddressing] using ancestorDistance⟩
      | phantom distance => trivial
      | lonePair => trivial
      | auxiliary => trivial

/-- Every complete executable exact ligand key has a recursive source-tree witness containing
exactly its addressed comparison occurrences and exactly the semantic child edges. -/
theorem buildExecutableExactOfficialRuleMajorKey_generatedSourceTree
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (key : ExactOfficialRuleMajorKey input.Atom)
    (computed : input.buildExecutableExactOfficialRuleMajorKey
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) = some key) :
    ∃ tree : OfficialCIPSourceTree input.Atom,
      OfficialCIPSourceTree.SourceLayersAligned key.sourceNodes tree ∧
        OfficialCIPSourceTree.GeneratedBy input.executableOfficialCIPChildren tree ∧
        tree.source = OfficialCIPNode.rootFromEdge center.1
          (input.canonicalLigandAtom center index) := by
  have expansion := input.buildExecutableExactOfficialRuleMajorKey_declarative_default
    center index key computed
  exact ExactOfficialRuleMajorKey.DeclarativeAddressedExpansion.generatedSourceTree
    input.moleculeGraph input.executableOfficialCIPChildren
    (input.certified.input.molecule.atomCount + 1)
    (OfficialCIPNode.rootFromEdge center.1
      (input.canonicalLigandAtom center index)) key.sourceNodes
    (input.executableOfficialExpansionCompleteWithin_default center index) expansion

/-- A successful exact-key build exposes a finite, format-neutral declarative hierarchy in which
every multiple-bond and ring duplicate satisfies the independent Rule-1b distance semantics under
every parent-preserving addressing. -/
theorem buildExecutableExactOfficialRuleMajorKey_duplicateDistancesCorrect
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (key : ExactOfficialRuleMajorKey input.Atom)
    (computed : input.buildExecutableExactOfficialRuleMajorKey
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) = some key) :
    ∃ tree : OfficialCIPSourceTree input.Atom,
      OfficialCIPSourceTree.SourceLayersAligned key.sourceNodes tree ∧
        ∀ addressing : tree.toDeclarativeDigraph.Addressing,
          DeclarativeCIP.RootedDigraph.DuplicateDistancesCorrect
            tree.toDeclarativeDigraph center.1 addressing := by
  obtain ⟨tree, aligned, generated, root⟩ :=
    input.buildExecutableExactOfficialRuleMajorKey_generatedSourceTree
      center index key computed
  refine ⟨tree, aligned, ?_⟩
  exact DeclarativeCIP.RootedDigraph.duplicateDistancesCorrect_all_of_one
    tree.toDeclarativeDigraph center.1 tree.declarativeAddressing
    (input.generatedSourceTree_duplicateDistancesCorrect tree center.1
      (input.canonicalLigandAtom center index) generated root)

/-- Every Rule-1b value in a complete executable semantic-input ligand key is exactly the
position-sensitive declarative observation. Duplicate payload validation is a logically prior
well-formedness obligation; the multiple-bond case is proved above, while full ring-ancestor
validation awaits the format-neutral declarative-digraph bridge. -/
theorem buildExecutableExactOfficialRuleMajorKey_rule1bProjection_eq_independent
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (key : ExactOfficialRuleMajorKey input.Atom)
    (computed : input.buildExecutableExactOfficialRuleMajorKey
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) = some key) :
    ExactOfficialRuleMajorKey.rule1bLayers key.sourceNodes =
      OfficialRuleMajorKey.independentRule1bLayers key.sourceNodes := by
  have expansion := input.buildExecutableExactOfficialRuleMajorKey_declarative_default
    center index key computed
  have historyCorrect :=
    ExactOfficialRuleMajorKey.DeclarativeAddressedExpansion.sourceHistoryLengthFrom
      input.moleculeGraph input.executableOfficialCIPChildren
      input.executableOfficialCIPChildren_history_length
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) key.sourceNodes expansion
  have rooted : OfficialRuleMajorKey.SourceHistoryLengthFrom 2 key.sourceNodes := by
    simpa [OfficialCIPNode.rootFromEdge] using historyCorrect
  have generated :=
    ExactOfficialRuleMajorKey.DeclarativeAddressedExpansion.sourceGraphGenerated
      input.moleculeGraph input.executableOfficialCIPChildren
      input.executableOfficialCIPChildren_graphGenerated
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) key.sourceNodes
      (by simp [OfficialCIPNode.GraphGenerated, OfficialCIPNode.rootFromEdge]) expansion
  exact OfficialRuleMajorKey.rule1bLayers_eq_independentRule1bLayers_of_sourceHistoryLength
    key.sourceNodes rooted generated

/-- End-to-end Rule-1b refinement for the executable exact-key pipeline.  The hierarchy carrying
the compiler's source occurrences satisfies the independent duplicate-distance relation under
every addressing, and the observations emitted from those same occurrences equal the independent
position-sensitive specification. -/
theorem buildExecutableExactOfficialRuleMajorKey_rule1bRefinesIndependentSpecification
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (key : ExactOfficialRuleMajorKey input.Atom)
    (computed : input.buildExecutableExactOfficialRuleMajorKey
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1
        (input.canonicalLigandAtom center index)) = some key) :
    ∃ tree : OfficialCIPSourceTree input.Atom,
      OfficialCIPSourceTree.SourceLayersAligned key.sourceNodes tree ∧
        (∀ addressing : tree.toDeclarativeDigraph.Addressing,
          DeclarativeCIP.RootedDigraph.DuplicateDistancesCorrect
            tree.toDeclarativeDigraph center.1 addressing) ∧
        ExactOfficialRuleMajorKey.rule1bLayers key.sourceNodes =
          OfficialRuleMajorKey.independentRule1bLayers key.sourceNodes := by
  obtain ⟨tree, aligned, distancesCorrect⟩ :=
    input.buildExecutableExactOfficialRuleMajorKey_duplicateDistancesCorrect
      center index key computed
  exact ⟨tree, aligned, distancesCorrect,
    input.buildExecutableExactOfficialRuleMajorKey_rule1bProjection_eq_independent
      center index key computed⟩

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
