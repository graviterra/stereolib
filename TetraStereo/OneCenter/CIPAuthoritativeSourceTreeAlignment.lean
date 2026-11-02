import TetraStereo.OneCenter.CIPAuthoritativeSparseScheduleConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace RawMolecule

/-!
# Sphere-table alignment with the recursive source tree

The authoritative compiler retains the same occurrences twice: a sphere-major table drives rule
comparison, while a recursive tree drives the declarative molecular digraph.  The following
kernel proofs show that these are two traversals of exactly the same path/source occurrences.
-/

/-- A sphere-major source table and recursive source tree contain exactly the same addressed
source occurrences. -/
def CanonicalBranchKey.SourceTreeAligned
    (key : CanonicalBranchKey) (tree : CanonicalSourceTree) : Prop :=
  key.sourceTree? = some tree ∧
    ∀ entry, entry ∈ key.sourceNodes.flatten ↔ entry ∈ tree.occurrences

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

private theorem child_sourceLayers_length_le_count
    (children : List CanonicalBranchKey) (child : CanonicalBranchKey)
    (present : child ∈ children) :
    child.sourceNodes.length ≤
      canonicalChildLayerCount children CanonicalBranchKey.sourceNodes := by
  exact value_le_foldl_max_of_mem (fun key => key.sourceNodes.length)
    children 0 child present

/-- Flattening the ragged sphere transpose produced by child merging contains exactly every
child occurrence prefixed by its ranked sibling slot. -/
theorem mem_mergeCanonicalSourceChildren_flatten_iff
    (children : List CanonicalBranchKey) (entry : CanonicalSourceEntry) :
    entry ∈ (mergeCanonicalSourceChildren children).flatten ↔
      ∃ child ∈ children.zipIdx, ∃ source,
        source ∈ child.1.sourceNodes.flatten ∧
          entry = (child.2 :: source.1, source.2) := by
  constructor
  · intro present
    rw [mem_flatten_iff_getD] at present
    rcases present with ⟨depth, depthLt, entryPresent⟩
    have depthLtCount : depth < canonicalChildLayerCount children
        CanonicalBranchKey.sourceNodes := by
      simpa [mergeCanonicalSourceChildren] using depthLt
    have inMerged : entry ∈ children.zipIdx.flatMap fun child =>
        prefixCanonicalSourceLayer child.2
          (child.1.sourceNodes.getD depth []) := by
      simpa [mergeCanonicalSourceChildren, List.getD, depthLtCount] using entryPresent
    simp only [List.mem_flatMap] at inMerged
    rcases inMerged with ⟨child, childPresent, inPrefix⟩
    simp only [prefixCanonicalSourceLayer, List.mem_map] at inPrefix
    rcases inPrefix with ⟨source, sourcePresent, rfl⟩
    have depthLtChild : depth < child.1.sourceNodes.length := by
      by_contra outside
      have notLt : ¬depth < child.1.sourceNodes.length := outside
      simp [List.getD, notLt] at sourcePresent
    have sourceFlatten : source ∈ child.1.sourceNodes.flatten :=
      (mem_flatten_iff_getD source child.1.sourceNodes).2
        ⟨depth, depthLtChild, sourcePresent⟩
    exact ⟨child, childPresent, source, sourceFlatten, rfl⟩
  · rintro ⟨child, childPresent, source, sourcePresent, rfl⟩
    rw [mem_flatten_iff_getD] at sourcePresent
    rcases sourcePresent with ⟨depth, depthLtChild, sourceInLayer⟩
    have childInChildren : child.1 ∈ children :=
      List.fst_mem_of_mem_zipIdx childPresent
    have depthLtCount : depth < canonicalChildLayerCount children
        CanonicalBranchKey.sourceNodes :=
      lt_of_lt_of_le depthLtChild
        (child_sourceLayers_length_le_count children child.1 childInChildren)
    rw [mem_flatten_iff_getD]
    refine ⟨depth, ?_, ?_⟩
    · simpa [mergeCanonicalSourceChildren] using depthLtCount
    · have inMerged : (child.2 :: source.1, source.2) ∈
          children.zipIdx.flatMap fun indexed =>
            prefixCanonicalSourceLayer indexed.2
              (indexed.1.sourceNodes.getD depth []) := by
        simp only [List.mem_flatMap]
        refine ⟨child, childPresent, ?_⟩
        simp only [prefixCanonicalSourceLayer, List.mem_map]
        exact ⟨source, sourceInLayer, rfl⟩
      simpa [mergeCanonicalSourceChildren, List.getD, depthLtCount] using inMerged

/-- Forest preorder occurrences have the corresponding ranked sibling decomposition. -/
theorem CanonicalSourceForest.mem_occurrences_iff_zipIdx
    : ∀ (forest : CanonicalSourceForest) (start : ℕ)
    (entry : CanonicalSourceEntry),
    entry ∈ forest.occurrences start ↔
      ∃ indexed ∈ forest.toList.zipIdx start, ∃ source,
        source ∈ indexed.1.occurrences ∧
          entry = (indexed.2 :: source.1, source.2)
  | .nil, start, entry => by
      simp [CanonicalSourceForest.occurrences, CanonicalSourceForest.toList]
  | .cons tree forest, start, entry => by
      simp only [CanonicalSourceForest.occurrences, List.mem_append,
        List.mem_map, CanonicalSourceForest.toList]
      constructor
      · rintro (⟨source, sourcePresent, rfl⟩ | tailPresent)
        · exact ⟨(tree, start), by simp [List.zipIdx],
            source, sourcePresent, rfl⟩
        · rw [CanonicalSourceForest.mem_occurrences_iff_zipIdx
              forest (start + 1) entry] at tailPresent
          rcases tailPresent with ⟨indexed, indexedPresent, source,
            sourcePresent, rfl⟩
          refine ⟨indexed, ?_, source, sourcePresent, rfl⟩
          change indexed ∈ (tree, start) :: forest.toList.zipIdx (start + 1)
          exact List.mem_cons.mpr (Or.inr indexedPresent)
      · rintro ⟨indexed, indexedPresent, source, sourcePresent, rfl⟩
        change indexed ∈ (tree, start) :: forest.toList.zipIdx (start + 1)
          at indexedPresent
        rcases List.mem_cons.mp indexedPresent with headEq | tailPresent
        · subst indexed
          exact Or.inl ⟨source, sourcePresent, rfl⟩
        · apply Or.inr
          rw [CanonicalSourceForest.mem_occurrences_iff_zipIdx forest (start + 1)]
          exact ⟨indexed, tailPresent, source, sourcePresent, rfl⟩

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

private theorem collectSourceTreeAlignedForest :
    ∀ children : List CanonicalBranchKey,
    (∀ child, child ∈ children → ∃ tree, child.SourceTreeAligned tree) →
      ∃ forest, canonicalSourceForest? children = some forest ∧
        List.Forall₂ CanonicalBranchKey.SourceTreeAligned children forest.toList
  | [], _ => ⟨.nil, rfl, .nil⟩
  | child :: children, aligned => by
      obtain ⟨tree, treeAligned⟩ := aligned child (by simp)
      obtain ⟨forest, forestComputed, tailAligned⟩ :=
        collectSourceTreeAlignedForest children (by
          intro tail present
          exact aligned tail (by simp [present]))
      refine ⟨.cons tree forest, ?_, ?_⟩
      · simp [canonicalSourceForest?, treeAligned.1, forestComputed]
      · simpa [CanonicalSourceForest.toList] using
          List.Forall₂.cons treeAligned tailAligned

private theorem mapM_mem_sourceTree {α β : Type*} (f : α → Option β) :
    ∀ (inputs : List α) (outputs : List β), inputs.mapM f = some outputs →
      ∀ output, output ∈ outputs → ∃ input, input ∈ inputs ∧ f input = some output
  | [], outputs, computed, output, present => by
      simp at computed
      subst outputs
      simp at present
  | input :: inputs, outputs, computed, output, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : f input with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : inputs.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst outputs
              rcases List.mem_cons.mp present with rfl | tailPresent
              · exact ⟨input, by simp, headComputed⟩
              · obtain ⟨source, sourcePresent, sourceComputed⟩ :=
                  mapM_mem_sourceTree f inputs tail tailComputed output tailPresent
                exact ⟨source, by simp [sourcePresent], sourceComputed⟩

private theorem mergeCanonicalSourceChildren_alignedWithForest
    (children : List CanonicalBranchKey) (forest : CanonicalSourceForest)
    (aligned : List.Forall₂ CanonicalBranchKey.SourceTreeAligned
      children forest.toList) (entry : CanonicalSourceEntry) :
    entry ∈ (mergeCanonicalSourceChildren children).flatten ↔
      entry ∈ forest.occurrences 0 := by
  rw [mem_mergeCanonicalSourceChildren_flatten_iff,
    forest.mem_occurrences_iff_zipIdx]
  constructor
  · rintro ⟨child, childPresent, source, sourcePresent, rfl⟩
    obtain ⟨tree, treePresent, childAligned⟩ :=
      forall₂_zipIdx_right aligned child childPresent
    refine ⟨(tree, child.2), treePresent, source, ?_, rfl⟩
    exact (childAligned.2 source).mp sourcePresent
  · rintro ⟨tree, treePresent, source, sourcePresent, rfl⟩
    have flipped : List.Forall₂ (flip CanonicalBranchKey.SourceTreeAligned)
        forest.toList children :=
      List.Forall₂.flip (R := flip CanonicalBranchKey.SourceTreeAligned) aligned
    obtain ⟨child, childPresent, childAligned⟩ :=
      forall₂_zipIdx_right flipped tree treePresent
    refine ⟨(child, tree.2), childPresent, source, ?_, rfl⟩
    exact (childAligned.2 source).mpr sourcePresent

theorem canonicalRootKeyAuthoritative?_sourceTreeAligned
    (mol : RawMolecule) (node : CanonicalBranchNode) (complete : Bool)
    (key : CanonicalBranchKey)
    (computed : mol.canonicalRootKeyAuthoritative? node complete = some key) :
    ∃ tree, key.SourceTreeAligned tree := by
  unfold canonicalRootKeyAuthoritative? at computed
  cases labelComputed : mol.canonicalRule1aLabelAuthoritative? node with
  | none => simp [labelComputed] at computed
  | some label =>
      simp [labelComputed] at computed
      subst key
      refine ⟨.node node .nil, rfl, ?_⟩
      intro entry
      simp [CanonicalSourceTree.occurrences, CanonicalSourceForest.occurrences]

/-- Every successful authoritative compilation proves that its sphere table and recursive tree
are exact alternate traversals of the same addressed source occurrences. -/
theorem buildCanonicalBranchKeyAuthoritative_sourceTreeAligned
    (mol : RawMolecule) : ∀ fuel node key,
    mol.buildCanonicalBranchKeyAuthoritative fuel node = some key →
      ∃ tree, key.SourceTreeAligned tree
  | 0, node, key, computed =>
      mol.canonicalRootKeyAuthoritative?_sourceTreeAligned node
        (mol.canonicalTerminal node) key computed
  | fuel + 1, node, key, computed => by
      unfold buildCanonicalBranchKeyAuthoritative at computed
      by_cases terminal : mol.canonicalTerminal node = true
      · simp [terminal] at computed
        exact mol.canonicalRootKeyAuthoritative?_sourceTreeAligned node true key computed
      · rw [if_neg terminal] at computed
        let children := mol.canonicalChildren node
        by_cases tooWide : authoritativeChildSlots < children.length
        · simp [children, tooWide] at computed
        · rw [if_neg tooWide] at computed
          cases childKeysComputed : children.mapM
              (mol.buildCanonicalBranchKeyAuthoritative fuel) with
          | none => simp [children, childKeysComputed] at computed
          | some childKeys =>
              cases sortedComputed : sortCanonicalKeys? childKeys with
              | none => simp [children, childKeysComputed, sortedComputed] at computed
              | some sorted =>
                  cases rootComputed : mol.canonicalRootKeyAuthoritative? node
                      (sorted.all fun child => child.complete) with
                  | none =>
                      simp [children, childKeysComputed, sortedComputed, rootComputed] at computed
                  | some root =>
                      simp [children, childKeysComputed, sortedComputed, rootComputed] at computed
                      subst key
                      have sortedAligned : ∀ child, child ∈ sorted →
                          ∃ tree, child.SourceTreeAligned tree := by
                        intro child present
                        have permutation :=
                          sortCanonicalKeys?_perm childKeys sorted sortedComputed
                        have childPresent : child ∈ childKeys :=
                          (permutation.mem_iff).mp present
                        obtain ⟨source, sourcePresent, sourceComputed⟩ :=
                          mapM_mem_sourceTree (mol.buildCanonicalBranchKeyAuthoritative fuel)
                            children childKeys childKeysComputed child childPresent
                        exact buildCanonicalBranchKeyAuthoritative_sourceTreeAligned
                          mol fuel source child sourceComputed
                      obtain ⟨forest, forestComputed, forestAligned⟩ :=
                        collectSourceTreeAlignedForest sorted sortedAligned
                      have rootSources := mol.canonicalRootKeyAuthoritative?_sourceNodes_eq
                        node (sorted.all fun child => child.complete) root rootComputed
                      have rootTree : root.sourceTree? = some (.node node .nil) := by
                        unfold canonicalRootKeyAuthoritative? at rootComputed
                        cases labelComputed : mol.canonicalRule1aLabelAuthoritative? node with
                        | none => simp [labelComputed] at rootComputed
                        | some label =>
                            simp [labelComputed] at rootComputed
                            subst root
                            rfl
                      refine ⟨.node node forest, ?_, ?_⟩
                      · simp [assembleCanonicalBranchKey, rootTree, forestComputed]
                      · intro entry
                        change entry ∈
                            (root.sourceNodes ++ mergeCanonicalSourceChildren sorted).flatten ↔ _
                        rw [List.flatten_append, rootSources]
                        simp only [List.flatten_cons, List.flatten_nil, List.append_nil,
                          List.mem_append, CanonicalSourceTree.occurrences, List.mem_cons]
                        rw [mergeCanonicalSourceChildren_alignedWithForest
                          sorted forest forestAligned entry]
                        simp

/-- Public branch compilation inherits the exact sphere-table/recursive-tree alignment. -/
theorem branchCanonicalKeyAuthoritative?_sourceTreeAligned
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (computed : branchCanonicalKeyAuthoritative? mol center ligand = some key) :
    ∃ tree, key.SourceTreeAligned tree := by
  unfold branchCanonicalKeyAuthoritative? at computed
  exact mol.buildCanonicalBranchKeyAuthoritative_sourceTreeAligned
    (2 * mol.atomCount + 2) (canonicalRoot center ligand) key computed

/-- Under source-tree alignment, membership in the sphere table is exactly recursive tree lookup. -/
theorem CanonicalBranchKey.SourceTreeAligned.mem_flatten_iff_sourceNodeAtAddress
    (key : CanonicalBranchKey) (tree : CanonicalSourceTree)
    (aligned : key.SourceTreeAligned tree)
    (address : List ℕ) (source : CanonicalBranchNode) :
    (address, source) ∈ key.sourceNodes.flatten ↔
      key.sourceNodeAtAddress? address = some source := by
  rw [aligned.2]
  rw [tree.mem_occurrences_iff_subtreeAt]
  rw [key.sourceNodeAtAddress?_eq_tree_sourceAt tree aligned.1]
  unfold CanonicalSourceTree.sourceAt?
  cases found : tree.subtreeAt? address with
  | none => simp
  | some subtree =>
      cases subtree with
      | node foundSource children => simp

/-- The flattened comparison schedule is precisely the address support of the declarative
digraph produced from the same key. -/
theorem CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff
    (key : CanonicalBranchKey) (tree : CanonicalSourceTree)
    (aligned : key.SourceTreeAligned tree) (address : List ℕ) :
    address ∈ key.sourceAddressSchedule ↔ address ∈ key.hierarchyAddresses := by
  rw [key.mem_hierarchyAddresses_iff_tree_occurrence tree aligned.1]
  unfold CanonicalBranchKey.sourceAddressSchedule
  simp only [List.mem_map]
  constructor
  · rintro ⟨entry, entryPresent, entryAddress⟩
    rcases entry with ⟨entryPath, entrySource⟩
    simp only at entryAddress
    subst entryPath
    exact ⟨entrySource,
      (aligned.2 (address, entrySource)).mp entryPresent⟩
  · rintro ⟨source, sourcePresent⟩
    refine ⟨(address, source), ?_, rfl⟩
    exact (aligned.2 (address, source)).mpr sourcePresent

/-- Equivalently, a schedule address is present exactly when recursive lookup returns a concrete
source occurrence. -/
theorem CanonicalBranchKey.SourceTreeAligned.mem_sourceAddressSchedule_iff_exists_source
    (key : CanonicalBranchKey) (tree : CanonicalSourceTree)
    (aligned : key.SourceTreeAligned tree) (address : List ℕ) :
    address ∈ key.sourceAddressSchedule ↔
      ∃ source, key.sourceNodeAtAddress? address = some source := by
  unfold CanonicalBranchKey.sourceAddressSchedule
  simp only [List.mem_map]
  constructor
  · rintro ⟨entry, entryPresent, entryAddress⟩
    rcases entry with ⟨entryPath, entrySource⟩
    simp only at entryAddress
    subst entryPath
    exact ⟨entrySource,
      (CanonicalBranchKey.SourceTreeAligned.mem_flatten_iff_sourceNodeAtAddress
        key tree aligned address entrySource).mp entryPresent⟩
  · rintro ⟨source, sourceAt⟩
    refine ⟨(address, source), ?_, rfl⟩
    exact (CanonicalBranchKey.SourceTreeAligned.mem_flatten_iff_sourceNodeAtAddress
      key tree aligned address source).mpr sourceAt

/-- Reading any observation back through recursive lookup reproduces the sphere-table observation
list exactly. -/
theorem CanonicalBranchKey.SourceTreeAligned.map_observation_eq_schedule_map
    {α : Type*} [Inhabited α]
    (key : CanonicalBranchKey) (tree : CanonicalSourceTree)
    (aligned : key.SourceTreeAligned tree)
    (observe : CanonicalBranchNode → α) :
    key.sourceNodes.flatten.map (observe ∘ Prod.snd) =
      key.sourceAddressSchedule.map fun address =>
        (key.sourceNodeAtAddress? address).map observe |>.getD default := by
  unfold CanonicalBranchKey.sourceAddressSchedule
  rw [List.map_map]
  apply List.map_congr_left
  intro entry entryPresent
  change observe entry.2 =
    ((key.sourceNodeAtAddress? entry.1).map observe).getD default
  rw [(CanonicalBranchKey.SourceTreeAligned.mem_flatten_iff_sourceNodeAtAddress
    key tree aligned entry.1 entry.2).mp entryPresent]
  rfl

end RawMolecule

end TetraStereo.OneCenter
