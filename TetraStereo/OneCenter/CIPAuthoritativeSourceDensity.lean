import TetraStereo.OneCenter.CIPAuthoritativeSourceAlignment

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace RawMolecule

/-!
# No empty semantic spheres in successful authoritative keys

The sparse hierarchy comparator treats a present outer list cell structurally, even when that
sphere contains no observations.  Successful recursive compilation never creates such a cell:
its layer count is the maximum child depth, so every retained depth is witnessed by at least one
child source layer.
-/

/-- Every stored source sphere contains at least one source observation. -/
def CanonicalSourceLayersDense (layers : List (List CanonicalSourceEntry)) : Prop :=
  ∀ layer, layer ∈ layers → layer ≠ []

/-- Exceeding a fold of maxima is witnessed either by the initial bound or by one input. -/
private theorem lt_foldl_max_sourceLength_witness
    (depth initial : ℕ) : ∀ children : List CanonicalBranchKey,
    depth < children.foldl
        (fun longest child => max longest child.sourceNodes.length) initial →
      depth < initial ∨
        ∃ child, child ∈ children ∧ depth < child.sourceNodes.length
  | [], less => Or.inl less
  | child :: children, less => by
      have witness := lt_foldl_max_sourceLength_witness depth
        (max initial child.sourceNodes.length) children less
      rcases witness with first | tail
      · rcases (lt_max_iff.mp first) with old | head
        · exact Or.inl old
        · exact Or.inr ⟨child, by simp, head⟩
      · rcases tail with ⟨found, present, foundDepth⟩
        exact Or.inr ⟨found, by simp [present], foundDepth⟩

/-- A depth below the canonical child-layer count is present in some child key. -/
theorem exists_child_sourceLayer_of_lt_canonicalChildLayerCount
    (children : List CanonicalBranchKey) (depth : ℕ)
    (less : depth < canonicalChildLayerCount children
      (fun child => child.sourceNodes)) :
    ∃ child, child ∈ children ∧ depth < child.sourceNodes.length := by
  have witness := lt_foldl_max_sourceLength_witness depth 0 children (by
    simpa [canonicalChildLayerCount] using less)
  exact witness.resolve_left (Nat.not_lt_zero depth)

private theorem mergedSourceLayer_nonempty_of_child
    (children : List CanonicalBranchKey) (depth : ℕ)
    (child : CanonicalBranchKey) (childPresent : child ∈ children)
    (childLayerNonempty : child.sourceNodes.getD depth [] ≠ []) :
    children.zipIdx.flatMap (fun indexed =>
      prefixCanonicalSourceLayer indexed.2
        (indexed.1.sourceNodes.getD depth [])) ≠ [] := by
  intro empty
  rw [List.flatMap_eq_nil_iff] at empty
  rw [List.mem_iff_getElem] at childPresent
  rcases childPresent with ⟨slot, slotValid, childAtSlot⟩
  have indexedPresent : (child, slot) ∈ children.zipIdx := by
    rw [List.mem_iff_getElem]
    refine ⟨slot, by simpa using slotValid, ?_⟩
    simp [childAtSlot]
  have prefixedEmpty := empty (child, slot) indexedPresent
  simp [prefixCanonicalSourceLayer] at prefixedEmpty
  exact childLayerNonempty prefixedEmpty

/-- Merging dense child source hierarchies cannot introduce an empty retained sphere. -/
theorem mergeCanonicalSourceChildren_dense
    (children : List CanonicalBranchKey)
    (dense : ∀ child, child ∈ children →
      CanonicalSourceLayersDense child.sourceNodes) :
    CanonicalSourceLayersDense (mergeCanonicalSourceChildren children) := by
  intro layer layerPresent
  unfold mergeCanonicalSourceChildren at layerPresent
  simp only [List.mem_map] at layerPresent
  rcases layerPresent with ⟨depth, depthPresent, rfl⟩
  have depthLess : depth < canonicalChildLayerCount children
      (fun child => child.sourceNodes) := by
    simpa using depthPresent
  obtain ⟨child, childPresent, childDepth⟩ :=
    exists_child_sourceLayer_of_lt_canonicalChildLayerCount children depth depthLess
  have childLayerNonempty : child.sourceNodes.getD depth [] ≠ [] := by
    have layerPresent : child.sourceNodes.getD depth [] ∈ child.sourceNodes := by
      simp [List.getD, childDepth]
    exact dense child childPresent _ layerPresent
  exact mergedSourceLayer_nonempty_of_child children depth child childPresent
    childLayerNonempty

/-- A root above merged dense children is again dense. -/
theorem root_cons_mergeCanonicalSourceChildren_dense
    (node : CanonicalBranchNode) (children : List CanonicalBranchKey)
    (dense : ∀ child, child ∈ children →
      CanonicalSourceLayersDense child.sourceNodes) :
    CanonicalSourceLayersDense
      ([[([], node)]] ++ mergeCanonicalSourceChildren children) := by
  intro layer present
  simp only [List.mem_append] at present
  rcases present with root | merged
  · simp at root
    subst layer
    simp
  · exact mergeCanonicalSourceChildren_dense children dense layer merged

private theorem mapM_mem_source_dense {alpha beta : Type*} (f : alpha → Option beta) :
    ∀ (inputs : List alpha) (outputs : List beta), inputs.mapM f = some outputs →
      ∀ output, output ∈ outputs →
        ∃ input, input ∈ inputs ∧ f input = some output
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
                  mapM_mem_source_dense f inputs tail tailComputed output tailPresent
                exact ⟨source, by simp [sourcePresent], sourceComputed⟩

/-- Every successfully compiled recursive authoritative key has no empty source sphere. -/
theorem buildCanonicalBranchKeyAuthoritative_dense
    (mol : RawMolecule) : ∀ fuel node key,
    mol.buildCanonicalBranchKeyAuthoritative fuel node = some key →
      CanonicalSourceLayersDense key.sourceNodes
  | 0, node, key, computed => by
      rw [mol.canonicalRootKeyAuthoritative?_sourceNodes_eq node
        (mol.canonicalTerminal node) key computed]
      intro layer present
      simp at present
      subst layer
      simp
  | fuel + 1, node, key, computed => by
      unfold buildCanonicalBranchKeyAuthoritative at computed
      by_cases terminal : mol.canonicalTerminal node = true
      · simp [terminal] at computed
        rw [mol.canonicalRootKeyAuthoritative?_sourceNodes_eq node true key computed]
        intro layer present
        simp at present
        subst layer
        simp
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
                      change CanonicalSourceLayersDense
                        (root.sourceNodes ++ mergeCanonicalSourceChildren sorted)
                      rw [mol.canonicalRootKeyAuthoritative?_sourceNodes_eq node
                        (sorted.all fun child => child.complete) root rootComputed]
                      apply root_cons_mergeCanonicalSourceChildren_dense node sorted
                      intro child present
                      have permutation := sortCanonicalKeys?_perm childKeys sorted sortedComputed
                      have childPresent : child ∈ childKeys := (permutation.mem_iff).mp present
                      obtain ⟨source, sourcePresent, sourceComputed⟩ :=
                        mapM_mem_source_dense (mol.buildCanonicalBranchKeyAuthoritative fuel)
                          children childKeys childKeysComputed child childPresent
                      exact buildCanonicalBranchKeyAuthoritative_dense mol fuel
                        source child sourceComputed

/-- Public successful authoritative compilation never emits an empty source sphere. -/
theorem branchCanonicalKeyAuthoritative?_dense
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (computed : branchCanonicalKeyAuthoritative? mol center ligand = some key) :
    CanonicalSourceLayersDense key.sourceNodes := by
  unfold branchCanonicalKeyAuthoritative? at computed
  exact mol.buildCanonicalBranchKeyAuthoritative_dense
    (2 * mol.atomCount + 2) (canonicalRoot center ligand) key computed

/-- A pointwise observation projection preserves nonempty source spheres. -/
theorem CanonicalSourceLayersDense.map_observation
    {alpha : Type*} (layers : List (List CanonicalSourceEntry))
    (dense : CanonicalSourceLayersDense layers)
    (observe : CanonicalBranchNode → alpha) :
    ∀ layer, layer ∈ mapCanonicalSourceLayers observe layers → layer ≠ [] := by
  intro layer present
  simp only [mapCanonicalSourceLayers, List.mem_map] at present
  rcases present with ⟨sourceLayer, sourcePresent, rfl⟩
  intro mappedEmpty
  rw [List.map_eq_nil_iff] at mappedEmpty
  exact dense sourceLayer sourcePresent mappedEmpty

end RawMolecule

end TetraStereo.OneCenter
