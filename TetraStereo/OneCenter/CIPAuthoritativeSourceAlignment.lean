import TetraStereo.OneCenter.CIPAuthoritativeRule2Soundness
import TetraStereo.OneCenter.DeclarativeCIPFirstDifferenceSchedule

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace RawMolecule

open DeclarativeCIP

/-!
# Address-preserving constitutional source alignment

The authoritative compiler caches three numeric rule projections beside one provenance-bearing
source-node hierarchy.  These theorems prove that successful compilation never fabricates, drops,
or relocates an observation: every cached field is exactly a pointwise projection of that common
source hierarchy.
-/

/-- Map an observation over source layers without changing sphere or parent-slot addresses. -/
def mapCanonicalSourceLayers {α : Type*} (observe : CanonicalBranchNode → α)
    (layers : List (List CanonicalSourceEntry)) : List (List (List ℕ × α)) :=
  layers.map fun layer => layer.map fun entry => (entry.1, observe entry.2)

/-- Total Rule-1a observation used only to state source alignment. Successful compilation proves
that the fallback branch is unreachable at every retained source. -/
def canonicalRule1aLabelAuthoritativeTotal (mol : RawMolecule)
    (node : CanonicalBranchNode) : CIPAtomicLabel :=
  (mol.canonicalRule1aLabelAuthoritative? node).getD
    { numerator := 0, denominator := 1 }

/-- The three cached constitutional projections are exactly observations of the common source
layers. -/
def CanonicalBranchKey.AuthoritativeSourceAligned
    (mol : RawMolecule) (key : CanonicalBranchKey) : Prop :=
  key.rule1a = mapCanonicalSourceLayers
      (mol.canonicalRule1aLabelAuthoritativeTotal) key.sourceNodes ∧
    key.rule1b = mapCanonicalSourceLayers CanonicalBranchNode.rule1bCode key.sourceNodes ∧
    key.rule2 = mapCanonicalSourceLayers mol.canonicalRule2Mass key.sourceNodes

/-- Canonical source layers are ordered by parent-slot path within each sphere, and every path in
layer `depth` has absolute length `offset + depth`. -/
structure CanonicalSourceLayersScheduledFrom
    (offset : ℕ) (layers : List (List CanonicalSourceEntry)) : Prop where
  layerOrdered : ∀ depth,
    ((layers.getD depth []).map Prod.fst).Pairwise (fun left right => left < right)
  depthCorrect : ∀ depth entry, entry ∈ layers.getD depth [] →
    entry.1.length = offset + depth

/-- Sphere-major address schedule retained by a compiled key. -/
def CanonicalBranchKey.sourceAddressSchedule (key : CanonicalBranchKey) : List (List ℕ) :=
  key.sourceNodes.flatten.map Prod.fst

theorem CanonicalSourceLayersScheduledFrom.root
    (node : CanonicalBranchNode) :
    CanonicalSourceLayersScheduledFrom 0 [[([], node)]] := by
  constructor
  · intro depth
    cases depth <;> simp
  · intro depth entry present
    cases depth with
    | zero =>
        simp at present
        subst entry
        rfl
    | succ depth => simp at present

private theorem pairwise_indices_zipIdx {α : Type*} (values : List α) :
    values.zipIdx.Pairwise (fun left right => left.2 < right.2) := by
  apply List.pairwise_map.mp
  rw [List.zipIdx_map_snd]
  exact List.pairwise_lt_range'

private theorem pairwise_prefix_paths (slot : ℕ) (paths : List (List ℕ))
    (ordered : paths.Pairwise (fun left right => left < right)) :
    (paths.map (slot :: ·)).Pairwise (fun left right => left < right) := by
  rw [List.pairwise_map]
  exact ordered.imp fun {left right} less => by
    simpa [List.cons_lt_cons_iff] using less

private theorem mergedCanonicalSourceLayer_ordered
    (children : List CanonicalBranchKey)
    (scheduled : ∀ child, child ∈ children →
      CanonicalSourceLayersScheduledFrom 0 child.sourceNodes)
    (depth : ℕ) :
    ((children.zipIdx.flatMap fun child =>
        prefixCanonicalSourceLayer child.2
          (child.1.sourceNodes.getD depth [])).map Prod.fst).Pairwise
      (fun left right => left < right) := by
  rw [List.map_flatMap]
  apply List.pairwise_flatMap.mpr
  constructor
  · intro child present
    have childPresent : child.1 ∈ children := List.fst_mem_of_mem_zipIdx present
    have childOrdered := (scheduled child.1 childPresent).layerOrdered depth
    simpa [prefixCanonicalSourceLayer, List.map_map, Function.comp_def] using
      pairwise_prefix_paths child.2
        ((child.1.sourceNodes.getD depth []).map Prod.fst) childOrdered
  · exact (pairwise_indices_zipIdx children).imp fun {left right} slots => by
      intro leftPath leftPresent rightPath rightPresent
      simp only [List.mem_map] at leftPresent rightPresent
      rcases leftPresent with ⟨leftEntry, leftInPrefix, rfl⟩
      rcases rightPresent with ⟨rightEntry, rightInPrefix, rfl⟩
      simp only [prefixCanonicalSourceLayer, List.mem_map] at leftInPrefix rightInPrefix
      rcases leftInPrefix with ⟨leftSource, _, rfl⟩
      rcases rightInPrefix with ⟨rightSource, _, rfl⟩
      exact List.cons_lt_cons_iff.mpr (Or.inl slots)

private theorem mergedCanonicalSourceLayer_depth
    (children : List CanonicalBranchKey)
    (scheduled : ∀ child, child ∈ children →
      CanonicalSourceLayersScheduledFrom 0 child.sourceNodes)
    (depth : ℕ) (entry : CanonicalSourceEntry)
    (present : entry ∈ children.zipIdx.flatMap fun child =>
      prefixCanonicalSourceLayer child.2
        (child.1.sourceNodes.getD depth [])) :
    entry.1.length = 1 + depth := by
  simp only [List.mem_flatMap] at present
  rcases present with ⟨child, childPresent, entryPresent⟩
  have sourcePresent : child.1 ∈ children := List.fst_mem_of_mem_zipIdx childPresent
  simp only [prefixCanonicalSourceLayer, List.mem_map] at entryPresent
  rcases entryPresent with ⟨source, sourceInLayer, rfl⟩
  have sourceDepth := (scheduled child.1 sourcePresent).depthCorrect
    depth source sourceInLayer
  simp [sourceDepth, Nat.add_comm]

/-- Merging scheduled child trees under ranked sibling slots yields scheduled layers beginning one
sphere below the parent. -/
theorem mergeCanonicalSourceChildren_scheduledFrom_one
    (children : List CanonicalBranchKey)
    (scheduled : ∀ child, child ∈ children →
      CanonicalSourceLayersScheduledFrom 0 child.sourceNodes) :
    CanonicalSourceLayersScheduledFrom 1
      (mergeCanonicalSourceChildren children) := by
  constructor
  · intro depth
    by_cases inRange : depth < canonicalChildLayerCount children
        (fun child => child.sourceNodes)
    · simpa [mergeCanonicalSourceChildren, List.getD, inRange] using
        mergedCanonicalSourceLayer_ordered children scheduled depth
    · simp [mergeCanonicalSourceChildren, List.getD, inRange]
  · intro depth entry present
    by_cases inRange : depth < canonicalChildLayerCount children
        (fun child => child.sourceNodes)
    · have mergedPresent : entry ∈ children.zipIdx.flatMap fun child =>
          prefixCanonicalSourceLayer child.2
            (child.1.sourceNodes.getD depth []) := by
        simpa [mergeCanonicalSourceChildren, List.getD, inRange] using present
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        mergedCanonicalSourceLayer_depth children scheduled depth entry mergedPresent
    · simp [mergeCanonicalSourceChildren, List.getD, inRange] at present

/-- Adding a root layer above a scheduled child merge restores a zero-based schedule. -/
theorem root_cons_mergeCanonicalSourceChildren_scheduled
    (node : CanonicalBranchNode) (children : List CanonicalBranchKey)
    (scheduled : ∀ child, child ∈ children →
      CanonicalSourceLayersScheduledFrom 0 child.sourceNodes) :
    CanonicalSourceLayersScheduledFrom 0
      ([[([], node)]] ++ mergeCanonicalSourceChildren children) := by
  have merged := mergeCanonicalSourceChildren_scheduledFrom_one children scheduled
  constructor
  · intro depth
    cases depth with
    | zero => simp
    | succ depth => simpa using merged.layerOrdered depth
  · intro depth entry present
    cases depth with
    | zero =>
        simp at present
        subst entry
        rfl
    | succ depth =>
        have := merged.depthCorrect depth entry (by simpa using present)
        simpa [Nat.add_assoc, Nat.add_comm] using this

private theorem hierarchyAddressBefore_of_length_lt
    {left right : List ℕ} (less : left.length < right.length) :
    HierarchyAddressBefore left right := by
  simp [HierarchyAddressBefore, HierarchyAddressKey, List.cons_lt_cons_iff, less]

private theorem hierarchyAddressBefore_of_length_eq_of_lt
    {left right : List ℕ} (lengthEq : left.length = right.length)
    (less : left < right) : HierarchyAddressBefore left right := by
  simp [HierarchyAddressBefore, HierarchyAddressKey, lengthEq, less]

/-- A scheduled source-layer table flattens to the exact strict sphere-major semantic address
order used by `FirstDifferenceOutcome`. -/
theorem CanonicalSourceLayersScheduledFrom.flattened_pairwise
    (offset : ℕ) (layers : List (List CanonicalSourceEntry))
    (scheduled : CanonicalSourceLayersScheduledFrom offset layers) :
    (layers.flatten.map Prod.fst).Pairwise HierarchyAddressBefore := by
  have scheduleEq : layers.flatten.map Prod.fst =
      layers.zipIdx.flatMap (fun layer => layer.1.map Prod.fst) := by
    rw [List.map_flatten]
    unfold List.flatMap
    apply congrArg List.flatten
    calc
      layers.map (List.map Prod.fst) =
          (layers.zipIdx.map Prod.fst).map (List.map Prod.fst) := by
            rw [List.zipIdx_map_fst]
      _ = layers.zipIdx.map (fun layer => layer.1.map Prod.fst) := by
            rw [List.map_map]
            apply List.map_congr_left
            intro layer _
            rfl
  rw [scheduleEq]
  apply List.pairwise_flatMap.mpr
  constructor
  · intro layer layerPresent
    have layerIndex : layer.2 < layers.length := List.snd_lt_of_mem_zipIdx layerPresent
    have getLayer : layers.getD layer.2 [] = layer.1 := by
      have fstEq := List.fst_eq_of_mem_zipIdx layerPresent
      simpa [List.getD, layerIndex] using fstEq.symm
    have ordered := scheduled.layerOrdered layer.2
    rw [getLayer] at ordered
    exact ordered.imp_of_mem fun leftPresent rightPresent less => by
      rcases List.mem_map.mp leftPresent with ⟨leftEntry, leftEntryPresent, rfl⟩
      rcases List.mem_map.mp rightPresent with ⟨rightEntry, rightEntryPresent, rfl⟩
      have depthCorrect := scheduled.depthCorrect layer.2
      rw [getLayer] at depthCorrect
      exact hierarchyAddressBefore_of_length_eq_of_lt
        ((depthCorrect leftEntry leftEntryPresent).trans
          (depthCorrect rightEntry rightEntryPresent).symm)
        less
  · exact (pairwise_indices_zipIdx layers).imp_of_mem
      fun {leftLayer rightLayer} leftLayerPresent rightLayerPresent indicesLess => by
        intro leftPath leftPathPresent rightPath rightPathPresent
        have leftIndex : leftLayer.2 < layers.length :=
          List.snd_lt_of_mem_zipIdx leftLayerPresent
        have rightIndex : rightLayer.2 < layers.length :=
          List.snd_lt_of_mem_zipIdx rightLayerPresent
        have leftLayerEq : layers.getD leftLayer.2 [] = leftLayer.1 := by
          have fstEq := List.fst_eq_of_mem_zipIdx leftLayerPresent
          simpa [List.getD, leftIndex] using fstEq.symm
        have rightLayerEq : layers.getD rightLayer.2 [] = rightLayer.1 := by
          have fstEq := List.fst_eq_of_mem_zipIdx rightLayerPresent
          simpa [List.getD, rightIndex] using fstEq.symm
        rcases List.mem_map.mp leftPathPresent with
          ⟨leftEntry, leftEntryPresent, rfl⟩
        rcases List.mem_map.mp rightPathPresent with
          ⟨rightEntry, rightEntryPresent, rfl⟩
        have leftDepth := scheduled.depthCorrect leftLayer.2
        have rightDepth := scheduled.depthCorrect rightLayer.2
        rw [leftLayerEq] at leftDepth
        rw [rightLayerEq] at rightDepth
        apply hierarchyAddressBefore_of_length_lt
        rw [leftDepth leftEntry leftEntryPresent, rightDepth rightEntry rightEntryPresent]
        omega

theorem mapCanonicalSourceLayers_append {α : Type*}
    (observe : CanonicalBranchNode → α)
    (left right : List (List CanonicalSourceEntry)) :
    mapCanonicalSourceLayers observe (left ++ right) =
      mapCanonicalSourceLayers observe left ++ mapCanonicalSourceLayers observe right := by
  simp [mapCanonicalSourceLayers]

theorem mapCanonicalSourceLayers_getD {α : Type*}
    (observe : CanonicalBranchNode → α)
    (layers : List (List CanonicalSourceEntry)) (depth : ℕ) :
    (mapCanonicalSourceLayers observe layers).getD depth [] =
      (layers.getD depth []).map fun entry => (entry.1, observe entry.2) := by
  unfold mapCanonicalSourceLayers List.getD
  rw [List.getElem?_map]
  cases layers[depth]? <;> rfl

theorem prefixCanonicalAtomicLayer_mapSource
    (observe : CanonicalBranchNode → CIPAtomicLabel)
    (slot : ℕ) (layer : List CanonicalSourceEntry) :
    prefixCanonicalAtomicLayer slot
        (layer.map fun entry => (entry.1, observe entry.2)) =
      (prefixCanonicalSourceLayer slot layer).map
        (fun entry => (entry.1, observe entry.2)) := by
  simp [prefixCanonicalAtomicLayer, prefixCanonicalSourceLayer, List.map_map,
    Function.comp_def]

theorem prefixCanonicalNatLayer_mapSource
    (observe : CanonicalBranchNode → ℕ)
    (slot : ℕ) (layer : List CanonicalSourceEntry) :
    prefixCanonicalNatLayer slot
        (layer.map fun entry => (entry.1, observe entry.2)) =
      (prefixCanonicalSourceLayer slot layer).map
        (fun entry => (entry.1, observe entry.2)) := by
  simp [prefixCanonicalNatLayer, prefixCanonicalSourceLayer, List.map_map,
    Function.comp_def]

theorem canonicalChildLayerCount_mapCanonicalSourceLayers
    {α : Type*} (children : List CanonicalBranchKey)
    (layers : CanonicalBranchKey → List (List (List ℕ × α)))
    (observe : CanonicalBranchNode → α)
    (aligned : ∀ child, child ∈ children →
      layers child = mapCanonicalSourceLayers observe child.sourceNodes) :
    canonicalChildLayerCount children layers =
      canonicalChildLayerCount children CanonicalBranchKey.sourceNodes := by
  unfold canonicalChildLayerCount
  have generalized : ∀ initial,
      List.foldl (fun longest child => max longest (layers child).length)
          initial children =
        List.foldl (fun longest child => max longest child.sourceNodes.length)
          initial children := by
    induction children with
    | nil => intro initial; rfl
    | cons child children inductionHypothesis =>
        intro initial
        simp only [List.foldl_cons]
        have childAligned := aligned child (by simp)
        have tailAligned : ∀ tail, tail ∈ children →
            layers tail = mapCanonicalSourceLayers observe tail.sourceNodes := by
          intro tail present
          exact aligned tail (by simp [present])
        rw [childAligned]
        simp only [mapCanonicalSourceLayers, List.length_map]
        exact inductionHypothesis tailAligned _
  exact generalized 0

theorem mergeCanonicalAtomicChildren_mapCanonicalSourceLayers
    (children : List CanonicalBranchKey)
    (observe : CanonicalBranchNode → CIPAtomicLabel)
    (aligned : ∀ child, child ∈ children →
      child.rule1a = mapCanonicalSourceLayers observe child.sourceNodes) :
    mergeCanonicalAtomicChildren children =
      mapCanonicalSourceLayers observe (mergeCanonicalSourceChildren children) := by
  unfold mergeCanonicalAtomicChildren mergeCanonicalSourceChildren
    mapCanonicalSourceLayers
  rw [canonicalChildLayerCount_mapCanonicalSourceLayers children
    CanonicalBranchKey.rule1a observe aligned]
  rw [List.map_map]
  apply List.map_congr_left
  intro depth _
  simp only [Function.comp_apply, List.map_flatMap]
  apply List.flatMap_congr
  intro child present
  have keyPresent : child.1 ∈ children := List.fst_mem_of_mem_zipIdx present
  rw [aligned child.1 keyPresent]
  rw [mapCanonicalSourceLayers_getD]
  rw [prefixCanonicalAtomicLayer_mapSource]

theorem mergeCanonicalNatChildren_mapCanonicalSourceLayers
    (children : List CanonicalBranchKey)
    (layers : CanonicalBranchKey → List (List CanonicalNatEntry))
    (observe : CanonicalBranchNode → ℕ)
    (aligned : ∀ child, child ∈ children →
      layers child = mapCanonicalSourceLayers observe child.sourceNodes) :
    mergeCanonicalNatChildren layers children =
      mapCanonicalSourceLayers observe (mergeCanonicalSourceChildren children) := by
  unfold mergeCanonicalNatChildren mergeCanonicalSourceChildren
    mapCanonicalSourceLayers
  rw [canonicalChildLayerCount_mapCanonicalSourceLayers children layers observe aligned]
  rw [List.map_map]
  apply List.map_congr_left
  intro depth _
  simp only [Function.comp_apply, List.map_flatMap]
  apply List.flatMap_congr
  intro child present
  have keyPresent : child.1 ∈ children := List.fst_mem_of_mem_zipIdx present
  rw [aligned child.1 keyPresent]
  rw [mapCanonicalSourceLayers_getD]
  rw [prefixCanonicalNatLayer_mapSource]

/-- Assembly preserves exact source alignment for all three constitutional rules. -/
theorem CanonicalBranchKey.AuthoritativeSourceAligned.assemble
    (mol : RawMolecule) (root : CanonicalBranchKey)
    (children : List CanonicalBranchKey)
    (rootAligned : root.AuthoritativeSourceAligned mol)
    (childrenAligned : ∀ child, child ∈ children →
      child.AuthoritativeSourceAligned mol) :
    (assembleCanonicalBranchKey root children).AuthoritativeSourceAligned mol := by
  rcases rootAligned with ⟨root1a, root1b, root2⟩
  constructor
  · change root.rule1a ++ mergeCanonicalAtomicChildren children =
      mapCanonicalSourceLayers mol.canonicalRule1aLabelAuthoritativeTotal
        (root.sourceNodes ++ mergeCanonicalSourceChildren children)
    rw [mapCanonicalSourceLayers_append, root1a]
    congr 1
    exact mergeCanonicalAtomicChildren_mapCanonicalSourceLayers children _
      (fun child present => (childrenAligned child present).1)
  constructor
  · change root.rule1b ++ mergeCanonicalNatChildren
        (fun child => child.rule1b) children =
      mapCanonicalSourceLayers CanonicalBranchNode.rule1bCode
        (root.sourceNodes ++ mergeCanonicalSourceChildren children)
    rw [mapCanonicalSourceLayers_append, root1b]
    congr 1
    exact mergeCanonicalNatChildren_mapCanonicalSourceLayers children
      CanonicalBranchKey.rule1b _
      (fun child present => (childrenAligned child present).2.1)
  · change root.rule2 ++ mergeCanonicalNatChildren
        (fun child => child.rule2) children =
      mapCanonicalSourceLayers mol.canonicalRule2Mass
        (root.sourceNodes ++ mergeCanonicalSourceChildren children)
    rw [mapCanonicalSourceLayers_append, root2]
    congr 1
    exact mergeCanonicalNatChildren_mapCanonicalSourceLayers children
      CanonicalBranchKey.rule2 _
      (fun child present => (childrenAligned child present).2.2)

/-- Every successful authoritative root observation is aligned with its retained source node. -/
theorem canonicalRootKeyAuthoritative?_sourceAligned
    (mol : RawMolecule) (node : CanonicalBranchNode)
    (complete : Bool) (key : CanonicalBranchKey)
    (computed : mol.canonicalRootKeyAuthoritative? node complete = some key) :
    key.AuthoritativeSourceAligned mol := by
  unfold canonicalRootKeyAuthoritative? at computed
  cases labelComputed : mol.canonicalRule1aLabelAuthoritative? node with
  | none => simp [labelComputed] at computed
  | some label =>
      simp [labelComputed] at computed
      subst key
      simp [CanonicalBranchKey.AuthoritativeSourceAligned,
        mapCanonicalSourceLayers, canonicalRule1aLabelAuthoritativeTotal,
        labelComputed, canonicalRule2Mass, CanonicalBranchNode.rule1bCode]
      cases node.provenance <;> rfl

/-- A successful authoritative root observation retains exactly the singleton root source layer. -/
theorem canonicalRootKeyAuthoritative?_sourceNodes_eq
    (mol : RawMolecule) (node : CanonicalBranchNode)
    (complete : Bool) (key : CanonicalBranchKey)
    (computed : mol.canonicalRootKeyAuthoritative? node complete = some key) :
    key.sourceNodes = [[([], node)]] := by
  unfold canonicalRootKeyAuthoritative? at computed
  cases labelComputed : mol.canonicalRule1aLabelAuthoritative? node with
  | none => simp [labelComputed] at computed
  | some label =>
      simp [labelComputed] at computed
      subst key
      rfl

/-- Every successful authoritative root observation starts the semantic address schedule. -/
theorem canonicalRootKeyAuthoritative?_scheduled
    (mol : RawMolecule) (node : CanonicalBranchNode)
    (complete : Bool) (key : CanonicalBranchKey)
    (computed : mol.canonicalRootKeyAuthoritative? node complete = some key) :
    CanonicalSourceLayersScheduledFrom 0 key.sourceNodes := by
  rw [mol.canonicalRootKeyAuthoritative?_sourceNodes_eq node complete key computed]
  exact CanonicalSourceLayersScheduledFrom.root node

private theorem mapM_mem_source {α β : Type*} (f : α → Option β) :
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
                  mapM_mem_source f inputs tail tailComputed output tailPresent
                exact ⟨source, by simp [sourcePresent], sourceComputed⟩

/-- Every successfully compiled authoritative key is exactly source-aligned. -/
theorem buildCanonicalBranchKeyAuthoritative_sourceAligned
    (mol : RawMolecule) : ∀ fuel node key,
    mol.buildCanonicalBranchKeyAuthoritative fuel node = some key →
      key.AuthoritativeSourceAligned mol
  | 0, node, key, computed =>
      mol.canonicalRootKeyAuthoritative?_sourceAligned node
        (mol.canonicalTerminal node) key computed
  | fuel + 1, node, key, computed => by
      unfold buildCanonicalBranchKeyAuthoritative at computed
      by_cases terminal : mol.canonicalTerminal node = true
      · simp [terminal] at computed
        exact mol.canonicalRootKeyAuthoritative?_sourceAligned node true key computed
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
                      apply CanonicalBranchKey.AuthoritativeSourceAligned.assemble mol root sorted
                        (mol.canonicalRootKeyAuthoritative?_sourceAligned node
                          (sorted.all fun child => child.complete) root rootComputed)
                      intro child present
                      have permutation := sortCanonicalKeys?_perm childKeys sorted sortedComputed
                      have childPresent : child ∈ childKeys := (permutation.mem_iff).mp present
                      obtain ⟨source, sourcePresent, sourceComputed⟩ :=
                        mapM_mem_source (mol.buildCanonicalBranchKeyAuthoritative fuel)
                          children childKeys childKeysComputed child childPresent
                      exact buildCanonicalBranchKeyAuthoritative_sourceAligned mol fuel
                        source child sourceComputed

/-- Every successfully compiled authoritative key retains its sources in strict sphere-major,
then parent-slot-path order. -/
theorem buildCanonicalBranchKeyAuthoritative_scheduled
    (mol : RawMolecule) : ∀ fuel node key,
    mol.buildCanonicalBranchKeyAuthoritative fuel node = some key →
      CanonicalSourceLayersScheduledFrom 0 key.sourceNodes
  | 0, node, key, computed =>
      mol.canonicalRootKeyAuthoritative?_scheduled node
        (mol.canonicalTerminal node) key computed
  | fuel + 1, node, key, computed => by
      unfold buildCanonicalBranchKeyAuthoritative at computed
      by_cases terminal : mol.canonicalTerminal node = true
      · simp [terminal] at computed
        exact mol.canonicalRootKeyAuthoritative?_scheduled node true key computed
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
                      change CanonicalSourceLayersScheduledFrom 0
                        (root.sourceNodes ++ mergeCanonicalSourceChildren sorted)
                      rw [mol.canonicalRootKeyAuthoritative?_sourceNodes_eq node
                        (sorted.all fun child => child.complete) root rootComputed]
                      apply root_cons_mergeCanonicalSourceChildren_scheduled node sorted
                      intro child present
                      have permutation := sortCanonicalKeys?_perm childKeys sorted sortedComputed
                      have childPresent : child ∈ childKeys := (permutation.mem_iff).mp present
                      obtain ⟨source, sourcePresent, sourceComputed⟩ :=
                        mapM_mem_source (mol.buildCanonicalBranchKeyAuthoritative fuel)
                          children childKeys childKeysComputed child childPresent
                      exact buildCanonicalBranchKeyAuthoritative_scheduled mol fuel
                        source child sourceComputed

/-- Public successful branch compilation inherits exact source alignment. -/
theorem branchCanonicalKeyAuthoritative?_sourceAligned
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (computed : branchCanonicalKeyAuthoritative? mol center ligand = some key) :
    key.AuthoritativeSourceAligned mol := by
  unfold branchCanonicalKeyAuthoritative? at computed
  exact mol.buildCanonicalBranchKeyAuthoritative_sourceAligned
    (2 * mol.atomCount + 2) (canonicalRoot center ligand) key computed

/-- Public successful branch compilation retains the exact semantic address schedule. -/
theorem branchCanonicalKeyAuthoritative?_scheduled
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (computed : branchCanonicalKeyAuthoritative? mol center ligand = some key) :
    CanonicalSourceLayersScheduledFrom 0 key.sourceNodes := by
  unfold branchCanonicalKeyAuthoritative? at computed
  exact mol.buildCanonicalBranchKeyAuthoritative_scheduled
    (2 * mol.atomCount + 2) (canonicalRoot center ligand) key computed

/-- The flattened source address schedule of every public authoritative key is strictly ordered by
the declarative sphere-major semantic address relation. -/
theorem branchCanonicalKeyAuthoritative?_sourceAddressSchedule_pairwise
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (computed : branchCanonicalKeyAuthoritative? mol center ligand = some key) :
    key.sourceAddressSchedule.Pairwise HierarchyAddressBefore := by
  have scheduled := mol.branchCanonicalKeyAuthoritative?_scheduled
    center ligand key computed
  exact CanonicalSourceLayersScheduledFrom.flattened_pairwise 0 key.sourceNodes scheduled

end RawMolecule

end TetraStereo.OneCenter
