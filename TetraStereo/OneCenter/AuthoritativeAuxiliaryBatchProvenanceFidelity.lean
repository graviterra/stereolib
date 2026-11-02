import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceFactConformance
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Authoritative auxiliary depth-batch provenance

`buildOccurrenceAuxStateFullyAuthoritative?` labels every generated real tetrahedral occurrence
with `occurrenceFactAuthoritative?`, processing occurrences in non-increasing depth order and
committing one whole depth batch at a time.  The binary equation

```lean
buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some aux
```

does not by itself say which state each callback saw.  This module extracts that information from
an actual successful run: it reconstructs the indexed depth-batch history (`AuxBatchLayer`), proves
that the state used for a layer is exactly the initial state extended by the facts of the strictly
deeper preceding layers, and proves that every fact in `aux` was produced by a concrete occurrence
node at that exact predecessor state.  The existing primitive certificate
`authoritativeOrdinaryFactClauses_of_production` is then applied at the recovered state.

The module does **not** identify the authoritative callback `occurrenceFactAuthoritative?` with the
declarative callback `occurrenceFact?`, does not claim that the builder succeeds, and does not
claim any chemical view correctness.
-/

/-! ## Depth-descending occurrence lists -/

/-- Non-increasing depth order of canonical branch nodes. -/
abbrev DepthDescending (nodes : List RawMolecule.CanonicalBranchNode) : Prop :=
  nodes.Pairwise (fun left right => right.depth ≤ left.depth)

theorem depthDescending_cons {node : RawMolecule.CanonicalBranchNode}
    {nodes : List RawMolecule.CanonicalBranchNode}
    (sorted : DepthDescending (node :: nodes)) :
    (∀ other ∈ nodes, other.depth ≤ node.depth) ∧ DepthDescending nodes := by
  simpa [DepthDescending] using List.pairwise_cons.mp sorted

/-! ### Insertion-sort facts -/

theorem mem_insertDescBy {α : Type*} (before : α → α → Bool) (value : α) :
    ∀ (values : List α) (other : α),
      other ∈ insertDescBy before value values ↔ other = value ∨ other ∈ values
  | [], other => by simp [insertDescBy]
  | head :: tail, other => by
      simp only [insertDescBy]
      split
      · simp only [List.mem_cons]
      · simp only [List.mem_cons, mem_insertDescBy before value tail other]
        tauto

theorem mem_sortDescBy {α : Type*} (before : α → α → Bool) :
    ∀ (values : List α) (other : α),
      other ∈ sortDescBy before values ↔ other ∈ values
  | [], other => by simp [sortDescBy]
  | head :: tail, other => by
      simp only [sortDescBy, mem_insertDescBy before head (sortDescBy before tail) other,
        mem_sortDescBy before tail other, List.mem_cons]

theorem insertDescBy_depthDescending (value : RawMolecule.CanonicalBranchNode)
    (values : List RawMolecule.CanonicalBranchNode)
    (sorted : DepthDescending values) :
    DepthDescending (insertDescBy (fun left right => left.depth ≥ right.depth) value values) := by
  induction values with
  | nil => simp [insertDescBy]
  | cons head tail ih =>
      have hd := depthDescending_cons sorted
      have headLe : ∀ other ∈ tail, other.depth ≤ head.depth := hd.1
      have ih' : DepthDescending
          (insertDescBy (fun left right => left.depth ≥ right.depth) value tail) :=
        ih hd.2
      simp only [insertDescBy]
      split
      · rename_i beforeTrue
        have hle : head.depth ≤ value.depth := by simpa using beforeTrue
        change (value :: head :: tail).Pairwise (fun left right => right.depth ≤ left.depth)
        rw [List.pairwise_cons]
        exact ⟨fun other hother => by
          rcases List.mem_cons.mp hother with rfl | htail
          · exact hle
          · exact Nat.le_trans (headLe other htail) hle, sorted⟩
      · rename_i beforeFalse
        have hle : value.depth ≤ head.depth := by
          have hnot : ¬ (head.depth ≤ value.depth) := by
            intro h
            exact beforeFalse (by simpa using h)
          exact Nat.le_of_lt (Nat.lt_of_not_le hnot)
        change (head :: insertDescBy (fun left right => left.depth ≥ right.depth) value tail).Pairwise
          (fun left right => right.depth ≤ left.depth)
        rw [List.pairwise_cons]
        refine ⟨?_, ih'⟩
        intro other hother
        rcases (mem_insertDescBy (fun left right => left.depth ≥ right.depth) value tail other).mp
          hother with rfl | htail
        · exact hle
        · exact headLe other htail

theorem sortDescBy_depthDescending (values : List RawMolecule.CanonicalBranchNode) :
    DepthDescending (sortDescBy (fun left right => left.depth ≥ right.depth) values) := by
  induction values with
  | nil => exact List.Pairwise.nil
  | cons head tail ih =>
      exact insertDescBy_depthDescending head
        (sortDescBy (fun left right => left.depth ≥ right.depth) tail) ih

/-! ### The depth boundary produced by `takeWhile` / `dropWhile` -/

theorem takeWhile_depth_eq (depth : ℕ) (nodes : List RawMolecule.CanonicalBranchNode) :
    ∀ node ∈ nodes.takeWhile (fun node => node.depth == depth), node.depth = depth := by
  intro node hnode
  have hall := List.all_takeWhile (l := nodes) (p := fun node => node.depth == depth)
  have hnodeEq := (List.all_eq_true.mp hall) node hnode
  simpa using hnodeEq

theorem depths_lt_of_dropWhile (first : RawMolecule.CanonicalBranchNode)
    (rest : List RawMolecule.CanonicalBranchNode)
    (sorted : DepthDescending (first :: rest)) :
    ∀ node ∈ (first :: rest).dropWhile (fun node => node.depth == first.depth),
      node.depth < first.depth := by
  intro node hnode
  have droppedSorted : DepthDescending
      ((first :: rest).dropWhile (fun node => node.depth == first.depth)) :=
    List.Pairwise.sublist
      (List.dropWhile_suffix (fun node => node.depth == first.depth)
        (l := first :: rest)).sublist
      sorted
  have droppedSub : List.Sublist
      ((first :: rest).dropWhile (fun node => node.depth == first.depth)) (first :: rest) :=
    (List.dropWhile_suffix (fun node => node.depth == first.depth)
      (l := first :: rest)).sublist
  cases hdrop : (first :: rest).dropWhile (fun node => node.depth == first.depth) with
  | nil => simp [hdrop] at hnode
  | cons head tail =>
      rw [hdrop] at hnode droppedSorted
      have hheadMem : head ∈ (first :: rest).dropWhile
          (fun node => node.depth == first.depth) := by
        rw [hdrop]
        exact List.mem_cons_self ..
      have hheadAll : head ∈ first :: rest := List.Sublist.subset droppedSub hheadMem
      have hheadLe : head.depth ≤ first.depth := by
        rcases List.mem_cons.mp hheadAll with rfl | hmemRest
        · exact Nat.le_refl _
        · exact (depthDescending_cons sorted).1 head hmemRest
      have hfalse : (fun node => node.depth == first.depth) head = false := by
        have hh := List.head?_dropWhile_not (fun node => node.depth == first.depth)
          (first :: rest)
        rw [hdrop] at hh
        simpa using hh
      have hheadNe : head.depth ≠ first.depth := by simpa using hfalse
      have hheadLt : head.depth < first.depth := Nat.lt_of_le_of_ne hheadLe hheadNe
      rcases List.mem_cons.mp hnode with rfl | htail
      · exact hheadLt
      · have htailLe : node.depth ≤ head.depth :=
          (depthDescending_cons droppedSorted).1 node htail
        exact Nat.lt_of_le_of_lt htailLe hheadLt

/-! ## Batch layers -/

/-- One committed depth batch: the occurrences of a single depth, the state they were evaluated
against is supplied by the surrounding run, and the produced facts. -/
structure AuxBatchLayer where
  depth : ℕ
  nodes : List RawMolecule.CanonicalBranchNode
  facts : OccurrenceAuxState

/-- Concatenation of all occurrence nodes of a layer history. -/
def AuxBatchLayerNodes : List AuxBatchLayer → List RawMolecule.CanonicalBranchNode
  | [] => []
  | layer :: rest => layer.nodes ++ AuxBatchLayerNodes rest

/-- Concatenation of all produced facts of a layer history. -/
def AuxBatchLayerFacts : List AuxBatchLayer → OccurrenceAuxState
  | [] => []
  | layer :: rest => layer.facts ++ AuxBatchLayerFacts rest

/-- Earlier layers are strictly deeper than later ones. -/
abbrev AuxBatchDepthsStrict (layers : List AuxBatchLayer) : Prop :=
  layers.Pairwise (fun earlier later => later.depth < earlier.depth)

/-- The state at which each layer is evaluated.  Entry `i` is the initial state extended with the
facts of layers `0, …, i-1`. -/
def AuxBatchStates : List AuxBatchLayer → OccurrenceAuxState → List OccurrenceAuxState
  | [], _ => []
  | layer :: rest, state => state :: AuxBatchStates rest (state ++ layer.facts)

@[simp] theorem AuxBatchStates_length (layers : List AuxBatchLayer)
    (state : OccurrenceAuxState) :
    (AuxBatchStates layers state).length = layers.length := by
  induction layers generalizing state with
  | nil => rfl
  | cons layer rest ih => simp [AuxBatchStates, ih]

/-- Every layer was computed against the corresponding entry of `AuxBatchStates`. -/
inductive AuxBatchLayersRun
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact) :
    List AuxBatchLayer → OccurrenceAuxState → Prop where
  | nil (state : OccurrenceAuxState) : AuxBatchLayersRun label? [] state
  | cons {layer : AuxBatchLayer} {rest : List AuxBatchLayer} {state : OccurrenceAuxState}
      (computed : layer.nodes.mapM (fun node => label? state node) = some layer.facts)
      (tail : AuxBatchLayersRun label? rest (state ++ layer.facts)) :
      AuxBatchLayersRun label? (layer :: rest) state

theorem AuxBatchLayersRun.get_computed
    {label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact} :
    ∀ {layers : List AuxBatchLayer} {state : OccurrenceAuxState},
      AuxBatchLayersRun label? layers state →
      ∀ (i : ℕ) (hi : i < layers.length),
        (layers[i]).nodes.mapM
            (fun node =>
              label? ((AuxBatchStates layers state)[i]'(by simpa using hi)) node) =
          some (layers[i]).facts := by
  intro layers
  induction layers with
  | nil =>
      intro state run i hi
      exact absurd hi (by simp)
  | cons layer rest ih =>
      intro state run i hi
      cases run with
      | cons computed tail =>
          cases i with
          | zero => simpa [AuxBatchStates] using computed
          | succ j =>
              have hj : j < rest.length := by simpa using hi
              simpa [AuxBatchStates] using ih tail j hj

theorem AuxBatchStates.get_eq :
    ∀ (layers : List AuxBatchLayer) (state : OccurrenceAuxState),
      ∀ (i : ℕ) (hi : i < layers.length),
        (AuxBatchStates layers state)[i]'(by simpa using hi) =
          state ++ AuxBatchLayerFacts (layers.take i) := by
  intro layers
  induction layers with
  | nil =>
      intro state i hi
      exact absurd hi (by simp)
  | cons layer rest ih =>
      intro state i hi
      cases i with
      | zero => simp [AuxBatchStates, AuxBatchLayerFacts]
      | succ j =>
          have hj : j < rest.length := by simpa using hi
          have h := ih (state ++ layer.facts) j hj
          simpa [AuxBatchStates, AuxBatchLayerFacts, List.append_assoc] using h

/-! ### Membership and prefix facts for layer histories -/

theorem mem_auxBatchLayerNodes_of_mem_layer {layers : List AuxBatchLayer} {layer : AuxBatchLayer}
    (hlayer : layer ∈ layers) {node : RawMolecule.CanonicalBranchNode}
    (hnode : node ∈ layer.nodes) : node ∈ AuxBatchLayerNodes layers := by
  induction layers with
  | nil => simp at hlayer
  | cons head tail ih =>
      rcases List.mem_cons.mp hlayer with rfl | hmem
      · exact List.mem_append.mpr (Or.inl hnode)
      · exact List.mem_append.mpr (Or.inr (ih hmem))

theorem mem_auxBatchLayerFacts {layers : List AuxBatchLayer} {fact : OccurrenceAuxFact} :
    fact ∈ AuxBatchLayerFacts layers ↔ ∃ layer ∈ layers, fact ∈ layer.facts := by
  induction layers with
  | nil => simp [AuxBatchLayerFacts]
  | cons layer rest ih =>
      simp only [AuxBatchLayerFacts, List.mem_append, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨later, hlater, hfact⟩)
        · exact ⟨layer, Or.inl rfl, h⟩
        · exact ⟨later, Or.inr hlater, hfact⟩
      · rintro ⟨later, rfl | hlater, hfact⟩
        · exact Or.inl hfact
        · exact Or.inr ⟨later, hlater, hfact⟩

theorem mem_auxBatchLayerFacts_of_mem_layer {layers : List AuxBatchLayer} {layer : AuxBatchLayer}
    (hlayer : layer ∈ layers) {fact : OccurrenceAuxFact} (hfact : fact ∈ layer.facts) :
    fact ∈ AuxBatchLayerFacts layers :=
  mem_auxBatchLayerFacts.mpr ⟨layer, hlayer, hfact⟩

theorem auxBatchLayerFacts_append (left right : List AuxBatchLayer) :
    AuxBatchLayerFacts (left ++ right) = AuxBatchLayerFacts left ++ AuxBatchLayerFacts right := by
  induction left with
  | nil => rfl
  | cons layer rest ih => simp [AuxBatchLayerFacts, ih, List.append_assoc]

theorem auxBatchLayerFacts_prefix {left right : List AuxBatchLayer} (hprefix : left <+: right) :
    AuxBatchLayerFacts left <+: AuxBatchLayerFacts right := by
  rcases hprefix with ⟨tail, rfl⟩
  exact ⟨AuxBatchLayerFacts tail, by rw [auxBatchLayerFacts_append]⟩

theorem auxBatchLayerFacts_take_prefix {layers : List AuxBatchLayer} {i j : ℕ} (hij : i ≤ j) :
    AuxBatchLayerFacts (layers.take i) <+: AuxBatchLayerFacts (layers.take j) :=
  auxBatchLayerFacts_prefix (List.take_prefix_take_left hij)

/-! ### `mapM` inversion -/

theorem mapM_mem_of_mem {α β : Type*} (f : α → Option β)
    (inputs : List α) (outputs : List β) (computed : inputs.mapM f = some outputs) :
    ∀ {input : α}, input ∈ inputs → ∀ {output : β}, f input = some output → output ∈ outputs := by
  induction inputs generalizing outputs with
  | nil =>
      intro input present
      simp at present
  | cons head tail ih =>
      intro input present output outputEq
      rw [List.mapM_cons] at computed
      cases headComputed : f head with
      | none => simp [headComputed] at computed
      | some headOut =>
          cases tailComputed : tail.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tailOut =>
              simp [headComputed, tailComputed] at computed
              subst outputs
              rcases List.mem_cons.mp present with rfl | present
              · have hhead : output = headOut := by
                  rw [outputEq] at headComputed
                  exact Option.some.inj headComputed
                subst output
                exact List.mem_cons_self ..
              · exact List.mem_cons_of_mem headOut (ih tailOut tailComputed present outputEq)

theorem mapM_exists_of_mem {α β : Type*} (f : α → Option β)
    (inputs : List α) (outputs : List β) (computed : inputs.mapM f = some outputs) :
    ∀ {output : β}, output ∈ outputs → ∃ input ∈ inputs, f input = some output := by
  induction inputs generalizing outputs with
  | nil =>
      intro output present
      have hout : outputs = [] := by simpa using computed.symm
      subst outputs
      simp at present
  | cons head tail ih =>
      intro output present
      rw [List.mapM_cons] at computed
      cases headComputed : f head with
      | none => simp [headComputed] at computed
      | some headOut =>
          cases tailComputed : tail.mapM f with
          | none => simp [headComputed, tailComputed] at computed
          | some tailOut =>
              simp [headComputed, tailComputed] at computed
              subst outputs
              rcases List.mem_cons.mp present with rfl | present
              · exact ⟨head, List.mem_cons_self .., headComputed⟩
              · rcases ih tailOut tailComputed present with ⟨node, hnode, hcomputed⟩
                exact ⟨node, List.mem_cons_of_mem head hnode, hcomputed⟩

/-! ## Unfolding the authoritative batch discovery -/

theorem discoverAuxBatches_zero_nil
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact)
    (state : OccurrenceAuxState) :
    discoverOccurrenceAuxBatchesAuthoritative? label? 0 [] state = some state := rfl

theorem discoverAuxBatches_zero_cons
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact)
    (head : RawMolecule.CanonicalBranchNode)
    (tail : List RawMolecule.CanonicalBranchNode) (state : OccurrenceAuxState) :
    discoverOccurrenceAuxBatchesAuthoritative? label? 0 (head :: tail) state = none := rfl

theorem discoverAuxBatches_succ_nil
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact)
    (remaining : ℕ) (state : OccurrenceAuxState) :
    discoverOccurrenceAuxBatchesAuthoritative? label? (Nat.succ remaining) [] state = some state :=
  rfl

theorem discoverAuxBatches_succ_cons
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact)
    (remaining : ℕ) (head : RawMolecule.CanonicalBranchNode)
    (tail : List RawMolecule.CanonicalBranchNode) (state : OccurrenceAuxState) :
    discoverOccurrenceAuxBatchesAuthoritative? label? (Nat.succ remaining) (head :: tail) state =
      ((head :: tail).takeWhile (fun node => node.depth == head.depth)).mapM
          (fun node => label? state node) >>=
        (fun batch =>
          discoverOccurrenceAuxBatchesAuthoritative? label? remaining
            ((head :: tail).dropWhile (fun node => node.depth == head.depth))
            (state ++ batch)) := rfl

/-- **Generic exact batch provenance.**  Every successful run of the authoritative batch discovery
on a depth-descending list factors through an indexed history of nonempty equal-depth batches.
Each batch was computed against the initial state extended with exactly the facts of the strictly
deeper batches before it, and its facts are the concatenation of the batch callbacks. -/
theorem discoverAuxBatches_exact_provenance
    (label? : OccurrenceAuxState → RawMolecule.CanonicalBranchNode → Option OccurrenceAuxFact) :
    ∀ (fuel : ℕ) (nodes : List RawMolecule.CanonicalBranchNode)
      (state final : OccurrenceAuxState),
      DepthDescending nodes →
      discoverOccurrenceAuxBatchesAuthoritative? label? fuel nodes state = some final →
      ∃ layers : List AuxBatchLayer,
        AuxBatchLayerNodes layers = nodes ∧
        AuxBatchLayersRun label? layers state ∧
        final = state ++ AuxBatchLayerFacts layers ∧
        AuxBatchDepthsStrict layers ∧
        (∀ layer ∈ layers, 0 < layer.nodes.length) ∧
        (∀ layer ∈ layers, ∀ node ∈ layer.nodes, node.depth = layer.depth) ∧
        (∀ i (hi : i < layers.length),
          (layers[i]).nodes.mapM
              (fun node =>
                label? ((AuxBatchStates layers state)[i]'(by simpa using hi)) node) =
            some (layers[i]).facts) ∧
        (∀ i (hi : i < layers.length),
          (AuxBatchStates layers state)[i]'(by simpa using hi) =
            state ++ AuxBatchLayerFacts (layers.take i)) := by
  intro fuel
  induction fuel with
  | zero =>
      intro nodes state final sorted computed
      cases nodes with
      | nil =>
          rw [discoverAuxBatches_zero_nil] at computed
          have hfin : final = state := (Option.some.inj computed).symm
          subst final
          refine ⟨[], rfl, AuxBatchLayersRun.nil state, ?_, List.Pairwise.nil, ?_, ?_, ?_, ?_⟩
          · simp [AuxBatchLayerFacts]
          · intro layer hlayer
            simp at hlayer
          · intro layer hlayer
            simp at hlayer
          · intro i hi
            simp at hi
          · intro i hi
            simp at hi
      | cons head tail =>
          rw [discoverAuxBatches_zero_cons] at computed
          cases computed
  | succ remaining ih =>
      intro nodes state final sorted computed
      cases nodes with
      | nil =>
          rw [discoverAuxBatches_succ_nil] at computed
          have hfin : final = state := (Option.some.inj computed).symm
          subst final
          refine ⟨[], rfl, AuxBatchLayersRun.nil state, ?_, List.Pairwise.nil, ?_, ?_, ?_, ?_⟩
          · simp [AuxBatchLayerFacts]
          · intro layer hlayer
            simp at hlayer
          · intro layer hlayer
            simp at hlayer
          · intro i hi
            simp at hi
          · intro i hi
            simp at hi
      | cons head tail =>
          rw [discoverAuxBatches_succ_cons] at computed
          dsimp only [Bind.bind] at computed
          simp only [Option.bind_eq_some_iff] at computed
          rcases computed with ⟨batch, hbatch, hrec⟩
          have hdrop : DepthDescending
              ((head :: tail).dropWhile (fun node => node.depth == head.depth)) :=
            List.Pairwise.sublist
              (List.dropWhile_suffix (fun node => node.depth == head.depth)
                (l := head :: tail)).sublist
              sorted
          let layer : AuxBatchLayer :=
            { depth := head.depth
              nodes := (head :: tail).takeWhile (fun node => node.depth == head.depth)
              facts := batch }
          rcases ih ((head :: tail).dropWhile (fun node => node.depth == head.depth))
              (state ++ batch) final hdrop hrec with
            ⟨layers, hnodes, hrun, hfinal, hstrict, hnonempty, hsame, hcomputed, hstates⟩
          have hlayerNonempty : 0 < layer.nodes.length := by
            simp [layer]
          have hlayerSame : ∀ node ∈ layer.nodes, node.depth = layer.depth := by
            intro node hnode
            simpa [layer] using takeWhile_depth_eq head.depth (head :: tail) node hnode
          have hlayerStrict : ∀ later ∈ layers, later.depth < layer.depth := by
            intro later hlater
            have hpos : 0 < later.nodes.length := hnonempty later hlater
            have hne : later.nodes ≠ [] := by
              intro hnil
              rw [hnil] at hpos
              simp at hpos
            rcases List.exists_cons_of_ne_nil hne with ⟨z, zs, hz⟩
            have hzmem : z ∈ later.nodes := by rw [hz]; exact List.mem_cons_self ..
            have hzcovered : z ∈ AuxBatchLayerNodes layers :=
              mem_auxBatchLayerNodes_of_mem_layer hlater hzmem
            have hzlt : z.depth < head.depth := by
              apply depths_lt_of_dropWhile head tail sorted z
              rw [← hnodes]
              exact hzcovered
            have hzeq : z.depth = later.depth := hsame later hlater z hzmem
            simpa [layer, hzeq] using hzlt
          refine ⟨layer :: layers, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · change layer.nodes ++ AuxBatchLayerNodes layers = head :: tail
            rw [hnodes]
            exact List.takeWhile_append_dropWhile
          · exact AuxBatchLayersRun.cons hbatch hrun
          · rw [hfinal]
            simp [layer, AuxBatchLayerFacts, List.append_assoc]
          · change (layer :: layers).Pairwise (fun earlier later => later.depth < earlier.depth)
            rw [List.pairwise_cons]
            exact ⟨hlayerStrict, hstrict⟩
          · intro candidate hcandidate
            rcases List.mem_cons.mp hcandidate with rfl | hmem
            · exact hlayerNonempty
            · exact hnonempty candidate hmem
          · intro candidate hcandidate node hnode
            rcases List.mem_cons.mp hcandidate with rfl | hmem
            · exact hlayerSame node hnode
            · exact hsame candidate hmem node hnode
          · exact AuxBatchLayersRun.get_computed (AuxBatchLayersRun.cons hbatch hrun)
          · exact AuxBatchStates.get_eq (layer :: layers) state

/-! ## The builder's exact provenance -/

/-- The occurrence filter used verbatim by `buildOccurrenceAuxStateFullyAuthoritative?`. -/
def authoritativeOccurrenceCandidates (mol : RawMolecule)
    (nodes : List RawMolecule.CanonicalBranchNode) (center : ℕ) :
    List RawMolecule.CanonicalBranchNode :=
  nodes.filter fun node =>
    node.provenance == RawMolecule.CanonicalNodeProvenance.realAtom && node.atom != center &&
      (mol.atomAt? node.atom).any fun spec => spec.tetrahedral?.isSome

theorem buildOccurrenceAuxStateFullyAuthoritative?_eq_bind (mol : RawMolecule) (fuel center : ℕ) :
    buildOccurrenceAuxStateFullyAuthoritative? mol fuel center =
      (collectCanonicalTreeAuthoritative mol fuel [canonicalCenterRoot center]).bind
        (fun nodes =>
          discoverOccurrenceAuxBatchesAuthoritative? (occurrenceFactAuthoritative? mol fuel)
            ((sortDescBy (fun left right => left.depth ≥ right.depth)
              (authoritativeOccurrenceCandidates mol nodes center)).length + 1)
            (sortDescBy (fun left right => left.depth ≥ right.depth)
              (authoritativeOccurrenceCandidates mol nodes center)) []) := by
  rfl

/-- Provenance of the constructor itself: the evaluator always labels a node with its own
canonical occurrence key and atom. -/
theorem legacyOccurrenceFactAuthoritative?_key_atom (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (fact : OccurrenceAuxFact)
    (computed : legacyOccurrenceFactAuthoritative? mol fuel state node = some fact) :
    fact.key = canonicalOccurrenceKey node ∧ fact.atom = node.atom := by
  unfold legacyOccurrenceFactAuthoritative? at computed
  dsimp only [Bind.bind] at computed
  simp only [Option.bind_eq_some_iff] at computed
  rcases computed with ⟨spec, -, parity, -, roots, -, sorted, -, positions, -, decisions, -, hfinal⟩
  split at hfinal
  · simp at hfinal
  · have hfact := Option.some.inj hfinal
    subst fact
    exact ⟨rfl, rfl⟩

theorem framedOccurrenceFactAuthoritative?_key_atom (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (fact : OccurrenceAuxFact)
    (computed : framedOccurrenceFactAuthoritative? mol fuel state node = some fact) :
    fact.key = canonicalOccurrenceKey node ∧ fact.atom = node.atom := by
  unfold framedOccurrenceFactAuthoritative? at computed
  dsimp only [Bind.bind] at computed
  simp only [Option.bind_eq_some_iff] at computed
  rcases computed with
    ⟨profile, -, spec, -, parity, -, roots, -, sorted, -, positions, -, decisions, -, hfinal⟩
  split at hfinal
  · simp at hfinal
  · have hfact := Option.some.inj hfinal
    subst fact
    exact ⟨rfl, rfl⟩

theorem occurrenceFactAuthoritative?_key_atom (mol : RawMolecule) (fuel : ℕ)
    (state : OccurrenceAuxState) (node : RawMolecule.CanonicalBranchNode)
    (fact : OccurrenceAuxFact)
    (computed : occurrenceFactAuthoritative? mol fuel state node = some fact) :
    fact.key = canonicalOccurrenceKey node ∧ fact.atom = node.atom := by
  cases hprofile : FrameRuntime.profile? mol node with
  | none =>
      have hlegacy : legacyOccurrenceFactAuthoritative? mol fuel state node = some fact := by
        simpa only [occurrenceFactAuthoritative?, hprofile] using computed
      exact legacyOccurrenceFactAuthoritative?_key_atom mol fuel state node fact hlegacy
  | some profile =>
      have hframed : framedOccurrenceFactAuthoritative? mol fuel state node = some fact := by
        simpa only [occurrenceFactAuthoritative?, hprofile] using computed
      exact framedOccurrenceFactAuthoritative?_key_atom mol fuel state node fact hframed

theorem OccurrenceAuxState.factAt?_isSome_of_mem_key (state : OccurrenceAuxState)
    (node : RawMolecule.CanonicalBranchNode) (fact : OccurrenceAuxFact)
    (hmem : fact ∈ state) (hkey : fact.key = canonicalOccurrenceKey node) :
    (state.factAt? node).isSome = true := by
  simp only [OccurrenceAuxState.factAt?, List.find?_isSome]
  exact ⟨fact, hmem, by simp [hkey]⟩

/-- Indexed provenance recovered from an actual successful builder run. -/
structure AuthoritativeBatchProvenance (mol : RawMolecule) (fuel center : ℕ)
    (aux : OccurrenceAuxState) where
  nodes : List RawMolecule.CanonicalBranchNode
  occurrences : List RawMolecule.CanonicalBranchNode
  layers : List AuxBatchLayer
  collected : collectCanonicalTreeAuthoritative mol fuel [canonicalCenterRoot center] = some nodes
  occurrences_eq : occurrences = authoritativeOccurrenceCandidates mol nodes center
  layered : AuxBatchLayerNodes layers =
    sortDescBy (fun left right => left.depth ≥ right.depth) occurrences
  facts_eq : aux = AuxBatchLayerFacts layers
  run : AuxBatchLayersRun (fun state node => occurrenceFactAuthoritative? mol fuel state node)
    layers []
  depths : AuxBatchDepthsStrict layers
  nonempty : ∀ layer ∈ layers, 0 < layer.nodes.length
  sameDepth : ∀ layer ∈ layers, ∀ node ∈ layer.nodes, node.depth = layer.depth
  source : ∀ layer ∈ layers, ∀ node ∈ layer.nodes, node ∈ occurrences
  computed : ∀ i (hi : i < layers.length),
    (layers[i]).nodes.mapM
        (fun node =>
          occurrenceFactAuthoritative? mol fuel
            ((AuxBatchStates layers [])[i]'(by simpa using hi)) node) =
      some (layers[i]).facts
  states : ∀ i (hi : i < layers.length),
    (AuxBatchStates layers [])[i]'(by simpa using hi) = AuxBatchLayerFacts (layers.take i)

/-- **Builder exact provenance.**  A successful authoritative builder run yields an indexed
depth-batch history covering exactly the builder's ordered occurrences, whose facts concatenate to
the produced auxiliary state, and whose every layer was evaluated against the exact accumulated
state of the strictly deeper preceding layers. -/
theorem buildOccurrenceAuxStateFullyAuthoritative?_has_batchProvenance
    (mol : RawMolecule) (fuel center : ℕ) (aux : OccurrenceAuxState)
    (built : buildOccurrenceAuxStateFullyAuthoritative? mol fuel center = some aux) :
    Nonempty (AuthoritativeBatchProvenance mol fuel center aux) := by
  rw [buildOccurrenceAuxStateFullyAuthoritative?_eq_bind] at built
  simp only [Option.bind_eq_some_iff] at built
  rcases built with ⟨nodes, collected, discovered⟩
  let occurrences := authoritativeOccurrenceCandidates mol nodes center
  let ordered := sortDescBy (fun left right => left.depth ≥ right.depth) occurrences
  have sorted : DepthDescending ordered := sortDescBy_depthDescending occurrences
  rcases discoverAuxBatches_exact_provenance
      (fun state node => occurrenceFactAuthoritative? mol fuel state node)
      (ordered.length + 1) ordered [] aux sorted discovered with
    ⟨layers, hnodes, hrun, hfinal, hstrict, hnonempty, hsame, hcomputed, hstates⟩
  refine ⟨{ nodes := nodes
            occurrences := occurrences
            layers := layers
            collected := collected
            occurrences_eq := rfl
            layered := hnodes
            facts_eq := ?_
            run := hrun
            depths := hstrict
            nonempty := hnonempty
            sameDepth := hsame
            source := ?_
            computed := hcomputed
            states := hstates }⟩
  · simpa using hfinal
  · intro layer hlayer node hnode
    have hmem : node ∈ AuxBatchLayerNodes layers :=
      mem_auxBatchLayerNodes_of_mem_layer hlayer hnode
    rw [hnodes] at hmem
    exact (mem_sortDescBy (fun left right => left.depth ≥ right.depth) occurrences node).mp hmem

/-! ## Consequences of recovered provenance -/

theorem AuthoritativeBatchProvenance.exact_predecessor_state
    {mol : RawMolecule} {fuel center : ℕ} {aux : OccurrenceAuxState}
    (provenance : AuthoritativeBatchProvenance mol fuel center aux)
    (i : ℕ) (hi : i < provenance.layers.length) :
    (AuxBatchStates provenance.layers [])[i]'(by simpa using hi) =
      AuxBatchLayerFacts (provenance.layers.take i) :=
  provenance.states i hi

theorem AuthoritativeBatchProvenance.layer_computed_at_exact_state
    {mol : RawMolecule} {fuel center : ℕ} {aux : OccurrenceAuxState}
    (provenance : AuthoritativeBatchProvenance mol fuel center aux)
    (i : ℕ) (hi : i < provenance.layers.length) :
    (provenance.layers[i]).nodes.mapM
        (fun node => occurrenceFactAuthoritative? mol fuel
          ((AuxBatchStates provenance.layers [])[i]'(by simpa using hi)) node) =
      some (provenance.layers[i]).facts :=
  provenance.computed i hi

theorem AuthoritativeBatchProvenance.strictly_deeper_prefix
    {mol : RawMolecule} {fuel center : ℕ} {aux : OccurrenceAuxState}
    (provenance : AuthoritativeBatchProvenance mol fuel center aux)
    (i : ℕ) (hi : i < provenance.layers.length) :
    ∀ layer ∈ provenance.layers.take i, (provenance.layers[i]).depth < layer.depth := by
  intro layer hlayer
  rcases (List.mem_take_iff_getElem.mp hlayer) with ⟨j, hj, hjeq⟩
  have hjlen : j < provenance.layers.length := by omega
  have hji : j < i := by omega
  have hp := (List.pairwise_iff_getElem.mp provenance.depths) j i hjlen hi hji
  simpa [hjeq] using hp

theorem AuthoritativeBatchProvenance.node_candidate
    {mol : RawMolecule} {fuel center : ℕ} {aux : OccurrenceAuxState}
    (provenance : AuthoritativeBatchProvenance mol fuel center aux)
    {layer : AuxBatchLayer} (hlayer : layer ∈ provenance.layers)
    {node : RawMolecule.CanonicalBranchNode} (hnode : node ∈ layer.nodes) :
    node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
      node.atom ≠ center ∧
      (mol.atomAt? node.atom).any (fun spec => spec.tetrahedral?.isSome) = true := by
  have hocc := provenance.source layer hlayer node hnode
  rw [provenance.occurrences_eq] at hocc
  rcases List.mem_filter.mp hocc with ⟨-, hpred⟩
  simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne] at hpred
  exact ⟨hpred.1.1, hpred.1.2, hpred.2⟩

theorem AuthoritativeBatchProvenance.node_mem_collected
    {mol : RawMolecule} {fuel center : ℕ} {aux : OccurrenceAuxState}
    (provenance : AuthoritativeBatchProvenance mol fuel center aux)
    {layer : AuxBatchLayer} (hlayer : layer ∈ provenance.layers)
    {node : RawMolecule.CanonicalBranchNode} (hnode : node ∈ layer.nodes) :
    node ∈ provenance.nodes := by
  have hocc := provenance.source layer hlayer node hnode
  rw [provenance.occurrences_eq] at hocc
  exact (List.mem_filter.mp hocc).1

theorem AuthoritativeBatchProvenance.generated_fact_certified
    {mol : RawMolecule} {fuel center : ℕ} {aux : OccurrenceAuxState}
    (provenance : AuthoritativeBatchProvenance mol fuel center aux)
    (i : ℕ) (hi : i < provenance.layers.length)
    (node : RawMolecule.CanonicalBranchNode) (hnode : node ∈ (provenance.layers[i]).nodes)
    (fact : OccurrenceAuxFact)
    (hfact : occurrenceFactAuthoritative? mol fuel
      ((AuxBatchStates provenance.layers [])[i]'(by simpa using hi)) node = some fact) :
    fact ∈ (provenance.layers[i]).facts ∧
      fact ∈ aux ∧
      fact.key = canonicalOccurrenceKey node ∧
      fact.atom = node.atom ∧
      AuthoritativeOrdinaryFactClauses mol
        ((AuxBatchStates provenance.layers [])[i]'(by simpa using hi)) fuel node fact := by
  have hcomputed := provenance.computed i hi
  have hmemFacts : fact ∈ (provenance.layers[i]).facts :=
    mapM_mem_of_mem (fun node => occurrenceFactAuthoritative? mol fuel
      ((AuxBatchStates provenance.layers [])[i]'(by simpa using hi)) node)
      _ _ hcomputed hnode hfact
  have hlayerMem : (provenance.layers[i]) ∈ provenance.layers :=
    List.mem_iff_getElem.mpr ⟨i, hi, rfl⟩
  have hmemAux : fact ∈ aux := by
    rw [provenance.facts_eq]
    exact mem_auxBatchLayerFacts_of_mem_layer hlayerMem hmemFacts
  obtain ⟨hkey, hatom⟩ :=
    occurrenceFactAuthoritative?_key_atom mol fuel _ node fact hfact
  exact ⟨hmemFacts, hmemAux, hkey, hatom,
    authoritativeOrdinaryFactClauses_of_production hfact⟩

theorem AuthoritativeBatchProvenance.factAt?_isSome
    {mol : RawMolecule} {fuel center : ℕ} {aux : OccurrenceAuxState}
    (provenance : AuthoritativeBatchProvenance mol fuel center aux)
    (i : ℕ) (hi : i < provenance.layers.length)
    (node : RawMolecule.CanonicalBranchNode) (hnode : node ∈ (provenance.layers[i]).nodes)
    (fact : OccurrenceAuxFact)
    (hfact : occurrenceFactAuthoritative? mol fuel
      ((AuxBatchStates provenance.layers [])[i]'(by simpa using hi)) node = some fact) :
    (aux.factAt? node).isSome = true := by
  obtain ⟨-, hmemAux, hkey, -⟩ := provenance.generated_fact_certified i hi node hnode fact hfact
  exact OccurrenceAuxState.factAt?_isSome_of_mem_key aux node fact hmemAux hkey

/-- **Every produced auxiliary fact has an exact certified predecessor.**  The fact is produced by
a concrete occurrence node in a concrete layer, at a state that is exactly the concatenation of the
strictly deeper preceding layer facts; all later layers are strictly shallower, and the existing
primitive production certificate holds at that recovered state. -/
theorem AuthoritativeBatchProvenance.fact_has_exact_certified_predecessor
    {mol : RawMolecule} {fuel center : ℕ} {aux : OccurrenceAuxState}
    (provenance : AuthoritativeBatchProvenance mol fuel center aux)
    {fact : OccurrenceAuxFact} (hfact : fact ∈ aux) :
    ∃ (i : ℕ) (hi : i < provenance.layers.length)
      (node : RawMolecule.CanonicalBranchNode),
      node ∈ (provenance.layers[i]).nodes ∧
      occurrenceFactAuthoritative? mol fuel
        ((AuxBatchStates provenance.layers [])[i]'(by simpa using hi)) node = some fact ∧
      (AuxBatchStates provenance.layers [])[i]'(by simpa using hi) =
        AuxBatchLayerFacts (provenance.layers.take i) ∧
      (∀ layer ∈ provenance.layers.take i,
        (provenance.layers[i]).depth < layer.depth) ∧
      AuthoritativeOrdinaryFactClauses mol
        ((AuxBatchStates provenance.layers [])[i]'(by simpa using hi)) fuel node fact ∧
      (∀ (j : ℕ) (hj : j < provenance.layers.length), i < j →
        (provenance.layers[j]).depth < (provenance.layers[i]).depth) := by
  have hmemLayers : fact ∈ AuxBatchLayerFacts provenance.layers := by
    rw [← provenance.facts_eq]
    exact hfact
  rcases mem_auxBatchLayerFacts.mp hmemLayers with ⟨layer, hlayer, hfactLayer⟩
  rcases List.mem_iff_getElem.mp hlayer with ⟨i, hi, rfl⟩
  have hcomputed := provenance.computed i hi
  rcases mapM_exists_of_mem (fun node => occurrenceFactAuthoritative? mol fuel
      ((AuxBatchStates provenance.layers [])[i]'(by simpa using hi)) node)
      _ _ hcomputed hfactLayer with
    ⟨node, hnode, hnodeFact⟩
  have hlayerMem : (provenance.layers[i]) ∈ provenance.layers :=
    List.mem_iff_getElem.mpr ⟨i, hi, rfl⟩
  refine ⟨i, hi, node, hnode, hnodeFact, provenance.states i hi,
    provenance.strictly_deeper_prefix i hi, ?_, ?_⟩
  · exact authoritativeOrdinaryFactClauses_of_production hnodeFact
  · intro j hj hij
    exact (List.pairwise_iff_getElem.mp provenance.depths) i j hi hj hij

theorem AuthoritativeBatchProvenance.state_prefix_of_le
    {mol : RawMolecule} {fuel center : ℕ} {aux : OccurrenceAuxState}
    (provenance : AuthoritativeBatchProvenance mol fuel center aux)
    {i j : ℕ} (hi : i < provenance.layers.length)
    (hj : j < provenance.layers.length) (hij : i ≤ j) :
    (AuxBatchStates provenance.layers [])[i]'(by simpa using hi) <+:
      (AuxBatchStates provenance.layers [])[j]'(by simpa using hj) := by
  rw [provenance.states i hi, provenance.states j hj]
  exact auxBatchLayerFacts_take_prefix hij

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.depthDescending_cons
assert_kernel_only TetraStereo.OneCenter.mem_insertDescBy
assert_kernel_only TetraStereo.OneCenter.mem_sortDescBy
assert_kernel_only TetraStereo.OneCenter.insertDescBy_depthDescending
assert_kernel_only TetraStereo.OneCenter.sortDescBy_depthDescending
assert_kernel_only TetraStereo.OneCenter.takeWhile_depth_eq
assert_kernel_only TetraStereo.OneCenter.depths_lt_of_dropWhile
assert_kernel_only TetraStereo.OneCenter.AuxBatchStates_length
assert_kernel_only TetraStereo.OneCenter.AuxBatchLayersRun.get_computed
assert_kernel_only TetraStereo.OneCenter.AuxBatchStates.get_eq
assert_kernel_only TetraStereo.OneCenter.mem_auxBatchLayerNodes_of_mem_layer
assert_kernel_only TetraStereo.OneCenter.mem_auxBatchLayerFacts
assert_kernel_only TetraStereo.OneCenter.mem_auxBatchLayerFacts_of_mem_layer
assert_kernel_only TetraStereo.OneCenter.auxBatchLayerFacts_append
assert_kernel_only TetraStereo.OneCenter.auxBatchLayerFacts_prefix
assert_kernel_only TetraStereo.OneCenter.auxBatchLayerFacts_take_prefix
assert_kernel_only TetraStereo.OneCenter.mapM_mem_of_mem
assert_kernel_only TetraStereo.OneCenter.mapM_exists_of_mem
assert_kernel_only TetraStereo.OneCenter.discoverAuxBatches_exact_provenance
assert_kernel_only TetraStereo.OneCenter.buildOccurrenceAuxStateFullyAuthoritative?_eq_bind
assert_kernel_only TetraStereo.OneCenter.legacyOccurrenceFactAuthoritative?_key_atom
assert_kernel_only TetraStereo.OneCenter.framedOccurrenceFactAuthoritative?_key_atom
assert_kernel_only TetraStereo.OneCenter.occurrenceFactAuthoritative?_key_atom
assert_kernel_only TetraStereo.OneCenter.OccurrenceAuxState.factAt?_isSome_of_mem_key
assert_kernel_only TetraStereo.OneCenter.buildOccurrenceAuxStateFullyAuthoritative?_has_batchProvenance
assert_kernel_only TetraStereo.OneCenter.AuthoritativeBatchProvenance.exact_predecessor_state
assert_kernel_only TetraStereo.OneCenter.AuthoritativeBatchProvenance.layer_computed_at_exact_state
assert_kernel_only TetraStereo.OneCenter.AuthoritativeBatchProvenance.strictly_deeper_prefix
assert_kernel_only TetraStereo.OneCenter.AuthoritativeBatchProvenance.node_candidate
assert_kernel_only TetraStereo.OneCenter.AuthoritativeBatchProvenance.node_mem_collected
assert_kernel_only TetraStereo.OneCenter.AuthoritativeBatchProvenance.generated_fact_certified
assert_kernel_only TetraStereo.OneCenter.AuthoritativeBatchProvenance.factAt?_isSome
assert_kernel_only TetraStereo.OneCenter.AuthoritativeBatchProvenance.fact_has_exact_certified_predecessor
assert_kernel_only TetraStereo.OneCenter.AuthoritativeBatchProvenance.state_prefix_of_le
