import TetraStereo.OneCenter.SmilesTetrahedral

set_option autoImplicit false

namespace TetraStereo.UniversalProof.OccurrenceDepthBatchListLawsProofs.OccurrenceDepthBatchListLaws

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule




























/-! ## Generic take/drop reconstruction -/

/-- Cons-list `take`/`drop` reconstruction: the retained batch followed by the remaining
suffix is exactly the original list. -/
theorem takeWhile_append_dropWhile_eq {α : Type} (p : α → Bool) (l : List α) :
    l.takeWhile p ++ l.dropWhile p = l :=
  List.takeWhile_append_dropWhile (p := p) (l := l)

/-- First-node equality of the reconstruction: when the list is a cons, the reconstructed
head is the original head. -/
theorem takeWhile_append_dropWhile_head? {α : Type} (p : α → Bool) (first : α)
    (tail : List α) :
    ((first :: tail).takeWhile p ++ (first :: tail).dropWhile p).head? = some first := by
  rw [takeWhile_append_dropWhile_eq]
  rfl

/-- Length form of the reconstruction: retained length plus remaining length is the
original length. -/
theorem takeWhile_length_add_dropWhile_length {α : Type} (p : α → Bool) (l : List α) :
    (l.takeWhile p).length + (l.dropWhile p).length = l.length := by
  have decomp := congrArg List.length (takeWhile_append_dropWhile_eq p l)
  simpa only [List.length_append] using decomp

/-! ## Nonempty first batch and strict remaining decrease -/

/-- Unfolding of `takeWhile` at a cons whose head satisfies the predicate. -/
theorem takeWhile_cons_eq_of_pos {α : Type} (p : α → Bool) (first : α) (tail : List α)
    (h : p first = true) :
    (first :: tail).takeWhile p = first :: tail.takeWhile p :=
  List.takeWhile_cons_of_pos (by simpa using h)

/-- The first depth batch is nonempty: a cons whose head satisfies the predicate retains at
least the head. -/
theorem takeWhile_length_pos_of_head {α : Type} (p : α → Bool) (first : α) (tail : List α)
    (h : p first = true) :
    0 < ((first :: tail).takeWhile p).length := by
  rw [takeWhile_cons_eq_of_pos p first tail h]
  simp

/-- The remaining suffix strictly decreases in length once a nonempty batch is removed. -/
theorem dropWhile_length_lt_of_head {α : Type} (p : α → Bool) (first : α) (tail : List α)
    (h : p first = true) :
    ((first :: tail).dropWhile p).length < (first :: tail).length := by
  have decomp : ((first :: tail).takeWhile p).length +
      ((first :: tail).dropWhile p).length = (first :: tail).length :=
    takeWhile_length_add_dropWhile_length p (first :: tail)
  have pos : 0 < ((first :: tail).takeWhile p).length :=
    takeWhile_length_pos_of_head p first tail h
  have lt : ((first :: tail).dropWhile p).length <
      ((first :: tail).takeWhile p).length + ((first :: tail).dropWhile p).length :=
    Nat.lt_add_of_pos_left pos
  exact Nat.lt_of_lt_of_le lt (le_of_eq decomp)

/-! ## Retention of order

Elements of the batch and of the remaining suffix are elements of the original list, and
the concatenation `batch ++ rest` reconstructs the original order. -/

/-- Every batch element is retained in the original list. -/
theorem mem_of_mem_takeWhile {α : Type} {p : α → Bool} {a : α} {l : List α}
    (h : a ∈ l.takeWhile p) : a ∈ l := by
  rw [← takeWhile_append_dropWhile_eq p l]
  exact List.mem_append.mpr (Or.inl h)

/-- Every remaining element is retained in the original list. -/
theorem mem_of_mem_dropWhile {α : Type} {p : α → Bool} {a : α} {l : List α}
    (h : a ∈ l.dropWhile p) : a ∈ l := by
  rw [← takeWhile_append_dropWhile_eq p l]
  exact List.mem_append.mpr (Or.inr h)

/-! ## `mapM` of a total callback -/

/-- `mapM` of a total callback equals the pure `map` by the callback's fact function. -/
theorem mapM_eq_map_of_total {α β : Type} (callback : α → Option β) (facts : α → β)
    (nodes : List α) (total : ∀ node ∈ nodes, callback node = some (facts node)) :
    nodes.mapM callback = some (nodes.map facts) := by
  revert total
  induction nodes with
  | nil => intro _; rfl
  | cons first tail ih =>
      intro total
      have head := total first List.mem_cons_self
      have remaining := ih (fun node member => total node (List.mem_cons_of_mem first member))
      simp [List.mapM_cons, head, remaining]

/-! ## Explicit totality interface -/

/-- Explicit list lemma interface: a total, state-independent label function on a given list
of nodes.  This is a LIST premise only; it is never a family success assumption. -/
structure TotalOn
    (label? : OccurrenceAuxState → CanonicalBranchNode → Option OccurrenceAuxFact)
    (facts : CanonicalBranchNode → OccurrenceAuxFact)
    (nodes : List CanonicalBranchNode) : Prop where
  total : ∀ node ∈ nodes, ∀ current, label? current node = some (facts node)

/-! ## Generic authoritative batch theorem -/

/-- Generic authoritative batch discovery: under the explicit list totality interface, the
exact `discoverOccurrenceAuxBatchesAuthoritative?` appends exactly the mapped facts, whenever
the fuel exceeds the node count. -/
theorem authoritative_batches_eq_of_uniform_label
    (label? : OccurrenceAuxState → CanonicalBranchNode → Option OccurrenceAuxFact)
    (facts : CanonicalBranchNode → OccurrenceAuxFact) :
    ∀ (fuel : ℕ) (nodes : List CanonicalBranchNode) (state : OccurrenceAuxState),
      nodes.length < fuel →
      (∀ node ∈ nodes, ∀ current, label? current node = some (facts node)) →
      discoverOccurrenceAuxBatchesAuthoritative? label? fuel nodes state =
        some (state ++ nodes.map facts) := by
  intro fuel
  induction fuel with
  | zero =>
      intro nodes state enough _
      exact absurd enough (Nat.not_lt_zero nodes.length)
  | succ remaining ih =>
      intro nodes state enough uniform
      cases nodes with
      | nil => simp [discoverOccurrenceAuxBatchesAuthoritative?]
      | cons first tail =>
          let predicate : CanonicalBranchNode → Bool := fun node => node.depth == first.depth
          let batch := (first :: tail).takeWhile predicate
          let rest := (first :: tail).dropWhile predicate
          have joined : batch ++ rest = first :: tail :=
            takeWhile_append_dropWhile_eq predicate (first :: tail)
          have batchPositive : 0 < batch.length :=
            takeWhile_length_pos_of_head predicate first tail (by simp [predicate])
          have restEnough : rest.length < remaining := by
            have decrease : rest.length < (first :: tail).length :=
              dropWhile_length_lt_of_head predicate first tail (by simp [predicate])
            have bound : (first :: tail).length ≤ remaining := Nat.le_of_lt_succ enough
            exact Nat.lt_of_lt_of_le decrease bound
          have batchUniform : ∀ node ∈ batch, label? state node = some (facts node) := by
            intro node member
            exact uniform node (by
              rw [← joined]
              exact List.mem_append.mpr (Or.inl member)) state
          have restUniform : ∀ node ∈ rest, ∀ current, label? current node = some (facts node) := by
            intro node member current
            exact uniform node (by
              rw [← joined]
              exact List.mem_append.mpr (Or.inr member)) current
          have batchComputed := mapM_eq_map_of_total (label? state) facts batch batchUniform
          have deeper := ih rest (state ++ batch.map facts) restEnough restUniform
          change (do
            let batchFacts ← batch.mapM (label? state)
            discoverOccurrenceAuxBatchesAuthoritative? label? remaining rest
              (state ++ batchFacts)) = _
          rw [batchComputed]
          change discoverOccurrenceAuxBatchesAuthoritative? label? remaining rest
            (state ++ List.map facts batch) = some (state ++ List.map facts (first :: tail))
          rw [deeper]
          apply congrArg some
          rw [List.append_assoc, ← List.map_append, joined]

/-- The generic theorem at the literal authoritative budget `nodes.length + 1`, stated through
the explicit `TotalOn` list interface. -/
theorem authoritative_batches_budget_length_succ
    (label? : OccurrenceAuxState → CanonicalBranchNode → Option OccurrenceAuxFact)
    (facts : CanonicalBranchNode → OccurrenceAuxFact)
    (nodes : List CanonicalBranchNode) (state : OccurrenceAuxState)
    (h : TotalOn label? facts nodes) :
    discoverOccurrenceAuxBatchesAuthoritative? label? (nodes.length + 1) nodes state =
      some (state ++ nodes.map facts) :=
  authoritative_batches_eq_of_uniform_label label? facts (nodes.length + 1) nodes state
    (Nat.lt_succ_self nodes.length) h.total

/-! ## Depth-batch specialization -/

/-- The exact depth predicate used by the authoritative definition for a fixed head. -/
def depthPredicate (first : CanonicalBranchNode) : CanonicalBranchNode → Bool :=
  fun node => node.depth == first.depth

/-- Batch/rest decomposition with first-node equality for the authoritative depth predicate. -/
theorem depthBatch_decomposition (first : CanonicalBranchNode) (tail : List CanonicalBranchNode) :
    (first :: tail).takeWhile (depthPredicate first) ++
      (first :: tail).dropWhile (depthPredicate first) = first :: tail :=
  takeWhile_append_dropWhile_eq (depthPredicate first) (first :: tail)

/-- Head of the reconstructed depth decomposition is the original first node. -/
theorem depthBatch_head?_eq (first : CanonicalBranchNode) (tail : List CanonicalBranchNode) :
    (((first :: tail).takeWhile (depthPredicate first)) ++
      ((first :: tail).dropWhile (depthPredicate first))).head? = some first :=
  takeWhile_append_dropWhile_head? (depthPredicate first) first tail

/-- The first depth batch is nonempty. -/
theorem depthBatch_nonempty (first : CanonicalBranchNode) (tail : List CanonicalBranchNode) :
    0 < ((first :: tail).takeWhile (depthPredicate first)).length :=
  takeWhile_length_pos_of_head (depthPredicate first) first tail (by simp [depthPredicate])

/-- The remaining suffix after the first depth batch strictly decreases in length. -/
theorem depthRest_length_lt (first : CanonicalBranchNode) (tail : List CanonicalBranchNode) :
    ((first :: tail).dropWhile (depthPredicate first)).length < (first :: tail).length :=
  dropWhile_length_lt_of_head (depthPredicate first) first tail (by simp [depthPredicate])

end TetraStereo.UniversalProof.OccurrenceDepthBatchListLawsProofs.OccurrenceDepthBatchListLaws
