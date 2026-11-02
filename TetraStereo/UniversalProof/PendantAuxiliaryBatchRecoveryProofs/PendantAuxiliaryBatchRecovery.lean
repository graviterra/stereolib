import TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery

set_option autoImplicit false

namespace TetraStereo.UniversalProof.PendantAuxiliaryBatchRecoveryProofs.PendantAuxiliaryBatchRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery
open TetraStereo.UniversalProof.FiniteCanonicalCollectorRecoveryProofs.FiniteCanonicalCollectorRecovery
open TetraStereo.UniversalProof.NonleafPublicOccurrenceRecoveryProofs.NonleafPublicOccurrenceRecovery
open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery














/-- Raw-domain facts only: each actual observed tag is on a physical pendant C(H,F,Br) site.
The domain need not enumerate sites or supply any successful generated callback. -/
structure PendantFamily (raw : RawMolecule) : Prop where
  well : raw.WellFormed
  written : raw.WrittenNeighborExact
  taggedSite : ∀ atom spec, raw.atomAt? atom = some spec → spec.tetrahedral?.isSome = true →
    Nonempty (PendantSite raw atom)

/-- Exact predicate and original occurrence order consumed by the production builder. -/
def selectedNodes (raw : RawMolecule) (root fuel : Nat) : List CanonicalBranchNode :=
  (prefixTree raw root 0 fuel).filter fun node =>
    node.provenance == CanonicalNodeProvenance.realAtom && node.atom != root &&
      (raw.atomAt? node.atom).any fun spec => spec.tetrahedral?.isSome

def orderedNodes (raw : RawMolecule) (root fuel : Nat) : List CanonicalBranchNode :=
  sortDescBy (fun left right => left.depth ≥ right.depth) (selectedNodes raw root fuel)

/-- Projection from the ACTUAL []/0 local callback. The fallback is used only outside the
successful selected domain; selected_callback_uniform proves it unreachable before any use. -/
noncomputable def nodeFact (raw : RawMolecule) (node : CanonicalBranchNode) : OccurrenceAuxFact :=
  (occurrenceFactAuthoritative? raw 0 [] node).getD
    { key := canonicalOccurrenceKey node, atom := node.atom,
      descriptor := .R, uppercase := false, priorityPositions := [] }

private theorem insert_permutation {α : Type} (before : α → α → Bool)
    (value : α) (values : List α) : (insertDescBy before value values).Perm (value :: values) := by
  induction values with
  | nil => exact List.Perm.refl _
  | cons head tail ih =>
      unfold insertDescBy
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons head ih).trans (List.Perm.swap value head tail)

/-- Structural depth sorting changes order, not the original selected occurrence objects. -/
theorem ordered_nodes_permutation (raw : RawMolecule) (root fuel : Nat) :
    (orderedNodes raw root fuel).Perm (selectedNodes raw root fuel) := by
  unfold orderedNodes
  generalize selectedNodes raw root fuel = nodes
  induction nodes with
  | nil => exact List.Perm.refl _
  | cons first tail ih =>
      exact (insert_permutation _ first (sortDescBy _ tail)).trans (List.Perm.cons first ih)

/-- Actual selection entails an actual real generated child of a physical pendant site,
including recovery of its original incoming backbone parent. -/
theorem selected_pendant_structure (raw : RawMolecule) (family : PendantFamily raw)
    (root fuel : Nat) (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (node : CanonicalBranchNode) (member : node ∈ selectedNodes raw root fuel) :
    ∃ spec parity, ∃ site : PendantSite raw node.atom, ∃ parent,
      raw.atomAt? node.atom = some spec ∧ spec.tetrahedral? = some parity ∧
      node.provenance = CanonicalNodeProvenance.realAtom ∧
      CanonicalCenterTreeNode raw root parent ∧ node ∈ raw.canonicalChildren parent ∧
      parent.atom = site.backbone := by
  rcases List.mem_filter.mp member with ⟨generatedMember, passes⟩
  have realPart := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp passes).1).1
  have real : node.provenance = CanonicalNodeProvenance.realAtom := by simpa using realPart
  have different : node.atom ≠ root := by
    intro equal
    simp [equal] at passes
  cases lookup : raw.atomAt? node.atom with
  | none => simp [lookup] at passes
  | some spec =>
      have tagged : spec.tetrahedral?.isSome = true := by
        simpa only [lookup, Option.any_some] using (Bool.and_eq_true_iff.mp passes).2
      obtain ⟨site⟩ := family.taggedSite node.atom spec lookup tagged
      obtain ⟨parent, parentGenerated, child, entry⟩ := collected_pendant_entry raw family.well
        root node.atom fuel rootBound rootCarbon site node generatedMember real rfl different
      cases parityObserved : spec.tetrahedral? with
      | none => simp [parityObserved] at tagged
      | some parity =>
          exact ⟨spec, parity, site, parent, rfl, parityObserved, real, parentGenerated, child, entry⟩

/-- Every selected actual callback returns one fixed actual fact at every state and fuel;
this is DERIVED from physical raw structure and actual generated membership. -/
theorem selected_callback_uniform (raw : RawMolecule) (family : PendantFamily raw)
    (root fuel : Nat) (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (node : CanonicalBranchNode) (member : node ∈ selectedNodes raw root fuel) :
    ∀ state budget, occurrenceFactAuthoritative? raw budget state node = some (nodeFact raw node) := by
  obtain ⟨spec, parity, site, parent, lookup, tag, real, parentGenerated, child, _⟩ :=
    selected_pendant_structure raw family root fuel rootBound rootCarbon node member
  obtain ⟨positions, uniform⟩ := actual_interior_fact_uniform raw family.well family.written
    root node.atom rootBound rootCarbon site parentGenerated child real rfl spec lookup parity tag
  have baseline := uniform [] 0
  have representative : nodeFact raw node = interiorFact node positions
      (RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions)) := by
    simp [nodeFact, baseline]
  intro state budget
  rw [representative]
  exact uniform state budget

theorem ordered_callback_uniform (raw : RawMolecule) (family : PendantFamily raw)
    (root fuel : Nat) (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (node : CanonicalBranchNode) (member : node ∈ orderedNodes raw root fuel) :
    ∀ state budget, occurrenceFactAuthoritative? raw budget state node = some (nodeFact raw node) :=
  selected_callback_uniform raw family root fuel rootBound rootCarbon node
    ((ordered_nodes_permutation raw root fuel).mem_iff.mp member)

private theorem mapM_uniform {α β : Type} (callback : α → Option β) (facts : α → β)
    (nodes : List α) (uniform : ∀ node ∈ nodes, callback node = some (facts node)) :
    nodes.mapM callback = some (nodes.map facts) := by
  revert uniform
  induction nodes with
  | nil => intro _; rfl
  | cons first tail ih =>
      intro uniform
      have head := uniform first List.mem_cons_self
      have remaining := ih (fun node member => uniform node (List.mem_cons_of_mem first member))
      simp [List.mapM_cons, head, remaining]

/-- Library INTERMEDIATE only: all-success callback premise is discharged by the physical
family in actual_pendant_batches below; it is never substituted as the final family domain. -/
theorem batches_eq_of_uniform_label
    (label? : OccurrenceAuxState → CanonicalBranchNode → Option OccurrenceAuxFact)
    (facts : CanonicalBranchNode → OccurrenceAuxFact) (fuel : Nat)
    (nodes : List CanonicalBranchNode) (state : OccurrenceAuxState)
    (enough : nodes.length < fuel)
    (uniform : ∀ node ∈ nodes, ∀ current, label? current node = some (facts node)) :
    discoverOccurrenceAuxBatchesAuthoritative? label? fuel nodes state =
      some (state ++ nodes.map facts) := by
  induction fuel generalizing nodes state with
  | zero => omega
  | succ remaining ih =>
      cases nodes with
      | nil => simp [discoverOccurrenceAuxBatchesAuthoritative?]
      | cons first tail =>
          let predicate := fun node : CanonicalBranchNode => node.depth == first.depth
          let batch := (first :: tail).takeWhile predicate
          let rest := (first :: tail).dropWhile predicate
          have joined : batch ++ rest = first :: tail := List.takeWhile_append_dropWhile
          have sizes := congrArg List.length joined
          simp only [List.length_append, List.length_cons] at sizes
          have batchPositive : 0 < batch.length := by
            change 0 < ((first :: tail).takeWhile predicate).length
            rw [List.takeWhile_cons_of_pos (by simp [predicate])]
            simp
          have restEnough : rest.length < remaining := by
            simp only [List.length_cons] at enough
            omega
          have batchUniform : ∀ node ∈ batch, label? state node = some (facts node) := by
            intro node member
            have retained : node ∈ first :: tail := by
              rw [← joined]
              exact List.mem_append.mpr (Or.inl member)
            exact uniform node retained state
          have restUniform : ∀ node ∈ rest, ∀ current, label? current node = some (facts node) := by
            intro node member current
            have retained : node ∈ first :: tail := by
              rw [← joined]
              exact List.mem_append.mpr (Or.inr member)
            exact uniform node retained current
          have batchComputed := mapM_uniform (label? state) facts batch batchUniform
          have deeper := ih rest (state ++ batch.map facts) restEnough restUniform
          change (do
            let batchFacts ← batch.mapM (label? state)
            discoverOccurrenceAuxBatchesAuthoritative? label? remaining rest (state ++ batchFacts)) = _
          rw [batchComputed]
          change discoverOccurrenceAuxBatchesAuthoritative? label? remaining rest
            (state ++ List.map facts batch) = some (state ++ List.map facts (first :: tail))
          rw [deeper]
          apply congrArg some
          rw [List.append_assoc, ← List.map_append, joined]

/-- Actual ordered-batch discovery succeeds for ANY initial state. No callback/state/frame
success is a domain field: selected-node uniformity is derived above from raw pendant facts. -/
theorem actual_pendant_batches (raw : RawMolecule) (family : PendantFamily raw)
    (root fuel : Nat) (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (initial : OccurrenceAuxState) :
    discoverOccurrenceAuxBatchesAuthoritative? (occurrenceFactAuthoritative? raw fuel)
      ((orderedNodes raw root fuel).length + 1) (orderedNodes raw root fuel) initial =
      some (initial ++ (orderedNodes raw root fuel).map (nodeFact raw)) := by
  apply batches_eq_of_uniform_label
  · omega
  · intro node member current
    exact ordered_callback_uniform raw family root fuel rootBound rootCarbon node member current fuel

/-- The exact environment materialized by the actual authoritative production builder. -/
noncomputable def actualAuxiliaryState (raw : RawMolecule) (root fuel : Nat) : OccurrenceAuxState :=
  (orderedNodes raw root fuel).map (nodeFact raw)

/-- GENERAL actual whole auxiliary build from finite collection + physical tagged pendant domain.
There may be arbitrarily many tags/cycles. No OnlyCenterTagged or supplied expected tree/state. -/
theorem actual_auxiliary_build (raw : RawMolecule) (family : PendantFamily raw)
    (root fuel : Nat) (rootBound : root < raw.atomCount) (rootCarbon : raw.atomZAt root = 6)
    (enough : raw.atomCount + 1 ≤ fuel) :
    buildOccurrenceAuxStateFullyAuthoritative? raw fuel root = some (actualAuxiliaryState raw root fuel) := by
  have collected := actual_collector_complete raw root fuel family.well rootBound enough
  unfold buildOccurrenceAuxStateFullyAuthoritative?
  rw [collected]
  change discoverOccurrenceAuxBatchesAuthoritative? (occurrenceFactAuthoritative? raw fuel)
    ((orderedNodes raw root fuel).length + 1) (orderedNodes raw root fuel) [] = _
  simpa only [List.nil_append, actualAuxiliaryState] using
    actual_pendant_batches raw family root fuel rootBound rootCarbon []

/-- Actual production evidence counts retain the derived full state; no empty-state substitute. -/
def publicFact (root : Nat) (state : OccurrenceAuxState) (positions : List Nat)
    (descriptor : RS) : RawDescriptorFact where
  atom := root
  descriptor := descriptor
  uppercase := true
  evidenceSize := max 1 state.length
  decisiveRule? := none
  descriptorDependentPairs := state.length
  priorityPositions := positions

/-- Actual PUBLIC occurrence consumer on a multitag pendant family, using its own derived full
state. The expected descriptor is never an input; parity and written-position computation derive it. -/
theorem actual_public_pendant_fact (raw : RawMolecule) (family : PendantFamily raw)
    (root fuel : Nat) (spec : AtomSpec) (lookup : raw.atomAt? root = some spec)
    (parity : TetrahedralInputParity) (tag : spec.tetrahedral? = some parity)
    (enough : raw.atomCount + 1 ≤ fuel) :
    ∃ positions, tetrahedralOccurrenceFact? raw fuel root =
      some (publicFact root (actualAuxiliaryState raw root fuel) positions
        (RawMolecule.descriptorOfParity parity (RawMolecule.permutationIsEven positions))) := by
  obtain ⟨site⟩ := family.taggedSite root spec lookup (by simp [tag])
  have domain := PendantSite.atomic_domain raw family.well root site
  have stateComputed := actual_auxiliary_build raw family root fuel site.bound site.carbon enough
  obtain ⟨positions, localComputed⟩ := actual_local_fact raw root domain family.written
    (PendantSite.four raw root site) spec lookup parity tag (actualAuxiliaryState raw root fuel) fuel
  refine ⟨positions, ?_⟩
  unfold tetrahedralOccurrenceFact? tetrahedralOccurrenceFactAuthoritative?
  change (do
    let actualState ← buildOccurrenceAuxStateFullyAuthoritative? raw fuel root
    let actualFact ← occurrenceFactAuthoritative? raw fuel actualState (canonicalCenterRoot root)
    some ({ atom := root, descriptor := actualFact.descriptor, uppercase := actualFact.uppercase, evidenceSize := max 1 actualState.length, decisiveRule? := none, descriptorDependentPairs := actualState.length, priorityPositions := actualFact.priorityPositions } : RawDescriptorFact)) = _
  simp [stateComputed, localComputed, publicFact, recoveredFact]

namespace TwoPendantBatch

open TetraStereo.UniversalProof.NativeInitialSeedRuntimeSupportProofsLibrary.GeneratedPendantOccurrenceRecovery.TwoPendants

def rootSite : PendantSite raw 0 where
  backbone := 1
  hydrogen := 2
  fluorine := 3
  bromine := 4
  bound := by decide +kernel
  carbon := by decide +kernel
  neighbors := List.Perm.refl _
  single := by
    intro other member
    change other ∈ [1, 2, 3, 4] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide +kernel
  backboneCarbon := by decide +kernel
  hydrogenZ := by decide +kernel
  fluorineZ := by decide +kernel
  bromineZ := by decide +kernel
  hydrogenRow := rfl
  fluorineRow := rfl
  bromineRow := rfl

/-- Both actual tags have physical pendant domains. No global singleton-tag restriction. -/
theorem actual_family : PendantFamily raw := by
  refine ⟨actual_admissible.1.1, actual_written, ?_⟩
  intro atom spec lookup tagged
  have bound := listGet?_eq_some_implies_lt raw.atoms atom spec lookup
  change atom < 11 at bound
  interval_cases atom <;> simp [raw, atomAt?, listGet?] at lookup
  all_goals subst spec
  all_goals first
    | exact ⟨rootSite⟩
    | exact ⟨site⟩
    | simp [AtomSpec.aliphatic, hydrogen] at tagged

/-- Actual original selected interior occurrence; this checks selection/order, not a label input. -/
theorem actual_ordered : orderedNodes raw 0 12 = [daughter] := by decide +kernel

theorem actual_auxiliary : buildOccurrenceAuxStateFullyAuthoritative? raw 12 0 =
    some (actualAuxiliaryState raw 0 12) :=
  actual_auxiliary_build raw actual_family 0 12 (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem actual_auxiliary_nonempty : (actualAuxiliaryState raw 0 12).length = 1 := by
  unfold actualAuxiliaryState
  rw [actual_ordered]
  rfl

/-- The actual public consumer uses nonempty actual deeper evidence. No caller state/tree/sort/
positions/descriptor is accepted, and no empty-environment simplification replaces this state. -/
theorem actual_public_nonempty :
    ∃ positions, tetrahedralOccurrenceFact? raw 12 0 =
      some (publicFact 0 (actualAuxiliaryState raw 0 12) positions
        (RawMolecule.descriptorOfParity .clockwise (RawMolecule.permutationIsEven positions))) ∧
      (actualAuxiliaryState raw 0 12).length = 1 := by
  obtain ⟨positions, computed⟩ := actual_public_pendant_fact raw actual_family 0 12
    { AtomSpec.aliphatic .C with tetrahedral? := some .clockwise } rfl .clockwise rfl (by decide +kernel)
  exact ⟨positions, computed, actual_auxiliary_nonempty⟩

end TwoPendantBatch

end TetraStereo.UniversalProof.PendantAuxiliaryBatchRecoveryProofs.PendantAuxiliaryBatchRecovery
