import TetraStereo.OneCenter.CanonicalRule3Hierarchy
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace RawMolecule

/-!
# Source provenance of stored addressed Rule-3 observations

`CanonicalRule3Hierarchy` compiles a recursive Rules-1a--3 key from a caller-supplied child
enumerator and a caller-supplied node observer, sorts sibling keys, and merges the addressed
observation evidence bottom-up.  The comparison projection and the alignment of stored
observations with the compared Rule-3 priority layers are already proved there.

This leaf module proves the missing *source-binding* property of that construction:

> every addressed observation stored in a successfully compiled key originates from a source node
> reachable through the supplied child enumerator, and the supplied observer returned exactly that
> observation at that node.

The statement is deliberately generic.  It mentions no SMILES perception, no expected key and no
expected geometry: the compiler cannot manufacture evidence that the observer did not return.
Because the returned value is the observer's own `CanonicalRule3Observation`, the physical unit,
the near/far endpoints and the incoming entry are preserved verbatim; sorting only transports the
evidence and never reconstructs numeric priorities.  The latter fact is recorded separately through
the existing `Rule3Aligned` law.

The SMILES instantiation (`rule3BranchChildren`, `rule3BranchObserver`,
`compileRule3HierarchyKeyComplete?`) lives in the staged companion module because the current main
`SmilesTetrahedral` still uses the old flat Rule-3 semantics.  No chemical-validity claim is made
here for policy flips or exclusions.
-/

/-! ## Reachability through the supplied child enumerator -/

/-- Reachability from a root node through the caller's child enumerator.

This is the exact structural relation used by `buildCanonicalRule3Key?`; it deliberately does not
mention atom identifiers, atom counts, depth fuel, or the order in which siblings are sorted. -/
inductive SourceReachable (children : CanonicalBranchNode → List CanonicalBranchNode) :
    CanonicalBranchNode → CanonicalBranchNode → Prop
  /-- The root itself is reachable. -/
  | refl (node : CanonicalBranchNode) : SourceReachable children node node
  /-- One child step followed by a reachable suffix. -/
  | step {node child source : CanonicalBranchNode} :
      child ∈ children node →
      SourceReachable children child source →
      SourceReachable children node source

/-! ## Addressed observation membership -/

/-- A stored observation entry occurs in the retained evidence at the given address.

The evidence is the same `observations` field carried by `CanonicalRule3Key`; an entry is a pair of
its sibling-slot address and the observation value. -/
def ObservationEntryMem
    (observations : List (List (List ℕ × CanonicalRule3Observation)))
    (addr : List ℕ) (value : CanonicalRule3Observation) : Prop :=
  ∃ layer, layer ∈ observations ∧ (addr, value) ∈ layer

/-- Address membership distributes through `++`, matching the root-plus-merged layout of
`assembleCanonicalRule3Key`. -/
theorem observationEntryMem_append
    {left right : List (List (List ℕ × CanonicalRule3Observation))}
    {addr : List ℕ} {value : CanonicalRule3Observation} :
    ObservationEntryMem (left ++ right) addr value ↔
      ObservationEntryMem left addr value ∨ ObservationEntryMem right addr value := by
  unfold ObservationEntryMem
  constructor
  · rintro ⟨layer, layerMember, entryMember⟩
    rcases List.mem_append.mp layerMember with leftMember | rightMember
    · exact Or.inl ⟨layer, leftMember, entryMember⟩
    · exact Or.inr ⟨layer, rightMember, entryMember⟩
  · rintro (⟨layer, layerMember, entryMember⟩ | ⟨layer, layerMember, entryMember⟩)
    · exact ⟨layer, List.mem_append_left right layerMember, entryMember⟩
    · exact ⟨layer, List.mem_append_right left layerMember, entryMember⟩

/-- The root evidence contains exactly the observation supplied at the root. -/
theorem observationEntryMem_rule3ObservationRoot
    {rootObservation : Option CanonicalRule3Observation}
    {addr : List ℕ} {value : CanonicalRule3Observation}
    (mem : ObservationEntryMem (rule3ObservationRoot rootObservation) addr value) :
    rootObservation = some value := by
  obtain ⟨layer, layerMember, entryMember⟩ := mem
  cases rootObservation with
  | none =>
      simp [rule3ObservationRoot] at layerMember
      subst layer
      simp at entryMember
  | some observed =>
      simp [rule3ObservationRoot] at layerMember
      subst layer
      simp only [List.mem_singleton, Prod.mk.injEq] at entryMember
      obtain ⟨_, valueEq⟩ := entryMember
      rw [valueEq]

/-- Lifting an entry out of `getD` recovers the layer it came from. -/
theorem mem_of_mem_getD {α : Type*} {layers : List (List α)} {depth : ℕ} {entry : α}
    (member : entry ∈ layers.getD depth []) :
    ∃ layer, layer ∈ layers ∧ entry ∈ layer := by
  unfold List.getD at member
  cases fetched : layers[depth]? with
  | none => simp [fetched] at member
  | some layer =>
      exact ⟨layer, List.mem_of_getElem? fetched, by simpa [fetched] using member⟩

/-- Every stored entry of the addressed child merge comes from one child's own evidence, with the
child's final sibling slot prefixed to the address. -/
theorem observationEntryMem_mergeObservationObserved
    {children : List (List (List (List ℕ × CanonicalRule3Observation)))}
    {addr : List ℕ} {value : CanonicalRule3Observation}
    (mem : ObservationEntryMem (mergeObservationObserved children) addr value) :
    ∃ child ∈ children.zipIdx, ∃ rest : List ℕ,
      addr = child.2 :: rest ∧ ObservationEntryMem child.1 rest value := by
  obtain ⟨layer, layerMember, entryMember⟩ := mem
  unfold mergeObservationObserved at layerMember
  obtain ⟨depth, _, layerEq⟩ := List.mem_map.mp layerMember
  subst layer
  obtain ⟨child, childMember, prefixMember⟩ := List.mem_flatMap.mp entryMember
  unfold prefixCanonicalObservationLayer at prefixMember
  obtain ⟨entry, sourceEntryMember, entryEq⟩ := List.mem_map.mp prefixMember
  have addrEq : addr = child.2 :: entry.1 := (congrArg Prod.fst entryEq).symm
  have valueEq : value = entry.2 := (congrArg Prod.snd entryEq).symm
  refine ⟨child, childMember, entry.1, addrEq, ?_⟩
  obtain ⟨sourceLayer, sourceLayerMember, layerEntryMember⟩ :=
    mem_of_mem_getD (layers := child.1) (depth := depth) (entry := entry) sourceEntryMember
  exact ⟨sourceLayer, sourceLayerMember, by simpa [valueEq] using layerEntryMember⟩

/-! ## Terminal assembly keeps exactly the root observation -/

/-- The assembled evidence is exactly the root evidence followed by the addressed child merge. -/
theorem assembleCanonicalRule3Key_observations_cons
    (root : CanonicalBranchKey) (rootObservation : Option CanonicalRule3Observation)
    (sorted : List CanonicalRule3Key) :
    (assembleCanonicalRule3Key root rootObservation sorted).observations =
      rule3ObservationRoot rootObservation ++
        mergeCanonicalRule3ObservationChildren sorted :=
  rfl

/-- With no children, the assembled evidence is precisely the addressed root observation. -/
theorem assembleCanonicalRule3Key_observations_nil
    (root : CanonicalBranchKey) (rootObservation : Option CanonicalRule3Observation) :
    (assembleCanonicalRule3Key root rootObservation []).observations =
      rule3ObservationRoot rootObservation := by
  rw [assembleCanonicalRule3Key_observations_cons]
  simp [mergeCanonicalRule3ObservationChildren, mergeObservationObserved]

/-- Terminal assembly: any stored observation is the root observation returned by the observer at
the root node itself. -/
theorem terminal_observation_source
    {children : CanonicalBranchNode → List CanonicalBranchNode}
    {observe : CanonicalBranchNode → Option (Option CanonicalRule3Observation)}
    {node : CanonicalBranchNode} {rootObservation : Option CanonicalRule3Observation}
    {root : CanonicalBranchKey}
    {addr : List ℕ} {value : CanonicalRule3Observation}
    (observed : observe node = some rootObservation)
    (mem : ObservationEntryMem
      (assembleCanonicalRule3Key root rootObservation []).observations addr value) :
    ∃ source : CanonicalBranchNode,
      SourceReachable children node source ∧ observe source = some (some value) := by
  have rootObsEq : rootObservation = some value :=
    observationEntryMem_rule3ObservationRoot (by
      simpa only [assembleCanonicalRule3Key_observations_nil] using mem)
  exact ⟨node, SourceReachable.refl node, by rw [observed, rootObsEq]⟩

/-! ## Source binding for every successful build -/

/-- **Source-binding theorem for the recursive Rule-3 builder.**

Every addressed observation retained by a successfully compiled key was returned by the supplied
observer at some source node reachable from the compiled root through the supplied child
enumerator.  The returned value is the stored value itself, so unit, near/far endpoints, incoming
entry and geometry are not reconstructed, renumbered or flattened. -/
theorem buildCanonicalRule3Key?_observation_source
    {mol : RawMolecule}
    {children : CanonicalBranchNode → List CanonicalBranchNode}
    {observe : CanonicalBranchNode → Option (Option CanonicalRule3Observation)} :
    ∀ (fuel : ℕ) (node : CanonicalBranchNode) (key : CanonicalRule3Key),
      buildCanonicalRule3Key? mol children observe fuel node = some key →
      ∀ {addr : List ℕ} {value : CanonicalRule3Observation},
        ObservationEntryMem key.observations addr value →
        ∃ source : CanonicalBranchNode,
          SourceReachable children node source ∧ observe source = some (some value) := by
  intro fuel
  induction fuel with
  | zero =>
      intro node key computed addr value mem
      unfold buildCanonicalRule3Key? at computed
      cases observed : observe node with
      | none =>
          rw [observed] at computed
          dsimp at computed
          cases computed
      | some rootObservation =>
          rw [observed] at computed
          dsimp at computed
          cases childNodes : children node with
          | cons child rest =>
              rw [childNodes] at computed
              dsimp at computed
              cases computed
          | nil =>
              rw [childNodes] at computed
              dsimp at computed
              cases rootComputed : mol.canonicalRootKeyAuthoritative? node true with
              | none =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
              | some root =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
                  exact terminal_observation_source observed mem
  | succ fuel inductionHypothesis =>
      intro node key computed addr value mem
      unfold buildCanonicalRule3Key? at computed
      cases observed : observe node with
      | none =>
          rw [observed] at computed
          dsimp at computed
          cases computed
      | some rootObservation =>
          rw [observed] at computed
          dsimp at computed
          cases childNodes : children node with
          | nil =>
              rw [childNodes] at computed
              dsimp at computed
              cases rootComputed : mol.canonicalRootKeyAuthoritative? node true with
              | none =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
              | some root =>
                  rw [rootComputed] at computed
                  dsimp at computed
                  cases computed
                  exact terminal_observation_source observed mem
          | cons child rest =>
              rw [childNodes] at computed
              dsimp at computed
              cases childKeysComputed : compileRule3Children
                  (fun childNode =>
                    buildCanonicalRule3Key? mol children observe fuel childNode)
                  (child :: rest) with
              | none =>
                  rw [childKeysComputed] at computed
                  dsimp at computed
                  cases computed
              | some childKeys =>
                  rw [childKeysComputed] at computed
                  dsimp at computed
                  cases rootComputed : mol.canonicalRootKeyAuthoritative? node true with
                  | none =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                  | some root =>
                      rw [rootComputed] at computed
                      dsimp at computed
                      cases computed
                      have splitMem : ObservationEntryMem
                          (rule3ObservationRoot rootObservation ++
                            mergeCanonicalRule3ObservationChildren
                              (sortCanonicalRule3Keys childKeys)) addr value := by
                        simpa only [assembleCanonicalRule3Key_observations_cons] using mem
                      rcases observationEntryMem_append.mp splitMem with
                        rootMem | mergedMem
                      · have rootObsEq : rootObservation = some value :=
                          observationEntryMem_rule3ObservationRoot rootMem
                        exact ⟨node, SourceReachable.refl node,
                          by rw [observed, rootObsEq]⟩
                      · have mergedMem' : ObservationEntryMem
                            (mergeObservationObserved
                              ((sortCanonicalRule3Keys childKeys).map
                                (fun childKey => childKey.observations))) addr value := by
                          simpa only [mergeCanonicalRule3ObservationChildren_eq_observed]
                            using mergedMem
                        obtain ⟨storedChild, storedMember, restAddr, _, entryMem⟩ :=
                          observationEntryMem_mergeObservationObserved mergedMem'
                        rw [List.zipIdx_map] at storedMember
                        obtain ⟨zippedKey, zippedMember, pairEq⟩ :=
                          List.mem_map.mp storedMember
                        obtain ⟨keyAtSlot, slotIndex⟩ := zippedKey
                        have pairEq' : (keyAtSlot.observations, slotIndex) = storedChild := by
                          simpa only [Prod.map] using pairEq
                        have keyObsEq : keyAtSlot.observations = storedChild.1 :=
                          congrArg Prod.fst pairEq'
                        have sortedMember : keyAtSlot ∈ sortCanonicalRule3Keys childKeys :=
                          List.fst_mem_of_mem_zipIdx zippedMember
                        have childKeyMember : keyAtSlot ∈ childKeys :=
                          (sortCanonicalRule3Keys_perm childKeys).mem_iff.mp sortedMember
                        obtain ⟨sourceChild, sourceChildMember, sourceChildComputed⟩ :=
                          compileRule3Children_member childKeysComputed childKeyMember
                        have storedEntryMem :
                            ObservationEntryMem keyAtSlot.observations restAddr value := by
                          rw [keyObsEq]
                          exact entryMem
                        obtain ⟨source, reachable, observedSource⟩ :=
                          inductionHypothesis sourceChild keyAtSlot sourceChildComputed
                            storedEntryMem
                        exact ⟨source,
                          SourceReachable.step (by simpa [childNodes] using sourceChildMember)
                            reachable,
                          observedSource⟩

/-! ## Priority transport under alignment -/

/-- Under `Rule3Aligned`, the compared Rule-3 priority entry at an address is exactly the stored
observation's priority at the same address.  Sorting transports evidence; it never invents a
numeric priority for an observation that was not stored. -/
theorem observationEntryMem_priority_of_aligned
    {key : CanonicalRule3Key} (aligned : key.Rule3Aligned)
    {addr : List ℕ} {value : CanonicalRule3Observation}
    (mem : ObservationEntryMem key.observations addr value) :
    ∃ layer, layer ∈ key.rule3 ∧ (addr, value.priority) ∈ layer := by
  obtain ⟨obsLayer, obsLayerMember, entryMember⟩ := mem
  have mappedMember : mapObservationPriorityLayer obsLayer ∈
      mapObservationPriorityLayers key.observations :=
    List.mem_map_of_mem (f := mapObservationPriorityLayer) obsLayerMember
  have entryMapped : (addr, value.priority) ∈ mapObservationPriorityLayer obsLayer :=
    List.mem_map_of_mem (f := fun entry => (entry.1, entry.2.priority)) entryMember
  unfold CanonicalRule3Key.Rule3Aligned at aligned
  rw [aligned] at mappedMember
  exact ⟨mapObservationPriorityLayer obsLayer, mappedMember, entryMapped⟩

/-- Combined form: every stored addressed observation of a successful build is both source-bound
and transported to exactly its own priority entry. -/
theorem buildCanonicalRule3Key?_observation_source_and_priority
    {mol : RawMolecule}
    {children : CanonicalBranchNode → List CanonicalBranchNode}
    {observe : CanonicalBranchNode → Option (Option CanonicalRule3Observation)}
    {fuel : ℕ} {node : CanonicalBranchNode} {key : CanonicalRule3Key}
    (computed : buildCanonicalRule3Key? mol children observe fuel node = some key)
    {addr : List ℕ} {value : CanonicalRule3Observation}
    (mem : ObservationEntryMem key.observations addr value) :
    (∃ source : CanonicalBranchNode,
        SourceReachable children node source ∧ observe source = some (some value)) ∧
      ∃ layer, layer ∈ key.rule3 ∧ (addr, value.priority) ∈ layer := by
  refine ⟨buildCanonicalRule3Key?_observation_source fuel node key computed mem, ?_⟩
  exact observationEntryMem_priority_of_aligned
    (buildCanonicalRule3Key?_rule3Aligned mol children observe fuel node key computed) mem

/- Kernel trust checks for every theorem in this module. -/
assert_kernel_only observationEntryMem_append
assert_kernel_only observationEntryMem_rule3ObservationRoot
assert_kernel_only mem_of_mem_getD
assert_kernel_only observationEntryMem_mergeObservationObserved
assert_kernel_only assembleCanonicalRule3Key_observations_cons
assert_kernel_only assembleCanonicalRule3Key_observations_nil
assert_kernel_only terminal_observation_source
assert_kernel_only buildCanonicalRule3Key?_observation_source
assert_kernel_only observationEntryMem_priority_of_aligned
assert_kernel_only buildCanonicalRule3Key?_observation_source_and_priority

end RawMolecule
end OneCenter
end TetraStereo
