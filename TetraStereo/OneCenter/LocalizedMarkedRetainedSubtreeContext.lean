import TetraStereo.OneCenter.LocalizedRetainedContextObservationReadback
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Subtree observations in the original retained context

A local subtree node is embedded at `stem ++ localAddress` in the original arm. Its
constitutional observation and molecular reading are pulled back from that independent graph,
with the original detected unit unchanged. The ancestor-path theorem below records the exact
stem concatenation; the subtree root is included once, in the local ancestor path.

The actual readback theorems use a realized original arm and derive the correspondence. They do
not retarget the molecular reader, assume its desired readings, or require acyclicity. This file
does not yet construct the subtree's complete reference selection or compound comparison.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeContext

open CertifiedLocalizedCIPInput DeclarativeCIP LocalizedCumulativeDecoratedTree
open Rule4aTableBridge

noncomputable section

/-- Ancestor labels strictly before the selected subtree root. -/
def prefixLabels {V : Type} : OfficialCIPSourceTree V → List Nat → List (Option V)
  | _, [] => []
  | .node source children, slot :: rest =>
      source.current? :: match children[slot]? with
        | none => []
        | some child => prefixLabels child rest

/-- Successful subtree lookup splits the original ancestor path into the strict stem and
the local path, including its own root. -/
theorem pathLabels_append {V : Type} [DecidableEq V]
    (stem : List Nat) (tree subtree : OfficialCIPSourceTree V)
    (lookup : tree.subtreeAt? stem = some subtree) (suffix : List Nat) :
    MolecularEvidenceTree.pathLabels tree (stem ++ suffix) =
      prefixLabels tree stem ++ MolecularEvidenceTree.pathLabels subtree suffix := by
  induction stem generalizing tree with
  | nil =>
      have same : tree = subtree := Option.some.inj lookup
      subst tree
      rfl
  | cons slot rest ih =>
      cases tree with
      | node source children =>
          obtain ⟨child, childLookup, tailLookup⟩ :=
            MolecularEvidenceTree.subtreeAt?_cons_child lookup
          rw [List.cons_append,
            MolecularEvidenceTree.pathLabels_cons source children slot (rest ++ suffix)
              child childLookup,
            ih child tailLookup]
          simp only [prefixLabels, childLookup, List.cons_append]

variable {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}

theorem exists_local_subtree (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (node : (ruleMajorTreeGraph tree).Node) :
    ∃ actual, subtreeAt? tree node.1 = some actual := by
  obtain ⟨erased, lookup⟩ :=
    (toOfficialSourceTree tree).exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
      node.1 node.2
  rw [MolecularEvidenceTree.toOfficialSourceTree_subtreeAt?_eq, Option.map_eq_some_iff] at lookup
  obtain ⟨actual, found, _⟩ := lookup
  exact ⟨actual, found⟩

theorem address_mem_of_lookup (tree actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (address : List Nat) (lookup : subtreeAt? tree address = some actual) :
    address ∈ (toOfficialSourceTree tree).hierarchyAddresses := by
  have erased : (toOfficialSourceTree tree).subtreeAt? address =
      some (toOfficialSourceTree actual) := by
    rw [MolecularEvidenceTree.toOfficialSourceTree_subtreeAt?_eq, lookup]
    rfl
  exact (toOfficialSourceTree tree).mem_hierarchyAddresses_of_occurrence _
    (OfficialCIPSourceTree.mem_occurrences_of_subtreeAt?_eq_some address _ _ erased)

variable (tree subtree : LocalizedCumulativeDecoratedTree input carrierFuel)
  (stem : List Nat) (lookup : subtreeAt? tree stem = some subtree)

/-- Actual address embedding; its membership is constructed from lookup composition. -/
def embed (node : (ruleMajorTreeGraph subtree).Node) : (ruleMajorTreeGraph tree).Node :=
  ⟨stem ++ node.1, by
    obtain ⟨actual, localLookup⟩ := exists_local_subtree subtree node
    apply address_mem_of_lookup tree actual
    rw [subtreeAt?_append, lookup]
    exact localLookup⟩

theorem embed_lookup (node : (ruleMajorTreeGraph subtree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (localLookup : subtreeAt? subtree node.1 = some actual) :
    subtreeAt? tree (embed tree subtree stem lookup node).1 = some actual := by
  change subtreeAt? tree (stem ++ node.1) = some actual
  rw [subtreeAt?_append, lookup]
  exact localLookup

theorem embed_injective : Function.Injective (embed tree subtree stem lookup) := by
  intro left right same
  apply Subtype.ext
  exact List.append_cancel_left (congrArg Subtype.val same)

/-- Prefix-aware atom steps are derived from the original graph's ancestor path. `mapM id`
preserves failure if any atom label is missing; no default atom is inserted. -/
theorem ancestorAtoms_embed (node : (ruleMajorTreeGraph subtree).Node) :
    ancestorAtoms (ruleMajorTreeGraph tree) (embed tree subtree stem lookup node) =
      (prefixLabels (toOfficialSourceTree tree) stem).mapM id >>= fun before =>
        (ancestorAtoms (ruleMajorTreeGraph subtree) node).map (before ++ ·) := by
  have erased : (toOfficialSourceTree tree).subtreeAt? stem =
      some (toOfficialSourceTree subtree) := by
    rw [MolecularEvidenceTree.toOfficialSourceTree_subtreeAt?_eq, lookup]
    rfl
  change ancestorAtoms (toOfficialSourceTree tree).toDeclarativeDigraph _ =
    (prefixLabels (toOfficialSourceTree tree) stem).mapM id >>= fun before =>
      (ancestorAtoms (toOfficialSourceTree subtree).toDeclarativeDigraph node).map (before ++ ·)
  simp only [ancestorAtoms, MolecularEvidenceTree.ancestorPath_toDeclarativeDigraph,
    Option.bind_some]
  change (MolecularEvidenceTree.pathLabels (toOfficialSourceTree tree)
      (stem ++ node.1)).mapM id = _
  rw [pathLabels_append stem _ _ erased, List.mapM_append]
  cases (prefixLabels (toOfficialSourceTree tree) stem).mapM id <;>
    cases (MolecularEvidenceTree.pathLabels (toOfficialSourceTree subtree) node.1).mapM id <;> rfl

/-- Independent constitutional observer restricted to the subtree, retaining the original
descriptor unit and all ancestor steps. -/
def observation (unit : DetectedOccurrence input.moleculeGraph)
    (rule : ConstitutionalRule) (node : (ruleMajorTreeGraph subtree).Node) : ℤ :=
  retainedContextNodeObservation input.moleculeGraph (ruleMajorTreeGraph tree) unit rule
    (embed tree subtree stem lookup node)

/-- Independent molecular reading restricted to the subtree, retaining the original dependency
cutoff. This is not the reading of a newly rooted subtree graph. -/
def reading (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (node : (ruleMajorTreeGraph subtree).Node) : OccurrenceReading :=
  occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree)
    (embed tree subtree stem lookup node)

theorem reading_eq_prefixed
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph)
    (node : (ruleMajorTreeGraph subtree).Node) :
    reading tree subtree stem lookup descriptorMap unit node =
      match ((ruleMajorTreeGraph tree).label (embed tree subtree stem lookup node)).provenance,
        ((prefixLabels (toOfficialSourceTree tree) stem).mapM id >>= fun before =>
          (ancestorAtoms (ruleMajorTreeGraph subtree) node).map (before ++ ·)) with
      | .realAtom, some steps => readContext input.moleculeGraph descriptorMap unit steps
      | _, _ => .unavailable := by
  unfold reading occurrenceReading
  rw [ancestorAtoms_embed tree subtree stem lookup node]
  cases ((ruleMajorTreeGraph tree).label (embed tree subtree stem lookup node)).provenance <;>
    cases ((prefixLabels (toOfficialSourceTree tree) stem).mapM id >>= fun before =>
      (ancestorAtoms (ruleMajorTreeGraph subtree) node).map (before ++ ·)) <;> rfl

variable (singleBonded : input.moleculeGraph.SimpleBonded)
  (target : input.LocalizedRerootCursor carrierFuel)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.occurrence.1 = unit.1)

include singleBonded targetUnit

/-- All constitutional columns at every actual subtree node, with no changed origin. -/
theorem observation_readback
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target)
    (rule : ConstitutionalRule) (node : (ruleMajorTreeGraph subtree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (localLookup : subtreeAt? subtree node.1 = some actual) :
    observation tree subtree stem lookup unit rule node =
      priorityValue rule (armObservation rule actual) := by
  exact input.retainedContextNodeObservation_eq_armObservation singleBonded target unit
    targetUnit tree realizes rootChild rule (embed tree subtree stem lookup node) actual
    (embed_lookup tree subtree stem lookup node actual localLookup)

/-- Actual molecular labels, including unavailable ring leaves, are derived from the original
reader on a realized arm. Neither a desired label nor a new subtree target is assumed. -/
theorem label_readback
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (realizes : LocalizedCumulativeTreeRealizes input
      (input.molecularReader descriptorMap target.occurrence) tree)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren target)
    (node : (ruleMajorTreeGraph subtree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel)
    (localLookup : subtreeAt? subtree node.1 = some actual) :
    actual.label = (reading tree subtree stem lookup descriptorMap unit node).toLocalizedLabel := by
  exact (input.retainedRealizedTree_label_eq_occurrenceReading descriptorMap singleBonded target
    unit targetUnit tree realizes rootChild (embed tree subtree stem lookup node) actual
    (embed_lookup tree subtree stem lookup node actual localLookup)).1

end

end TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeContext

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeContext.pathLabels_append
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeContext.exists_local_subtree
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeContext.address_mem_of_lookup
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeContext.embed
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeContext.embed_lookup
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeContext.embed_injective
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeContext.ancestorAtoms_embed
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeContext.reading_eq_prefixed
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeContext.observation_readback
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedSubtreeContext.label_readback
