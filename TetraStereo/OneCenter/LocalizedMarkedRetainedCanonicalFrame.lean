import TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalMarker
import TetraStereo.OneCenter.LocalizedMarkedRetainedVirtualTarget
import TetraStereo.OneCenter.LocalizedMarkedRetainedPromotedRanking
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The actual promoted frame order is an independent canonical order

`LocalizedMarkedRetainedCanonicalMarker` reduced the actual marker to the independent canonical
marker under one premise: sibling agreement of the actual ordinary order with an independent
linear prior. Here that premise is discharged on every actual ligand arm:

* `deepPrior` assigns every hierarchy node the independent retained complete Rule-5 key of its
  actual stage graph, read in its actual parent's occurrence context with the descriptor map cut
  at the original target's depth (`LocalizedMarkedRetainedVirtualTarget`). The parent windows are
  common to all its children.
* `deepPrior_agreement` proves `SiblingPriorAgreement`, at every parent, branching or not and
  whatever its atom (including three-coordinate nitrogen).
* `refinedKey_eq_canonical` and `partition?_eq_canonical`: at every real detected target of a
  single-bond input, for an arbitrary raw auxiliary state, every reference atom and every layout,
  the actual promoted four-ligand partition is the descending order of
  `(independent retained Rules-1–5 key, independent canonical marker)`.

Thus the second component, formerly "the actual computed marker", is now the independent
`PromotedCanonical.markerKey` of the actual arm hierarchy. Rings, ring-duplicate leaves, empty and
multiple-reference branches and arbitrary depth are included. This is an operational agreement
with an independent construction; it does not make the experimental promotion policy official CIP
semantics.
-/

namespace TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame

open CertifiedLocalizedCIPInput DeclarativeCIP DeclarativeCIP.PromotedCanonical Rule4aTableBridge
open LocalizedCumulativeDecoratedTree LocalizedMarkedRetainedSubtreeContext
open LocalizedMarkedRetainedPromotedKey LocalizedMarkedRetainedCanonicalMarker
open LocalizedMarkedRetainedVirtualTarget LocalizedMarkedRetainedMolecularSelection

noncomputable section
open scoped Classical

theorem le_foldr_max {l : List Nat} {x : Nat} (member : x ∈ l) : x ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at member
  | cons a l ih =>
      rcases List.mem_cons.1 member with rfl | member
      · exact le_max_left _ _
      · exact (ih member).trans (le_max_right _ _)

variable {input : CertifiedLocalizedCIPInput}
  (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
  (t : input.LocalizedCIPOccurrence (retainedCarrierFuel input))

/-! ## Independent deep keys -/

/-- Chosen actual stage families of a child under the virtual parent reader. -/
def childStages (parent child : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (member : child ∈ input.executableLocalizedRerootChildren parent) :
    input.RuleMajorContextStages (retainedCarrierFuel input)
      (virtualReader descriptorMap t parent) child :=
  Classical.choice (input.exists_ruleMajorContextStages_at_actualChild _ _ parent child member)

def childWidth (parent child : input.LocalizedRerootCursor (retainedCarrierFuel input)) : Nat :=
  if member : child ∈ input.executableLocalizedRerootChildren parent then
    (childStages descriptorMap t parent child member).widthBound else 0

def childDepth (parent child : input.LocalizedRerootCursor (retainedCarrierFuel input)) : Nat :=
  if member : child ∈ input.executableLocalizedRerootChildren parent then
    (childStages descriptorMap t parent child member).depthBound else 0

/-- A layout common to all children of one parent. -/
def parentWidth (parent : input.LocalizedRerootCursor (retainedCarrierFuel input)) : Nat :=
  ((input.executableLocalizedRerootChildren parent).map (childWidth descriptorMap t parent)).foldr
    max 0

def parentDepth (parent : input.LocalizedRerootCursor (retainedCarrierFuel input)) : Nat :=
  ((input.executableLocalizedRerootChildren parent).map (childDepth descriptorMap t parent)).foldr
    max 0

theorem childStages_width_le (parent child : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (member : child ∈ input.executableLocalizedRerootChildren parent) :
    (childStages descriptorMap t parent child member).widthBound ≤
      parentWidth descriptorMap t parent := by
  have value : childWidth descriptorMap t parent child =
      (childStages descriptorMap t parent child member).widthBound := by
    simp only [childWidth, dif_pos member]
  rw [← value]
  exact le_foldr_max (List.mem_map_of_mem member)

theorem childStages_depth_le (parent child : input.LocalizedRerootCursor (retainedCarrierFuel input))
    (member : child ∈ input.executableLocalizedRerootChildren parent) :
    (childStages descriptorMap t parent child member).depthBound ≤
      parentDepth descriptorMap t parent := by
  have value : childDepth descriptorMap t parent child =
      (childStages descriptorMap t parent child member).depthBound := by
    simp only [childDepth, dif_pos member]
  rw [← value]
  exact le_foldr_max (List.mem_map_of_mem member)

variable (fallback : CompleteLigandRule5Key)

/-- Independent retained key of a child, read from its detected parent's own unit with the
descriptor map cut at the original target's depth. No runtime comparison is consulted. -/
def deepKey (parent child : input.LocalizedRerootCursor (retainedCarrierFuel input)) :
    CompleteLigandRule5Key :=
  if h : child ∈ input.executableLocalizedRerootChildren parent then
    retainedCompleteLigandRule5KeyAt input.moleculeGraph (cutMap descriptorMap t.1.address.length)
      (parentUnit parent) (ruleMajorTreeGraph (childStages descriptorMap t parent child h).a.tree)
      (parentWidth descriptorMap t parent) (parentDepth descriptorMap t parent)
  else fallback

variable (tree : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input))

/-- The cursor of a node's parent address. -/
def parentSource (node : (ruleMajorTreeGraph tree).Node) :
    input.LocalizedRerootCursor (retainedCarrierFuel input) :=
  ((subtreeAt? tree node.1.dropLast).map LocalizedCumulativeDecoratedTree.source).getD tree.source

/-- The independent prior of every hierarchy node. -/
def deepPrior (node : (ruleMajorTreeGraph tree).Node) : CompleteLigandRule5Key :=
  deepKey descriptorMap t fallback (parentSource tree node) (nodeSource input tree node)

theorem parentSource_of_child {parent node : (ruleMajorTreeGraph tree).Node}
    (edge : (ruleMajorTreeGraph tree).child parent node) :
    parentSource tree node = nodeSource input tree parent := by
  obtain ⟨slot, hslot⟩ := edge
  unfold parentSource nodeSource
  rw [hslot, List.dropLast_concat]

variable {read : input.LocalizedRerootCursor (retainedCarrierFuel input) → Option LocalizedAuxiliaryLabel}
  (realizes : LocalizedCumulativeTreeRealizes input read tree)

include realizes in
theorem child_edge {parent node : (ruleMajorTreeGraph tree).Node}
    (edge : (ruleMajorTreeGraph tree).child parent node) :
    E input (nodeSource input tree parent) (nodeSource input tree node) := by
  obtain ⟨slot, hslot⟩ := edge
  obtain ⟨sub, lookup⟩ := exists_local_subtree tree parent
  obtain ⟨childTree, nodeLookup⟩ := exists_local_subtree tree node
  have slotLookup : sub.children[slot]? = some childTree := by
    have h := nodeLookup
    rw [hslot, subtreeAt?_append_singleton, lookup] at h
    simpa using h
  rw [nodeSource_of_lookup input tree lookup, nodeSource_of_lookup input tree nodeLookup]
  exact mem_executable_of_child (realizes_of_subtree realizes lookup) slotLookup

include realizes in
theorem nodeSource_reach (node : (ruleMajorTreeGraph tree).Node) :
    Relation.ReflTransGen (E input) tree.source (nodeSource input tree node) := by
  induction (ruleMajorTreeGraph tree).reachable node with
  | refl =>
      rw [nodeSource_root]
  | tail _ edge ih => exact ih.tail (child_edge tree realizes edge)

/-- A lawful comparator on a linear order is that order's `compare`. -/
theorem linear_compare_eq {P : Type*} [LinearOrder P] (cmp : P → P → Ordering)
    (hlt : ∀ a b, cmp a b = .lt ↔ a < b) (heq : ∀ a b, cmp a b = .eq ↔ a = b) (a b : P) :
    cmp a b = compare a b := by
  rcases lt_trichotomy a b with less | equal | greater
  · rw [(hlt a b).2 less, compare_lt_iff_lt.2 less]
  · rw [(heq a b).2 equal, compare_eq_iff_eq.2 equal]
  · rw [compare_gt_iff_gt.2 greater]
    cases h : cmp a b
    · exact absurd ((hlt a b).1 h) (lt_asymm greater)
    · exact absurd ((heq a b).1 h) (ne_of_gt greater)
    · rfl

include realizes in
/-- **Sibling agreement is derived.** On every actual arm, the actual ordinary order of every
sibling pair under the original view is the order of the independent deep keys. -/
theorem deepPrior_agreement
    (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren ⟨t, none⟩) :
    SiblingPriorAgreement input t (input.molecularView descriptorMap t) tree
      (deepPrior descriptorMap t fallback tree) := by
  intro parent left right edgeL edgeR leftKey rightKey builtL builtR
  have reach : Relation.ReflTransGen (E input) ⟨t, none⟩ (nodeSource input tree parent) :=
    (Relation.ReflTransGen.single rootChild).trans (nodeSource_reach tree realizes parent)
  have childL := child_edge tree realizes edgeL
  have childR := child_edge tree realizes edgeR
  have priorL : deepPrior descriptorMap t fallback tree left =
      retainedCompleteLigandRule5KeyAt input.moleculeGraph
        (cutMap descriptorMap t.1.address.length) (parentUnit (nodeSource input tree parent))
        (ruleMajorTreeGraph (childStages descriptorMap t _ _ childL).a.tree)
        (parentWidth descriptorMap t (nodeSource input tree parent))
        (parentDepth descriptorMap t (nodeSource input tree parent)) := by
    unfold deepPrior
    rw [parentSource_of_child tree edgeL]
    unfold deepKey
    exact dif_pos childL
  have priorR : deepPrior descriptorMap t fallback tree right =
      retainedCompleteLigandRule5KeyAt input.moleculeGraph
        (cutMap descriptorMap t.1.address.length) (parentUnit (nodeSource input tree parent))
        (ruleMajorTreeGraph (childStages descriptorMap t _ _ childR).a.tree)
        (parentWidth descriptorMap t (nodeSource input tree parent))
        (parentDepth descriptorMap t (nodeSource input tree parent)) := by
    unfold deepPrior
    rw [parentSource_of_child tree edgeR]
    unfold deepKey
    exact dif_pos childR
  rw [priorL, priorR]
  exact (virtual_sibling_compare descriptorMap tetrahedralMap singleBonded t _ _ _ reach
    childL childR _ _
    (childStages_width_le descriptorMap t _ _ childL) (childStages_depth_le descriptorMap t _ _ childL)
    (childStages_width_le descriptorMap t _ _ childR) (childStages_depth_le descriptorMap t _ _ childR)
    builtL builtR).trans
    (linear_compare_eq _ completeLigandRule5Key_compare_lt_iff
      completeLigandRule5Key_compare_eq_iff _ _)

include realizes in
/-- **Actual marker = independent canonical marker with independent deep priors.** -/
theorem marker_eq_deepMarker
    (tetrahedralMap : ∀ unit value, descriptorMap unit = some value → value.IsTetrahedral)
    (singleBonded : input.moleculeGraph.SimpleBonded)
    (rootChild : tree.source ∈ input.executableLocalizedRerootChildren ⟨t, none⟩)
    (reference : input.Atom) (W D fuel : Nat)
    (result : PromotedKey input)
    (built : build? input t (input.molecularView descriptorMap t) reference W D fuel tree.source =
      some result) :
    result.marker = markerKey (ruleMajorTreeGraph tree) (deepPrior descriptorMap t fallback tree)
      (referenceMark input reference tree) W D (ruleMajorTreeGraph tree).root :=
  root_marker_eq_markerKey input t (input.molecularView descriptorMap t) reference W D tree realizes
    _ (deepPrior_agreement descriptorMap t fallback tree realizes tetrahedralMap singleBonded
      rootChild) fuel result built

end

/-! ## The actual promoted frame partition -/

section Frame

open LocalizedMarkedRetainedStateReader LocalizedMarkedRetainedOrdinaryRanking
open LocalizedMarkedRetainedPromotedRanking

noncomputable section

variable (input : CertifiedLocalizedCIPInput)
  (single : input.moleculeGraph.SimpleBonded) (state : OccurrenceAuxState)
  (target : input.LocalizedCIPOccurrence (retainedCarrierFuel input))
  (real : target.1.node.provenance = OfficialCIPNodeProvenance.realAtom)
  (unit : DetectedOccurrence input.moleculeGraph)
  (targetUnit : input.molecularFrameUnit target.1 = unit.1)
  (reference : input.Atom) (W D : Nat) (fallback : CompleteLigandRule5Key)

/-- The actual Rule-4a arm tree of one frame slot. -/
abbrev slotTree (slot : Fin 4) : LocalizedCumulativeDecoratedTree input (retainedCarrierFuel input) :=
  ((frames input single state target real unit targetUnit).stages slot).a.tree

/-- Independent key of one frame slot: retained Rules-1–5 key, then canonical marker. -/
def canonicalKey (slot : Fin 4) : RefinedKey :=
  toLex (rawStateKeys input single state target real unit targetUnit slot,
    markerKey (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit slot))
      (deepPrior (rawStateDescriptorMap input state) target fallback
        (slotTree input single state target real unit targetUnit slot))
      (referenceMark input reference (slotTree input single state target real unit targetUnit slot))
      W D (ruleMajorTreeGraph (slotTree input single state target real unit targetUnit slot)).root)

/-- **The actual promoted sort key of every slot is the independent canonical key.** -/
theorem refinedKey_eq_canonical (slot : Fin 4) :
    refinedKey input single state target real unit targetUnit reference W D slot =
      canonicalKey input single state target real unit targetUnit reference W D fallback slot := by
  have source := ((frames input single state target real unit targetUnit).stages slot).a.sourceEq
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace
    ((frames input single state target real unit targetUnit).stages slot).a.trace
  have rootChild : (slotTree input single state target real unit targetUnit slot).source ∈
      input.executableLocalizedRerootChildren ⟨target, none⟩ := by
    rw [source]
    exact (frames input single state target real unit targetUnit).childAt slot
  have built := compiled_built input single state target real unit targetUnit reference W D slot
  rw [rawStateView_eq_molecularView, ← source] at built
  unfold refinedKey canonicalKey
  rw [marker_eq_deepMarker (rawStateDescriptorMap input state) target fallback _ realizes
    (rawStateDescriptorMap_tetrahedral input state) single rootChild reference W D
    _ _ built]

/-- **The actual promoted four-ligand partition is the descending order of the independent
canonical keys**, with the adjacent decisions of that order. Arbitrary raw state, reference atom
and layout; rings, reference ties and arbitrary branching atoms allowed. -/
theorem partition?_eq_canonical :
    partition? input state target reference W D =
      some (keyOrder (canonicalKey input single state target real unit targetUnit reference W D
          fallback) (List.finRange 4),
        adjacentBy (fun left right => some
          (compare (canonicalKey input single state target real unit targetUnit reference W D
              fallback left)
            (canonicalKey input single state target real unit targetUnit reference W D
              fallback right)))
          (keyOrder (canonicalKey input single state target real unit targetUnit reference W D
            fallback) (List.finRange 4))) := by
  have same : refinedKey input single state target real unit targetUnit reference W D =
      canonicalKey input single state target real unit targetUnit reference W D fallback :=
    funext (refinedKey_eq_canonical input single state target real unit targetUnit reference W D
      fallback)
  rw [partition?_eq input single state target real unit targetUnit reference W D, same]

end

end Frame

end TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame

assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.childStages_width_le
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.parentSource_of_child
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.child_edge
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.nodeSource_reach
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.deepPrior_agreement
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.marker_eq_deepMarker
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.refinedKey_eq_canonical
assert_kernel_only TetraStereo.OneCenter.LocalizedMarkedRetainedCanonicalFrame.partition?_eq_canonical
