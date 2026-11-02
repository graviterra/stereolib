import TetraStereo.OneCenter.LocalizedOccurrenceExecutableChildSlots
import TetraStereo.OneCenter.AuthoritativeLocalizedRuleMajorAnalysis

set_option autoImplicit false

/-!
# Universal occurrence-expansion depth for the localized carrier

`LocalizedOccurrenceCarrier` enumerates proof-relevant occurrences with a depth grading
`address.length + remaining = fuel + 1`.  A priori, picking `fuel` too small truncates a rooted
official ligand expansion: an occurrence whose provenance subtree still has executable children
would be stored with `remaining = 0`, silently discarding the independent semantic occurrences
below it.

This module removes that failure mode universally.  It reuses the already-proved simple-path /
visited-set frontier bound (`MoleculeGraph.officialCIPFrontier_rootFromEdge_eq_nil_card_add_one`,
via `executableOfficialExpansionCompleteWithin_default`) to show that, at the graph-derived bound
`input.certified.input.molecule.atomCount + 1`, the center-rooted carrier covers *every* unbounded
descendant of every canonical ligand root — including ring and multiple-bond duplicate leaves —
with its full remaining depth.  No per-molecule evidence is assumed; the only hypothesis is the
`CertifiedLocalizedCIPInput` structure and the already admitted completeness theorem.

The bridge is the unbounded reachability relation `UnboundedOfficialSubtree`, which is independent
of the fuel parameter.  Three transfer lemmas connect it to the executable occurrence enumeration:

* `mem_localizedOccurrenceSubtree_of_unbounded`: an unbounded descendant at relative address
  `address` lies in the bounded subtree once `address.length ≤ fuel`, with `remaining` exactly
  `fuel - address.length`;
* `unboundedOfficialSubtree_address_length_le_of_complete`: completeness within `fuel` bounds the
  address length of every unbounded descendant;
* `unboundedOfficialSubtree_children_nil_of_complete_at_depth`: at the completeness frontier the
  stored `remaining = 0` frames are genuinely terminal, so no semantic occurrence is truncated.
-/

namespace TetraStereo.OneCenter

namespace CertifiedLocalizedCIPInput

/-- Unbounded reachability in the executable official subtree.  `UnboundedOfficialSubtree input
node address descendant` says that `descendant` is obtained from `node` by repeatedly following
enumerated executable children, with `address` the concatenation of the sibling slots taken along
the path.  Unlike `localizedOccurrenceSubtree`, it carries no fuel and no `remaining` counter, so
it describes the full graph-derived expansion rather than any truncated prefix. -/
inductive UnboundedOfficialSubtree (input : CertifiedLocalizedCIPInput) :
    OfficialCIPNode input.Atom → List Nat → OfficialCIPNode input.Atom → Prop where
  | refl (node : OfficialCIPNode input.Atom) :
      UnboundedOfficialSubtree input node [] node
  | step {node child : OfficialCIPNode input.Atom} {inner : List Nat}
      {descendant : OfficialCIPNode input.Atom} {slot : Nat}
      (childAtSlot : (child, slot) ∈ (input.executableOfficialCIPChildren node).zipIdx)
      (rest : UnboundedOfficialSubtree input child inner descendant) :
      UnboundedOfficialSubtree input node (slot :: inner) descendant

/-- Any unbounded descendant below a subtree root is present in the bounded executable occurrence
subtree once the bound covers its address depth.  Its stored remaining depth is exactly the fuel
left after the address has been consumed; this is the fuel-safe half of the universal-depth bridge. -/
theorem mem_localizedOccurrenceSubtree_of_unbounded
    (input : CertifiedLocalizedCIPInput) {root : input.Atom} (fuel : Nat)
    {path : List Nat} {node : OfficialCIPNode input.Atom} :
    ∀ {address : List Nat} {descendant : OfficialCIPNode input.Atom},
      input.UnboundedOfficialSubtree node address descendant →
      address.length ≤ fuel →
      { root := root, address := path ++ address, node := descendant,
        remaining := fuel - address.length } ∈
        input.localizedOccurrenceSubtree root fuel path node := by
  induction fuel generalizing path node with
  | zero =>
      intro address descendant reachable enough
      cases reachable with
      | refl node => simp [localizedOccurrenceSubtree]
      | @step node child inner descendant slot childAtSlot rest =>
          have impossible : inner.length + 1 ≤ 0 := by
            simp only [List.length_cons] at enough
            omega
          omega
  | succ fuel ih =>
      intro address descendant reachable enough
      cases reachable with
      | refl node => simp [localizedOccurrenceSubtree]
      | @step node child inner descendant slot childAtSlot rest =>
          rw [localizedOccurrenceSubtree, List.mem_cons]
          apply Or.inr
          rw [List.mem_flatMap]
          refine ⟨(child, slot), childAtSlot, ?_⟩
          have enough' : inner.length ≤ fuel := by
            have bounded := enough
            simp only [List.length_cons] at bounded
            omega
          have ih' := ih (path := path ++ [slot]) (node := child) rest enough'
          have hAddress : path ++ (slot :: inner) = (path ++ [slot]) ++ inner := by
            simp
          have hRemaining : Nat.succ fuel - (slot :: inner).length = fuel - inner.length := by
            simp only [List.length_cons]
            omega
          rw [hAddress, hRemaining]
          exact ih'

/-- Completeness within `fuel` propagates down an unbounded path, leaving exactly the fuel that
was not yet consumed by the address. -/
theorem unboundedOfficialSubtree_complete_of_complete
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    {node : OfficialCIPNode input.Atom}
    (complete : MoleculeGraph.OfficialExpansionCompleteWithin
      input.executableOfficialCIPChildren fuel node) :
    ∀ {address : List Nat} {descendant : OfficialCIPNode input.Atom},
      input.UnboundedOfficialSubtree node address descendant →
      MoleculeGraph.OfficialExpansionCompleteWithin input.executableOfficialCIPChildren
        (fuel - address.length) descendant := by
  revert complete
  revert node
  induction fuel with
  | zero =>
      intro node complete address descendant reachable
      cases reachable with
      | refl node => simpa [MoleculeGraph.OfficialExpansionCompleteWithin] using complete
      | @step node child inner descendant slot childAtSlot rest =>
          have empty : input.executableOfficialCIPChildren node = [] := by
            simpa [MoleculeGraph.OfficialExpansionCompleteWithin] using complete
          have childMem := List.fst_mem_of_mem_zipIdx childAtSlot
          simp [empty] at childMem
  | succ fuel ih =>
      intro node complete address descendant reachable
      cases reachable with
      | refl node => simpa [MoleculeGraph.OfficialExpansionCompleteWithin] using complete
      | @step node child inner descendant slot childAtSlot rest =>
          have childComplete : MoleculeGraph.OfficialExpansionCompleteWithin
              input.executableOfficialCIPChildren fuel child :=
            complete child (List.fst_mem_of_mem_zipIdx childAtSlot)
          have restComplete := ih (node := child) childComplete rest
          have hRemaining : Nat.succ fuel - (slot :: inner).length = fuel - inner.length := by
            simp only [List.length_cons]
            omega
          rw [hRemaining]
          exact restComplete

/-- Completeness within `fuel` is a bound on the address depth of every unbounded descendant. -/
theorem unboundedOfficialSubtree_address_length_le_of_complete
    (input : CertifiedLocalizedCIPInput) (fuel : Nat)
    {node : OfficialCIPNode input.Atom}
    (complete : MoleculeGraph.OfficialExpansionCompleteWithin
      input.executableOfficialCIPChildren fuel node) :
    ∀ {address : List Nat} {descendant : OfficialCIPNode input.Atom},
      input.UnboundedOfficialSubtree node address descendant →
      address.length ≤ fuel := by
  revert complete
  revert node
  induction fuel with
  | zero =>
      intro node complete address descendant reachable
      cases reachable with
      | refl node => simp
      | @step node child inner descendant slot childAtSlot rest =>
          have empty : input.executableOfficialCIPChildren node = [] := by
            simpa [MoleculeGraph.OfficialExpansionCompleteWithin] using complete
          have childMem := List.fst_mem_of_mem_zipIdx childAtSlot
          simp [empty] at childMem
  | succ fuel ih =>
      intro node complete address descendant reachable
      cases reachable with
      | refl node => simp
      | @step node child inner descendant slot childAtSlot rest =>
          have childComplete : MoleculeGraph.OfficialExpansionCompleteWithin
              input.executableOfficialCIPChildren fuel child :=
            complete child (List.fst_mem_of_mem_zipIdx childAtSlot)
          have innerBound : inner.length ≤ fuel := ih (node := child) childComplete rest
          simp only [List.length_cons]
          omega

/-- At the completeness frontier (address depth exactly `fuel`) a descendant has no executable
children.  Consequently a `remaining = 0` frame generated at the universal depth is a genuine
terminal leaf, and fuel truncation loses no independent semantic occurrence. -/
theorem unboundedOfficialSubtree_children_nil_of_complete_at_depth
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    {node : OfficialCIPNode input.Atom}
    (complete : MoleculeGraph.OfficialExpansionCompleteWithin
      input.executableOfficialCIPChildren fuel node)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree node address descendant)
    (atDepth : address.length = fuel) :
    input.executableOfficialCIPChildren descendant = [] := by
  have descendantComplete := input.unboundedOfficialSubtree_complete_of_complete fuel complete reachable
  rw [atDepth] at descendantComplete
  simpa [MoleculeGraph.OfficialExpansionCompleteWithin] using descendantComplete

/-! ## Canonical ligand-root coordinates -/

/-- The official node at which one canonical ligand expansion is rooted.  This is the zero-copy
real child of the center root, matching the node actually stored by the occurrence carrier. -/
def localizedLigandRootNode (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) : OfficialCIPNode input.Atom :=
  (OfficialCIPNode.root center.1).extend (input.canonicalLigandAtom center index) 0

/-- The canonical ligand root is a real atom (the zero copy of a non-parent graph edge). -/
theorem localizedLigandRootNode_provenance (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    (input.localizedLigandRootNode center index).provenance =
      OfficialCIPNodeProvenance.realAtom := by
  unfold localizedLigandRootNode
  have different := input.canonicalLigandAtom_ne_center center index
  have notIn : input.canonicalLigandAtom center index ∉ [center.1] := by
    intro present
    exact different (List.mem_singleton.mp present)
  simp [OfficialCIPNode.extend, OfficialCIPNode.childProvenance, OfficialCIPNode.root, notIn]

/-- The canonical ligand root is an executable child of the center root. -/
theorem localizedLigandRootNode_mem (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    input.localizedLigandRootNode center index ∈
      input.executableOfficialCIPChildren (OfficialCIPNode.root center.1) := by
  unfold localizedLigandRootNode
  exact input.extend_zero_mem_executableOfficialCIPChildren_of_real
    (OfficialCIPNode.root center.1) center.1 (input.canonicalLigandAtom center index)
    rfl rfl (input.canonicalLigandAtom_adj center index)
    (by simp [OfficialCIPNode.root, OfficialCIPNode.parent?])

/-- The zero-copy center-root extension coincides with the `rootFromEdge` node used by the
rule-major completeness theorem. -/
theorem localizedLigandRootNode_eq_rootFromEdge (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    input.localizedLigandRootNode center index =
      OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index) := by
  unfold localizedLigandRootNode
  have different := input.canonicalLigandAtom_ne_center center index
  have notIn : input.canonicalLigandAtom center index ∉ [center.1] := by
    intro present
    exact different (List.mem_singleton.mp present)
  simp [OfficialCIPNode.rootFromEdge, OfficialCIPNode.root, OfficialCIPNode.extend,
    OfficialCIPNode.childProvenance, notIn]

/-- Executable (leftmost) sibling slot of the canonical ligand root inside the center-root
child enumeration.  No `Classical.choose` is needed: the slot is computed by `List.idxOf`. -/
def localizedLigandRootSlot (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) : Nat :=
  List.idxOf (input.localizedLigandRootNode center index)
    (input.executableOfficialCIPChildren (OfficialCIPNode.root center.1))

/-- The selected ligand-root slot is backed by the executable child enumeration. -/
theorem localizedLigandRootSlot_mem (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    (input.localizedLigandRootNode center index, input.localizedLigandRootSlot center index) ∈
      (input.executableOfficialCIPChildren (OfficialCIPNode.root center.1)).zipIdx := by
  unfold localizedLigandRootSlot
  exact input.executableOfficialCIPChild_idxOf_mem
    (OfficialCIPNode.root center.1)
    (input.localizedLigandRootNode center index)
    (input.localizedLigandRootNode_mem center index)

/-- The selected ligand-root slot is strictly below the executable child-list length. -/
theorem localizedLigandRootSlot_lt (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) :
    input.localizedLigandRootSlot center index <
      (input.executableOfficialCIPChildren (OfficialCIPNode.root center.1)).length := by
  unfold localizedLigandRootSlot
  exact input.executableOfficialCIPChild_idxOf_lt
    (OfficialCIPNode.root center.1)
    (input.localizedLigandRootNode center index)
    (input.localizedLigandRootNode_mem center index)

/-! ## The universal depth -/

/-- At the graph-derived carrier bound `atomCount + 1`, the center-rooted occurrence subtree
covers every unbounded descendant of every canonical ligand root, with full remaining depth.
The only completeness input is the already-proved simple-path / visited-set expansion bound. -/
theorem localizedOccurrenceUniversalDepth_covers_ligand
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree
      (OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index))
      address descendant) :
    { root := center.1
      address := [input.localizedLigandRootSlot center index] ++ address
      node := descendant
      remaining := input.certified.input.molecule.atomCount + 1 - address.length } ∈
      input.localizedOccurrencesAtCenter
        (input.certified.input.molecule.atomCount + 1) center := by
  have complete : MoleculeGraph.OfficialExpansionCompleteWithin
      input.executableOfficialCIPChildren
      (input.certified.input.molecule.atomCount + 1)
      (OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index)) :=
    input.executableOfficialExpansionCompleteWithin_default center index
  have addressBound : address.length ≤ input.certified.input.molecule.atomCount + 1 :=
    input.unboundedOfficialSubtree_address_length_le_of_complete
      (input.certified.input.molecule.atomCount + 1) complete reachable
  have ligandReachable : input.UnboundedOfficialSubtree
      (input.localizedLigandRootNode center index) address descendant := by
    simpa [← input.localizedLigandRootNode_eq_rootFromEdge center index] using reachable
  have rootReachable : UnboundedOfficialSubtree input
      (OfficialCIPNode.root center.1)
      (input.localizedLigandRootSlot center index :: address) descendant :=
    UnboundedOfficialSubtree.step
      (input.localizedLigandRootSlot_mem center index) ligandReachable
  have enough : (input.localizedLigandRootSlot center index :: address).length ≤
      input.certified.input.molecule.atomCount + 1 + 1 := by
    simp only [List.length_cons]
    omega
  have covered := input.mem_localizedOccurrenceSubtree_of_unbounded
    (root := center.1) (fuel := input.certified.input.molecule.atomCount + 1 + 1)
    (path := []) rootReachable enough
  have hRemaining : input.certified.input.molecule.atomCount + 1 + 1 -
      (input.localizedLigandRootSlot center index :: address).length =
      input.certified.input.molecule.atomCount + 1 - address.length := by
    simp only [List.length_cons]
    omega
  simpa [localizedOccurrencesAtCenter, hRemaining] using covered

/-- Molecule-wide carrier form of the universal-depth coverage: the deduplicated
`localizedOccurrences` enumeration at `atomCount + 1` also contains the covered ligand frame. -/
theorem localizedOccurrenceUniversalDepth_covers_ligand_moleculeWide
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree
      (OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index))
      address descendant) :
    { root := center.1
      address := [input.localizedLigandRootSlot center index] ++ address
      node := descendant
      remaining := input.certified.input.molecule.atomCount + 1 - address.length } ∈
      input.localizedOccurrences (input.certified.input.molecule.atomCount + 1) := by
  have covered := input.localizedOccurrenceUniversalDepth_covers_ligand center index reachable
  unfold localizedOccurrences
  rw [List.mem_dedup, List.mem_flatMap]
  refine ⟨center.1, by simp, ?_⟩
  simpa [localizedOccurrencesAtAtom, localizedOccurrencesAtCenter] using covered

/-- At the universal depth, an unbounded descendant that has already consumed the full bound has
no executable children.  The carrier's `remaining = 0` frontier is therefore terminal, so
address-fuel truncation loses no independent semantic occurrence. -/
theorem localizedOccurrenceUniversalDepth_frontier_terminal
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    {address : List Nat} {descendant : OfficialCIPNode input.Atom}
    (reachable : input.UnboundedOfficialSubtree
      (OfficialCIPNode.rootFromEdge center.1 (input.canonicalLigandAtom center index))
      address descendant)
    (atDepth : address.length = input.certified.input.molecule.atomCount + 1) :
    input.executableOfficialCIPChildren descendant = [] := by
  have complete := input.executableOfficialExpansionCompleteWithin_default center index
  exact input.unboundedOfficialSubtree_children_nil_of_complete_at_depth
    complete reachable atDepth

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
