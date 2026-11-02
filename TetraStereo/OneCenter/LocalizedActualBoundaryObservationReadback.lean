import TetraStereo.OneCenter.LocalizedRetainedConstitutionalTreeReadback
import TetraStereo.OneCenter.LocalizedActualOutwardRule1bEquivalence
import TetraStereo.OneCenter.LocalizedRetainedCoherentSymmetry
import TetraStereo.OneCenter.DeclarativeCIPFaithfulExpansionBisimulation
import TetraStereo.OneCenter.LocalizedOccurrenceCarrierCoverage
import TetraStereo.OneCenter.LocalizedActualBoundaryPathRealization
import TetraStereo.OneCenter.DeclarativeCIPBoundaryComponentReconstruction
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

/-!
# Actual boundary observation readback

This module is the bridge from an actual complete original-root arm comparison to the residual
path-tree premise consumed by coherent component reconstruction. The accepted constitutional
tree readback proves equality of the source-erased `RetainedObservationTree` from an actual
constitutional key tie.

`actualArmResidualPathTreeEquiv` constructs the stronger `ResidualPathTreeEquiv` with boundary
`[center]` from that tie, on single-bonded inputs with constant formal charge. Every simple
outward path from the left ligand is realized at an actual ranked address of the left source
tree. The same address of the right tree carries an equal label/provenance observation, so it is
the real node of a simple path from the right ligand. Parentage, terminal labels, the center bond
and every ordered ancestor bond are read from ring-duplicate children with indexed Rule-1b
distances (`LocalizedActualBoundaryPathRealization`).

`actualArm_automorphism_of_constitutionalTie` composes it with
`BoundaryComponentReconstruction.root_outward_arm_automorphism`: a molecular automorphism fixing
the center and sending the left ligand to the right one. In
`actualArm_automorphism_witnessed_occurrences` every atom of the left component is reached by a
path whose left and `π`-image right occurrences sit at one common actual address. The
automorphism is not claimed to preserve configuration or parity.

For two actual outward sibling cursors at a real auxiliary target the same construction runs
below the whole root-first target history. Any constitutional tie of successful revised builds,
at any stages, readers and fuels, gives a same-boundary `ResidualPathTreeEquiv` for real siblings
(`nonempty_outwardSiblingResidualPathTreeEquiv`). A real/ring-duplicate tie is excluded by the
sibling Rule-1b values, and two distinct ring-duplicate siblings carry different Rule-1b values.
At a target atom with `ConstitutionallyRigidGraphAt` (unfolded in the statements),
every distinct sibling pair is therefore constitutionally separated
(`outwardSiblings_separated_of_rigidTarget`). The original root is the case of the center's
root-start cursor (`ligandRootSiblingPair`).

The distinction matters on cyclic graphs: duplicate-distance observations identify the exact
ancestor index, and the missing edge information is recovered from that indexed occurrence.
Acyclicity, endpoint consistency, a Hamiltonian path and a preselected path map are not inputs.
-/

namespace TetraStereo.OneCenter
namespace LocalizedActualBoundaryObservationReadback

open CertifiedLocalizedCIPInput
open LocalizedRetainedConstitutionalTreeReadback
open RetainedRingSymmetryReconstruction
open RetainedCoherentSymmetry
open LocalizedActualBoundaryPathRealization
open LocalizedCumulativeDecoratedTree

/-- Actual constitutional comparison equality implies equality of the complete source-erased
retained observations for the chosen actual original-root arms. -/
theorem actualArmObservation_eq_of_constitutionalTie
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (tie : OfficialRuleMajorKey.compare
      (actualOriginalRootArm input center left stage read).key.constitutional
      (actualOriginalRootArm input center right stage read).key.constitutional = Ordering.eq) :
    retainedObservationTree (actualOriginalRootArm input center left stage read) =
      retainedObservationTree (actualOriginalRootArm input center right stage read) :=
  retainedObservationTree_eq_of_actual_tie input center left right stage read tie




theorem actualArmShape_eq_of_constitutionalTie
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (tie : OfficialRuleMajorKey.compare
      (actualOriginalRootArm input center left stage read).key.constitutional
      (actualOriginalRootArm input center right stage read).key.constitutional = Ordering.eq) :
    (actualOriginalRootArm input center left stage read).tree.shape =
      (actualOriginalRootArm input center right stage read).tree.shape := by
  exact shape_eq_of_constitutional_tie
    (actualOriginalRootArm input center left stage read)
    (actualOriginalRootArm input center right stage read) tie

/-- A source-tree address occupied in one actual arm is occupied at the identical address in the
other arm, with the same three constitutional node observations, whenever their actual
constitutional keys tie. This is the reusable local bridge from source-path addresses to the
matched actual tree. -/
theorem actualArm_subtreeAt_address_eq_of_constitutionalTie
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (tie : OfficialRuleMajorKey.compare
      (actualOriginalRootArm input center left stage read).key.constitutional
      (actualOriginalRootArm input center right stage read).key.constitutional = Ordering.eq)
    (address : List Nat)
    (source : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1))
    (lookup : (actualOriginalRootArm input center left stage read).tree.decoratedSubtreeAt?
      address = some source) :
    ∃ target : LocalizedCumulativeDecoratedTree input
        (input.certified.input.molecule.atomCount + 1),
      (actualOriginalRootArm input center right stage read).tree.decoratedSubtreeAt?
        address = some target ∧ source.shape = target.shape := by
  have sameShape := actualArmShape_eq_of_constitutionalTie
    input center left right stage read tie
  have sameAt := map_shape_decoratedSubtreeAt?
    (actualOriginalRootArm input center left stage read).tree
    (actualOriginalRootArm input center right stage read).tree sameShape address
  rw [lookup] at sameAt
  cases htarget : (actualOriginalRootArm input center right stage read).tree.decoratedSubtreeAt?
      address with
  | none => simp [htarget] at sameAt
  | some target =>
      simp only [Option.map_some] at sameAt
      rw [htarget] at sameAt
      exact ⟨target, rfl, Option.some.inj sameAt⟩



/-- Read the matched address back to the actual occurrence sources. In addition to equal Z/mass
columns, their duplicate classifications agree after collapsing the official provenance. This
provides the real-versus-ancestor-duplicate discriminator required when lifting a simple path. -/
theorem actualArm_addressed_occurrence_observations_eq
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (tie : OfficialRuleMajorKey.compare
      (actualOriginalRootArm input center left stage read).key.constitutional
      (actualOriginalRootArm input center right stage read).key.constitutional = Ordering.eq)
    (address : List Nat)
    (source : LocalizedCumulativeDecoratedTree input
      (input.certified.input.molecule.atomCount + 1))
    (sourceLookup : (actualOriginalRootArm input center left stage read).tree.decoratedSubtreeAt?
      address = some source) :
    ∃ target, (actualOriginalRootArm input center right stage read).tree.decoratedSubtreeAt?
        address = some target ∧
      source.shape.atomicNumber = target.shape.atomicNumber ∧
        source.shape.isotopeMass = target.shape.isotopeMass ∧
        collapseProvenance source.source.occurrence.1.node.provenance =
          collapseProvenance target.source.occurrence.1.node.provenance := by
  obtain ⟨target, targetLookup, sameShape⟩ :=
    actualArm_subtreeAt_address_eq_of_constitutionalTie
      input center left right stage read tie address source sourceLookup
  have rbSource := addressedRetainedReadback
    (actualOriginalRootArm input center left stage read) address source sourceLookup
  have rbTarget := addressedRetainedReadback
    (actualOriginalRootArm input center right stage read) address target targetLookup
  refine ⟨target, targetLookup, ?_, ?_, ?_⟩
  · exact congrArg LocalizedCumulativeBranchShape.atomicNumber sameShape
  · exact congrArg LocalizedCumulativeBranchShape.isotopeMass sameShape
  · calc
      collapseProvenance source.source.occurrence.1.node.provenance =
          (ofShape (address.length + 1) source.shape).provenance := rbSource.provenance_eq.symm
      _ = (ofShape (address.length + 1) target.shape).provenance := by rw [sameShape]
      _ = collapseProvenance target.source.occurrence.1.node.provenance := rbTarget.provenance_eq



/-- In a faithful exact expansion, every positively bonded atom absent from the ordered branch
history occurs as a real child. Under single bonding this is the path-extension existence fact;
it uses no acyclicity assumption. -/
theorem exists_real_child_for_fresh_neighbor
    {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (externalParent ligand : Atom)
    (graph : DeclarativeCIP.RootedDigraph Atom)
    (faithful : DeclarativeCIP.RootedDigraph.FaithfulExactExpansion
      molecule externalParent ligand graph)
    (parent : graph.Node) (parentAtom atom : Atom)
    (parentLabel : (graph.label parent).atom? = some parentAtom)
    (parentReal : DeclarativeCIP.RootedDigraph.ProvenanceRealAtom
      (graph.label parent).provenance)
    (adjacent : molecule.Adj parentAtom atom)
    (fresh : ¬ DeclarativeCIP.RootedDigraph.BranchAncestorAtom
      graph externalParent atom parent) :
    ∃ child, graph.child parent child ∧ (graph.label child).atom? = some atom ∧
      DeclarativeCIP.RootedDigraph.ProvenanceRealAtom (graph.label child).provenance := by
  classical
  open DeclarativeCIP.RootedDigraph in
  letI : Fintype graph.Node := graph.nodeFintype
  rcases faithful.1.2 with ⟨_addressing, multiplicities⟩
  have counts := multiplicities parent parentAtom parentLabel parentReal atom
  have hrealCount : ChildAtomProvenanceCount graph parent atom ProvenanceRealAtom = 1 := by
    rw [counts.2.2.2]
    simp [adjacent, fresh]
  have hpositive : 0 < ChildAtomProvenanceCount graph parent atom ProvenanceRealAtom := by
    rw [hrealCount]
    omega
  obtain ⟨⟨child, edge, childLabel, childReal⟩⟩ := Nat.card_pos_iff.mp hpositive
  exact ⟨child, edge, childLabel, childReal⟩



/-- Every immediate executable child covered by a generated source tree occurs at some actual
sibling slot. The slot is the one used by that sorted source tree, not a guessed atom ordering. -/
theorem generated_source_child_has_address
    {Atom : Type*} [DecidableEq Atom]
    (enumerate : OfficialCIPNode Atom → List (OfficialCIPNode Atom))
    (tree : OfficialCIPSourceTree Atom)
    (generated : tree.GeneratedBy enumerate)
    (node : OfficialCIPNode Atom)
    (member : node ∈ enumerate tree.source) :
    ∃ slot child,
      tree.subtreeAt? [slot] = some child ∧ child.source = node := by
  classical
  cases tree with
  | node root children =>
      simp only [OfficialCIPSourceTree.GeneratedBy] at generated
      have hmap : node ∈ children.map OfficialCIPSourceTree.source :=
        generated.1.mem_iff.mpr member
      obtain ⟨child, hchild, hsource⟩ := List.mem_map.mp hmap
      let slot := children.idxOf child
      have hget : children[slot]? = some child := by
        simpa [slot] using List.getElem?_idxOf (l := children) (a := child) hchild
      refine ⟨slot, child, ?_, hsource⟩
      simp [OfficialCIPSourceTree.subtreeAt?, hget]

/-- An executable descendant of a generated source tree is represented by some ranked-tree
address. The address is existential because `GeneratedBy` records sibling order up to permutation;
the theorem does not confuse executable child slots with ranked sibling positions. -/
theorem generated_tree_address_of_unbounded_subtree
    (input : CertifiedLocalizedCIPInput)
    (tree : OfficialCIPSourceTree input.Atom)
    (generated : tree.GeneratedBy input.executableOfficialCIPChildren)
    {start : OfficialCIPNode input.Atom} {execAddress : List Nat}
    {node : OfficialCIPNode input.Atom}
    (rootEq : tree.source = start)
    (reachable : input.UnboundedOfficialSubtree start execAddress node) :
    ∃ address subtree, tree.subtreeAt? address = some subtree ∧ subtree.source = node := by
  induction reachable generalizing tree with
  | refl current =>
      exact ⟨[], tree, rfl, rootEq⟩
  | @step current child inner descendant execSlot childAtSlot rest ih =>
      cases tree with
      | node sourceNode subtrees =>
          have childInEnum : child ∈ input.executableOfficialCIPChildren sourceNode := by
            have h := List.fst_mem_of_mem_zipIdx childAtSlot
            change sourceNode = current at rootEq
            rw [← rootEq] at h
            exact h
          have childInMap : child ∈ subtrees.map OfficialCIPSourceTree.source := by
            exact generated.1.mem_iff.mpr childInEnum
          obtain ⟨childTree, childTreeMem, childTreeSource⟩ :=
            List.mem_map.mp childInMap
          have childSlot : ∃ slot : Nat, subtrees[slot]? = some childTree := by
            exact List.mem_iff_getElem?.mp childTreeMem
          obtain ⟨slot, childSlot⟩ := childSlot
          have childGenerated := OfficialCIPSourceTree.GeneratedBy.of_subtreeAt?
            input.executableOfficialCIPChildren [slot] (.node sourceNode subtrees) childTree generated
            (by simp [OfficialCIPSourceTree.subtreeAt?, childSlot])
          obtain ⟨tailAddress, finalTree, finalLookup, finalSource⟩ :=
            ih childTree childGenerated childTreeSource
          refine ⟨slot :: tailAddress, finalTree, ?_, finalSource⟩
          simp [OfficialCIPSourceTree.subtreeAt?, childSlot, finalLookup]

/-! ## Residual path-tree equivalence from the actual tie -/

/-- Collapsed provenance is injective on graph-generated official provenances. -/
theorem provenance_eq_of_collapse_eq {V : Type*} {first second : OfficialCIPNode V}
    (hfirst : first.GraphGenerated) (hsecond : second.GraphGenerated)
    (h : collapseProvenance first.provenance = collapseProvenance second.provenance) :
    first.provenance = second.provenance := by
  rcases first with ⟨current₁, history₁, provenance₁⟩
  rcases second with ⟨current₂, history₂, provenance₂⟩
  simp only [OfficialCIPNode.GraphGenerated] at hfirst hsecond
  simp only at h ⊢
  cases provenance₁ <;> cases provenance₂ <;> simp_all [collapseProvenance]

/-- The erased source tree of an actual original-root arm is rooted at its ligand below the
center. -/
theorem actualArm_boundaryRooted (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel) :
    BoundaryRootedTree input [center.1] (input.canonicalLigandAtom center index)
      (toOfficialSourceTree (actualOriginalRootArm input center index stage read).tree) where
  generated := (actualOriginalRootArm input center index stage read).generated
  root := by
    rw [(actualOriginalRootArm input center index stage read).root,
      rootFromEdge_eq_boundaryNode]
  nodup := by
    have hne := ne_of_adj input.moleculeGraph (input.canonicalLigandAtom_adj center index)
    simp [hne]

/-- The label/provenance observation of an erased decorated tree is read off its decorated
lookup. -/
theorem observationAt_toOfficialSourceTree (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat} (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (address : List ℕ) :
    observationAt input.moleculeGraph (toOfficialSourceTree tree) address =
      (tree.decoratedSubtreeAt? address).map fun subtree =>
        nodeObservation input.moleculeGraph subtree.source.occurrence.1.node := by
  unfold observationAt OfficialCIPSourceTree.sourceAtAddress?
  rw [toOfficialSourceTree_subtreeAt?]
  cases tree.decoratedSubtreeAt? address with
  | none => rfl
  | some subtree => simp [toOfficialSourceTree_source]

/-- **Addressed observations from the actual tie.** Equal actual constitutional keys give equal
label/provenance observations of the two erased source trees at every ranked address, occupied or
not. -/
theorem actualArm_observationAt_eq_of_constitutionalTie
    (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (tie : OfficialRuleMajorKey.compare
      (actualOriginalRootArm input center left stage read).key.constitutional
      (actualOriginalRootArm input center right stage read).key.constitutional = Ordering.eq)
    (address : List ℕ) :
    observationAt input.moleculeGraph
        (toOfficialSourceTree (actualOriginalRootArm input center left stage read).tree)
        address =
      observationAt input.moleculeGraph
        (toOfficialSourceTree (actualOriginalRootArm input center right stage read).tree)
        address := by
  rw [observationAt_toOfficialSourceTree, observationAt_toOfficialSourceTree]
  have sameShape := actualArmShape_eq_of_constitutionalTie input center left right stage read tie
  have sameAt := map_shape_decoratedSubtreeAt?
    (actualOriginalRootArm input center left stage read).tree
    (actualOriginalRootArm input center right stage read).tree sameShape address
  cases hleft : (actualOriginalRootArm input center left stage read).tree.decoratedSubtreeAt?
      address with
  | none =>
      cases hright : (actualOriginalRootArm input center right stage read).tree.decoratedSubtreeAt?
          address with
      | none => rfl
      | some target =>
          rw [hleft, hright] at sameAt
          simp at sameAt
  | some source =>
      obtain ⟨target, htarget, hshape⟩ :=
        actualArm_subtreeAt_address_eq_of_constitutionalTie input center left right stage read
          tie address source hleft
      rw [htarget]
      simp only [Option.map_some, Option.some.injEq]
      have rbSource := addressedRetainedReadback
        (actualOriginalRootArm input center left stage read) address source hleft
      have rbTarget := addressedRetainedReadback
        (actualOriginalRootArm input center right stage read) address target htarget
      have hZ : (ofLex (input.moleculeGraph.officialNodeAtomLabel
            source.source.occurrence.1.node)).1 =
          (ofLex (input.moleculeGraph.officialNodeAtomLabel
            target.source.occurrence.1.node)).1 := by
        rw [← rbSource.atomicNumber_eq, ← rbTarget.atomicNumber_eq, hshape]
      have hmass : (ofLex (input.moleculeGraph.officialNodeAtomLabel
            source.source.occurrence.1.node)).2 =
          (ofLex (input.moleculeGraph.officialNodeAtomLabel
            target.source.occurrence.1.node)).2 := by
        rw [← rbSource.isotopeMass_eq, ← rbTarget.isotopeMass_eq, hshape]
      have hlabel : input.moleculeGraph.officialNodeAtomLabel source.source.occurrence.1.node =
          input.moleculeGraph.officialNodeAtomLabel target.source.occurrence.1.node :=
        ofLex_inj.mp (Prod.ext hZ hmass)
      have hcollapse : collapseProvenance source.source.occurrence.1.node.provenance =
          collapseProvenance target.source.occurrence.1.node.provenance := by
        rw [← rbSource.provenance_eq, ← rbTarget.provenance_eq, hshape]
      have hprov := provenance_eq_of_collapse_eq rbSource.sphere.graphGenerated
        rbTarget.sphere.graphGenerated hcollapse
      unfold nodeObservation
      rw [hlabel, hprov]

/-- The two actual arms of a constitutional tie form an observed pair of boundary-rooted trees. -/
theorem actualArm_observedTreePair
    (input : CertifiedLocalizedCIPInput) (simple : input.moleculeGraph.SimpleBonded)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (tie : OfficialRuleMajorKey.compare
      (actualOriginalRootArm input center left stage read).key.constitutional
      (actualOriginalRootArm input center right stage read).key.constitutional = Ordering.eq) :
    ObservedTreePair input [center.1] [center.1]
      (input.canonicalLigandAtom center left) (input.canonicalLigandAtom center right)
      (toOfficialSourceTree (actualOriginalRootArm input center left stage read).tree)
      (toOfficialSourceTree (actualOriginalRootArm input center right stage read).tree) :=
  ⟨simple, actualArm_boundaryRooted input center left stage read,
    actualArm_boundaryRooted input center right stage read,
    actualArm_observationAt_eq_of_constitutionalTie input center left right stage read tie⟩

theorem ligand_adj_center_of_getLast? (input : CertifiedLocalizedCIPInput)
    (center : input.TetrahedralCenter) (index : Fin 4) (z : input.Atom)
    (hz : [center.1].getLast? = some z) :
    input.moleculeGraph.Adj (input.canonicalLigandAtom center index) z := by
  have hcenter : center.1 = z := by simpa using hz
  rw [← hcenter]
  exact input.moleculeGraph.adj_symm.mp (input.canonicalLigandAtom_adj center index)

/-- **Residual path-tree equivalence from an actual constitutional tie.** On a single-bonded
input with constant formal charge, equal actual constitutional keys of two original-root arms of
one center give a full `ResidualPathTreeEquiv` with boundary `[center]` between the two ligands.
It is constructed from the actual decorated trees: no path map, endpoint consistency, acyclicity
or automorphism is supplied. -/
noncomputable def actualArmResidualPathTreeEquiv
    (input : CertifiedLocalizedCIPInput) (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (tie : OfficialRuleMajorKey.compare
      (actualOriginalRootArm input center left stage read).key.constitutional
      (actualOriginalRootArm input center right stage read).key.constitutional = Ordering.eq) :
    ResidualPathTreeEquiv input.moleculeGraph [center.1] [center.1]
      (input.canonicalLigandAtom center left) (input.canonicalLigandAtom center right) :=
  residualPathTreeEquivOfSameObservations
    (actualArm_observedTreePair input simple center left right stage read tie) charge rfl
    (ligand_adj_center_of_getLast? input center left)
    (ligand_adj_center_of_getLast? input center right)

theorem nonempty_actualArmResidualPathTreeEquiv
    (input : CertifiedLocalizedCIPInput) (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (tie : OfficialRuleMajorKey.compare
      (actualOriginalRootArm input center left stage read).key.constitutional
      (actualOriginalRootArm input center right stage read).key.constitutional = Ordering.eq) :
    Nonempty (ResidualPathTreeEquiv input.moleculeGraph [center.1] [center.1]
      (input.canonicalLigandAtom center left) (input.canonicalLigandAtom center right)) :=
  ⟨actualArmResidualPathTreeEquiv input simple charge center left right stage read tie⟩

/-- **Molecular automorphism from an actual constitutional tie.** On a single-bonded input with
constant formal charge, equal actual constitutional keys of two original-root arms give a
molecular automorphism that fixes the center and sends the left ligand to the right ligand. It is
the identity outside the two center-deleted components, and every atom of the left component is
the terminal of an actual simple path whose path-tree image is its pointwise image. No
configuration or parity preservation is claimed. -/
theorem actualArm_automorphism_of_constitutionalTie
    (input : CertifiedLocalizedCIPInput) (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (tie : OfficialRuleMajorKey.compare
      (actualOriginalRootArm input center left stage read).key.constitutional
      (actualOriginalRootArm input center right stage read).key.constitutional = Ordering.eq) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      π center.1 = center.1 ∧
      π (input.canonicalLigandAtom center left) = input.canonicalLigandAtom center right ∧
      (∀ z, ¬ InComponent input.moleculeGraph [center.1] (input.canonicalLigandAtom center left) z →
        ¬ InComponent input.moleculeGraph [center.1] (input.canonicalLigandAtom center right) z →
          π z = z) ∧
      ∀ z, InComponent input.moleculeGraph [center.1] (input.canonicalLigandAtom center left) z →
        ∃ p : {p : List input.Atom // ResidualObsPath input.moleculeGraph [center.1]
            (input.canonicalLigandAtom center left) p},
          pathTerminal p.1 p.2.nonempty = z ∧
            ((actualArmResidualPathTreeEquiv input simple charge center left right stage read
              tie).toEquiv p).1 = p.1.map π :=
  BoundaryComponentReconstruction.root_outward_arm_automorphism
    (input.canonicalLigandAtom_adj center left)
    (actualArmResidualPathTreeEquiv input simple charge center left right stage read tie)

theorem sourceAtAddress?_toOfficialSourceTree (input : CertifiedLocalizedCIPInput)
    {carrierFuel : Nat} (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (address : List ℕ) :
    (toOfficialSourceTree tree).sourceAtAddress? address =
      (tree.decoratedSubtreeAt? address).map fun subtree => subtree.source.occurrence.1.node := by
  unfold OfficialCIPSourceTree.sourceAtAddress?
  rw [toOfficialSourceTree_subtreeAt?]
  cases tree.decoratedSubtreeAt? address with
  | none => rfl
  | some subtree => simp [toOfficialSourceTree_source]

/-- **Witnessed automorphism at actual occurrences.** In the automorphism from an actual
constitutional tie, every atom `z` of the left center-deleted component is the terminal of a
simple path `p` such that the real occurrence of `p` in the left actual tree and the real
occurrence of `p.map π` in the right actual tree sit at one common ranked address. The right
occurrence's whole stored history is therefore the `π`-image of the left one. -/
theorem actualArm_automorphism_witnessed_occurrences
    (input : CertifiedLocalizedCIPInput) (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (tie : OfficialRuleMajorKey.compare
      (actualOriginalRootArm input center left stage read).key.constitutional
      (actualOriginalRootArm input center right stage read).key.constitutional = Ordering.eq) :
    ∃ π : Equiv.Perm input.Atom, input.moleculeGraph.IsAutomorphism π ∧
      π center.1 = center.1 ∧
      π (input.canonicalLigandAtom center left) = input.canonicalLigandAtom center right ∧
      (∀ z, ¬ InComponent input.moleculeGraph [center.1] (input.canonicalLigandAtom center left) z →
        ¬ InComponent input.moleculeGraph [center.1] (input.canonicalLigandAtom center right) z →
          π z = z) ∧
      ∀ z, InComponent input.moleculeGraph [center.1] (input.canonicalLigandAtom center left) z →
        ∃ (p : List input.Atom) (address : List ℕ)
          (source target : LocalizedCumulativeDecoratedTree input
            (input.certified.input.molecule.atomCount + 1)),
          ResidualObsPath input.moleculeGraph [center.1]
            (input.canonicalLigandAtom center left) p ∧
          p.getLast? = some z ∧
          (actualOriginalRootArm input center left stage read).tree.decoratedSubtreeAt? address =
            some source ∧
          (actualOriginalRootArm input center right stage read).tree.decoratedSubtreeAt? address =
            some target ∧
          source.source.occurrence.1.node = boundaryNode [center.1] p ∧
          target.source.occurrence.1.node = boundaryNode [center.1] (p.map π) := by
  obtain ⟨π, hπ, hcenter, hmove, hout, hwit⟩ :=
    actualArm_automorphism_of_constitutionalTie input simple charge center left right stage read
      tie
  refine ⟨π, hπ, hcenter, hmove, hout, ?_⟩
  intro z hz
  obtain ⟨p, hterm, himg⟩ := hwit z hz
  have himg' : ((residualPathTreeEquivOfSameObservations
      (actualArm_observedTreePair input simple center left right stage read tie) charge rfl
      (ligand_adj_center_of_getLast? input center left)
      (ligand_adj_center_of_getLast? input center right)).toEquiv p).1 = p.1.map π := himg
  obtain ⟨address, hL, hR⟩ := residualPathTreeEquivOfSameObservations_correspond
    (actualArm_observedTreePair input simple center left right stage read tie) charge rfl
    (ligand_adj_center_of_getLast? input center left)
    (ligand_adj_center_of_getLast? input center right) p
  rw [sourceAtAddress?_toOfficialSourceTree] at hL hR
  obtain ⟨source, hsource, hsourceNode⟩ := Option.map_eq_some_iff.mp hL
  obtain ⟨target, htarget, htargetNode⟩ := Option.map_eq_some_iff.mp hR
  refine ⟨p.1, address, source, target, p.2, ?_, hsource, htarget, hsourceNode,
    htargetNode.trans ?_⟩
  · rw [List.getLast?_eq_some_getLast p.2.nonempty]
    exact congrArg some hterm
  · rw [himg']

/-- A distinct pair of original-root ligands of a constitutionally rigid center never tie
constitutionally: the tie would give a center-fixing automorphism moving one ligand to the other.
The hypothesis `rigid` is `ConstitutionallyRigidGraphAt input.moleculeGraph center.1` unfolded. -/
theorem actualArm_constitutional_compare_ne_eq_of_rigid
    (input : CertifiedLocalizedCIPInput) (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (center : input.TetrahedralCenter) (left right : Fin 4) (distinct : left ≠ right)
    (stage : LocalizedCumulativeRule45Stage)
    (read : input.LocalizedRerootCursor
      (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
    (rigid : ∀ e : input.moleculeGraph.Aut, (e : Equiv.Perm input.Atom) center.1 = center.1 →
      ∀ z, input.moleculeGraph.Adj center.1 z → (e : Equiv.Perm input.Atom) z = z) :
    OfficialRuleMajorKey.compare
      (actualOriginalRootArm input center left stage read).key.constitutional
      (actualOriginalRootArm input center right stage read).key.constitutional ≠ Ordering.eq := by
  intro tie
  obtain ⟨π, hπ, hcenter, hmove, -, -⟩ :=
    actualArm_automorphism_of_constitutionalTie input simple charge center left right stage read
      tie
  have hfixed := rigid ⟨π, hπ⟩ hcenter _ (input.canonicalLigandAtom_adj center left)
  exact distinct (input.canonicalLigandAtom_injective center (hfixed.symm.trans hmove))

/-! ## Outward sibling ties below an arbitrary ancestor boundary -/

section Sibling

variable (input : CertifiedLocalizedCIPInput)

/-- An actual outward child cursor arrived from its target. -/
theorem outwardChild_incoming
    (target child : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (previous : child.previous? = some target.occurrence)
    (root : child.occurrence.1.root = target.occurrence.1.root) (slot : ℕ)
    (address : child.occurrence.1.address = target.occurrence.1.address ++ [slot]) :
    LocalizedRerootCursorIncomingParent input child :=
  ⟨target.occurrence, previous, root.symm, by rw [address]; simp, by rw [address]; simp⟩

/-- The node of an actual outward child cursor is an executable child of the target node. -/
theorem outwardChild_node_mem
    (target child : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (root : child.occurrence.1.root = target.occurrence.1.root) (slot : ℕ)
    (address : child.occurrence.1.address = target.occurrence.1.address ++ [slot]) :
    child.occurrence.1.node ∈ input.executableOfficialCIPChildren target.occurrence.1.node := by
  have hframe : child.occurrence.1 ∈
      input.localizedCarrierOutwardChildFrames
        (fuel := input.certified.input.molecule.atomCount + 1) target.occurrence.1 :=
    (input.mem_localizedCarrierOutwardChildFrames_iff target.occurrence.1 child.occurrence.1).mpr
      ⟨child.occurrence.2, root, by rw [address]; simp, by rw [address]; simp⟩
  have derived := (input.mem_localizedOccurrences_iff _ target.occurrence.1).mp
    target.occurrence.2
  have positive := input.localizedOccurrences_remaining_pos_of_atomCount_le
    (Nat.le_succ _) target.occurrence.1 target.occurrence.2
  have perm := input.localizedOutwardChildFrames_nodes_perm_executable target.occurrence.1
    derived positive
  exact perm.subset (List.mem_map_of_mem hframe)

/-- Two actual outward children of one target with the same node are the same cursor. -/
theorem outwardChild_eq_of_node_eq (simple : input.moleculeGraph.SimpleBonded)
    (target left right :
      input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (leftPrevious : left.previous? = some target.occurrence)
    (rightPrevious : right.previous? = some target.occurrence)
    (leftRoot : left.occurrence.1.root = target.occurrence.1.root)
    (rightRoot : right.occurrence.1.root = target.occurrence.1.root) (leftSlot rightSlot : ℕ)
    (leftAddress : left.occurrence.1.address = target.occurrence.1.address ++ [leftSlot])
    (rightAddress : right.occurrence.1.address = target.occurrence.1.address ++ [rightSlot])
    (same : left.occurrence.1.node = right.occurrence.1.node) : left = right := by
  have frame : ∀ (child : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1)) (slot : ℕ),
      child.occurrence.1.root = target.occurrence.1.root →
      child.occurrence.1.address = target.occurrence.1.address ++ [slot] →
      child.occurrence.1 ∈ input.localizedCarrierOutwardChildFrames
        (fuel := input.certified.input.molecule.atomCount + 1) target.occurrence.1 := by
    intro child slot root address
    exact (input.mem_localizedCarrierOutwardChildFrames_iff target.occurrence.1
      child.occurrence.1).mpr ⟨child.occurrence.2, root, by rw [address]; simp,
        by rw [address]; simp⟩
  have derived := (input.mem_localizedOccurrences_iff _ target.occurrence.1).mp
    target.occurrence.2
  have positive := input.localizedOccurrences_remaining_pos_of_atomCount_le
    (Nat.le_succ _) target.occurrence.1 target.occurrence.2
  have perm := input.localizedOutwardChildFrames_nodes_perm_executable target.occurrence.1
    derived positive
  have hnodup := perm.nodup_iff.mpr
    (executableOfficialCIPChildren_nodup input simple target.occurrence.1.node)
  have hframes := List.inj_on_of_nodup_map hnodup
    (frame left leftSlot leftRoot leftAddress) (frame right rightSlot rightRoot rightAddress) same
  apply LocalizedRerootCursor.ext input
  · exact Subtype.ext hframes
  · rw [leftPrevious, rightPrevious]

/-- A real carrier occurrence has a duplicate-free history whose newest atom is current. -/
theorem occurrence_history_facts {fuel : Nat} (occurrence : input.LocalizedCIPOccurrence fuel)
    (real : occurrence.1.node.provenance = .realAtom) :
    occurrence.1.node.history.Nodup ∧
      occurrence.1.node.current? = occurrence.1.node.history.head? := by
  have reach := input.declarativeLocalizedOccurrence_unbounded
    ((input.mem_localizedOccurrences_iff fuel occurrence.1).mp occurrence.2)
  exact ⟨unbounded_real_history_nodup reach (by simp [OfficialCIPNode.root]) real,
    unbounded_current_eq_head reach rfl⟩

/-- An actual tree of the shipped revised builder at an incoming cursor, at stage Rule 4a with
the empty reader: build, table match, realization and executable generatedness. -/
theorem exists_actualIncomingTree
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (incoming : LocalizedRerootCursorIncomingParent input cursor) :
    ∃ (tree : LocalizedCumulativeDecoratedTree input
        (input.certified.input.molecule.atomCount + 1))
      (key : input.LocalizedRerootCumulativeRule45Key),
      tree.source = cursor ∧
      input.buildRuleMajorCumulativeWithRead? .rule4a (fun _ => none)
        (2 * (input.certified.input.molecule.atomCount + 1 + 1)) cursor = some key ∧
      LocalizedCumulativeTreeTableMatch .rule4a tree key ∧
      LocalizedCumulativeTreeRealizes input (fun _ => none) tree ∧
      (toOfficialSourceTree tree).GeneratedBy input.executableOfficialCIPChildren := by
  have valid := input.localizedRerootCursorValid_of_incoming cursor incoming
  obtain ⟨tree, key, source, built, trace⟩ :=
    exists_ruleMajorTrace_at_twice input .rule4a (fun _ => none) cursor valid
  have tableMatch := (LocalizedRuleMajorSortTrace.fullMatch_of_trace trace).tableMatch
  have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
  have positive : LocalizedCumulativeTreePositive tree :=
    input.localizedCumulativeTreePositive_of_atomCount_le
      (fuel := input.certified.input.molecule.atomCount + 1) (by omega) tree
  have treeIncoming : LocalizedCumulativeTreeIncoming input tree := by
    apply input.localizedCumulativeTreeIncoming_of_realizes (fun _ => none) tree realizes
    rwa [source]
  exact ⟨tree, key, source, built, tableMatch, realizes,
    input.toOfficialSourceTree_generatedBy (fun _ => none) tree realizes positive treeIncoming⟩

/-- The comparison-visible fields of a realized decorated subtree read its source node. -/
theorem realized_fields {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizes : LocalizedCumulativeTreeRealizes input read tree) (address : List ℕ)
    (subtree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (lookup : tree.decoratedSubtreeAt? address = some subtree) :
    subtree.shape.atomicNumber =
        (ofLex (input.moleculeGraph.officialNodeAtomLabel subtree.source.occurrence.1.node)).1 ∧
      subtree.shape.rule1bDistance = subtree.source.occurrence.1.node.rule1bRootDistance ∧
      subtree.shape.isotopeMass =
        (ofLex (input.moleculeGraph.officialNodeAtomLabel subtree.source.occurrence.1.node)).2 := by
  have realized := realizes_of_decoratedSubtreeAt? tree realizes address subtree lookup
  have fields : subtree.shape.atomicNumber = subtree.atomicNumber ∧
      subtree.shape.rule1bDistance = subtree.rule1bDistance ∧
      subtree.shape.isotopeMass = subtree.isotopeMass := by
    obtain ⟨source, atomicNumber, rule1bDistance, isotopeMass, label, children⟩ := subtree
    rw [shape]
    exact ⟨rfl, rfl, rfl⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [fields.1, realized]
    rfl
  · rw [fields.2.1, realized]
    rfl
  · rw [fields.2.2, realized]
    rfl

/-- Equal shapes of two realized decorated trees give equal label/Rule-1b observations of their
erased source trees at every ranked address. -/
theorem constitutionalObservationAt_eq_of_shape_eq {carrierFuel : Nat}
    {readL readR : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (treeL treeR : LocalizedCumulativeDecoratedTree input carrierFuel)
    (realizesL : LocalizedCumulativeTreeRealizes input readL treeL)
    (realizesR : LocalizedCumulativeTreeRealizes input readR treeR)
    (sameShape : treeL.shape = treeR.shape) (address : List ℕ) :
    constitutionalObservationAt input.moleculeGraph (toOfficialSourceTree treeL) address =
      constitutionalObservationAt input.moleculeGraph (toOfficialSourceTree treeR) address := by
  have hobs : ∀ tree : LocalizedCumulativeDecoratedTree input carrierFuel,
      constitutionalObservationAt input.moleculeGraph (toOfficialSourceTree tree) address =
        (tree.decoratedSubtreeAt? address).map fun subtree =>
          (input.moleculeGraph.officialNodeAtomLabel subtree.source.occurrence.1.node,
            subtree.source.occurrence.1.node.rule1bRootDistance) := by
    intro tree
    unfold constitutionalObservationAt OfficialCIPSourceTree.sourceAtAddress?
    rw [toOfficialSourceTree_subtreeAt?]
    cases tree.decoratedSubtreeAt? address with
    | none => rfl
    | some subtree => simp [toOfficialSourceTree_source]
  rw [hobs treeL, hobs treeR]
  have sameAt := map_shape_decoratedSubtreeAt? treeL treeR sameShape address
  cases hL : treeL.decoratedSubtreeAt? address with
  | none =>
      cases hR : treeR.decoratedSubtreeAt? address with
      | none => rfl
      | some target =>
          rw [hL, hR] at sameAt
          simp at sameAt
  | some source =>
      cases hR : treeR.decoratedSubtreeAt? address with
      | none =>
          rw [hL, hR] at sameAt
          simp at sameAt
      | some target =>
          rw [hL, hR] at sameAt
          have hshape : source.shape = target.shape := by simpa using sameAt
          have fL := realized_fields input treeL realizesL address source hL
          have fR := realized_fields input treeR realizesR address target hR
          have hZ : (ofLex (input.moleculeGraph.officialNodeAtomLabel
                source.source.occurrence.1.node)).1 =
              (ofLex (input.moleculeGraph.officialNodeAtomLabel
                target.source.occurrence.1.node)).1 := by
            rw [← fL.1, ← fR.1, hshape]
          have hmass : (ofLex (input.moleculeGraph.officialNodeAtomLabel
                source.source.occurrence.1.node)).2 =
              (ofLex (input.moleculeGraph.officialNodeAtomLabel
                target.source.occurrence.1.node)).2 := by
            rw [← fL.2.2, ← fR.2.2, hshape]
          have hrule : source.source.occurrence.1.node.rule1bRootDistance =
              target.source.occurrence.1.node.rule1bRootDistance := by
            rw [← fL.2.1, ← fR.2.1, hshape]
          have hlabel :
              input.moleculeGraph.officialNodeAtomLabel source.source.occurrence.1.node =
                input.moleculeGraph.officialNodeAtomLabel target.source.occurrence.1.node :=
            ofLex_inj.mp (Prod.ext hZ hmass)
          simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
          exact ⟨hlabel, hrule⟩

/-- A real outward child of a real target is the fresh zero-index extension of the target node by
an atom bonded to the target atom. -/
theorem outwardChild_atom_facts (simple : input.moleculeGraph.SimpleBonded)
    (target child : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (root : child.occurrence.1.root = target.occurrence.1.root) (slot : ℕ)
    (address : child.occurrence.1.address = target.occurrence.1.address ++ [slot])
    (targetReal : target.occurrence.1.node.provenance = .realAtom)
    (childReal : child.occurrence.1.node.provenance = .realAtom)
    {t : input.Atom} (ht : target.occurrence.1.node.current? = some t) :
    ∃ a, child.occurrence.1.node = target.occurrence.1.node.extend a 0 ∧
      input.moleculeGraph.Adj t a ∧ a ∉ target.occurrence.1.node.history := by
  have hmem := outwardChild_node_mem input target child root slot address
  obtain ⟨a, ha, hadj, _⟩ :=
    (mem_executableOfficialCIPChildren_iff input simple _ ht targetReal _).mp hmem
  refine ⟨a, ha, hadj, ?_⟩
  intro hin
  have hprov := childReal
  rw [ha, OfficialCIPNode.extend_provenance,
    OfficialCIPNode.childProvenance_ring_duplicate _ _ hin] at hprov
  exact OfficialCIPNodeProvenance.noConfusion hprov

/-- The erased actual tree at a real outward child of a real target is boundary-rooted at the
child atom below the whole root-first target history. The child atom is bonded to the target
atom, which is the last boundary atom, and lies outside the boundary. -/
theorem outwardChild_boundaryRooted (simple : input.moleculeGraph.SimpleBonded)
    (target child : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (root : child.occurrence.1.root = target.occurrence.1.root) (slot : ℕ)
    (address : child.occurrence.1.address = target.occurrence.1.address ++ [slot])
    (targetReal : target.occurrence.1.node.provenance = .realAtom)
    (childReal : child.occurrence.1.node.provenance = .realAtom)
    {a : input.Atom} (ha : child.occurrence.1.node.current? = some a)
    (tree : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
    (source : tree.source = child)
    (generated : (toOfficialSourceTree tree).GeneratedBy input.executableOfficialCIPChildren) :
    BoundaryRootedTree input target.occurrence.1.node.history.reverse a
        (toOfficialSourceTree tree) ∧
      a ∉ target.occurrence.1.node.history ∧
      ∀ t, target.occurrence.1.node.current? = some t → input.moleculeGraph.Adj t a := by
  have targetFacts := occurrence_history_facts input target.occurrence targetReal
  obtain ⟨t, ht⟩ := exists_current_of_mem_children input
    (outwardChild_node_mem input target child root slot address)
  have hall : ∀ t', target.occurrence.1.node.current? = some t' →
      child.occurrence.1.node = target.occurrence.1.node.extend a 0 ∧
        input.moleculeGraph.Adj t' a ∧ a ∉ target.occurrence.1.node.history := by
    intro t' ht'
    obtain ⟨z, hz, hadj, hfresh⟩ := outwardChild_atom_facts input simple target child root slot
      address targetReal childReal ht'
    have hza : z = a := by
      have hcur := congrArg OfficialCIPNode.current? hz
      rw [ha, OfficialCIPNode.extend_current?] at hcur
      exact (Option.some.inj hcur).symm
    rw [hza] at hz hadj hfresh
    exact ⟨hz, hadj, hfresh⟩
  obtain ⟨hnode, -, hfresh⟩ := hall t ht
  refine ⟨⟨generated, ?_, ?_⟩, hfresh, fun t' ht' => (hall t' ht').2.1⟩
  · rw [toOfficialSourceTree_source, source, hnode, extend_eq_boundaryNode_history hfresh]
  · rw [List.nodup_append]
    refine ⟨List.nodup_reverse.mpr targetFacts.1, List.nodup_singleton a, ?_⟩
    intro u hu v hv huv
    rw [List.mem_singleton] at hv
    rw [hv] at huv
    rw [huv] at hu
    exact hfresh (List.mem_reverse.mp hu)

/-- A constitutional tie of any two successful revised builds at two actual outward sibling
cursors, at any stages, readers and fuels, gives two actual realized Rule-4a trees at the cursors,
both executable-generated, with equal constitutional shapes. -/
theorem exists_outwardSibling_trees_of_tie
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input
      (input.certified.input.molecule.atomCount + 1))
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    {fuelL fuelR : Nat} {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL readL fuelL pair.left = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR readR fuelR pair.right = some keyR)
    (tie : OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional =
      Ordering.eq) :
    ∃ treeL treeR : LocalizedCumulativeDecoratedTree input
        (input.certified.input.molecule.atomCount + 1),
      treeL.source = pair.left ∧ treeR.source = pair.right ∧
      LocalizedCumulativeTreeRealizes input (fun _ => none) treeL ∧
      LocalizedCumulativeTreeRealizes input (fun _ => none) treeR ∧
      (toOfficialSourceTree treeL).GeneratedBy input.executableOfficialCIPChildren ∧
      (toOfficialSourceTree treeR).GeneratedBy input.executableOfficialCIPChildren ∧
      treeL.shape = treeR.shape := by
  obtain ⟨treeL, keyL₀, sourceL, builtL₀, matchL, realizesL, generatedL⟩ :=
    exists_actualIncomingTree input pair.left
      (outwardChild_incoming input pair.target pair.left pair.leftPrevious pair.leftRoot
        pair.leftSlot pair.leftAddress)
  obtain ⟨treeR, keyR₀, sourceR, builtR₀, matchR, realizesR, generatedR⟩ :=
    exists_actualIncomingTree input pair.right
      (outwardChild_incoming input pair.target pair.right pair.rightPrevious pair.rightRoot
        pair.rightSlot pair.rightAddress)
  have tie₀ : OfficialRuleMajorKey.compare keyL₀.constitutional keyR₀.constitutional =
      Ordering.eq := by
    rw [← RetainedConstitutionalReaderIndependence.ruleMajorBuild_constitutional_compare_congr
      stageL stageR .rule4a .rule4a readL readR (fun _ => none) (fun _ => none)
      pair.left pair.right builtL builtR builtL₀ builtR₀]
    exact tie
  have cols := (officialRuleMajorKey_compare_eq_iff _ _).mp tie₀
  have sameShape : treeL.shape = treeR.shape := by
    rcases matchL with ⟨h1aL, h1bL, h2L, _⟩
    rcases matchR with ⟨h1aR, h1bR, h2R, _⟩
    simp only [tables_rule1a, tables_rule1b, tables_rule2] at h1aL h1bL h2L h1aR h1bR h2R
    exact table_shape_eq_of_constitutional_tables_eq treeL treeR
      (h1aL.trans (cols.1.trans h1aR.symm))
      (h1bL.trans (cols.2.1.trans h1bR.symm))
      (h2L.trans (cols.2.2.trans h2R.symm))
  exact ⟨treeL, treeR, sourceL, sourceR, realizesL, realizesR, generatedL, generatedR,
    sameShape⟩

/-- A constitutional tie of actual outward siblings forces equal Rule-1b values at the two
sibling nodes themselves. -/
theorem outwardSibling_rule1b_eq_of_tie
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input
      (input.certified.input.molecule.atomCount + 1))
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    {fuelL fuelR : Nat} {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL readL fuelL pair.left = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR readR fuelR pair.right = some keyR)
    (tie : OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional =
      Ordering.eq) :
    pair.left.occurrence.1.node.rule1bRootDistance =
      pair.right.occurrence.1.node.rule1bRootDistance := by
  obtain ⟨treeL, treeR, sourceL, sourceR, realizesL, realizesR, _, _, sameShape⟩ :=
    exists_outwardSibling_trees_of_tie input pair builtL builtR tie
  have fL := realized_fields input treeL realizesL [] treeL rfl
  have fR := realized_fields input treeR realizesR [] treeR rfl
  rw [← sourceL, ← sourceR, ← fL.2.1, ← fR.2.1, sameShape]

/-- **Same-boundary residual path-tree equivalence from an actual outward sibling tie.** Let two
actual outward sibling cursors at a real target be real, with atoms `a` and `b`. If any two
successful revised builds at the two cursors, at any stages, readers and fuels, tie
constitutionally, then there is a residual path-tree equivalence from `a` to `b` whose ordered
boundary on both sides is the whole root-first history of the target, ending with the target
atom. No path map, acyclicity or automorphism is supplied. -/
theorem nonempty_outwardSiblingResidualPathTreeEquiv (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input
      (input.certified.input.molecule.atomCount + 1))
    (targetReal : pair.target.occurrence.1.node.provenance = .realAtom)
    (leftReal : pair.left.occurrence.1.node.provenance = .realAtom)
    (rightReal : pair.right.occurrence.1.node.provenance = .realAtom)
    {a b : input.Atom} (ha : pair.left.occurrence.1.node.current? = some a)
    (hb : pair.right.occurrence.1.node.current? = some b)
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    {fuelL fuelR : Nat} {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL readL fuelL pair.left = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR readR fuelR pair.right = some keyR)
    (tie : OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional =
      Ordering.eq) :
    Nonempty (ResidualPathTreeEquiv input.moleculeGraph
      pair.target.occurrence.1.node.history.reverse
      pair.target.occurrence.1.node.history.reverse a b) := by
  obtain ⟨treeL, treeR, sourceL, sourceR, realizesL, realizesR, generatedL, generatedR,
    sameShape⟩ := exists_outwardSibling_trees_of_tie input pair builtL builtR tie
  obtain ⟨rootedL, _, hadjL⟩ := outwardChild_boundaryRooted input simple pair.target pair.left
    pair.leftRoot pair.leftSlot pair.leftAddress targetReal leftReal ha treeL sourceL generatedL
  obtain ⟨rootedR, _, hadjR⟩ := outwardChild_boundaryRooted input simple pair.target pair.right
    pair.rightRoot pair.rightSlot pair.rightAddress targetReal rightReal hb treeR sourceR
    generatedR
  have observed := observedTreePair_of_constitutional simple rootedL rootedR rfl
    (constitutionalObservationAt_eq_of_shape_eq input treeL treeR realizesL realizesR sameShape)
  have targetFacts := occurrence_history_facts input pair.target.occurrence targetReal
  have parentOf : ∀ c : input.Atom,
      (∀ t, pair.target.occurrence.1.node.current? = some t → input.moleculeGraph.Adj t c) →
        ∀ z, pair.target.occurrence.1.node.history.reverse.getLast? = some z →
          input.moleculeGraph.Adj c z := by
    intro c hadj z hz
    rw [List.getLast?_reverse, ← targetFacts.2] at hz
    exact input.moleculeGraph.adj_symm.mp (hadj z hz)
  exact ⟨residualPathTreeEquivOfSameObservations observed charge rfl (parentOf a hadjL)
    (parentOf b hadjR)⟩

/-- **Constitutional strictness of real outward siblings at a rigid real target.** Let two
distinct actual outward sibling cursors at a real target be real. If the target atom is
constitutionally rigid, every pair of successful revised builds at the two cursors, at any stages,
readers and fuels, is constitutionally strict. A tie would give a same-boundary residual
path-tree equivalence, hence a molecular automorphism fixing the target history and moving one
outward neighbor to the other. The conclusion is `ConstitutionallySeparated pair.left pair.right`
unfolded, and `rigid` is `ConstitutionallyRigidGraphAt input.moleculeGraph t` unfolded. -/
theorem outwardSibling_constitutionallySeparated_of_rigid
    (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input
      (input.certified.input.molecule.atomCount + 1))
    (targetReal : pair.target.occurrence.1.node.provenance = .realAtom)
    (leftReal : pair.left.occurrence.1.node.provenance = .realAtom)
    (rightReal : pair.right.occurrence.1.node.provenance = .realAtom)
    (distinct : pair.left ≠ pair.right)
    {t : input.Atom} (ht : pair.target.occurrence.1.node.current? = some t)
    (rigid : ∀ e : input.moleculeGraph.Aut, (e : Equiv.Perm input.Atom) t = t →
      ∀ z, input.moleculeGraph.Adj t z → (e : Equiv.Perm input.Atom) z = z) :
    ∀ (stageL stageR : LocalizedCumulativeRule45Stage)
      (readL readR : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
      (fuelL fuelR : Nat) (keyL keyR : input.LocalizedRerootCumulativeRule45Key),
      input.buildRuleMajorCumulativeWithRead? stageL readL fuelL pair.left = some keyL →
      input.buildRuleMajorCumulativeWithRead? stageR readR fuelR pair.right = some keyR →
      OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional ≠ Ordering.eq := by
  intro stageL stageR readL readR fuelL fuelR keyL keyR builtL builtR tie
  obtain ⟨a, haNode, hadjA, haFresh⟩ := outwardChild_atom_facts input simple pair.target
    pair.left pair.leftRoot pair.leftSlot pair.leftAddress targetReal leftReal ht
  obtain ⟨b, hbNode, _, _⟩ := outwardChild_atom_facts input simple pair.target pair.right
    pair.rightRoot pair.rightSlot pair.rightAddress targetReal rightReal ht
  have ha : pair.left.occurrence.1.node.current? = some a := by
    rw [haNode]
    rfl
  have hb : pair.right.occurrence.1.node.current? = some b := by
    rw [hbNode]
    rfl
  obtain ⟨e⟩ := nonempty_outwardSiblingResidualPathTreeEquiv input simple charge pair
    targetReal leftReal rightReal ha hb builtL builtR tie
  have targetFacts := occurrence_history_facts input pair.target.occurrence targetReal
  have htMem : t ∈ pair.target.occurrence.1.node.history.reverse := by
    rw [List.mem_reverse]
    rw [targetFacts.2] at ht
    exact List.mem_of_mem_head? ht
  have haOut : a ∉ pair.target.occurrence.1.node.history.reverse := by
    rw [List.mem_reverse]
    exact haFresh
  have hab : a ≠ b := by
    intro hsame
    apply distinct
    apply outwardChild_eq_of_node_eq input simple pair.target pair.left pair.right
      pair.leftPrevious pair.rightPrevious pair.leftRoot pair.rightRoot pair.leftSlot
      pair.rightSlot pair.leftAddress pair.rightAddress
    rw [haNode, hbNode, hsame]
  obtain ⟨π, hπ, hfix, hmove, -, -⟩ :=
    BoundaryComponentReconstruction.exists_sameBoundary_automorphism e haOut
  have hfixed := rigid ⟨π, hπ⟩ (hfix t htMem) a hadjA
  exact hab (hfixed.symm.trans hmove)

/-- **Constitutional separation of distinct actual outward siblings at a rigid real target.**
For a real target whose atom is constitutionally rigid, any two distinct actual outward sibling
cursors are constitutionally separated, whatever their provenance. A real/ring-duplicate tie is
excluded by the sibling Rule-1b values: a real child carries the depth and a ring duplicate a
smaller root-first index. Two ring duplicates with one index duplicate the same atom, hence are the
same cursor. A real/real tie contradicts rigidity
(`outwardSibling_constitutionallySeparated_of_rigid`). The conclusion is
`ConstitutionallySeparated pair.left pair.right` unfolded. -/
theorem outwardSibling_separated_of_rigidTarget
    (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input
      (input.certified.input.molecule.atomCount + 1))
    (targetReal : pair.target.occurrence.1.node.provenance = .realAtom)
    (distinct : pair.left ≠ pair.right)
    {t : input.Atom} (ht : pair.target.occurrence.1.node.current? = some t)
    (rigid : ∀ e : input.moleculeGraph.Aut, (e : Equiv.Perm input.Atom) t = t →
      ∀ z, input.moleculeGraph.Adj t z → (e : Equiv.Perm input.Atom) z = z) :
    ∀ (stageL stageR : LocalizedCumulativeRule45Stage)
      (readL readR : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
      (fuelL fuelR : Nat) (keyL keyR : input.LocalizedRerootCumulativeRule45Key),
      input.buildRuleMajorCumulativeWithRead? stageL readL fuelL pair.left = some keyL →
      input.buildRuleMajorCumulativeWithRead? stageR readR fuelR pair.right = some keyR →
      OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional ≠ Ordering.eq := by
  intro stageL stageR readL readR fuelL fuelR keyL keyR builtL builtR tie
  have hmemL := outwardChild_node_mem input pair.target pair.left pair.leftRoot pair.leftSlot
    pair.leftAddress
  have hmemR := outwardChild_node_mem input pair.target pair.right pair.rightRoot pair.rightSlot
    pair.rightAddress
  obtain ⟨zL, hzL, _, _⟩ :=
    (mem_executableOfficialCIPChildren_iff input simple _ ht targetReal _).mp hmemL
  obtain ⟨zR, hzR, _, _⟩ :=
    (mem_executableOfficialCIPChildren_iff input simple _ ht targetReal _).mp hmemR
  have hrule := outwardSibling_rule1b_eq_of_tie input pair builtL builtR tie
  rw [hzL, hzR] at hrule
  by_cases hL : zL ∈ pair.target.occurrence.1.node.history
  · obtain ⟨kL, hgetL, _, hruleL, hltL⟩ := extend_rule1b_of_mem hL
    by_cases hR : zR ∈ pair.target.occurrence.1.node.history
    · obtain ⟨kR, hgetR, _, hruleR, _⟩ := extend_rule1b_of_mem hR
      rw [hruleL, hruleR] at hrule
      rw [hrule] at hgetL
      have hz : zL = zR := Option.some.inj (hgetL.symm.trans hgetR)
      apply distinct
      apply outwardChild_eq_of_node_eq input simple pair.target pair.left pair.right
        pair.leftPrevious pair.rightPrevious pair.leftRoot pair.rightRoot pair.leftSlot
        pair.rightSlot pair.leftAddress pair.rightAddress
      rw [hzL, hzR, hz]
    · have hruleR := (extend_rule1b_of_not_mem hR).2
      rw [hruleL, hruleR] at hrule
      omega
  · have hruleL := (extend_rule1b_of_not_mem hL).2
    by_cases hR : zR ∈ pair.target.occurrence.1.node.history
    · obtain ⟨kR, _, _, hruleR, hltR⟩ := extend_rule1b_of_mem hR
      rw [hruleL, hruleR] at hrule
      omega
    · have leftReal : pair.left.occurrence.1.node.provenance = .realAtom := by
        rw [hzL]
        exact (extend_rule1b_of_not_mem hL).1
      have rightReal : pair.right.occurrence.1.node.provenance = .realAtom := by
        rw [hzR]
        exact (extend_rule1b_of_not_mem hR).1
      exact outwardSibling_constitutionallySeparated_of_rigid input simple charge pair targetReal
        leftReal rightReal distinct ht rigid stageL stageR readL readR fuelL fuelR keyL keyR
        builtL builtR tie

/-- **The outward separation obligation at a rigid real target.** Every actual outward sibling
pair of distinct cursors at the target-start cursor of a real target occurrence, whose atom is
constitutionally rigid, is constitutionally separated. This is the `outward` hypothesis of
`LocalizedCyclicGeneralRigidPriority.frameConstitutionalStrict_of_rootArmRule1aTie`, with
`ConstitutionallySeparated` unfolded; carrier fuel `carrierFuel input` is `atomCount + 1`. -/
theorem outwardSiblings_separated_of_rigidTarget
    (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (target : input.LocalizedCIPOccurrence (input.certified.input.molecule.atomCount + 1))
    (targetReal : target.1.node.provenance = .realAtom)
    {t : input.Atom} (ht : target.1.node.current? = some t)
    (rigid : ∀ e : input.moleculeGraph.Aut, (e : Equiv.Perm input.Atom) t = t →
      ∀ z, input.moleculeGraph.Adj t z → (e : Equiv.Perm input.Atom) z = z) :
    ∀ pair : LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input
        (input.certified.input.molecule.atomCount + 1),
      pair.target = { occurrence := target, previous? := none } → pair.left ≠ pair.right →
      ∀ (stageL stageR : LocalizedCumulativeRule45Stage)
        (readL readR : input.LocalizedRerootCursor
          (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
        (fuelL fuelR : Nat) (keyL keyR : input.LocalizedRerootCumulativeRule45Key),
        input.buildRuleMajorCumulativeWithRead? stageL readL fuelL pair.left = some keyL →
        input.buildRuleMajorCumulativeWithRead? stageR readR fuelR pair.right = some keyR →
        OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional ≠ Ordering.eq := by
  intro pair hpair distinct
  have hocc : pair.target.occurrence = target := by rw [hpair]
  have targetReal' : pair.target.occurrence.1.node.provenance = .realAtom := by
    rw [hocc]
    exact targetReal
  have ht' : pair.target.occurrence.1.node.current? = some t := by
    rw [hocc]
    exact ht
  exact outwardSibling_separated_of_rigidTarget input simple charge pair targetReal' distinct ht'
    rigid

/-! ### The original root as a sibling target -/

/-- The center's root-start cursor. -/
noncomputable def centerRootStartCursor (center : input.TetrahedralCenter) :
    input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) where
  occurrence := input.localizedAtomRootOccurrence
    (input.certified.input.molecule.atomCount + 1) center.1
  previous? := none

/-- Two actual ligand root cursors are actual outward siblings at the center's root-start
cursor. -/
noncomputable def ligandRootSiblingPair (center : input.TetrahedralCenter) (left right : Fin 4) :
    LocalizedActualOutwardRule1bEquivalence.ActualOutwardSiblingPair input
      (input.certified.input.molecule.atomCount + 1) where
  target := centerRootStartCursor input center
  left := input.localizedLigandRootCursor center left
  right := input.localizedLigandRootCursor center right
  leftPrevious := rfl
  rightPrevious := rfl
  leftRoot := rfl
  rightRoot := rfl
  leftSlot := input.localizedLigandRootSlot center left
  rightSlot := input.localizedLigandRootSlot center right
  leftAddress := rfl
  rightAddress := rfl

theorem localizedLigandRootCursor_ne (center : input.TetrahedralCenter) {left right : Fin 4}
    (distinct : left ≠ right) :
    input.localizedLigandRootCursor center left ≠ input.localizedLigandRootCursor center right := by
  intro same
  have hnode := congrArg (fun cursor : input.LocalizedRerootCursor
    (input.certified.input.molecule.atomCount + 1) => cursor.occurrence.1.node.current?) same
  simp only [localizedLigandRootCursor_node, localizedLigandRootNode,
    OfficialCIPNode.extend_current?, Option.some.injEq] at hnode
  exact distinct (input.canonicalLigandAtom_injective center hnode)

/-- **Root ligand ties of the revised builder.** Any constitutional tie of successful revised
builds at two actual ligand root cursors, at any stages, readers and fuels, gives a residual
path-tree equivalence with boundary `[center]` between the two ligands. -/
theorem nonempty_ligandRoot_residualPathTreeEquiv (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (center : input.TetrahedralCenter) (left right : Fin 4)
    {stageL stageR : LocalizedCumulativeRule45Stage}
    {readL readR : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
      Option LocalizedAuxiliaryLabel}
    {fuelL fuelR : Nat} {keyL keyR : input.LocalizedRerootCumulativeRule45Key}
    (builtL : input.buildRuleMajorCumulativeWithRead? stageL readL fuelL
      (input.localizedLigandRootCursor center left) = some keyL)
    (builtR : input.buildRuleMajorCumulativeWithRead? stageR readR fuelR
      (input.localizedLigandRootCursor center right) = some keyR)
    (tie : OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional =
      Ordering.eq) :
    Nonempty (ResidualPathTreeEquiv input.moleculeGraph [center.1] [center.1]
      (input.canonicalLigandAtom center left) (input.canonicalLigandAtom center right)) :=
  nonempty_outwardSiblingResidualPathTreeEquiv input simple charge
    (ligandRootSiblingPair input center left right) rfl
    (input.localizedLigandRootNode_provenance center left)
    (input.localizedLigandRootNode_provenance center right) rfl rfl builtL builtR tie

/-- **Root ligand strictness of the revised builder.** At a constitutionally rigid center, every
pair of successful revised builds at two distinct actual ligand root cursors, at any stages,
readers and fuels, is constitutionally strict. -/
theorem ligandRoots_separated_of_rigid (simple : input.moleculeGraph.SimpleBonded)
    (charge : AcyclicCutBranchAutomorphism.ConstantFormalCharge input.moleculeGraph)
    (center : input.TetrahedralCenter) {left right : Fin 4} (distinct : left ≠ right)
    (rigid : ∀ e : input.moleculeGraph.Aut, (e : Equiv.Perm input.Atom) center.1 = center.1 →
      ∀ z, input.moleculeGraph.Adj center.1 z → (e : Equiv.Perm input.Atom) z = z) :
    ∀ (stageL stageR : LocalizedCumulativeRule45Stage)
      (readL readR : input.LocalizedRerootCursor
        (input.certified.input.molecule.atomCount + 1) → Option LocalizedAuxiliaryLabel)
      (fuelL fuelR : Nat) (keyL keyR : input.LocalizedRerootCumulativeRule45Key),
      input.buildRuleMajorCumulativeWithRead? stageL readL fuelL
        (input.localizedLigandRootCursor center left) = some keyL →
      input.buildRuleMajorCumulativeWithRead? stageR readR fuelR
        (input.localizedLigandRootCursor center right) = some keyR →
      OfficialRuleMajorKey.compare keyL.constitutional keyR.constitutional ≠ Ordering.eq :=
  outwardSibling_separated_of_rigidTarget input simple charge
    (ligandRootSiblingPair input center left right) rfl
    (localizedLigandRootCursor_ne input center distinct) rfl rigid

end Sibling

end LocalizedActualBoundaryObservationReadback
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.actualArmObservation_eq_of_constitutionalTie
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.actualArmShape_eq_of_constitutionalTie
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.actualArm_subtreeAt_address_eq_of_constitutionalTie
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.actualArm_addressed_occurrence_observations_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.exists_real_child_for_fresh_neighbor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.generated_source_child_has_address
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.generated_tree_address_of_unbounded_subtree
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.provenance_eq_of_collapse_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.actualArm_boundaryRooted
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.observationAt_toOfficialSourceTree
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.actualArm_observedTreePair
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.ligand_adj_center_of_getLast?
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.sourceAtAddress?_toOfficialSourceTree
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.outwardChild_incoming
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.outwardChild_node_mem
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.outwardChild_eq_of_node_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.occurrence_history_facts
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.realized_fields
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.constitutionalObservationAt_eq_of_shape_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.outwardChild_atom_facts
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.centerRootStartCursor
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.localizedLigandRootCursor_ne
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.actualArm_observationAt_eq_of_constitutionalTie
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.actualArmResidualPathTreeEquiv
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.nonempty_actualArmResidualPathTreeEquiv
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.actualArm_automorphism_of_constitutionalTie
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.actualArm_automorphism_witnessed_occurrences
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.actualArm_constitutional_compare_ne_eq_of_rigid
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.exists_actualIncomingTree
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.outwardChild_boundaryRooted
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.nonempty_outwardSiblingResidualPathTreeEquiv
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.outwardSibling_constitutionallySeparated_of_rigid
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.exists_outwardSibling_trees_of_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.outwardSibling_rule1b_eq_of_tie
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.outwardSibling_separated_of_rigidTarget
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.outwardSiblings_separated_of_rigidTarget
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.ligandRootSiblingPair
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.nonempty_ligandRoot_residualPathTreeEquiv
assert_kernel_only TetraStereo.OneCenter.LocalizedActualBoundaryObservationReadback.ligandRoots_separated_of_rigid
