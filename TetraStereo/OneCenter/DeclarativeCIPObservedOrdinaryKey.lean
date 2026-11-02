import TetraStereo.OneCenter.DeclarativeCIPContextualConstitutional
import TetraStereo.OneCenter.DeclarativeCIPOrdinaryCanonicalAddressing
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! The independent eight-rule key with explicit constitutional observations.
All stereochemical evidence and its comparison meaning are unchanged. Only the constitutional
observer is a parameter, so auxiliary keys can retain their outer root. All eight columns still
share the recursively sorted sibling layout. -/

namespace TetraStereo.OneCenter.DeclarativeCIP
open Certificate.CanonicalSphereKey (Key assemble sortDesc WellShaped)
noncomputable section
open scoped Classical
universe u
variable {Atom : Type u}
  (graph : RootedDigraph Atom)
  (observe : ConstitutionalRule → graph.Node → ℤ)
  (evidence : StereochemicalEvidence graph)
local instance observedOrdinaryNodeFintype : Fintype graph.Node := graph.nodeFintype

/-- **The ordinary key.**  Children are ranked by their ordinary keys in descending lexicographic
order: first by the constitutional vector, then by the stereochemical vector.  All eight
components are laid out over that one ranking. -/
noncomputable def ordinaryKeyWithObservations (W D : ℕ) (node : graph.Node) : OrdinaryKey :=
  let ranked := sortDesc ((graph.childList node).attach.map fun child => ordinaryKeyWithObservations W D child.1)
  toLex
    ([ruleComponentWithObservations graph W D observe .rule1aAtomicNumber node (constitutionalProjection ranked),
      ruleComponentWithObservations graph W D observe .rule1bDuplicateNodeProximity node
        (constitutionalProjection ranked),
      ruleComponentWithObservations graph W D observe .rule2AtomicMass node (constitutionalProjection ranked)],
     [stereoComponent graph evidence W D .rule3DoubleBondGeometry node ranked,
      stereoComponent graph evidence W D .rule4aStereogenicUnitKind node ranked,
      stereoComponent graph evidence W D .rule4bLikeUnlikeDescriptorPairs node ranked,
      stereoComponent graph evidence W D .rule4cPseudoasymmetricDescriptor node ranked,
      stereoComponent graph evidence W D .rule5EnantiomorphicDescriptor node ranked])
termination_by graph.height + 1 - graph.depth node
decreasing_by
  have hchild := (graph.mem_childList).1 child.2
  have hdepth := graph.child_depth hchild
  have hle := graph.depth_le_height child.1
  omega

/-- The ranked ordinary keys of the children of a node. -/
def rankedOrdinaryKeysWithObservations (W D : ℕ) (node : graph.Node) : List OrdinaryKey :=
  sortDesc ((graph.childList node).map (ordinaryKeyWithObservations graph observe evidence W D))

theorem ordinaryKeyWithObservations_eq (W D : ℕ) (node : graph.Node) :
    ordinaryKeyWithObservations graph observe evidence W D node =
      toLex
        ([ruleComponentWithObservations graph W D observe .rule1aAtomicNumber node
            (constitutionalProjection (rankedOrdinaryKeysWithObservations graph observe evidence W D node)),
          ruleComponentWithObservations graph W D observe .rule1bDuplicateNodeProximity node
            (constitutionalProjection (rankedOrdinaryKeysWithObservations graph observe evidence W D node)),
          ruleComponentWithObservations graph W D observe .rule2AtomicMass node
            (constitutionalProjection (rankedOrdinaryKeysWithObservations graph observe evidence W D node))],
         [stereoComponent graph evidence W D .rule3DoubleBondGeometry node
            (rankedOrdinaryKeysWithObservations graph observe evidence W D node),
          stereoComponent graph evidence W D .rule4aStereogenicUnitKind node
            (rankedOrdinaryKeysWithObservations graph observe evidence W D node),
          stereoComponent graph evidence W D .rule4bLikeUnlikeDescriptorPairs node
            (rankedOrdinaryKeysWithObservations graph observe evidence W D node),
          stereoComponent graph evidence W D .rule4cPseudoasymmetricDescriptor node
            (rankedOrdinaryKeysWithObservations graph observe evidence W D node),
          stereoComponent graph evidence W D .rule5EnantiomorphicDescriptor node
            (rankedOrdinaryKeysWithObservations graph observe evidence W D node)]) := by
  rw [ordinaryKeyWithObservations]
  simp only [List.attach_map_val, rankedOrdinaryKeysWithObservations]

theorem ordinaryKeyWithObservations_stereo_getD (W D : ℕ) (rule : StereochemicalRule) (node : graph.Node) :
    (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD (stereoIndex rule) [] =
      stereoComponent graph evidence W D rule node
        (rankedOrdinaryKeysWithObservations graph observe evidence W D node) := by
  rw [ordinaryKeyWithObservations_eq]
  cases rule <;> rfl

/-- **Compatibility.**  The constitutional half of the ordinary key is the observer-parametric three-rule
vector key: later evidence only refines constitutional ties. -/
theorem ordinaryKeyWithObservations_fst (W D : ℕ) :
    ∀ node, (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).1 =
      ruleKeyWithObservations graph W D observe node := by
  intro node
  refine node_induction graph (motive := fun node =>
    (ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).1 = ruleKeyWithObservations graph W D observe node)
    ?_ node
  intro node ih
  have hproj : constitutionalProjection (rankedOrdinaryKeysWithObservations graph observe evidence W D node) =
      sortDesc ((graph.childList node).map (ruleKeyWithObservations graph W D observe)) := by
    have hperm : (constitutionalProjection (rankedOrdinaryKeysWithObservations graph observe evidence W D node)).Perm
        ((graph.childList node).map (ruleKeyWithObservations graph W D observe)) := by
      unfold constitutionalProjection rankedOrdinaryKeysWithObservations
      refine ((Certificate.CanonicalSphereKey.sortDesc_perm _).map _).trans ?_
      rw [List.map_map]
      exact List.Perm.of_eq (List.map_congr_left fun child hchild =>
        ih child ((graph.mem_childList).1 hchild))
    have hsorted : (constitutionalProjection
        (rankedOrdinaryKeysWithObservations graph observe evidence W D node)).Pairwise fun x y => y ≤ x := by
      unfold constitutionalProjection
      rw [List.pairwise_map]
      exact (Certificate.CanonicalSphereKey.sortDesc_pairwise _).imp fun h => fst_le_of_le h
    rw [Certificate.CanonicalSphereKey.sortDesc_eq_of_perm hperm.symm,
      Certificate.CanonicalSphereKey.sortDesc_of_pairwise hsorted]
  rw [ordinaryKeyWithObservations_eq, ruleKeyWithObservations_eq, ofLex_toLex, hproj]

theorem ordinaryKeyWithObservations_stereo_wellShaped (W D : ℕ) (rule : StereochemicalRule) :
    ∀ node, WellShaped W D
      ((ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD (stereoIndex rule) []) := by
  intro node
  revert rule
  refine node_induction graph (motive := fun node => ∀ rule, WellShaped W D
    ((ofLex (ordinaryKeyWithObservations graph observe evidence W D node)).2.getD (stereoIndex rule) [])) ?_ node
  intro node ih rule
  rw [ordinaryKeyWithObservations_stereo_getD]
  apply Certificate.CanonicalSphereKey.assemble_wellShaped
  intro key hkey
  obtain ⟨vector, hvector, rfl⟩ := List.mem_map.1 hkey
  obtain ⟨child, hchild, rfl⟩ :=
    List.mem_map.1 (Certificate.CanonicalSphereKey.sortDesc_mem hvector)
  exact ih child ((graph.mem_childList).1 hchild) rule

/-- Changing no constitutional observations changes none of the eight recursively ordered columns. -/
theorem ordinaryKeyWithObservations_congr
    (other : ConstitutionalRule → graph.Node → ℤ)
    (same : ∀ rule node, observe rule node = other rule node) (W D : Nat) :
    ∀ node, ordinaryKeyWithObservations graph observe evidence W D node =
      ordinaryKeyWithObservations graph other evidence W D node := by
  refine node_induction graph (motive := fun node =>
    ordinaryKeyWithObservations graph observe evidence W D node =
      ordinaryKeyWithObservations graph other evidence W D node) ?_
  intro node ih
  have children : rankedOrdinaryKeysWithObservations graph observe evidence W D node =
      rankedOrdinaryKeysWithObservations graph other evidence W D node := by
    unfold rankedOrdinaryKeysWithObservations
    congr 1
    apply List.map_congr_left
    intro child present
    exact ih child ((graph.mem_childList).1 present)
  rw [ordinaryKeyWithObservations_eq, ordinaryKeyWithObservations_eq, children]
  simp only [ruleComponentWithObservations, same]

/-- At the established constitutional observer this construction is exactly the established
eight-rule key, including its recursively ranked stereochemical columns. -/
theorem ordinaryKeyWithObservations_eq_ordinaryKey [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom) (W D : Nat) :
    ∀ node, ordinaryKeyWithObservations graph (nodeObservation molecule graph) evidence W D node =
      ordinaryKey molecule graph evidence W D node := by
  refine node_induction graph (motive := fun node =>
    ordinaryKeyWithObservations graph (nodeObservation molecule graph) evidence W D node =
      ordinaryKey molecule graph evidence W D node) ?_
  intro node ih
  have children : rankedOrdinaryKeysWithObservations graph (nodeObservation molecule graph)
      evidence W D node = rankedOrdinaryKeys molecule graph evidence W D node := by
    unfold rankedOrdinaryKeysWithObservations rankedOrdinaryKeys
    congr 1
    apply List.map_congr_left
    intro child present
    exact ih child ((graph.mem_childList).1 present)
  rw [ordinaryKeyWithObservations_eq, ordinaryKey_eq, children]
  rfl

/-- Independent ordinary key for the retained outer-root profile. -/
def contextualOrdinaryKey [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom) (outerRoot : Atom)
    (W D : Nat) (node : graph.Node) : OrdinaryKey :=
  ordinaryKeyWithObservations graph (contextualNodeObservation molecule graph outerRoot)
    evidence W D node

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKeyWithObservations
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKeyWithObservations_fst
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKeyWithObservations_stereo_wellShaped
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKeyWithObservations_congr
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ordinaryKeyWithObservations_eq_ordinaryKey
