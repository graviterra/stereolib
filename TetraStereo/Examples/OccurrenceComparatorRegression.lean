import TetraStereo.OneCenter.ProductionCIPOccurrenceDescriptorComparatorLaws

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

/-! # Occurrence-comparator regressions

These computational kernel checks are intentionally kept out of the production comparator module.
They preserve the adversarial witnesses which motivated intrinsic terminal padding and the exact,
real-node automorphism frame gate. -/

namespace CursorTerminalPaddingRegression

private def carbon : AtomSpec := AtomSpec.aliphatic Element.C
private def wildcard : AtomSpec := AtomSpec.aliphatic Element.wildcard

private def molecule : RawMolecule where
  atoms := [carbon, carbon, wildcard]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single } ]

private def shortLeafNode : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 1, history := [0, 1, 1, 1, 1],
    provenance := .multipleBondDuplicate 5 }

private def longLeafNode : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 1, history := [0, 1, 1, 1, 1, 1, 1],
    provenance := .multipleBondDuplicate 5 }

private def realNode : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 1, history := [0, 1, 1, 1, 1, 1],
    provenance := .realAtom }

private def realPrevious : RawMolecule.CanonicalBranchNode :=
  { atom := 1, parent := 1, history := [1, 1, 1, 1, 1],
    provenance := .realAtom }

private def shortLeaf : CanonicalRerootCursor := { node := shortLeafNode }
private def longLeaf : CanonicalRerootCursor := { node := longLeafNode }
private def realBranch : CanonicalRerootCursor :=
  { node := realNode, previous? := some realPrevious }

theorem terminal_tie_is_congruent_against_nonterminal :
    compareCursorBranchAt molecule 1 .rule2 shortLeaf longLeaf = some .eq ∧
      compareCursorBranchAt molecule 1 .rule2 shortLeaf realBranch = some .lt ∧
      compareCursorBranchAt molecule 1 .rule2 longLeaf realBranch = some .lt := by
  decide

end CursorTerminalPaddingRegression

namespace OccurrenceAutomorphismFrameRegression

private def carbon : AtomSpec := AtomSpec.aliphatic Element.C

private def singleBond (left right : ℕ) : RawBond :=
  { source := left, target := right, kind := .single }

/-- Two constitutionally symmetric cyclic ligands at atom 0, with symmetric pendant atoms 4 and 8.
The pendant atom 4 supplies the deliberately malformed incoming frame below. -/
private def molecule : RawMolecule where
  atoms := List.replicate 9 carbon
  bonds :=
    [ singleBond 0 1, singleBond 0 5,
      singleBond 1 2, singleBond 2 3, singleBond 3 1,
      singleBond 5 6, singleBond 6 7, singleBond 7 5,
      singleBond 2 4, singleBond 6 8 ]

private def centerRoot : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 0, history := [0], provenance := .realAtom }

/-- This is not the incoming node of the right ligand. It deliberately copies `centerRoot`'s
legacy key while retaining a different physical atom. -/
private def malformedRootWithCollidingKey : RawMolecule.CanonicalBranchNode :=
  { atom := 4, parent := 4, history := [0], provenance := .realAtom }

private def leftCursor : CanonicalRerootCursor :=
  { node := RawMolecule.canonicalRoot 0 1, previous? := some centerRoot }

private def malformedRightCursor : CanonicalRerootCursor :=
  { node := RawMolecule.canonicalRoot 0 5,
    previous? := some malformedRootWithCollidingKey }

theorem legacy_keys_collide :
    canonicalOccurrenceKey centerRoot = canonicalOccurrenceKey malformedRootWithCollidingKey := by
  decide

/-- Before exact-frame validation this orientation was changed from constitutional `lt` to `eq` by
an automorphism fixing atom 0. The malformed right cursor now fails closed at the frame gate and the
complete occurrence comparator retains its compiled strict decision. -/
theorem malformed_equal_key_pair_no_longer_ties :
    (compareOccurrenceBranches? molecule [] 20 leftCursor malformedRightCursor).map
      OccurrenceComparison.ordering = some Ordering.lt := by
  decide

theorem malformed_equal_key_reverse_no_longer_uses_other_center :
    (compareOccurrenceBranches? molecule [] 20 malformedRightCursor leftCursor).map
      OccurrenceComparison.ordering = some Ordering.gt := by
  decide

end OccurrenceAutomorphismFrameRegression

namespace OccurrenceAutomorphismProvenanceRegression

private def carbon : AtomSpec := AtomSpec.aliphatic Element.C

private def bond (kind : ParsedBondKind) (left right : ℕ) : RawBond :=
  { source := left, target := right, kind := kind }

/-- The root has symmetric double-bonded cyclic arms and a generated two-carbon comparison arm.
Each double bond contributes both a real child and a multiple-bond duplicate to the exact canonical
neighbor family. -/
private def molecule : RawMolecule where
  atoms := List.replicate 11 carbon
  bonds :=
    [ bond .double 0 1, bond .double 0 5,
      bond .single 1 2, bond .single 2 3, bond .single 3 1,
      bond .single 5 6, bond .single 6 7, bond .single 7 5,
      bond .single 2 4, bond .single 6 8,
      bond .single 0 9, bond .single 9 10 ]

private def commonRoot : RawMolecule.CanonicalBranchNode :=
  { atom := 0, parent := 0, history := [0], provenance := .realAtom }

private def realCyclicNode : RawMolecule.CanonicalBranchNode :=
  { atom := 1, parent := 0, history := [1, 0], provenance := .realAtom }

private def duplicateCyclicNode : RawMolecule.CanonicalBranchNode :=
  { atom := 5, parent := 0, history := [5, 0], provenance := .multipleBondDuplicate 0 }

private def middleChainNode : RawMolecule.CanonicalBranchNode :=
  { atom := 9, parent := 0, history := [9, 0], provenance := .realAtom }

private def senior : CanonicalRerootCursor :=
  { node := realCyclicNode, previous? := some commonRoot }

private def junior : CanonicalRerootCursor :=
  { node := duplicateCyclicNode, previous? := some commonRoot }

private def middle : CanonicalRerootCursor :=
  { node := middleChainNode, previous? := some commonRoot }

theorem all_three_nodes_are_exact_generated_neighbors :
    senior.node ∈ (({ node := commonRoot } : CanonicalRerootCursor).neighbors molecule) ∧
      middle.node ∈ (({ node := commonRoot } : CanonicalRerootCursor).neighbors molecule) ∧
      junior.node ∈ (({ node := commonRoot } : CanonicalRerootCursor).neighbors molecule) := by
  decide

theorem atom_automorphism_exists_but_duplicate_override_is_rejected :
    molecule.hasConstitutionAutomorphismSwapping commonRoot.atom senior.node.atom junior.node.atom =
        true ∧
      occurrenceRootsProvedAutomorphic molecule 20 senior junior Ordering.gt = false := by
  decide

private def ordering? (left right : CanonicalRerootCursor) : Option Ordering :=
  (compareOccurrenceBranches? molecule [] 20 left right).map OccurrenceComparison.ordering

/-- The formerly tied real/duplicate pair now retains its strict constitutional order. -/
theorem real_duplicate_pair_no_longer_ties :
    ordering? senior junior = some Ordering.gt := by
  decide

/-- The repaired results form the strict composable chain `senior > middle > junior`, whose endpoint
is the retained real-versus-duplicate decision. -/
theorem repaired_generated_triple_is_transitive :
    ordering? senior middle = some Ordering.gt ∧
      ordering? middle junior = some Ordering.gt ∧
      ordering? senior junior = some Ordering.gt := by
  decide

end OccurrenceAutomorphismProvenanceRegression

namespace RerootDepthAutomorphismConflictRegression

private def carbon : AtomSpec := AtomSpec.aliphatic Element.C

private def singleBond (left right : ℕ) : RawBond :=
  { source := left, target := right, kind := .single }

/-- Atom 1 is an inner re-rooted occurrence reached from cyclic arm 0.  Arms 0, 2, and 7
are constitutionally identical disjoint carbon triangles, so constitution automorphisms fixing
atom 1 permute them. -/
private def molecule : RawMolecule where
  atoms := List.replicate 10 carbon
  bonds :=
    [ singleBond 1 0, singleBond 0 3, singleBond 3 4, singleBond 4 0,
      singleBond 1 2, singleBond 2 5, singleBond 5 6, singleBond 6 2,
      singleBond 1 7, singleBond 7 8, singleBond 8 9, singleBond 9 7 ]

private def innerRoot : RawMolecule.CanonicalBranchNode :=
  { atom := 1, parent := 0, history := [1, 0], provenance := .realAtom }

private def oldParent : CanonicalRerootCursor :=
  { node := { atom := 0, parent := 0, history := [0], provenance := .realAtom },
    previous? := some innerRoot }

private def newChild : CanonicalRerootCursor :=
  { node := { atom := 2, parent := 1, history := [2, 1, 0], provenance := .realAtom },
    previous? := some innerRoot }

private def thirdChild : CanonicalRerootCursor :=
  { node := { atom := 7, parent := 1, history := [7, 1, 0], provenance := .realAtom },
    previous? := some innerRoot }

/-- All three cursors are exact physical real-atom members of the production re-rooted sibling
frame.  This is not a forged-history or duplicate-provenance example. -/
theorem exact_generated_real_sibling_frame :
    ({ node := innerRoot } : CanonicalRerootCursor).neighbors molecule =
        [oldParent.node, newChild.node, thirdChild.node] ∧
      oldParent.node.provenance = .realAtom ∧
      newChild.node.provenance = .realAtom ∧
      thirdChild.node.provenance = .realAtom := by
  decide

/-- The old parent and both new children are cyclic, the re-rooted center is acyclic, and an exact
constitution automorphism fixing the center exchanges the old parent with either child. -/
theorem exact_automorphism_frame :
    molecule.atomLiesInCycle 12 oldParent.node.atom = true ∧
      molecule.atomLiesInCycle 12 newChild.node.atom = true ∧
      molecule.atomLiesInCycle 12 thirdChild.node.atom = true ∧
      molecule.atomLiesInCycle 12 innerRoot.atom = false ∧
      molecule.hasConstitutionAutomorphismSwapping innerRoot.atom
        oldParent.node.atom newChild.node.atom = true ∧
      molecule.hasConstitutionAutomorphismSwapping innerRoot.atom
        oldParent.node.atom thirdChild.node.atom = true := by
  decide

/-- The two outward children carry the same occurrence-relative history depth and raw-tie. -/
theorem raw_new_children_tie :
    compareCursorBranchAt molecule 12 .rule2 newChild thirdChild = some .eq := by
  decide

/-- The physically automorphic old-parent/new-child pair receives a strict raw Rule-1b result
because their inherited canonical histories have depths 0 and 2.  The exact production gate
recognizes that strict result as a constitutional conflict. -/
theorem raw_strict_automorphism_conflict :
    compareCursorBranchAt molecule 12 .rule2 oldParent newChild = some .gt ∧
      occurrenceRootsProvedAutomorphic molecule 12 oldParent newChild .gt = true := by
  decide

/-- Production is conservative on the witnessed raw/symmetry disagreement: it refuses the
constitutional stage instead of manufacturing a tie from one selected sibling representation. -/
theorem certified_stage_refuses_strict_automorphism_conflict :
    certifiedConstitutionalStage? molecule 12 oldParent newChild = none := by
  decide

/-- The complete occurrence comparator propagates the certified constitutional refusal and cannot
silently fall through to Rules 4a--5 on the disputed pair. -/
theorem occurrence_comparator_propagates_strict_automorphism_refusal :
    compareOccurrenceBranches? molecule [] 12 oldParent newChild = none := by
  decide

end RerootDepthAutomorphismConflictRegression

namespace FailClosedEndpointSuccessRegression

open ProductionCIPOccurrenceDescriptorComparatorLaws

/-- The strong endpoint-closure property which would eliminate the third-success premise from the
production composition theorem. -/
def TwoSuccessEndpointClosure (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : Nat) : Prop :=
  ∀ (left middle right : CanonicalRerootCursor)
    (leftMiddle middleRight : OccurrenceComparison) (composed : Ordering),
    compareOccurrenceBranches? mol state fuel left middle = some leftMiddle →
    compareOccurrenceBranches? mol state fuel middle right = some middleRight →
    composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering = some composed →
    ∃ leftRight,
      compareOccurrenceBranches? mol state fuel left right = some leftRight ∧
        leftRight.ordering = composed

private def carbon : AtomSpec := AtomSpec.aliphatic Element.C

private def singleBond (left right : Nat) : RawBond :=
  { source := left, target := right, kind := .single }

/-- The minimal simple-graph frame used here has one acyclic atom joining two disjoint carbon
triangles.  The two triangle roots are exchanged by an exact center-fixing automorphism. -/
private def molecule : RawMolecule where
  atoms := List.replicate 7 carbon
  bonds :=
    [ singleBond 1 0, singleBond 0 3, singleBond 3 4, singleBond 4 0,
      singleBond 1 2, singleBond 2 5, singleBond 5 6, singleBond 6 2 ]

private def innerRoot : RawMolecule.CanonicalBranchNode :=
  { atom := 1, parent := 0, history := [1, 0], provenance := .realAtom }

private def shortRoot : RawMolecule.CanonicalBranchNode :=
  { atom := 1, parent := 1, history := [1], provenance := .realAtom }

private def left : CanonicalRerootCursor :=
  { node := { atom := 0, parent := 0, history := [0], provenance := .realAtom },
    previous? := some innerRoot }

/-- The middle cursor is the same physical arm as `right`, but in a different incoming history
frame.  Arbitrary-cursor endpoint closure must cover it if it is claimed without locality premises. -/
private def middle : CanonicalRerootCursor :=
  { node := { atom := 2, parent := 1, history := [2, 1], provenance := .realAtom },
    previous? := some shortRoot }

private def right : CanonicalRerootCursor :=
  { node := { atom := 2, parent := 1, history := [2, 1, 0], provenance := .realAtom },
    previous? := some innerRoot }

/-- Both legs and the endpoint have the same strict raw decision.  Only the exact-frame endpoint
activates the conservative automorphism-conflict gate. -/
theorem raw_chain_with_exact_frame_endpoint_conflict :
    compareCursorBranchAt molecule 3 .rule2 left middle = some .gt ∧
      compareCursorBranchAt molecule 3 .rule2 middle right = some .gt ∧
      compareCursorBranchAt molecule 3 .rule2 left right = some .gt ∧
      occurrenceRootsProvedAutomorphic molecule 3 left middle .gt = false ∧
      occurrenceRootsProvedAutomorphic molecule 3 middle right .gt = false ∧
      occurrenceRootsProvedAutomorphic molecule 3 left right .gt = true := by
  decide

/-- Actual production has two composable successful legs but refuses their endpoint. -/
theorem actual_two_success_legs_and_refused_endpoint :
    compareOccurrenceBranches? molecule [] 3 left middle = some { ordering := .gt } ∧
      compareOccurrenceBranches? molecule [] 3 middle right = some { ordering := .gt } ∧
      composeSuccessfulOrdering? .gt .gt = some .gt ∧
      compareOccurrenceBranches? molecule [] 3 left right = none := by
  decide

/-- Therefore the actual fail-closed comparator is not endpoint-success closed after only two
successful composable calls; the third-success premise in the production theorem is necessary. -/
theorem actual_comparator_not_two_success_endpoint_closed :
    ¬ TwoSuccessEndpointClosure molecule [] 3 := by
  intro closure
  have leftMiddleEq :
      compareOccurrenceBranches? molecule [] 3 left middle = some { ordering := .gt } := by
    decide
  have middleRightEq :
      compareOccurrenceBranches? molecule [] 3 middle right = some { ordering := .gt } := by
    decide
  have compositionEq : composeSuccessfulOrdering? .gt .gt = some .gt := by
    decide
  rcases closure left middle right { ordering := .gt } { ordering := .gt } .gt
      leftMiddleEq middleRightEq compositionEq with ⟨leftRight, endpointEq, _⟩
  have refused : compareOccurrenceBranches? molecule [] 3 left right = none := by
    decide
  rw [refused] at endpointEq
  contradiction

end FailClosedEndpointSuccessRegression

namespace SameFrameFailClosedEndpointSuccessRegression

open ProductionCIPOccurrenceDescriptorComparatorLaws

private def wildcard : AtomSpec := AtomSpec.aliphatic Element.wildcard

private def bond (kind : ParsedBondKind) (left right : Nat) : RawBond :=
  { source := left, target := right, kind := kind }

/-- An acyclic center joins two constitutionally symmetric wildcard triangles by symmetric written
double bonds.  Wildcard Rule-1a labels are zero, so real and phantom-padded spheres remain tied and
the generated Rule-1b distances control the raw comparisons. -/
private def molecule : RawMolecule where
  atoms := List.replicate 7 wildcard
  bonds :=
    [ bond .double 1 0, bond .single 0 3, bond .single 3 4, bond .single 4 0,
      bond .double 1 2, bond .single 2 5, bond .single 5 6, bond .single 6 2 ]

private def innerRoot : RawMolecule.CanonicalBranchNode :=
  { atom := 1, parent := 0, history := [1, 0], provenance := .realAtom }

/-- Exact old-parent cursor in the rerooted frame, at Rule-1b distance zero. -/
private def left : CanonicalRerootCursor :=
  { node := { atom := 0, parent := 0, history := [0], provenance := .realAtom },
    previous? := some innerRoot }

/-- Exact multiple-bond duplicate generated from the old-parent edge, at distance one. -/
private def middle : CanonicalRerootCursor :=
  { node :=
      { atom := 0, parent := 1, history := [0, 1, 0],
        provenance := .multipleBondDuplicate 1 },
    previous? := some innerRoot }

/-- Exact opposite real child in the same rerooted frame, at Rule-1b distance two. -/
private def right : CanonicalRerootCursor :=
  { node := { atom := 2, parent := 1, history := [2, 1, 0], provenance := .realAtom },
    previous? := some innerRoot }

/-- All three operands have the same exact incoming cursor and are literal members of its generated
production neighbor family. -/
theorem all_three_share_one_exact_generated_frame :
    left.previous? = some innerRoot ∧ middle.previous? = some innerRoot ∧
      right.previous? = some innerRoot ∧
      left.node ∈ (({ node := innerRoot } : CanonicalRerootCursor).neighbors molecule) ∧
      middle.node ∈ (({ node := innerRoot } : CanonicalRerootCursor).neighbors molecule) ∧
      right.node ∈ (({ node := innerRoot } : CanonicalRerootCursor).neighbors molecule) := by
  decide

theorem generated_rule1b_distance_chain :
    left.node.rule1bRootDistance = 0 ∧ middle.node.rule1bRootDistance = 1 ∧
      right.node.rule1bRootDistance = 2 := by
  decide

/-- Raw comparison is the composable strict chain `0 > 1 > 2`.  The fail-closed gate rejects only
the endpoint: its two real cyclic roots are automorphic, while each leg contains the generated
multiple-bond duplicate and therefore cannot activate the real-node gate. -/
theorem raw_chain_with_same_exact_frame_endpoint_conflict :
    compareCursorBranchAt molecule 3 .rule2 left middle = some .gt ∧
      compareCursorBranchAt molecule 3 .rule2 middle right = some .gt ∧
      compareCursorBranchAt molecule 3 .rule2 left right = some .gt ∧
      occurrenceRootsProvedAutomorphic molecule 3 left middle .gt = false ∧
      occurrenceRootsProvedAutomorphic molecule 3 middle right .gt = false ∧
      occurrenceRootsProvedAutomorphic molecule 3 left right .gt = true := by
  decide

/-- Even one exact generated sibling frame does not make the fail-closed production comparator
endpoint-success closed after two composable calls. -/
theorem actual_two_success_legs_and_refused_same_frame_endpoint :
    compareOccurrenceBranches? molecule [] 3 left middle = some { ordering := .gt } ∧
      compareOccurrenceBranches? molecule [] 3 middle right = some { ordering := .gt } ∧
      composeSuccessfulOrdering? .gt .gt = some .gt ∧
      compareOccurrenceBranches? molecule [] 3 left right = none := by
  decide

theorem common_exact_generated_frame_does_not_rescue_two_success_endpoint_closure :
    ¬ FailClosedEndpointSuccessRegression.TwoSuccessEndpointClosure molecule [] 3 := by
  intro closure
  have leftMiddleEq :
      compareOccurrenceBranches? molecule [] 3 left middle = some { ordering := .gt } := by
    decide
  have middleRightEq :
      compareOccurrenceBranches? molecule [] 3 middle right = some { ordering := .gt } := by
    decide
  have compositionEq : composeSuccessfulOrdering? .gt .gt = some .gt := by
    decide
  rcases closure left middle right { ordering := .gt } { ordering := .gt } .gt
      leftMiddleEq middleRightEq compositionEq with ⟨leftRight, endpointEq, _⟩
  have refused : compareOccurrenceBranches? molecule [] 3 left right = none := by
    decide
  rw [refused] at endpointEq
  contradiction

end SameFrameFailClosedEndpointSuccessRegression

namespace SameFrameRealFailClosedEndpointSuccessRegression

open ProductionCIPOccurrenceDescriptorComparatorLaws

/-- The proposed narrower domain: three physical cursors generated as siblings from one exact
incoming reroot node. -/
def ExactGeneratedRealSiblingTriple (mol : RawMolecule)
    (left middle right : CanonicalRerootCursor) : Prop :=
  ∃ root,
    left.previous? = some root ∧ middle.previous? = some root ∧
      right.previous? = some root ∧
      left.node ∈ (({ node := root } : CanonicalRerootCursor).neighbors mol) ∧
      middle.node ∈ (({ node := root } : CanonicalRerootCursor).neighbors mol) ∧
      right.node ∈ (({ node := root } : CanonicalRerootCursor).neighbors mol) ∧
      left.node.provenance = .realAtom ∧ middle.node.provenance = .realAtom ∧
      right.node.provenance = .realAtom

/-- Two-success endpoint closure restricted to exact generated physical sibling triples. -/
def RealSiblingTwoSuccessEndpointClosure (mol : RawMolecule) (state : OccurrenceAuxState)
    (fuel : Nat) : Prop :=
  ∀ (left middle right : CanonicalRerootCursor)
    (leftMiddle middleRight : OccurrenceComparison) (composed : Ordering),
    ExactGeneratedRealSiblingTriple mol left middle right →
    compareOccurrenceBranches? mol state fuel left middle = some leftMiddle →
    compareOccurrenceBranches? mol state fuel middle right = some middleRight →
    composeSuccessfulOrdering? leftMiddle.ordering middleRight.ordering = some composed →
    ∃ leftRight,
      compareOccurrenceBranches? mol state fuel left right = some leftRight ∧
        leftRight.ordering = composed

private def wildcard : AtomSpec := AtomSpec.aliphatic Element.wildcard

private def bond (kind : ParsedBondKind) (left right : Nat) : RawBond :=
  { source := left, target := right, kind := kind }

/-- An acyclic root has three physical arms.  The old-parent and right arms are symmetric wildcard
triangles.  The middle arm is a constitutionally different acyclic wildcard double-bond arm.
Wildcard Rule-1a labels keep the three raw traversals tied until Rule 1b. -/
private def molecule : RawMolecule where
  atoms := List.replicate 9 wildcard
  bonds :=
    [ bond .single 1 0, bond .single 0 3, bond .single 3 4, bond .single 4 0,
      bond .single 1 2, bond .single 2 5, bond .single 5 6, bond .single 6 2,
      bond .single 1 7, bond .double 7 8 ]

private def innerRoot : RawMolecule.CanonicalBranchNode :=
  { atom := 1, parent := 0, history := [1, 0], provenance := .realAtom }

/-- Exact real old-parent sibling, with Rule-1b root distance zero. -/
private def left : CanonicalRerootCursor :=
  { node := { atom := 0, parent := 0, history := [0], provenance := .realAtom },
    previous? := some innerRoot }

/-- Exact real child whose internal written double bond gives it a senior Rule-1b duplicate. -/
private def middle : CanonicalRerootCursor :=
  { node := { atom := 7, parent := 1, history := [7, 1, 0], provenance := .realAtom },
    previous? := some innerRoot }

/-- Exact real cyclic child constitutionally symmetric to the old-parent arm. -/
private def right : CanonicalRerootCursor :=
  { node := { atom := 2, parent := 1, history := [2, 1, 0], provenance := .realAtom },
    previous? := some innerRoot }

/-- The counterexample satisfies the proposed narrower domain, including physical provenance and
literal membership in one generated sibling list.  Its operands are also pairwise distinct. -/
theorem all_three_are_distinct_exact_generated_real_siblings :
    ExactGeneratedRealSiblingTriple molecule left middle right ∧
      left ≠ middle ∧ middle ≠ right ∧ left ≠ right := by
  constructor
  · refine ⟨innerRoot, ?_⟩
    decide
  · decide

/-- The old-parent history makes `left > middle`; the middle arm's multiple-bond duplicate makes
`middle > right`.  Only the symmetric cyclic endpoint activates the real-node conflict gate. -/
theorem raw_chain_with_real_same_frame_endpoint_conflict :
    compareCursorBranchAt molecule 6 .rule2 left middle = some .gt ∧
      compareCursorBranchAt molecule 6 .rule2 middle right = some .gt ∧
      compareCursorBranchAt molecule 6 .rule2 left right = some .gt ∧
      occurrenceRootsProvedAutomorphic molecule 6 left middle .gt = false ∧
      occurrenceRootsProvedAutomorphic molecule 6 middle right .gt = false ∧
      occurrenceRootsProvedAutomorphic molecule 6 left right .gt = true := by
  decide

/-- Both composable legs succeed for physical real siblings, but their physical real endpoint is
refused by the production comparator. -/
theorem actual_two_success_real_sibling_legs_and_refused_endpoint :
    compareOccurrenceBranches? molecule [] 6 left middle = some { ordering := .gt } ∧
      compareOccurrenceBranches? molecule [] 6 middle right = some { ordering := .gt } ∧
      composeSuccessfulOrdering? .gt .gt = some .gt ∧
      compareOccurrenceBranches? molecule [] 6 left right = none := by
  decide

/-- Exact generated-frame membership and physical `realAtom` provenance still do not make the
optional production comparator endpoint-closed after two successful composable calls. -/
theorem exact_generated_real_frame_does_not_rescue_two_success_endpoint_closure :
    ¬ RealSiblingTwoSuccessEndpointClosure molecule [] 6 := by
  intro closure
  have frame : ExactGeneratedRealSiblingTriple molecule left middle right := by
    refine ⟨innerRoot, ?_⟩
    decide
  have leftMiddleEq :
      compareOccurrenceBranches? molecule [] 6 left middle = some { ordering := .gt } := by
    decide
  have middleRightEq :
      compareOccurrenceBranches? molecule [] 6 middle right = some { ordering := .gt } := by
    decide
  have compositionEq : composeSuccessfulOrdering? .gt .gt = some .gt := by
    decide
  rcases closure left middle right { ordering := .gt } { ordering := .gt } .gt
      frame leftMiddleEq middleRightEq compositionEq with ⟨leftRight, endpointEq, _⟩
  have refused : compareOccurrenceBranches? molecule [] 6 left right = none := by
    decide
  rw [refused] at endpointEq
  contradiction

end SameFrameRealFailClosedEndpointSuccessRegression

end OneCenter
end TetraStereo
