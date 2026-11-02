import TetraStereo.OneCenter.CIPAuthoritativeRule1aSoundness

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open DeclarativeCIP

namespace DeclarativeCIP

/-- Executable natural comparison is exactly the independent higher-mass relational outcome. -/
theorem compare_eq_iff_descendingNatOutcome (left right : ℕ) (outcome : Ordering) :
    compare left right = outcome ↔ DescendingNatOutcome left right outcome := by
  cases outcome with
  | lt =>
      exact ⟨fun compared => .lt (Nat.compare_eq_lt.mp compared),
        fun relation => by cases relation with | lt lower => exact Nat.compare_eq_lt.mpr lower⟩
  | eq =>
      exact ⟨fun compared => .eq (Nat.compare_eq_eq.mp compared),
        fun relation => by cases relation with | eq equal => exact Nat.compare_eq_eq.mpr equal⟩
  | gt =>
      exact ⟨fun compared => .gt (Nat.compare_eq_gt.mp compared),
        fun relation => by cases relation with | gt higher => exact Nat.compare_eq_gt.mpr higher⟩

end DeclarativeCIP

namespace RawMolecule

/-!
# Chemical soundness of authoritative Rule 2

Revised-CIP Rule 2 assigns physical isotope/ordinary mass only to real atom nodes.  Multiple-bond
and ring duplicates participate in Rules 1a and 1b but carry Rule-2 mass zero, as do atomless
phantom positions.  The executable has exactly that provenance split.  The theorems below prove
its agreement with the independent declarative hierarchy at every realized node, not only at real
atoms.
-/

/-- Rule-2 mass used by the authoritative node comparator, exposed as a unary observation. -/
def canonicalRule2Mass (mol : RawMolecule) (node : CanonicalBranchNode) : ℕ :=
  match node.provenance with
  | .realAtom => mol.atomMassAt node.atom
  | _ => 0

/-- Every realized source node's executable Rule-2 observation equals the independent declarative
observation, including the zero-mass convention for all duplicate and phantom provenance. -/
theorem CanonicalBranchKey.canonicalRule2Mass_eq_nodeAtomicMass
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.val = some source) :
    mol.canonicalRule2Mass source =
      nodeAtomicMass (mol.canonicalHierarchyMoleculeGraph center ligand)
        (some ((key.toDeclarativeDigraph mol).label node)) := by
  have coherent := key.sourceCoherent_of_root_and_childrenExact
    mol center ligand hwellFormed hroot hexact node source hsource
  change mol.canonicalRule2Mass source =
    nodeAtomicMass (mol.canonicalHierarchyMoleculeGraph center ligand)
      (some (key.declarativeLabel mol node))
  rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol node source hsource]
  cases provenanceEq : source.provenance with
  | realAtom =>
      have bound : source.atom < mol.atomCount := by
        simpa [provenanceEq] using coherent.2
      simp only [canonicalRule2Mass, provenanceEq, nodeAtomicMass,
        declarativeProvenance, atomFin?, bound]
      exact mol.atomMassAt_eq_toMoleculeGraph_atomMass source.atom bound
  | multipleBondDuplicate | ringDuplicate | phantom =>
      simp [canonicalRule2Mass, provenanceEq, nodeAtomicMass, declarativeProvenance]

/-- The executable authoritative Rule-2 node comparison is exactly the independent P-92 Rule-2
judgment at two realized hierarchy positions. -/
theorem compareCanonicalNodeRuleAuthoritative?_rule2_nodeOutcome_iff
    (mol : RawMolecule) (leftKey rightKey : CanonicalBranchKey)
    (leftCenter leftLigand rightCenter rightLigand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (leftRoot : leftKey.RootedAt leftCenter leftLigand)
    (rightRoot : rightKey.RootedAt rightCenter rightLigand)
    (leftExact : leftKey.ChildrenExact mol)
    (rightExact : rightKey.ChildrenExact mol)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (leftSource rightSource : CanonicalBranchNode)
    (leftSourceAt : leftKey.sourceNodeAtAddress? leftNode.val = some leftSource)
    (rightSourceAt : rightKey.sourceNodeAtAddress? rightNode.val = some rightSource)
    (outcome : Ordering) :
    mol.compareCanonicalNodeRuleAuthoritative? CanonicalRuleStage.rule2
        leftSource rightSource = some outcome ↔
      ConstitutionalNodeOutcome (mol.canonicalHierarchyMoleculeGraph leftCenter leftLigand)
        .rule2AtomicMass leftNode.val
        (some ((leftKey.toDeclarativeDigraph mol).label leftNode))
        (some ((rightKey.toDeclarativeDigraph mol).label rightNode)) outcome := by
  have leftMass := leftKey.canonicalRule2Mass_eq_nodeAtomicMass
    mol leftCenter leftLigand hwellFormed leftRoot leftExact leftNode leftSource leftSourceAt
  have rightMassOnRight := rightKey.canonicalRule2Mass_eq_nodeAtomicMass
    mol rightCenter rightLigand hwellFormed rightRoot rightExact rightNode rightSource rightSourceAt
  have rightMass : mol.canonicalRule2Mass rightSource =
      nodeAtomicMass (mol.canonicalHierarchyMoleculeGraph leftCenter leftLigand)
        (some ((rightKey.toDeclarativeDigraph mol).label rightNode)) := by
    rw [rightMassOnRight]
    unfold nodeAtomicMass
    cases (rightKey.toDeclarativeDigraph mol).label rightNode with
    | mk atom provenance => cases atom <;> cases provenance <;> rfl
  change some (compare (mol.canonicalRule2Mass leftSource)
      (mol.canonicalRule2Mass rightSource)) = some outcome ↔ _
  simp only [Option.some.injEq]
  unfold ConstitutionalNodeOutcome
  rw [leftMass, rightMass]
  exact compare_eq_iff_descendingNatOutcome _ _ outcome

/-- For two complete authoritative branches of the same molecular root graph, every realized
Rule-2 comparison agrees with the independent constitutional hierarchy semantics. -/
theorem branchCanonicalKeysAuthoritative_rule2_nodeOutcome_iff
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (leftComputed :
      branchCanonicalKeyAuthoritative? mol center.val leftLigand.val = some leftKey)
    (rightComputed :
      branchCanonicalKeyAuthoritative? mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (leftSource rightSource : CanonicalBranchNode)
    (leftSourceAt : leftKey.sourceNodeAtAddress? leftNode.val = some leftSource)
    (rightSourceAt : rightKey.sourceNodeAtAddress? rightNode.val = some rightSource)
    (outcome : Ordering) :
    mol.compareCanonicalNodeRuleAuthoritative? CanonicalRuleStage.rule2
        leftSource rightSource = some outcome ↔
      ConstitutionalNodeOutcome (mol.canonicalHierarchyMoleculeGraph center leftLigand)
        .rule2AtomicMass leftNode.val
        (some ((leftKey.toDeclarativeDigraph mol).label leftNode))
        (some ((rightKey.toDeclarativeDigraph mol).label rightNode)) outcome := by
  have leftStructural := mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
    center.val leftLigand.val leftKey leftComputed leftComplete
  have rightStructural := mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
    center.val rightLigand.val rightKey rightComputed rightComplete
  exact compareCanonicalNodeRuleAuthoritative?_rule2_nodeOutcome_iff
    mol leftKey rightKey center leftLigand center rightLigand admitted.1
    leftStructural.1 rightStructural.1 leftStructural.2 rightStructural.2
    leftNode rightNode leftSource rightSource leftSourceAt rightSourceAt outcome

end RawMolecule

end

end TetraStereo.OneCenter
