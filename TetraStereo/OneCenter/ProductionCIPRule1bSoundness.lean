import TetraStereo.OneCenter.ProductionCIPFaithfulAssembly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule.CanonicalBranchKey

/-!
# Production/declarative Rule-1b observation correspondence

The declarative Rule-1b observation is total and position-aware.  This module identifies it with
the exact unary root-distance code carried by every source node in a complete production
hierarchy.  Real nodes use their semantic sphere; duplicate and explicit phantom nodes retain the
payload compiled by production.
-/

/-- At every realized hierarchy node, the total declarative Rule-1b observation is exactly the
unary Rule-1b code compiled from the corresponding production source node. -/
theorem nodeRule1bRootDistance_eq_sourceCode
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source) :
    nodeRule1bRootDistance node.1
        (some ((key.toDeclarativeDigraph mol).label node)) =
      source.rule1bCode := by
  change nodeRule1bRootDistance node.1 (some (key.declarativeLabel mol node)) = _
  rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol node source hsource]
  cases hprovenance : source.provenance with
  | realAtom =>
      have hdepth := key.source_depth_eq_address_length_succ mol center ligand
        hroot hexact node source hsource
      simpa [nodeRule1bRootDistance, CanonicalBranchNode.rule1bCode,
        CanonicalBranchNode.rule1bRootDistance, hprovenance] using hdepth.symm
  | multipleBondDuplicate distance =>
      simp [nodeRule1bRootDistance, CanonicalBranchNode.rule1bCode,
        CanonicalBranchNode.rule1bRootDistance, hprovenance, declarativeProvenance]
  | ringDuplicate distance =>
      simp [nodeRule1bRootDistance, CanonicalBranchNode.rule1bCode,
        CanonicalBranchNode.rule1bRootDistance, hprovenance, declarativeProvenance]
  | phantom distance =>
      simp [nodeRule1bRootDistance, CanonicalBranchNode.rule1bCode,
        CanonicalBranchNode.rule1bRootDistance, hprovenance]

/-- The public canonical addressing presents the same observation equality. -/
theorem addressedNodeRule1bRootDistance_eq_sourceCode
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source) :
    nodeRule1bRootDistance ((key.declarativeAddressing mol).address node)
        (some ((key.toDeclarativeDigraph mol).label node)) =
      source.rule1bCode := by
  simpa using key.nodeRule1bRootDistance_eq_sourceCode mol center ligand
    hroot hexact node source hsource

end RawMolecule.CanonicalBranchKey

namespace RawMolecule

/-- The executable Rule-1b node comparator is exactly the independent total-distance relation. -/
theorem compareCanonicalNodeRule_rule1b_eq_iff
    (mol : RawMolecule) (left right : CanonicalBranchNode) (outcome : Ordering) :
    mol.compareCanonicalNodeRule CanonicalRuleStage.rule1b left right = outcome ↔
      Rule1bDistanceOutcome left.rule1bCode right.rule1bCode outcome := by
  change (if left.rule1bRootDistance < right.rule1bRootDistance then Ordering.gt
      else if right.rule1bRootDistance < left.rule1bRootDistance then Ordering.lt
      else Ordering.eq) = outcome ↔
    Rule1bDistanceOutcome left.rule1bRootDistance right.rule1bRootDistance outcome
  rcases lt_trichotomy left.rule1bRootDistance right.rule1bRootDistance with
      hlt | heq | hgt
  · have hnot : ¬right.rule1bRootDistance < left.rule1bRootDistance :=
      not_lt_of_ge hlt.le
    have hne : left.rule1bRootDistance ≠ right.rule1bRootDistance := Nat.ne_of_lt hlt
    cases outcome <;> simp [hlt, hnot, hne]
  · cases outcome <;> simp [heq]
  · have hnot : ¬left.rule1bRootDistance < right.rule1bRootDistance :=
      not_lt_of_ge hgt.le
    have hne : left.rule1bRootDistance ≠ right.rule1bRootDistance :=
      (Nat.ne_of_lt hgt).symm
    cases outcome <;> simp [hgt, hnot, hne]

end RawMolecule

namespace RawMolecule.CanonicalBranchKey

/-- At a shared semantic position, executable production Rule 1b and the declarative local Rule-1b
judgment have exactly the same outcome. -/
theorem pairedNodeRule1bOutcome_iff_production
    (mol : RawMolecule) (semanticMolecule : MoleculeGraph (Fin mol.atomCount))
    (leftKey rightKey : CanonicalBranchKey)
    (leftCenter leftLigand rightCenter rightLigand : Fin mol.atomCount)
    (hleftRoot : leftKey.RootedAt leftCenter leftLigand)
    (hrightRoot : rightKey.RootedAt rightCenter rightLigand)
    (hleftExact : leftKey.ChildrenExact mol)
    (hrightExact : rightKey.ChildrenExact mol)
    (position : List ℕ)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (hleftPosition : leftNode.1 = position) (hrightPosition : rightNode.1 = position)
    (leftSource rightSource : CanonicalBranchNode)
    (hleftSource : leftKey.sourceNodeAtAddress? leftNode.1 = some leftSource)
    (hrightSource : rightKey.sourceNodeAtAddress? rightNode.1 = some rightSource)
    (outcome : Ordering) :
    mol.compareCanonicalNodeRule CanonicalRuleStage.rule1b leftSource rightSource = outcome ↔
      ConstitutionalNodeOutcome semanticMolecule
        ConstitutionalRule.rule1bDuplicateNodeProximity position
        (some ((leftKey.toDeclarativeDigraph mol).label leftNode))
        (some ((rightKey.toDeclarativeDigraph mol).label rightNode)) outcome := by
  have hleftObservation := leftKey.nodeRule1bRootDistance_eq_sourceCode mol
    leftCenter leftLigand hleftRoot hleftExact leftNode leftSource hleftSource
  have hrightObservation := rightKey.nodeRule1bRootDistance_eq_sourceCode mol
    rightCenter rightLigand hrightRoot hrightExact rightNode rightSource hrightSource
  rw [mol.compareCanonicalNodeRule_rule1b_eq_iff leftSource rightSource outcome]
  change Rule1bDistanceOutcome leftSource.rule1bCode rightSource.rule1bCode outcome ↔ _
  rw [← hleftObservation, ← hrightObservation, hleftPosition, hrightPosition]
  rfl

end RawMolecule.CanonicalBranchKey

namespace RawMolecule

/-- A successful complete production hierarchy has correct duplicate-root distances under every
parent-preserving declarative addressing, not only under its stored positional addressing. -/
theorem branchCanonicalKey?_duplicateDistancesCorrect_all
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true) :
    ∀ addressing : (key.toDeclarativeDigraph mol).Addressing,
      RootedDigraph.DuplicateDistancesCorrect
        (key.toDeclarativeDigraph mol) center addressing := by
  have hbuild := mol.branchCanonicalKey?_completeBuild center ligand key hkey hcomplete
  have hroot : key.RootedAt center ligand := canonicalCompleteBuild_root_source hbuild
  have hexact : key.ChildrenExact mol := hbuild.childrenExact
  have hcanonical := key.duplicateDistancesCorrect_of_childrenExact
    mol center ligand hwellFormed hroot hexact
  exact RootedDigraph.duplicateDistancesCorrect_all_of_one
    (key.toDeclarativeDigraph mol) center (key.declarativeAddressing mol) hcanonical

/-- Every node emitted by a successful complete branch compilation has exact declarative and
production Rule-1b observations. -/
theorem branchCanonicalKey?_rule1bObservationExact
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true) :
    ∀ node source, key.sourceNodeAtAddress? node.1 = some source →
      nodeRule1bRootDistance ((key.declarativeAddressing mol).address node)
          (some ((key.toDeclarativeDigraph mol).label node)) =
        source.rule1bCode := by
  have hbuild := mol.branchCanonicalKey?_completeBuild center ligand key hkey hcomplete
  have hroot : key.RootedAt center ligand := canonicalCompleteBuild_root_source hbuild
  have hexact : key.ChildrenExact mol := hbuild.childrenExact
  intro node source hsource
  exact key.addressedNodeRule1bRootDistance_eq_sourceCode mol center ligand
    hroot hexact node source hsource

/-- Final combined boundary: a successful admissible production hierarchy is both a universally
addressing-faithful exact declarative expansion and pointwise exact for the total Rule-1b
observations actually compiled by production. -/
theorem branchCanonicalKey?_faithfulExactExpansion_and_rule1bObservationExact
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true)
    (hrootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand) :
    RootedDigraph.FaithfulExactExpansion
        (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
        (key.toDeclarativeDigraph mol) ∧
      ∀ node source, key.sourceNodeAtAddress? node.1 = some source →
        nodeRule1bRootDistance ((key.declarativeAddressing mol).address node)
            (some ((key.toDeclarativeDigraph mol).label node)) =
          source.rule1bCode := by
  exact ⟨mol.branchCanonicalKey?_faithfulExactExpansion center ligand key
      hwellFormed hunique hkey hcomplete hrootBond,
    mol.branchCanonicalKey?_rule1bObservationExact center ligand key hkey hcomplete⟩

end RawMolecule

end
end OneCenter
end TetraStereo
