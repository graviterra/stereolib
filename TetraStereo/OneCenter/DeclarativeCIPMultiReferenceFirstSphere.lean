import TetraStereo.OneCenter.DeclarativeCIPMultiReferenceProblem
import TetraStereo.OneCenter.LocalizedFirstSpherePhysicalPriority
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# The declarative first sphere decides distinct-atom ligands

For a faithful exact expansion, the root is the actual ligand atom.  Thus distinct atomic numbers
decide Rule 1a at address `[]`, before any later hierarchy address.  This file packages that fact
for the multireference molecular problem: it is independent of descriptor maps and holds for every
faithful expansion.  Non-vacuity hypotheses are kept explicit when a result concerns the universal
`Problem.RuleOutcome` or `Problem.Higher` relations.

No runtime key or evaluator output is used here.
-/

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

open RootedDigraph

universe u

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Root-first Rule 1a hierarchy outcome for any parent-preserving addressings. -/
theorem constitutionalHierarchyOutcome_rule1a_gt_of_rootLabels
    (molecule : MoleculeGraph Atom) {left right : RootedDigraph Atom}
    {leftAtom rightAtom : Atom}
    (hleftRoot : left.label left.root = ⟨some leftAtom, NodeProvenance.realAtom⟩)
    (hrightRoot : right.label right.root = ⟨some rightAtom, NodeProvenance.realAtom⟩)
    (hZ : molecule.atomZ rightAtom < molecule.atomZ leftAtom)
    (leftAddressing : left.Addressing) (rightAddressing : right.Addressing) :
    ConstitutionalHierarchyOutcome molecule .rule1aAtomicNumber left leftAddressing
      right rightAddressing Ordering.gt := by
  change FirstDifferenceOutcome
    (ConstitutionalOutcomeAt molecule .rule1aAtomicNumber left leftAddressing right
      rightAddressing) Ordering.gt
  refine ⟨[], ?_, ?_⟩
  · unfold ConstitutionalOutcomeAt
    refine ⟨some (left.label left.root), some (right.label right.root), ?_, ?_, ?_⟩
    · exact Or.inl ⟨left.root, leftAddressing.root_address, rfl⟩
    · exact Or.inl ⟨right.root, rightAddressing.root_address, rfl⟩
    · change DescendingNatOutcome
        (nodeAtomicNumber molecule (some (left.label left.root)))
        (nodeAtomicNumber molecule (some (right.label right.root))) Ordering.gt
      simpa [nodeAtomicNumber, hleftRoot, hrightRoot] using
        (DescendingNatOutcome.gt hZ)
  · intro earlier hearlier
    exact False.elim (not_hierarchyAddressBefore_nil earlier hearlier)

/-- If the two faithful ligand roots have distinct atomic numbers, Rule 1a's canonical hierarchy
outcome is read at the root, uniformly over every pair of semantic addressings. -/
theorem constitutionalCanonical_rule1a_gt_of_faithful
    (molecule : MoleculeGraph Atom) (externalParent leftAtom rightAtom : Atom)
    {left right : RootedDigraph Atom}
    (leftFaithful : FaithfulExactExpansion molecule externalParent leftAtom left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent rightAtom right)
    (hZ : molecule.atomZ rightAtom < molecule.atomZ leftAtom) :
    ConstitutionalCanonical molecule .rule1aAtomicNumber left right Ordering.gt := by
  have hleftRoot : left.label left.root = ⟨some leftAtom, NodeProvenance.realAtom⟩ :=
    leftFaithful.1.1.1
  have hrightRoot : right.label right.root = ⟨some rightAtom, NodeProvenance.realAtom⟩ :=
    rightFaithful.1.1.1
  obtain ⟨leftBase, _⟩ := leftFaithful.1.2
  obtain ⟨rightBase, _⟩ := rightFaithful.1.2
  obtain ⟨leftAddressing, hleftCanonical⟩ :=
    exists_canonicalAddressing molecule leftBase
  obtain ⟨rightAddressing, hrightCanonical⟩ :=
    exists_canonicalAddressing molecule rightBase
  unfold ConstitutionalCanonical
  refine ⟨⟨leftAddressing, hleftCanonical⟩, ⟨rightAddressing, hrightCanonical⟩, ?_⟩
  intro leftAddressing' rightAddressing' _ _
  exact constitutionalHierarchyOutcome_rule1a_gt_of_rootLabels molecule hleftRoot hrightRoot
    hZ leftAddressing' rightAddressing'

/-- The corresponding root-first Rule 1a outcome when the right ligand has the larger atomic
number. -/
theorem constitutionalHierarchyOutcome_rule1a_lt_of_rootLabels
    (molecule : MoleculeGraph Atom) {left right : RootedDigraph Atom}
    {leftAtom rightAtom : Atom}
    (hleftRoot : left.label left.root = ⟨some leftAtom, NodeProvenance.realAtom⟩)
    (hrightRoot : right.label right.root = ⟨some rightAtom, NodeProvenance.realAtom⟩)
    (hZ : molecule.atomZ leftAtom < molecule.atomZ rightAtom)
    (leftAddressing : left.Addressing) (rightAddressing : right.Addressing) :
    ConstitutionalHierarchyOutcome molecule .rule1aAtomicNumber left leftAddressing
      right rightAddressing Ordering.lt := by
  change FirstDifferenceOutcome
    (ConstitutionalOutcomeAt molecule .rule1aAtomicNumber left leftAddressing right
      rightAddressing) Ordering.lt
  refine ⟨[], ?_, ?_⟩
  · unfold ConstitutionalOutcomeAt
    refine ⟨some (left.label left.root), some (right.label right.root), ?_, ?_, ?_⟩
    · exact Or.inl ⟨left.root, leftAddressing.root_address, rfl⟩
    · exact Or.inl ⟨right.root, rightAddressing.root_address, rfl⟩
    · change DescendingNatOutcome
        (nodeAtomicNumber molecule (some (left.label left.root)))
        (nodeAtomicNumber molecule (some (right.label right.root))) Ordering.lt
      simpa [nodeAtomicNumber, hleftRoot, hrightRoot] using
        (DescendingNatOutcome.lt hZ)
  · intro earlier hearlier
    exact False.elim (not_hierarchyAddressBefore_nil earlier hearlier)

theorem constitutionalCanonical_rule1a_lt_of_faithful
    (molecule : MoleculeGraph Atom) (externalParent leftAtom rightAtom : Atom)
    {left right : RootedDigraph Atom}
    (leftFaithful : FaithfulExactExpansion molecule externalParent leftAtom left)
    (rightFaithful : FaithfulExactExpansion molecule externalParent rightAtom right)
    (hZ : molecule.atomZ leftAtom < molecule.atomZ rightAtom) :
    ConstitutionalCanonical molecule .rule1aAtomicNumber left right Ordering.lt := by
  have hleftRoot : left.label left.root = ⟨some leftAtom, NodeProvenance.realAtom⟩ :=
    leftFaithful.1.1.1
  have hrightRoot : right.label right.root = ⟨some rightAtom, NodeProvenance.realAtom⟩ :=
    rightFaithful.1.1.1
  obtain ⟨leftBase, _⟩ := leftFaithful.1.2
  obtain ⟨rightBase, _⟩ := rightFaithful.1.2
  obtain ⟨leftAddressing, hleftCanonical⟩ :=
    exists_canonicalAddressing molecule leftBase
  obtain ⟨rightAddressing, hrightCanonical⟩ :=
    exists_canonicalAddressing molecule rightBase
  unfold ConstitutionalCanonical
  refine ⟨⟨leftAddressing, hleftCanonical⟩, ⟨rightAddressing, hrightCanonical⟩, ?_⟩
  intro leftAddressing' rightAddressing' _ _
  exact constitutionalHierarchyOutcome_rule1a_lt_of_rootLabels molecule hleftRoot hrightRoot
    hZ leftAddressing' rightAddressing'

/-- Canonical constitutional judgments are functional, even when their addressing witnesses are
chosen independently. -/
theorem constitutionalCanonical_functional
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    {left right : RootedDigraph Atom} {first second : Ordering}
    (hfirst : ConstitutionalCanonical molecule rule left right first)
    (hsecond : ConstitutionalCanonical molecule rule left right second) :
    first = second := by
  rcases hfirst with ⟨⟨leftAddressing, hleftCanonical⟩,
    ⟨rightAddressing, hrightCanonical⟩, hallFirst⟩
  rcases hsecond with ⟨_, _, hallSecond⟩
  exact constitutionalHierarchyOutcome_functional molecule rule left leftAddressing right
    rightAddressing
    (hallFirst leftAddressing rightAddressing hleftCanonical hrightCanonical)
    (hallSecond leftAddressing rightAddressing hleftCanonical hrightCanonical)

/-- On any faithful exact expansion pair, Rule 1a gives `gt` whenever the left ligand atom has the
larger atomic number.  The descriptor map is arbitrary and does not enter the judgment. -/
theorem multiReferenceRule1a_outcomeOnGraphs_gt_of_atomZ_gt
    (molecule : MoleculeGraph Atom) (frame : DetectedFrame molecule)
    (orientation : DetectedOccurrence molecule → Equiv.Perm (Fin 4) → Descriptor → Prop)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (leftIndex rightIndex : Fin 4)
    {left right : RootedDigraph Atom}
    (leftFaithful : FaithfulExactExpansion molecule unit.1.atom
      (frame.ligand unit leftIndex) left)
    (rightFaithful : FaithfulExactExpansion molecule unit.1.atom
      (frame.ligand unit rightIndex) right)
    (hZ : molecule.atomZ (frame.ligand unit rightIndex) <
      molecule.atomZ (frame.ligand unit leftIndex)) :
    (multiReferenceProblem molecule frame orientation).OutcomeOnGraphs descriptorMap
      .rule1aAtomicNumber unit left right Ordering.gt := by
  rw [outcomeOnGraphs_multiReference molecule frame orientation descriptorMap
    .rule1aAtomicNumber (by decide) unit left right Ordering.gt]
  change ConstitutionalCanonical molecule .rule1aAtomicNumber left right Ordering.gt
  exact constitutionalCanonical_rule1a_gt_of_faithful molecule unit.1.atom
    (frame.ligand unit leftIndex) (frame.ligand unit rightIndex)
    leftFaithful rightFaithful hZ

/-- Universal Rule-1a outcome for every faithful exact expansion pair. -/
theorem multiReferenceRule1a_ruleOutcome_gt_of_atomZ_gt
    (molecule : MoleculeGraph Atom) (frame : DetectedFrame molecule)
    (orientation : DetectedOccurrence molecule → Equiv.Perm (Fin 4) → Descriptor → Prop)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (leftIndex rightIndex : Fin 4)
    (hZ : molecule.atomZ (frame.ligand unit rightIndex) <
      molecule.atomZ (frame.ligand unit leftIndex)) :
    (multiReferenceProblem molecule frame orientation).RuleOutcome descriptorMap
      .rule1aAtomicNumber unit leftIndex rightIndex Ordering.gt := by
  intro left right hleft hright
  exact multiReferenceRule1a_outcomeOnGraphs_gt_of_atomZ_gt molecule frame orientation
    descriptorMap unit leftIndex rightIndex hleft hright hZ

/-- Two canonical constitutional outcomes for one pair of expansions cannot disagree. -/
theorem multiReferenceRule1a_eq_outcome_implies_atomicNumber_eq
    (molecule : MoleculeGraph Atom) (frame : DetectedFrame molecule)
    (orientation : DetectedOccurrence molecule → Equiv.Perm (Fin 4) → Descriptor → Prop)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (leftIndex rightIndex : Fin 4)
    {left right : RootedDigraph Atom}
    (leftFaithful : FaithfulExactExpansion molecule unit.1.atom
      (frame.ligand unit leftIndex) left)
    (rightFaithful : FaithfulExactExpansion molecule unit.1.atom
      (frame.ligand unit rightIndex) right)
    (heq : (multiReferenceProblem molecule frame orientation).OutcomeOnGraphs descriptorMap
      .rule1aAtomicNumber unit left right Ordering.eq) :
    molecule.atomZ (frame.ligand unit leftIndex) =
      molecule.atomZ (frame.ligand unit rightIndex) := by
  have hcanonical : ConstitutionalCanonical molecule .rule1aAtomicNumber left right Ordering.eq := by
    have h := (outcomeOnGraphs_multiReference molecule frame orientation descriptorMap
      .rule1aAtomicNumber (by decide) unit left right Ordering.eq).1 heq
    change ConstitutionalCanonical molecule .rule1aAtomicNumber left right Ordering.eq at h
    exact h
  rcases lt_trichotomy (molecule.atomZ (frame.ligand unit leftIndex))
      (molecule.atomZ (frame.ligand unit rightIndex)) with hlt | heqZ | hgt
  · have hother := constitutionalCanonical_rule1a_lt_of_faithful molecule unit.1.atom
      (frame.ligand unit leftIndex) (frame.ligand unit rightIndex)
      leftFaithful rightFaithful hlt
    have hbad := constitutionalCanonical_functional molecule .rule1aAtomicNumber
      hcanonical hother
    cases hbad
  · exact heqZ
  · have hother := constitutionalCanonical_rule1a_gt_of_faithful molecule unit.1.atom
      (frame.ligand unit leftIndex) (frame.ligand unit rightIndex)
      leftFaithful rightFaithful hgt
    have hbad := constitutionalCanonical_functional molecule .rule1aAtomicNumber
      hcanonical hother
    cases hbad

/-- A distinct-atomic-number Rule-1a tie is impossible for the universal problem outcome, provided
each side has at least one admissible faithful exact expansion. -/
theorem multiReferenceRule1a_ruleOutcome_eq_impossible_of_atomicNumber_ne
    (molecule : MoleculeGraph Atom) (frame : DetectedFrame molecule)
    (orientation : DetectedOccurrence molecule → Equiv.Perm (Fin 4) → Descriptor → Prop)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (leftIndex rightIndex : Fin 4)
    (leftExists : ∃ graph, (multiReferenceProblem molecule frame orientation).admissibleExpansion
      unit leftIndex graph)
    (rightExists : ∃ graph, (multiReferenceProblem molecule frame orientation).admissibleExpansion
      unit rightIndex graph)
    (hZ : molecule.atomZ (frame.ligand unit leftIndex) ≠
      molecule.atomZ (frame.ligand unit rightIndex)) :
    ¬ (multiReferenceProblem molecule frame orientation).RuleOutcome descriptorMap
      .rule1aAtomicNumber unit leftIndex rightIndex Ordering.eq := by
  intro heq
  obtain ⟨left, hleft⟩ := leftExists
  obtain ⟨right, hright⟩ := rightExists
  have heqGraph := heq left right hleft hright
  have hZeq := multiReferenceRule1a_eq_outcome_implies_atomicNumber_eq molecule frame
    orientation descriptorMap unit leftIndex rightIndex hleft hright heqGraph
  exact hZ hZeq

/-- Under distinct atomic numbers and nonempty expansion families, the universal Rule-1a `gt`
outcome is equivalent to the left ligand atom having larger atomic number. -/
theorem multiReferenceRule1a_ruleOutcome_gt_iff_of_atomicNumber_ne
    (molecule : MoleculeGraph Atom) (frame : DetectedFrame molecule)
    (orientation : DetectedOccurrence molecule → Equiv.Perm (Fin 4) → Descriptor → Prop)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (leftIndex rightIndex : Fin 4)
    (leftExists : ∃ graph, (multiReferenceProblem molecule frame orientation).admissibleExpansion
      unit leftIndex graph)
    (rightExists : ∃ graph, (multiReferenceProblem molecule frame orientation).admissibleExpansion
      unit rightIndex graph)
    (hZ : molecule.atomZ (frame.ligand unit leftIndex) ≠
      molecule.atomZ (frame.ligand unit rightIndex)) :
    (multiReferenceProblem molecule frame orientation).RuleOutcome descriptorMap
      .rule1aAtomicNumber unit leftIndex rightIndex Ordering.gt ↔
        molecule.atomZ (frame.ligand unit rightIndex) <
          molecule.atomZ (frame.ligand unit leftIndex) := by
  constructor
  · intro hgt
    obtain ⟨left, hleft⟩ := leftExists
    obtain ⟨right, hright⟩ := rightExists
    have hgtGraph := hgt left right hleft hright
    have hgtCanonical : ConstitutionalCanonical molecule .rule1aAtomicNumber left right
        Ordering.gt := by
      have h := (outcomeOnGraphs_multiReference molecule frame orientation descriptorMap
        .rule1aAtomicNumber (by decide) unit left right Ordering.gt).1 hgtGraph
      change ConstitutionalCanonical molecule .rule1aAtomicNumber left right Ordering.gt at h
      exact h
    rcases lt_trichotomy (molecule.atomZ (frame.ligand unit rightIndex))
        (molecule.atomZ (frame.ligand unit leftIndex)) with hlt | heqZ | hgtZ
    · exact hlt
    · exact False.elim (hZ heqZ.symm)
    · have hltCanonical := constitutionalCanonical_rule1a_lt_of_faithful molecule
        unit.1.atom (frame.ligand unit leftIndex) (frame.ligand unit rightIndex)
        hleft hright hgtZ
      have hbad := constitutionalCanonical_functional molecule .rule1aAtomicNumber
        hgtCanonical hltCanonical
      cases hbad
  · intro hZgt
    exact multiReferenceRule1a_ruleOutcome_gt_of_atomZ_gt molecule frame orientation
      descriptorMap unit leftIndex rightIndex hZgt

/-- For distinct ligand atomic numbers, the multireference problem's strict priority is exactly
the descending atomic-number order.  Existence of one faithful expansion per side rules out
vacuous universal rule outcomes. -/
theorem multiReferenceHigher_iff_atomicNumber_gt_of_ne
    (molecule : MoleculeGraph Atom) (frame : DetectedFrame molecule)
    (orientation : DetectedOccurrence molecule → Equiv.Perm (Fin 4) → Descriptor → Prop)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (leftIndex rightIndex : Fin 4)
    (leftExists : ∃ graph, (multiReferenceProblem molecule frame orientation).admissibleExpansion
      unit leftIndex graph)
    (rightExists : ∃ graph, (multiReferenceProblem molecule frame orientation).admissibleExpansion
      unit rightIndex graph)
    (hZ : molecule.atomZ (frame.ligand unit leftIndex) ≠
      molecule.atomZ (frame.ligand unit rightIndex)) :
    (multiReferenceProblem molecule frame orientation).Higher descriptorMap unit leftIndex
      rightIndex ↔
        molecule.atomZ (frame.ligand unit rightIndex) <
          molecule.atomZ (frame.ligand unit leftIndex) := by
  constructor
  · rintro ⟨rule, hear, hrule⟩
    cases rule with
    | rule1aAtomicNumber =>
        exact (multiReferenceRule1a_ruleOutcome_gt_iff_of_atomicNumber_ne molecule frame
          orientation descriptorMap unit leftIndex rightIndex leftExists rightExists hZ).1 hrule
    | rule1bDuplicateNodeProximity
    | rule2AtomicMass
    | rule3DoubleBondGeometry
    | rule4aStereogenicUnitKind
    | rule4bLikeUnlikeDescriptorPairs
    | rule4cPseudoasymmetricDescriptor
    | rule5EnantiomorphicDescriptor
    | rule6ReferencePromotion =>
        have hfirst : (multiReferenceProblem molecule frame orientation).RuleOutcome descriptorMap
            .rule1aAtomicNumber unit leftIndex rightIndex Ordering.eq :=
          hear .rule1aAtomicNumber (by simp [SequenceRule.Before, SequenceRule.rank])
        exact False.elim ((multiReferenceRule1a_ruleOutcome_eq_impossible_of_atomicNumber_ne
          molecule frame orientation descriptorMap unit leftIndex rightIndex leftExists
          rightExists hZ) hfirst)
  · intro hZgt
    refine ⟨.rule1aAtomicNumber, ?_, ?_⟩
    · intro earlier hbefore
      simp [SequenceRule.Before, SequenceRule.rank] at hbefore
    · exact multiReferenceRule1a_ruleOutcome_gt_of_atomZ_gt molecule frame orientation
        descriptorMap unit leftIndex rightIndex hZgt

/-- Distinct atomic numbers make Rule 5 unreachable: its `EarlierRulesTie` premise would require
the already decisive Rule 1a comparison to tie. -/
theorem multiReferenceEarlierRulesTie5_false_of_atomicNumber_ne
    (molecule : MoleculeGraph Atom) (frame : DetectedFrame molecule)
    (orientation : DetectedOccurrence molecule → Equiv.Perm (Fin 4) → Descriptor → Prop)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (leftIndex rightIndex : Fin 4)
    (leftExists : ∃ graph, (multiReferenceProblem molecule frame orientation).admissibleExpansion
      unit leftIndex graph)
    (rightExists : ∃ graph, (multiReferenceProblem molecule frame orientation).admissibleExpansion
      unit rightIndex graph)
    (hZ : molecule.atomZ (frame.ligand unit leftIndex) ≠
      molecule.atomZ (frame.ligand unit rightIndex)) :
    ¬ (multiReferenceProblem molecule frame orientation).EarlierRulesTie descriptorMap
      .rule5EnantiomorphicDescriptor unit leftIndex rightIndex := by
  intro hTie
  have hfirst : (multiReferenceProblem molecule frame orientation).RuleOutcome descriptorMap
      .rule1aAtomicNumber unit leftIndex rightIndex Ordering.eq :=
    hTie .rule1aAtomicNumber (by
      change (0 : ℕ) < SequenceRule.rank .rule5EnantiomorphicDescriptor
      decide)
  exact (multiReferenceRule1a_ruleOutcome_eq_impossible_of_atomicNumber_ne molecule frame
    orientation descriptorMap unit leftIndex rightIndex leftExists rightExists hZ) hfirst

end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.constitutionalHierarchyOutcome_rule1a_gt_of_rootLabels
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.constitutionalCanonical_rule1a_gt_of_faithful
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.constitutionalHierarchyOutcome_rule1a_lt_of_rootLabels
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.constitutionalCanonical_rule1a_lt_of_faithful
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.constitutionalCanonical_functional
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.multiReferenceRule1a_outcomeOnGraphs_gt_of_atomZ_gt
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.multiReferenceRule1a_ruleOutcome_gt_of_atomZ_gt
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.multiReferenceRule1a_eq_outcome_implies_atomicNumber_eq
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.multiReferenceRule1a_ruleOutcome_eq_impossible_of_atomicNumber_ne
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.multiReferenceRule1a_ruleOutcome_gt_iff_of_atomicNumber_ne
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.multiReferenceHigher_iff_atomicNumber_gt_of_ne
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.multiReferenceEarlierRulesTie5_false_of_atomicNumber_ne
