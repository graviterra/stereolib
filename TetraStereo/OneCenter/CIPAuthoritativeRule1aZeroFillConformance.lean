import TetraStereo.OneCenter.CIPAuthoritativeRule1aPositivity
import TetraStereo.OneCenter.CIPAuthoritativeSparseZeroFillConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace RawMolecule

/-!
# Unconditional sparse-to-zero-filled Rule-1a bridge for certified chemistry

Rule-2 mass admission excludes the atomic-number-zero wildcard.  Therefore every retained Rule-1a
observation is strictly above the declarative value at an absent address.  Successful recursive
compilation also proves that no empty sphere was retained.  These two facts remove the final side
conditions from the generic sparse zero-fill theorem.
-/

/-- The declarative Rule-1a value at a missing hierarchy address. -/
def zeroRule1aLabel : CIPAtomicLabel :=
  { numerator := 0, denominator := 1 }

/-- Total authoritative Rule-1a observation at a semantic address, with the exact declarative
zero value outside the represented branch support. -/
def authoritativeRule1aObservationAt
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (position : List ℕ) : CIPAtomicLabel :=
  ((key.sourceNodeAtAddress? position).map
    mol.canonicalRule1aLabelAuthoritativeTotal).getD zeroRule1aLabel

@[simp] theorem compareCIPAtomicLabel_zeroRule1aLabel_self :
    compareCIPAtomicLabel zeroRule1aLabel zeroRule1aLabel = .eq := by
  exact compareCIPAtomicLabel_self zeroRule1aLabel

@[simp] theorem zeroRule1aLabel_toExactAtomicNumber :
    zeroRule1aLabel.toExactAtomicNumber = DeclarativeCIP.ExactAtomicNumber.zero := by
  rfl

theorem compareCIPAtomicLabel_zeroRule1aLabel_eq_gt
    (label : CIPAtomicLabel) (positive : 0 < label.numerator) :
    compareCIPAtomicLabel label zeroRule1aLabel = .gt := by
  simp [compareCIPAtomicLabel, zeroRule1aLabel,
    CIPAtomicLabel.effectiveDenominator, Nat.compare_eq_gt.mpr positive]

theorem compareCIPAtomicLabel_zeroRule1aLabel_eq_lt
    (label : CIPAtomicLabel) (positive : 0 < label.numerator) :
    compareCIPAtomicLabel zeroRule1aLabel label = .lt := by
  simp [compareCIPAtomicLabel, zeroRule1aLabel,
    CIPAtomicLabel.effectiveDenominator, Nat.compare_eq_lt.mpr positive]

/-- On complete mass-admitted authoritative branches, the executable nested sparse Rule-1a
comparison is exactly ordinary lexicographic comparison after both branches are zero-filled on
their union of semantic addresses. -/
theorem branchCanonicalKeysAuthoritative_rule1a_eq_compareLex_zeroFilled
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (known : mol.Rule2MassesKnown)
    (leftComputed : branchCanonicalKeyAuthoritative?
      mol center.val leftLigand.val = some leftKey)
    (rightComputed : branchCanonicalKeyAuthoritative?
      mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true) :
    compareSparseCanonicalLayers compareCIPAtomicLabel
        leftKey.rule1a rightKey.rule1a =
      List.compareLex compareCIPAtomicLabel
        ((alignSparseCanonicalLayers zeroRule1aLabel
          leftKey.rule1a rightKey.rule1a).flatten.map
            AlignedSparseCanonicalEntry.left)
        ((alignSparseCanonicalLayers zeroRule1aLabel
          leftKey.rule1a rightKey.rule1a).flatten.map
            AlignedSparseCanonicalEntry.right) := by
  have leftSourceAligned := mol.branchCanonicalKeyAuthoritative?_sourceAligned
    center.val leftLigand.val leftKey leftComputed
  have rightSourceAligned := mol.branchCanonicalKeyAuthoritative?_sourceAligned
    center.val rightLigand.val rightKey rightComputed
  have leftDense := mol.branchCanonicalKeyAuthoritative?_dense
    center.val leftLigand.val leftKey leftComputed
  have rightDense := mol.branchCanonicalKeyAuthoritative?_dense
    center.val rightLigand.val rightKey rightComputed
  have leftNonempty : ∀ layer, layer ∈ leftKey.rule1a → layer ≠ [] := by
    rw [leftSourceAligned.1]
    exact leftDense.map_observation leftKey.sourceNodes
      mol.canonicalRule1aLabelAuthoritativeTotal
  have rightNonempty : ∀ layer, layer ∈ rightKey.rule1a → layer ≠ [] := by
    rw [rightSourceAligned.1]
    exact rightDense.map_observation rightKey.sourceNodes
      mol.canonicalRule1aLabelAuthoritativeTotal
  have leftPositive := mol.branchCanonicalKeyAuthoritative?_rule1a_numerator_pos
    center leftLigand leftKey admitted known leftComputed leftComplete
  have rightPositive := mol.branchCanonicalKeyAuthoritative?_rule1a_numerator_pos
    center rightLigand rightKey admitted known rightComputed rightComplete
  apply compareSparseCanonicalLayers_eq_compareLex_aligned
    compareCIPAtomicLabel zeroRule1aLabel
      compareCIPAtomicLabel_zeroRule1aLabel_self
      leftKey.rule1a rightKey.rule1a leftNonempty rightNonempty
  · intro layer layerPresent entry entryPresent
    exact compareCIPAtomicLabel_zeroRule1aLabel_eq_gt entry.2
      (leftPositive layer layerPresent entry entryPresent)
  · intro layer layerPresent entry entryPresent
    exact compareCIPAtomicLabel_zeroRule1aLabel_eq_lt entry.2
      (rightPositive layer layerPresent entry entryPresent)

/-- The two aligned projections are exactly the authoritative source observations read at their
common union-address schedule.  Thus zero filling is not merely comparator-equivalent: every
aligned cell has its precise molecule-to-source meaning. -/
theorem branchCanonicalKeysAuthoritative_rule1a_aligned_projections
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (leftComputed : branchCanonicalKeyAuthoritative?
      mol center.val leftLigand.val = some leftKey)
    (rightComputed : branchCanonicalKeyAuthoritative?
      mol center.val rightLigand.val = some rightKey) :
    let aligned := alignSparseCanonicalLayers zeroRule1aLabel
      leftKey.rule1a rightKey.rule1a
    aligned.flatten.map AlignedSparseCanonicalEntry.left =
        (aligned.flatten.map AlignedSparseCanonicalEntry.address).map
          (authoritativeRule1aObservationAt mol leftKey) ∧
      aligned.flatten.map AlignedSparseCanonicalEntry.right =
        (aligned.flatten.map AlignedSparseCanonicalEntry.address).map
          (authoritativeRule1aObservationAt mol rightKey) := by
  dsimp only
  have leftSourceAligned := mol.branchCanonicalKeyAuthoritative?_sourceAligned
    center.val leftLigand.val leftKey leftComputed
  have rightSourceAligned := mol.branchCanonicalKeyAuthoritative?_sourceAligned
    center.val rightLigand.val rightKey rightComputed
  obtain ⟨leftTree, leftTreeAligned⟩ :=
    mol.branchCanonicalKeyAuthoritative?_sourceTreeAligned
      center.val leftLigand.val leftKey leftComputed
  obtain ⟨rightTree, rightTreeAligned⟩ :=
    mol.branchCanonicalKeyAuthoritative?_sourceTreeAligned
      center.val rightLigand.val rightKey rightComputed
  have leftSourceScheduled := mol.branchCanonicalKeyAuthoritative?_scheduled
    center.val leftLigand.val leftKey leftComputed
  have rightSourceScheduled := mol.branchCanonicalKeyAuthoritative?_scheduled
    center.val rightLigand.val rightKey rightComputed
  have leftScheduled : SparseCanonicalLayersScheduledFrom 0 leftKey.rule1a := by
    rw [leftSourceAligned.1]
    exact leftSourceScheduled.map_observation 0 leftKey.sourceNodes
      mol.canonicalRule1aLabelAuthoritativeTotal
  have rightScheduled : SparseCanonicalLayersScheduledFrom 0 rightKey.rule1a := by
    rw [rightSourceAligned.1]
    exact rightSourceScheduled.map_observation 0 rightKey.sourceNodes
      mol.canonicalRule1aLabelAuthoritativeTotal
  have alignedScheduled := leftScheduled.align zeroRule1aLabel 0
    leftKey.rule1a rightKey.rule1a rightScheduled
  have alignedOrdered := alignedScheduled.flattened_pairwise 0
    (alignSparseCanonicalLayers zeroRule1aLabel leftKey.rule1a rightKey.rule1a)
  have addressesNodup :
      ((alignSparseCanonicalLayers zeroRule1aLabel
        leftKey.rule1a rightKey.rule1a).flatten.map
          AlignedSparseCanonicalEntry.address).Nodup :=
    alignedOrdered.imp fun {first second} before => by
      intro equal
      subst second
      unfold DeclarativeCIP.HierarchyAddressBefore at before
      exact (lt_irrefl _ before)
  have leftFlatten : leftKey.rule1a.flatten =
      leftKey.sourceNodes.flatten.map fun entry =>
        (entry.1, mol.canonicalRule1aLabelAuthoritativeTotal entry.2) := by
    rw [leftSourceAligned.1]
    simp [mapCanonicalSourceLayers, List.map_flatten]
  have rightFlatten : rightKey.rule1a.flatten =
      rightKey.sourceNodes.flatten.map fun entry =>
        (entry.1, mol.canonicalRule1aLabelAuthoritativeTotal entry.2) := by
    rw [rightSourceAligned.1]
    simp [mapCanonicalSourceLayers, List.map_flatten]
  have leftAddressSupport : leftKey.rule1a.flatten.map Prod.fst =
      leftKey.sourceAddressSchedule := by
    rw [leftFlatten]
    simp [CanonicalBranchKey.sourceAddressSchedule, List.map_map, Function.comp_def]
  have rightAddressSupport : rightKey.rule1a.flatten.map Prod.fst =
      rightKey.sourceAddressSchedule := by
    rw [rightFlatten]
    simp [CanonicalBranchKey.sourceAddressSchedule, List.map_map, Function.comp_def]
  constructor
  · rw [List.map_map]
    apply List.map_congr_left
    intro entry entryPresent
    change entry.left = authoritativeRule1aObservationAt mol leftKey entry.address
    cases sourceFound : leftKey.sourceNodeAtAddress? entry.address with
    | none =>
        have addressAbsent : entry.address ∉ leftKey.rule1a.flatten.map Prod.fst := by
          rw [leftAddressSupport]
          intro addressPresent
          obtain ⟨source, sourceAt⟩ :=
            (leftTreeAligned.mem_sourceAddressSchedule_iff_exists_source
              leftKey leftTree entry.address).mp addressPresent
          rw [sourceFound] at sourceAt
          contradiction
        rw [entry.left_eq_zero_of_not_mem_flatten zeroRule1aLabel
          leftKey.rule1a rightKey.rule1a entryPresent addressAbsent]
        simp [authoritativeRule1aObservationAt, sourceFound]
    | some source =>
        have sourcePresent : (entry.address, source) ∈ leftKey.sourceNodes.flatten :=
          (leftTreeAligned.mem_flatten_iff_sourceNodeAtAddress
            leftKey leftTree entry.address source).mpr sourceFound
        have rulePresent :
            (entry.address, mol.canonicalRule1aLabelAuthoritativeTotal source) ∈
              leftKey.rule1a.flatten := by
          rw [leftFlatten]
          exact List.mem_map.mpr ⟨(entry.address, source), sourcePresent, rfl⟩
        rw [entry.left_eq_of_mem_flatten zeroRule1aLabel
          leftKey.rule1a rightKey.rule1a addressesNodup entryPresent
            (entry.address, mol.canonicalRule1aLabelAuthoritativeTotal source)
              rulePresent rfl]
        simp [authoritativeRule1aObservationAt, sourceFound]
  · rw [List.map_map]
    apply List.map_congr_left
    intro entry entryPresent
    change entry.right = authoritativeRule1aObservationAt mol rightKey entry.address
    cases sourceFound : rightKey.sourceNodeAtAddress? entry.address with
    | none =>
        have addressAbsent : entry.address ∉ rightKey.rule1a.flatten.map Prod.fst := by
          rw [rightAddressSupport]
          intro addressPresent
          obtain ⟨source, sourceAt⟩ :=
            (rightTreeAligned.mem_sourceAddressSchedule_iff_exists_source
              rightKey rightTree entry.address).mp addressPresent
          rw [sourceFound] at sourceAt
          contradiction
        rw [entry.right_eq_zero_of_not_mem_flatten zeroRule1aLabel
          leftKey.rule1a rightKey.rule1a entryPresent addressAbsent]
        simp [authoritativeRule1aObservationAt, sourceFound]
    | some source =>
        have sourcePresent : (entry.address, source) ∈ rightKey.sourceNodes.flatten :=
          (rightTreeAligned.mem_flatten_iff_sourceNodeAtAddress
            rightKey rightTree entry.address source).mpr sourceFound
        have rulePresent :
            (entry.address, mol.canonicalRule1aLabelAuthoritativeTotal source) ∈
              rightKey.rule1a.flatten := by
          rw [rightFlatten]
          exact List.mem_map.mpr ⟨(entry.address, source), sourcePresent, rfl⟩
        rw [entry.right_eq_of_mem_flatten zeroRule1aLabel
          leftKey.rule1a rightKey.rule1a addressesNodup entryPresent
            (entry.address, mol.canonicalRule1aLabelAuthoritativeTotal source)
              rulePresent rfl]
        simp [authoritativeRule1aObservationAt, sourceFound]

private theorem exactRule1aObservationAt_zero_of_sourceNodeAtAddress?_eq_none
    (mol : RawMolecule) (key : CanonicalBranchKey) (tree : CanonicalSourceTree)
    (aligned : key.SourceTreeAligned tree) (position : List ℕ)
    (sourceAbsent : key.sourceNodeAtAddress? position = none) :
    DeclarativeCIP.ExactRule1aObservationAt mol.toMoleculeGraph
      (key.toDeclarativeDigraph mol) (key.declarativeAddressing mol)
      position DeclarativeCIP.ExactAtomicNumber.zero := by
  right
  refine ⟨rfl, ?_⟩
  intro node nodePosition
  have schedulePresent : position ∈ key.sourceAddressSchedule := by
    apply (aligned.mem_sourceAddressSchedule_iff key tree position).2
    change node.1 = position at nodePosition
    rw [← nodePosition]
    exact node.2
  obtain ⟨source, sourceAt⟩ :=
    (aligned.mem_sourceAddressSchedule_iff_exists_source
      key tree position).mp schedulePresent
  rw [sourceAbsent] at sourceAt
  contradiction

/-- At every semantic address, including a position represented on only one side, comparison of
the total zero-filled authoritative observations is exactly the independent relational Rule-1a
outcome. -/
theorem branchCanonicalKeysAuthoritative_rule1aOutcomeAt_iff
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (known : mol.Rule2MassesKnown)
    (leftComputed : branchCanonicalKeyAuthoritative?
      mol center.val leftLigand.val = some leftKey)
    (rightComputed : branchCanonicalKeyAuthoritative?
      mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true)
    (position : List ℕ) (outcome : Ordering) :
    compareCIPAtomicLabel
        (authoritativeRule1aObservationAt mol leftKey position)
        (authoritativeRule1aObservationAt mol rightKey position) = outcome ↔
      DeclarativeCIP.ExactRule1aOutcomeAt mol.toMoleculeGraph
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        position outcome := by
  obtain ⟨leftTree, leftTreeAligned⟩ :=
    mol.branchCanonicalKeyAuthoritative?_sourceTreeAligned
      center.val leftLigand.val leftKey leftComputed
  obtain ⟨rightTree, rightTreeAligned⟩ :=
    mol.branchCanonicalKeyAuthoritative?_sourceTreeAligned
      center.val rightLigand.val rightKey rightComputed
  have leftStructural := mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
    center.val leftLigand.val leftKey leftComputed leftComplete
  have rightStructural := mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
    center.val rightLigand.val rightKey rightComputed rightComplete
  cases leftFound : leftKey.sourceNodeAtAddress? position with
  | some leftSource =>
      have leftSchedule : position ∈ leftKey.sourceAddressSchedule :=
        (leftTreeAligned.mem_sourceAddressSchedule_iff_exists_source
          leftKey leftTree position).2 ⟨leftSource, leftFound⟩
      have leftAddress : position ∈ leftKey.hierarchyAddresses :=
        (leftTreeAligned.mem_sourceAddressSchedule_iff
          leftKey leftTree position).mp leftSchedule
      let leftNode : leftKey.HierarchyNode := ⟨position, leftAddress⟩
      have leftCorrect :=
        mol.branchCanonicalKeyAuthoritative?_rule1aObservationCorrect
          center leftLigand leftKey admitted leftComputed leftComplete
            leftNode leftSource leftFound
      rcases leftCorrect with ⟨leftLabel, leftLabelAt, leftValue⟩
      have leftPositive := leftKey.authoritativeRule1aLabel_numerator_pos
        mol center leftLigand admitted.1 admitted.2 leftStructural.1 leftStructural.2
          known leftNode leftSource leftFound leftLabel leftLabelAt
      cases rightFound : rightKey.sourceNodeAtAddress? position with
      | some rightSource =>
          have rightSchedule : position ∈ rightKey.sourceAddressSchedule :=
            (rightTreeAligned.mem_sourceAddressSchedule_iff_exists_source
              rightKey rightTree position).2 ⟨rightSource, rightFound⟩
          have rightAddress : position ∈ rightKey.hierarchyAddresses :=
            (rightTreeAligned.mem_sourceAddressSchedule_iff
              rightKey rightTree position).mp rightSchedule
          let rightNode : rightKey.HierarchyNode := ⟨position, rightAddress⟩
          have rightCorrect :=
            mol.branchCanonicalKeyAuthoritative?_rule1aObservationCorrect
              center rightLigand rightKey admitted rightComputed rightComplete
                rightNode rightSource rightFound
          rcases rightCorrect with ⟨rightLabel, rightLabelAt, rightValue⟩
          have paired := pairedNodeRule1aOutcome_iff_authoritative
            mol leftKey rightKey position leftNode rightNode rfl rfl
              leftSource rightSource
              ⟨leftLabel, leftLabelAt, leftValue⟩
              ⟨rightLabel, rightLabelAt, rightValue⟩ outcome
          simpa [authoritativeRule1aObservationAt,
            canonicalRule1aLabelAuthoritativeTotal, leftFound, rightFound,
            leftLabelAt, rightLabelAt, compareCanonicalNodeRuleAuthoritative?] using paired
      | none =>
          let leftExact := DeclarativeCIP.exactRule1aNodeObservation
            mol.toMoleculeGraph (leftKey.toDeclarativeDigraph mol)
              (leftKey.declarativeAddressing mol) leftNode
          have leftObservation : DeclarativeCIP.ExactRule1aObservationAt
              mol.toMoleculeGraph (leftKey.toDeclarativeDigraph mol)
                (leftKey.declarativeAddressing mol) position leftExact :=
            Or.inl ⟨leftNode, rfl, rfl⟩
          have rightObservation : DeclarativeCIP.ExactRule1aObservationAt
              mol.toMoleculeGraph (rightKey.toDeclarativeDigraph mol)
                (rightKey.declarativeAddressing mol) position
                  DeclarativeCIP.ExactAtomicNumber.zero :=
            exactRule1aObservationAt_zero_of_sourceNodeAtAddress?_eq_none
              mol rightKey rightTree rightTreeAligned position rightFound
          have computedGt : compareCIPAtomicLabel
              (authoritativeRule1aObservationAt mol leftKey position)
              (authoritativeRule1aObservationAt mol rightKey position) = .gt := by
            simpa [authoritativeRule1aObservationAt,
              canonicalRule1aLabelAuthoritativeTotal, leftFound, rightFound, leftLabelAt] using
                compareCIPAtomicLabel_zeroRule1aLabel_eq_gt leftLabel leftPositive
          have exactGt : DeclarativeCIP.ExactAtomicNumber.Outcome
              leftExact DeclarativeCIP.ExactAtomicNumber.zero .gt := by
            unfold DeclarativeCIP.ExactAtomicNumber.Outcome
            rw [LinearOrder.compare_eq_compareOfLessAndEq, ← leftValue,
              ← zeroRule1aLabel_toExactAtomicNumber,
              ← compareCIPAtomicLabel_eq_exactOutcomeValue]
            exact compareCIPAtomicLabel_zeroRule1aLabel_eq_gt leftLabel leftPositive
          have semanticGt : DeclarativeCIP.ExactRule1aOutcomeAt mol.toMoleculeGraph
              (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
              (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
              position .gt :=
            ⟨leftExact, DeclarativeCIP.ExactAtomicNumber.zero,
              leftObservation, rightObservation, exactGt⟩
          constructor
          · intro computed
            have outcomeEq : outcome = .gt := computed.symm.trans computedGt
            rw [outcomeEq]
            exact semanticGt
          · intro semantic
            have outcomeEq := DeclarativeCIP.exactRule1aOutcomeAt_functional
              mol.toMoleculeGraph
              (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
              (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
              position semantic semanticGt
            rw [outcomeEq]
            exact computedGt
  | none =>
      have leftZeroObservation :=
        exactRule1aObservationAt_zero_of_sourceNodeAtAddress?_eq_none
          mol leftKey leftTree leftTreeAligned position leftFound
      cases rightFound : rightKey.sourceNodeAtAddress? position with
      | some rightSource =>
          have rightSchedule : position ∈ rightKey.sourceAddressSchedule :=
            (rightTreeAligned.mem_sourceAddressSchedule_iff_exists_source
              rightKey rightTree position).2 ⟨rightSource, rightFound⟩
          have rightAddress : position ∈ rightKey.hierarchyAddresses :=
            (rightTreeAligned.mem_sourceAddressSchedule_iff
              rightKey rightTree position).mp rightSchedule
          let rightNode : rightKey.HierarchyNode := ⟨position, rightAddress⟩
          have rightCorrect :=
            mol.branchCanonicalKeyAuthoritative?_rule1aObservationCorrect
              center rightLigand rightKey admitted rightComputed rightComplete
                rightNode rightSource rightFound
          rcases rightCorrect with ⟨rightLabel, rightLabelAt, rightValue⟩
          have rightPositive := rightKey.authoritativeRule1aLabel_numerator_pos
            mol center rightLigand admitted.1 admitted.2 rightStructural.1 rightStructural.2
              known rightNode rightSource rightFound rightLabel rightLabelAt
          let rightExact := DeclarativeCIP.exactRule1aNodeObservation
            mol.toMoleculeGraph (rightKey.toDeclarativeDigraph mol)
              (rightKey.declarativeAddressing mol) rightNode
          have leftObservation : DeclarativeCIP.ExactRule1aObservationAt
              mol.toMoleculeGraph (leftKey.toDeclarativeDigraph mol)
                (leftKey.declarativeAddressing mol) position
                  DeclarativeCIP.ExactAtomicNumber.zero :=
            leftZeroObservation
          have rightObservation : DeclarativeCIP.ExactRule1aObservationAt
              mol.toMoleculeGraph (rightKey.toDeclarativeDigraph mol)
                (rightKey.declarativeAddressing mol) position rightExact :=
            Or.inl ⟨rightNode, rfl, rfl⟩
          have computedLt : compareCIPAtomicLabel
              (authoritativeRule1aObservationAt mol leftKey position)
              (authoritativeRule1aObservationAt mol rightKey position) = .lt := by
            simpa [authoritativeRule1aObservationAt,
              canonicalRule1aLabelAuthoritativeTotal, leftFound, rightFound, rightLabelAt] using
                compareCIPAtomicLabel_zeroRule1aLabel_eq_lt rightLabel rightPositive
          have exactLt : DeclarativeCIP.ExactAtomicNumber.Outcome
              DeclarativeCIP.ExactAtomicNumber.zero rightExact .lt := by
            unfold DeclarativeCIP.ExactAtomicNumber.Outcome
            rw [LinearOrder.compare_eq_compareOfLessAndEq, ← rightValue,
              ← zeroRule1aLabel_toExactAtomicNumber,
              ← compareCIPAtomicLabel_eq_exactOutcomeValue]
            exact compareCIPAtomicLabel_zeroRule1aLabel_eq_lt rightLabel rightPositive
          have semanticLt : DeclarativeCIP.ExactRule1aOutcomeAt mol.toMoleculeGraph
              (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
              (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
              position .lt :=
            ⟨DeclarativeCIP.ExactAtomicNumber.zero, rightExact,
              leftObservation, rightObservation, exactLt⟩
          constructor
          · intro computed
            have outcomeEq : outcome = .lt := computed.symm.trans computedLt
            rw [outcomeEq]
            exact semanticLt
          · intro semantic
            have outcomeEq := DeclarativeCIP.exactRule1aOutcomeAt_functional
              mol.toMoleculeGraph
              (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
              (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
              position semantic semanticLt
            rw [outcomeEq]
            exact computedLt
      | none =>
          have rightZeroObservation :=
            exactRule1aObservationAt_zero_of_sourceNodeAtAddress?_eq_none
              mol rightKey rightTree rightTreeAligned position rightFound
          have computedEq : compareCIPAtomicLabel
              (authoritativeRule1aObservationAt mol leftKey position)
              (authoritativeRule1aObservationAt mol rightKey position) = .eq := by
            simp [authoritativeRule1aObservationAt, leftFound, rightFound]
          have semanticEq : DeclarativeCIP.ExactRule1aOutcomeAt mol.toMoleculeGraph
              (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
              (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
              position .eq :=
            ⟨DeclarativeCIP.ExactAtomicNumber.zero,
              DeclarativeCIP.ExactAtomicNumber.zero,
              leftZeroObservation, rightZeroObservation, by
                simp [DeclarativeCIP.ExactAtomicNumber.Outcome]⟩
          constructor
          · intro computed
            have outcomeEq : outcome = .eq := computed.symm.trans computedEq
            rw [outcomeEq]
            exact semanticEq
          · intro semantic
            have outcomeEq := DeclarativeCIP.exactRule1aOutcomeAt_functional
              mol.toMoleculeGraph
              (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
              (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
              position semantic semanticEq
            rw [outcomeEq]
            exact computedEq

/-- Complete mass-admitted authoritative branches satisfy the unconditional whole-hierarchy
Rule-1a theorem: the executable sparse comparison is exactly the independent sphere-major first
difference relation, even when the two sparse supports differ. -/
theorem branchCanonicalKeysAuthoritative_rule1aHierarchyOutcome_iff
    (mol : RawMolecule) (center leftLigand rightLigand : Fin mol.atomCount)
    (leftKey rightKey : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (known : mol.Rule2MassesKnown)
    (leftComputed : branchCanonicalKeyAuthoritative?
      mol center.val leftLigand.val = some leftKey)
    (rightComputed : branchCanonicalKeyAuthoritative?
      mol center.val rightLigand.val = some rightKey)
    (leftComplete : leftKey.complete = true)
    (rightComplete : rightKey.complete = true)
    (outcome : Ordering) :
    compareSparseCanonicalLayers compareCIPAtomicLabel
        leftKey.rule1a rightKey.rule1a = outcome ↔
      DeclarativeCIP.ExactRule1aHierarchyOutcome mol.toMoleculeGraph
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        outcome := by
  let aligned := alignSparseCanonicalLayers zeroRule1aLabel
    leftKey.rule1a rightKey.rule1a
  let positions := aligned.flatten.map AlignedSparseCanonicalEntry.address
  have sparseEq := branchCanonicalKeysAuthoritative_rule1a_eq_compareLex_zeroFilled
    mol center leftLigand rightLigand leftKey rightKey admitted known
      leftComputed rightComputed leftComplete rightComplete
  have projections := branchCanonicalKeysAuthoritative_rule1a_aligned_projections
    mol center leftLigand rightLigand leftKey rightKey leftComputed rightComputed
  have leftSourceAligned := mol.branchCanonicalKeyAuthoritative?_sourceAligned
    center.val leftLigand.val leftKey leftComputed
  have rightSourceAligned := mol.branchCanonicalKeyAuthoritative?_sourceAligned
    center.val rightLigand.val rightKey rightComputed
  obtain ⟨leftTree, leftTreeAligned⟩ :=
    mol.branchCanonicalKeyAuthoritative?_sourceTreeAligned
      center.val leftLigand.val leftKey leftComputed
  obtain ⟨rightTree, rightTreeAligned⟩ :=
    mol.branchCanonicalKeyAuthoritative?_sourceTreeAligned
      center.val rightLigand.val rightKey rightComputed
  have leftSourceScheduled := mol.branchCanonicalKeyAuthoritative?_scheduled
    center.val leftLigand.val leftKey leftComputed
  have rightSourceScheduled := mol.branchCanonicalKeyAuthoritative?_scheduled
    center.val rightLigand.val rightKey rightComputed
  have leftScheduled : SparseCanonicalLayersScheduledFrom 0 leftKey.rule1a := by
    rw [leftSourceAligned.1]
    exact leftSourceScheduled.map_observation 0 leftKey.sourceNodes
      mol.canonicalRule1aLabelAuthoritativeTotal
  have rightScheduled : SparseCanonicalLayersScheduledFrom 0 rightKey.rule1a := by
    rw [rightSourceAligned.1]
    exact rightSourceScheduled.map_observation 0 rightKey.sourceNodes
      mol.canonicalRule1aLabelAuthoritativeTotal
  have alignedScheduled := leftScheduled.align zeroRule1aLabel 0
    leftKey.rule1a rightKey.rule1a rightScheduled
  have positionsOrdered : positions.Pairwise DeclarativeCIP.HierarchyAddressBefore := by
    exact alignedScheduled.flattened_pairwise 0 aligned
  have leftFlatten : leftKey.rule1a.flatten =
      leftKey.sourceNodes.flatten.map fun entry =>
        (entry.1, mol.canonicalRule1aLabelAuthoritativeTotal entry.2) := by
    rw [leftSourceAligned.1]
    simp [mapCanonicalSourceLayers, List.map_flatten]
  have rightFlatten : rightKey.rule1a.flatten =
      rightKey.sourceNodes.flatten.map fun entry =>
        (entry.1, mol.canonicalRule1aLabelAuthoritativeTotal entry.2) := by
    rw [rightSourceAligned.1]
    simp [mapCanonicalSourceLayers, List.map_flatten]
  have leftAddressSupport : leftKey.rule1a.flatten.map Prod.fst =
      leftKey.sourceAddressSchedule := by
    rw [leftFlatten]
    simp [CanonicalBranchKey.sourceAddressSchedule, List.map_map, Function.comp_def]
  have rightAddressSupport : rightKey.rule1a.flatten.map Prod.fst =
      rightKey.sourceAddressSchedule := by
    rw [rightFlatten]
    simp [CanonicalBranchKey.sourceAddressSchedule, List.map_map, Function.comp_def]
  have outside : ∀ position, position ∉ positions →
      compareCIPAtomicLabel
        (authoritativeRule1aObservationAt mol leftKey position)
        (authoritativeRule1aObservationAt mol rightKey position) = .eq := by
    intro position positionAbsent
    have leftAbsent : position ∉ leftKey.rule1a.flatten.map Prod.fst := by
      intro leftPresent
      apply positionAbsent
      apply (mem_alignSparseCanonicalLayers_flatten_addresses
        zeroRule1aLabel position leftKey.rule1a rightKey.rule1a).2
      exact Or.inl leftPresent
    have rightAbsent : position ∉ rightKey.rule1a.flatten.map Prod.fst := by
      intro rightPresent
      apply positionAbsent
      apply (mem_alignSparseCanonicalLayers_flatten_addresses
        zeroRule1aLabel position leftKey.rule1a rightKey.rule1a).2
      exact Or.inr rightPresent
    have leftLookup : leftKey.sourceNodeAtAddress? position = none := by
      cases found : leftKey.sourceNodeAtAddress? position with
      | none => rfl
      | some source =>
          have schedulePresent : position ∈ leftKey.sourceAddressSchedule :=
            (leftTreeAligned.mem_sourceAddressSchedule_iff_exists_source
              leftKey leftTree position).2 ⟨source, found⟩
          exact (leftAbsent (by rwa [leftAddressSupport])).elim
    have rightLookup : rightKey.sourceNodeAtAddress? position = none := by
      cases found : rightKey.sourceNodeAtAddress? position with
      | none => rfl
      | some source =>
          have schedulePresent : position ∈ rightKey.sourceAddressSchedule :=
            (rightTreeAligned.mem_sourceAddressSchedule_iff_exists_source
              rightKey rightTree position).2 ⟨source, found⟩
          exact (rightAbsent (by rwa [rightAddressSupport])).elim
    simp [authoritativeRule1aObservationAt, leftLookup, rightLookup]
  rw [sparseEq]
  change List.compareLex compareCIPAtomicLabel
      (aligned.flatten.map AlignedSparseCanonicalEntry.left)
      (aligned.flatten.map AlignedSparseCanonicalEntry.right) = outcome ↔ _
  rw [projections.1, projections.2]
  have scheduledFirstDifference := DeclarativeCIP.compareLex_map_iff_firstDifference
    compareCIPAtomicLabel
    (authoritativeRule1aObservationAt mol leftKey)
    (authoritativeRule1aObservationAt mol rightKey)
    positions positionsOrdered outside outcome
  rw [scheduledFirstDifference]
  unfold DeclarativeCIP.ExactRule1aHierarchyOutcome
  exact DeclarativeCIP.FirstDifferenceOutcome.congr
    (fun position localOutcome =>
      branchCanonicalKeysAuthoritative_rule1aOutcomeAt_iff
        mol center leftLigand rightLigand leftKey rightKey admitted known
          leftComputed rightComputed leftComplete rightComplete position localOutcome)
    outcome

end RawMolecule

end TetraStereo.OneCenter
