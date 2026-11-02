import TetraStereo.OneCenter.CIPAuthoritativeExactExpansion
import TetraStereo.OneCenter.CIPAuthoritativeConformance
import TetraStereo.OneCenter.ProductionCIPRule1aCertifiedGlobal

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

/-!
# Chemical soundness of the uncapped authoritative Rule-1a labeler

The production Rule-1a proof establishes that its finite raw localized-mancude graph realizes the
independent P-92 maximum-matching semantics.  This file gives the same direct proof for the
authoritative executable and every finite component size.
-/

/-- Every successful uncapped general-mancude label is the independent mean over all maximum
matchings of the localized component. -/
theorem generalMancudeRule1aLabelAuthoritative?_exactAverage
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached duplicated : Fin mol.atomCount)
    (label : CIPAtomicLabel)
    (hlabel :
      mol.generalMancudeRule1aLabelAuthoritative? attached.val duplicated.val = some label) :
    label.toExactAtomicNumber.value =
      (mol.toMoleculeGraph.exactMancudeAverage attached).value := by
  let vertices := mol.localizedMancudeComponentVertices attached.val
  let edges := mol.localizedMancudeComponentEdges attached.val
  unfold generalMancudeRule1aLabelAuthoritative? at hlabel
  change (if !(vertices.contains duplicated.val) || edges.isEmpty then none
    else do
      let stats ← mol.mancudeMatchingStats attached.val (edges.length + 1) edges
      let writtenDoubleCount :=
        (edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2).length
      if stats.size != writtenDoubleCount || stats.count == 0 then none
      else some { numerator := stats.partnerZSum, denominator := stats.count }) =
        some label at hlabel
  split at hlabel <;> rename_i hguard
  · contradiction
  · have hstatsCall := mol.mancudeMatchingStats_length_succ attached.val edges
    rw [hstatsCall] at hlabel
    simp only [instMonadOption, Option.bind_some] at hlabel
    split at hlabel <;> rename_i hsupport
    · contradiction
    · have hlabelEq : label =
          { numerator :=
              (mol.exhaustiveMancudeMatchingStats attached.val edges).partnerZSum
            denominator :=
              (mol.exhaustiveMancudeMatchingStats attached.val edges).count } := by
          exact Option.some.inj hlabel.symm
      subst label
      have hcount := mol.componentExhaustiveStats_count_eq_independent_card
        hwellFormed hunique attached
      have hsum := mol.componentExhaustiveStats_partnerZSum_eq_independent_sum
        hwellFormed hunique attached
      unfold CIPAtomicLabel.toExactAtomicNumber ExactAtomicNumber.value
        MoleculeGraph.exactMancudeAverage
      simp only [CIPAtomicLabel.effectiveDenominator]
      rw [hsum, hcount]
      have hindependentPositive :
          0 < (mol.toMoleculeGraph.maximumMancudeMatchings attached).card :=
        Finset.card_pos.mpr
          (mol.toMoleculeGraph.maximumMancudeMatchings_nonempty attached)
      have hone : 1 ≤ (mol.toMoleculeGraph.maximumMancudeMatchings attached).card :=
        hindependentPositive
      rw [max_eq_left hone]

/-- The uncapped general branch is exact when the duplicated edge is raw-localized. -/
theorem generalMancudeRule1aLabelAuthoritative?_sound_of_raw_localized
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached duplicated : Fin mol.atomCount)
    (hraw : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true)
    (label : CIPAtomicLabel)
    (hlabel :
      mol.generalMancudeRule1aLabelAuthoritative? attached.val duplicated.val = some label) :
    label.toExactAtomicNumber.value =
      (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value := by
  have hlocalized : mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated :=
    (mol.containsUndirectedEdge_localizedMancudeEdges_iff
      hwellFormed hunique attached duplicated).1 hraw
  rw [mol.toMoleculeGraph.exactRule1aMultipleBond_of_localized hlocalized]
  exact mol.generalMancudeRule1aLabelAuthoritative?_exactAverage
    hwellFormed hunique attached duplicated label hlabel

/-- Global exact-rational soundness proposition for the uncapped authoritative dispatcher. -/
def AuthoritativeMancudeRule1aSound (mol : RawMolecule) : Prop :=
  ∀ (attached duplicated : Fin mol.atomCount) (label : CIPAtomicLabel),
    mol.mancudeRule1aLabelAuthoritative? attached.val duplicated.val = some label →
      label.toExactAtomicNumber.value =
        (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value

/-- Every well-formed finite molecule with unique raw bond records satisfies global chemical
soundness for every successful uncapped authoritative Rule-1a label. -/
theorem authoritativeMancudeRule1aSound
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) : mol.AuthoritativeMancudeRule1aSound := by
  intro attached duplicated label hlabel
  by_cases hraw : containsUndirectedEdge mol.localizedMancudeEdges
      attached.val duplicated.val = true
  · have hlocalized : mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated :=
      (mol.containsUndirectedEdge_localizedMancudeEdges_iff
        hwellFormed hunique attached duplicated).1 hraw
    cases hcycle : mol.simpleMancudeCycle? attached.val duplicated.val with
    | none =>
        apply mol.generalMancudeRule1aLabelAuthoritative?_sound_of_raw_localized
          hwellFormed hunique attached duplicated hraw label
        unfold mancudeRule1aLabelAuthoritative? at hlabel
        simpa [hraw, hcycle] using hlabel
    | some cycleData =>
        rcases cycleData with ⟨cycle, alternate⟩
        have hlabelEq :
            label = mol.simpleMancudeCycleLabel duplicated.val alternate cycle := by
          unfold mancudeRule1aLabelAuthoritative? at hlabel
          simp only [hraw, Bool.not_true, Bool.false_eq_true, if_false, hcycle,
            Option.some.injEq] at hlabel
          exact hlabel.symm
        subst label
        rw [mol.toMoleculeGraph.exactRule1aMultipleBond_of_localized hlocalized]
        exact mol.simpleMancudeCycleLabel_exactAverage hwellFormed hunique
          attached duplicated cycle alternate hcycle
  · have hrawFalse : containsUndirectedEdge mol.localizedMancudeEdges
        attached.val duplicated.val = false := Bool.eq_false_of_not_eq_true hraw
    have hsemantic :
        ¬ mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated := by
      intro localized
      apply hraw
      exact (mol.containsUndirectedEdge_localizedMancudeEdges_iff
        hwellFormed hunique attached duplicated).2 localized
    have hproduction :
        mol.mancudeRule1aLabel? attached.val duplicated.val = some label := by
      unfold mancudeRule1aLabelAuthoritative? at hlabel
      unfold mancudeRule1aLabel?
      simpa [hrawFalse] using hlabel
    exact mol.mancudeRule1aLabel?_sound_of_not_localized attached duplicated
      hrawFalse hsemantic label hproduction

/-! ## Realized authoritative node observations -/

/-- Exact Rule-1a correctness at a realized authoritative hierarchy node.  Unlike the earlier
production predicate, the observed label is supplied by the uncapped authoritative dispatcher. -/
def CanonicalBranchKey.AuthoritativeRule1aObservationCorrectAt
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (node : key.HierarchyNode) (source : CanonicalBranchNode) : Prop :=
  ∃ label, mol.canonicalRule1aLabelAuthoritative? source = some label ∧
    label.toExactAtomicNumber.value =
      (exactRule1aNodeObservation mol.toMoleculeGraph (key.toDeclarativeDigraph mol)
        (key.declarativeAddressing mol) node).value

/-- Ordinary, ring-duplicate, and phantom nodes are exact without a mancude hypothesis. -/
theorem CanonicalBranchKey.authoritativeRule1aObservationCorrectAt_of_not_multiple
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.val = some source)
    (hnotMultiple : ∀ distance,
      source.provenance ≠ CanonicalNodeProvenance.multipleBondDuplicate distance) :
    key.AuthoritativeRule1aObservationCorrectAt mol node source := by
  let observation := nodeAtomicNumber
    (mol.canonicalHierarchyMoleculeGraph center ligand)
    (some ((key.toDeclarativeDigraph mol).label node))
  refine ⟨{ numerator := observation, denominator := 1 }, ?_, ?_⟩
  · have hobservation := key.nodeAtomicNumber_eq_sourceProjection mol center ligand
      hwellFormed hroot hexact node source hsource
    cases hprovenance : source.provenance with
    | realAtom | ringDuplicate =>
        simp [canonicalRule1aLabelAuthoritative?, hprovenance, observation, hobservation]
    | phantom =>
        simp [canonicalRule1aLabelAuthoritative?, hprovenance, observation, hobservation]
    | multipleBondDuplicate distance =>
        exact (hnotMultiple distance hprovenance).elim
  · have hindependent :=
      key.exactRule1aNodeObservation_eq_ofNat_nodeAtomicNumber_of_not_multiple
        mol center ligand hwellFormed hroot hexact node source hsource hnotMultiple
    rw [hindependent]
    rfl

/-- At a multiple-bond duplicate, global authoritative mancude soundness and the label actually
observed by the uncapped compiler imply the independent P-92 node observation. -/
theorem CanonicalBranchKey.authoritativeRule1aObservationCorrectAt_of_multiple
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.val = some source)
    (distance : ℕ)
    (hprovenance : source.provenance =
      CanonicalNodeProvenance.multipleBondDuplicate distance)
    (hsound : mol.AuthoritativeMancudeRule1aSound)
    (label : CIPAtomicLabel)
    (hlabel : mol.canonicalRule1aLabelAuthoritative? source = some label) :
    key.AuthoritativeRule1aObservationCorrectAt mol node source := by
  obtain ⟨attached, duplicated, hattached, hduplicated, hindependent⟩ :=
    key.exactRule1aNodeObservation_eq_exactMultipleBond_of_source
      mol center ligand hwellFormed hroot hexact node source hsource distance hprovenance
  have hdispatcher :
      mol.mancudeRule1aLabelAuthoritative? attached.val duplicated.val = some label := by
    unfold canonicalRule1aLabelAuthoritative? at hlabel
    rw [hprovenance] at hlabel
    simpa [hattached, hduplicated] using hlabel
  refine ⟨label, hlabel, ?_⟩
  exact (hsound attached duplicated label hdispatcher).trans
    (congrArg ExactAtomicNumber.value hindependent.symm)

/-- Every successfully observed authoritative label on an exact realized hierarchy is the
independent exact Rule-1a observation. -/
theorem CanonicalBranchKey.authoritativeRule1aObservationCorrectAt
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (hsound : mol.AuthoritativeMancudeRule1aSound)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.val = some source)
    (label : CIPAtomicLabel)
    (hlabel : mol.canonicalRule1aLabelAuthoritative? source = some label) :
    key.AuthoritativeRule1aObservationCorrectAt mol node source := by
  cases hprovenance : source.provenance with
  | realAtom | ringDuplicate | phantom =>
      apply key.authoritativeRule1aObservationCorrectAt_of_not_multiple
        mol center ligand hwellFormed hroot hexact node source hsource
      intro distance hmultiple
      simp [hprovenance] at hmultiple
  | multipleBondDuplicate distance =>
      exact key.authoritativeRule1aObservationCorrectAt_of_multiple
        mol center ligand hwellFormed hroot hexact node source hsource distance
        hprovenance hsound label hlabel

/-- The uncapped executable Rule-1a comparator agrees exactly with the independent molecular
node observations represented at the two hierarchy positions. -/
theorem compareCanonicalNodeRuleAuthoritative?_rule1a_exactNodeOutcome_iff
    (mol : RawMolecule) (leftKey rightKey : CanonicalBranchKey)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (leftSource rightSource : CanonicalBranchNode)
    (hleft : leftKey.AuthoritativeRule1aObservationCorrectAt mol leftNode leftSource)
    (hright : rightKey.AuthoritativeRule1aObservationCorrectAt mol rightNode rightSource)
    (outcome : Ordering) :
    mol.compareCanonicalNodeRuleAuthoritative? CanonicalRuleStage.rule1a
        leftSource rightSource = some outcome ↔
      ExactAtomicNumber.Outcome
        (exactRule1aNodeObservation mol.toMoleculeGraph
          (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol) leftNode)
        (exactRule1aNodeObservation mol.toMoleculeGraph
          (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol) rightNode)
        outcome := by
  rcases hleft with ⟨leftLabel, hleftLabel, hleftValue⟩
  rcases hright with ⟨rightLabel, hrightLabel, hrightValue⟩
  rw [authoritative_rule1a_conforms_independent_exact mol leftSource rightSource
    leftLabel rightLabel hleftLabel hrightLabel outcome]
  unfold ExactAtomicNumber.Outcome
  rw [hleftValue, hrightValue]

/-- Public shared-position refinement: a successful authoritative Rule-1a comparison has exactly
the independent P-92 relational outcome at that digraph position. -/
theorem pairedNodeRule1aOutcome_iff_authoritative
    (mol : RawMolecule) (leftKey rightKey : CanonicalBranchKey)
    (position : List ℕ)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (hleftPosition : leftNode.val = position)
    (hrightPosition : rightNode.val = position)
    (leftSource rightSource : CanonicalBranchNode)
    (hleft : leftKey.AuthoritativeRule1aObservationCorrectAt mol leftNode leftSource)
    (hright : rightKey.AuthoritativeRule1aObservationCorrectAt mol rightNode rightSource)
    (outcome : Ordering) :
    mol.compareCanonicalNodeRuleAuthoritative? CanonicalRuleStage.rule1a
        leftSource rightSource = some outcome ↔
      ExactRule1aOutcomeAt mol.toMoleculeGraph
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        position outcome := by
  exact
    (compareCanonicalNodeRuleAuthoritative?_rule1a_exactNodeOutcome_iff
      mol leftKey rightKey leftNode rightNode leftSource rightSource hleft hright outcome).trans
      (CanonicalBranchKey.exactRule1aOutcomeAt_iff_nodeOutcome mol leftKey rightKey position
        leftNode rightNode hleftPosition hrightPosition outcome).symm

/-! ## Complete authoritative branch certificate -/

/-- Every node retained by a successful complete authoritative branch compiler has the exact
independent P-92 Rule-1a observation.  Label availability, hierarchy realization, and mancude
soundness are all discharged from the compiler result and ordinary raw-molecule admission. -/
theorem branchCanonicalKeyAuthoritative?_rule1aObservationCorrect
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (computed : branchCanonicalKeyAuthoritative? mol center.val ligand.val = some key)
    (complete : key.complete = true) :
    ∀ (node : key.HierarchyNode) (source : CanonicalBranchNode),
      key.sourceNodeAtAddress? node.val = some source →
        key.AuthoritativeRule1aObservationCorrectAt mol node source := by
  have structural := mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
    center.val ligand.val key computed complete
  have sound := mol.authoritativeMancudeRule1aSound admitted.1 admitted.2
  intro node source sourceAt
  obtain ⟨label, labelObserved⟩ :=
    mol.branchCanonicalKeyAuthoritative?_rule1aLabelSupportedAt
      center.val ligand.val key computed complete node.val source sourceAt
  exact key.authoritativeRule1aObservationCorrectAt mol center ligand
    admitted.1 structural.1 structural.2 sound node source sourceAt label labelObserved

/-- A complete authoritative branch is simultaneously a faithful molecular CIP digraph and
Rule-1a-correct at every realized occurrence. -/
theorem branchCanonicalKeyAuthoritative?_faithfulExactExpansion_and_rule1aObservationCorrect
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (computed : branchCanonicalKeyAuthoritative? mol center.val ligand.val = some key)
    (complete : key.complete = true)
    (rootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand) :
    RootedDigraph.FaithfulExactExpansion
        (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
        (key.toDeclarativeDigraph mol) ∧
      ∀ (node : key.HierarchyNode) (source : CanonicalBranchNode),
        key.sourceNodeAtAddress? node.val = some source →
          key.AuthoritativeRule1aObservationCorrectAt mol node source := by
  exact ⟨mol.branchCanonicalKeyAuthoritative?_faithfulExactExpansion
      center ligand key admitted computed complete rootBond,
    mol.branchCanonicalKeyAuthoritative?_rule1aObservationCorrect
      center ligand key admitted computed complete⟩

end RawMolecule

end

end TetraStereo.OneCenter
