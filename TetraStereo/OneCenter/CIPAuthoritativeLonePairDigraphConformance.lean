import TetraStereo.OneCenter.CIPAuthoritativeMoleculeDigraphConformance

set_option autoImplicit false

namespace TetraStereo.OneCenter

open ProductionCIPOccurrenceDiscovery
open DeclarativeCIP

/-- Every independently observed hierarchy is Rule-1a-equal to itself. -/
theorem exactRule1aHierarchyOutcome_refl
    {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) :
    ExactRule1aHierarchyOutcome molecule graph addressing graph addressing .eq := by
  intro position
  obtain ⟨observation, observed⟩ :=
    exactRule1aObservationAt_total molecule graph addressing position
  exact ⟨observation, observation, observed, observed, by
    simp [ExactAtomicNumber.Outcome]⟩

/-- Every independently observed hierarchy is Rule-1b- and Rule-2-equal to itself. -/
theorem constitutionalHierarchyOutcome_refl
    {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (rule : ConstitutionalRule)
    (graph : RootedDigraph Atom) (addressing : graph.Addressing) :
    ConstitutionalHierarchyOutcome molecule rule graph addressing graph addressing .eq := by
  intro position
  obtain ⟨label, observed⟩ :=
    RootedDigraph.Addressing.labelAt_exists graph addressing position
  refine ⟨label, label, observed, observed, ?_⟩
  cases rule
  · exact DescendingNatOutcome.eq rfl
  · exact Rule1bDistanceOutcome.eq rfl
  · exact DescendingNatOutcome.eq rfl

/-- Reflexivity of the complete independent constitutional hierarchy specification. -/
theorem RawMolecule.exactConstitutionalHierarchyFirstStrictOutcome_refl
    {Atom : Type*} [Fintype Atom] [DecidableEq Atom]
    (molecule : MoleculeGraph Atom) (graph : RootedDigraph Atom)
    (addressing : graph.Addressing) :
    RawMolecule.ExactConstitutionalHierarchyFirstStrictOutcome molecule
      graph addressing graph addressing .eq := by
  exact ⟨.eq, .eq, .eq,
    exactRule1aHierarchyOutcome_refl molecule graph addressing,
    constitutionalHierarchyOutcome_refl molecule .rule1bDuplicateNodeProximity graph addressing,
    constitutionalHierarchyOutcome_refl molecule .rule2AtomicMass graph addressing,
    rfl⟩

private theorem listCompareLex_self_of {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = .eq) :
    ∀ values : List α, List.compareLex cmp values values = .eq := by
  intro values
  induction values with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [List.compareLex, refl head, inductionHypothesis]

private theorem compareCanonicalPath_self (path : List ℕ) :
    RawMolecule.compareCanonicalPath path path = .eq := by
  exact listCompareLex_self_of compare (fun _ => by simp) path

private theorem compareSparseCanonicalEntry_self {α : Type*}
    (cmp : α → α → Ordering) (refl : ∀ value, cmp value value = .eq)
    (entry : List ℕ × α) :
    RawMolecule.compareSparseCanonicalEntry cmp entry entry = .eq := by
  rcases entry with ⟨path, value⟩
  simp [RawMolecule.compareSparseCanonicalEntry, compareLex,
    Ordering.byKey, flip, compareCanonicalPath_self path, refl value]

private theorem compareSparseCanonicalLayers_self {α : Type*}
    (cmp : α → α → Ordering) (refl : ∀ value, cmp value value = .eq)
    (layers : List (List (List ℕ × α))) :
    RawMolecule.compareSparseCanonicalLayers cmp layers layers = .eq := by
  apply listCompareLex_self_of
  intro layer
  apply listCompareLex_self_of
  exact compareSparseCanonicalEntry_self cmp refl

/-- Reflexivity of the production constitutional branch-key comparator. -/
theorem RawMolecule.compareCanonicalBranchKeys_self
    (key : RawMolecule.CanonicalBranchKey) :
    RawMolecule.compareCanonicalBranchKeys key key = .eq := by
  simp [RawMolecule.compareCanonicalBranchKeys, compareLex, Ordering.byKey,
    compareSparseCanonicalLayers_self compareCIPAtomicLabel
      (fun label => by simp [compareCIPAtomicLabel]),
    compareSparseCanonicalLayers_self RawMolecule.compareRule1bRootDistance
      (fun _ => by simp [RawMolecule.compareRule1bRootDistance, flip]),
    compareSparseCanonicalLayers_self (compare : ℕ → ℕ → Ordering) (fun (_ : ℕ) => by
      exact Std.ReflCmp.compare_self (cmp := (compare : ℕ → ℕ → Ordering)))]

namespace RawMolecule

/-- Authoritative recursive compilation never moves the branch root out of the first Rule-1a
sphere.  This shape lemma is independent of the descendants and exposes the chemically decisive
root observation without evaluating the complete finite branch. -/
theorem buildCanonicalBranchKeyAuthoritative_rule1a_head
    (mol : RawMolecule) : ∀ fuel node key label,
    mol.buildCanonicalBranchKeyAuthoritative fuel node = some key →
    mol.canonicalRule1aLabelAuthoritative? node = some label →
    key.rule1a.head? = some [([], label)]
  | 0, node, key, label, computed, labelComputed => by
      unfold buildCanonicalBranchKeyAuthoritative at computed
      unfold canonicalRootKeyAuthoritative? at computed
      simp [labelComputed] at computed
      subst key
      rfl
  | fuel + 1, node, key, label, computed, labelComputed => by
      unfold buildCanonicalBranchKeyAuthoritative at computed
      by_cases terminal : mol.canonicalTerminal node = true
      · simp only [terminal, ↓reduceIte] at computed
        unfold canonicalRootKeyAuthoritative? at computed
        simp [labelComputed] at computed
        subst key
        rfl
      · rw [if_neg terminal] at computed
        let children := mol.canonicalChildren node
        by_cases tooWide : authoritativeChildSlots < children.length
        · simp [children, tooWide] at computed
        · rw [if_neg tooWide] at computed
          cases childrenComputed : children.mapM
              (mol.buildCanonicalBranchKeyAuthoritative fuel) with
          | none => simp [children, childrenComputed] at computed
          | some childKeys =>
              cases sortedComputed : sortCanonicalKeys? childKeys with
              | none => simp [children, childrenComputed, sortedComputed] at computed
              | some sorted =>
                  cases rootComputed : mol.canonicalRootKeyAuthoritative? node
                      (sorted.all fun child => child.complete) with
                  | none => simp [children, childrenComputed, sortedComputed,
                      rootComputed] at computed
                  | some root =>
                      simp [children, childrenComputed, sortedComputed,
                        rootComputed] at computed
                      subst key
                      have rootHead : root.rule1a.head? = some [([], label)] := by
                        unfold canonicalRootKeyAuthoritative? at rootComputed
                        simp [labelComputed] at rootComputed
                        subst root
                        rfl
                      simp [assembleCanonicalBranchKey, rootHead]

/-- Public authoritative branch compilation retains its physical ligand's exact Rule-1a root
layer as the first sphere. -/
theorem branchCanonicalKeyAuthoritative?_rule1a_head
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (label : CIPAtomicLabel)
    (computed : branchCanonicalKeyAuthoritative? mol center ligand = some key)
    (labelComputed : mol.canonicalRule1aLabelAuthoritative?
      (canonicalRoot center ligand) = some label) :
    key.rule1a.head? = some [([], label)] := by
  unfold branchCanonicalKeyAuthoritative? at computed
  exact mol.buildCanonicalBranchKeyAuthoritative_rule1a_head
    (2 * mol.atomCount + 2) (canonicalRoot center ligand) key label computed labelComputed

/-- Local list lookup fails exactly at the one-past-the-end index used for the production
lone-pair sentinel. -/
theorem listGet?_length_eq_none {α : Type*} (values : List α) :
    listGet? values values.length = none := by
  induction values with
  | nil => rfl
  | cons _ tail inductionHypothesis =>
      simpa [listGet?] using inductionHypothesis

/-- A well-formed molecule has no physical bond incident to the atom-count sentinel. -/
theorem canonicalChildCopies_eq_nil_of_atom_eq_atomCount
    (mol : RawMolecule) (node : CanonicalBranchNode)
    (wellFormed : mol.WellFormed) (atomEq : node.atom = mol.atomCount) :
    mol.canonicalChildCopies node = [] := by
  unfold canonicalChildCopies
  have copiesNil :
      mol.bonds.flatMap (fun bond =>
        let next? :=
          if bond.source == node.atom then some bond.target
          else if bond.target == node.atom then some bond.source
          else none
        match next? with
        | none => []
        | some next =>
            (List.range (mol.canonicalBondOrder node next)).map fun copyIndex =>
              (next, copyIndex)) = [] := by
    apply List.flatMap_eq_nil_iff.mpr
    intro bond membership
    have endpoints := wellFormed bond membership
    have sourceNe : bond.source ≠ node.atom := by
      rw [atomEq]
      exact Nat.ne_of_lt endpoints.1
    have targetNe : bond.target ≠ node.atom := by
      rw [atomEq]
      exact Nat.ne_of_lt endpoints.2.1
    simp [sourceNe, targetNe]
  change eraseCanonicalParentCopy node.parent
    (mol.bonds.flatMap (fun bond =>
      let next? :=
        if bond.source == node.atom then some bond.target
        else if bond.target == node.atom then some bond.source
        else none
      match next? with
      | none => []
      | some next =>
          (List.range (mol.canonicalBondOrder node next)).map fun copyIndex =>
            (next, copyIndex))) = []
  rw [copiesNil]
  rfl

theorem canonicalChildren_eq_nil_of_atom_eq_atomCount
    (mol : RawMolecule) (node : CanonicalBranchNode)
    (wellFormed : mol.WellFormed) (atomEq : node.atom = mol.atomCount) :
    mol.canonicalChildren node = [] := by
  simp [canonicalChildren, canonicalChildCopies_eq_nil_of_atom_eq_atomCount
    mol node wellFormed atomEq]

theorem canonicalTerminal_of_atom_eq_atomCount
    (mol : RawMolecule) (node : CanonicalBranchNode)
    (wellFormed : mol.WellFormed) (atomEq : node.atom = mol.atomCount) :
    mol.canonicalTerminal node = true := by
  simp [canonicalTerminal, canonicalChildren_eq_nil_of_atom_eq_atomCount
    mol node wellFormed atomEq]

/-- At every fuel, authoritative compilation of the atom-count sentinel stops at its root. -/
theorem buildCanonicalBranchKeyAuthoritative_eq_root_of_atom_eq_atomCount
    (mol : RawMolecule) (fuel : ℕ) (node : CanonicalBranchNode)
    (wellFormed : mol.WellFormed) (atomEq : node.atom = mol.atomCount) :
    mol.buildCanonicalBranchKeyAuthoritative fuel node =
      mol.canonicalRootKeyAuthoritative? node true := by
  have terminal := canonicalTerminal_of_atom_eq_atomCount mol node wellFormed atomEq
  cases fuel <;> simp [buildCanonicalBranchKeyAuthoritative, terminal]

/-- The authoritative and independently projected root-only representations of a lone pair
coincide exactly. Its out-of-range atom becomes an atomless declarative node, while all three
constitutional executable fields are zero-valued. -/
theorem canonicalRootKeyAuthoritative?_lonePair
    (mol : RawMolecule) (center : ℕ) :
    mol.canonicalRootKeyAuthoritative? (canonicalRoot center mol.atomCount) true =
      some (mol.canonicalRootKey (canonicalRoot center mol.atomCount) true) := by
  simp [canonicalRootKeyAuthoritative?, canonicalRule1aLabelAuthoritative?,
    canonicalRootKey, canonicalRule1aLabel, canonicalRule1aLabel?, canonicalRoot,
    atomZAt, atomAt?, atomCount, atomMassAt, atomMassAt?, listGet?_length_eq_none]

/-- The public uncapped branch compiler produces exactly the terminal zero-valued key for a
lone-pair sentinel. -/
theorem branchCanonicalKeyAuthoritative?_lonePair
    (mol : RawMolecule) (center : Fin mol.atomCount) (wellFormed : mol.WellFormed) :
    branchCanonicalKeyAuthoritative? mol center.val mol.atomCount =
      some (mol.canonicalRootKey (canonicalRoot center.val mol.atomCount) true) := by
  unfold branchCanonicalKeyAuthoritative?
  rw [buildCanonicalBranchKeyAuthoritative_eq_root_of_atom_eq_atomCount
    mol (2 * mol.atomCount + 2) (canonicalRoot center.val mol.atomCount) wellFormed rfl]
  exact canonicalRootKeyAuthoritative?_lonePair mol center.val

end RawMolecule

namespace AuthoritativeCIPDiscovery

/-- Independent atomless-node boundary realized by one successfully discovered lone-pair slot. -/
structure LonePairBranchConformance {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (slot : Fin 4) : Prop where
  sentinel : ligandAtom root slot = mol.atomCount
  exactKey : (discovery.branch slot).key =
    mol.canonicalRootKey
      (RawMolecule.canonicalRoot (centerAtom root).val mol.atomCount) true
  atomlessRoot :
    ((((discovery.branch slot).key.toDeclarativeDigraph mol).label
      ((discovery.branch slot).key.toDeclarativeDigraph mol).root).atom?) = none
  rule1aZero : (discovery.branch slot).key.rule1a =
    [[([], { numerator := 0, denominator := 1 })]]
  rule1bRootDistance : (discovery.branch slot).key.rule1b = [[([], 1)]]
  rule2Zero : (discovery.branch slot).key.rule2 = [[([], 0)]]

/-- Successful authoritative discovery of the sentinel is not merely conventional: it is proved
to be the exact one-node atomless digraph with zero Rules-1a--2 observations. -/
theorem lonePairBranchConformance {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (slot : Fin 4)
    (admitted : mol.Admissible) (sentinel : ligandAtom root slot = mol.atomCount) :
    LonePairBranchConformance discovery slot := by
  have compiled := RawMolecule.branchCanonicalKeyAuthoritative?_lonePair
    mol (centerAtom root) admitted.1
  have accepted := (discovery.branch slot).accepted
  have accepted' : branchCanonicalKeyAuthoritative?
      mol (centerAtom root).val mol.atomCount = some (discovery.branch slot).key := by
    simpa only [sentinel] using accepted
  have keyEq : (discovery.branch slot).key =
      mol.canonicalRootKey
        (RawMolecule.canonicalRoot (centerAtom root).val mol.atomCount) true :=
    Option.some.inj (accepted'.symm.trans compiled)
  refine
    { sentinel := sentinel
      exactKey := keyEq
      atomlessRoot := ?_
      rule1aZero := ?_
      rule1bRootDistance := ?_
      rule2Zero := ?_ }
  · rw [keyEq]
    simp [RawMolecule.CanonicalBranchKey.toDeclarativeDigraph,
      RawMolecule.CanonicalBranchKey.declarativeLabel, RawMolecule.canonicalRootKey,
      RawMolecule.canonicalRoot, RawMolecule.CanonicalBranchKey.atomFin?,
      RawMolecule.atomCount]
  · rw [keyEq]
    simp [RawMolecule.canonicalRootKey, RawMolecule.canonicalRule1aLabel,
      RawMolecule.canonicalRule1aLabel?, RawMolecule.canonicalRoot,
      RawMolecule.atomZAt, RawMolecule.atomAt?, RawMolecule.atomCount,
      RawMolecule.listGet?_length_eq_none]
  · rw [keyEq]
    simp [RawMolecule.canonicalRootKey, RawMolecule.CanonicalBranchNode.rule1bCode,
      RawMolecule.CanonicalBranchNode.rule1bRootDistance,
      RawMolecule.CanonicalBranchNode.depth, RawMolecule.canonicalRoot]
  · rw [keyEq]
    simp [RawMolecule.canonicalRootKey, RawMolecule.canonicalRoot,
      RawMolecule.atomMassAt, RawMolecule.atomMassAt?, RawMolecule.atomAt?,
      RawMolecule.atomCount, RawMolecule.listGet?_length_eq_none]

/-- The production Rule-1a key of every mass-admitted physical ligand is already strictly above
the one-node lone-pair key in the root sphere.  No descendant or later constitutional rule is
consulted. -/
theorem physicalBranch_rule1a_gt_lonePair
    {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (physical lonePair : Fin 4)
    (physicalLigand : Fin mol.atomCount)
    (admitted : mol.Admissible) (known : mol.Rule2MassesKnown)
    (physicalEq : physicalLigand.val = ligandAtom root physical)
    (lonePairSentinel : ligandAtom root lonePair = mol.atomCount) :
    RawMolecule.compareSparseCanonicalLayers RawMolecule.compareCIPAtomicLabel
        (discovery.branch physical).key.rule1a
        (discovery.branch lonePair).key.rule1a = .gt := by
  let physicalLabel : RawMolecule.CIPAtomicLabel :=
    { numerator := mol.atomZAt physicalLigand.val, denominator := 1 }
  have physicalLabelComputed : mol.canonicalRule1aLabelAuthoritative?
      (RawMolecule.canonicalRoot (centerAtom root).val physicalLigand.val) =
        some physicalLabel := by
    simp [physicalLabel, RawMolecule.canonicalRule1aLabelAuthoritative?,
      RawMolecule.canonicalRoot]
  have physicalComputed : branchCanonicalKeyAuthoritative? mol
      (centerAtom root).val physicalLigand.val =
        some (discovery.branch physical).key := by
    simpa [physicalEq] using (discovery.branch physical).accepted
  have physicalHead := RawMolecule.branchCanonicalKeyAuthoritative?_rule1a_head
    mol (centerAtom root).val physicalLigand.val (discovery.branch physical).key
      physicalLabel physicalComputed physicalLabelComputed
  have lonePairConformance := lonePairBranchConformance
    discovery lonePair admitted lonePairSentinel
  have physicalPositive : 0 < physicalLabel.numerator := by
    change 0 < mol.atomZAt physicalLigand.val
    rw [mol.atomZAt_eq_toMoleculeGraph_atomZ physicalLigand.val physicalLigand.isLt]
    exact mol.atomZ_positive_of_rule2MassesKnown known physicalLigand
  cases physicalRules : (discovery.branch physical).key.rule1a with
  | nil => simp [physicalRules] at physicalHead
  | cons firstSphere laterSpheres =>
      rw [physicalRules] at physicalHead
      simp only [List.head?_cons, Option.some.injEq] at physicalHead
      subst firstSphere
      rw [lonePairConformance.rule1aZero]
      change RawMolecule.compareSparseCanonicalLayers
        RawMolecule.compareCIPAtomicLabel
          ([([], physicalLabel)] :: laterSpheres)
          [[([], RawMolecule.zeroRule1aLabel)]] = .gt
      have labelGt : RawMolecule.compareCIPAtomicLabel physicalLabel
          RawMolecule.zeroRule1aLabel = .gt :=
        RawMolecule.compareCIPAtomicLabel_zeroRule1aLabel_eq_gt
          physicalLabel physicalPositive
      have entryGt : RawMolecule.compareSparseCanonicalEntry
          RawMolecule.compareCIPAtomicLabel ([], physicalLabel)
            ([], RawMolecule.zeroRule1aLabel) = .gt := by
        rw [RawMolecule.compareSparseCanonicalEntry_samePath]
        exact labelGt
      have sphereGt : RawMolecule.compareSparseCanonicalLayer
          RawMolecule.compareCIPAtomicLabel [([], physicalLabel)]
            [([], RawMolecule.zeroRule1aLabel)] = .gt := by
        unfold RawMolecule.compareSparseCanonicalLayer
        simp only [List.compareLex]
        rw [entryGt]
      simp only [RawMolecule.compareSparseCanonicalLayers, List.compareLex]
      rw [sphereGt]

/-- Independently, the physical root has positive exact atomic number while the atomless lone-pair
root has exact atomic number zero.  Hence Rule 1a's first strict semantic outcome is `gt` at the
empty root address. -/
theorem physicalBranch_exactRule1aHierarchy_gt_lonePair
    {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (physical lonePair : Fin 4)
    (physicalLigand : Fin mol.atomCount)
    (admitted : mol.Admissible) (known : mol.Rule2MassesKnown)
    (physicalEq : physicalLigand.val = ligandAtom root physical)
    (lonePairSentinel : ligandAtom root lonePair = mol.atomCount) :
    ExactRule1aHierarchyOutcome mol.toMoleculeGraph
        ((discovery.branch physical).key.toDeclarativeDigraph mol)
        ((discovery.branch physical).key.declarativeAddressing mol)
        ((discovery.branch lonePair).key.toDeclarativeDigraph mol)
        ((discovery.branch lonePair).key.declarativeAddressing mol) .gt := by
  let physicalGraph := (discovery.branch physical).key.toDeclarativeDigraph mol
  let physicalAddressing := (discovery.branch physical).key.declarativeAddressing mol
  let lonePairGraph := (discovery.branch lonePair).key.toDeclarativeDigraph mol
  let lonePairAddressing := (discovery.branch lonePair).key.declarativeAddressing mol
  have physicalRooted : (discovery.branch physical).key.RootedAt
      (centerAtom root).val physicalLigand.val := by
    have accepted : branchCanonicalKeyAuthoritative? mol
        (centerAtom root).val physicalLigand.val =
          some (discovery.branch physical).key := by
      simpa [physicalEq] using (discovery.branch physical).accepted
    exact (mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
      (centerAtom root).val physicalLigand.val (discovery.branch physical).key
        accepted (discovery.branch physical).complete).1
  have physicalRootLabel : physicalGraph.label physicalGraph.root =
      ⟨some physicalLigand, NodeProvenance.realAtom⟩ := by
    exact (discovery.branch physical).key.declarativeLabel_root_eq
      mol (centerAtom root) physicalLigand physicalRooted
  have lonePairConformance := lonePairBranchConformance
    discovery lonePair admitted lonePairSentinel
  have lonePairRootAtomless : (lonePairGraph.label lonePairGraph.root).atom? = none := by
    exact lonePairConformance.atomlessRoot
  have physicalNodeObservation :
      exactRule1aNodeObservation mol.toMoleculeGraph physicalGraph physicalAddressing
          physicalGraph.root =
        ExactAtomicNumber.ofNat (mol.toMoleculeGraph.atomZ physicalLigand) := by
    apply exactRule1aNodeObservation_nonmultiple
    · simpa [physicalGraph] using congrArg NodeLabel.atom? physicalRootLabel
    · intro distance
      rw [physicalRootLabel]
      simp
  have lonePairNodeObservation :
      exactRule1aNodeObservation mol.toMoleculeGraph lonePairGraph lonePairAddressing
          lonePairGraph.root = ExactAtomicNumber.zero :=
    exactRule1aNodeObservation_atomless mol.toMoleculeGraph lonePairGraph
      lonePairAddressing lonePairGraph.root lonePairRootAtomless
  have physicalObservation : ExactRule1aObservationAt mol.toMoleculeGraph
      physicalGraph physicalAddressing []
        (ExactAtomicNumber.ofNat (mol.toMoleculeGraph.atomZ physicalLigand)) := by
    left
    exact ⟨physicalGraph.root, physicalAddressing.root_address,
      physicalNodeObservation.symm⟩
  have lonePairObservation : ExactRule1aObservationAt mol.toMoleculeGraph
      lonePairGraph lonePairAddressing [] ExactAtomicNumber.zero := by
    left
    exact ⟨lonePairGraph.root, lonePairAddressing.root_address,
      lonePairNodeObservation.symm⟩
  have positive := mol.atomZ_positive_of_rule2MassesKnown known physicalLigand
  have rootOutcome : ExactRule1aOutcomeAt mol.toMoleculeGraph
      physicalGraph physicalAddressing lonePairGraph lonePairAddressing [] .gt := by
    refine ⟨ExactAtomicNumber.ofNat (mol.toMoleculeGraph.atomZ physicalLigand),
      ExactAtomicNumber.zero, physicalObservation, lonePairObservation, ?_⟩
    let physicalLabel : RawMolecule.CIPAtomicLabel :=
      { numerator := mol.toMoleculeGraph.atomZ physicalLigand, denominator := 1 }
    have physicalLabelPositive : 0 < physicalLabel.numerator := by
      exact positive
    have labelGt : RawMolecule.compareCIPAtomicLabel physicalLabel
        RawMolecule.zeroRule1aLabel = .gt :=
      RawMolecule.compareCIPAtomicLabel_zeroRule1aLabel_eq_gt
        physicalLabel physicalLabelPositive
    unfold ExactAtomicNumber.Outcome
    rw [LinearOrder.compare_eq_compareOfLessAndEq,
      ← show physicalLabel.toExactAtomicNumber =
          ExactAtomicNumber.ofNat (mol.toMoleculeGraph.atomZ physicalLigand) from by
            rfl,
      ← RawMolecule.zeroRule1aLabel_toExactAtomicNumber,
      ← RawMolecule.compareCIPAtomicLabel_eq_exactOutcomeValue]
    exact labelGt
  refine ⟨[], rootOutcome, ?_⟩
  intro earlier beforeRoot
  simp [HierarchyAddressBefore, HierarchyAddressKey,
    List.cons_lt_cons_iff] at beforeRoot

/-- The complete production Rules-1a--2 comparator and the independent atom-or-atomless-digraph
semantics agree for a physical ligand on the left and a lone pair on the right.  Rule 1a decides
strictly at the root, so the theorem does not assume or inspect any later-rule outcome. -/
theorem physicalBranch_exactConstitutionalComparison_lonePair
    {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (physical lonePair : Fin 4)
    (physicalLigand : Fin mol.atomCount)
    (admitted : mol.Admissible) (known : mol.Rule2MassesKnown)
    (physicalEq : physicalLigand.val = ligandAtom root physical)
    (lonePairSentinel : ligandAtom root lonePair = mol.atomCount)
    (outcome : Ordering) :
    RawMolecule.compareCanonicalBranchKeys
        (discovery.branch physical).key (discovery.branch lonePair).key = outcome ↔
      RawMolecule.ExactConstitutionalHierarchyFirstStrictOutcome mol.toMoleculeGraph
        ((discovery.branch physical).key.toDeclarativeDigraph mol)
        ((discovery.branch physical).key.declarativeAddressing mol)
        ((discovery.branch lonePair).key.toDeclarativeDigraph mol)
        ((discovery.branch lonePair).key.declarativeAddressing mol)
        outcome := by
  have rule1aGt := physicalBranch_rule1a_gt_lonePair discovery physical lonePair
    physicalLigand admitted known physicalEq lonePairSentinel
  have executableGt : RawMolecule.compareCanonicalBranchKeys
      (discovery.branch physical).key (discovery.branch lonePair).key = .gt := by
    simp [RawMolecule.compareCanonicalBranchKeys, compareLex, Ordering.byKey, rule1aGt]
  have semanticRule1aGt := physicalBranch_exactRule1aHierarchy_gt_lonePair
    discovery physical lonePair physicalLigand admitted known physicalEq lonePairSentinel
  obtain ⟨rule1b, semanticRule1b⟩ := constitutionalHierarchyOutcome_total
    mol.toMoleculeGraph .rule1bDuplicateNodeProximity
      ((discovery.branch physical).key.toDeclarativeDigraph mol)
      ((discovery.branch physical).key.declarativeAddressing mol)
      ((discovery.branch lonePair).key.toDeclarativeDigraph mol)
      ((discovery.branch lonePair).key.declarativeAddressing mol)
  obtain ⟨rule2, semanticRule2⟩ := constitutionalHierarchyOutcome_total
    mol.toMoleculeGraph .rule2AtomicMass
      ((discovery.branch physical).key.toDeclarativeDigraph mol)
      ((discovery.branch physical).key.declarativeAddressing mol)
      ((discovery.branch lonePair).key.toDeclarativeDigraph mol)
      ((discovery.branch lonePair).key.declarativeAddressing mol)
  have semanticGt : RawMolecule.ExactConstitutionalHierarchyFirstStrictOutcome
      mol.toMoleculeGraph
        ((discovery.branch physical).key.toDeclarativeDigraph mol)
        ((discovery.branch physical).key.declarativeAddressing mol)
        ((discovery.branch lonePair).key.toDeclarativeDigraph mol)
        ((discovery.branch lonePair).key.declarativeAddressing mol) .gt :=
    ⟨.gt, rule1b, rule2, semanticRule1aGt, semanticRule1b, semanticRule2,
      by rfl⟩
  constructor
  · intro executable
    have outcomeEq : outcome = .gt := executable.symm.trans executableGt
    rw [outcomeEq]
    exact semanticGt
  · intro semantic
    have outcomeEq : outcome = .gt :=
      RawMolecule.exactConstitutionalHierarchyFirstStrictOutcome_functional
        mol.toMoleculeGraph
        ((discovery.branch physical).key.toDeclarativeDigraph mol)
        ((discovery.branch physical).key.declarativeAddressing mol)
        ((discovery.branch lonePair).key.toDeclarativeDigraph mol)
        ((discovery.branch lonePair).key.declarativeAddressing mol)
        semantic semanticGt
    rw [outcomeEq]
    exact executableGt

/-- Reversing the ordered pair reverses the decisive root Rule-1a result: the lone pair's zero
observation is strictly below the positive physical-ligand observation. -/
theorem lonePair_rule1a_lt_physicalBranch
    {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (lonePair physical : Fin 4)
    (physicalLigand : Fin mol.atomCount)
    (admitted : mol.Admissible) (known : mol.Rule2MassesKnown)
    (lonePairSentinel : ligandAtom root lonePair = mol.atomCount)
    (physicalEq : physicalLigand.val = ligandAtom root physical) :
    RawMolecule.compareSparseCanonicalLayers RawMolecule.compareCIPAtomicLabel
        (discovery.branch lonePair).key.rule1a
        (discovery.branch physical).key.rule1a = .lt := by
  let physicalLabel : RawMolecule.CIPAtomicLabel :=
    { numerator := mol.atomZAt physicalLigand.val, denominator := 1 }
  have physicalLabelComputed : mol.canonicalRule1aLabelAuthoritative?
      (RawMolecule.canonicalRoot (centerAtom root).val physicalLigand.val) =
        some physicalLabel := by
    simp [physicalLabel, RawMolecule.canonicalRule1aLabelAuthoritative?,
      RawMolecule.canonicalRoot]
  have physicalComputed : branchCanonicalKeyAuthoritative? mol
      (centerAtom root).val physicalLigand.val =
        some (discovery.branch physical).key := by
    simpa [physicalEq] using (discovery.branch physical).accepted
  have physicalHead := RawMolecule.branchCanonicalKeyAuthoritative?_rule1a_head
    mol (centerAtom root).val physicalLigand.val (discovery.branch physical).key
      physicalLabel physicalComputed physicalLabelComputed
  have lonePairConformance := lonePairBranchConformance
    discovery lonePair admitted lonePairSentinel
  have physicalPositive : 0 < physicalLabel.numerator := by
    change 0 < mol.atomZAt physicalLigand.val
    rw [mol.atomZAt_eq_toMoleculeGraph_atomZ physicalLigand.val physicalLigand.isLt]
    exact mol.atomZ_positive_of_rule2MassesKnown known physicalLigand
  cases physicalRules : (discovery.branch physical).key.rule1a with
  | nil => simp [physicalRules] at physicalHead
  | cons firstSphere laterSpheres =>
      rw [physicalRules] at physicalHead
      simp only [List.head?_cons, Option.some.injEq] at physicalHead
      subst firstSphere
      rw [lonePairConformance.rule1aZero]
      change RawMolecule.compareSparseCanonicalLayers
        RawMolecule.compareCIPAtomicLabel
          [[([], RawMolecule.zeroRule1aLabel)]]
          ([([], physicalLabel)] :: laterSpheres) = .lt
      have labelLt : RawMolecule.compareCIPAtomicLabel
          RawMolecule.zeroRule1aLabel physicalLabel = .lt :=
        RawMolecule.compareCIPAtomicLabel_zeroRule1aLabel_eq_lt
          physicalLabel physicalPositive
      have entryLt : RawMolecule.compareSparseCanonicalEntry
          RawMolecule.compareCIPAtomicLabel ([], RawMolecule.zeroRule1aLabel)
            ([], physicalLabel) = .lt := by
        rw [RawMolecule.compareSparseCanonicalEntry_samePath]
        exact labelLt
      have sphereLt : RawMolecule.compareSparseCanonicalLayer
          RawMolecule.compareCIPAtomicLabel [([], RawMolecule.zeroRule1aLabel)]
            [([], physicalLabel)] = .lt := by
        unfold RawMolecule.compareSparseCanonicalLayer
        simp only [List.compareLex]
        rw [entryLt]
      simp only [RawMolecule.compareSparseCanonicalLayers, List.compareLex]
      rw [sphereLt]

/-- Independent exact Rule 1a likewise ranks the atomless lone-pair root below the physical root
at the empty semantic address. -/
theorem lonePair_exactRule1aHierarchy_lt_physicalBranch
    {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (lonePair physical : Fin 4)
    (physicalLigand : Fin mol.atomCount)
    (admitted : mol.Admissible) (known : mol.Rule2MassesKnown)
    (lonePairSentinel : ligandAtom root lonePair = mol.atomCount)
    (physicalEq : physicalLigand.val = ligandAtom root physical) :
    ExactRule1aHierarchyOutcome mol.toMoleculeGraph
        ((discovery.branch lonePair).key.toDeclarativeDigraph mol)
        ((discovery.branch lonePair).key.declarativeAddressing mol)
        ((discovery.branch physical).key.toDeclarativeDigraph mol)
        ((discovery.branch physical).key.declarativeAddressing mol) .lt := by
  let lonePairGraph := (discovery.branch lonePair).key.toDeclarativeDigraph mol
  let lonePairAddressing := (discovery.branch lonePair).key.declarativeAddressing mol
  let physicalGraph := (discovery.branch physical).key.toDeclarativeDigraph mol
  let physicalAddressing := (discovery.branch physical).key.declarativeAddressing mol
  have physicalRooted : (discovery.branch physical).key.RootedAt
      (centerAtom root).val physicalLigand.val := by
    have accepted : branchCanonicalKeyAuthoritative? mol
        (centerAtom root).val physicalLigand.val =
          some (discovery.branch physical).key := by
      simpa [physicalEq] using (discovery.branch physical).accepted
    exact (mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
      (centerAtom root).val physicalLigand.val (discovery.branch physical).key
        accepted (discovery.branch physical).complete).1
  have physicalRootLabel : physicalGraph.label physicalGraph.root =
      ⟨some physicalLigand, NodeProvenance.realAtom⟩ := by
    exact (discovery.branch physical).key.declarativeLabel_root_eq
      mol (centerAtom root) physicalLigand physicalRooted
  have lonePairConformance := lonePairBranchConformance
    discovery lonePair admitted lonePairSentinel
  have lonePairRootAtomless : (lonePairGraph.label lonePairGraph.root).atom? = none :=
    lonePairConformance.atomlessRoot
  have lonePairNodeObservation :
      exactRule1aNodeObservation mol.toMoleculeGraph lonePairGraph lonePairAddressing
          lonePairGraph.root = ExactAtomicNumber.zero :=
    exactRule1aNodeObservation_atomless mol.toMoleculeGraph lonePairGraph
      lonePairAddressing lonePairGraph.root lonePairRootAtomless
  have physicalNodeObservation :
      exactRule1aNodeObservation mol.toMoleculeGraph physicalGraph physicalAddressing
          physicalGraph.root =
        ExactAtomicNumber.ofNat (mol.toMoleculeGraph.atomZ physicalLigand) := by
    apply exactRule1aNodeObservation_nonmultiple
    · simpa [physicalGraph] using congrArg NodeLabel.atom? physicalRootLabel
    · intro distance
      rw [physicalRootLabel]
      simp
  have lonePairObservation : ExactRule1aObservationAt mol.toMoleculeGraph
      lonePairGraph lonePairAddressing [] ExactAtomicNumber.zero := by
    left
    exact ⟨lonePairGraph.root, lonePairAddressing.root_address,
      lonePairNodeObservation.symm⟩
  have physicalObservation : ExactRule1aObservationAt mol.toMoleculeGraph
      physicalGraph physicalAddressing []
        (ExactAtomicNumber.ofNat (mol.toMoleculeGraph.atomZ physicalLigand)) := by
    left
    exact ⟨physicalGraph.root, physicalAddressing.root_address,
      physicalNodeObservation.symm⟩
  have positive := mol.atomZ_positive_of_rule2MassesKnown known physicalLigand
  have rootOutcome : ExactRule1aOutcomeAt mol.toMoleculeGraph
      lonePairGraph lonePairAddressing physicalGraph physicalAddressing [] .lt := by
    refine ⟨ExactAtomicNumber.zero,
      ExactAtomicNumber.ofNat (mol.toMoleculeGraph.atomZ physicalLigand),
      lonePairObservation, physicalObservation, ?_⟩
    let physicalLabel : RawMolecule.CIPAtomicLabel :=
      { numerator := mol.toMoleculeGraph.atomZ physicalLigand, denominator := 1 }
    have physicalLabelPositive : 0 < physicalLabel.numerator := positive
    have labelLt : RawMolecule.compareCIPAtomicLabel RawMolecule.zeroRule1aLabel
        physicalLabel = .lt :=
      RawMolecule.compareCIPAtomicLabel_zeroRule1aLabel_eq_lt
        physicalLabel physicalLabelPositive
    unfold ExactAtomicNumber.Outcome
    rw [LinearOrder.compare_eq_compareOfLessAndEq,
      ← RawMolecule.zeroRule1aLabel_toExactAtomicNumber,
      ← show physicalLabel.toExactAtomicNumber =
          ExactAtomicNumber.ofNat (mol.toMoleculeGraph.atomZ physicalLigand) from by
            rfl,
      ← RawMolecule.compareCIPAtomicLabel_eq_exactOutcomeValue]
    exact labelLt
  refine ⟨[], rootOutcome, ?_⟩
  intro earlier beforeRoot
  simp [HierarchyAddressBefore, HierarchyAddressKey,
    List.cons_lt_cons_iff] at beforeRoot

/-- Complete constitutional conformance for the reversed mixed ordered pair. -/
theorem lonePair_exactConstitutionalComparison_physicalBranch
    {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (lonePair physical : Fin 4)
    (physicalLigand : Fin mol.atomCount)
    (admitted : mol.Admissible) (known : mol.Rule2MassesKnown)
    (lonePairSentinel : ligandAtom root lonePair = mol.atomCount)
    (physicalEq : physicalLigand.val = ligandAtom root physical)
    (outcome : Ordering) :
    RawMolecule.compareCanonicalBranchKeys
        (discovery.branch lonePair).key (discovery.branch physical).key = outcome ↔
      RawMolecule.ExactConstitutionalHierarchyFirstStrictOutcome mol.toMoleculeGraph
        ((discovery.branch lonePair).key.toDeclarativeDigraph mol)
        ((discovery.branch lonePair).key.declarativeAddressing mol)
        ((discovery.branch physical).key.toDeclarativeDigraph mol)
        ((discovery.branch physical).key.declarativeAddressing mol)
        outcome := by
  have rule1aLt := lonePair_rule1a_lt_physicalBranch discovery lonePair physical
    physicalLigand admitted known lonePairSentinel physicalEq
  have executableLt : RawMolecule.compareCanonicalBranchKeys
      (discovery.branch lonePair).key (discovery.branch physical).key = .lt := by
    simp [RawMolecule.compareCanonicalBranchKeys, compareLex, Ordering.byKey, rule1aLt]
  have semanticRule1aLt := lonePair_exactRule1aHierarchy_lt_physicalBranch
    discovery lonePair physical physicalLigand admitted known lonePairSentinel physicalEq
  obtain ⟨rule1b, semanticRule1b⟩ := constitutionalHierarchyOutcome_total
    mol.toMoleculeGraph .rule1bDuplicateNodeProximity
      ((discovery.branch lonePair).key.toDeclarativeDigraph mol)
      ((discovery.branch lonePair).key.declarativeAddressing mol)
      ((discovery.branch physical).key.toDeclarativeDigraph mol)
      ((discovery.branch physical).key.declarativeAddressing mol)
  obtain ⟨rule2, semanticRule2⟩ := constitutionalHierarchyOutcome_total
    mol.toMoleculeGraph .rule2AtomicMass
      ((discovery.branch lonePair).key.toDeclarativeDigraph mol)
      ((discovery.branch lonePair).key.declarativeAddressing mol)
      ((discovery.branch physical).key.toDeclarativeDigraph mol)
      ((discovery.branch physical).key.declarativeAddressing mol)
  have semanticLt : RawMolecule.ExactConstitutionalHierarchyFirstStrictOutcome
      mol.toMoleculeGraph
        ((discovery.branch lonePair).key.toDeclarativeDigraph mol)
        ((discovery.branch lonePair).key.declarativeAddressing mol)
        ((discovery.branch physical).key.toDeclarativeDigraph mol)
        ((discovery.branch physical).key.declarativeAddressing mol) .lt :=
    ⟨.lt, rule1b, rule2, semanticRule1aLt, semanticRule1b, semanticRule2,
      by rfl⟩
  constructor
  · intro executable
    have outcomeEq : outcome = .lt := executable.symm.trans executableLt
    rw [outcomeEq]
    exact semanticLt
  · intro semantic
    have outcomeEq : outcome = .lt :=
      RawMolecule.exactConstitutionalHierarchyFirstStrictOutcome_functional
        mol.toMoleculeGraph
        ((discovery.branch lonePair).key.toDeclarativeDigraph mol)
        ((discovery.branch lonePair).key.declarativeAddressing mol)
        ((discovery.branch physical).key.toDeclarativeDigraph mol)
        ((discovery.branch physical).key.declarativeAddressing mol)
        semantic semanticLt
    rw [outcomeEq]
    exact executableLt

/-- Two lone-pair slots at one discovered center compare equal both executably and under the
independent atomless-node Rules-1a--2 hierarchy semantics. -/
theorem lonePairBranches_exactConstitutionalComparison
    {mol : RawMolecule} {root : Root mol}
    (discovery : CenterDiscovery mol root) (left right : Fin 4)
    (admitted : mol.Admissible)
    (leftSentinel : ligandAtom root left = mol.atomCount)
    (rightSentinel : ligandAtom root right = mol.atomCount)
    (outcome : Ordering) :
    RawMolecule.compareCanonicalBranchKeys
        (discovery.branch left).key (discovery.branch right).key = outcome ↔
      RawMolecule.ExactConstitutionalHierarchyFirstStrictOutcome mol.toMoleculeGraph
        ((discovery.branch left).key.toDeclarativeDigraph mol)
        ((discovery.branch left).key.declarativeAddressing mol)
        ((discovery.branch right).key.toDeclarativeDigraph mol)
        ((discovery.branch right).key.declarativeAddressing mol)
        outcome := by
  have leftConformance := lonePairBranchConformance
    discovery left admitted leftSentinel
  have rightConformance := lonePairBranchConformance
    discovery right admitted rightSentinel
  have keyEq : (discovery.branch left).key = (discovery.branch right).key :=
    leftConformance.exactKey.trans rightConformance.exactKey.symm
  have independentEq :
      RawMolecule.ExactConstitutionalHierarchyFirstStrictOutcome mol.toMoleculeGraph
        ((discovery.branch left).key.toDeclarativeDigraph mol)
        ((discovery.branch left).key.declarativeAddressing mol)
        ((discovery.branch right).key.toDeclarativeDigraph mol)
        ((discovery.branch right).key.declarativeAddressing mol)
        .eq := by
    rw [← keyEq]
    exact RawMolecule.exactConstitutionalHierarchyFirstStrictOutcome_refl
      mol.toMoleculeGraph
      ((discovery.branch left).key.toDeclarativeDigraph mol)
      ((discovery.branch left).key.declarativeAddressing mol)
  constructor
  · intro executable
    have outcomeEq : outcome = .eq := by
      rw [keyEq, RawMolecule.compareCanonicalBranchKeys_self] at executable
      exact executable.symm
    rw [outcomeEq]
    exact independentEq
  · intro independent
    have outcomeEq : outcome = .eq :=
      RawMolecule.exactConstitutionalHierarchyFirstStrictOutcome_functional
        mol.toMoleculeGraph
        ((discovery.branch left).key.toDeclarativeDigraph mol)
        ((discovery.branch left).key.declarativeAddressing mol)
        ((discovery.branch right).key.toDeclarativeDigraph mol)
        ((discovery.branch right).key.declarativeAddressing mol)
        independent independentEq
    rw [outcomeEq]
    rw [keyEq]
    exact RawMolecule.compareCanonicalBranchKeys_self _

/-- Every final-center ligand slot selected from an exact written-neighbor view is either a real
atom index or precisely the distinguished one-past-the-end lone-pair sentinel.  There is no third
auxiliary or malformed index case at the checked stereochemical boundary. -/
theorem ligandAtom_lt_or_eq_atomCount_of_writtenNeighborExact
    {mol : RawMolecule} (root : Root mol) (slot : Fin 4)
    (exact : mol.WrittenNeighborExact) :
    ligandAtom root slot < mol.atomCount ∨ ligandAtom root slot = mol.atomCount := by
  by_cases sentinel : ligandAtom root slot = mol.atomCount
  · exact Or.inr sentinel
  · left
    have written : ligandAtom root slot ∈
        mol.writtenNeighbors (centerAtom root).val :=
      mem_writtenNeighbors_of_mem_ligandsWithLonePair_of_ne mol
        (centerAtom root).val (ligandAtom root slot) (ligandAtom_mem root slot) sentinel
    exact (RawMolecule.WrittenNeighborExact.at mol exact (centerAtom root)).2.1
      (ligandAtom root slot) written

/-- Exact independent constitutional comparison of every ordered pair of discovered ligand
slots, including physical/physical, physical/lone-pair, lone-pair/physical, and lone-pair/lone-pair
cases. -/
structure ExactConstitutionalAllSlotCenterHierarchy
    {mol : RawMolecule} {root : Root mol} (discovery : CenterDiscovery mol root) : Prop where
  comparison : ∀ (left right : Fin 4) (outcome : Ordering),
    RawMolecule.compareCanonicalBranchKeys
        (discovery.branch left).key (discovery.branch right).key = outcome ↔
      RawMolecule.ExactConstitutionalHierarchyFirstStrictOutcome mol.toMoleculeGraph
        ((discovery.branch left).key.toDeclarativeDigraph mol)
        ((discovery.branch left).key.declarativeAddressing mol)
        ((discovery.branch right).key.toDeclarativeDigraph mol)
        ((discovery.branch right).key.declarativeAddressing mol)
        outcome

/-- Checked stereochemical admission and Rule-2 source coverage prove the exact Rules-1a--2
theorem for all sixteen ordered ligand-slot pairs at one discovered tetrahedral center. -/
theorem exactConstitutionalAllSlotCenterHierarchy
    {mol : RawMolecule} {root : Root mol} (discovery : CenterDiscovery mol root)
    (admitted : mol.StereochemicalAdmissible) (known : mol.Rule2MassesKnown) :
    ExactConstitutionalAllSlotCenterHierarchy discovery where
  comparison := by
    intro left right outcome
    rcases ligandAtom_lt_or_eq_atomCount_of_writtenNeighborExact
        root left admitted.2 with leftPhysical | leftSentinel
    · let leftLigand : Fin mol.atomCount := ⟨ligandAtom root left, leftPhysical⟩
      rcases ligandAtom_lt_or_eq_atomCount_of_writtenNeighborExact
          root right admitted.2 with rightPhysical | rightSentinel
      · let rightLigand : Fin mol.atomCount := ⟨ligandAtom root right, rightPhysical⟩
        exact (exactConstitutionalCenterHierarchy discovery admitted.1 known).comparison
          left right leftLigand rightLigand rfl rfl outcome
      · exact physicalBranch_exactConstitutionalComparison_lonePair
          discovery left right leftLigand admitted.1 known rfl rightSentinel outcome
    · rcases ligandAtom_lt_or_eq_atomCount_of_writtenNeighborExact
          root right admitted.2 with rightPhysical | rightSentinel
      · let rightLigand : Fin mol.atomCount := ⟨ligandAtom root right, rightPhysical⟩
        exact lonePair_exactConstitutionalComparison_physicalBranch
          discovery left right rightLigand admitted.1 known leftSentinel rfl outcome
      · exact lonePairBranches_exactConstitutionalComparison
          discovery left right admitted.1 leftSentinel rightSentinel outcome

end AuthoritativeCIPDiscovery

namespace BlueBookP92.Digraph

/-- Molecule-wide exact constitutional refinement over every discovered ligand slot.  Physical
slots retain faithful molecular expansion, while the lone-pair slot is the proved one-node
atomless digraph and participates in the same independent Rules-1a--2 relation. -/
structure AuthoritativeExactAllSlotConstitutionalMoleculeConformance
    (mol : RawMolecule) (discovery : AuthoritativeCIPDiscovery.Discovery mol) : Prop where
  moleculeDigraph : AuthoritativeMoleculeConformance mol discovery
  constitutionalAllSlotHierarchies : ∀ root : Root mol,
    AuthoritativeCIPDiscovery.ExactConstitutionalAllSlotCenterHierarchy
      (discovery.center root)

end BlueBookP92.Digraph

namespace AuthoritativeCIPDiscovery.Discovery

/-- The exact molecule-level Rules-1a--2 theorem now covers all discovered physical and lone-pair
slots, not merely pairs admitting two `Fin atomCount` witnesses. -/
theorem exactAllSlotConstitutionalMoleculeConformance_of_stereochemicalAdmissible
    {mol : RawMolecule} (discovery : AuthoritativeCIPDiscovery.Discovery mol)
    (admitted : mol.StereochemicalAdmissible) (known : mol.Rule2MassesKnown) :
    BlueBookP92.Digraph.AuthoritativeExactAllSlotConstitutionalMoleculeConformance
      mol discovery where
  moleculeDigraph := discovery.moleculeConformance_of_stereochemicalAdmissible admitted
  constitutionalAllSlotHierarchies := fun root =>
    AuthoritativeCIPDiscovery.exactConstitutionalAllSlotCenterHierarchy
      (discovery.center root) admitted known

end AuthoritativeCIPDiscovery.Discovery

end TetraStereo.OneCenter
