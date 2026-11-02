import TetraStereo.OneCenter.CIPAuthoritativeRule1aSoundness
import TetraStereo.OneCenter.CIPAuthoritativeSourceDensity
import TetraStereo.OneCenter.CIPAuthoritativeSourceTreeAlignment
import TetraStereo.OneCenter.ProductionCIPRule1aUniformFallbackSoundness

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

open DeclarativeCIP

namespace Element

/-- Every parser element other than the explicitly nonchemical wildcard has positive atomic
number. -/
theorem atomicNumber_pos_of_ne_wildcard (element : Element)
    (real : element ≠ .wildcard) : 0 < element.atomicNumber := by
  cases element <;> simp_all [Element.atomicNumber]

end Element

namespace RawMolecule

/-- Source-backed Rule-2 admission excludes wildcard atoms and therefore proves positive atomic
number for every real parsed atom. -/
theorem atomZ_positive_of_rule2MassesKnown
    (mol : RawMolecule) (known : mol.Rule2MassesKnown)
    (atom : Fin mol.atomCount) : 0 < mol.toMoleculeGraph.atomZ atom := by
  let spec := mol.atoms.get atom
  have membership : spec ∈ mol.atoms := List.get_mem mol.atoms atom
  obtain ⟨mass, massKnown⟩ := known spec membership
  have real : spec.element ≠ .wildcard := by
    intro wildcard
    rw [wildcard] at massKnown
    simp [rule2MassPico?] at massKnown
  exact Element.atomicNumber_pos_of_ne_wildcard spec.element real

/-- A successful uncapped general mancude label on a written localized double bond has positive
numerator whenever every real atomic number is positive.  The proof uses the written Kekulé
matching as a member of the independently realized maximum-matching family. -/
theorem generalMancudeRule1aLabelAuthoritative?_numerator_pos
    (mol : RawMolecule) (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique) (attached duplicated : Fin mol.atomCount)
    (hlocalized : mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated)
    (hdouble : mol.bondOrder attached.val duplicated.val = 2)
    (atomsPositive : ∀ atom : Fin mol.atomCount,
      0 < mol.toMoleculeGraph.atomZ atom)
    (label : CIPAtomicLabel)
    (hlabel : mol.generalMancudeRule1aLabelAuthoritative?
      attached.val duplicated.val = some label) :
    0 < label.numerator := by
  classical
  let edges := mol.localizedMancudeComponentEdges attached.val
  let written := edges.filter fun edge => mol.bondOrder edge.1 edge.2 == 2
  let stats := mol.exhaustiveMancudeMatchingStats attached.val edges
  have hstatsCall := mol.mancudeMatchingStats_length_succ attached.val edges
  unfold generalMancudeRule1aLabelAuthoritative? at hlabel
  change (if !((mol.localizedMancudeComponentVertices attached.val).contains duplicated.val) ||
      edges.isEmpty then none
    else do
      let observed ← mol.mancudeMatchingStats attached.val (edges.length + 1) edges
      if observed.size != written.length || observed.count == 0 then none
      else some { numerator := observed.partnerZSum, denominator := observed.count }) =
        some label at hlabel
  split at hlabel <;> rename_i hguard
  · contradiction
  · rw [hstatsCall] at hlabel
    simp only [instMonadOption, Option.bind_some] at hlabel
    split at hlabel <;> rename_i hsupported
    · contradiction
    · have labelEq : label =
          { numerator := stats.partnerZSum, denominator := stats.count } := by
        exact Option.some.inj hlabel.symm
      subst label
      have supportedFalse : (stats.size != written.length || stats.count == 0) = false :=
        Bool.eq_false_of_not_eq_true hsupported
      have sizeEq : stats.size = written.length := by
        have := (Bool.or_eq_false_iff.mp supportedFalse).1
        simpa using this
      have realization := mol.localizedMancudeComponentEdges_realization
        hwellFormed hunique attached
      have writtenMatching : IsMancudeEdgeMatching written edges := by
        simpa [edges, written] using
          mol.writtenMancudeEdges_isMatching hwellFormed hunique attached
      have attachedComponent : mol.toMoleculeGraph.InMancudeComponent attached attached :=
        Relation.ReflTransGen.refl
      have componentMatched : NatEdgeMatchedBy edges attached duplicated :=
        (realization.localizedComponent_iff attached duplicated).2
          ⟨hlocalized, attachedComponent⟩
      have writtenMatched : NatEdgeMatchedBy written attached duplicated := by
        rcases componentMatched with ⟨edge, edgePresent, incident⟩
        refine ⟨edge, List.mem_filter.2 ⟨edgePresent, ?_⟩, incident⟩
        simp only [beq_iff_eq]
        rcases incident with forward | reverse
        · have edgeEq : edge = (attached.val, duplicated.val) := forward
          simpa [edgeEq] using hdouble
        · have edgeEq : edge = (duplicated.val, attached.val) := reverse
          simpa [edgeEq, mol.bondOrder_symm] using hdouble
      have statsSize : stats.size =
          mancudeFamilyMaximumSize (exhaustiveMancudeEdgeMatchings edges) := by
        dsimp only [stats]
        rw [mol.exhaustiveMancudeMatchingStats_eq_edgeMatchingFamilyStats
          attached.val edges]
        rfl
      have writtenMaximum : IsMaximumMancudeEdgeMatching written edges := by
        apply (mem_maximum_exhaustiveMancudeEdgeMatchings_iff edges written).1
        unfold maximumMancudeEdgeMatchings
        apply List.mem_filter.2
        constructor
        · exact (mem_exhaustiveMancudeEdgeMatchings_iff edges written).2 writtenMatching
        · simp only [decide_eq_true_eq]
          rw [← statsSize, sizeEq]
      let writtenPartner := partnerOfMancudeEdgeMatching
        (atomCount := mol.atomCount) written
      have partnerMaximum :
          mol.toMoleculeGraph.IsMaximumMancudeMatching attached writtenPartner :=
        (partnerOfMancudeEdgeMatching_isMaximum_iff mol attached edges written
          realization writtenMatching).2 writtenMaximum
      have partnerPresent : writtenPartner ∈
          mol.toMoleculeGraph.maximumMancudeMatchings attached := by
        simp only [MoleculeGraph.maximumMancudeMatchings, Finset.mem_filter,
          Finset.mem_univ, true_and]
        exact partnerMaximum
      have writtenBounds : ∀ edge ∈ written,
          edge.1 < mol.atomCount ∧ edge.2 < mol.atomCount := by
        intro edge edgePresent
        exact realization.endpointsInBounds edge
          (List.filter_sublist.subset edgePresent)
      have writtenLoops : ∀ edge ∈ written, edge.1 ≠ edge.2 := by
        intro edge edgePresent
        exact realization.noSelfEdges edge (List.filter_sublist.subset edgePresent)
      have attachedPartner : writtenPartner attached = some duplicated :=
        (partnerOfMancudeEdgeMatching_eq_some_iff written writtenMatching.2
          writtenLoops attached duplicated).2 writtenMatched
      have contributionPositive : 0 <
          mol.toMoleculeGraph.mancudePartnerAtomicNumber attached writtenPartner := by
        simp [MoleculeGraph.mancudePartnerAtomicNumber, attachedPartner,
          atomsPositive duplicated]
      have contributionLe :
          mol.toMoleculeGraph.mancudePartnerAtomicNumber attached writtenPartner ≤
            (mol.toMoleculeGraph.maximumMancudeMatchings attached).sum
              (mol.toMoleculeGraph.mancudePartnerAtomicNumber attached) := by
        exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) partnerPresent
      have independentPositive : 0 <
          (mol.toMoleculeGraph.maximumMancudeMatchings attached).sum
            (mol.toMoleculeGraph.mancudePartnerAtomicNumber attached) :=
        contributionPositive.trans_le contributionLe
      have statsSum := mol.componentExhaustiveStats_partnerZSum_eq_independent_sum
        hwellFormed hunique attached
      dsimp only [stats]
      rw [statsSum]
      exact independentPositive

/-- A generated multiple-bond duplicate can only come from a raw bond of order at least two. -/
theorem canonicalChildren_multipleBondDuplicate_bondOrder_ge_two
    (mol : RawMolecule) (parent child : CanonicalBranchNode)
    (parentHead : parent.history.head? = some parent.atom)
    (childPresent : child ∈ mol.canonicalChildren parent)
    (distance : ℕ)
    (provenance : child.provenance =
      CanonicalNodeProvenance.multipleBondDuplicate distance) :
    2 ≤ mol.bondOrder parent.atom child.atom := by
  unfold canonicalChildren at childPresent
  by_cases forced : parent.forcedLeaf
  · simp [forced] at childPresent
  · simp only [forced, Bool.false_eq_true, ↓reduceIte, List.mem_map] at childPresent
    rcases childPresent with ⟨copy, copyPresent, rfl⟩
    by_cases nonzero : copy.2 != 0
    · rcases mol.canonicalChildCopies_source parent copy copyPresent with
        ⟨bond, bondPresent, endpoints, copyBound⟩
      have canonicalTwo : 2 ≤ mol.canonicalBondOrder parent copy.1 := by
        have copyPositive : 0 < copy.2 := by
          exact Nat.zero_lt_of_ne_zero (by simpa using nonzero)
        omega
      unfold canonicalBondOrder at canonicalTwo
      cases historyEq : parent.history with
      | nil => simp [historyEq] at parentHead
      | cons current history =>
          cases history with
          | nil => simpa [historyEq] using canonicalTwo
          | cons center rest =>
              cases rest with
              | nil =>
                  by_cases suppressed : copy.1 == center &&
                      mol.isTrigonalPyramidalOxidoRootEdge center current
                  · simp [historyEq, suppressed] at canonicalTwo
                  · simpa [historyEq, suppressed] using canonicalTwo
              | cons another rest => simpa [historyEq] using canonicalTwo
    · have nonzeroFalse : (copy.2 != 0) = false :=
        Bool.eq_false_of_not_eq_true nonzero
      by_cases ring : copy.1 ∈ parent.history
      · simp [nonzeroFalse, ring] at provenance
      · simp [nonzeroFalse, ring] at provenance

/-- Every realized source in an exact compiler hierarchy is non-phantom. -/
theorem CanonicalBranchKey.source_provenance_ne_phantom
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (sourceAt : key.sourceNodeAtAddress? node.1 = some source)
    (distance : ℕ) :
    source.provenance ≠ CanonicalNodeProvenance.phantom distance := by
  by_cases rootNode : node = (key.toDeclarativeDigraph mol).root
  · have addressRoot : node.1 = [] := congrArg Subtype.val rootNode
    have sourceRoot : source = canonicalRoot center ligand := by
      apply Option.some.inj
      exact sourceAt.symm.trans (by simpa [addressRoot] using hroot)
    subst source
    simp [canonicalRoot]
  · obtain ⟨parent, childEdge, _⟩ :=
      (key.declarativeAddressing mol).existsUnique_parent node rootNode
    change key.HierarchyChild parent node at childEdge
    have complete := key.sourceComplete_of_root_and_childrenExact mol
      (canonicalRoot center ligand) hroot hexact
    rcases complete parent with ⟨parentSource, parentAt⟩
    have generated := key.childrenSound_of_childrenExact mol hexact
      parent node parentSource source childEdge parentAt sourceAt
    exact mol.canonicalChildren_provenance_ne_phantom
      parentSource source generated distance

/-- A realized multiple-bond source is attached through a raw double bond.  Localization limits
the bond to order one or two, while duplicate construction proves it is at least two. -/
theorem CanonicalBranchKey.multiple_source_localized_bondOrder_eq_two
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (sourceAt : key.sourceNodeAtAddress? node.1 = some source)
    (distance : ℕ)
    (provenance : source.provenance =
      CanonicalNodeProvenance.multipleBondDuplicate distance)
    (attached duplicated : Fin mol.atomCount)
    (attachedEq : attached.val = source.parent)
    (duplicatedEq : duplicated.val = source.atom)
    (localized : mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated) :
    mol.bondOrder attached.val duplicated.val = 2 := by
  have notRoot : node ≠ (key.toDeclarativeDigraph mol).root := by
    intro rootNode
    have addressRoot : node.1 = [] := congrArg Subtype.val rootNode
    have sourceRoot : source = canonicalRoot center ligand := by
      apply Option.some.inj
      exact sourceAt.symm.trans (by simpa [addressRoot] using hroot)
    subst source
    simp [canonicalRoot] at provenance
  obtain ⟨parent, childEdge, _⟩ :=
    (key.declarativeAddressing mol).existsUnique_parent node notRoot
  change key.HierarchyChild parent node at childEdge
  have complete := key.sourceComplete_of_root_and_childrenExact mol
    (canonicalRoot center ligand) hroot hexact
  rcases complete parent with ⟨parentSource, parentAt⟩
  have generated := key.childrenSound_of_childrenExact mol hexact
    parent node parentSource source childEdge parentAt sourceAt
  have parentEq := mol.canonicalChildren_parent_eq parentSource source generated
  have parentCoherent := key.sourceCoherent_of_root_and_childrenExact
    mol center ligand hwellFormed hroot hexact parent parentSource parentAt
  have rawTwo := mol.canonicalChildren_multipleBondDuplicate_bondOrder_ge_two
    parentSource source parentCoherent.1 generated distance provenance
  have candidate := localized.1.1
  change (mol.bondOrder attached.val duplicated.val = 1 ∨
      mol.bondOrder attached.val duplicated.val = 2) at candidate
  rw [attachedEq, duplicatedEq] at candidate ⊢
  rw [parentEq] at candidate ⊢
  rcases candidate with candidate | candidate
  · have impossible := rawTwo
    rw [candidate] at impossible
    simp at impossible
  · exact candidate

/-- Every authoritative Rule-1a label retained at a realized exact source node has positive
numerator once the source molecule has passed Rule-2 mass admission.  This is the chemical fact
which makes a missing sparse observation (declarative value zero) strictly lower than every
present observation. -/
theorem CanonicalBranchKey.authoritativeRule1aLabel_numerator_pos
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (known : mol.Rule2MassesKnown)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (sourceAt : key.sourceNodeAtAddress? node.1 = some source)
    (label : CIPAtomicLabel)
    (labelAt : mol.canonicalRule1aLabelAuthoritative? source = some label) :
    0 < label.numerator := by
  have coherent := key.sourceCoherent_of_root_and_childrenExact
    mol center ligand hwellFormed hroot hexact node source sourceAt
  cases provenance : source.provenance with
  | phantom distance =>
      exact (key.source_provenance_ne_phantom mol center ligand hroot hexact
        node source sourceAt distance provenance).elim
  | realAtom | ringDuplicate =>
      have sourceBound : source.atom < mol.atomCount := by
        simpa [provenance] using coherent.2
      have sourcePositive : 0 < mol.atomZAt source.atom := by
        rw [mol.atomZAt_eq_toMoleculeGraph_atomZ source.atom sourceBound]
        exact mol.atomZ_positive_of_rule2MassesKnown known ⟨source.atom, sourceBound⟩
      simp [canonicalRule1aLabelAuthoritative?, provenance] at labelAt
      subst label
      exact sourcePositive
  | multipleBondDuplicate distance =>
      obtain ⟨attached, duplicated, attachedEq, duplicatedEq, _⟩ :=
        key.exactRule1aNodeObservation_eq_exactMultipleBond_of_source
          mol center ligand hwellFormed hroot hexact node source sourceAt distance provenance
      have duplicatedPositive : 0 < mol.atomZAt duplicated.val := by
        rw [mol.atomZAt_eq_toMoleculeGraph_atomZ duplicated.val duplicated.isLt]
        exact mol.atomZ_positive_of_rule2MassesKnown known duplicated
      have dispatcher : mol.mancudeRule1aLabelAuthoritative?
          attached.val duplicated.val = some label := by
        unfold canonicalRule1aLabelAuthoritative? at labelAt
        rw [provenance] at labelAt
        simpa [attachedEq, duplicatedEq] using labelAt
      by_cases raw : containsUndirectedEdge mol.localizedMancudeEdges
          attached.val duplicated.val = true
      · have localized : mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated :=
          (mol.containsUndirectedEdge_localizedMancudeEdges_iff
            hwellFormed hunique attached duplicated).1 raw
        cases cycleResult : mol.simpleMancudeCycle? attached.val duplicated.val with
        | none =>
            have general : mol.generalMancudeRule1aLabelAuthoritative?
                attached.val duplicated.val = some label := by
              unfold mancudeRule1aLabelAuthoritative? at dispatcher
              simpa [raw, cycleResult] using dispatcher
            have double := key.multiple_source_localized_bondOrder_eq_two
              mol center ligand hwellFormed hroot hexact node source sourceAt distance
                provenance attached duplicated attachedEq duplicatedEq localized
            exact mol.generalMancudeRule1aLabelAuthoritative?_numerator_pos
              hwellFormed hunique attached duplicated localized double
                (mol.atomZ_positive_of_rule2MassesKnown known) label general
        | some cycleData =>
            rcases cycleData with ⟨cycle, alternate⟩
            have labelEq : label =
                mol.simpleMancudeCycleLabel duplicated.val alternate cycle := by
              unfold mancudeRule1aLabelAuthoritative? at dispatcher
              simp only [raw, Bool.not_true, Bool.false_eq_true, if_false,
                cycleResult, Option.some.injEq] at dispatcher
              exact dispatcher.symm
            subst label
            have certificate := mol.simpleMancudeCycle?_certificate
              attached.val duplicated.val cycle alternate cycleResult
            have cycleLength : 3 ≤ cycle.length := by
              rcases certificate.shape with ⟨rest, rfl⟩
              simp
            unfold simpleMancudeCycleLabel
            split <;> rename_i parity
            · simp only
              exact Nat.add_pos_left duplicatedPositive _
            · simp only
              exact Nat.mul_pos (by omega) (Nat.add_pos_left duplicatedPositive _)
      · have rawFalse : containsUndirectedEdge mol.localizedMancudeEdges
            attached.val duplicated.val = false := Bool.eq_false_of_not_eq_true raw
        unfold mancudeRule1aLabelAuthoritative? at dispatcher
        simp only [rawFalse, Bool.not_false, if_true,
          Option.some.injEq] at dispatcher
        subst label
        exact duplicatedPositive

/-- Every sparse Rule-1a entry emitted by a successful complete authoritative branch compiler is
strictly positive on a mass-admitted chemical input. -/
theorem branchCanonicalKeyAuthoritative?_rule1a_numerator_pos
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (admitted : mol.Admissible)
    (known : mol.Rule2MassesKnown)
    (computed : branchCanonicalKeyAuthoritative?
      mol center.val ligand.val = some key)
    (complete : key.complete = true) :
    ∀ layer, layer ∈ key.rule1a → ∀ entry, entry ∈ layer →
      0 < entry.2.numerator := by
  have sourceAligned := mol.branchCanonicalKeyAuthoritative?_sourceAligned
    center.val ligand.val key computed
  obtain ⟨tree, treeAligned⟩ :=
    mol.branchCanonicalKeyAuthoritative?_sourceTreeAligned
      center.val ligand.val key computed
  have structural := mol.branchCanonicalKeyAuthoritative?_rootedAt_childrenExact
    center.val ligand.val key computed complete
  intro layer layerPresent entry entryPresent
  rw [sourceAligned.1] at layerPresent
  simp only [mapCanonicalSourceLayers, List.mem_map] at layerPresent
  rcases layerPresent with ⟨sourceLayer, sourceLayerPresent, rfl⟩
  simp only [List.mem_map] at entryPresent
  rcases entryPresent with ⟨sourceEntry, sourceEntryPresent, rfl⟩
  rcases sourceEntry with ⟨address, source⟩
  have sourceFlat : (address, source) ∈ key.sourceNodes.flatten :=
    List.mem_flatten.mpr ⟨sourceLayer, sourceLayerPresent, sourceEntryPresent⟩
  have sourceAt : key.sourceNodeAtAddress? address = some source :=
    (treeAligned.mem_flatten_iff_sourceNodeAtAddress key tree address source).mp sourceFlat
  have treeOccurrence : (address, source) ∈ tree.occurrences :=
    (treeAligned.2 (address, source)).mp sourceFlat
  have addressPresent : address ∈ key.hierarchyAddresses :=
    (key.mem_hierarchyAddresses_iff_tree_occurrence tree treeAligned.1 address).2
      ⟨source, treeOccurrence⟩
  let node : key.HierarchyNode := ⟨address, addressPresent⟩
  obtain ⟨label, labelAt⟩ :=
    mol.branchCanonicalKeyAuthoritative?_rule1aLabelSupportedAt
      center.val ligand.val key computed complete address source sourceAt
  have positive := key.authoritativeRule1aLabel_numerator_pos
    mol center ligand admitted.1 admitted.2 structural.1 structural.2 known
      node source sourceAt label labelAt
  simpa [canonicalRule1aLabelAuthoritativeTotal, labelAt] using positive

end RawMolecule

end

end TetraStereo.OneCenter
