import TetraStereo.UniversalProof.RuntimeLegacyClassifierClosureProofs.RuntimeLegacyClassifierClosure

set_option autoImplicit false

namespace TetraStereo.UniversalProof.IsotopeSourcePublicDescriptorRecoveryProofs.IsotopeSourcePublicDescriptorRecovery

open TetraStereo.OneCenter TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput.SingleWedgeSource
open TetraStereo.OneCenter.AuthoritativeCIPMoleculeCursorRanking
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
open TetraStereo.UniversalProof.NativeSourcePhysicalCoordinatesProofs.RuntimeSourceDescriptorAlignment
open TetraStereo.UniversalProof.RuntimeOccurrenceFactRecoveryProofs.RuntimeOccurrenceFactRecovery
open TetraStereo.UniversalProof.RuntimeSourcePublicPipelineRecoveryProofs.RuntimeSourcePublicPipelineRecovery
open TetraStereo.UniversalProof.SourceNativeRawAnnotationAgreementProofs.SourceNativeRawAnnotationAgreement
open TetraStereo.UniversalProof.SourceNativeParserOccurrenceAlignmentProofs.SourceNativeParserOccurrenceAlignment
open TetraStereo.UniversalProof.SourceNativeRichParserWitnessProofs.SourceNativeRichParserOccurrence
open TetraStereo.UniversalProof.SourceNativeParserConstitutionBridgeProofs.SourceNativeParserConstitutionBridge
















theorem actual_real_root_rule2 (raw : RawMolecule) (center left right : Nat) :
    raw.compareCanonicalNodeRule? .rule2 (canonicalRoot center left) (canonicalRoot center right) =
      some (compare (raw.atomMassAt left) (raw.atomMassAt right)) := rfl

/-- Node-level Rule-2 strictness after actual Rule-1a and Rule-1b root ties; it is not a claim
that an arbitrary nonterminal branch may skip its deeper Rule-1a layers. -/
theorem actual_tied_real_roots_through_rule2 (raw : RawMolecule) (center left right : Nat)
    (tied : raw.atomZAt left = raw.atomZAt right) :
    raw.compareCanonicalNodeThrough? .rule2 (canonicalRoot center left) (canonicalRoot center right) =
      some (compare (raw.atomMassAt left) (raw.atomMassAt right)) := by
  have rule1a := NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery.compareCanonicalNodeRule?_rule1a_realAtom_tied
    raw (canonicalRoot center left) (canonicalRoot center right) rfl rfl tied
  unfold compareCanonicalNodeThrough?
  rw [rule1a]
  rfl

private theorem unit_copy_records (raw : RawMolecule) (node : CanonicalBranchNode) :
    ∀ bonds : List RawBond,
      (∀ bond ∈ bonds, ∀ next, recordNeighbor? node.atom bond = some next →
        raw.canonicalBondOrder node next = 1) →
      (bonds.flatMap fun bond => match recordNeighbor? node.atom bond with
        | none => []
        | some next => (List.range (raw.canonicalBondOrder node next)).map (fun copy => (next, copy))) =
        (bonds.filterMap (recordNeighbor? node.atom)).map (fun next => (next, 0))
  | [], _ => rfl
  | bond :: bonds, single => by
      have tailSingle : ∀ selected ∈ bonds, ∀ next,
          recordNeighbor? node.atom selected = some next → raw.canonicalBondOrder node next = 1 := by
        intro selected member next observed
        exact single selected (List.mem_cons_of_mem bond member) next observed
      simp only [List.flatMap_cons, List.filterMap_cons]
      cases observed : recordNeighbor? node.atom bond with
      | none => simpa only [List.nil_append] using unit_copy_records raw node bonds tailSingle
      | some next =>
          have order := single bond List.mem_cons_self next observed
          simp only [order, List.range_succ, List.range_zero, List.nil_append,
            List.map_cons, List.map_nil, List.cons_append]
          rw [unit_copy_records raw node bonds tailSingle]

/-- Independent physical record row and bond-order intake derive terminal canonical roots.
Unlike SingleLeafDomain, this law does not require distinct atomic numbers. -/
theorem actual_terminal_root_of_record_row (raw : RawMolecule) (center atom : Nat)
    (row : recordNeighbors raw atom = [center]) (single : raw.bondOrder atom center = 1) :
    raw.canonicalChildren (canonicalRoot center atom) = [] := by
  have copies := unit_copy_records raw (canonicalRoot center atom) raw.bonds (by
    intro bond member next observed
    have retained : next ∈ recordNeighbors raw atom := List.mem_filterMap.mpr ⟨bond, member, observed⟩
    rw [row] at retained
    have same : next = center := List.mem_singleton.mp retained
    subst next
    simp [canonicalBondOrder, canonicalRoot, single])
  change (raw.bonds.flatMap fun bond => match recordNeighbor? atom bond with
    | none => []
    | some next => (List.range (raw.canonicalBondOrder (canonicalRoot center atom) next)).map
        (fun copy => (next, copy))) = (recordNeighbors raw atom).map (fun next => (next, 0)) at copies
  have children : raw.canonicalChildCopies (canonicalRoot center atom) = [] := by
    unfold canonicalChildCopies
    change eraseCanonicalParentCopy center
      (raw.bonds.flatMap fun bond => match recordNeighbor? atom bond with
        | none => []
        | some next => (List.range (raw.canonicalBondOrder (canonicalRoot center atom) next)).map
            (fun copy => (next, copy))) = []
    rw [copies, row]
    simp [eraseCanonicalParentCopy]
  simp [canonicalChildren, children]

/-- GENERAL actual legacy whole-branch Rule-2 comparison on physically terminal tied-Z roots.
Terminality is derived from raw rows; no successful comparison or generated-children premise. -/
theorem actual_terminal_isotope_branch (raw : RawMolecule) (fuel center left right : Nat)
    (leftRow : recordNeighbors raw left = [center]) (rightRow : recordNeighbors raw right = [center])
    (leftSingle : raw.bondOrder left center = 1) (rightSingle : raw.bondOrder right center = 1)
    (tied : raw.atomZAt left = raw.atomZAt right)
    (massDifferent : raw.atomMassAt left ≠ raw.atomMassAt right) :
    raw.compareBranches? fuel center left right = some (compare (raw.atomMassAt left) (raw.atomMassAt right)) := by
  have leftTerminal := actual_terminal_root_of_record_row raw center left leftRow leftSingle
  have rightTerminal := actual_terminal_root_of_record_row raw center right rightRow rightSingle
  have through := actual_tied_real_roots_through_rule2 raw center left right tied
  have rootTie : raw.compareCanonicalNodeRule .rule1a (canonicalRoot center left)
      (canonicalRoot center right) = .eq := by
    rw [NativeInitialSeedRuntimeSupportProofs.RuntimeNormalizedClassifierDomainRecovery.actual_legacy_root_rule1a, tied]
    exact Nat.compare_eq_eq.mpr rfl
  cases comparison : compare (raw.atomMassAt left) (raw.atomMassAt right) with
  | eq => exact False.elim (massDifferent (Nat.compare_eq_eq.mp comparison))
  | lt => simp [compareBranches?, rootTie, compareTerminalHydrogenShellRoots?,
      terminalHydrogenMasses?, leftTerminal, rightTerminal, through, comparison]
  | gt => simp [compareBranches?, rootTie, compareTerminalHydrogenShellRoots?,
      terminalHydrogenMasses?, leftTerminal, rightTerminal, through, comparison]

def centerSpec : AtomSpec :=
  { AtomSpec.aliphatic .C with explicitHydrogens? := some 0, tetrahedral? := some .clockwise }

def raw : RawMolecule :=
  { atoms := [centerSpec,
      { AtomSpec.aliphatic .F with explicitHydrogens? := some 0 },
      { AtomSpec.aliphatic .Br with explicitHydrogens? := some 0 },
      { AtomSpec.aliphatic .H with explicitHydrogens? := some 0, isotope? := some 1 },
      { AtomSpec.aliphatic .H with explicitHydrogens? := some 0, isotope? := some 2 }]
    bonds := [⟨0, 1, .single⟩, ⟨0, 2, .single⟩, ⟨0, 3, .single⟩, ⟨0, 4, .single⟩]
    neighborOrder := [[1, 2, 3, 4], [0], [0], [0], [0]] }

def source : AuthoritativeChemicalInput :=
  raw.toAuthoritativeChemicalInput?.getD { molecule := { atoms := [], interactions := [] } }

def atom (index : Fin 5) : source.AromaticCanonicalAtom := ⟨index.val, by
  change index.val < 5
  exact index.isLt⟩

def center : source.AromaticCanonicalTetrahedralCenter :=
  ⟨atom 0, (mem_aromaticCanonicalTetrahedralCenterSet_iff _ _).mpr ⟨by
    unfold ConnectivityOnlyTetrahedralCenterAtom ConnectivityOnlyTetrahedralPeriodicElement
    decide +kernel, by
      have neighbors : source.aromaticCanonicalNeighborFinset (atom 0) =
          {atom 1, atom 2, atom 3, atom 4} := by
        ext neighbor
        rw [mem_aromaticCanonicalNeighborFinset_iff]
        fin_cases neighbor <;> unfold AromaticCanonicalAdjacent <;> decide +kernel
      rw [neighbors]
      decide +kernel⟩⟩

noncomputable abbrev target : source.AromaticCanonicalOccurrence 0 :=
  source.aromaticCanonicalFinalOccurrence 0 center

noncomputable abbrev roots := finalOccurrenceRoots source 0 center

theorem actual_well_formed : raw.WellFormed := by
  rw [wellFormed_iff_all_bondEndpointsOK]
  decide +kernel

theorem actual_conversion : raw.toSemanticMolecule? = some source.molecule := by decide +kernel

theorem actual_annotation_agreement : RawAnnotationAgreement raw source := by
  apply (rawAnnotationAgreement_iff raw source).mpr
  exact ⟨actual_conversion, by decide +kernel⟩

theorem actual_written_exact : raw.WrittenNeighborExact :=
  (raw.writtenNeighborExact?_eq_true_iff).mp (by decide +kernel)

theorem actual_known_mass : raw.rule2MassesKnown? = true := by decide +kernel

theorem actual_tied_Z_strict_mass : raw.atomZAt 3 = raw.atomZAt 4 ∧ raw.atomMassAt 3 < raw.atomMassAt 4 := by
  decide +kernel

theorem actual_hydrogen_branch (fuel : Nat) : raw.compareBranches? fuel 0 4 3 = some .gt := by
  have computed := actual_terminal_isotope_branch raw fuel 0 4 3 (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel)
  exact computed.trans (by decide +kernel)

theorem actual_no_double : source.NoAromaticCanonicalOrdinaryDoubleBond := by
  have noneTwo : ∀ left right : source.AromaticCanonicalAtom,
      source.molecule.aromaticCanonicalBondOrder left right ≠ 2 := by decide +kernel
  intro left right ordinary
  exact noneTwo left right ordinary.2

/-- Exact ACTUAL returned original-target nodes; isotope labels are not borrowed from another
source, and no desired-root-order premise is supplied. -/
theorem actual_root_nodes : roots.map (fun cursor => cursor.occurrence.1.node) =
    [OfficialCIPNode.rootFromEdge center.1 (atom 1), OfficialCIPNode.rootFromEdge center.1 (atom 2),
      OfficialCIPNode.rootFromEdge center.1 (atom 3), OfficialCIPNode.rootFromEdge center.1 (atom 4)] := by
  decide +kernel

theorem actual_roots_length : roots.length = 4 := by
  have same := congrArg List.length actual_root_nodes
  simpa only [List.length_map, List.length_cons, List.length_nil] using same

noncomputable def frame : source.AromaticCanonicalOccurrenceFourLigandFrame 0 :=
  { roots := roots, rootsLength := actual_roots_length }

def rootNodeAt (slot : Fin 4) : OfficialCIPNode source.AromaticCanonicalAtom :=
  OfficialCIPNode.rootFromEdge center.1 (atom ⟨slot.val + 1, by omega⟩)

theorem actual_root_node_at (slot : Fin 4) : (frame.cursorAt slot).occurrence.1.node = rootNodeAt slot := by
  have bound : slot.val < roots.length := by rw [actual_roots_length]; exact slot.isLt
  have mapped : (roots.map (fun cursor => cursor.occurrence.1.node))[slot.val]? =
      some (frame.cursorAt slot).occurrence.1.node := by
    rw [List.getElem?_map, getElem?_pos roots slot.val bound]
    rfl
  rw [actual_root_nodes] at mapped
  fin_cases slot <;> simpa [rootNodeAt] using mapped.symm

theorem actual_root_ids : occurrenceRootIDs source roots = [some 1, some 2, some 3, some 4] := by
  decide +kernel

theorem actual_keys_exist (view : source.AromaticCanonicalDependencyView target) :
    ∃ keys, source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? target view 2 roots = some keys :=
  exists_occurrence_production_keyFrame_of_valid_noDouble source target view roots actual_roots_length
    (finalOccurrenceRoots_valid source 0 center) actual_no_double

private theorem declarative_forall₂ {fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursors : List (source.AromaticCanonicalRerootCursor 0)}
    {keys : List source.AromaticCanonicalUncancelledRule3SpatialKey}
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExceptList excluded fuel cursors keys) :
    List.Forall₂ (source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded fuel) cursors keys :=
  match derived with
  | .nil _ => .nil
  | .cons head tail => .cons head (declarative_forall₂ tail)

private theorem constitutional_sources_terminal {fuel : Nat}
    {excluded : List source.AromaticCanonicalRule3PhysicalUnitId}
    {cursor : source.AromaticCanonicalRerootCursor 0}
    {key : source.AromaticCanonicalUncancelledRule3SpatialKey}
    (actualTerminal : source.aromaticCanonicalRerootChildren cursor = [])
    (derived : source.DeclarativeAromaticCanonicalRule3SpatialKeyExcept excluded fuel cursor key) :
    key.constitutional.sourceNodes = [[([], cursor.occurrence.1.node)]] := by
  cases derived with
  | zeroLeaf => rfl
  | successorLeaf => rfl
  | successorBranch childFrame nonterminal _ _ _ _ =>
      have computed := (source.aromaticCanonicalRerootChildren?_eq_some_iff cursor _).mpr childFrame
      have same := Option.some.inj computed
      exact False.elim (nonterminal (same.symm.trans actualTerminal))

theorem actual_key_sources (view : source.AromaticCanonicalDependencyView target)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame 0)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? target view 2 roots = some keys)
    (slot : Fin 4) : (keys.keyAt slot).rule3.constitutional.sourceNodes = [[([], rootNodeAt slot)]] := by
  have meaning := source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame?_sound target view 2 roots keys computed
  have pointwise := declarative_forall₂ meaning.1.2.2.2
  have derived := pointwise.get (i := slot.val)
    (by rw [actual_roots_length]; exact slot.isLt) (by rw [keys.rule3Length]; exact slot.isLt)
  have terminal := zero_carrier_final_cursor_children_nil source center (frame.cursorAt slot)
    (List.get_mem roots _)
  have exactSources := constitutional_sources_terminal terminal derived
  simpa only [actual_root_node_at slot] using exactSources

/-- Concrete ordinal encoding is justified by actual source constitutional observations below;
it is not supplied to the source compiler as a substitute comparison. -/
def isotopePriority (slot : Fin 4) : Nat := [2, 3, 0, 1].getD slot.val 0

theorem actual_constitutional_comparison (view : source.AromaticCanonicalDependencyView target)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame 0)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? target view 2 roots = some keys)
    (left right : Fin 4) :
    ExactOfficialRuleMajorKey.compare source.molecule.toLocalizedMoleculeGraph
      (keys.keyAt left).rule3.constitutional (keys.keyAt right).rule3.constitutional =
        compare (isotopePriority left) (isotopePriority right) := by
  unfold ExactOfficialRuleMajorKey.compare Ordering.byKey
  rw [actual_key_sources view keys computed left, actual_key_sources view keys computed right]
  fin_cases left <;> fin_cases right <;> decide +kernel

theorem actual_source_callback (view : source.AromaticCanonicalDependencyView target)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame 0)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? target view 2 roots = some keys)
    (left right : Fin 4) (different : left ≠ right) :
    source.compareAromaticCanonicalOccurrenceRule3Through5At? keys left right =
      strictRankComparison isotopePriority left right := by
  have injective : Function.Injective isotopePriority := by decide +kernel
  have rankDifferent : isotopePriority left ≠ isotopePriority right := fun same => different (injective same)
  have constitution := actual_constitutional_comparison view keys computed left right
  rcases Nat.lt_or_gt_of_ne rankDifferent with lower | higher
  · have rule3 : source.compareAromaticCanonicalUncancelledRule3SpatialKeys
        (keys.keyAt left).rule3 (keys.keyAt right).rule3 = .lt := by
      simp [compareAromaticCanonicalUncancelledRule3SpatialKeys, Ordering.byKey, compareLex,
        constitution, Nat.compare_eq_lt.mpr lower]
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?,
      aromaticCanonicalRule3Through5DescriptorComparison,
      compareAromaticCanonicalOccurrenceRule3Through5At, rule3, strictRankComparison, Nat.compare_eq_lt.mpr lower]
  · have rule3 := source.compareAromaticCanonicalUncancelledRule3SpatialKeys_of_constitutional_gt
      _ _ (constitution.trans (Nat.compare_eq_gt.mpr higher))
    simp [compareAromaticCanonicalOccurrenceRule3Through5At?,
      aromaticCanonicalRule3Through5DescriptorComparison,
      compareAromaticCanonicalOccurrenceRule3Through5At, rule3, strictRankComparison, Nat.compare_eq_gt.mpr higher]

def tracked : TrackedLocalizedLigandOrder := ⟨[1, 0, 3, 2], 0⟩

theorem actual_safe_sort (view : source.AromaticCanonicalDependencyView target)
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame 0)
    (computed : source.buildAromaticCanonicalOccurrenceRule3Through5KeyFrame? target view 2 roots = some keys) :
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked := by
  have execution := sortLocalizedLigandsTrackedFrom_eq_of_callback_ne
    (source.compareAromaticCanonicalOccurrenceRule3Through5At? keys) (strictRankComparison isotopePriority)
    (actual_source_callback view keys computed) (List.finRange 4) [] 0 (List.nodup_finRange 4)
  have literal : sortFourLocalizedLigandsTracked (strictRankComparison isotopePriority) = some tracked := by
    decide +kernel
  have rawComputed : source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked :=
    execution.trans literal
  have coherent : source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent keys tracked.highestFirst = true := by
    apply (source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff keys tracked.highestFirst).mpr
    have sorted : tracked.highestFirst.Pairwise (fun left right => isotopePriority right < isotopePriority left) := by
      decide +kernel
    apply sorted.imp
    intro left right higher
    have comparison := actual_source_callback view keys computed left right (by
      intro same; subst right; exact Nat.lt_irrefl _ higher)
    have projected : (source.compareAromaticCanonicalOccurrenceRule3Through5At keys left right).ordering =
        compare (isotopePriority left) (isotopePriority right) :=
      congrArg CertifiedLocalizedCIPInput.ConstitutionalDescriptorHierarchyComparison.ordering
        (Option.some.inj comparison)
    exact projected.trans (Nat.compare_eq_gt.mpr higher)
  simp [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?, rawComputed, coherent]

theorem actual_source_parser_R (view : source.AromaticCanonicalDependencyView target) :
    constitutionParserRichDescriptor? raw source actual_annotation_agreement actual_written_exact target view 2 =
      some (.chiral RS.R) := by
  obtain ⟨keys, keyComputed⟩ := actual_keys_exist view
  have sorted := actual_safe_sort view keys keyComputed
  have centerComputed := occurrenceTetrahedralCenter?_final source 0 center
  have alignment : findSlotAlignment? (raw.writtenNeighbors center.1.val) (occurrenceRootIDs source roots) =
        some [0, 1, 2, 3] := by
    rw [actual_root_ids]
    decide +kernel
  let evidence : ParserRichPriorityEvidence source 0 :=
    { slots := [0, 1, 2, 3], keys := keys, tracked := tracked, writtenParity := .clockwise, raw := .R }
  have evidenceComputed : constitutionParserRichPriorityEvidence? raw source actual_annotation_agreement
      actual_written_exact target view 2 = some evidence := by
    have observed : raw.atomAt? center.1.val = some centerSpec := by decide +kernel
    have tagged : centerSpec.tetrahedral? = some .clockwise := rfl
    simp [constitutionParserRichPriorityEvidence?, centerComputed, parserIndexViaConversion_val,
      rawWrittenLigandFrame, observed, tagged, finalOccurrenceRoots_are_returned,
      alignment, keyComputed, sorted, evidence]
    rfl
  simp [constitutionParserRichDescriptor?, evidenceComputed, evidence, tracked, classifyTetrahedralRSPseudo]

theorem actual_source_parser_R_meaning (view : source.AromaticCanonicalDependencyView target) :
    ConstitutionParserRichDescriptorMeaning raw source actual_annotation_agreement actual_written_exact
      target view 2 (.chiral RS.R) :=
  constitutionParserRichDescriptor?_sound raw source actual_annotation_agreement actual_written_exact
    target view 2 _ (actual_source_parser_R view)

def runtimeRoot (index : Nat) : CanonicalRerootCursor :=
  { node := canonicalRoot 0 index, previous? := some (canonicalCenterRoot 0) }

def runtimeSorted : List CanonicalRerootCursor :=
  [runtimeRoot 2, runtimeRoot 1, runtimeRoot 4, runtimeRoot 3]

/-- The ACTUAL complete occurrence comparator resolves the isotope pair; its real-node/cycle
and fixed-point auxiliary guards are retained in this literal returned-program witness. -/
theorem actual_runtime_isotope_comparison :
    (compareOccurrenceBranchesComplete? raw [] 12 (runtimeRoot 4) (runtimeRoot 3)).map
      (fun decision => (decision.ordering, decision.pseudo)) = some (.gt, false) := by
  decide +kernel

theorem actual_runtime_sort : sortOccurrencesTrackedAuthoritative? raw [] 12
    (occurrenceLigandCursors raw (canonicalCenterRoot 0)) = some (runtimeSorted, 0) := by
  decide +kernel

theorem actual_runtime_positions : runtimePriorityPositions? raw 0 runtimeSorted = some [1, 0, 3, 2] := by
  decide +kernel

theorem actual_runtime_fact : occurrenceFactAuthoritative? raw 12 [] (canonicalCenterRoot 0) =
    some (recoveredFact 0 [1, 0, 3, 2] RS.R) := by
  decide +kernel

theorem actual_only_center_tagged : OnlyCenterTagged raw 0 := by
  intro index spec observed tagged
  change Fin 5 at index
  fin_cases index <;> simp [raw, atomAt?, listGet?] at observed
  all_goals subst spec
  all_goals simp_all [centerSpec, AtomSpec.aliphatic]

def actualTree : List CanonicalBranchNode := canonicalCenterRoot 0 ::
  [canonicalRoot 0 1, canonicalRoot 0 2, canonicalRoot 0 3, canonicalRoot 0 4]

theorem actual_collected_tree : collectCanonicalTreeAuthoritative raw 12 [canonicalCenterRoot 0] =
    some actualTree := by decide +kernel

theorem actual_public_auxiliary_state : buildOccurrenceAuxStateFullyAuthoritative? raw 12 0 = some [] :=
  auxiliary_state_empty_of_actual_tree raw 12 0 actual_only_center_tagged actualTree actual_collected_tree

theorem actual_public_occurrence_R : tetrahedralOccurrenceFact? raw 12 0 =
    some (recoveredPublicFact 0 [1, 0, 3, 2] RS.R) :=
  public_fact_of_actual_local_fact raw 12 0 actual_only_center_tagged actualTree actual_collected_tree
    [1, 0, 3, 2] RS.R actual_runtime_fact

theorem actual_legacy_rank : raw.rankBranchPositions? (analysisFuel raw) 0 (raw.writtenNeighbors 0) =
    some [1, 0, 3, 2] := by decide +kernel

theorem actual_expanded_classifier_R : expandedTetrahedralDescriptorAt? raw 0 = some RS.R := by
  have observed : raw.atomAt? 0 = some centerSpec := rfl
  have four : (raw.writtenNeighbors 0).length = 4 := rfl
  have ligands := AuthoritativeCIPRule6Scheduler.ligandsWithLonePair_eq_writtenNeighbors_of_length_four
    raw 0 four
  simp [expandedTetrahedralDescriptorAt?, actual_known_mass, tetrahedralOutcome,
    observed, centerSpec, ligands, four, actual_legacy_rank,
    descriptorOfParity, permutationIsEven, centreElementSupported, inversionCount, AtomSpec.aliphatic]

theorem actual_expansion_fixed : raw.withExplicitHydrogens = raw :=
  ExplicitHydrogenExpansionIdentityProofs.ExplicitHydrogenExpansionIdentity.structurally_fixed_expansion_identity raw
    ⟨by
      intro spec member
      change spec ∈ [centerSpec, _, _, _, _] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same | same | same | same <;> subst spec <;> rfl,
      actual_written_exact, rfl⟩

theorem actual_parsed_classifier_R : parsedTetrahedralDescriptorAt? raw 0 = some RS.R := by
  have normalized : raw.normalizeUnspecifiedBonds = raw := by decide +kernel
  simpa only [parsedTetrahedralDescriptorAt?, normalized, actual_expansion_fixed] using actual_expanded_classifier_R

/-- Full closed emitted-label agreement, including the ACTUAL higher raw intake and OWN source
independent parser meaning. The genotype/isotope/source-policy adoption gates remain separate. -/
theorem actual_three_consumer_agreement (view : source.AromaticCanonicalDependencyView target) :
    tetrahedralOccurrenceFact? raw 12 0 = some (recoveredPublicFact 0 [1, 0, 3, 2] RS.R) ∧
      parsedTetrahedralDescriptorAt? raw 0 = some RS.R ∧
      constitutionParserRichDescriptor? raw source actual_annotation_agreement actual_written_exact
        target view 2 = some (.chiral RS.R) ∧
      ConstitutionParserRichDescriptorMeaning raw source actual_annotation_agreement actual_written_exact
        target view 2 (.chiral RS.R) :=
  ⟨actual_public_occurrence_R, actual_parsed_classifier_R, actual_source_parser_R view,
    actual_source_parser_R_meaning view⟩

end TetraStereo.UniversalProof.IsotopeSourcePublicDescriptorRecoveryProofs.IsotopeSourcePublicDescriptorRecovery
