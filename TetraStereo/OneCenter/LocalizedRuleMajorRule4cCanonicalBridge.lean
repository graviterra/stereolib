import TetraStereo.OneCenter.LocalizedRuleMajorCanonicalBridge
import TetraStereo.OneCenter.LocalizedRuleMajorRule4cObservation
import TetraStereo.OneCenter.LocalizedRuleMajorRule4cTableBridge
import TetraStereo.OneCenter.DeclarativeCIPRule4cReadingEvidence
import TetraStereo.OneCenter.LocalizedActualMolecularEvidenceRefinement
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! # Rule-4c independent node readback for the actual rule-major tree

The runtime table stores the two-level Rule-4c priority, while the independent molecular reading
stores `0 = absent`, `1 = s`, `2 = r`.  These are not pointwise equal.  This module proves the
node-level representation of the independent observation from an exact readback of the actual
localized label; the whole-table order transfer is supplied by `Rule4cObservationBridge` under a
preceding Rule-4a table tie.
-/

namespace TetraStereo.OneCenter
namespace Rule4aTableBridge

open LocalizedCumulativeDecoratedTree
open CertifiedLocalizedCIPInput
open OfficialSparseCanonicalVectorComparison
open DeclarativeCIP
open Rule4cObservationBridge
open SparsePhysicalFirstDifference SparseSupportAlignment

noncomputable section
open scoped Classical

/-- Readback needed by the Rule-4c recursive representation bridge.  It retains pseudoasymmetric
labels and only asks that every tree node's label is its independently read descriptor label. -/
structure RuleMajorTreeReadback4c
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (tree : LocalizedCumulativeDecoratedTree input carrierFuel)
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (ρ : RS) : Prop where
  label : ∀ (node : (ruleMajorTreeGraph tree).Node)
    (actual : LocalizedCumulativeDecoratedTree input carrierFuel),
    tree.decoratedSubtreeAt? node.1 = some actual →
      actual.label = (occurrenceReading input.moleculeGraph descriptorMap unit
        (ruleMajorTreeGraph tree) node).toLocalizedLabel
  tetrahedral : ∀ node : (ruleMajorTreeGraph tree).Node,
    (occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node).IsTetrahedral
  available : ∀ node : (ruleMajorTreeGraph tree).Node,
    occurrenceReading input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) node ≠ .unavailable
  rule4abcOnly : Rule4abcOnly (ruleMajorTreeGraph tree)
    (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorTreeGraph tree) (senseOf ρ))

/-! ## Exact label-table readback at one path -/

theorem encodedPseudo4c_nil
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key} {stage : LocalizedCumulativeRule45Stage}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    (tableMatch : LocalizedCumulativeTreeTableMatch stage tree key)
    (labels : LocalizedCumulativeTreeLabelMatch tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree) :
    encodedPseudo4c key [] =
      ((code (pseudoValueOfLabel tree.label) : StereoCode) : StereoLabel) := by
  unfold encodedPseudo4c
  have hpresent : HasAddress key.constitutional.rule1a [] := by
    have viaTable : HasAddress (table (fun node => node.atomicNumber) tree) [] :=
      (hasAddress_atomicNumber_table_iff_subtree realizes []).2 ⟨tree, rfl⟩
    simpa [← tableMatch.1, tables_rule1a] using viaTable
  rw [if_pos hpresent, pseudoTable_eq_table labels,
    tableValue_table_eq_observeAt (fun node => pseudoValueOfLabel node.label) tree []]
  rfl

private theorem pseudoConsSupport
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key} {stage : LocalizedCumulativeRule45Stage}
    (tableMatch : LocalizedCumulativeTreeTableMatch stage tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {sortedKeys : List input.LocalizedRerootCumulativeRule45Key}
    (paired : List.Forall₂ (fun childKey childTree =>
        LocalizedCumulativeTreeTableMatch stage childTree childKey ∧
          LocalizedCumulativeTreeRealizes input read childTree ∧
            LocalizedCumulativeTreeLabelMatch childTree childKey) sortedKeys tree.children)
    (digit : Nat) (path : List Nat) :
    (HasAddress key.constitutional.rule1a (digit :: path) →
      ∃ (hd : digit < tree.children.length) (hk : digit < sortedKeys.length),
        HasAddress (sortedKeys[digit]'hk).constitutional.rule1a path ∧
        LocalizedCumulativeTreeTableMatch stage (tree.children[digit]'hd)
          (sortedKeys[digit]'hk) ∧
        LocalizedCumulativeTreeRealizes input read (tree.children[digit]'hd) ∧
        LocalizedCumulativeTreeLabelMatch (tree.children[digit]'hd) (sortedKeys[digit]'hk) ∧
        tree.decoratedSubtreeAt? (digit :: path) =
          (tree.children[digit]'hd).decoratedSubtreeAt? path) ∧
    (¬ HasAddress key.constitutional.rule1a (digit :: path) →
      ∀ (hk : digit < sortedKeys.length),
        ¬ HasAddress (sortedKeys[digit]'hk).constitutional.rule1a path) := by
  have keysLength : sortedKeys.length = tree.children.length := List.Forall₂.length_eq paired
  constructor
  · intro hpresent
    have guardTable : HasAddress (table (fun node => node.atomicNumber) tree) (digit :: path) := by
      simpa [← tableMatch.1, tables_rule1a] using hpresent
    obtain ⟨subtree, subtreeLookup⟩ :=
      (hasAddress_atomicNumber_table_iff_subtree realizes (digit :: path)).1 guardTable
    obtain ⟨child, subtree', childGet, childPath⟩ :=
      (decoratedSubtreeAt?_cons_some tree digit path).1 ⟨subtree, subtreeLookup⟩
    have hd : digit < tree.children.length := (List.getElem?_eq_some_iff.1 childGet).1
    have hk : digit < sortedKeys.length := by omega
    have childIs : child = tree.children[digit]'hd :=
      (Option.some.inj ((List.getElem?_eq_getElem hd).symm.trans childGet)).symm
    have childPaired := List.Forall₂.get (i := digit) paired hk hd
    simp only [List.get_eq_getElem] at childPaired
    have childSubtree : (tree.children[digit]'hd).decoratedSubtreeAt? path = some subtree' := by
      simpa [childIs] using childPath
    have childGuard : HasAddress (sortedKeys[digit]'hk).constitutional.rule1a path := by
      have viaChildTable : HasAddress
          (table (fun node => node.atomicNumber) (tree.children[digit]'hd)) path :=
        (hasAddress_atomicNumber_table_iff_subtree childPaired.2.1 path).2
          ⟨subtree', childSubtree⟩
      simpa [← childPaired.1.1, tables_rule1a] using viaChildTable
    refine ⟨hd, hk, childGuard, childPaired.1, childPaired.2.1, childPaired.2.2, ?_⟩
    rw [decoratedSubtreeAt?, childGet, childIs]
  · intro hpresent hk childGuard
    apply hpresent
    have hd : digit < tree.children.length := by omega
    have childPaired := List.Forall₂.get (i := digit) paired hk hd
    simp only [List.get_eq_getElem] at childPaired
    have viaChildTable : HasAddress
        (table (fun node => node.atomicNumber) (tree.children[digit]'hd)) path := by
      simpa [← childPaired.1.1, tables_rule1a] using childGuard
    obtain ⟨subtree', childPath⟩ :=
      (hasAddress_atomicNumber_table_iff_subtree childPaired.2.1 path).1 viaChildTable
    have lookup : ∃ subtree, tree.decoratedSubtreeAt? (digit :: path) = some subtree :=
      (decoratedSubtreeAt?_cons_some tree digit path).2
        ⟨_, subtree', List.getElem?_eq_getElem hd, childPath⟩
    have viaTable := (hasAddress_atomicNumber_table_iff_subtree realizes (digit :: path)).2 lookup
    simpa [← tableMatch.1, tables_rule1a] using viaTable

theorem encodedPseudo4c_cons_of_key
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key} {stage : LocalizedCumulativeRule45Stage}
    (tableMatch : LocalizedCumulativeTreeTableMatch stage tree key)
    (labels : LocalizedCumulativeTreeLabelMatch tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {sortedKeys : List input.LocalizedRerootCumulativeRule45Key}
    (paired : List.Forall₂ (fun childKey childTree =>
        LocalizedCumulativeTreeTableMatch stage childTree childKey ∧
          LocalizedCumulativeTreeRealizes input read childTree ∧
            LocalizedCumulativeTreeLabelMatch childTree childKey) sortedKeys tree.children)
    (digit : Nat) (path : List Nat) :
    encodedPseudo4c key (digit :: path) =
      ((sortedKeys[digit]?).map fun childKey => encodedPseudo4c childKey path).getD ⊥ := by
  obtain ⟨present, absent⟩ := pseudoConsSupport tableMatch realizes paired digit path
  unfold encodedPseudo4c
  by_cases hpresent : HasAddress key.constitutional.rule1a (digit :: path)
  · obtain ⟨hd, hk, childGuard, childMatch, childRealizes, childLabels, lookupEq⟩ := present hpresent
    rw [if_pos hpresent, List.getElem?_eq_getElem hk]
    simp only [Option.map_some, Option.getD_some]
    rw [if_pos childGuard]
    have valueEq : tableValue (Rule4cObservationBridge.mapLabelTable pseudoValueOfLabel key.labels) (digit :: path) =
        tableValue (Rule4cObservationBridge.mapLabelTable pseudoValueOfLabel
          (sortedKeys[digit]'hk).labels) path := by
      rw [Rule4cObservationBridge.pseudoTable_eq_table labels,
        Rule4cObservationBridge.pseudoTable_eq_table childLabels,
        tableValue_table_eq_observeAt, tableValue_table_eq_observeAt]
      unfold observeAt
      rw [lookupEq]
    rw [valueEq]
  · rw [if_neg hpresent]
    cases keysGet : sortedKeys[digit]? with
    | none => rfl
    | some childKey =>
        simp only [Option.map_some, Option.getD_some]
        have hk : digit < sortedKeys.length := (List.getElem?_eq_some_iff.1 keysGet).1
        have childKeyIs : childKey = sortedKeys[digit]'hk :=
          Option.some.inj (keysGet.symm.trans (List.getElem?_eq_getElem hk))
        have childAbsent := absent hpresent hk
        rw [childKeyIs, if_neg childAbsent]

/-- Rule 4a reads the same child scalar table on actual stage-4c keys. -/
theorem encoded4a_cons_of_key_rule4c
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key} {ρ : RS}
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4c ρ) tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {sortedKeys : List input.LocalizedRerootCumulativeRule45Key}
    (paired : List.Forall₂ (fun childKey childTree =>
        LocalizedCumulativeTreeTableMatch (.rule4c ρ) childTree childKey ∧
          LocalizedCumulativeTreeRealizes input read childTree ∧
            LocalizedCumulativeTreeLabelMatch childTree childKey) sortedKeys tree.children)
    (digit : Nat) (path : List Nat) :
    encoded4a key (digit :: path) =
      ((sortedKeys[digit]?).map fun childKey => encoded4a childKey path).getD ⊥ := by
  obtain ⟨present, absent⟩ := pseudoConsSupport tableMatch realizes paired digit path
  unfold encoded4a
  by_cases hpresent : HasAddress key.constitutional.rule1a (digit :: path)
  · obtain ⟨_hd, hk, childGuard, childMatch, _childRealizes, _childLabels, lookupEq⟩ := present hpresent
    rw [if_pos hpresent, List.getElem?_eq_getElem hk]
    simp only [Option.map_some, Option.getD_some]
    rw [if_pos childGuard]
    have valueEq : tableValue (scalar4a key) (digit :: path) =
        tableValue (scalar4a (sortedKeys[digit]'hk)) path := by
      rw [Rule4cObservationBridge.scalar4a_rule4c_eq_table tableMatch,
        Rule4cObservationBridge.scalar4a_rule4c_eq_table childMatch,
        tableValue_table_eq_observeAt, tableValue_table_eq_observeAt]
      unfold observeAt
      rw [lookupEq]
    rw [valueEq]
  · rw [if_neg hpresent]
    cases keysGet : sortedKeys[digit]? with
    | none => rfl
    | some childKey =>
        simp only [Option.map_some, Option.getD_some]
        have hk : digit < sortedKeys.length := (List.getElem?_eq_some_iff.1 keysGet).1
        have childKeyIs : childKey = sortedKeys[digit]'hk :=
          Option.some.inj (keysGet.symm.trans (List.getElem?_eq_getElem hk))
        rw [childKeyIs, if_neg (absent hpresent hk)]

/-- Rule 4b reads the same pair of child scalar tables on actual stage-4c keys. -/
theorem encoded4b_cons_of_key_rule4c
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key} {ρ : RS}
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4c ρ) tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    {sortedKeys : List input.LocalizedRerootCumulativeRule45Key}
    (paired : List.Forall₂ (fun childKey childTree =>
        LocalizedCumulativeTreeTableMatch (.rule4c ρ) childTree childKey ∧
          LocalizedCumulativeTreeRealizes input read childTree ∧
            LocalizedCumulativeTreeLabelMatch childTree childKey) sortedKeys tree.children)
    (digit : Nat) (path : List Nat) :
    encoded4b key (digit :: path) =
      ((sortedKeys[digit]?).map fun childKey => encoded4b childKey path).getD ⊥ := by
  obtain ⟨present, absent⟩ := pseudoConsSupport tableMatch realizes paired digit path
  unfold encoded4b
  by_cases hpresent : HasAddress key.constitutional.rule1a (digit :: path)
  · obtain ⟨_hd, hk, childGuard, childMatch, _childRealizes, _childLabels, lookupEq⟩ := present hpresent
    rw [if_pos hpresent, List.getElem?_eq_getElem hk]
    simp only [Option.map_some, Option.getD_some]
    rw [if_pos childGuard]
    have h4a : tableValue (scalar4a key) (digit :: path) =
        tableValue (scalar4a (sortedKeys[digit]'hk)) path := by
      rw [Rule4cObservationBridge.scalar4a_rule4c_eq_table tableMatch,
        Rule4cObservationBridge.scalar4a_rule4c_eq_table childMatch,
        tableValue_table_eq_observeAt, tableValue_table_eq_observeAt]
      unfold observeAt
      rw [lookupEq]
    have h4b : tableValue (scalar4b key) (digit :: path) =
        tableValue (scalar4b (sortedKeys[digit]'hk)) path := by
      rw [Rule4cObservationBridge.scalar4b_rule4c_eq_table tableMatch,
        Rule4cObservationBridge.scalar4b_rule4c_eq_table childMatch,
        tableValue_table_eq_observeAt, tableValue_table_eq_observeAt]
      unfold observeAt
      rw [lookupEq]
    rw [h4a, h4b]
  · rw [if_neg hpresent]
    cases keysGet : sortedKeys[digit]? with
    | none => rfl
    | some childKey =>
        simp only [Option.map_some, Option.getD_some]
        have hk : digit < sortedKeys.length := (List.getElem?_eq_some_iff.1 keysGet).1
        have childKeyIs : childKey = sortedKeys[digit]'hk :=
          Option.some.inj (keysGet.symm.trans (List.getElem?_eq_getElem hk))
        rw [childKeyIs, if_neg (absent hpresent hk)]

/-- At the empty relative address, the independent Rule-4c node observation is the code of the
molecular pseudo-value read from the actual localized label.  This includes both `r` and `s`. -/
theorem stereoNodePathObservation_nil_eq_pseudoValueOfLabel
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom)
    (W D : Nat) (reference : DescriptorSense) (node : graph.Node)
    (dsub : LocalizedCumulativeDecoratedTree input carrierFuel)
    (hlabel : dsub.label =
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (havail : occurrenceReading input.moleculeGraph descriptorMap unit graph node ≠ .unavailable) :
    stereoNodePathObservation input.moleculeGraph graph
        (readingEvidence4c input.moleculeGraph descriptorMap unit graph reference) W D
        .rule4cPseudoasymmetricDescriptor node [] =
      ((code (pseudoValueOfLabel dsub.label) : StereoCode) : StereoLabel) := by
  rw [stereoNodePathObservation_nil]
  have hread : stereoLabel graph
      (readingEvidence4c input.moleculeGraph descriptorMap unit graph reference)
      .rule4cPseudoasymmetricDescriptor node =
        ((code (occurrenceReading input.moleculeGraph descriptorMap unit graph node).pseudoValue :
          StereoCode) : StereoLabel) := by
    unfold stereoLabel stereoValue readingEvidence4c
    cases h : occurrenceReading input.moleculeGraph descriptorMap unit graph node with
    | unavailable => exact absurd h havail
    | outsideInventory => simp [liftObservation, rule4cObservation, h,
        OccurrenceReading.pseudoValue, encodeHierarchy, encodeEntry, singleEntry, code]
    | unassigned => simp [liftObservation, rule4cObservation, h,
        OccurrenceReading.pseudoValue, encodeHierarchy, encodeEntry, singleEntry, code]
    | descriptor value => simp [liftObservation, rule4cObservation, h,
        OccurrenceReading.pseudoValue, encodeHierarchy, encodeEntry, singleEntry, code]
  rw [hread]
  have hvalue := pseudoValue_eq_pseudoValueOfLabel
    (occurrenceReading input.moleculeGraph descriptorMap unit graph node) dsub.label hlabel.symm
  rw [hvalue]

/-- The no-reference alternative has the same local Rule-4c readback, independently of the
reference-dependent Rule-4b component. -/
theorem stereoNodePathObservation_nil_eq_pseudoValueOfLabel_noReference
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom)
    (W D : Nat) (node : graph.Node) (dsub : LocalizedCumulativeDecoratedTree input carrierFuel)
    (hlabel : dsub.label =
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (havail : occurrenceReading input.moleculeGraph descriptorMap unit graph node ≠ .unavailable) :
    stereoNodePathObservation input.moleculeGraph graph
        (noReferenceEvidence4c input.moleculeGraph descriptorMap unit graph) W D
        .rule4cPseudoasymmetricDescriptor node [] =
      ((code (pseudoValueOfLabel dsub.label) : StereoCode) : StereoLabel) := by
  rw [stereoNodePathObservation_nil]
  have hread : stereoLabel graph
      (noReferenceEvidence4c input.moleculeGraph descriptorMap unit graph)
      .rule4cPseudoasymmetricDescriptor node =
        ((code (occurrenceReading input.moleculeGraph descriptorMap unit graph node).pseudoValue :
          StereoCode) : StereoLabel) := by
    unfold stereoLabel stereoValue noReferenceEvidence4c rankEvidence
    cases h : occurrenceReading input.moleculeGraph descriptorMap unit graph node with
    | unavailable => exact absurd h havail
    | outsideInventory => simp [liftObservation, rule4cObservation, h,
        OccurrenceReading.pseudoValue, encodeHierarchy, encodeEntry, singleEntry, code]
    | unassigned => simp [liftObservation, rule4cObservation, h,
        OccurrenceReading.pseudoValue, encodeHierarchy, encodeEntry, singleEntry, code]
    | descriptor value => simp [liftObservation, rule4cObservation, h,
        OccurrenceReading.pseudoValue, encodeHierarchy, encodeEntry, singleEntry, code]
  rw [hread]
  have hvalue := pseudoValue_eq_pseudoValueOfLabel
    (occurrenceReading input.moleculeGraph descriptorMap unit graph node) dsub.label hlabel.symm
  rw [hvalue]

theorem stereoNodePathObservation_nil_eq_encoded4a_rule4c
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} {ρ : RS}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom)
    (W D : Nat) (node : graph.Node)
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4c ρ) tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (hlabel : tree.label =
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (htetra : (occurrenceReading input.moleculeGraph descriptorMap unit graph node).IsTetrahedral)
    (havail : occurrenceReading input.moleculeGraph descriptorMap unit graph node ≠ .unavailable) :
    stereoNodePathObservation input.moleculeGraph graph
        (readingEvidence4c input.moleculeGraph descriptorMap unit graph (senseOf ρ)) W D
        .rule4aStereogenicUnitKind node [] = encoded4a key [] := by
  rw [stereoNodePathObservation_nil]
  rw [← Rule4cObservationBridge.encoded4a_rule4bTableView tableMatch []]
  change stereoLabel graph
      (readingEvidence input.moleculeGraph descriptorMap unit graph (senseOf ρ))
        .rule4aStereogenicUnitKind node =
      encoded4a (Rule4cObservationBridge.rule4bTableView ρ tree key) []
  have old := @stereoNodePathObservation_nil_eq_encoded4a_rule4b input carrierFuel read tree
    (Rule4cObservationBridge.rule4bTableView ρ tree key) ρ descriptorMap unit graph W D node
    (Rule4cObservationBridge.rule4bTableView_matches tableMatch) realizes hlabel htetra havail (senseOf ρ)
  rw [stereoNodePathObservation_nil] at old
  exact old

theorem stereoNodePathObservation_nil_eq_encoded4b_rule4c
    {input : CertifiedLocalizedCIPInput} {carrierFuel : Nat} {ρ : RS}
    {read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel}
    {tree : LocalizedCumulativeDecoratedTree input carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph))
    (unit : DetectedOccurrence input.moleculeGraph) (graph : RootedDigraph input.Atom)
    (W D : Nat) (node : graph.Node)
    (tableMatch : LocalizedCumulativeTreeTableMatch (.rule4c ρ) tree key)
    (realizes : LocalizedCumulativeTreeRealizes input read tree)
    (hlabel : tree.label =
      (occurrenceReading input.moleculeGraph descriptorMap unit graph node).toLocalizedLabel)
    (htetra : (occurrenceReading input.moleculeGraph descriptorMap unit graph node).IsTetrahedral) :
    stereoNodePathObservation input.moleculeGraph graph
        (readingEvidence4c input.moleculeGraph descriptorMap unit graph (senseOf ρ)) W D
        .rule4bLikeUnlikeDescriptorPairs node [] = encoded4b key [] := by
  rw [stereoNodePathObservation_nil]
  rw [← Rule4cObservationBridge.encoded4b_rule4bTableView tableMatch []]
  change stereoLabel graph
      (readingEvidence input.moleculeGraph descriptorMap unit graph (senseOf ρ))
        .rule4bLikeUnlikeDescriptorPairs node =
      encoded4b (Rule4cObservationBridge.rule4bTableView ρ tree key) []
  have old := @stereoNodePathObservation_nil_eq_encoded4b input carrierFuel read tree
    (Rule4cObservationBridge.rule4bTableView ρ tree key) ρ descriptorMap unit graph W D node
    (Rule4cObservationBridge.rule4bTableView_matches tableMatch) realizes hlabel htetra
  rw [stereoNodePathObservation_nil] at old
  exact old

section RuleMajorRootArmRule4c

variable {input : CertifiedLocalizedCIPInput} {center : input.TetrahedralCenter}
  {index : Fin 4}
  {read : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1) →
    Option LocalizedAuxiliaryLabel}
  {ρ : RS}
variable (arm : input.RuleMajorRootArm center index (.rule4c ρ) read)
  {descriptorMap : DescriptorMap (DetectedOccurrence input.moleculeGraph)}
  {unit : DetectedOccurrence input.moleculeGraph}

/-- Terminal stage-4c keys read all three active independent stereochemical columns at the root. -/
theorem ruleMajorRootArm_terminal_bridge4c
    (hyp : RuleMajorTreeReadback4c arm.tree descriptorMap unit ρ)
    (cursor : input.LocalizedRerootCursor (input.certified.input.molecule.atomCount + 1))
    (fullMatch : LocalizedCumulativeTreeFullMatch (.rule4c ρ)
      (localizedRootTree input cursor (read cursor) [])
      (localizedCumulativeRule45TerminalKey input (.rule4c ρ) cursor (read cursor)))
    (realizes : LocalizedCumulativeTreeRealizes input read
      (localizedRootTree input cursor (read cursor) []))
    {W D : Nat} (node : (ruleMajorArmGraph arm).Node)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 =
      some (localizedRootTree input cursor (read cursor) [])) :
    (((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
          (localizedRootTree input cursor (read cursor) []).children.length).map
        (rule4abcKey input.moleculeGraph (ruleMajorArmGraph arm)
          (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D node)
        (localizedCumulativeRule45TerminalKey input (.rule4c ρ) cursor (read cursor)) ∧
      Represents4b W D (rule4bComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D node)
        (localizedCumulativeRule45TerminalKey input (.rule4c ρ) cursor (read cursor)) ∧
      Represents4c W D (rule4cComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D node)
        (localizedCumulativeRule45TerminalKey input (.rule4c ρ) cursor (read cursor)) := by
  have childrenEq : (localizedRootTree input cursor (read cursor) []).children = [] := by
    unfold localizedRootTree
    rfl
  have pairedNil : List.Forall₂ (fun childKey childTree =>
      LocalizedCumulativeTreeTableMatch (.rule4c ρ) childTree childKey ∧
        LocalizedCumulativeTreeRealizes input read childTree ∧
          LocalizedCumulativeTreeLabelMatch childTree childKey)
      ([] : List input.LocalizedRerootCumulativeRule45Key)
      (localizedRootTree input cursor (read cursor) []).children := by
    rw [childrenEq]
    exact List.Forall₂.nil
  have pairedNilBasic : List.Forall₂ (fun childKey childTree =>
      LocalizedCumulativeTreeTableMatch (.rule4c ρ) childTree childKey ∧
        LocalizedCumulativeTreeRealizes input read childTree)
      ([] : List input.LocalizedRerootCumulativeRule45Key)
      (localizedRootTree input cursor (read cursor) []).children :=
    List.Forall₂.imp (fun _ _ related => ⟨related.1, related.2.1⟩) pairedNil
  have constBot : ∀ digit path,
      nodePathObservation input.moleculeGraph (ruleMajorArmGraph arm) W D 0 node
        (digit :: path) = ⊥ := by
    intro digit path
    have hconst := (ruleMajorRootArm_terminal_bridge arm cursor fullMatch realizes
      (W := W) (D := D) node lookup).2
    have hroot := hconst 0 (by omega) (digit :: path)
    unfold nodePathObservation
    rw [hroot, encodedObservation_cons_of_key fullMatch.tableMatch realizes pairedNilBasic
      (ruleOfIndex 0) digit path]
    rfl
  refine ⟨by rw [childrenEq]; simp [slotList], ?_, ?_, ?_⟩
  · intro path
    cases path with
    | nil =>
        exact stereoNodePathObservation_nil_eq_encoded4a_rule4c descriptorMap unit
          (ruleMajorArmGraph arm) W D node fullMatch.tableMatch realizes
          (hyp.label node _ lookup) (hyp.tetrahedral node) (hyp.available node)
    | cons digit path =>
        have rhs : encoded4a
            (localizedCumulativeRule45TerminalKey input (.rule4c ρ) cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encoded4a_cons_of_key_rule4c fullMatch.tableMatch realizes pairedNil digit path]
          rfl
        rw [rhs]
        exact (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (ruleMajorArmGraph arm)
          (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ))
          .rule4aStereogenicUnitKind W D (digit :: path) node).2 (constBot digit path)
  · intro path
    cases path with
    | nil =>
        exact stereoNodePathObservation_nil_eq_encoded4b_rule4c descriptorMap unit
          (ruleMajorArmGraph arm) W D node fullMatch.tableMatch realizes
          (hyp.label node _ lookup) (hyp.tetrahedral node)
    | cons digit path =>
        have rhs : encoded4b
            (localizedCumulativeRule45TerminalKey input (.rule4c ρ) cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encoded4b_cons_of_key_rule4c fullMatch.tableMatch realizes pairedNil digit path]
          rfl
        rw [rhs]
        exact (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (ruleMajorArmGraph arm)
          (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ))
          .rule4bLikeUnlikeDescriptorPairs W D (digit :: path) node).2 (constBot digit path)
  · intro path
    cases path with
    | nil =>
        rw [encodedPseudo4c_nil fullMatch.tableMatch fullMatch.labelMatch realizes]
        exact stereoNodePathObservation_nil_eq_pseudoValueOfLabel descriptorMap unit
          (ruleMajorArmGraph arm) W D (senseOf ρ) node
          (localizedRootTree input cursor (read cursor) [])
          (hyp.label node _ lookup) (hyp.available node)
    | cons digit path =>
        have rhs : encodedPseudo4c
            (localizedCumulativeRule45TerminalKey input (.rule4c ρ) cursor (read cursor))
            (digit :: path) = ⊥ := by
          rw [encodedPseudo4c_cons_of_key fullMatch.tableMatch fullMatch.labelMatch realizes
            pairedNil digit path]
          rfl
        rw [rhs]
        exact (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (ruleMajorArmGraph arm)
          (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ))
          .rule4cPseudoasymmetricDescriptor W D (digit :: path) node).2 (constBot digit path)

/-- Recursive actual-stage-4c representation.  The actual Rule-4c sort trace supplies the
descending 4abc key at every sibling family, and the three addressed observations are read from
the same decorated child trees. -/
theorem ruleMajorRootArm_node_bridge4c
    (hyp : RuleMajorTreeReadback4c arm.tree descriptorMap unit ρ)
    {W D : Nat} (hW : (ruleMajorArmGraph arm).width ≤ W)
    (hD : (ruleMajorArmGraph arm).height ≤ D)
    {fuel : Nat} (node : (ruleMajorArmGraph arm).Node)
    (dsub : LocalizedCumulativeDecoratedTree input (input.certified.input.molecule.atomCount + 1))
    (key : input.LocalizedRerootCumulativeRule45Key)
    (trace : LocalizedRuleMajorSortTrace input (.rule4c ρ) read fuel dsub key)
    (lookup : arm.tree.decoratedSubtreeAt? node.1 = some dsub) :
    (((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node dsub.children.length).map
        (rule4abcKey input.moleculeGraph (ruleMajorArmGraph arm)
          (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D)).Pairwise
      fun x y => y ≤ x) ∧
      Represents4a W D (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D node) key ∧
      Represents4b W D (rule4bComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D node) key ∧
      Represents4c W D (rule4cComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ)) W D node) key := by
  induction fuel generalizing dsub key node lookup with
  | zero =>
      cases trace with
      | terminal _fuel cursor _children _childrenComputed _terminalChildren fullMatch realizes =>
          exact ruleMajorRootArm_terminal_bridge4c arm hyp cursor fullMatch realizes node lookup
  | succ fuel ih =>
      have fullMatch := LocalizedRuleMajorSortTrace.fullMatch_of_trace trace
      have realizes := LocalizedRuleMajorSortTrace.realizes_of_trace trace
      rcases LocalizedRuleMajorSortTrace.structure_of_trace trace with
        ⟨cursor, _children, dsubEq, keyEq, _childrenEq, _childrenComputed, _terminalChildren⟩ |
        ⟨cursor, _children, _childKeys, sortedKeys, sortedTrees, dsubEq, keyEq, childrenEq,
          _childrenComputed, _nonempty, _childKeysComputed, sortedEq, _constitutionalDescending,
          sortedDescending, childrenTraced⟩
      · subst dsub
        subst key
        exact ruleMajorRootArm_terminal_bridge4c arm hyp cursor fullMatch realizes node lookup
      · subst dsub
        subst key
        set E := readingEvidence4c input.moleculeGraph descriptorMap unit
          (ruleMajorArmGraph arm) (senseOf ρ) with hE
        have hdense : DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length :=
          ruleMajorRootArm_denseAt_of_lookup arm node
            (localizedRootTree input cursor (read cursor) sortedTrees) lookup
        have paired := LocalizedRuleMajorSortTraceList.to_forall₂ childrenTraced
        have lengthEq : sortedKeys.length = sortedTrees.length := List.Forall₂.length_eq paired
        have pairedMatch : List.Forall₂ (fun childKey childTree =>
            LocalizedCumulativeTreeTableMatch (.rule4c ρ) childTree childKey ∧
              LocalizedCumulativeTreeRealizes input read childTree ∧
                LocalizedCumulativeTreeLabelMatch childTree childKey) sortedKeys sortedTrees :=
          List.Forall₂.imp (fun childKey childTree related =>
            ⟨(LocalizedRuleMajorSortTrace.fullMatch_of_trace related).tableMatch,
              LocalizedRuleMajorSortTrace.realizes_of_trace related,
              (LocalizedRuleMajorSortTrace.fullMatch_of_trace related).labelMatch⟩) paired
        have descending : input.RuleMajorCumulativeKeysDescending 3 sortedKeys := by
          have widthEq : CertifiedLocalizedCIPInput.ruleMajorStageWidth (.rule4c ρ) = 3 := rfl
          rw [← widthEq]
          exact sortedDescending
        have countEq : (localizedRootTree input cursor (read cursor) sortedTrees).children.length =
            sortedTrees.length := by rw [childrenEq]
        have slotLength : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).length =
            sortedTrees.length := by simp [slotList, countEq]
        have childAt : ∀ i (hi : i < sortedTrees.length), ∃ child : (ruleMajorArmGraph arm).Node,
            (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]? =
                some child ∧ child.1 = node.1 ++ [i] ∧
                arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) := by
          intro i hi
          obtain ⟨child, slotSome, addr⟩ := slotList_getD_of_lt
            (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := node)
            (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
            hdense (by rw [countEq]; exact hi)
          have addrFlat : child.1 = node.1 ++ [i] := by
            rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address,
              (toOfficialSourceTree arm.tree).declarativeAddressing_address] at addr
            exact addr
          refine ⟨child, slotSome, addrFlat, ?_⟩
          rw [addrFlat, decoratedSubtreeAt?_append arm.tree node.1 [i], lookup]
          simp [childrenEq, decoratedSubtreeAt?, List.getElem?_eq_getElem hi]
        have traceAt : ∀ i (hi : i < sortedTrees.length),
            LocalizedRuleMajorSortTrace input (.rule4c ρ) read fuel (sortedTrees[i]'hi)
              (sortedKeys[i]'(by omega)) :=
          fun i hi => List.Forall₂.get (i := i) paired (by omega) hi
        have ihAt : ∀ i (hi : i < sortedTrees.length) (child : (ruleMajorArmGraph arm).Node),
            arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents4a W D (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm)
                  E W D child) (sortedKeys[i]'(by omega)) ∧
              Represents4b W D (rule4bComponent input.moleculeGraph (ruleMajorArmGraph arm)
                  E W D child) (sortedKeys[i]'(by omega)) ∧
                Represents4c W D (rule4cComponent input.moleculeGraph (ruleMajorArmGraph arm)
                  E W D child) (sortedKeys[i]'(by omega)) := by
          intro i hi child hl
          exact (ih child (sortedTrees[i]'hi) (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
        have constAt : ∀ i (hi : i < sortedTrees.length) (child : (ruleMajorArmGraph arm).Node),
            arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
              Represents W D (ruleKey input.moleculeGraph (ruleMajorArmGraph arm) W D child)
                (sortedKeys[i]'(by omega)).constitutional := by
          intro i hi child hl
          exact (ruleMajorRootArm_node_bridge arm hW hD child (sortedTrees[i]'hi)
            (sortedKeys[i]'(by omega)) (traceAt i hi) hl).2
        have slotSorted : ((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
              (rule4abcKey input.moleculeGraph (ruleMajorArmGraph arm) E W D)).Pairwise
              (fun x y => y ≤ x) := by
          rw [List.pairwise_iff_getElem]
          intro i j hi hj hij
          rw [List.length_map, slotLength] at hi hj
          obtain ⟨childI, slotI, _, lookupI⟩ := childAt i hi
          obtain ⟨childJ, slotJ, _, lookupJ⟩ := childAt j hj
          have hneWidth : input.compareRuleMajorCumulativeDescriptor 3
              (sortedKeys[i]'(by omega)) (sortedKeys[j]'(by omega)) ≠ Ordering.lt :=
            (List.pairwise_iff_getElem.1 descending) i j (by omega) (by omega) hij
          have hle := Rule4cObservationBridge.rule4abcKey_le_of_compare_ne_lt E
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt i hi)).tableMatch
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt j hj)).tableMatch
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt i hi)).labelMatch
            (LocalizedRuleMajorSortTrace.fullMatch_of_trace (traceAt j hj)).labelMatch
            (LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt i hi))
            (LocalizedRuleMajorSortTrace.realizes_of_trace (traceAt j hj))
            (constAt i hi childI lookupI) (constAt j hj childJ lookupJ)
            (ihAt i hi childI lookupI).1 (ihAt j hj childJ lookupJ).1
            (ihAt i hi childI lookupI).2.1 (ihAt j hj childJ lookupJ).2.1
            (ihAt i hi childI lookupI).2.2 (ihAt j hj childJ lookupJ).2.2 hneWidth
          have getI : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[i]'(by
                rw [slotLength]; exact hi) = childI :=
            Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotI)
          have getJ : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
              (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[j]'(by
                rw [slotLength]; exact hj) = childJ :=
            Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotJ)
          simpa [List.getElem_map, getI, getJ] using hle
        have slotSortedOrd : ((slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
            (localizedRootTree input cursor (read cursor) sortedTrees).children.length).map
              (ordinaryKey input.moleculeGraph (ruleMajorArmGraph arm) E W D)).Pairwise
              (fun x y => y ≤ x) := by
          rw [List.pairwise_map] at slotSorted ⊢
          exact slotSorted.imp fun h =>
            (ordinaryKey_le_iff_rule4abcKey input.moleculeGraph (ruleMajorArmGraph arm) E
              hyp.rule4abcOnly W D _ _).2 h
        have hperm := slotList_perm
          (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing)
          (parent := node)
          (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length) hdense
        have consCase : ∀ (rule : StereochemicalRule)
            (enc : input.LocalizedRerootCumulativeRule45Key → List Nat → WithBot StereoLabel)
            (comp : (ruleMajorArmGraph arm).Node → Certificate.CanonicalSphereKey.Key StereoLabel),
            (∀ i (hi : i < sortedTrees.length) (child : (ruleMajorArmGraph arm).Node),
              arm.tree.decoratedSubtreeAt? child.1 = some (sortedTrees[i]'hi) →
                ∀ path, Certificate.CanonicalSphereKey.pathObservationOf W D (comp child) path =
                  enc (sortedKeys[i]'(by omega)) path) →
            (∀ child : (ruleMajorArmGraph arm).Node, comp child =
              (ofLex (ordinaryKey input.moleculeGraph (ruleMajorArmGraph arm) E W D child)).2.getD
                (stereoIndex rule) []) →
            (∀ digit path, enc (localizedCumulativeRule45StepKey input (.rule4c ρ) cursor
                (read cursor) sortedKeys) (digit :: path) =
              ((sortedKeys[digit]?).map fun childKey => enc childKey path).getD ⊥) →
            ∀ digit path,
              Certificate.CanonicalSphereKey.pathObservationOf W D (comp node) (digit :: path) =
                enc (localizedCumulativeRule45StepKey input (.rule4c ρ) cursor (read cursor) sortedKeys)
                  (digit :: path) := by
          intro rule enc comp repAt compEq encCons digit path
          rw [compEq node]
          change stereoNodePathObservation input.moleculeGraph (ruleMajorArmGraph arm) E W D rule node
            (digit :: path) = _
          rw [stereoNodePathObservation_cons input.moleculeGraph (ruleMajorArmGraph arm) E W D rule node
            hperm slotSortedOrd digit path, encCons digit path]
          by_cases hdigit : digit < sortedTrees.length
          · obtain ⟨child, slotSome, childAddr, childLookup⟩ := childAt digit hdigit
            have digitLtKeys : digit < sortedKeys.length := by omega
            have repChild := repAt digit hdigit child childLookup path
            rw [compEq child] at repChild
            rw [slotSome, List.getElem?_eq_getElem digitLtKeys]
            simp only [Option.map_some, Option.getD_some]
            by_cases hgate : digit < W ∧ path.length < D
            · rw [if_pos hgate]
              exact repChild
            · rw [if_neg hgate, ← repChild]
              symm
              apply (stereoNodePathObservation_eq_bot_iff input.moleculeGraph (ruleMajorArmGraph arm)
                E rule W D path child).2
              by_contra hne
              have bound := depth_add_length_le_of_nodePathObservation input.moleculeGraph
                (ruleMajorArmGraph arm) (W := W) (D := D) (by omega : (0 : Nat) < 3) path child hne
              have childDepth : (ruleMajorArmGraph arm).depth child =
                  (ruleMajorArmGraph arm).depth node + 1 :=
                (ruleMajorArmGraph arm).child_depth ⟨digit, childAddr⟩
              have countLe : sortedTrees.length ≤ (ruleMajorArmGraph arm).width := by
                have := count_le_width
                  (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing)
                  (parent := node)
                  (count := (localizedRootTree input cursor (read cursor) sortedTrees).children.length)
                  hdense
                rw [countEq] at this
                exact this
              have hdigitLtW : digit < W := by omega
              have hpath : ¬ path.length < D := fun h => hgate ⟨hdigitLtW, h⟩
              omega
          · have slotNone : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing node
                (localizedRootTree input cursor (read cursor) sortedTrees).children.length)[digit]? =
                  none := by
              rw [List.getElem?_eq_none_iff, slotLength]
              omega
            have keysNone : sortedKeys[digit]? = none := by
              rw [List.getElem?_eq_none_iff]
              omega
            rw [slotNone, keysNone]
            split <;> rfl
        refine ⟨slotSorted, ?_, ?_, ?_⟩
        · intro path
          cases path with
          | nil =>
              exact stereoNodePathObservation_nil_eq_encoded4a_rule4c descriptorMap unit
                (ruleMajorArmGraph arm) W D node fullMatch.tableMatch realizes
                (hyp.label node _ lookup) (hyp.tetrahedral node) (hyp.available node)
          | cons digit path =>
              exact consCase .rule4aStereogenicUnitKind encoded4a
                (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm) E W D)
                (fun i hi child hl => (ihAt i hi child hl).1) (fun _ => rfl)
                (fun digit path => encoded4a_cons_of_key_rule4c fullMatch.tableMatch realizes
                  pairedMatch digit path) digit path
        · intro path
          cases path with
          | nil =>
              exact stereoNodePathObservation_nil_eq_encoded4b_rule4c descriptorMap unit
                (ruleMajorArmGraph arm) W D node fullMatch.tableMatch realizes
                (hyp.label node _ lookup) (hyp.tetrahedral node)
          | cons digit path =>
              exact consCase .rule4bLikeUnlikeDescriptorPairs encoded4b
                (rule4bComponent input.moleculeGraph (ruleMajorArmGraph arm) E W D)
                (fun i hi child hl => (ihAt i hi child hl).2.1) (fun _ => rfl)
                (fun digit path => encoded4b_cons_of_key_rule4c fullMatch.tableMatch realizes
                  pairedMatch digit path) digit path
        · intro path
          cases path with
          | nil =>
              rw [encodedPseudo4c_nil fullMatch.tableMatch fullMatch.labelMatch realizes]
              exact stereoNodePathObservation_nil_eq_pseudoValueOfLabel descriptorMap unit
                (ruleMajorArmGraph arm) W D (senseOf ρ) node
                (localizedRootTree input cursor (read cursor) sortedTrees)
                (hyp.label node _ lookup) (hyp.available node)
          | cons digit path =>
              exact consCase .rule4cPseudoasymmetricDescriptor encodedPseudo4c
                (rule4cComponent input.moleculeGraph (ruleMajorArmGraph arm) E W D)
                (fun i hi child hl => (ihAt i hi child hl).2.2) (fun _ => rfl)
                (fun digit path => encodedPseudo4c_cons_of_key fullMatch.tableMatch fullMatch.labelMatch
                  realizes pairedMatch digit path) digit path

/-- The actual stage-4c addressing sorts every sibling pair by the independent complete 4abc
ordinary key. -/
theorem ruleMajorRootArm_keySorted_readingEvidence4c
    (hyp : RuleMajorTreeReadback4c arm.tree descriptorMap unit ρ) :
    KeySorted (ordinaryKey input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ))
        (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height)
      (toOfficialSourceTree arm.tree).declarativeAddressing := by
  intro parent first second firstSlot secondSlot addrFirst addrSecond hlt
  obtain ⟨dsub, lookup, _⟩ := ruleMajorRootArm_decoratedSubtree_of_node arm parent
  have hdense : DenseAt (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length := ruleMajorRootArm_denseAt_of_lookup arm parent dsub lookup
  rcases ruleMajorTrace_of_subtree input (.rule4c ρ) read arm.trace parent.1 dsub lookup with
    ⟨fuel', key', trace'⟩
  have bridge := ruleMajorRootArm_node_bridge4c arm hyp
    (W := (ruleMajorArmGraph arm).width) (D := (ruleMajorArmGraph arm).height)
    le_rfl le_rfl parent dsub key' trace' lookup
  have slotSorted := bridge.1
  have firstLt : firstSlot < dsub.children.length := (hdense firstSlot).1 ⟨first, addrFirst⟩
  have secondLt : secondSlot < dsub.children.length := (hdense secondSlot).1 ⟨second, addrSecond⟩
  obtain ⟨childI, slotI, addrI⟩ := slotList_getD_of_lt
    (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := parent)
    (count := dsub.children.length) hdense firstLt
  obtain ⟨childJ, slotJ, addrJ⟩ := slotList_getD_of_lt
    (addressing := (toOfficialSourceTree arm.tree).declarativeAddressing) (parent := parent)
    (count := dsub.children.length) hdense secondLt
  have firstEq : first = childI :=
    Subtype.ext (by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address] at addrFirst addrI
      exact addrFirst.trans addrI.symm)
  have secondEq : second = childJ :=
    Subtype.ext (by
      rw [(toOfficialSourceTree arm.tree).declarativeAddressing_address,
        (toOfficialSourceTree arm.tree).declarativeAddressing_address] at addrSecond addrJ
      exact addrSecond.trans addrJ.symm)
  have slotLength : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length).length = dsub.children.length := by simp [slotList]
  have getI : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length)[firstSlot]'(by rw [slotLength]; exact firstLt) = childI :=
    Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotI)
  have getJ : (slotList (toOfficialSourceTree arm.tree).declarativeAddressing parent
      dsub.children.length)[secondSlot]'(by rw [slotLength]; exact secondLt) = childJ :=
    Option.some.inj ((List.getElem?_eq_getElem _).symm.trans slotJ)
  have hpair := (List.pairwise_iff_getElem.1 slotSorted) firstSlot secondSlot
    (by rw [List.length_map, slotLength]; exact firstLt)
    (by rw [List.length_map, slotLength]; exact secondLt) hlt
  simp only [List.getElem_map, getI, getJ] at hpair
  rw [firstEq, secondEq]
  exact (ordinaryKey_le_iff_rule4abcKey input.moleculeGraph (ruleMajorArmGraph arm)
    (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ))
    hyp.rule4abcOnly (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height _ _).2 hpair

/-- The actual stage-4c addressing is ordinary-canonical under per-reference Rules 4a, 4b and
the molecule-derived Rule-4c pseudoasymmetric observation. -/
theorem ruleMajorRootArm_ordinaryCanonicalAddressing_readingEvidence4c
    (hyp : RuleMajorTreeReadback4c arm.tree descriptorMap unit ρ) :
    OrdinaryCanonicalAddressing input.moleculeGraph
      (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ))
      (toOfficialSourceTree arm.tree).declarativeAddressing :=
  ⟨(toOfficialSourceTree arm.tree).declarativeAddressing_dense,
    ruleMajorRootArm_keySorted_readingEvidence4c arm hyp⟩

/-- Root Rule-4a representation for the actual stage-4c arm. -/
theorem ruleMajorRootArm_root_represents4a_rule4c
    (hyp : RuleMajorTreeReadback4c arm.tree descriptorMap unit ρ) :
    Represents4a (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
      (rule4aComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ))
        (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height (ruleMajorArmGraph arm).root)
      arm.key :=
  (ruleMajorRootArm_node_bridge4c arm hyp le_rfl le_rfl
    (ruleMajorArmGraph arm).root arm.tree arm.key arm.trace rfl).2.1

/-- Root Rule-4b representation for the actual stage-4c arm. -/
theorem ruleMajorRootArm_root_represents4b_rule4c
    (hyp : RuleMajorTreeReadback4c arm.tree descriptorMap unit ρ) :
    Represents4b (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
      (rule4bComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ))
        (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height (ruleMajorArmGraph arm).root)
      arm.key :=
  (ruleMajorRootArm_node_bridge4c arm hyp le_rfl le_rfl
    (ruleMajorArmGraph arm).root arm.tree arm.key arm.trace rfl).2.2.1

/-- Root Rule-4c representation retains both pseudoasymmetric auxiliary values `r` and `s`. -/
theorem ruleMajorRootArm_root_represents4c
    (hyp : RuleMajorTreeReadback4c arm.tree descriptorMap unit ρ) :
    Represents4c (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height
      (rule4cComponent input.moleculeGraph (ruleMajorArmGraph arm)
        (readingEvidence4c input.moleculeGraph descriptorMap unit (ruleMajorArmGraph arm) (senseOf ρ))
        (ruleMajorArmGraph arm).width (ruleMajorArmGraph arm).height (ruleMajorArmGraph arm).root)
      arm.key :=
  (ruleMajorRootArm_node_bridge4c arm hyp le_rfl le_rfl
    (ruleMajorArmGraph arm).root arm.tree arm.key arm.trace rfl).2.2.2

end RuleMajorRootArmRule4c

end
end Rule4aTableBridge
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.RuleMajorTreeReadback4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.encodedPseudo4c_nil
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.encodedPseudo4c_cons_of_key
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.encoded4a_cons_of_key_rule4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.encoded4b_cons_of_key_rule4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.stereoNodePathObservation_nil_eq_pseudoValueOfLabel
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.stereoNodePathObservation_nil_eq_pseudoValueOfLabel_noReference
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.stereoNodePathObservation_nil_eq_encoded4a_rule4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.stereoNodePathObservation_nil_eq_encoded4b_rule4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_terminal_bridge4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_node_bridge4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_keySorted_readingEvidence4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_ordinaryCanonicalAddressing_readingEvidence4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_root_represents4a_rule4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_root_represents4b_rule4c
assert_kernel_only TetraStereo.OneCenter.Rule4aTableBridge.ruleMajorRootArm_root_represents4c
