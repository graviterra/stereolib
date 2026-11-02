import TetraStereo.OneCenter.AuthoritativeLocalizedRuleMajorAnalysis
import TetraStereo.OneCenter.AuthoritativeSemanticAromaticKekuleNormalization
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3AutomorphismNaturality
import TetraStereo.OneCenter.LocalizedSpiroAuthoritativeOccurrenceFrame
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

noncomputable section

/-!
# Exact/Nat constitutional projection bridge on honest no-localized-mancude scope

The exact-rational official key compiler reads Rule 1a from the independent maximum-matching
semantics.  On ordinary atoms those observations are integral.  This module proves that on the
sound, genuinely narrower domain where *no* localized mancude edge exists at all, every exact
Rule-1a observation is literally the integral atomic number projected from the same official
provenance node.  Consequently the exact observed comparator and the historical natural-number
rule-major comparator agree on source-aligned keys with the same provenance tree.

## Scope boundary

`noMancude : ∀ a b, ¬ moleculeGraph.LocalizedMancudeEdge a b` is a real hypothesis, not a
definitional convenience.  Localized admission by itself does **not** imply it: a heterocyclic
Kekule representation can require the rational maximum-matching average of a localized
multiple-bond duplicate.  On the no-localized-edge domain the exact observation collapses to an
integral observation, and the rational comparator collapses to natural-number comparison.
Nothing here is claimed for chemistry containing genuine localized mancude edges.

## Sufficient checkable domain

The final theorems expose a decidable sufficient condition: an exact source/candidate aromatic
mancude edge-set test together with the direct localized covalent pair-bond admission predicate
implies `noMancude` through the existing semantic aromatic-realization theory.
-/

namespace CertifiedLocalizedCIPInput

/-- The Rule-1a atomic-number component of an official node label is the graph atomic number of
its current atom.  Non-real provenance (duplicates and placeholders) carries the integral atomic
number as its first label component; real atoms carry the raw CIP label. -/
theorem officialNodeAtomLabel_ofLex_first_eq_atomZ
    (input : CertifiedLocalizedCIPInput) (node : OfficialCIPNode input.Atom)
    (atom : input.Atom) (current : node.current? = some atom) :
    (ofLex (input.moleculeGraph.officialNodeAtomLabel node)).1 =
      input.moleculeGraph.atomZ atom := by
  cases node with
  | mk observedCurrent history provenance =>
      cases observedCurrent with
      | none => simp at current
      | some observed =>
          simp only [Option.some.injEq] at current
          subst observed
          cases provenance <;> rfl

/-- On the no-localized-mancude-edge domain, the executable exact Rule-1a observation of every
official provenance node is exactly the integral atomic-number projection of that node's official
atom label.  This is the comparison-visible exact/Nat projection bridge. -/
theorem semanticExactOfficialRule1aObservation_eq_ofNat_officialNodeAtomLabel
    (input : CertifiedLocalizedCIPInput)
    (noMancude : ∀ left right,
      ¬ input.moleculeGraph.LocalizedMancudeEdge left right)
    (node : OfficialCIPNode input.Atom) :
    input.certified.input.molecule.semanticExactOfficialRule1aObservation node =
      DeclarativeCIP.ExactAtomicNumber.ofNat
        (ofLex (input.moleculeGraph.officialNodeAtomLabel node)).1 := by
  rw [input.executableExactOfficialRule1aObservation_correct]
  cases node with
  | mk current history provenance =>
      cases current with
      | none =>
          simp [MoleculeGraph.exactOfficialRule1aObservation,
            MoleculeGraph.officialNodeAtomLabel,
            DeclarativeCIP.ExactAtomicNumber.zero]
      | some atom =>
          cases provenance with
          | realAtom =>
              simp [MoleculeGraph.exactOfficialRule1aObservation,
                MoleculeGraph.officialNodeAtomLabel, MoleculeGraph.rawCIPAtomLabel]
          | ringDuplicate distance =>
              simp [MoleculeGraph.exactOfficialRule1aObservation,
                MoleculeGraph.officialNodeAtomLabel]
          | placeholder kind distance =>
              simp [MoleculeGraph.exactOfficialRule1aObservation,
                MoleculeGraph.officialNodeAtomLabel]
          | multipleBondDuplicate distance =>
              cases history with
              | nil =>
                  simp [MoleculeGraph.exactOfficialRule1aObservation,
                    MoleculeGraph.officialNodeAtomLabel, OfficialCIPNode.parent?]
              | cons first rest =>
                  cases rest with
                  | nil =>
                      simp [MoleculeGraph.exactOfficialRule1aObservation,
                        MoleculeGraph.officialNodeAtomLabel, OfficialCIPNode.parent?]
                  | cons parent tail =>
                      simp only [MoleculeGraph.exactOfficialRule1aObservation,
                        OfficialCIPNode.parent?]
                      rw [MoleculeGraph.exactRule1aMultipleBond_of_not_localized
                        input.moleculeGraph (noMancude parent atom)]
                      rw [officialNodeAtomLabel_ofLex_first_eq_atomZ input
                        ⟨some atom, first :: parent :: tail,
                          OfficialCIPNodeProvenance.multipleBondDuplicate distance⟩
                        atom rfl]

/-- Decidable sufficient domain: an exact aromatic mancude edge-set test together with direct
localized pair-bond admission yields the full no-localized-mancude-edge scope. -/
theorem noMancude_of_exactAromaticMancudeEdgeSet_and_localizedCovalentPairsOnly
    (input : CertifiedLocalizedCIPInput)
    (exactTest : input.certified.input.molecule.semanticAromaticMancudeEdgeSetExact?
      input.certified.input.molecule = true)
    (localized : input.certified.input.molecule.LocalizedCovalentPairsOnly) :
    ∀ left right, ¬ input.moleculeGraph.LocalizedMancudeEdge left right := by
  have exactEdges :=
    (SemanticMolecule.semanticAromaticMancudeEdgeSetExact?_eq_true_iff
      input.certified.input.molecule input.certified.input.molecule).mp exactTest
  have noAromaticEdges :=
    SemanticMolecule.aromaticPairEdges_eq_nil_of_localizedCovalentPairsOnly
      input.certified.input.molecule localized
  intro left right
  exact AuthoritativeChemicalInput.no_localizedMancudeEdge_of_no_aromatic_edges
    input.certified.input exactEdges noAromaticEdges left right

/-- Node-level exact/Nat projection bridge under the checkable sufficient domain. -/
theorem semanticExactOfficialRule1aObservation_eq_ofNat_of_sufficientDomain
    (input : CertifiedLocalizedCIPInput)
    (exactTest : input.certified.input.molecule.semanticAromaticMancudeEdgeSetExact?
      input.certified.input.molecule = true)
    (localized : input.certified.input.molecule.LocalizedCovalentPairsOnly)
    (node : OfficialCIPNode input.Atom) :
    input.certified.input.molecule.semanticExactOfficialRule1aObservation node =
      DeclarativeCIP.ExactAtomicNumber.ofNat
        (ofLex (input.moleculeGraph.officialNodeAtomLabel node)).1 :=
  input.semanticExactOfficialRule1aObservation_eq_ofNat_officialNodeAtomLabel
    (input.noMancude_of_exactAromaticMancudeEdgeSet_and_localizedCovalentPairsOnly
      exactTest localized)
    node

end CertifiedLocalizedCIPInput

namespace ExactOfficialRuleMajorKey

/-- Exact comparison of integral observations is natural-number comparison.  This is the
comparator-level half of the exact/Nat projection bridge. -/
theorem compareExactAtomicNumber_ofNat (left right : ℕ) :
    compareExactAtomicNumber
        (DeclarativeCIP.ExactAtomicNumber.ofNat left)
        (DeclarativeCIP.ExactAtomicNumber.ofNat right) =
      OfficialRuleMajorKey.compareNat left right := by
  unfold OfficialRuleMajorKey.compareNat
  cases compared : Ord.compare left right with
  | lt =>
      have lower : left < right := compare_lt_iff_lt.mp compared
      exact compareExactAtomicNumber_ofNat_lt lower
  | eq =>
      have equal : left = right := compare_eq_iff_eq.mp compared
      subst right
      unfold compareExactAtomicNumber Ordering.byKey
      simp only [DeclarativeCIP.ExactAtomicNumber.value,
        DeclarativeCIP.ExactAtomicNumber.ofNat, Nat.cast_one, div_one]
      exact Std.ReflOrd.compare_self
  | gt =>
      have higher : right < left := compare_gt_iff_gt.mp compared
      exact compareExactAtomicNumber_ofNat_gt higher

/-- Whole-entry projection transport: comparing integral observations at the same positional
address is exactly natural-number comparison of the underlying labels. -/
theorem compareSparseEntry_ofNat (left right : OfficialSparseEntry ℕ) :
    OfficialRuleMajorKey.compareSparseEntry
        compareExactAtomicNumber
        (left.1, DeclarativeCIP.ExactAtomicNumber.ofNat left.2)
        (right.1, DeclarativeCIP.ExactAtomicNumber.ofNat right.2) =
      OfficialRuleMajorKey.compareSparseEntry
        OfficialRuleMajorKey.compareNat left right := by
  rcases left with ⟨leftPosition, leftValue⟩
  rcases right with ⟨rightPosition, rightValue⟩
  unfold OfficialRuleMajorKey.compareSparseEntry
  simp only [Ordering.byKey, compareLex]
  rw [compareExactAtomicNumber_ofNat]

/-- Whole-layer projection transport. -/
theorem compareSparseLayer_ofNat
    (left right : List (OfficialSparseEntry ℕ)) :
    OfficialRuleMajorKey.compareSparseLayer compareExactAtomicNumber
        (left.map fun entry =>
          (entry.1, DeclarativeCIP.ExactAtomicNumber.ofNat entry.2))
        (right.map fun entry =>
          (entry.1, DeclarativeCIP.ExactAtomicNumber.ofNat entry.2)) =
      OfficialRuleMajorKey.compareSparseLayer
        OfficialRuleMajorKey.compareNat left right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons rightHead rightTail => rfl
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => rfl
      | cons rightHead rightTail =>
          unfold OfficialRuleMajorKey.compareSparseLayer
          simp only [List.map_cons, List.compareLex_cons_cons]
          rw [compareSparseEntry_ofNat]
          cases compared : OfficialRuleMajorKey.compareSparseEntry
              OfficialRuleMajorKey.compareNat leftHead rightHead with
          | lt => rfl
          | eq => simpa using inductionHypothesis rightTail
          | gt => rfl

/-- Nested sparse-source projection transport: every addressed sphere layer is transported at
once, so the full Rule-1a source projection can be compared in either representation. -/
theorem compareSparseLayers_ofNat
    (left right : List (List (OfficialSparseEntry ℕ))) :
    OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
        (left.map fun layer => layer.map fun entry =>
          (entry.1, DeclarativeCIP.ExactAtomicNumber.ofNat entry.2))
        (right.map fun layer => layer.map fun entry =>
          (entry.1, DeclarativeCIP.ExactAtomicNumber.ofNat entry.2)) =
      OfficialRuleMajorKey.compareSparseLayers
        OfficialRuleMajorKey.compareNat left right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons rightHead rightTail => rfl
  | cons leftHead leftTail inductionHypothesis =>
      cases right with
      | nil => rfl
      | cons rightHead rightTail =>
          unfold OfficialRuleMajorKey.compareSparseLayers
          simp only [List.map_cons, List.compareLex_cons_cons]
          rw [compareSparseLayer_ofNat]
          cases compared : OfficialRuleMajorKey.compareSparseLayer
              OfficialRuleMajorKey.compareNat leftHead rightHead with
          | lt => rfl
          | eq => simpa using inductionHypothesis rightTail
          | gt => rfl

/-- Lifting the integral observation map through nested source projections commutes with
`mapSourceLayers`: applying `ofNat` after an arbitrary node-level label map is the same as first
mapping the labels and then lifting each addressed entry. -/
theorem mapSourceLayers_ofNat_mapSourceLayers
    {V : Type*} (label : V → ℕ)
    (layers : List (List (OfficialSparseEntry V))) :
    OfficialRuleMajorKey.mapSourceLayers
        (fun node => DeclarativeCIP.ExactAtomicNumber.ofNat (label node)) layers =
      (OfficialRuleMajorKey.mapSourceLayers label layers).map
        (List.map fun entry =>
          (entry.1, DeclarativeCIP.ExactAtomicNumber.ofNat entry.2)) := by
  unfold OfficialRuleMajorKey.mapSourceLayers OfficialRuleMajorKey.mapObservation
  simp only [List.map_map, Function.comp_def]

/-- Nested sparse source projections commute with the exact/Nat observation lift.  Consequently
Rule-1a comparisons of exactly observed source layers are natural comparisons of the underlying
label layers. -/
theorem compareSparseLayers_mapSourceLayers_ofNat
    {V : Type*} (label : V → ℕ)
    (left right : List (List (OfficialSparseEntry V))) :
    OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
        (OfficialRuleMajorKey.mapSourceLayers
          (fun node => DeclarativeCIP.ExactAtomicNumber.ofNat (label node)) left)
        (OfficialRuleMajorKey.mapSourceLayers
          (fun node => DeclarativeCIP.ExactAtomicNumber.ofNat (label node)) right) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (OfficialRuleMajorKey.mapSourceLayers label left)
        (OfficialRuleMajorKey.mapSourceLayers label right) := by
  rw [mapSourceLayers_ofNat_mapSourceLayers,
    mapSourceLayers_ofNat_mapSourceLayers]
  exact compareSparseLayers_ofNat _ _

/-- Comparison-visible bridge: on honest no-localized-mancude scope, the exact observed
Rule-major comparator on compiled exact keys equals the historical natural-number rule-major
comparator on source-aligned ordinary keys carrying the same provenance tree.

`SourceAligned` is a concrete projection invariant of the compiled keys; no comparison or key
equality is assumed. -/
theorem compareObserved_eq_compare_of_sourceAligned_of_noMancude
    (input : CertifiedLocalizedCIPInput)
    (noMancude : ∀ left right,
      ¬ input.moleculeGraph.LocalizedMancudeEdge left right)
    (left right : OfficialRuleMajorKey input.Atom)
    (leftAligned : OfficialRuleMajorKey.SourceAligned input.moleculeGraph left)
    (rightAligned : OfficialRuleMajorKey.SourceAligned input.moleculeGraph right)
    (leftExact rightExact : ExactOfficialRuleMajorKey input.Atom)
    (leftSources : leftExact.sourceNodes = left.sourceNodes)
    (rightSources : rightExact.sourceNodes = right.sourceNodes) :
    ExactOfficialRuleMajorKey.compareObserved input.moleculeGraph
        input.certified.input.molecule.semanticExactOfficialRule1aObservation
        leftExact rightExact =
      OfficialRuleMajorKey.compare left right := by
  let observe : OfficialCIPNode input.Atom → DeclarativeCIP.ExactAtomicNumber :=
    input.certified.input.molecule.semanticExactOfficialRule1aObservation
  have observeEq : observe =
      fun node => DeclarativeCIP.ExactAtomicNumber.ofNat
        (ofLex (input.moleculeGraph.officialNodeAtomLabel node)).1 :=
    funext
      (input.semanticExactOfficialRule1aObservation_eq_ofNat_officialNodeAtomLabel
        noMancude)
  rcases leftAligned with ⟨leftRule1a, leftRule1b, leftRule2⟩
  rcases rightAligned with ⟨rightRule1a, rightRule1b, rightRule2⟩
  unfold ExactOfficialRuleMajorKey.compareObserved OfficialRuleMajorKey.compare
    Ordering.byKey
  unfold ExactOfficialRuleMajorKey.compareAddressedSourcesObserved compareLex
    Ordering.byKey
  have rule1aComparison :
      OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
          (ExactOfficialRuleMajorKey.observedRule1aLayers observe
            leftExact.sourceNodes)
          (ExactOfficialRuleMajorKey.observedRule1aLayers observe
            rightExact.sourceNodes) =
        OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          left.rule1a right.rule1a := by
    have layers : ExactOfficialRuleMajorKey.observedRule1aLayers observe =
        OfficialRuleMajorKey.mapSourceLayers
          (fun node => DeclarativeCIP.ExactAtomicNumber.ofNat
            (ofLex (input.moleculeGraph.officialNodeAtomLabel node)).1) := by
      unfold ExactOfficialRuleMajorKey.observedRule1aLayers
      rw [observeEq]
    rw [layers]
    rw [compareSparseLayers_mapSourceLayers_ofNat
      (fun node => (ofLex (input.moleculeGraph.officialNodeAtomLabel node)).1)
      leftExact.sourceNodes rightExact.sourceNodes]
    rw [leftSources, rightSources, ← leftRule1a, ← rightRule1a]
  have rule1bComparison :
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
          (ExactOfficialRuleMajorKey.rule1bLayers leftExact.sourceNodes)
          (ExactOfficialRuleMajorKey.rule1bLayers rightExact.sourceNodes) =
        OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
          left.rule1b right.rule1b := by
    have leftLayers :
        ExactOfficialRuleMajorKey.rule1bLayers leftExact.sourceNodes =
          left.rule1b := by
      unfold ExactOfficialRuleMajorKey.rule1bLayers
      rw [leftSources, ← leftRule1b]
    have rightLayers :
        ExactOfficialRuleMajorKey.rule1bLayers rightExact.sourceNodes =
          right.rule1b := by
      unfold ExactOfficialRuleMajorKey.rule1bLayers
      rw [rightSources, ← rightRule1b]
    rw [leftLayers, rightLayers]
  have rule2Comparison :
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          (ExactOfficialRuleMajorKey.rule2Layers input.moleculeGraph
            leftExact.sourceNodes)
          (ExactOfficialRuleMajorKey.rule2Layers input.moleculeGraph
            rightExact.sourceNodes) =
        OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          left.rule2 right.rule2 := by
    have leftLayers :
        ExactOfficialRuleMajorKey.rule2Layers input.moleculeGraph
            leftExact.sourceNodes = left.rule2 := by
      unfold ExactOfficialRuleMajorKey.rule2Layers
      rw [leftSources, ← leftRule2]
    have rightLayers :
        ExactOfficialRuleMajorKey.rule2Layers input.moleculeGraph
            rightExact.sourceNodes = right.rule2 := by
      unfold ExactOfficialRuleMajorKey.rule2Layers
      rw [rightSources, ← rightRule2]
    rw [leftLayers, rightLayers]
  rw [rule1aComparison]
  simp only [rule1bComparison, rule2Comparison]

/-- Checkable sufficient-domain comparison bridge: the exact observed comparator equals the
historical rule-major comparator whenever the exact aromatic edge-set test succeeds and the input
is admitted as localized covalent pairs only. -/
theorem compareObserved_eq_compare_of_sourceAligned_of_sufficientDomain
    (input : CertifiedLocalizedCIPInput)
    (exactTest : input.certified.input.molecule.semanticAromaticMancudeEdgeSetExact?
      input.certified.input.molecule = true)
    (localized : input.certified.input.molecule.LocalizedCovalentPairsOnly)
    (left right : OfficialRuleMajorKey input.Atom)
    (leftAligned : OfficialRuleMajorKey.SourceAligned input.moleculeGraph left)
    (rightAligned : OfficialRuleMajorKey.SourceAligned input.moleculeGraph right)
    (leftExact rightExact : ExactOfficialRuleMajorKey input.Atom)
    (leftSources : leftExact.sourceNodes = left.sourceNodes)
    (rightSources : rightExact.sourceNodes = right.sourceNodes) :
    ExactOfficialRuleMajorKey.compareObserved input.moleculeGraph
        input.certified.input.molecule.semanticExactOfficialRule1aObservation
        leftExact rightExact =
      OfficialRuleMajorKey.compare left right :=
  compareObserved_eq_compare_of_sourceAligned_of_noMancude input
    (input.noMancude_of_exactAromaticMancudeEdgeSet_and_localizedCovalentPairsOnly
      exactTest localized)
    left right leftAligned rightAligned leftExact rightExact leftSources rightSources

end ExactOfficialRuleMajorKey

end

end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.officialNodeAtomLabel_ofLex_first_eq_atomZ
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.semanticExactOfficialRule1aObservation_eq_ofNat_officialNodeAtomLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.noMancude_of_exactAromaticMancudeEdgeSet_and_localizedCovalentPairsOnly
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.semanticExactOfficialRule1aObservation_eq_ofNat_of_sufficientDomain
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.compareExactAtomicNumber_ofNat
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.compareSparseEntry_ofNat
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.compareSparseLayer_ofNat
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.compareSparseLayers_ofNat
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.mapSourceLayers_ofNat_mapSourceLayers
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.compareSparseLayers_mapSourceLayers_ofNat
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.compareObserved_eq_compare_of_sourceAligned_of_noMancude
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.compareObserved_eq_compare_of_sourceAligned_of_sufficientDomain
