import TetraStereo.OneCenter.DeclarativeCIPRule1aExact
import TetraStereo.OneCenter.ProductionCIPRule1bSoundness

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

noncomputable section

open DeclarativeCIP

namespace RawMolecule

/-!
# Production/declarative Rule-1a observation correspondence

Production compares exact nonnegative rational atomic-number labels.  The original declarative
`NodeLabel` observation is only a natural atomic number, so the two carriers agree automatically
away from multiple-bond duplicates.  At a multiple-bond duplicate, production may instead carry a
Mancude/Kekule average.  This module exposes that boundary explicitly rather than silently
projecting the rational value back to the duplicated atom's written atomic number.
-/

/-- Interpret the production label as the independent positive-rational Rule-1a carrier.  The
effective denominator preserves production's documented totalization of malformed hand-built
zero-denominator labels; every label actually emitted by production already has positive
denominator. -/
def CIPAtomicLabel.toExactAtomicNumber (label : CIPAtomicLabel) :
    ExactAtomicNumber where
  numerator := label.numerator
  denominator := label.effectiveDenominator
  denominator_pos := by simp [CIPAtomicLabel.effectiveDenominator]

/-- Production's cross-product comparison is exactly comparison of the independent rational
values, including for Mancude/Kekule averages. -/
theorem compareCIPAtomicLabel_eq_exactOutcomeValue
    (left right : CIPAtomicLabel) :
    compareCIPAtomicLabel left right =
      compareOfLessAndEq left.toExactAtomicNumber.value right.toExactAtomicNumber.value := by
  unfold compareCIPAtomicLabel CIPAtomicLabel.toExactAtomicNumber ExactAtomicNumber.value
  rw [LinearOrder.compare_eq_compareOfLessAndEq]
  unfold compareOfLessAndEq
  have leftPositive : (0 : ℚ) < left.effectiveDenominator := by
    have : 0 < left.effectiveDenominator := by
      simp [CIPAtomicLabel.effectiveDenominator]
    exact_mod_cast this
  have rightPositive : (0 : ℚ) < right.effectiveDenominator := by
    have : 0 < right.effectiveDenominator := by
      simp [CIPAtomicLabel.effectiveDenominator]
    exact_mod_cast this
  simp only [div_lt_div_iff₀ leftPositive rightPositive,
    div_eq_div_iff leftPositive.ne' rightPositive.ne']
  norm_cast

/-- The checked production node comparator has precisely the independent exact-rational outcome
whenever both optional observations are available. -/
theorem compareCanonicalNodeRule?_rule1a_exactOutcome_iff
    (mol : RawMolecule) (left right : CanonicalBranchNode)
    (leftLabel rightLabel : CIPAtomicLabel)
    (hleft : mol.canonicalRule1aLabel? left = some leftLabel)
    (hright : mol.canonicalRule1aLabel? right = some rightLabel)
    (outcome : Ordering) :
    mol.compareCanonicalNodeRule? CanonicalRuleStage.rule1a left right = some outcome ↔
      ExactAtomicNumber.Outcome leftLabel.toExactAtomicNumber
        rightLabel.toExactAtomicNumber outcome := by
  simp [compareCanonicalNodeRule?, hleft, hright, ExactAtomicNumber.Outcome,
    compareCIPAtomicLabel_eq_exactOutcomeValue]
  rw [LinearOrder.compare_eq_compareOfLessAndEq]

/-- Global partial correctness of the production Mancude/Kekule labeler against the independent
maximum-matching semantics.  It is deliberately an implication from a successful result:
unsupported systems may be refused with `none`, but no returned rational label may be wrong. -/
def MancudeRule1aSound (mol : RawMolecule) : Prop :=
  ∀ (attached duplicated : Fin mol.atomCount) (label : CIPAtomicLabel),
    mol.mancudeRule1aLabel? attached.1 duplicated.1 = some label →
      label.toExactAtomicNumber.value =
        (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value

/-- Every realized production multiple-bond source retained evidence that its optional Rule-1a
labeler succeeded.  This proposition is named separately from chemical soundness; successful
complete compilation proves it from the preflight evidence retained by `CanonicalCompleteBuild`.
-/
def CanonicalBranchKey.MultipleRule1aSupportedOn
    (mol : RawMolecule) (key : CanonicalBranchKey) : Prop :=
  ∀ (node : key.HierarchyNode) (source : CanonicalBranchNode),
    key.sourceNodeAtAddress? node.1 = some source →
    ∀ distance, source.provenance =
      CanonicalNodeProvenance.multipleBondDuplicate distance →
      ∃ label, mol.canonicalRule1aLabel? source = some label

private theorem listGet?_eq_some_get {alpha : Type*} (values : List alpha)
    (index : Fin values.length) :
    listGet? values index = some (values.get index) := by
  induction values with
  | nil => exact Fin.elim0 index
  | cons value values inductionHypothesis =>
      refine Fin.cases ?_ (fun tail => ?_) index
      · rfl
      · simpa [listGet?] using inductionHypothesis tail

/-- A successful parsed-atom lookup has the same atomic number as the corresponding `Fin` atom in
the proof-facing molecule graph. -/
theorem atomZAt_eq_toMoleculeGraph_atomZ (mol : RawMolecule) (atom : ℕ)
    (hbound : atom < mol.atomCount) :
    mol.atomZAt atom = mol.toMoleculeGraph.atomZ ⟨atom, hbound⟩ := by
  unfold atomZAt atomAt?
  rw [listGet?_eq_some_get mol.atoms ⟨atom, hbound⟩]
  rfl

/-- The nonlocalized multiple-bond branch is already exact.  The two explicit hypotheses isolate
the still-separate proof that the raw finite edge detector and the independent relational graph
agree about localization; no maximum-matching theorem is needed in this case. -/
theorem mancudeRule1aLabel?_sound_of_not_localized
    (mol : RawMolecule) (attached duplicated : Fin mol.atomCount)
    (hraw : containsUndirectedEdge mol.localizedMancudeEdges attached.1 duplicated.1 = false)
    (hsemantic : ¬ mol.toMoleculeGraph.LocalizedMancudeEdge attached duplicated)
    (label : CIPAtomicLabel)
    (hlabel : mol.mancudeRule1aLabel? attached.1 duplicated.1 = some label) :
    label.toExactAtomicNumber.value =
      (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value := by
  have hlabelEq : label = { numerator := mol.atomZAt duplicated.1, denominator := 1 } := by
    unfold mancudeRule1aLabel? at hlabel
    simp [hraw] at hlabel
    exact hlabel.symm
  subst label
  rw [mol.toMoleculeGraph.exactRule1aMultipleBond_of_not_localized hsemantic]
  unfold CIPAtomicLabel.toExactAtomicNumber ExactAtomicNumber.value
    ExactAtomicNumber.ofNat
  simp [CIPAtomicLabel.effectiveDenominator,
    mol.atomZAt_eq_toMoleculeGraph_atomZ duplicated.1 duplicated.2]

/-! ## Fuel erasure for the maximum-matching computation -/

/-- The full maximum-matching summary obtained by exhaustive exclude/include recursion, with no
implementation fuel parameter.  Taking an edge removes every remaining incident edge from the
included branch, so the recursive call is on a strictly shorter list.

This definition is useful as the algorithm-independent termination boundary of the production
search.  A subsequent graph-realization theorem can identify its edge-occurrence family with the
finite partner-function family in the independent Rule-1a specification. -/
def exhaustiveMancudeMatchingStats (mol : RawMolecule) (attached : ℕ) :
    List (ℕ × ℕ) → MancudeMatchingStats
  | [] => { size := 0, count := 1, partnerZSum := 0 }
  | edge :: edges =>
      let excluded := mol.exhaustiveMancudeMatchingStats attached edges
      let remaining := edges.filter fun candidate =>
        candidate.1 != edge.1 && candidate.2 != edge.1 &&
          candidate.1 != edge.2 && candidate.2 != edge.2
      let includedTail := mol.exhaustiveMancudeMatchingStats attached remaining
      let partnerZ :=
        if edge.1 == attached then mol.atomZAt edge.2
        else if edge.2 == attached then mol.atomZAt edge.1
        else 0
      let included : MancudeMatchingStats :=
        { size := includedTail.size + 1
          count := includedTail.count
          partnerZSum := includedTail.partnerZSum + includedTail.count * partnerZ }
      combineMancudeStats excluded included
termination_by edges => edges.length
decreasing_by
  simp_wf
  simpa using (List.length_filter_le
    (fun candidate : {candidate // candidate ∈ edges} =>
      candidate.val.1 != edge.1 && candidate.val.2 != edge.1 &&
        candidate.val.1 != edge.2 && candidate.val.2 != edge.2) edges.attach)

/-- Whenever fuel strictly exceeds the edge-list length, the production search returns the exact
fuel-free exhaustive summary.  Thus the `edges.length + 1` call used by production never truncates
the maximum-matching enumeration. -/
theorem mancudeMatchingStats_eq_exhaustive (mol : RawMolecule) (attached : ℕ) :
    ∀ fuel edges, edges.length < fuel →
      mol.mancudeMatchingStats attached fuel edges =
        some (mol.exhaustiveMancudeMatchingStats attached edges) := by
  intro fuel
  induction fuel with
  | zero =>
      intro edges hlength
      omega
  | succ fuel inductionHypothesis =>
      intro edges hlength
      cases edges with
      | nil =>
          rw [exhaustiveMancudeMatchingStats.eq_1]
          rfl
      | cons edge edges =>
          let remaining := edges.filter fun candidate =>
            candidate.1 != edge.1 && candidate.2 != edge.1 &&
              candidate.1 != edge.2 && candidate.2 != edge.2
          have htail : edges.length < fuel := by
            simpa using hlength
          have hremainingLe : remaining.length ≤ edges.length := by
            exact List.length_filter_le _ _
          have hremaining : remaining.length < fuel := hremainingLe.trans_lt htail
          simp only [mancudeMatchingStats]
          rw [inductionHypothesis edges htail,
            inductionHypothesis remaining hremaining]
          rw [exhaustiveMancudeMatchingStats.eq_2]
          simp [remaining]

@[simp] theorem mancudeMatchingStats_length_succ (mol : RawMolecule) (attached : ℕ)
    (edges : List (ℕ × ℕ)) :
    mol.mancudeMatchingStats attached (edges.length + 1) edges =
      some (mol.exhaustiveMancudeMatchingStats attached edges) := by
  apply mol.mancudeMatchingStats_eq_exhaustive attached
  omega

end RawMolecule

namespace RawMolecule.CanonicalBranchKey

/-- The natural-valued declarative Rule-1a observation represented at a realized production node.

This theorem is unconditional for every provenance.  Its right-hand side makes the information
loss visible: a multiple-bond duplicate still projects to the atomic number of its written
duplicate atom, while a production Rule-1a label may be a rational Mancude/Kekule average. -/
theorem nodeAtomicNumber_eq_sourceProjection
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source) :
    nodeAtomicNumber (mol.canonicalHierarchyMoleculeGraph center ligand)
        (some ((key.toDeclarativeDigraph mol).label node)) =
      match source.provenance with
      | CanonicalNodeProvenance.phantom _ => 0
      | _ => mol.atomZAt source.atom := by
  change nodeAtomicNumber (mol.canonicalHierarchyMoleculeGraph center ligand)
      (some (key.declarativeLabel mol node)) = _
  have hcoherent := key.sourceCoherent_of_root_and_childrenExact
    mol center ligand hwellFormed hroot hexact node source hsource
  rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol node source hsource]
  cases hprovenance : source.provenance with
  | phantom distance => simp [nodeAtomicNumber]
  | realAtom | multipleBondDuplicate | ringDuplicate =>
      have hbound : source.atom < mol.atomCount := by
        simpa [hprovenance] using hcoherent.2
      simp [nodeAtomicNumber, atomFin?, hbound,
        RawMolecule.atomZAt_eq_toMoleculeGraph_atomZ mol source.atom hbound]

/-- Off the Mancude/Kekule constructor, the checked production Rule-1a label is exactly the
integral encoding of the declarative natural observation. -/
theorem canonicalRule1aLabel?_eq_integral_nodeAtomicNumber_of_not_multiple
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source)
    (hnotMultiple : ∀ distance,
      source.provenance ≠ CanonicalNodeProvenance.multipleBondDuplicate distance) :
    mol.canonicalRule1aLabel? source =
      some
        { numerator := nodeAtomicNumber
            (mol.canonicalHierarchyMoleculeGraph center ligand)
            (some ((key.toDeclarativeDigraph mol).label node))
          denominator := 1 } := by
  have hobservation := key.nodeAtomicNumber_eq_sourceProjection mol center ligand
    hwellFormed hroot hexact node source hsource
  cases hprovenance : source.provenance with
  | realAtom | ringDuplicate =>
      simp [RawMolecule.canonicalRule1aLabel?, hprovenance, hobservation]
  | phantom =>
      simp [RawMolecule.canonicalRule1aLabel?, hprovenance, hobservation]
  | multipleBondDuplicate distance =>
      exact (hnotMultiple distance hprovenance).elim

/-- The independent exact observation itself reduces to the natural declarative observation away
from multiple-bond duplicates.  Rule 1a deliberately uses `mol.toMoleculeGraph`: Mancude
constitution is read from the raw molecular graph and must not inherit the separate P/S oxido
root-edge convention of `canonicalHierarchyMoleculeGraph`. -/
theorem exactRule1aNodeObservation_eq_ofNat_nodeAtomicNumber_of_not_multiple
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source)
    (hnotMultiple : ∀ distance,
      source.provenance ≠ CanonicalNodeProvenance.multipleBondDuplicate distance) :
    exactRule1aNodeObservation mol.toMoleculeGraph (key.toDeclarativeDigraph mol)
        (key.declarativeAddressing mol) node =
      .ofNat (nodeAtomicNumber
        (mol.canonicalHierarchyMoleculeGraph center ligand)
        (some ((key.toDeclarativeDigraph mol).label node))) := by
  change exactRule1aNodeObservation mol.toMoleculeGraph (key.toDeclarativeDigraph mol)
      (key.declarativeAddressing mol) node =
    .ofNat (nodeAtomicNumber (mol.canonicalHierarchyMoleculeGraph center ligand)
      (some (key.declarativeLabel mol node)))
  have hcoherent := key.sourceCoherent_of_root_and_childrenExact
    mol center ligand hwellFormed hroot hexact node source hsource
  rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol node source hsource]
  cases hprovenance : source.provenance with
  | phantom distance =>
      have hatomless : ((key.toDeclarativeDigraph mol).label node).atom? = none := by
        change (key.declarativeLabel mol node).atom? = none
        rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol node source hsource]
        simp [hprovenance]
      rw [exactRule1aNodeObservation_atomless mol.toMoleculeGraph
        (key.toDeclarativeDigraph mol) (key.declarativeAddressing mol) node hatomless]
      rfl
  | realAtom | ringDuplicate =>
      have hbound : source.atom < mol.atomCount := by
        simpa [hprovenance] using hcoherent.2
      let atom : Fin mol.atomCount := ⟨source.atom, hbound⟩
      have hatom : ((key.toDeclarativeDigraph mol).label node).atom? = some atom := by
        change (key.declarativeLabel mol node).atom? = some atom
        rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol node source hsource]
        simp [hprovenance, atomFin?, hbound, atom]
      have hnodeProvenance : ∀ distance,
          ((key.toDeclarativeDigraph mol).label node).provenance ≠
            NodeProvenance.multipleBondDuplicate distance := by
        intro distance
        change (key.declarativeLabel mol node).provenance ≠
          NodeProvenance.multipleBondDuplicate distance
        rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol node source hsource]
        simp [hprovenance, declarativeProvenance]
      rw [exactRule1aNodeObservation_nonmultiple mol.toMoleculeGraph
        (key.toDeclarativeDigraph mol) (key.declarativeAddressing mol) node atom
        hatom hnodeProvenance]
      simp [nodeAtomicNumber, declarativeProvenance, atomFin?, hbound, atom]
  | multipleBondDuplicate distance =>
      exact (hnotMultiple distance hprovenance).elim

/-- Pointwise production correctness for the independent exact Rule-1a carrier.

Equality is intentionally stated on rational values rather than raw numerator/denominator fields:
production and the independent maximum-matching semantics may present the same mean with different
unreduced positive fractions. -/
def Rule1aObservationCorrectAt
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (node : key.HierarchyNode) (source : CanonicalBranchNode) : Prop :=
  ∃ label, mol.canonicalRule1aLabel? source = some label ∧
    label.toExactAtomicNumber.value =
      (exactRule1aNodeObservation mol.toMoleculeGraph (key.toDeclarativeDigraph mol)
        (key.declarativeAddressing mol) node).value

/-- A correctness witness tied to the actual production source stored at this hierarchy node. -/
def RealizedRule1aObservationCorrectAt
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (node : key.HierarchyNode) (source : CanonicalBranchNode) : Prop :=
  key.sourceNodeAtAddress? node.1 = some source ∧
    key.Rule1aObservationCorrectAt mol node source

/-- Every ordinary, ring-duplicate, and phantom source node satisfies exact independent Rule 1a
without a further chemical hypothesis. -/
theorem rule1aObservationCorrectAt_of_not_multiple
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source)
    (hnotMultiple : ∀ distance,
      source.provenance ≠ CanonicalNodeProvenance.multipleBondDuplicate distance) :
    key.Rule1aObservationCorrectAt mol node source := by
  let observation := nodeAtomicNumber
    (mol.canonicalHierarchyMoleculeGraph center ligand)
    (some ((key.toDeclarativeDigraph mol).label node))
  refine ⟨{ numerator := observation, denominator := 1 }, ?_, ?_⟩
  · exact key.canonicalRule1aLabel?_eq_integral_nodeAtomicNumber_of_not_multiple
      mol center ligand hwellFormed hroot hexact node source hsource hnotMultiple
  · have hindependent :=
      key.exactRule1aNodeObservation_eq_ofNat_nodeAtomicNumber_of_not_multiple
        mol center ligand hwellFormed hroot hexact node source hsource hnotMultiple
    rw [hindependent]
    rfl

theorem realizedRule1aObservationCorrectAt_of_not_multiple
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source)
    (hnotMultiple : ∀ distance,
      source.provenance ≠ CanonicalNodeProvenance.multipleBondDuplicate distance) :
    key.RealizedRule1aObservationCorrectAt mol node source :=
  ⟨hsource, key.rule1aObservationCorrectAt_of_not_multiple mol center ligand
    hwellFormed hroot hexact node source hsource hnotMultiple⟩

/-- Structural multiple-bond bridge: a realized production duplicate has valid finite attached and
duplicated atoms, and the independent node observation is exactly the independent multiple-bond
function on that pair.  No Mancude-search correctness is assumed here; this theorem isolates it
from hierarchy conversion and parent recovery. -/
theorem exactRule1aNodeObservation_eq_exactMultipleBond_of_source
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source)
    (distance : ℕ)
    (hprovenance : source.provenance =
      CanonicalNodeProvenance.multipleBondDuplicate distance) :
    ∃ attached duplicated : Fin mol.atomCount,
      attached.1 = source.parent ∧ duplicated.1 = source.atom ∧
        exactRule1aNodeObservation mol.toMoleculeGraph (key.toDeclarativeDigraph mol)
            (key.declarativeAddressing mol) node =
          mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated := by
  have hcomplete := key.sourceComplete_of_root_and_childrenExact mol
    (RawMolecule.canonicalRoot center ligand) hroot hexact
  have hchildren := key.childrenSound_of_childrenExact mol hexact
  have hcoherent := key.sourceCoherent_of_root_and_childrenExact
    mol center ligand hwellFormed hroot hexact
  have hnotRoot : node ≠ (key.toDeclarativeDigraph mol).root := by
    intro hnode
    have haddress : node.1 = [] := congrArg Subtype.val hnode
    have hsourceRoot : source = RawMolecule.canonicalRoot center ligand := by
      apply Option.some.inj
      exact hsource.symm.trans (by simpa [haddress] using hroot)
    subst source
    simp [RawMolecule.canonicalRoot] at hprovenance
  obtain ⟨parent, hchild, _⟩ :=
    (key.declarativeAddressing mol).existsUnique_parent node hnotRoot
  change key.HierarchyChild parent node at hchild
  rcases hcomplete parent with ⟨parentSource, hparentSource⟩
  have hgenerated := hchildren parent node parentSource source hchild
    hparentSource hsource
  have hparentEq := mol.canonicalChildren_parent_eq parentSource source hgenerated
  have hparentReal := key.parentSource_real_of_hierarchyChild mol hchildren
    parent node parentSource source hchild hparentSource hsource
  have hparentCoherent := hcoherent parent parentSource hparentSource
  have hsourceCoherent := hcoherent node source hsource
  have hparentBound : parentSource.atom < mol.atomCount := by
    simpa [hparentReal] using hparentCoherent.2
  have hsourceBound : source.atom < mol.atomCount := by
    simpa [hprovenance] using hsourceCoherent.2
  let attached : Fin mol.atomCount := ⟨parentSource.atom, hparentBound⟩
  let duplicated : Fin mol.atomCount := ⟨source.atom, hsourceBound⟩
  refine ⟨attached, duplicated, ?_, rfl, ?_⟩
  · simpa [attached] using hparentEq.symm
  · have hnodeLabel : (key.toDeclarativeDigraph mol).label node =
        ⟨some duplicated, NodeProvenance.multipleBondDuplicate distance⟩ := by
      change key.declarativeLabel mol node = _
      rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol node source hsource]
      simp [hprovenance, atomFin?, hsourceBound, duplicated, declarativeProvenance]
    have hparentLabel : ((key.toDeclarativeDigraph mol).label parent).atom? =
        some attached := by
      change (key.declarativeLabel mol parent).atom? = some attached
      rw [key.declarativeLabel_eq_of_sourceNodeAtAddress mol parent parentSource hparentSource]
      simp [hparentReal, atomFin?, hparentBound, attached]
    exact exactRule1aNodeObservation_multiple_of_parent mol.toMoleculeGraph
      (key.toDeclarativeDigraph mol) (key.declarativeAddressing mol)
      parent node duplicated attached distance hchild hnodeLabel hparentLabel

/-- The remaining multiple-bond obligation has no hidden hierarchy content: once production's
Mancude/Kekule rational value is shown equal to the independent multiple-bond value on the recovered
atom pair, pointwise Rule-1a observation correctness follows. -/
theorem rule1aObservationCorrectAt_of_multiple
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source)
    (distance : ℕ)
    (hprovenance : source.provenance =
      CanonicalNodeProvenance.multipleBondDuplicate distance)
    (haverage : ∀ attached duplicated : Fin mol.atomCount,
      attached.1 = source.parent → duplicated.1 = source.atom →
      ∃ label, mol.canonicalRule1aLabel? source = some label ∧
        label.toExactAtomicNumber.value =
          (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value) :
    key.Rule1aObservationCorrectAt mol node source := by
  obtain ⟨attached, duplicated, hattached, hduplicated, hindependent⟩ :=
    key.exactRule1aNodeObservation_eq_exactMultipleBond_of_source
      mol center ligand hwellFormed hroot hexact node source hsource distance hprovenance
  obtain ⟨label, hlabel, hvalue⟩ :=
    haverage attached duplicated hattached hduplicated
  exact ⟨label, hlabel, hvalue.trans (congrArg ExactAtomicNumber.value hindependent.symm)⟩

theorem realizedRule1aObservationCorrectAt_of_multiple
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (center ligand : Fin mol.atomCount)
    (hwellFormed : mol.WellFormed)
    (hroot : key.RootedAt center ligand)
    (hexact : key.ChildrenExact mol)
    (node : key.HierarchyNode) (source : CanonicalBranchNode)
    (hsource : key.sourceNodeAtAddress? node.1 = some source)
    (distance : ℕ)
    (hprovenance : source.provenance =
      CanonicalNodeProvenance.multipleBondDuplicate distance)
    (haverage : ∀ attached duplicated : Fin mol.atomCount,
      attached.1 = source.parent → duplicated.1 = source.atom →
      ∃ label, mol.canonicalRule1aLabel? source = some label ∧
        label.toExactAtomicNumber.value =
          (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value) :
    key.RealizedRule1aObservationCorrectAt mol node source :=
  ⟨hsource, key.rule1aObservationCorrectAt_of_multiple mol center ligand
    hwellFormed hroot hexact node source hsource distance hprovenance haverage⟩

/-- Under the explicit pointwise correspondence hypotheses, checked production Rule 1a and the
independent exact-rational node outcome are logically equivalent.  The only nonautomatic instances
of those hypotheses are localized multiple-bond duplicates. -/
theorem compareCanonicalNodeRule?_rule1a_exactNodeOutcome_iff
    (mol : RawMolecule) (leftKey rightKey : CanonicalBranchKey)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (leftSource rightSource : CanonicalBranchNode)
    (hleft : leftKey.Rule1aObservationCorrectAt mol leftNode leftSource)
    (hright : rightKey.Rule1aObservationCorrectAt mol rightNode rightSource)
    (outcome : Ordering) :
    mol.compareCanonicalNodeRule? CanonicalRuleStage.rule1a leftSource rightSource =
        some outcome ↔
      ExactAtomicNumber.Outcome
        (exactRule1aNodeObservation mol.toMoleculeGraph
          (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol) leftNode)
        (exactRule1aNodeObservation mol.toMoleculeGraph
          (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol) rightNode)
        outcome := by
  rcases hleft with ⟨leftLabel, hleftLabel, hleftValue⟩
  rcases hright with ⟨rightLabel, hrightLabel, hrightValue⟩
  rw [mol.compareCanonicalNodeRule?_rule1a_exactOutcome_iff leftSource rightSource
    leftLabel rightLabel hleftLabel hrightLabel outcome]
  unfold ExactAtomicNumber.Outcome
  rw [hleftValue, hrightValue]

/-- At a shared production position, the local exact Rule-1a relational judgment is exactly the
outcome of comparing the represented nodes' independent observations. -/
theorem exactRule1aOutcomeAt_iff_nodeOutcome
    (mol : RawMolecule) (leftKey rightKey : CanonicalBranchKey)
    (position : List ℕ)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (hleftPosition : leftNode.1 = position)
    (hrightPosition : rightNode.1 = position)
    (outcome : Ordering) :
    ExactRule1aOutcomeAt mol.toMoleculeGraph
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        position outcome ↔
      ExactAtomicNumber.Outcome
        (exactRule1aNodeObservation mol.toMoleculeGraph
          (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol) leftNode)
        (exactRule1aNodeObservation mol.toMoleculeGraph
          (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol) rightNode)
        outcome := by
  let leftObservation := exactRule1aNodeObservation mol.toMoleculeGraph
    (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol) leftNode
  let rightObservation := exactRule1aNodeObservation mol.toMoleculeGraph
    (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol) rightNode
  have hleftAt : ExactRule1aObservationAt mol.toMoleculeGraph
      (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
      position leftObservation :=
    Or.inl ⟨leftNode, hleftPosition, rfl⟩
  have hrightAt : ExactRule1aObservationAt mol.toMoleculeGraph
      (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
      position rightObservation :=
    Or.inl ⟨rightNode, hrightPosition, rfl⟩
  constructor
  · rintro ⟨left, right, hleft, hright, houtcome⟩
    have hleftEq := exactRule1aObservationAt_functional mol.toMoleculeGraph
      (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
      position hleft hleftAt
    have hrightEq := exactRule1aObservationAt_functional mol.toMoleculeGraph
      (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
      position hright hrightAt
    simpa [leftObservation, rightObservation, hleftEq, hrightEq] using houtcome
  · intro houtcome
    exact ⟨leftObservation, rightObservation, hleftAt, hrightAt,
      by simpa [leftObservation, rightObservation] using houtcome⟩

/-- Strongest current honest paired-node bridge: executable and independent exact Rule 1a have the
same result at a shared position exactly when each production rational observation realizes the
independent node value. -/
theorem pairedNodeRule1aOutcome_iff_production_of_observations
    (mol : RawMolecule) (leftKey rightKey : CanonicalBranchKey)
    (position : List ℕ)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (hleftPosition : leftNode.1 = position)
    (hrightPosition : rightNode.1 = position)
    (leftSource rightSource : CanonicalBranchNode)
    (hleftCorrect : leftKey.Rule1aObservationCorrectAt mol leftNode leftSource)
    (hrightCorrect : rightKey.Rule1aObservationCorrectAt mol rightNode rightSource)
    (outcome : Ordering) :
    mol.compareCanonicalNodeRule? CanonicalRuleStage.rule1a leftSource rightSource =
        some outcome ↔
      ExactRule1aOutcomeAt mol.toMoleculeGraph
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        position outcome := by
  exact
    (compareCanonicalNodeRule?_rule1a_exactNodeOutcome_iff mol leftKey rightKey
      leftNode rightNode leftSource rightSource hleftCorrect hrightCorrect outcome).trans
      (exactRule1aOutcomeAt_iff_nodeOutcome mol leftKey rightKey position
        leftNode rightNode hleftPosition hrightPosition outcome).symm

/-- Public paired-node correspondence.  Unlike the extensional lemma above, both production
sources are required to be the sources actually realized at the compared hierarchy positions. -/
theorem pairedNodeRule1aOutcome_iff_production
    (mol : RawMolecule) (leftKey rightKey : CanonicalBranchKey)
    (position : List ℕ)
    (leftNode : leftKey.HierarchyNode) (rightNode : rightKey.HierarchyNode)
    (hleftPosition : leftNode.1 = position)
    (hrightPosition : rightNode.1 = position)
    (leftSource rightSource : CanonicalBranchNode)
    (hleft : leftKey.RealizedRule1aObservationCorrectAt mol leftNode leftSource)
    (hright : rightKey.RealizedRule1aObservationCorrectAt mol rightNode rightSource)
    (outcome : Ordering) :
    mol.compareCanonicalNodeRule? CanonicalRuleStage.rule1a leftSource rightSource =
        some outcome ↔
      ExactRule1aOutcomeAt mol.toMoleculeGraph
        (leftKey.toDeclarativeDigraph mol) (leftKey.declarativeAddressing mol)
        (rightKey.toDeclarativeDigraph mol) (rightKey.declarativeAddressing mol)
        position outcome :=
  pairedNodeRule1aOutcome_iff_production_of_observations mol leftKey rightKey position
    leftNode rightNode hleftPosition hrightPosition leftSource rightSource
    hleft.2 hright.2 outcome

end RawMolecule.CanonicalBranchKey

namespace RawMolecule

/-- Exact remaining chemical boundary for one compiled hierarchy.

It requires support and value equality only for multiple-bond duplicate sources actually realized
in `key`.  Therefore production refusal outside this successfully compiled hierarchy is not turned
into a false totality claim. -/
def CanonicalBranchKey.MancudeRule1aSoundOn
    (mol : RawMolecule) (key : CanonicalBranchKey) : Prop :=
  ∀ (node : key.HierarchyNode) (source : CanonicalBranchNode),
    key.sourceNodeAtAddress? node.1 = some source →
    ∀ distance, source.provenance =
      CanonicalNodeProvenance.multipleBondDuplicate distance →
    ∀ attached duplicated : Fin mol.atomCount,
      attached.1 = source.parent → duplicated.1 = source.atom →
      ∃ label, mol.canonicalRule1aLabel? source = some label ∧
        label.toExactAtomicNumber.value =
          (mol.toMoleculeGraph.exactRule1aMultipleBond attached duplicated).value

/-- Global chemical soundness and retained per-node label support imply the exact hierarchy-local
boundary used by the correspondence theorem. -/
theorem CanonicalBranchKey.mancudeRule1aSoundOn_of_global
    (mol : RawMolecule) (key : CanonicalBranchKey)
    (hsound : mol.MancudeRule1aSound)
    (hsupported : key.MultipleRule1aSupportedOn mol) :
    key.MancudeRule1aSoundOn mol := by
  intro node source hsource distance hprovenance attached duplicated
    hattached hduplicated
  obtain ⟨label, hlabel⟩ := hsupported node source hsource distance hprovenance
  refine ⟨label, hlabel, ?_⟩
  apply hsound attached duplicated label
  have hmancude : mol.mancudeRule1aLabel? source.parent source.atom = some label := by
    simpa [canonicalRule1aLabel?, hprovenance] using hlabel
  simpa [hattached, hduplicated] using hmancude

/-- Successful complete compilation itself supplies the per-occurrence label-support evidence;
it is no longer an external hypothesis erased by the complete-build certificate. -/
theorem branchCanonicalKey?_multipleRule1aSupportedOn
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true) :
    key.MultipleRule1aSupportedOn mol := by
  intro node source hsource distance hprovenance
  exact mol.branchCanonicalKey?_rule1aLabelSupportedAt center ligand key
    hkey hcomplete node.1 source hsource

/-- Global Mancude soundness specializes to the exact hierarchy-local boundary for every
successful complete public branch compilation. -/
theorem branchCanonicalKey?_mancudeRule1aSoundOn_of_global
    (mol : RawMolecule) (center ligand : ℕ) (key : CanonicalBranchKey)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true) (hsound : mol.MancudeRule1aSound) :
    key.MancudeRule1aSoundOn mol :=
  key.mancudeRule1aSoundOn_of_global mol hsound
    (mol.branchCanonicalKey?_multipleRule1aSupportedOn center ligand key hkey hcomplete)

/-- Complete-hierarchy Rule-1a observation correspondence, with the sole remaining chemical
boundary quantified exactly at localized multiple-bond duplicates.  All other provenance cases
are discharged by the theorem, as are source realization, parent recovery, and finite atom bounds.
-/
theorem branchCanonicalKey?_rule1aObservationCorrect
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true)
    (hmultiple : key.MancudeRule1aSoundOn mol) :
    ∀ (node : key.HierarchyNode) (source : CanonicalBranchNode),
      key.sourceNodeAtAddress? node.1 = some source →
      key.RealizedRule1aObservationCorrectAt mol node source := by
  have hbuild := mol.branchCanonicalKey?_completeBuild center ligand key hkey hcomplete
  have hroot : key.RootedAt center ligand := canonicalCompleteBuild_root_source hbuild
  have hexact : key.ChildrenExact mol := hbuild.childrenExact
  intro node source hsource
  cases hprovenance : source.provenance with
  | realAtom | ringDuplicate | phantom =>
      apply key.realizedRule1aObservationCorrectAt_of_not_multiple mol center ligand
        hwellFormed hroot hexact node source hsource
      intro distance hmultipleProvenance
      simp [hprovenance] at hmultipleProvenance
  | multipleBondDuplicate distance =>
      exact key.realizedRule1aObservationCorrectAt_of_multiple mol center ligand
        hwellFormed hroot hexact node source hsource distance hprovenance
        (hmultiple node source hsource distance hprovenance)

/-- Combined production boundary: faithful exact expansion plus exact Rule-1a observations at every
realized node, conditional only on the named Mancude/Kekule soundness boundary above. -/
theorem branchCanonicalKey?_faithfulExactExpansion_and_rule1aObservationCorrect
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true)
    (hrootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
    (hmancude : key.MancudeRule1aSoundOn mol) :
    RootedDigraph.FaithfulExactExpansion
        (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
        (key.toDeclarativeDigraph mol) ∧
      ∀ (node : key.HierarchyNode) (source : CanonicalBranchNode),
        key.sourceNodeAtAddress? node.1 = some source →
          key.RealizedRule1aObservationCorrectAt mol node source := by
  exact ⟨mol.branchCanonicalKey?_faithfulExactExpansion center ligand key
      hwellFormed hunique hkey hcomplete hrootBond,
    mol.branchCanonicalKey?_rule1aObservationCorrect center ligand key
      hwellFormed hkey hcomplete hmancude⟩

/-- Once global Mancude/Kekule label soundness is established, complete production compilation
needs no separate per-node support premise: that evidence is retained by its certified build. -/
theorem branchCanonicalKey?_faithfulExactExpansion_and_rule1aObservationCorrect_of_global
    (mol : RawMolecule) (center ligand : Fin mol.atomCount)
    (key : CanonicalBranchKey)
    (hwellFormed : mol.WellFormed)
    (hunique : mol.BondRecordsUnique)
    (hkey : branchCanonicalKey? mol center ligand = some key)
    (hcomplete : key.complete = true)
    (hrootBond : (mol.canonicalHierarchyMoleculeGraph center ligand).Adj center ligand)
    (hmancude : mol.MancudeRule1aSound) :
    RootedDigraph.FaithfulExactExpansion
        (mol.canonicalHierarchyMoleculeGraph center ligand) center ligand
        (key.toDeclarativeDigraph mol) ∧
      ∀ (node : key.HierarchyNode) (source : CanonicalBranchNode),
        key.sourceNodeAtAddress? node.1 = some source →
          key.RealizedRule1aObservationCorrectAt mol node source := by
  apply mol.branchCanonicalKey?_faithfulExactExpansion_and_rule1aObservationCorrect
    center ligand key hwellFormed hunique hkey hcomplete hrootBond
  exact mol.branchCanonicalKey?_mancudeRule1aSoundOn_of_global center ligand key
    hkey hcomplete hmancude

end RawMolecule

end
end OneCenter
end TetraStereo
