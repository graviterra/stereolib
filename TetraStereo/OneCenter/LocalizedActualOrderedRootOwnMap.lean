import TetraStereo.OneCenter.LocalizedOrderedMolecularEvidence
import TetraStereo.OneCenter.LocalizedActualArmReadback
import TetraStereo.OneCenter.LocalizedActualOrderedRootDeclarativeDescriptor
import TetraStereo.OneCenter.DeclarativeCIPFinalTetrahedralAssignment
import TetraStereo.OneCenter.AuxiliaryContextIntegrity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

/-!
# Root judgments for the ordered runtime's own descriptor map

The molecular descriptor map in this module is defined from the ordered runtime's callable
reference state (`actualOrderedReferenceDescriptorMap`).  The transfer to the accepted general
root theorem is local: only units read along the four actual physical arm graphs are compared,
and P1 supplies state agreement only at the exact strict same-root descendants that those reads
name.  No equality of the two maps or of their states away from these dependencies is assumed.
-/

namespace TetraStereo.OneCenter

open DeclarativeCIP
open CertifiedLocalizedCIPInput
open LocalizedCumulativeDecoratedTree
open MolecularEvidenceTree
open RootedDigraph
open RootedTetrahedralBranchSymmetry

noncomputable section
open scoped Classical

namespace Rule4aTableBridge
namespace ActualCentrePhysicalSetup

variable {input : LocalizedUniversalReference.Input} (S : ActualCentrePhysicalSetup input)

abbrev ownDescriptorMap (input : LocalizedUniversalReference.Input) :
    DescriptorMap (DetectedOccurrence input.certified.moleculeGraph) :=
  actualOrderedReferenceDescriptorMap input

/-- At a specified strict dependency of this root, the ordered pipeline state agrees with the
generated production reference state.  This is P1's same-root/depth result followed by the
pointwise pipeline/fixed-point equality; no final-occurrence agreement is used. -/
theorem orderedState_eq_generated_of_strictDependency
    {source : LocalizedUniversalReference.Occurrence input}
    (dependency : input.certified.LocalizedDepthDependency source S.top) :
    LocalizedOrderedReference.referenceState input source =
      LocalizedUniversalReference.referenceState input source := by
  have hfixed := orderedReferenceState_eq_referenceState_of_dependency input S.singleBonded
    S.acyclic S.hcharge S.noDouble
    (input.certified.canonicalReindexConfiguration S.cfg) S.c
    (S.slotSetup 0).globalDomain ⟨S.c.1, S.c.2⟩ rfl source dependency
  exact (orderedReferenceStateAt_eq_pipelineState input source).symm.trans hfixed

/-- Source data recovered from an actual arm node.  Its path is a nonempty simple outward path
from this root, and its carrier occurrence is therefore a strict same-root dependency of `S.top`.
The final equality records the exact molecular unit used by `contextOccurrence`. -/
theorem armNode_sourceWitness (ℓ : Fin 4) (node : (S.armG ℓ).Node) :
    ∃ actual steps,
      subtreeAt? (S.arm4a ℓ).tree node.1 = some actual ∧
      actual.source.occurrence.1.root = S.center.1 ∧
      actual.source.occurrence.1.address ≠ [] ∧
      actual.source.occurrence.1.node.provenance = .realAtom ∧
      ((S.armG ℓ).label node).provenance = .realAtom ∧
      actual.source.occurrence.1.node.history = (S.center.1 :: steps).reverse ∧
      (S.center.1 :: steps).Nodup ∧ steps ≠ [] ∧
      input.certified.molecularFrameUnit actual.source.occurrence.1 = ⟨S.center.1, steps⟩ ∧
      ancestorAtoms (S.armG ℓ) node = some steps := by
  let arm := S.arm4a ℓ
  have realizes := arm.realizes
  have generated := arm.generated
  have treeRoot := arm.root
  have hsource := arm.source
  have incoming : LocalizedCumulativeTreeIncoming input.certified arm.tree :=
    input.certified.localizedCumulativeTreeIncoming_of_realizes _ arm.tree realizes
      (by rw [hsource]; exact input.certified.localizedLigandRootCursor_incoming S.center ℓ)
  obtain ⟨erased, herased⟩ :=
    OfficialCIPSourceTree.exists_subtreeAt?_eq_some_of_mem_hierarchyAddresses
      (toOfficialSourceTree arm.tree) node.1 node.2
  rw [toOfficialSourceTree_subtreeAt?_eq, Option.map_eq_some_iff] at herased
  obtain ⟨actual, hactual, rfl⟩ := herased
  have hlookup : (toOfficialSourceTree arm.tree).subtreeAt? node.1 =
      some (toOfficialSourceTree actual) := by
    rw [toOfficialSourceTree_subtreeAt?_eq, hactual]
    rfl
  have hrealCursor : actual.source.occurrence.1.node.provenance = .realAtom :=
    input.certified.carrierOccurrence_provenance_real S.singleBonded S.acyclic
      actual.source.occurrence
  have hrealSource : (toOfficialSourceTree actual).source.provenance = .realAtom := by
    rw [toOfficialSourceTree_source]
    exact hrealCursor
  have hlabel := OfficialCIPSourceTree.declarativeLabel_eq_of_subtreeAt?
    (toOfficialSourceTree arm.tree) _ node hlookup
  have hrealGraph : ((S.armG ℓ).label node).provenance = .realAtom := by
    change ((toOfficialSourceTree arm.tree).toDeclarativeDigraph.label node).provenance = .realAtom
    have hprovenance :
        ((toOfficialSourceTree arm.tree).toDeclarativeDigraph.label node).provenance =
          (toOfficialSourceTree actual).source.provenance.toDeclarative := by
      change ((toOfficialSourceTree arm.tree).declarativeLabel node).provenance = _
      rw [hlabel]
      rfl
    rw [hprovenance, hrealSource]
    rfl
  have rootCurrent : (toOfficialSourceTree arm.tree).source.current? =
      some (input.certified.canonicalLigandAtom S.center ℓ) := by rw [treeRoot]; rfl
  obtain ⟨rest, hpath, hhistory⟩ :=
    generated_history input.certified.executableOfficialCIPChildren
      (executableOfficialCIPChildren_extend input.certified) node.1
      (toOfficialSourceTree arm.tree) _ (input.certified.canonicalLigandAtom S.center ℓ)
      generated rootCurrent hlookup
  have hligand : input.certified.canonicalLigandAtom S.center ℓ ≠ S.center.1 := by
    intro h
    have hadj := input.certified.canonicalLigandAtom_adj S.center ℓ
    rw [show input.certified.canonicalLigandAtom S.center ℓ = S.center.1 from h] at hadj
    simp [MoleculeGraph.Adj, input.certified.moleculeGraph.bond_self] at hadj
  have rootNodup : (toOfficialSourceTree arm.tree).source.history.Nodup := by
    rw [treeRoot]
    simp [OfficialCIPNode.rootFromEdge, hligand]
  have hnodup := generated_nodup input.certified.executableOfficialCIPChildren
    (executableOfficialCIPChildren_extend input.certified)
    (executableOfficialCIPChildren_terminal input.certified) node.1
    (toOfficialSourceTree arm.tree) _ generated rootNodup hlookup
    (by rw [toOfficialSourceTree_source]; exact hrealCursor)
  have rootHistory : (toOfficialSourceTree arm.tree).source.history =
      [input.certified.canonicalLigandAtom S.center ℓ, S.center.1] := by rw [treeRoot]; rfl
  have hcursorHistory : actual.source.occurrence.1.node.history =
      (S.center.1 :: input.certified.canonicalLigandAtom S.center ℓ :: rest).reverse := by
    rw [← toOfficialSourceTree_source, hhistory, rootHistory]
    simp
  let steps : List input.certified.Atom := input.certified.canonicalLigandAtom S.center ℓ :: rest
  have hsimple' :
      (S.center.1 :: input.certified.canonicalLigandAtom S.center ℓ :: rest).Nodup := by
    rw [← List.nodup_reverse, ← hcursorHistory, ← toOfficialSourceTree_source]
    exact hnodup
  have hsimple : (S.center.1 :: steps).Nodup := by simpa [steps] using hsimple'
  have hroot : actual.source.occurrence.1.root = S.center.1 := by
    rw [subtreeAt?_source_occurrence_root_eq realizes hactual, hsource]
    rfl
  have haddress : actual.source.occurrence.1.address ≠ [] :=
    address_ne_nil_of_incoming (incoming_of_subtreeAt? node.1 arm.tree actual incoming hactual)
  have hsteps : ancestorAtoms (S.armG ℓ) node = some steps := by
    rw [ancestorAtoms, ancestorPath_toDeclarativeDigraph, hpath]
    simpa [steps] using mapM_id_map_some
      (input.certified.canonicalLigandAtom S.center ℓ :: rest)
  have hhistory' : actual.source.occurrence.1.node.history = (S.center.1 :: steps).reverse := by
    simpa [steps] using hcursorHistory
  have hframe : input.certified.molecularFrameUnit actual.source.occurrence.1 =
      ⟨S.center.1, steps⟩ := by
    simp [CertifiedLocalizedCIPInput.molecularFrameUnit, hroot, hhistory', steps]
  have hne : steps ≠ [] := by simp [steps]
  exact ⟨actual, steps, hactual, hroot, haddress, hrealCursor, hrealGraph, hhistory',
    hsimple, hne, hframe, hsteps⟩

/-- The generated and ordered maps agree at a detected unit read by an arm node.  Agreement is
proved at the actual source occurrence, which is a strict dependency; there is no global map
equality hypothesis. -/
theorem ownMap_eq_generated_at_strictSource
    (unit : DetectedOccurrence input.certified.moleculeGraph)
    (actual : LocalizedOrderedReference.Occurrence input)
    (sourceEq : input.certified.molecularFrameUnit actual.1 = unit.1)
    (rootEq : actual.1.root = S.center.1) (addressNe : actual.1.address ≠ []) :
    ownDescriptorMap input unit = actualReferenceDescriptorMap input unit := by
  have hdep : input.certified.LocalizedDepthDependency actual S.top := by
    refine ⟨(rootEq.trans S.hcenter).trans
      (ActualReaderPhysicalBranchInverse.topTarget_root input S.c).symm, ?_⟩
    rw [ActualReaderPhysicalBranchInverse.topTarget_address]
    exact List.length_pos_of_ne_nil addressNe
  exact actualOrderedReferenceDescriptorMap_eq_actualReferenceDescriptorMap_of_stateEq
    input S.singleBonded S.acyclic unit actual sourceEq
    (S.orderedState_eq_generated_of_strictDependency hdep)

/-- The exact node observation is invariant under replacing the generated map by the ordered
runtime's own map, for each physical root arm. -/
theorem occurrenceReading_eq_of_armNode (ℓ : Fin 4) (node : (S.armG ℓ).Node) :
    occurrenceReading input.certified.moleculeGraph (ownDescriptorMap input) S.declUnit
        (S.armG ℓ) node =
      occurrenceReading input.certified.moleculeGraph (actualReferenceDescriptorMap input)
        S.declUnit (S.armG ℓ) node := by
  obtain ⟨actual, steps, hactual, hroot, haddress, hrealCursor, hreal, hhistory, hsimple, hne,
    hunit, hsteps⟩ := S.armNode_sourceWitness ℓ node
  have hcontext :
      contextOccurrence input.certified.moleculeGraph S.declUnit steps =
        if hdet : IsDetectedCenter input.certified.moleculeGraph
            (OccurrenceUnit.atom ⟨S.center.1, steps⟩)
        then some ⟨⟨S.center.1, steps⟩, hdet⟩ else none := by
    have hpath : S.declUnit.1.path = [] := rfl
    have hrootUnit : S.declUnit.1.root = S.center.1 := rfl
    have hwalk : rerootWalk S.center.1 [] steps = steps := by
      simpa using rerootWalk_eq_append S.center.1 steps [] (by simpa using hsimple)
    have hlen : S.declUnit.1.path.length < steps.length := by
      rw [hpath]
      exact List.length_pos_of_ne_nil hne
    have hlen' : 0 < steps.length := by simpa [hpath] using hlen
    by_cases hdet : IsDetectedCenter input.certified.moleculeGraph
        (OccurrenceUnit.atom ⟨S.center.1, steps⟩)
    · simp [contextOccurrence, hpath, hrootUnit, hwalk, hlen', hdet]
    · simp [contextOccurrence, hpath, hrootUnit, hwalk, hlen', hdet]
  rw [occurrenceReading_eq_readContext input.certified.moleculeGraph
      (ownDescriptorMap input) S.declUnit (S.armG ℓ) hreal hsteps,
    occurrenceReading_eq_readContext input.certified.moleculeGraph
      (actualReferenceDescriptorMap input) S.declUnit (S.armG ℓ) hreal hsteps]
  by_cases detected : IsDetectedCenter input.certified.moleculeGraph
      (OccurrenceUnit.atom ⟨S.center.1, steps⟩)
  · let unit : DetectedOccurrence input.certified.moleculeGraph := ⟨⟨S.center.1, steps⟩, detected⟩
    have hcontext' : contextOccurrence input.certified.moleculeGraph S.declUnit steps =
        some unit := by
      rw [hcontext]
      simp [detected, unit]
    have sourceEq : input.certified.molecularFrameUnit actual.source.occurrence.1 = unit.1 := by
      simpa [unit] using hunit
    have hmap := S.ownMap_eq_generated_at_strictSource unit actual.source.occurrence
      sourceEq hroot haddress
    simp only [readContext, hcontext']
    rw [hmap]
  · have hcontext' : contextOccurrence input.certified.moleculeGraph S.declUnit steps = none := by
      rw [hcontext]
      simp [detected]
    simp only [readContext, hcontext']

end ActualCentrePhysicalSetup
end Rule4aTableBridge

/-! ## Declarative judgments depend only on the graph's occurrence readings -/

namespace DeclarativeCIP

open Certificate.CanonicalSphereKey (Key)

variable {Atom : Type} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (unit : DetectedOccurrence molecule)
  (firstMap secondMap : DescriptorMap (DetectedOccurrence molecule))
  {left right : RootedDigraph Atom}

local instance congrNodeFintype (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

/-- The complete multireference judgment for a pair of graphs is unchanged when their node
readings agree pointwise.  This packages the induced equality of ranking evidence, reference
selection, complete readings, molecular evidence and the Rules 3--5 streams. -/
theorem multiReferenceJudgment_congr_of_occurrenceReading_eq
    (hleft : ∀ node, occurrenceReading molecule firstMap unit left node =
      occurrenceReading molecule secondMap unit left node)
    (hright : ∀ node, occurrenceReading molecule firstMap unit right node =
      occurrenceReading molecule secondMap unit right node)
    (rule : SequenceRule) (outcome : Ordering) :
    MultiReferenceJudgment molecule firstMap unit rule left right outcome ↔
      MultiReferenceJudgment molecule secondMap unit rule left right outcome := by
  have hrankEvidence (graph : RootedDigraph Atom) (hread : ∀ node,
      occurrenceReading molecule firstMap unit graph node =
        occurrenceReading molecule secondMap unit graph node) :
      rankEvidence molecule firstMap unit graph = rankEvidence molecule secondMap unit graph := by
    funext node
    simp [rankEvidence, rule3Observation, rule4aObservation, hread node]
  have hmolecularEvidence (graph : RootedDigraph Atom) (hread : ∀ node,
      occurrenceReading molecule firstMap unit graph node =
        occurrenceReading molecule secondMap unit graph node) :
      molecularEvidence molecule firstMap unit graph = molecularEvidence molecule secondMap unit graph := by
    have hsense : ∀ node, eligibleSense molecule firstMap unit graph node =
        eligibleSense molecule secondMap unit graph node := by
      intro node
      simp [eligibleSense, hread node]
    have hEligible (node : graph.Node) :
        Eligible molecule firstMap unit graph node ↔ Eligible molecule secondMap unit graph node := by
      simp [Eligible, hsense node]
    have hNearest (node : graph.Node) :
        NearestEligible molecule firstMap unit graph node ↔
          NearestEligible molecule secondMap unit graph node := by
      simp [NearestEligible, hEligible]
    have hpopulation : referencePopulation molecule firstMap unit graph =
        referencePopulation molecule secondMap unit graph := by
      by_cases hE : ∃ node, Eligible molecule firstMap unit graph node
      · have hE' : ∃ node, Eligible molecule secondMap unit graph node := by
          rcases hE with ⟨node, hnode⟩
          exact ⟨node, (hEligible node).mp hnode⟩
        by_cases hU : ∃! node, NearestEligible molecule firstMap unit graph node
        · rcases hU with ⟨nearest, hnearest, hunique⟩
          have hnearest' : NearestEligible molecule secondMap unit graph nearest :=
            (hNearest nearest).mp hnearest
          have hunique' : ∀ other, NearestEligible molecule secondMap unit graph other →
              other = nearest := by
            intro other hother
            exact hunique other ((hNearest other).mpr hother)
          rw [referencePopulation_eq_unique molecule firstMap unit graph hnearest hunique,
            referencePopulation_eq_unique molecule secondMap unit graph hnearest' hunique']
          congr 1
          exact option_get_congr (hsense nearest) hnearest.1 hnearest'.1
        · have hU' : ¬ ∃! node, NearestEligible molecule secondMap unit graph node := by
            intro h
            rcases h with ⟨nearest, hnearest, hunique⟩
            apply hU
            refine ⟨nearest, (hNearest nearest).mpr hnearest, ?_⟩
            intro other hother
            exact hunique other ((hNearest other).mp hother)
          simp [referencePopulation, hE, hE', hU, hU']
      · have hE' : ¬ ∃ node, Eligible molecule secondMap unit graph node := by
          rintro ⟨node, hnode⟩
          exact hE ⟨node, (hEligible node).mpr hnode⟩
        simp [referencePopulation, hE, hE']
    funext node
    simp [molecularEvidence, rule3Observation, rule4aObservation, rule4bObservation,
      rule4cObservation, rule5Observation, hread node, hsense node, hpopulation]
  have hreadingEvidence (graph : RootedDigraph Atom) (hread : ∀ node,
      occurrenceReading molecule firstMap unit graph node =
        occurrenceReading molecule secondMap unit graph node) (sense : DescriptorSense) :
      readingEvidence molecule firstMap unit graph sense =
        readingEvidence molecule secondMap unit graph sense := by
    funext node
    simp [readingEvidence, rule3Observation, rule4aObservation, eligibleSense, hread node]
  have hselection (graph : RootedDigraph Atom) (hread : ∀ node,
      occurrenceReading molecule firstMap unit graph node =
        occurrenceReading molecule secondMap unit graph node) :
      referenceSelection molecule firstMap unit graph =
        referenceSelection molecule secondMap unit graph := by
    have hrank := hrankEvidence graph hread
    have hrankKey : rankKey molecule firstMap unit graph =
        rankKey molecule secondMap unit graph := by
      funext node
      unfold rankKey
      rw [hrank]
    have hrankPath : rankPath molecule firstMap unit graph =
        rankPath molecule secondMap unit graph := by
      funext node
      unfold rankPath
      simp [hrankKey]
    have hEligible (node : graph.Node) :
        Eligible molecule firstMap unit graph node ↔ Eligible molecule secondMap unit graph node := by
      simp [Eligible, eligibleSense, hread node]
    have hNearest (node : graph.Node) :
        NearestEligible molecule firstMap unit graph node ↔
          NearestEligible molecule secondMap unit graph node := by
      simp [NearestEligible, hEligible]
    have hclass : referenceClass molecule firstMap unit graph =
        referenceClass molecule secondMap unit graph := by
      apply Finset.ext
      intro node
      simp only [referenceClass, Finset.mem_filter, Finset.mem_univ, true_and]
      simp [InReferenceClass, hNearest, hrankPath]
    have hsenior : seniorCount molecule firstMap unit graph =
        seniorCount molecule secondMap unit graph := by
      unfold seniorCount
      rw [hclass]
      congr 1
      apply Finset.ext
      intro node
      simp [eligibleSense, hread node]
    have hjunior : juniorCount molecule firstMap unit graph =
        juniorCount molecule secondMap unit graph := by
      unfold juniorCount
      rw [hclass]
      congr 1
      apply Finset.ext
      intro node
      simp [eligibleSense, hread node]
    unfold referenceSelection
    by_cases hE : ∃ node, Eligible molecule firstMap unit graph node
    · have hE' : ∃ node, Eligible molecule secondMap unit graph node := by
        rcases hE with ⟨node, hnode⟩
        exact ⟨node, (hEligible node).mp hnode⟩
      simp [hE, hE', hsenior, hjunior]
    · have hE' : ¬ ∃ node, Eligible molecule secondMap unit graph node := by
        rintro ⟨node, hnode⟩
        exact hE ⟨node, (hEligible node).mpr hnode⟩
      simp [hE, hE']
  have hreadingAt (graph : RootedDigraph Atom)
      (hread : ∀ node, occurrenceReading molecule firstMap unit graph node =
        occurrenceReading molecule secondMap unit graph node)
      (W D : ℕ) (sense : DescriptorSense) :
      readingAt molecule firstMap unit graph W D sense =
        readingAt molecule secondMap unit graph W D sense := by
    unfold readingAt
    rw [hreadingEvidence graph hread sense]
  have hsignature (graph : RootedDigraph Atom)
      (hread : ∀ node, occurrenceReading molecule firstMap unit graph node =
        occurrenceReading molecule secondMap unit graph node)
      (W D : ℕ) :
      ligandSignatureAt molecule firstMap unit graph W D =
        ligandSignatureAt molecule secondMap unit graph W D := by
    unfold ligandSignatureAt
    rw [hselection graph hread]
    cases hs : referenceSelection molecule secondMap unit graph <;>
      simp [hreadingAt graph hread W D]
  have hrule3 (graph : RootedDigraph Atom) (hread : ∀ node,
      occurrenceReading molecule firstMap unit graph node =
        occurrenceReading molecule secondMap unit graph node) (W D : ℕ) :
      ligandRule3Key molecule firstMap unit graph W D =
        ligandRule3Key molecule secondMap unit graph W D := by
    unfold ligandRule3Key
    rw [hrankEvidence graph hread]
  have hrule4a (graph : RootedDigraph Atom) (hread : ∀ node,
      occurrenceReading molecule firstMap unit graph node =
        occurrenceReading molecule secondMap unit graph node) (W D : ℕ) :
      ligandRule4aKey molecule firstMap unit graph W D =
        ligandRule4aKey molecule secondMap unit graph W D := by
    unfold ligandRule4aKey rule4aComponent
    rw [hrankEvidence graph hread]
  have hrule4c (graph : RootedDigraph Atom) (hread : ∀ node,
      occurrenceReading molecule firstMap unit graph node =
        occurrenceReading molecule secondMap unit graph node) (W D : ℕ) :
      ligandRule4cKey molecule firstMap unit graph W D =
        ligandRule4cKey molecule secondMap unit graph W D := by
    unfold ligandRule4cKey
    rw [hmolecularEvidence graph hread]
  have hrule5 (graph : RootedDigraph Atom) (hread : ∀ node,
      occurrenceReading molecule firstMap unit graph node =
        occurrenceReading molecule secondMap unit graph node) :
      ligandRule5Stream molecule firstMap unit graph =
        ligandRule5Stream molecule secondMap unit graph := by
    funext path
    unfold ligandRule5Stream
    have hreadings : readingAt molecule firstMap unit graph graph.width graph.height =
        readingAt molecule secondMap unit graph graph.width graph.height :=
      funext (hreadingAt graph hread graph.width graph.height)
    rw [hselection graph hread, hreadings]
  cases rule with
  | rule1aAtomicNumber => rfl
  | rule1bDuplicateNodeProximity => rfl
  | rule2AtomicMass => rfl
  | rule3DoubleBondGeometry =>
      change compare _ _ = outcome ↔ compare _ _ = outcome
      rw [hrule3 left hleft (pairWidth left right) (pairHeight left right),
        hrule3 right hright (pairWidth left right) (pairHeight left right)]
  | rule4aStereogenicUnitKind =>
      change compare _ _ = outcome ↔ compare _ _ = outcome
      rw [hrule4a left hleft (pairWidth left right) (pairHeight left right),
        hrule4a right hright (pairWidth left right) (pairHeight left right)]
  | rule4bLikeUnlikeDescriptorPairs =>
      change signatureCompare _ _ = outcome ↔ signatureCompare _ _ = outcome
      rw [hsignature left hleft (pairWidth left right) (pairHeight left right),
        hsignature right hright (pairWidth left right) (pairHeight left right)]
  | rule4cPseudoasymmetricDescriptor =>
      change compare _ _ = outcome ↔ compare _ _ = outcome
      rw [hrule4c left hleft (pairWidth left right) (pairHeight left right),
        hrule4c right hright (pairWidth left right) (pairHeight left right)]
  | rule5EnantiomorphicDescriptor =>
      change FirstDifferenceOutcome _ outcome ↔ FirstDifferenceOutcome _ outcome
      rw [hrule5 left hleft, hrule5 right hright]
  | rule6ReferencePromotion => rfl

end DeclarativeCIP

namespace Rule4aTableBridge
namespace ActualCentrePhysicalSetup

variable {input : LocalizedUniversalReference.Input} (S : ActualCentrePhysicalSetup input)

/-- The two descriptor maps give the same complete declarative judgment on a pair of physical
root arms.  This is obtained from their exact node-reading agreement, rather than a global map
equality. -/
theorem armPairJudgment_iff_generated (ℓ m : Fin 4) (rule : SequenceRule)
    (outcome : Ordering) :
    MultiReferenceJudgment input.certified.moleculeGraph
        (ownDescriptorMap input) S.declUnit rule (S.armG ℓ) (S.armG m) outcome ↔
      MultiReferenceJudgment input.certified.moleculeGraph
        (actualReferenceDescriptorMap input) S.declUnit rule (S.armG ℓ) (S.armG m) outcome := by
  exact (DeclarativeCIP.multiReferenceJudgment_congr_of_occurrenceReading_eq
    input.certified.moleculeGraph S.declUnit (ownDescriptorMap input)
      (actualReferenceDescriptorMap input)
      (S.occurrenceReading_eq_of_armNode ℓ) (S.occurrenceReading_eq_of_armNode m)
      rule outcome)

/-- The universal RuleOutcome agrees for any rule at or after Rule 3.  The existing
`ruleOutcome_iff_judgment` theorem reduces universal faithful-expansion quantification to the
actual physical arms, where strict-occurrence readback gives map agreement. -/
theorem ruleOutcome_map_iff_of_rank (ℓ m : Fin 4) (rule : SequenceRule)
    (hnot6 : rule ≠ .rule6ReferencePromotion) (hrank : 3 ≤ rule.rank)
    (outcome : Ordering) :
    (geoProblem (input := input)).RuleOutcome (actualReferenceDescriptorMap input) rule
        S.declUnit ℓ m outcome ↔
      (geoProblem (input := input)).RuleOutcome (ownDescriptorMap input) rule
        S.declUnit ℓ m outcome := by
  constructor
  · intro oldOutcome
    have oldArm := (DeclarativeCIP.ruleOutcome_iff_judgment
      input.certified.moleculeGraph input.certified.localizedDetectedFrame
      input.certified.geometricOrientation (actualReferenceDescriptorMap input) rule hrank hnot6
      S.declUnit (i := ℓ) (j := m) (leftGraph := S.armG ℓ) (rightGraph := S.armG m)
      (S.admissible_arm input.certified.geometricOrientation ℓ)
      (S.admissible_arm input.certified.geometricOrientation m) outcome).1 oldOutcome
    have ownArm := (S.armPairJudgment_iff_generated ℓ m rule outcome).mpr oldArm
    exact (DeclarativeCIP.ruleOutcome_iff_judgment
      input.certified.moleculeGraph input.certified.localizedDetectedFrame
      input.certified.geometricOrientation (ownDescriptorMap input) rule hrank hnot6
      S.declUnit (i := ℓ) (j := m) (leftGraph := S.armG ℓ) (rightGraph := S.armG m)
      (S.admissible_arm input.certified.geometricOrientation ℓ)
      (S.admissible_arm input.certified.geometricOrientation m) outcome).2 ownArm
  · intro ownOutcome
    have ownArm := (DeclarativeCIP.ruleOutcome_iff_judgment
      input.certified.moleculeGraph input.certified.localizedDetectedFrame
      input.certified.geometricOrientation (ownDescriptorMap input) rule hrank hnot6
      S.declUnit (i := ℓ) (j := m) (leftGraph := S.armG ℓ) (rightGraph := S.armG m)
      (S.admissible_arm input.certified.geometricOrientation ℓ)
      (S.admissible_arm input.certified.geometricOrientation m) outcome).1 ownOutcome
    have oldArm := (S.armPairJudgment_iff_generated ℓ m rule outcome).mp ownArm
    exact (DeclarativeCIP.ruleOutcome_iff_judgment
      input.certified.moleculeGraph input.certified.localizedDetectedFrame
      input.certified.geometricOrientation (actualReferenceDescriptorMap input) rule hrank hnot6
      S.declUnit (i := ℓ) (j := m) (leftGraph := S.armG ℓ) (rightGraph := S.armG m)
      (S.admissible_arm input.certified.geometricOrientation ℓ)
      (S.admissible_arm input.certified.geometricOrientation m) outcome).2 oldArm

/-- Every Rule 1a--5 outcome is invariant under replacing the generated production map with the
ordered runtime's own map.  Rules 1a, 1b and 2 ignore the descriptor map; Rules 3--5 use the
universal-to-actual reduction above. -/
theorem ruleOutcome_map_iff (ℓ m : Fin 4) (rule : SequenceRule)
    (hnot6 : rule ≠ .rule6ReferencePromotion) (outcome : Ordering) :
    (geoProblem (input := input)).RuleOutcome (actualReferenceDescriptorMap input) rule
        S.declUnit ℓ m outcome ↔
      (geoProblem (input := input)).RuleOutcome (ownDescriptorMap input) rule
        S.declUnit ℓ m outcome := by
  cases rule with
  | rule1aAtomicNumber => rfl
  | rule1bDuplicateNodeProximity => rfl
  | rule2AtomicMass => rfl
  | rule3DoubleBondGeometry =>
      exact S.ruleOutcome_map_iff_of_rank ℓ m .rule3DoubleBondGeometry hnot6 (by decide) outcome
  | rule4aStereogenicUnitKind =>
      exact S.ruleOutcome_map_iff_of_rank ℓ m .rule4aStereogenicUnitKind hnot6 (by decide) outcome
  | rule4bLikeUnlikeDescriptorPairs =>
      exact S.ruleOutcome_map_iff_of_rank ℓ m .rule4bLikeUnlikeDescriptorPairs hnot6 (by decide) outcome
  | rule4cPseudoasymmetricDescriptor =>
      exact S.ruleOutcome_map_iff_of_rank ℓ m .rule4cPseudoasymmetricDescriptor hnot6 (by decide) outcome
  | rule5EnantiomorphicDescriptor =>
      exact S.ruleOutcome_map_iff_of_rank ℓ m .rule5EnantiomorphicDescriptor hnot6 (by decide) outcome
  | rule6ReferencePromotion => exact False.elim (hnot6 rfl)

/-- Rule 6 remains absent for the ordered map, as specified by the multireference problem. -/
theorem rule6_never_ownMap (ℓ m : Fin 4) (outcome : Ordering) :
    ¬ (geoProblem (input := input)).RuleOutcome (ownDescriptorMap input)
      .rule6ReferencePromotion S.declUnit ℓ m outcome := by
  intro h
  have hgraph := h (S.armG ℓ) (S.armG m)
    (S.admissible_arm input.certified.geometricOrientation ℓ)
    (S.admissible_arm input.certified.geometricOrientation m)
  simp [Problem.OutcomeOnGraphs, multiReferenceProblem] at hgraph

/-- Strict priority agrees between the ordered map and the accepted general production-map
eight-rule theorem. -/
theorem higher_map_iff_generated (ℓ m : Fin 4) :
    (geoProblem (input := input)).Higher (ownDescriptorMap input) S.declUnit ℓ m ↔
      (geoProblem (input := input)).Higher (actualReferenceDescriptorMap input)
        S.declUnit ℓ m := by
  unfold Problem.Higher
  constructor
  · rintro ⟨rule, hprefix, hdecisive⟩
    by_cases h6 : rule = .rule6ReferencePromotion
    · subst rule
      exact False.elim ((S.rule6_never_ownMap ℓ m .gt) hdecisive)
    · refine ⟨rule, ?_, ?_⟩
      · intro earlier hearlier
        exact (S.ruleOutcome_map_iff ℓ m earlier
          (EightRuleAssembly.ne_rule6_of_before h6 hearlier) .eq).2
          (hprefix earlier hearlier)
      · exact (S.ruleOutcome_map_iff ℓ m rule h6 .gt).2 hdecisive
  · rintro ⟨rule, hprefix, hdecisive⟩
    by_cases h6 : rule = .rule6ReferencePromotion
    · subst rule
      exact False.elim ((S.rule6_never_ownMap ℓ m .gt) hdecisive)
    · refine ⟨rule, ?_, ?_⟩
      · intro earlier hearlier
        exact (S.ruleOutcome_map_iff ℓ m earlier
          (EightRuleAssembly.ne_rule6_of_before h6 hearlier) .eq).1
          (hprefix earlier hearlier)
      · exact (S.ruleOutcome_map_iff ℓ m rule h6 .gt).1 hdecisive

/-- Rule-5's earlier-tie predicate also transfers exactly. -/
theorem earlierRulesTie5_map_iff_generated (ℓ m : Fin 4) :
    (geoProblem (input := input)).EarlierRulesTie (actualReferenceDescriptorMap input)
        .rule5EnantiomorphicDescriptor S.declUnit ℓ m ↔
      (geoProblem (input := input)).EarlierRulesTie (ownDescriptorMap input)
        .rule5EnantiomorphicDescriptor S.declUnit ℓ m := by
  unfold Problem.EarlierRulesTie
  constructor
  · intro hold earlier hearlier
    exact (S.ruleOutcome_map_iff ℓ m earlier
      (EightRuleAssembly.ne_rule6_of_before (by decide) hearlier) .eq).1
      (hold earlier hearlier)
  · intro hold earlier hearlier
    exact (S.ruleOutcome_map_iff ℓ m earlier
      (EightRuleAssembly.ne_rule6_of_before (by decide) hearlier) .eq).2
      (hold earlier hearlier)

/-- The complete ranking relation is invariant under the local map transfer. -/
theorem ranks_map_iff_generated {ranking : Equiv.Perm (Fin 4)} :
    (geoProblem (input := input)).Ranks (actualReferenceDescriptorMap input)
        S.declUnit ranking ↔
      (geoProblem (input := input)).Ranks (ownDescriptorMap input) S.declUnit ranking := by
  unfold Problem.Ranks
  constructor
  · intro oldRanks i j hij
    exact (S.higher_map_iff_generated (ranking i) (ranking j)).mpr (oldRanks i j hij)
  · intro ownRanks i j hij
    exact (S.higher_map_iff_generated (ranking i) (ranking j)).mp (ownRanks i j hij)

/-- The geometric descriptor judgment and its uniqueness transfer to the ordered map. -/
theorem descriptorJudgment_map_iff_generated (descriptor : Descriptor) :
    (geoProblem (input := input)).DescriptorJudgment (actualReferenceDescriptorMap input)
        S.declUnit descriptor ↔
      (geoProblem (input := input)).DescriptorJudgment (ownDescriptorMap input)
        S.declUnit descriptor := by
  unfold Problem.DescriptorJudgment
  constructor
  · rintro ⟨ranking, hranks, horient⟩
    exact ⟨ranking, (S.ranks_map_iff_generated).mp hranks, horient⟩
  · rintro ⟨ranking, hranks, horient⟩
    exact ⟨ranking, (S.ranks_map_iff_generated).mpr hranks, horient⟩

/-- The ordered map's independent Rule-5 count equals the physical root theorem's declarative
count because every earlier RuleOutcome agrees pair by pair. -/
theorem finalRule5PairCount_eq_declarative :
    DeclarativeCIP.finalRule5PairCount (geoProblem (input := input))
        (ownDescriptorMap input) S.declUnit = S.declarativeRule5PairCount := by
  unfold DeclarativeCIP.finalRule5PairCount declarativeRule5PairCount
  apply sourceEnantiomorphicPairCount_congr_of_forall
  intro i j
  constructor
  · rintro ⟨hne, htie⟩
    exact ⟨hne, (S.earlierRulesTie5_map_iff_generated i j).2 htie⟩
  · rintro ⟨hne, htie⟩
    exact ⟨hne, (S.earlierRulesTie5_map_iff_generated i j).1 htie⟩

/-- The ordered runtime's own pipeline state at the root is the independent final assignment
licensed by the same geometric judgment, with the final Rule-5 case count recomputed under that
own map.  Existence and uniqueness of the descriptor judgment come from the general root theorem;
the map transfer above changes only the actual strict descendants read on the four physical arms. -/
theorem orderedReferenceState_top_descriptorJudgment_ownMap
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ ProperTransport input.certified.detectedMultiCenterMolecule S.cfg S.c i j)
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨S.c.1, S.c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃ rs : RS,
      LocalizedOrderedReference.referenceState input S.top =
        some (classifyTetrahedralRSPseudo rs
          (DeclarativeCIP.finalRule5PairCount (geoProblem (input := input))
            (ownDescriptorMap input) S.declUnit)) ∧
        (geoProblem (input := input)).DescriptorJudgment (ownDescriptorMap input)
          S.declUnit (rsDescriptor rs) ∧
        ∀ descriptor, (geoProblem (input := input)).DescriptorJudgment
          (ownDescriptorMap input) S.declUnit descriptor → descriptor = rsDescriptor rs := by
  obtain ⟨rs, hstate, hjudgment, hunique⟩ :=
    S.orderedReferenceState_top_descriptorJudgment distinct coordinates
  have hpipeline : LocalizedOrderedReference.referenceState input S.top =
      some (classifyTetrahedralRSPseudo rs S.declarativeRule5PairCount) :=
    (orderedReferenceStateAt_eq_pipelineState input S.top).symm.trans hstate
  have hjudgmentOwn := (S.descriptorJudgment_map_iff_generated (rsDescriptor rs)).1 hjudgment
  have huniqueOwn : ∀ descriptor,
      (geoProblem (input := input)).DescriptorJudgment (ownDescriptorMap input)
        S.declUnit descriptor → descriptor = rsDescriptor rs := by
    intro descriptor hdescriptor
    exact hunique descriptor
      ((S.descriptorJudgment_map_iff_generated descriptor).2 hdescriptor)
  rw [← S.finalRule5PairCount_eq_declarative] at hpipeline
  exact ⟨rs, hpipeline, hjudgmentOwn, huniqueOwn⟩

/-- At the root, the actual ordered pipeline label inhabits the independent complete assignment
relation under the ordered runtime's own descriptor map. -/
theorem orderedReferenceState_top_satisfies_ownFinalAssignment
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ ProperTransport input.certified.detectedMultiCenterMolecule S.cfg S.c i j)
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨S.c.1, S.c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃ rs : RS,
      LocalizedOrderedReference.referenceState input S.top =
        some (classifyTetrahedralRSPseudo rs
          (DeclarativeCIP.finalRule5PairCount (geoProblem (input := input))
            (ownDescriptorMap input) S.declUnit)) ∧
      DeclarativeCIP.FinalTetrahedralAssignment (geoProblem (input := input))
        (ownDescriptorMap input) S.declUnit
        (classifyTetrahedralRSPseudo rs
          (DeclarativeCIP.finalRule5PairCount (geoProblem (input := input))
            (ownDescriptorMap input) S.declUnit)) := by
  obtain ⟨rs, hstate, hjudgment, _⟩ :=
    S.orderedReferenceState_top_descriptorJudgment_ownMap distinct coordinates
  exact ⟨rs, hstate, ⟨rs, hjudgment, rfl⟩⟩

/-- The own-map final assignment has exactly one descriptor. -/
theorem ownFinalTetrahedralAssignment_existsUnique
    (distinct : ∀ i j : Fin 4, i ≠ j →
      ¬ ProperTransport input.certified.detectedMultiCenterMolecule S.cfg S.c i j)
    (coordinates : input.certified.ActualCanonicalRootCoordinates
      (⟨S.c.1, S.c.2⟩ : input.certified.TetrahedralCenter)) :
    ∃! label, DeclarativeCIP.FinalTetrahedralAssignment (geoProblem (input := input))
      (ownDescriptorMap input) S.declUnit label := by
  obtain ⟨rs, _, hjudgment, hunique⟩ :=
    S.orderedReferenceState_top_descriptorJudgment_ownMap distinct coordinates
  exact DeclarativeCIP.finalTetrahedralAssignment_existsUnique
    (geoProblem (input := input)) (ownDescriptorMap input) S.declUnit rs hjudgment hunique

end ActualCentrePhysicalSetup
end Rule4aTableBridge

end

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedState_eq_generated_of_strictDependency
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.armNode_sourceWitness
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ownMap_eq_generated_at_strictSource
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.occurrenceReading_eq_of_armNode
assert_kernel_only
  TetraStereo.OneCenter.DeclarativeCIP.multiReferenceJudgment_congr_of_occurrenceReading_eq
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.armPairJudgment_iff_generated
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ruleOutcome_map_iff_of_rank
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ruleOutcome_map_iff
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.rule6_never_ownMap
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.higher_map_iff_generated
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.earlierRulesTie5_map_iff_generated
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ranks_map_iff_generated
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.descriptorJudgment_map_iff_generated
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.finalRule5PairCount_eq_declarative
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedReferenceState_top_descriptorJudgment_ownMap
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.orderedReferenceState_top_satisfies_ownFinalAssignment
assert_kernel_only
  TetraStereo.OneCenter.Rule4aTableBridge.ActualCentrePhysicalSetup.ownFinalTetrahedralAssignment_existsUnique
