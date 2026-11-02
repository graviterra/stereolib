import TetraStereo.OneCenter.DeclarativeCIPLigandSignatureLayout
import TetraStereo.OneCenter.DeclarativeCIPRankKeyProjection
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# A molecular eight-rule problem that keeps multi-reference Rule 4b

`DeclarativeCIPMolecularEvidence.molecularEvidence` maps two or more nearest eligible references
to `unsupported`, so its per-node Rule-4b observation is absent on the whole ligand and two such
ligands silently tie at Rule 4b.  This module builds a specialized molecular `Problem` whose
ordinary-rule judgments are whole-ligand judgments read from independent declarative objects, so
that the P-92.5.2.1 selection and complete readings survive:

* Rules 1a, 1b, 2: the constitutional first-difference hierarchy outcome at every canonical
  addressing (`ConstitutionalCanonical`, the existing localized constitutional judgment);
* Rule 3: the Rule-3 component of the ligand root's ordinary key over the pre-Rule-4b evidence
  (`rankEvidence`: Rules 3 and 4a), compared as keys;
* Rule 4a: the Rule-4a component of that key (`rule4aComponent`);
* Rule 4b: the independent ligand signature `ligandSignatureAt` — criterion (c)(i) count
  (`empty ↦ 0`, `one ↦ 2`, `both ↦ 1`), then the complete readings in descending order — compared
  by `signatureCompare`;
* Rule 4c: the Rule-4c component of the ordinary key over the molecular evidence. This is the
  legacy per-node projection; it is not a general multireference-aware Rule-4c theorem;
* Rule 5: the first difference of the **common-`R` seniority streams** of the two ligands
  (`ligandRule5Stream`): the ligand's head reference is the reference of its best complete reading
  (`headSense`, the head of `descendingPair`), and at every address the stream is `1` exactly when
  the chiral node that this reading lays out there carries the senior sense (`R`), read back from
  the reading's like/unlike code.  This is the selected complete reading / first chiral criterion,
  with its reference-order covariance; it is not "the `R` reference wins".

Every layout is the pair's common bound (`pairWidth`, `pairHeight`) or the ligand's own layout,
so each judgment is a function of the two isomorphism classes.  The isomorphism invariance of the
P-92.5.2.1 selection is proved here (`referenceSelection_iso`, through `ancestorChain_iso` and
`rankPath_iso`), and with it the invariance of every stereochemical judgment
(`multiReferenceJudgment_iso`).  `Problem.RuleOutcome`'s quantification over every faithful exact
expansion is unchanged; `ruleOutcome_iff_judgment` reduces it to any one admissible pair.

These judgments are generic invariant constructions from a molecule, descriptor map and exact
ligand graphs. Their chemical agreement with the ordered evaluator is established separately by
`LocalizedActualOrderedRootEightRuleConnection` on its physical domain: finite, acyclic,
simple-bonded, constant-formal-charge molecules with no double-bond records and the stated rigid /
terminal-twin conditions. In particular, the Rule-4c projection is adequate there because the
physical reader proves that every descriptor read has `pseudoSense = none`, so
`rule4cObservation` yields the same zero label at every node. This does not establish Rule-4c
agreement for arbitrary descriptor maps with multireference ties.

Rule 6 is outside this problem (`False`), as are auxiliary dependencies.  The orientation judgment
is a parameter.  Nothing here reads a runtime value.

`seniorityMirror_gt_iff` is the declarative form of the mirror-pair decision: when two streams
read the same like/unlike observations under opposite head senses, the first difference is at the
first chiral address and the ligand whose reading names the senior sense there precedes.
-/

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

open Certificate.CanonicalSphereKey (Key WellShaped pathObservationOf)
open RootedDigraph

noncomputable section
open scoped Classical

universe u

/-! ## Isomorphism invariance of the P-92.5.2.1 selection -/

section SelectionIso

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) {left right : RootedDigraph Atom}
  (iso : RootedDigraph.Iso left right)

local instance multiRefNodeFintype (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

omit [Fintype Atom] [DecidableEq Atom] in
theorem ancestorChain_rel_iso {node : left.Node} {chain : List left.Node}
    (h : AncestorChain left node chain) :
    AncestorChain right (iso.toEquiv node) (chain.map iso.toEquiv) := by
  induction h with
  | root =>
      show AncestorChain right (iso.toEquiv left.root) [iso.toEquiv left.root]
      rw [iso.map_root]
      exact AncestorChain.root
  | step hedge _ ih =>
      rw [List.map_append, List.map_singleton]
      exact AncestorChain.step ((iso.map_child _ _).1 hedge) ih

omit [Fintype Atom] [DecidableEq Atom] in
/-- The ancestor chain is carried by an isomorphism. -/
theorem ancestorChain_iso (node : left.Node) :
    ancestorChain right (iso.toEquiv node) = (ancestorChain left node).map iso.toEquiv := by
  have back : ∀ {n : right.Node} {c : List right.Node}, AncestorChain right n c →
      AncestorChain left (iso.toEquiv.symm n) (c.map iso.toEquiv.symm) :=
    fun h => ancestorChain_rel_iso iso.symm h
  by_cases hu : ∃! chain, AncestorChain left node chain
  · have hu' : ∃! chain, AncestorChain right (iso.toEquiv node) chain := by
      obtain ⟨c, hc, huniq⟩ := hu
      refine ⟨c.map iso.toEquiv, ancestorChain_rel_iso iso hc, fun c' hc' => ?_⟩
      have hback := back hc'
      rw [Equiv.symm_apply_apply] at hback
      rw [← huniq _ hback, List.map_map]
      simp
    rw [ancestorChain, dif_pos hu', ancestorChain, dif_pos hu]
    exact hu'.unique (Classical.choose_spec hu'.exists)
      (ancestorChain_rel_iso iso (Classical.choose_spec hu.exists))
  · have hu' : ¬ ∃! chain, AncestorChain right (iso.toEquiv node) chain := by
      rintro ⟨c, hc, huniq⟩
      apply hu
      have hback := back hc
      rw [Equiv.symm_apply_apply] at hback
      refine ⟨c.map iso.toEquiv.symm, hback, fun c' hc' => ?_⟩
      rw [← huniq _ (ancestorChain_rel_iso iso hc'), List.map_map]
      simp
    rw [ancestorChain, dif_neg hu', ancestorChain, dif_neg hu]
    rfl

theorem rankEvidence_preserved :
    RootedDigraph.Addressing.EvidencePreserved iso
      (rankEvidence molecule descriptorMap unit left)
      (rankEvidence molecule descriptorMap unit right) := by
  intro node
  simp only [rankEvidence]
  rw [rule3Observation_iso molecule descriptorMap unit iso node,
    rule4aObservation_iso molecule descriptorMap unit iso node]

theorem rankKey_iso (node : left.Node) :
    rankKey molecule descriptorMap unit right (iso.toEquiv node) =
      rankKey molecule descriptorMap unit left node := by
  unfold rankKey
  rw [width_iso iso, height_iso iso]
  exact ordinaryKey_iso molecule iso (rankEvidence_preserved molecule descriptorMap unit iso)
    _ _ node

theorem rankPath_iso (node : left.Node) :
    rankPath molecule descriptorMap unit right (iso.toEquiv node) =
      rankPath molecule descriptorMap unit left node := by
  unfold rankPath
  rw [ancestorChain_iso iso node, List.map_map]
  congr 1
  funext x
  exact rankKey_iso molecule descriptorMap unit iso x

theorem inReferenceClass_iso (node : left.Node) :
    InReferenceClass molecule descriptorMap unit left node ↔
      InReferenceClass molecule descriptorMap unit right (iso.toEquiv node) := by
  unfold InReferenceClass
  rw [nearestEligible_iso molecule descriptorMap unit iso node,
    rankPath_iso molecule descriptorMap unit iso node]
  refine and_congr_right fun _ => iso.toEquiv.forall_congr fun other => ?_
  rw [nearestEligible_iso molecule descriptorMap unit iso other,
    rankPath_iso molecule descriptorMap unit iso other]

include iso in
theorem seniorCount_iso :
    seniorCount molecule descriptorMap unit right = seniorCount molecule descriptorMap unit left := by
  unfold seniorCount referenceClass
  symm
  apply Finset.card_equiv iso.toEquiv
  intro node
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [inReferenceClass_iso molecule descriptorMap unit iso node,
    eligibleSense_iso molecule descriptorMap unit iso node]

include iso in
theorem juniorCount_iso :
    juniorCount molecule descriptorMap unit right = juniorCount molecule descriptorMap unit left := by
  unfold juniorCount referenceClass
  symm
  apply Finset.card_equiv iso.toEquiv
  intro node
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [inReferenceClass_iso molecule descriptorMap unit iso node,
    eligibleSense_iso molecule descriptorMap unit iso node]

include iso in
theorem exists_eligible_iso :
    (∃ node, Eligible molecule descriptorMap unit left node) ↔
      ∃ node, Eligible molecule descriptorMap unit right node :=
  iso.toEquiv.exists_congr fun node => eligible_iso molecule descriptorMap unit iso node

include iso in
/-- **The P-92.5.2.1 selection is an isomorphism invariant.** -/
theorem referenceSelection_iso :
    referenceSelection molecule descriptorMap unit right =
      referenceSelection molecule descriptorMap unit left := by
  unfold referenceSelection
  rw [seniorCount_iso molecule descriptorMap unit iso, juniorCount_iso molecule descriptorMap unit iso]
  by_cases h : ∃ node, Eligible molecule descriptorMap unit left node
  · rw [if_neg (not_not.2 ((exists_eligible_iso molecule descriptorMap unit iso).1 h)),
      if_neg (not_not.2 h)]
  · rw [if_pos (fun h' => h ((exists_eligible_iso molecule descriptorMap unit iso).2 h')), if_pos h]

include iso in
theorem ligandSignatureAt_iso (W D : ℕ) :
    ligandSignatureAt molecule descriptorMap unit right W D =
      ligandSignatureAt molecule descriptorMap unit left W D := by
  unfold ligandSignatureAt
  simp only [referenceSelection_iso molecule descriptorMap unit iso,
    readingAt_iso molecule descriptorMap unit iso W D]

end SelectionIso

/-! ## The whole-ligand observables -/

section Observables

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

/-- Rule 3: the Rule-3 component of the ligand root's ordinary key over the evidence of the
rules applied before Rule 4b. -/
def ligandRule3Key (W D : ℕ) : Key StereoLabel :=
  (ofLex (ordinaryKey molecule graph (rankEvidence molecule descriptorMap unit graph) W D
    graph.root)).2.getD (stereoIndex .rule3DoubleBondGeometry) []

/-- Rule 4a: the Rule-4a component of the same key. -/
def ligandRule4aKey (W D : ℕ) : Key StereoLabel :=
  rule4aComponent molecule graph (rankEvidence molecule descriptorMap unit graph) W D graph.root

/-- Rule 4c: the Rule-4c component of the ligand root's ordinary key over the molecular
evidence. -/
def ligandRule4cKey (W D : ℕ) : Key StereoLabel :=
  (ofLex (ordinaryKey molecule graph (molecularEvidence molecule descriptorMap unit graph) W D
    graph.root)).2.getD (stereoIndex .rule4cPseudoasymmetricDescriptor) []

/-- The observation of a like (`1`) Rule-4b pairing. -/
def likeObservation : WithBot StereoLabel :=
  (((encodeReadings [[1]] : StereoCode) : StereoLabel) : WithBot StereoLabel)

/-- The observation of an unlike (`0`) Rule-4b pairing. -/
def unlikeObservation : WithBot StereoLabel :=
  (((encodeReadings [[0]] : StereoCode) : StereoLabel) : WithBot StereoLabel)

theorem likeObservation_ne_unlikeObservation : likeObservation ≠ unlikeObservation := by
  unfold likeObservation unlikeObservation encodeReadings
  simp

/-- The Rule-5 seniority read from one like/unlike observation of a reading under `reference`:
`1` exactly when the observed chiral node carries the senior sense. -/
def seniorityOf (reference : DescriptorSense) (observation : WithBot StereoLabel) : ℕ :=
  if observation = likeObservation then (if reference = .senior then 1 else 0)
  else if observation = unlikeObservation then (if reference = .senior then 0 else 1)
  else 0

/-- The head reference of a ligand: the reference of its best complete reading (the head of
`descendingPair`), or none without references. -/
def headSense (selection : ReferenceSelection) (reading : DescriptorSense → Key StereoLabel) :
    Option DescriptorSense :=
  match selection with
  | .empty => none
  | .one sense => some sense
  | .both => some (if compare (reading .senior) (reading .junior) = .lt then .junior else .senior)

/-- **Rule 5: the common-`R` seniority stream** of a ligand, laid out over its head reading. -/
def ligandRule5Stream (path : List ℕ) : ℕ :=
  match headSense (referenceSelection molecule descriptorMap unit graph)
      (readingAt molecule descriptorMap unit graph graph.width graph.height) with
  | none => 0
  | some sense =>
      seniorityOf sense
        (pathObservationOf graph.width graph.height
          (readingAt molecule descriptorMap unit graph graph.width graph.height sense) path)

/-- The common layout of a pair of ligand graphs. -/
def pairWidth (left right : RootedDigraph Atom) : ℕ := max left.width right.width

def pairHeight (left right : RootedDigraph Atom) : ℕ := max left.height right.height

end Observables

section ObservableIso

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom) (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) {left right : RootedDigraph Atom}
  (iso : RootedDigraph.Iso left right)

include iso in
theorem ligandRule3Key_iso (W D : ℕ) :
    ligandRule3Key molecule descriptorMap unit right W D =
      ligandRule3Key molecule descriptorMap unit left W D := by
  unfold ligandRule3Key
  rw [← iso.map_root, ordinaryKey_iso molecule iso
    (rankEvidence_preserved molecule descriptorMap unit iso) W D left.root]

include iso in
theorem ligandRule4aKey_iso (W D : ℕ) :
    ligandRule4aKey molecule descriptorMap unit right W D =
      ligandRule4aKey molecule descriptorMap unit left W D := by
  unfold ligandRule4aKey rule4aComponent
  rw [← iso.map_root, ordinaryKey_iso molecule iso
    (rankEvidence_preserved molecule descriptorMap unit iso) W D left.root]

include iso in
theorem ligandRule4cKey_iso (W D : ℕ) :
    ligandRule4cKey molecule descriptorMap unit right W D =
      ligandRule4cKey molecule descriptorMap unit left W D := by
  unfold ligandRule4cKey
  rw [← iso.map_root, ordinaryKey_iso molecule iso
    (molecularEvidence_preserved molecule descriptorMap unit iso) W D left.root]

include iso in
theorem ligandRule5Stream_iso (path : List ℕ) :
    ligandRule5Stream molecule descriptorMap unit right path =
      ligandRule5Stream molecule descriptorMap unit left path := by
  have hreading : readingAt molecule descriptorMap unit right left.width left.height =
      readingAt molecule descriptorMap unit left left.width left.height :=
    funext (readingAt_iso molecule descriptorMap unit iso left.width left.height)
  unfold ligandRule5Stream
  simp only [width_iso iso, height_iso iso, referenceSelection_iso molecule descriptorMap unit iso,
    hreading]

omit [Fintype Atom] [DecidableEq Atom] in
theorem pairWidth_iso {left' right' : RootedDigraph Atom} (isoL : RootedDigraph.Iso left left')
    (isoR : RootedDigraph.Iso right right') : pairWidth left' right' = pairWidth left right := by
  unfold pairWidth
  rw [width_iso isoL, width_iso isoR]

omit [Fintype Atom] [DecidableEq Atom] in
theorem pairHeight_iso {left' right' : RootedDigraph Atom} (isoL : RootedDigraph.Iso left left')
    (isoR : RootedDigraph.Iso right right') : pairHeight left' right' = pairHeight left right := by
  unfold pairHeight
  rw [height_iso isoL, height_iso isoR]

end ObservableIso

/-! ## The judgments and the problem -/

section Problem

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)

/-- The constitutional first-difference outcome at every canonical addressing of both graphs,
with both addressing families nonempty (the existing localized constitutional judgment). -/
def ConstitutionalCanonical (rule : ConstitutionalRule) (left right : RootedDigraph Atom)
    (outcome : Ordering) : Prop :=
  (∃ leftAddressing : left.Addressing, CanonicalAddressing molecule leftAddressing) ∧
    (∃ rightAddressing : right.Addressing, CanonicalAddressing molecule rightAddressing) ∧
    ∀ leftAddressing rightAddressing,
      CanonicalAddressing molecule leftAddressing →
        CanonicalAddressing molecule rightAddressing →
          ConstitutionalHierarchyOutcome molecule rule left leftAddressing right rightAddressing
            outcome

/-- **The whole-ligand ordinary-rule judgments.** -/
def MultiReferenceJudgment (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) :
    SequenceRule → RootedDigraph Atom → RootedDigraph Atom → Ordering → Prop
  | .rule1aAtomicNumber, left, right, outcome =>
      ConstitutionalCanonical molecule .rule1aAtomicNumber left right outcome
  | .rule1bDuplicateNodeProximity, left, right, outcome =>
      ConstitutionalCanonical molecule .rule1bDuplicateNodeProximity left right outcome
  | .rule2AtomicMass, left, right, outcome =>
      ConstitutionalCanonical molecule .rule2AtomicMass left right outcome
  | .rule3DoubleBondGeometry, left, right, outcome =>
      compare
        (ligandRule3Key molecule descriptorMap unit left (pairWidth left right) (pairHeight left right))
        (ligandRule3Key molecule descriptorMap unit right (pairWidth left right)
          (pairHeight left right)) = outcome
  | .rule4aStereogenicUnitKind, left, right, outcome =>
      compare
        (ligandRule4aKey molecule descriptorMap unit left (pairWidth left right)
          (pairHeight left right))
        (ligandRule4aKey molecule descriptorMap unit right (pairWidth left right)
          (pairHeight left right)) = outcome
  | .rule4bLikeUnlikeDescriptorPairs, left, right, outcome =>
      signatureCompare
        (ligandSignatureAt molecule descriptorMap unit left (pairWidth left right)
          (pairHeight left right))
        (ligandSignatureAt molecule descriptorMap unit right (pairWidth left right)
          (pairHeight left right)) = outcome
  | .rule4cPseudoasymmetricDescriptor, left, right, outcome =>
      compare
        (ligandRule4cKey molecule descriptorMap unit left (pairWidth left right)
          (pairHeight left right))
        (ligandRule4cKey molecule descriptorMap unit right (pairWidth left right)
          (pairHeight left right)) = outcome
  | .rule5EnantiomorphicDescriptor, left, right, outcome =>
      FirstDifferenceOutcome
        (fun position localOutcome =>
          compare (ligandRule5Stream molecule descriptorMap unit left position)
            (ligandRule5Stream molecule descriptorMap unit right position) = localOutcome)
        outcome
  | .rule6ReferencePromotion, _, _, _ => False

/-- **The specialized molecular problem.**  Units are detected occurrences, ligands come from a
`DetectedFrame`, admissible expansions are the faithful exact expansions, and the ordinary rules
are the whole-ligand judgments above.  Rule 6 and dependencies are not modelled (`False`). -/
def multiReferenceProblem (frame : DetectedFrame molecule)
    (orientation : DetectedOccurrence molecule → Equiv.Perm (Fin 4) → Descriptor → Prop) :
    Problem Atom (DetectedOccurrence molecule) where
  molecule := molecule
  ligandAtom := frame.ligand
  admissibleExpansion unit ligand graph :=
    RootedDigraph.FaithfulExactExpansion molecule unit.1.atom (frame.ligand unit ligand) graph
  ordinaryRuleJudgment descriptorMap rule unit left right outcome :=
    MultiReferenceJudgment molecule descriptorMap unit rule left right outcome
  admissibleRule6Reference _ _ _ := False
  rule6Judgment _ _ _ _ _ _ := False
  dependsOn _ _ _ := False
  orientationJudgment := orientation

/-- Every stereochemical whole-ligand judgment is invariant under isomorphisms of both graphs. -/
theorem multiReferenceJudgment_iso (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (rule : SequenceRule) (hrule : 3 ≤ rule.rank)
    {left left' right right' : RootedDigraph Atom} (isoL : RootedDigraph.Iso left left')
    (isoR : RootedDigraph.Iso right right') (outcome : Ordering) :
    MultiReferenceJudgment molecule descriptorMap unit rule left right outcome ↔
      MultiReferenceJudgment molecule descriptorMap unit rule left' right' outcome := by
  have hW := pairWidth_iso isoL isoR
  have hD := pairHeight_iso isoL isoR
  cases rule with
  | rule1aAtomicNumber => exact absurd hrule (by decide)
  | rule1bDuplicateNodeProximity => exact absurd hrule (by decide)
  | rule2AtomicMass => exact absurd hrule (by decide)
  | rule3DoubleBondGeometry =>
      simp only [MultiReferenceJudgment]
      rw [hW, hD, ligandRule3Key_iso molecule descriptorMap unit isoL,
        ligandRule3Key_iso molecule descriptorMap unit isoR]
  | rule4aStereogenicUnitKind =>
      simp only [MultiReferenceJudgment]
      rw [hW, hD, ligandRule4aKey_iso molecule descriptorMap unit isoL,
        ligandRule4aKey_iso molecule descriptorMap unit isoR]
  | rule4bLikeUnlikeDescriptorPairs =>
      simp only [MultiReferenceJudgment]
      rw [hW, hD, ligandSignatureAt_iso molecule descriptorMap unit isoL,
        ligandSignatureAt_iso molecule descriptorMap unit isoR]
  | rule4cPseudoasymmetricDescriptor =>
      simp only [MultiReferenceJudgment]
      rw [hW, hD, ligandRule4cKey_iso molecule descriptorMap unit isoL,
        ligandRule4cKey_iso molecule descriptorMap unit isoR]
  | rule5EnantiomorphicDescriptor =>
      simp only [MultiReferenceJudgment]
      have hl : ligandRule5Stream molecule descriptorMap unit left' =
          ligandRule5Stream molecule descriptorMap unit left :=
        funext (ligandRule5Stream_iso molecule descriptorMap unit isoL)
      have hr : ligandRule5Stream molecule descriptorMap unit right' =
          ligandRule5Stream molecule descriptorMap unit right :=
        funext (ligandRule5Stream_iso molecule descriptorMap unit isoR)
      rw [hl, hr]
  | rule6ReferencePromotion => exact Iff.rfl

theorem outcomeOnGraphs_multiReference (frame : DetectedFrame molecule)
    (orientation : DetectedOccurrence molecule → Equiv.Perm (Fin 4) → Descriptor → Prop)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule)) (rule : SequenceRule)
    (hrule : rule ≠ .rule6ReferencePromotion) (unit : DetectedOccurrence molecule)
    (left right : RootedDigraph Atom) (outcome : Ordering) :
    (multiReferenceProblem molecule frame orientation).OutcomeOnGraphs descriptorMap rule unit
        left right outcome ↔
      MultiReferenceJudgment molecule descriptorMap unit rule left right outcome := by
  cases rule <;> first | exact absurd rfl hrule | exact Iff.rfl

/-- **Rule outcomes at one admissible pair.**  For a stereochemical rule, the problem's rule
outcome — quantified over every faithful exact expansion of both ligands — is the whole-ligand
judgment at any one admissible pair. -/
theorem ruleOutcome_iff_judgment (frame : DetectedFrame molecule)
    (orientation : DetectedOccurrence molecule → Equiv.Perm (Fin 4) → Descriptor → Prop)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule)) (rule : SequenceRule)
    (hrule : 3 ≤ rule.rank) (h6 : rule ≠ .rule6ReferencePromotion)
    (unit : DetectedOccurrence molecule) {i j : Fin 4} {leftGraph rightGraph : RootedDigraph Atom}
    (hleft : (multiReferenceProblem molecule frame orientation).admissibleExpansion unit i leftGraph)
    (hright : (multiReferenceProblem molecule frame orientation).admissibleExpansion unit j
      rightGraph)
    (outcome : Ordering) :
    (multiReferenceProblem molecule frame orientation).RuleOutcome descriptorMap rule unit i j
        outcome ↔
      MultiReferenceJudgment molecule descriptorMap unit rule leftGraph rightGraph outcome := by
  constructor
  · intro h
    exact (outcomeOnGraphs_multiReference molecule frame orientation descriptorMap rule h6 unit
      leftGraph rightGraph outcome).1 (h leftGraph rightGraph hleft hright)
  · intro h left right hl hr
    obtain ⟨isoL⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso molecule unit.1.atom
      (frame.ligand unit i) leftGraph left hleft hl
    obtain ⟨isoR⟩ := RootedDigraph.faithfulExactExpansion_unique_up_to_iso molecule unit.1.atom
      (frame.ligand unit j) rightGraph right hright hr
    exact (outcomeOnGraphs_multiReference molecule frame orientation descriptorMap rule h6 unit
      left right outcome).2
      ((multiReferenceJudgment_iso molecule descriptorMap unit rule hrule isoL isoR outcome).1 h)

end Problem

/-! ## Constant-label components are constitutional shapes -/

section ConstantComponents

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)

local instance constNodeFintype (graph : RootedDigraph Atom) : Fintype graph.Node :=
  graph.nodeFintype

/-- A stereochemical component whose label is one constant `label` at every node observes
`some label` exactly where the constitutional vector key observes a node. -/
theorem constComponent_pathObservation (graph : RootedDigraph Atom)
    (evidence : StereochemicalEvidence graph) (rule : StereochemicalRule) (label : StereoLabel)
    (hlabel : ∀ node, stereoLabel graph evidence rule node = label) (W D : ℕ) :
    ∀ (path : List ℕ) (node : graph.Node),
      stereoNodePathObservation molecule graph evidence W D rule node path =
        (nodePathObservation molecule graph W D 0 node path).map (fun _ => label)
  | [], node => by
      rw [stereoNodePathObservation_nil, hlabel, nodePathObservation_nil molecule graph (by omega)]
      rfl
  | digit :: path, node => by
      obtain ⟨ranked, hperm, hsorted⟩ := exists_ordinaryRanked molecule graph evidence W D node
      rw [stereoNodePathObservation_cons molecule graph evidence W D rule node hperm hsorted,
        nodePathObservation_cons molecule graph (by omega) node hperm
          (ruleKey_sorted_of_ordinary_sorted molecule graph evidence W D hsorted)]
      by_cases hguard : digit < W ∧ path.length < D
      · rw [if_pos hguard, if_pos hguard]
        cases ranked[digit]? with
        | none => rfl
        | some child =>
            simp only [Option.map_some, Option.getD_some]
            exact constComponent_pathObservation graph evidence rule label hlabel W D path child
      · rw [if_neg hguard, if_neg hguard]
        rfl

/-- Two ligand roots with equal constitutional vector keys have equal constant-label
components. -/
theorem constComponent_eq_of_ruleKey_eq {left right : RootedDigraph Atom}
    (leftEvidence : StereochemicalEvidence left) (rightEvidence : StereochemicalEvidence right)
    (rule : StereochemicalRule) (label : StereoLabel)
    (hleft : ∀ node, stereoLabel left leftEvidence rule node = label)
    (hright : ∀ node, stereoLabel right rightEvidence rule node = label) (W D : ℕ)
    (h : ruleKey molecule left W D left.root = ruleKey molecule right W D right.root) :
    (ofLex (ordinaryKey molecule left leftEvidence W D left.root)).2.getD (stereoIndex rule) [] =
      (ofLex (ordinaryKey molecule right rightEvidence W D right.root)).2.getD
        (stereoIndex rule) [] := by
  refine (Certificate.CanonicalSphereKey.key_eq_iff_pathObservation
    (ordinaryKey_stereo_wellShaped molecule left leftEvidence W D rule left.root)
    (ordinaryKey_stereo_wellShaped molecule right rightEvidence W D rule right.root)).2 ?_
  intro path
  change stereoNodePathObservation molecule left leftEvidence W D rule left.root path =
    stereoNodePathObservation molecule right rightEvidence W D rule right.root path
  rw [constComponent_pathObservation molecule left leftEvidence rule label hleft W D path left.root,
    constComponent_pathObservation molecule right rightEvidence rule label hright W D path
      right.root]
  unfold nodePathObservation
  rw [h]

end ConstantComponents

/-! ## The mirror-pair Rule-5 decision, declaratively -/

section Mirror

theorem seniorityOf_like (reference : DescriptorSense) :
    seniorityOf reference likeObservation = if reference = .senior then 1 else 0 := by
  unfold seniorityOf
  rw [if_pos rfl]

theorem seniorityOf_unlike (reference : DescriptorSense) :
    seniorityOf reference unlikeObservation = if reference = .senior then 0 else 1 := by
  unfold seniorityOf
  rw [if_neg (Ne.symm likeObservation_ne_unlikeObservation), if_pos rfl]

theorem seniorityOf_other (reference : DescriptorSense) {observation : WithBot StereoLabel}
    (hlike : observation ≠ likeObservation) (hunlike : observation ≠ unlikeObservation) :
    seniorityOf reference observation = 0 := by
  unfold seniorityOf
  rw [if_neg hlike, if_neg hunlike]

/-- The observation that makes `reference`'s reading name the senior sense. -/
def seniorObservation (reference : DescriptorSense) : WithBot StereoLabel :=
  if reference = .senior then likeObservation else unlikeObservation

/-- At one address, two readings of the same observation under opposite references compare `gt`
exactly at the observation naming the senior sense for the first reading, `eq` exactly off the
like/unlike observations. -/
theorem compare_seniority_mirror (reference : DescriptorSense) (observation : WithBot StereoLabel) :
    (compare (seniorityOf reference observation) (seniorityOf reference.mirror observation) =
        .gt ↔ observation = seniorObservation reference) ∧
      (compare (seniorityOf reference observation) (seniorityOf reference.mirror observation) =
        .eq ↔ observation ≠ likeObservation ∧ observation ≠ unlikeObservation) := by
  have hne := likeObservation_ne_unlikeObservation
  by_cases hl : observation = likeObservation
  · subst hl
    cases reference <;>
      simp [seniorityOf_like, DescriptorSense.mirror, seniorObservation, hne] <;> decide
  · by_cases hu : observation = unlikeObservation
    · subst hu
      cases reference <;>
        simp [seniorityOf_unlike, DescriptorSense.mirror, seniorObservation, Ne.symm hne] <;> decide
    · rw [seniorityOf_other _ hl hu, seniorityOf_other _ hl hu]
      cases reference <;> simp [seniorObservation, hl, hu]

/-- **The declarative mirror-pair Rule-5 decision.**  Two streams reading one observation
function under opposite head references: the first is senior exactly when, at the first address
carrying a like/unlike observation, that observation names the senior sense for the first
reading. -/
theorem seniorityMirror_gt_iff (observation : List ℕ → WithBot StereoLabel)
    (reference : DescriptorSense) :
    FirstDifferenceOutcome
        (fun position localOutcome =>
          compare (seniorityOf reference (observation position))
            (seniorityOf reference.mirror (observation position)) = localOutcome) .gt ↔
      ∃ position, observation position = seniorObservation reference ∧
        ∀ earlier, HierarchyAddressBefore earlier position →
          observation earlier ≠ likeObservation ∧ observation earlier ≠ unlikeObservation := by
  constructor
  · rintro ⟨position, hgt, hearlier⟩
    exact ⟨position, (compare_seniority_mirror reference _).1.1 hgt,
      fun earlier h => (compare_seniority_mirror reference _).2.1 (hearlier earlier h)⟩
  · rintro ⟨position, hpos, hearlier⟩
    exact ⟨position, (compare_seniority_mirror reference _).1.2 hpos,
      fun earlier h => (compare_seniority_mirror reference _).2.2 (hearlier earlier h)⟩

end Mirror

end

end DeclarativeCIP
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ancestorChain_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.referenceSelection_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ligandSignatureAt_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ligandRule5Stream_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.multiReferenceJudgment_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ruleOutcome_iff_judgment
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.constComponent_eq_of_ruleKey_eq
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.seniorityMirror_gt_iff
