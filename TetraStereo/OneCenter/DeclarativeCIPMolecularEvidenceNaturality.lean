import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidence
import TetraStereo.OneCenter.DeclarativeCIPOrdinaryCanonicalOrderLaws
import TetraStereo.OneCenter.IUPACP92SemanticGraphFaithfulExpansion
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace DeclarativeCIP

noncomputable section

open scoped Classical

universe u
































/-! ## Transport of occurrence contexts -/

section Context

variable {Atom : Type u} {left right : RootedDigraph Atom} (iso : RootedDigraph.Iso left right)

theorem ancestorPath_rel_transport {node : left.Node} {path : List (Option Atom)}
    (h : AncestorPath left node path) : AncestorPath right (iso.toEquiv node) path := by
  induction h with
  | root =>
      rw [iso.map_label left.root, iso.map_root]
      exact AncestorPath.root
  | step hedge _ ih =>
      rw [iso.map_label]
      exact AncestorPath.step ((iso.map_child _ _).1 hedge) ih

theorem ancestorPath_rel_iso_iff (node : left.Node) (path : List (Option Atom)) :
    AncestorPath left node path ↔ AncestorPath right (iso.toEquiv node) path := by
  refine ⟨ancestorPath_rel_transport iso, fun h => ?_⟩
  have hback := ancestorPath_rel_transport iso.symm h
  rwa [show iso.symm.toEquiv (iso.toEquiv node) = node from iso.toEquiv.symm_apply_apply node]
    at hback

theorem ancestorPath_iso (node : left.Node) :
    ancestorPath left node = ancestorPath right (iso.toEquiv node) := by
  have h := ancestorPath_rel_iso_iff iso node
  unfold ancestorPath
  by_cases hleft : ∃! path, AncestorPath left node path
  · have hright : ∃! path, AncestorPath right (iso.toEquiv node) path :=
      (existsUnique_congr h).1 hleft
    rw [dif_pos hleft, dif_pos hright]
    exact congrArg some (hright.unique ((h _).1 (Classical.choose_spec hleft.exists))
      (Classical.choose_spec hright.exists))
  · have hright : ¬ ∃! path, AncestorPath right (iso.toEquiv node) path :=
      fun hright => hleft ((existsUnique_congr h).2 hright)
    rw [dif_neg hleft, dif_neg hright]

theorem ancestorAtoms_iso (node : left.Node) :
    ancestorAtoms left node = ancestorAtoms right (iso.toEquiv node) := by
  rw [ancestorAtoms, ancestorAtoms, ancestorPath_iso iso]

end Context

/-! ## Transport of readings, eligibility and references -/

section Evidence

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom] (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule)) (unit : DetectedOccurrence molecule)
  {left right : RootedDigraph Atom} (iso : RootedDigraph.Iso left right)

theorem occurrenceReading_iso (node : left.Node) :
    occurrenceReading molecule descriptorMap unit left node =
      occurrenceReading molecule descriptorMap unit right (iso.toEquiv node) := by
  unfold occurrenceReading
  rw [iso.map_label node, ancestorAtoms_iso iso node]

theorem eligibleSense_iso (node : left.Node) :
    eligibleSense molecule descriptorMap unit left node =
      eligibleSense molecule descriptorMap unit right (iso.toEquiv node) := by
  unfold eligibleSense
  rw [occurrenceReading_iso molecule descriptorMap unit iso node]

theorem eligible_iso (node : left.Node) :
    Eligible molecule descriptorMap unit left node ↔
      Eligible molecule descriptorMap unit right (iso.toEquiv node) := by
  unfold Eligible
  rw [eligibleSense_iso molecule descriptorMap unit iso node]

theorem nearestEligible_iso (node : left.Node) :
    NearestEligible molecule descriptorMap unit left node ↔
      NearestEligible molecule descriptorMap unit right (iso.toEquiv node) := by
  unfold NearestEligible
  rw [eligible_iso molecule descriptorMap unit iso node, iso.map_depth node]
  refine and_congr_right fun _ => iso.toEquiv.forall_congr fun other => ?_
  rw [eligible_iso molecule descriptorMap unit iso other, iso.map_depth other]

include iso in
/-- The reference population is an isomorphism invariant. -/
theorem referencePopulation_iso :
    referencePopulation molecule descriptorMap unit left =
      referencePopulation molecule descriptorMap unit right := by
  have heligible : (∃ node, Eligible molecule descriptorMap unit left node) ↔
      ∃ node, Eligible molecule descriptorMap unit right node :=
    iso.toEquiv.exists_congr (eligible_iso molecule descriptorMap unit iso)
  have hnearest : (∃! node, NearestEligible molecule descriptorMap unit left node) ↔
      ∃! node, NearestEligible molecule descriptorMap unit right node :=
    iso.toEquiv.existsUnique_congr (nearestEligible_iso molecule descriptorMap unit iso)
  unfold referencePopulation
  by_cases hexists : ∃ node, Eligible molecule descriptorMap unit left node
  · rw [if_neg (not_not.2 hexists), if_neg (not_not.2 (heligible.1 hexists))]
    by_cases hunique : ∃! node, NearestEligible molecule descriptorMap unit left node
    · have hunique' := hnearest.1 hunique
      rw [dif_pos hunique, dif_pos hunique']
      have hchoice : Classical.choose hunique'.exists = iso.toEquiv (Classical.choose hunique.exists) :=
        hunique'.unique (Classical.choose_spec hunique'.exists)
          ((nearestEligible_iso molecule descriptorMap unit iso _).1
            (Classical.choose_spec hunique.exists))
      congr 1
      exact option_get_congr ((eligibleSense_iso molecule descriptorMap unit iso _).trans
        (congrArg _ hchoice.symm)) _ _
    · rw [dif_neg hunique, dif_neg fun h => hunique (hnearest.2 h)]
  · rw [if_pos hexists, if_pos fun h => hexists (heligible.2 h)]

theorem rule3Observation_iso (node : left.Node) :
    rule3Observation molecule descriptorMap unit left node =
      rule3Observation molecule descriptorMap unit right (iso.toEquiv node) := by
  unfold rule3Observation
  rw [iso.map_label node, occurrenceReading_iso molecule descriptorMap unit iso node]

theorem rule4aObservation_iso (node : left.Node) :
    rule4aObservation molecule descriptorMap unit left node =
      rule4aObservation molecule descriptorMap unit right (iso.toEquiv node) := by
  unfold rule4aObservation
  rw [occurrenceReading_iso molecule descriptorMap unit iso node]

theorem rule4bObservation_iso (node : left.Node) :
    rule4bObservation molecule descriptorMap unit left node =
      rule4bObservation molecule descriptorMap unit right (iso.toEquiv node) := by
  unfold rule4bObservation
  rw [referencePopulation_iso molecule descriptorMap unit iso,
    eligibleSense_iso molecule descriptorMap unit iso node]

theorem rule4cObservation_iso (node : left.Node) :
    rule4cObservation molecule descriptorMap unit left node =
      rule4cObservation molecule descriptorMap unit right (iso.toEquiv node) := by
  unfold rule4cObservation
  rw [occurrenceReading_iso molecule descriptorMap unit iso node]

theorem rule5Observation_iso (node : left.Node) :
    rule5Observation molecule descriptorMap unit left node =
      rule5Observation molecule descriptorMap unit right (iso.toEquiv node) := by
  unfold rule5Observation
  rw [occurrenceReading_iso molecule descriptorMap unit iso node]

/-- **Generated naturality.**  The molecular evidence is preserved by every rooted-digraph
isomorphism. -/
theorem molecularEvidence_preserved :
    RootedDigraph.Addressing.EvidencePreserved iso
      (molecularEvidence molecule descriptorMap unit left)
      (molecularEvidence molecule descriptorMap unit right) := by
  intro node
  simp only [molecularEvidence]
  rw [rule3Observation_iso molecule descriptorMap unit iso node,
    rule4aObservation_iso molecule descriptorMap unit iso node,
    rule4bObservation_iso molecule descriptorMap unit iso node,
    rule4cObservation_iso molecule descriptorMap unit iso node,
    rule5Observation_iso molecule descriptorMap unit iso node]

end Evidence

/-! ## The molecular problem instance -/

section Instance

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]

/-- Replace the supplied evidence field by molecular evidence.  The `evidence_invariant` field is
`molecularEvidence_preserved`. -/
def ConstitutionalProblemData.withMolecularEvidence {molecule : MoleculeGraph Atom}
    (base : ConstitutionalProblemData Atom (DetectedOccurrence molecule)) :
    StereochemicalProblemData Atom (DetectedOccurrence molecule) :=
  { base with
    evidence := molecularEvidence molecule
    evidence_invariant := fun descriptorMap unit _ _ iso =>
      molecularEvidence_preserved molecule descriptorMap unit iso
    hierarchy_compatible := by
      intro _ _ rule _ _ _ _ _ _ _ _ _ _ _
      cases rule <;> trivial }

/-- An ordered ligand frame for every detected occurrence. -/
structure DetectedFrame (molecule : MoleculeGraph Atom) where
  ligand : DetectedOccurrence molecule → Fin 4 → Atom
  adjacent : ∀ unit index, molecule.Adj unit.1.atom (ligand unit index)

/-- A canonical frame: an enumeration of the four neighbours of the occurrence atom. -/
def canonicalDetectedFrame (molecule : MoleculeGraph Atom) : DetectedFrame molecule where
  ligand unit index :=
    ((Finset.equivFinOfCardEq (show (molecule.neighborFinset unit.1.atom).card = 4 from unit.2)).symm
      index).1
  adjacent unit index :=
    (molecule.mem_neighborFinset _ _).1
      ((Finset.equivFinOfCardEq (show (molecule.neighborFinset unit.1.atom).card = 4 from
        unit.2)).symm index).2

/-- The constitutional half on the detected inventory.  Only the Rule-6, dependency, orientation
and later-rule fields of `extra` are retained; the ordinary priority does not read them. -/
def detectedConstitutionalData (molecule : MoleculeGraph Atom) (frame : DetectedFrame molecule)
    (extra : ConstitutionalProblemData Atom (DetectedOccurrence molecule)) :
    ConstitutionalProblemData Atom (DetectedOccurrence molecule) :=
  { extra with
    molecule := molecule
    centerAtom := fun unit => unit.1.atom
    ligandAtom := frame.ligand
    admissibleExpansion := fun unit ligand graph =>
      RootedDigraph.FaithfulExactExpansion molecule unit.1.atom (frame.ligand unit ligand) graph
    expansion_sound := fun _ _ _ h => h.1 }

/-- **The molecular stereochemical instance.** -/
def detectedMolecularData (molecule : MoleculeGraph Atom) (frame : DetectedFrame molecule)
    (extra : ConstitutionalProblemData Atom (DetectedOccurrence molecule)) :
    StereochemicalProblemData Atom (DetectedOccurrence molecule) :=
  (detectedConstitutionalData molecule frame extra).withMolecularEvidence

theorem detectedMolecularData_evidence (molecule : MoleculeGraph Atom)
    (frame : DetectedFrame molecule)
    (extra : ConstitutionalProblemData Atom (DetectedOccurrence molecule)) :
    (detectedMolecularData molecule frame extra).withOrdinaryCanonicalAddressing.evidence =
      molecularEvidence molecule :=
  rfl

theorem detectedMolecularData_expansionsFaithful (molecule : MoleculeGraph Atom)
    (frame : DetectedFrame molecule)
    (extra : ConstitutionalProblemData Atom (DetectedOccurrence molecule)) :
    (detectedMolecularData molecule frame extra).toConstitutionalProblemData.ExpansionsFaithful :=
  fun _ _ _ h => h

/-- A ligand of a detected occurrence is a different atom. -/
theorem DetectedFrame.ligand_ne {molecule : MoleculeGraph Atom} (frame : DetectedFrame molecule)
    (unit : DetectedOccurrence molecule) (index : Fin 4) :
    frame.ligand unit index ≠ unit.1.atom := by
  intro h
  have hadj := frame.adjacent unit index
  rw [h] at hadj
  simp [MoleculeGraph.Adj, molecule.bond_self] at hadj

end Instance

/-! ## First acceptance theorem -/

section Acceptance

variable {atomCount : ℕ} (molecule : MoleculeGraph (Fin atomCount))
  (frame : DetectedFrame molecule)
  (extra : ConstitutionalProblemData (Fin atomCount) (DetectedOccurrence molecule))

/-- Faithful expansions exist for every detected occurrence and ligand. -/
theorem detectedMolecularData_expansion_exists :
    ∀ unit ligand, ∃ graph,
      (detectedMolecularData molecule frame extra).admissibleExpansion unit ligand graph := by
  intro unit ligand
  obtain ⟨_, hfaithful⟩ := MoleculeGraph.semanticOfficialFaithfulExactExpansion_exists molecule
    unit.1.atom (frame.ligand unit ligand) (frame.ligand_ne unit ligand) (frame.adjacent unit ligand)
  exact ⟨_, hfaithful⟩

/-- **First acceptance theorem: the molecular key model.**  The accepted ordinary-rule constructor,
applied to the molecular instance, gives an `OrdinaryRuleKeyModel` with no remaining premise. -/
def detectedMolecularData_ordinaryRuleKeyModel
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule)) :
    OrdinaryRuleKeyModel
      (detectedMolecularData molecule frame extra).withOrdinaryCanonicalAddressing.toProblem
      descriptorMap :=
  (detectedMolecularData molecule frame extra).withOrdinaryCanonicalAddressing_ordinaryRuleKeyModel
    (detectedMolecularData_expansionsFaithful molecule frame extra)
    (detectedMolecularData_expansion_exists molecule frame extra) descriptorMap

/-- **First acceptance theorem: the molecular ordinary total preorder.** -/
theorem detectedMolecularData_ordinaryPriority
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule)) :
    (detectedMolecularData molecule frame extra).withOrdinaryCanonicalAddressing.toProblem
      |>.OrdinaryPriorityIsTotalPreorder descriptorMap :=
  (detectedMolecularData_ordinaryRuleKeyModel molecule frame extra descriptorMap).ordinaryPriorityIsTotalPreorder

/-- On single-bond molecules the instance carries no Rule-3 observation anywhere. -/
theorem detectedMolecularData_rule3_eq_none
    (hsingle : ∀ atom other, molecule.bond atom other ≤ 1)
    (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
    (unit : DetectedOccurrence molecule) (graph : RootedDigraph (Fin atomCount))
    (node : graph.Node) :
    ((detectedMolecularData molecule frame extra).withOrdinaryCanonicalAddressing.evidence
      descriptorMap unit graph node).rule3 = none :=
  molecularEvidence_rule3_eq_none molecule hsingle descriptorMap unit graph node

end Acceptance

/-! ## A source-backed nonconstant example

An 11-atom single-bonded skeleton C0(a, b, c, C1), C1(x, y, C2), C2(p, q, r) with three detected
centers.  The fixed map assigns `R` to C1 and `S` to C2, both in the hierarchy of C0.  In the branch
of ligand C1, C1 is the unique nearest reference, C2 is a deeper eligible occurrence, and
non-centers carry plain observations.  The branch of ligand `a` has an empty reference population.
Every value below is computed by `molecularEvidence`; no signature array is supplied.
-/

namespace MolecularEvidenceExample

/-- Single-bond skeleton: C0(a,b,c,C1), C1(x,y,C2), C2(p,q,r). -/
def bonds : List (ℕ × ℕ) :=
  [(0, 1), (0, 2), (0, 3), (0, 4), (4, 5), (4, 6), (4, 7), (7, 8), (7, 9), (7, 10)]

def molecule : MoleculeGraph (Fin 11) where
  atomZ _ := 6
  bond a b := if (a.val, b.val) ∈ bonds ∨ (b.val, a.val) ∈ bonds then 1 else 0
  bond_symm := by decide
  bond_self := by decide

theorem singleBonded : ∀ atom other, molecule.bond atom other ≤ 1 := by decide

theorem center0 : IsDetectedCenter molecule 0 := by decide
theorem notCenter1 : ¬ IsDetectedCenter molecule 1 := by decide

/-- The top occurrence of the root stereocenter C0. -/
def top : DetectedOccurrence molecule := ⟨⟨0, []⟩, center0⟩

/-- A fixed descriptor map on occurrences: C1 is `R` and C2 is `S` in the hierarchy of C0. -/
def descriptors : DescriptorMap (DetectedOccurrence molecule) := fun unit =>
  if unit.1 = ⟨0, [4]⟩ then some .R else if unit.1 = ⟨0, [4, 7]⟩ then some .S else none

/-! ### The branch of ligand C1 -/

def branchAtom (node : Fin 7) : Fin 11 := [4, 5, 6, 7, 8, 9, 10].getD node.val 0
def branchParent (node : Fin 7) : Option (Fin 7) :=
  [none, some 0, some 0, some 0, some 3, some 3, some 3].getD node.val none
def branchDepth (node : Fin 7) : ℕ := [0, 1, 1, 1, 2, 2, 2].getD node.val 0

theorem branch_reachable (node : Fin 7) :
    Relation.ReflTransGen (fun parent node => branchParent node = some parent) 0 node := by
  fin_cases node
  all_goals first
    | exact Relation.ReflTransGen.refl
    | exact Relation.ReflTransGen.single (by decide)
    | exact Relation.ReflTransGen.tail (Relation.ReflTransGen.single (b := (3 : Fin 7)) (by decide))
        (by decide)

def branch : RootedDigraph (Fin 11) where
  Node := Fin 7
  nodeFintype := inferInstance
  root := 0
  child parent node := branchParent node = some parent
  label node := ⟨some (branchAtom node), .realAtom⟩
  depth := branchDepth
  root_depth := rfl
  child_depth := by
    intro parent node h
    have key : ∀ parent node : Fin 7, branchParent node = some parent →
        branchDepth node = branchDepth parent + 1 := by decide
    exact key parent node h
  reachable := branch_reachable

theorem branch_atoms : ∀ node : Fin 7,
    ancestorAtoms branch node = some (([[4], [4, 5], [4, 6], [4, 7], [4, 7, 8], [4, 7, 9],
      [4, 7, 10]] : List (List (Fin 11))).getD node.val []) := by
  have noParent : ∀ parent, ¬ branch.child parent branch.root := by
    intro parent h
    exact (by decide : ∀ parent : Fin 7, branchParent 0 ≠ some parent) parent h
  have parentUnique : ∀ {first second node}, branch.child first node → branch.child second node →
      first = second := fun hfirst hsecond => Option.some_injective _ (hfirst.symm.trans hsecond)
  have atoms : ∀ {node : branch.Node} {path}, AncestorPath branch node path →
      ancestorAtoms branch node = path.mapM id := by
    intro node path h
    rw [ancestorAtoms, ancestorPath_eq_some h fun _ hother =>
      ancestorPath_unique_of_parent_unique noParent parentUnique hother h]
    rfl
  have p0 : AncestorPath branch (0 : Fin 7) _ := AncestorPath.root
  have p3 : AncestorPath branch (3 : Fin 7) _ :=
    AncestorPath.step (show branch.child (0 : Fin 7) (3 : Fin 7) from rfl) p0
  intro node
  fin_cases node
  · exact (atoms p0).trans rfl
  · exact (atoms (AncestorPath.step (show branch.child (0 : Fin 7) (1 : Fin 7) from rfl) p0)).trans rfl
  · exact (atoms (AncestorPath.step (show branch.child (0 : Fin 7) (2 : Fin 7) from rfl) p0)).trans rfl
  · exact (atoms p3).trans rfl
  · exact (atoms (AncestorPath.step (show branch.child (3 : Fin 7) (4 : Fin 7) from rfl) p3)).trans rfl
  · exact (atoms (AncestorPath.step (show branch.child (3 : Fin 7) (5 : Fin 7) from rfl) p3)).trans rfl
  · exact (atoms (AncestorPath.step (show branch.child (3 : Fin 7) (6 : Fin 7) from rfl) p3)).trans rfl

theorem branch_reading : ∀ node : Fin 7,
    occurrenceReading molecule descriptors top branch node =
      ([.descriptor .R, .outsideInventory, .outsideInventory, .descriptor .S, .outsideInventory,
        .outsideInventory, .outsideInventory] : List OccurrenceReading).getD node.val .unavailable := by
  intro node
  rw [occurrenceReading_eq_readContext molecule descriptors top branch rfl (branch_atoms node)]
  revert node
  decide

theorem branch_eligibleSense : ∀ node : Fin 7,
    eligibleSense molecule descriptors top branch node =
      ([some .senior, none, none, some .junior, none, none, none] :
        List (Option DescriptorSense)).getD node.val none := by
  intro node
  unfold eligibleSense
  rw [branch_reading node]
  revert node
  decide

/-- C1 is the unique nearest eligible occurrence; its `R` descriptor is the reference. -/
theorem branch_referencePopulation :
    referencePopulation molecule descriptors top branch = .unique .senior := by
  have hsense : eligibleSense molecule descriptors top branch (0 : Fin 7) = some .senior :=
    branch_eligibleSense 0
  have heligible : Eligible molecule descriptors top branch (0 : Fin 7) := by
    unfold Eligible
    rw [hsense]
    rfl
  have hnearest : NearestEligible molecule descriptors top branch (0 : Fin 7) :=
    ⟨heligible, fun _ _ => Nat.zero_le _⟩
  rw [referencePopulation_eq_unique molecule descriptors top branch hnearest fun other hother =>
    (by decide : ∀ node : Fin 7, branchDepth node ≤ 0 → node = 0) other (hother.2 _ heligible)]
  exact congrArg ReferencePopulation.unique (Option.get_of_mem _ hsense)

theorem branch_rule3 (node : Fin 7) : rule3Observation molecule descriptors top branch node = none :=
  molecularEvidence_rule3_eq_none molecule singleBonded descriptors top branch node

/-- The reference C1 itself: chiral, like-paired with itself, senior sense. -/
theorem branch_evidence_reference :
    molecularEvidence molecule descriptors top branch (0 : Fin 7) =
      ⟨none, some ⟨singleEntry .chiral⟩, some ⟨[[1]]⟩, some ⟨singleEntry 0⟩,
        some ⟨singleEntry 2⟩⟩ := by
  simp only [molecularEvidence, branch_rule3, rule4aObservation, rule4bObservation,
    rule4cObservation, rule5Observation, branch_reading, branch_eligibleSense,
    branch_referencePopulation]
  rfl

/-- The deeper center C2: chiral, unlike-paired with the reference, junior sense. -/
theorem branch_evidence_deeper :
    molecularEvidence molecule descriptors top branch (3 : Fin 7) =
      ⟨none, some ⟨singleEntry .chiral⟩, some ⟨[[0]]⟩, some ⟨singleEntry 0⟩,
        some ⟨singleEntry 1⟩⟩ := by
  simp only [molecularEvidence, branch_rule3, rule4aObservation, rule4bObservation,
    rule4cObservation, rule5Observation, branch_reading, branch_eligibleSense,
    branch_referencePopulation]
  rfl

/-- A non-center atom of the same branch: nonstereogenic, no Rule-4b pairing. -/
theorem branch_evidence_plain :
    molecularEvidence molecule descriptors top branch (1 : Fin 7) =
      ⟨none, some ⟨singleEntry .nonstereogenic⟩, none, some ⟨singleEntry 0⟩,
        some ⟨singleEntry 0⟩⟩ := by
  simp only [molecularEvidence, branch_rule3, rule4aObservation, rule4bObservation,
    rule4cObservation, rule5Observation, branch_reading, branch_eligibleSense,
    branch_referencePopulation]
  rfl

/-! ### The branch of ligand `a`: an empty reference population -/

def leaf : RootedDigraph (Fin 11) where
  Node := Fin 1
  nodeFintype := inferInstance
  root := 0
  child _ _ := False
  label _ := ⟨some 1, .realAtom⟩
  depth _ := 0
  root_depth := rfl
  child_depth := fun h => h.elim
  reachable node := by
    rw [Subsingleton.elim node (0 : Fin 1)]

theorem leaf_reading (node : Fin 1) :
    occurrenceReading molecule descriptors top leaf node = .outsideInventory := by
  rw [Subsingleton.elim node (0 : Fin 1)]
  have hatoms : ancestorAtoms leaf (0 : Fin 1) = some [1] := by
    have hroot : AncestorPath leaf (0 : Fin 1) [some 1] := AncestorPath.root (graph := leaf)
    rw [ancestorAtoms, ancestorPath_eq_some hroot fun _ hother =>
      ancestorPath_unique_of_parent_unique (graph := leaf) (fun _ h => False.elim h)
        (fun h _ => False.elim h) hother hroot]
    rfl
  rw [occurrenceReading_eq_readContext molecule descriptors top leaf rfl hatoms]
  decide

theorem leaf_referencePopulation :
    referencePopulation molecule descriptors top leaf = .empty := by
  refine referencePopulation_eq_empty molecule descriptors top leaf fun node h => ?_
  unfold Eligible eligibleSense at h
  rw [leaf_reading] at h
  exact absurd h (by decide)

theorem leaf_evidence (node : Fin 1) :
    molecularEvidence molecule descriptors top leaf node =
      ⟨none, some ⟨singleEntry .nonstereogenic⟩, none, some ⟨singleEntry 0⟩,
        some ⟨singleEntry 0⟩⟩ := by
  have h3 : rule3Observation molecule descriptors top leaf node = none :=
    molecularEvidence_rule3_eq_none molecule singleBonded descriptors top leaf node
  simp only [molecularEvidence, h3, rule4aObservation, rule4bObservation, rule4cObservation,
    rule5Observation, eligibleSense, leaf_reading, leaf_referencePopulation]

end MolecularEvidenceExample

end
end DeclarativeCIP
end OneCenter
end TetraStereo

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ancestorPath_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.referencePopulation_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.molecularEvidence_preserved
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ConstitutionalProblemData.withMolecularEvidence
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.detectedMolecularData_expansion_exists
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.detectedMolecularData_ordinaryRuleKeyModel
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.detectedMolecularData_ordinaryPriority
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.detectedMolecularData_rule3_eq_none
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.MolecularEvidenceExample.branch_referencePopulation
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.MolecularEvidenceExample.branch_evidence_reference
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.MolecularEvidenceExample.branch_evidence_deeper
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.MolecularEvidenceExample.branch_evidence_plain
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.MolecularEvidenceExample.leaf_referencePopulation
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.MolecularEvidenceExample.leaf_evidence
