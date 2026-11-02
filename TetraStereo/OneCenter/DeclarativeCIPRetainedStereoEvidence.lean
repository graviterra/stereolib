import TetraStereo.OneCenter.DeclarativeCIPMolecularEvidenceNaturality
import TetraStereo.OneCenter.DeclarativeCIPMolecularReferenceSelection
import TetraStereo.OneCenter.DeclarativeCIPRankKeyProjection
import TetraStereo.OneCenter.DeclarativeCIPRule4cReadingEvidence
import TetraStereo.KernelOnly

set_option autoImplicit false

/-! Neutral stereochemical evidence for constitutionally present ring-duplicate nodes.

A ring-duplicate node is an address in the retained hierarchy. It is not a stereogenic unit.
Its Rule-4a observation is therefore the present nonstereogenic code, and its Rule-4c and Rule-5
observations are the present numeric zero. Those are the same present codes already used for a
real node with no descriptor (`outsideInventory` / `unassigned`). They are not the absence code
`⊥`, which means the address is off the hierarchy.

Neutralization reads ring-duplicate provenance only. It does not read atomic number, isotopic
mass, stored duplicate distance, or a production priority table. A real node keeps the ordinary
molecular observation, including a genuine `.unavailable` reading: missing real data stays
absent and is not rewritten as nonstereogenic.

Stage masks match the accepted evidence. `retainedRankEvidence` and `retainedReadingEvidence`
keep Rule 4c and Rule 5 masked. Only `retainedReadingEvidence4c` and
`retainedNoReferenceEvidence4c` expose the neutral Rule-4c column. Rule 5 stays a node
observation here so a later stage can opt into it; no stage evidence in this file turns Rule 5
on. Multiple-bond, phantom, lone-pair, and auxiliary provenances are not neutralized.
-/

namespace TetraStereo.OneCenter.DeclarativeCIP
noncomputable section
open scoped Classical
universe u

/-- Ring-closure duplicate provenance. Every stored duplicate distance is included. -/
def NodeProvenance.isRingDuplicate : NodeProvenance → Bool
  | .ringDuplicate _ => true
  | .realAtom => false
  | .multipleBondDuplicate _ => false
  | .phantom _ => false
  | .lonePair _ => false
  | .auxiliary _ => false

theorem NodeProvenance.isRingDuplicate_iff (provenance : NodeProvenance) :
    provenance.isRingDuplicate = true ↔ ∃ distance, provenance = .ringDuplicate distance := by
  cases provenance <;> simp [NodeProvenance.isRingDuplicate]

/-- Replace the kept observation by a present value exactly on ring-duplicate provenance. -/
def neutralizeRingDuplicate {α : Type} (provenance : NodeProvenance) (present : α)
    (kept : Option α) : Option α :=
  match provenance with
  | .ringDuplicate _ => some present
  | .realAtom => kept
  | .multipleBondDuplicate _ => kept
  | .phantom _ => kept
  | .lonePair _ => kept
  | .auxiliary _ => kept

section Observations

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

/-- Rule 4a at a retained address. Ring duplicates are present nonstereogenic units.
Real and other provenances keep `rule4aObservation`, so a real `.unavailable` reading stays
absent. -/
def retainedRule4aObservation (node : graph.Node) : Option Rule4aSignature :=
  neutralizeRingDuplicate (graph.label node).provenance ⟨singleEntry .nonstereogenic⟩
    (rule4aObservation molecule descriptorMap unit graph node)

/-- Rule 4c at a retained address. Ring duplicates carry present zero. -/
def retainedRule4cObservation (node : graph.Node) : Option Rule4cSignature :=
  neutralizeRingDuplicate (graph.label node).provenance ⟨singleEntry 0⟩
    (rule4cObservation molecule descriptorMap unit graph node)

/-- Rule 5 at a retained address. Ring duplicates carry present zero. This observation is not
installed in the Rule-4a, Rule-4b, or Rule-4c stage evidence below. -/
def retainedRule5Observation (node : graph.Node) : Option Rule5Signature :=
  neutralizeRingDuplicate (graph.label node).provenance ⟨singleEntry 0⟩
    (rule5Observation molecule descriptorMap unit graph node)

theorem occurrenceReading_of_ringDuplicate (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    occurrenceReading molecule descriptorMap unit graph node = .unavailable := by
  unfold occurrenceReading
  rw [duplicate]

theorem retainedRule4aObservation_ringDuplicate (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    retainedRule4aObservation molecule descriptorMap unit graph node =
      some ⟨singleEntry .nonstereogenic⟩ := by
  simp [retainedRule4aObservation, neutralizeRingDuplicate, duplicate]

theorem retainedRule4cObservation_ringDuplicate (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    retainedRule4cObservation molecule descriptorMap unit graph node =
      some ⟨singleEntry 0⟩ := by
  simp [retainedRule4cObservation, neutralizeRingDuplicate, duplicate]

theorem retainedRule5Observation_ringDuplicate (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    retainedRule5Observation molecule descriptorMap unit graph node =
      some ⟨singleEntry 0⟩ := by
  simp [retainedRule5Observation, neutralizeRingDuplicate, duplicate]

theorem retainedRule4aObservation_of_not_ringDuplicate (node : graph.Node)
    (notDuplicate : ∀ distance, (graph.label node).provenance ≠ .ringDuplicate distance) :
    retainedRule4aObservation molecule descriptorMap unit graph node =
      rule4aObservation molecule descriptorMap unit graph node := by
  unfold retainedRule4aObservation neutralizeRingDuplicate
  cases provenanceEq : (graph.label node).provenance with
  | ringDuplicate distance => exact (notDuplicate distance provenanceEq).elim
  | realAtom => rfl
  | multipleBondDuplicate _ => rfl
  | phantom _ => rfl
  | lonePair _ => rfl
  | auxiliary _ => rfl

theorem retainedRule4cObservation_of_not_ringDuplicate (node : graph.Node)
    (notDuplicate : ∀ distance, (graph.label node).provenance ≠ .ringDuplicate distance) :
    retainedRule4cObservation molecule descriptorMap unit graph node =
      rule4cObservation molecule descriptorMap unit graph node := by
  unfold retainedRule4cObservation neutralizeRingDuplicate
  cases provenanceEq : (graph.label node).provenance with
  | ringDuplicate distance => exact (notDuplicate distance provenanceEq).elim
  | realAtom => rfl
  | multipleBondDuplicate _ => rfl
  | phantom _ => rfl
  | lonePair _ => rfl
  | auxiliary _ => rfl

theorem retainedRule5Observation_of_not_ringDuplicate (node : graph.Node)
    (notDuplicate : ∀ distance, (graph.label node).provenance ≠ .ringDuplicate distance) :
    retainedRule5Observation molecule descriptorMap unit graph node =
      rule5Observation molecule descriptorMap unit graph node := by
  unfold retainedRule5Observation neutralizeRingDuplicate
  cases provenanceEq : (graph.label node).provenance with
  | ringDuplicate distance => exact (notDuplicate distance provenanceEq).elim
  | realAtom => rfl
  | multipleBondDuplicate _ => rfl
  | phantom _ => rfl
  | lonePair _ => rfl
  | auxiliary _ => rfl

omit [Fintype Atom] [DecidableEq Atom] in
theorem not_ringDuplicate_of_realAtom (node : graph.Node)
    (real : (graph.label node).provenance = .realAtom) :
    ∀ distance, (graph.label node).provenance ≠ .ringDuplicate distance := by
  intro distance duplicate
  rw [real] at duplicate
  cases duplicate

/-- A real node whose occurrence reading is unavailable stays an absent Rule-4a observation. -/
theorem retainedRule4aObservation_real_unavailable (node : graph.Node)
    (real : (graph.label node).provenance = .realAtom)
    (unavailable : occurrenceReading molecule descriptorMap unit graph node = .unavailable) :
    retainedRule4aObservation molecule descriptorMap unit graph node = none := by
  rw [retainedRule4aObservation_of_not_ringDuplicate molecule descriptorMap unit graph node
    (not_ringDuplicate_of_realAtom graph node real)]
  simp [rule4aObservation, unavailable]

theorem retainedRule4cObservation_real_unavailable (node : graph.Node)
    (real : (graph.label node).provenance = .realAtom)
    (unavailable : occurrenceReading molecule descriptorMap unit graph node = .unavailable) :
    retainedRule4cObservation molecule descriptorMap unit graph node = none := by
  rw [retainedRule4cObservation_of_not_ringDuplicate molecule descriptorMap unit graph node
    (not_ringDuplicate_of_realAtom graph node real)]
  simp [rule4cObservation, unavailable]

theorem retainedRule5Observation_real_unavailable (node : graph.Node)
    (real : (graph.label node).provenance = .realAtom)
    (unavailable : occurrenceReading molecule descriptorMap unit graph node = .unavailable) :
    retainedRule5Observation molecule descriptorMap unit graph node = none := by
  rw [retainedRule5Observation_of_not_ringDuplicate molecule descriptorMap unit graph node
    (not_ringDuplicate_of_realAtom graph node real)]
  simp [rule5Observation, unavailable]

end Observations

section Evidence

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule) (graph : RootedDigraph Atom)

/-- Pre-Rule-4b retained evidence. Rule 4c and Rule 5 stay masked, as in `rankEvidence`. -/
def retainedRankEvidence : StereochemicalEvidence graph := fun node =>
  { rule3 := rule3Observation molecule descriptorMap unit graph node
    rule4a := retainedRule4aObservation molecule descriptorMap unit graph node
    rule4b := none
    rule4c := none
    rule5 := none }

/-- One-reference retained evidence. The Rule-4b column is the ordinary eligible-sense pairing.
Ring duplicates are not eligible, so that column stays empty there. Rule 4c and Rule 5 stay
masked, as in `readingEvidence`. -/
def retainedReadingEvidence (reference : DescriptorSense) : StereochemicalEvidence graph :=
  fun node =>
    { rule3 := rule3Observation molecule descriptorMap unit graph node
      rule4a := retainedRule4aObservation molecule descriptorMap unit graph node
      rule4b := (eligibleSense molecule descriptorMap unit graph node).map fun observed =>
        ⟨[[(DescriptorPairKind.ofSenses reference observed).priority]]⟩
      rule4c := none
      rule5 := none }

/-- Per-reference Rule-4c evidence. This is the first stage that exposes neutral Rule 4c.
Rule 5 remains masked. -/
def retainedReadingEvidence4c (reference : DescriptorSense) : StereochemicalEvidence graph :=
  fun node =>
    { (retainedReadingEvidence molecule descriptorMap unit graph reference node) with
      rule4c := retainedRule4cObservation molecule descriptorMap unit graph node
      rule5 := none }

/-- Empty-reference Rule-4c evidence. Rule 4b stays absent with the rank mask, and Rule 5 stays
masked. -/
def retainedNoReferenceEvidence4c : StereochemicalEvidence graph := fun node =>
  { (retainedRankEvidence molecule descriptorMap unit graph node) with
    rule4c := retainedRule4cObservation molecule descriptorMap unit graph node
    rule5 := none }

@[simp] theorem retainedRankEvidence_rule4b (node : graph.Node) :
    (retainedRankEvidence molecule descriptorMap unit graph node).rule4b = none := rfl

@[simp] theorem retainedRankEvidence_rule4c (node : graph.Node) :
    (retainedRankEvidence molecule descriptorMap unit graph node).rule4c = none := rfl

@[simp] theorem retainedRankEvidence_rule5 (node : graph.Node) :
    (retainedRankEvidence molecule descriptorMap unit graph node).rule5 = none := rfl

@[simp] theorem retainedReadingEvidence_rule4c (reference : DescriptorSense) (node : graph.Node) :
    (retainedReadingEvidence molecule descriptorMap unit graph reference node).rule4c = none := rfl

@[simp] theorem retainedReadingEvidence_rule5 (reference : DescriptorSense) (node : graph.Node) :
    (retainedReadingEvidence molecule descriptorMap unit graph reference node).rule5 = none := rfl

@[simp] theorem retainedReadingEvidence4c_rule5 (reference : DescriptorSense) (node : graph.Node) :
    (retainedReadingEvidence4c molecule descriptorMap unit graph reference node).rule5 = none := rfl

@[simp] theorem retainedNoReferenceEvidence4c_rule4b (node : graph.Node) :
    (retainedNoReferenceEvidence4c molecule descriptorMap unit graph node).rule4b = none := rfl

@[simp] theorem retainedNoReferenceEvidence4c_rule5 (node : graph.Node) :
    (retainedNoReferenceEvidence4c molecule descriptorMap unit graph node).rule5 = none := rfl

theorem retainedRankEvidence_eq_rankEvidence_of_not_ringDuplicate (node : graph.Node)
    (notDuplicate : ∀ distance, (graph.label node).provenance ≠ .ringDuplicate distance) :
    retainedRankEvidence molecule descriptorMap unit graph node =
      rankEvidence molecule descriptorMap unit graph node := by
  simp [retainedRankEvidence, rankEvidence,
    retainedRule4aObservation_of_not_ringDuplicate molecule descriptorMap unit graph node
      notDuplicate]

theorem retainedReadingEvidence_eq_readingEvidence_of_not_ringDuplicate
    (reference : DescriptorSense) (node : graph.Node)
    (notDuplicate : ∀ distance, (graph.label node).provenance ≠ .ringDuplicate distance) :
    retainedReadingEvidence molecule descriptorMap unit graph reference node =
      readingEvidence molecule descriptorMap unit graph reference node := by
  simp [retainedReadingEvidence, readingEvidence,
    retainedRule4aObservation_of_not_ringDuplicate molecule descriptorMap unit graph node
      notDuplicate]

theorem retainedReadingEvidence4c_eq_readingEvidence4c_of_not_ringDuplicate
    (reference : DescriptorSense) (node : graph.Node)
    (notDuplicate : ∀ distance, (graph.label node).provenance ≠ .ringDuplicate distance) :
    retainedReadingEvidence4c molecule descriptorMap unit graph reference node =
      readingEvidence4c molecule descriptorMap unit graph reference node := by
  simp [retainedReadingEvidence4c, readingEvidence4c, retainedReadingEvidence, readingEvidence,
    retainedRule4aObservation_of_not_ringDuplicate molecule descriptorMap unit graph node
      notDuplicate,
    retainedRule4cObservation_of_not_ringDuplicate molecule descriptorMap unit graph node
      notDuplicate]

theorem retainedNoReferenceEvidence4c_eq_noReferenceEvidence4c_of_not_ringDuplicate
    (node : graph.Node)
    (notDuplicate : ∀ distance, (graph.label node).provenance ≠ .ringDuplicate distance) :
    retainedNoReferenceEvidence4c molecule descriptorMap unit graph node =
      noReferenceEvidence4c molecule descriptorMap unit graph node := by
  simp [retainedNoReferenceEvidence4c, noReferenceEvidence4c, retainedRankEvidence, rankEvidence,
    retainedRule4aObservation_of_not_ringDuplicate molecule descriptorMap unit graph node
      notDuplicate,
    retainedRule4cObservation_of_not_ringDuplicate molecule descriptorMap unit graph node
      notDuplicate]

/-- Present nonstereogenic Rule 4a at a ring duplicate, on the rank-stage evidence. -/
theorem stereoLabel_retainedRankEvidence_rule4a_ringDuplicate (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    stereoLabel graph (retainedRankEvidence molecule descriptorMap unit graph)
        .rule4aStereogenicUnitKind node =
      ((encodeHierarchy StereogenicUnitKind.priority (singleEntry .nonstereogenic) :
        StereoCode) : StereoLabel) := by
  unfold stereoLabel stereoValue retainedRankEvidence
  rw [retainedRule4aObservation_ringDuplicate molecule descriptorMap unit graph node distance
    duplicate]
  rfl

/-- Real unavailable data remains `⊥` under the retained Rule-4a column. -/
theorem stereoLabel_retainedRankEvidence_rule4a_real_unavailable (node : graph.Node)
    (real : (graph.label node).provenance = .realAtom)
    (unavailable : occurrenceReading molecule descriptorMap unit graph node = .unavailable) :
    stereoLabel graph (retainedRankEvidence molecule descriptorMap unit graph)
        .rule4aStereogenicUnitKind node = ⊥ := by
  have observed := retainedRule4aObservation_real_unavailable molecule descriptorMap unit graph
    node real unavailable
  unfold stereoLabel stereoValue retainedRankEvidence
  rw [observed]
  rfl

theorem stereoLabel_retainedReadingEvidence_rule4b_ringDuplicate (reference : DescriptorSense)
    (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    stereoLabel graph (retainedReadingEvidence molecule descriptorMap unit graph reference)
        .rule4bLikeUnlikeDescriptorPairs node = ⊥ := by
  have unavailable := occurrenceReading_of_ringDuplicate molecule descriptorMap unit graph node
    distance duplicate
  unfold stereoLabel stereoValue retainedReadingEvidence eligibleSense
  rw [unavailable]
  rfl

theorem stereoLabel_retainedReadingEvidence4c_rule4b_ringDuplicate (reference : DescriptorSense)
    (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    stereoLabel graph (retainedReadingEvidence4c molecule descriptorMap unit graph reference)
        .rule4bLikeUnlikeDescriptorPairs node = ⊥ := by
  have unavailable := occurrenceReading_of_ringDuplicate molecule descriptorMap unit graph node
    distance duplicate
  unfold stereoLabel stereoValue retainedReadingEvidence4c retainedReadingEvidence eligibleSense
  rw [unavailable]
  rfl

/-- Present zero Rule 4c at a ring duplicate. Successor bridges rewrite this with `code 0`. -/
theorem stereoLabel_retainedReadingEvidence4c_rule4c_ringDuplicate (reference : DescriptorSense)
    (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    stereoLabel graph (retainedReadingEvidence4c molecule descriptorMap unit graph reference)
        .rule4cPseudoasymmetricDescriptor node =
      ((encodeHierarchy id (singleEntry 0) : StereoCode) : StereoLabel) := by
  unfold stereoLabel stereoValue retainedReadingEvidence4c
  rw [retainedRule4cObservation_ringDuplicate molecule descriptorMap unit graph node distance
    duplicate]
  rfl

theorem stereoLabel_retainedNoReferenceEvidence4c_rule4c_ringDuplicate (node : graph.Node)
    (distance : ℕ) (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    stereoLabel graph (retainedNoReferenceEvidence4c molecule descriptorMap unit graph)
        .rule4cPseudoasymmetricDescriptor node =
      ((encodeHierarchy id (singleEntry 0) : StereoCode) : StereoLabel) := by
  unfold stereoLabel stereoValue retainedNoReferenceEvidence4c retainedRankEvidence
  rw [retainedRule4cObservation_ringDuplicate molecule descriptorMap unit graph node distance
    duplicate]
  rfl

/-- Present zero Rule 5 at a ring duplicate, as a masked node observation. -/
theorem liftObservation_retainedRule5_ringDuplicate (node : graph.Node) (distance : ℕ)
    (duplicate : (graph.label node).provenance = .ringDuplicate distance) :
    liftObservation (fun signature : Rule5Signature => encodeHierarchy id signature.layers)
        (retainedRule5Observation molecule descriptorMap unit graph node) =
      ((encodeHierarchy id (singleEntry 0) : StereoCode) : StereoLabel) := by
  rw [retainedRule5Observation_ringDuplicate molecule descriptorMap unit graph node distance
    duplicate]
  rfl

private theorem bond_le_one_of_simpleBonded (singleBonded : molecule.SimpleBonded) :
    ∀ atom other, molecule.bond atom other ≤ 1 := by
  intro atom other
  rcases Nat.eq_zero_or_pos (molecule.bond atom other) with zero | positive
  · rw [zero]
    exact Nat.zero_le 1
  · exact le_of_eq (singleBonded atom other positive)

theorem rule4aOnly_retainedRankEvidence_of_simpleBonded (singleBonded : molecule.SimpleBonded) :
    Rule4aOnly graph (retainedRankEvidence molecule descriptorMap unit graph) := by
  intro rule not4a node
  have single := bond_le_one_of_simpleBonded molecule singleBonded
  cases rule with
  | rule4aStereogenicUnitKind => exact (not4a rfl).elim
  | rule3DoubleBondGeometry =>
      have absent := molecularEvidence_rule3_eq_none molecule single descriptorMap unit graph node
      change rule3Observation molecule descriptorMap unit graph node = none at absent
      show stereoValue .rule3DoubleBondGeometry
        (some (retainedRankEvidence molecule descriptorMap unit graph node)) = ⊥
      simp [stereoValue, retainedRankEvidence, absent, liftObservation]
  | rule4bLikeUnlikeDescriptorPairs =>
      show stereoValue .rule4bLikeUnlikeDescriptorPairs
        (some (retainedRankEvidence molecule descriptorMap unit graph node)) = ⊥
      simp [stereoValue, retainedRankEvidence, liftObservation]
  | rule4cPseudoasymmetricDescriptor =>
      show stereoValue .rule4cPseudoasymmetricDescriptor
        (some (retainedRankEvidence molecule descriptorMap unit graph node)) = ⊥
      simp [stereoValue, retainedRankEvidence, liftObservation]
  | rule5EnantiomorphicDescriptor =>
      show stereoValue .rule5EnantiomorphicDescriptor
        (some (retainedRankEvidence molecule descriptorMap unit graph node)) = ⊥
      simp [stereoValue, retainedRankEvidence, liftObservation]

theorem rule4abcOnly_retainedReadingEvidence4c_of_simpleBonded
    (singleBonded : molecule.SimpleBonded) (reference : DescriptorSense) :
    Rule4abcOnly graph
      (retainedReadingEvidence4c molecule descriptorMap unit graph reference) := by
  intro rule not4a not4b not4c node
  have single := bond_le_one_of_simpleBonded molecule singleBonded
  cases rule with
  | rule3DoubleBondGeometry =>
      have absent := molecularEvidence_rule3_eq_none molecule single descriptorMap unit graph node
      change rule3Observation molecule descriptorMap unit graph node = none at absent
      show stereoValue .rule3DoubleBondGeometry
        (some (retainedReadingEvidence4c molecule descriptorMap unit graph reference node)) = ⊥
      simp [stereoValue, retainedReadingEvidence4c, retainedReadingEvidence, absent, liftObservation]
  | rule4aStereogenicUnitKind => exact (not4a rfl).elim
  | rule4bLikeUnlikeDescriptorPairs => exact (not4b rfl).elim
  | rule4cPseudoasymmetricDescriptor => exact (not4c rfl).elim
  | rule5EnantiomorphicDescriptor =>
      show stereoValue .rule5EnantiomorphicDescriptor
        (some (retainedReadingEvidence4c molecule descriptorMap unit graph reference node)) = ⊥
      simp [stereoValue, retainedReadingEvidence4c, liftObservation]

theorem rule4acOnly_retainedNoReferenceEvidence4c_of_simpleBonded
    (singleBonded : molecule.SimpleBonded) :
    Rule4acOnly graph (retainedNoReferenceEvidence4c molecule descriptorMap unit graph) := by
  intro rule not4a not4c node
  have single := bond_le_one_of_simpleBonded molecule singleBonded
  cases rule with
  | rule3DoubleBondGeometry =>
      have absent := molecularEvidence_rule3_eq_none molecule single descriptorMap unit graph node
      change rule3Observation molecule descriptorMap unit graph node = none at absent
      show stereoValue .rule3DoubleBondGeometry
        (some (retainedNoReferenceEvidence4c molecule descriptorMap unit graph node)) = ⊥
      simp [stereoValue, retainedNoReferenceEvidence4c, retainedRankEvidence, absent, liftObservation]
  | rule4aStereogenicUnitKind => exact (not4a rfl).elim
  | rule4bLikeUnlikeDescriptorPairs =>
      show stereoValue .rule4bLikeUnlikeDescriptorPairs
        (some (retainedNoReferenceEvidence4c molecule descriptorMap unit graph node)) = ⊥
      simp [stereoValue, retainedNoReferenceEvidence4c, retainedRankEvidence, liftObservation]
  | rule4cPseudoasymmetricDescriptor => exact (not4c rfl).elim
  | rule5EnantiomorphicDescriptor =>
      show stereoValue .rule5EnantiomorphicDescriptor
        (some (retainedNoReferenceEvidence4c molecule descriptorMap unit graph node)) = ⊥
      simp [stereoValue, retainedNoReferenceEvidence4c, liftObservation]

end Evidence

section Transport

variable {Atom : Type u} [Fintype Atom] [DecidableEq Atom]
  (molecule : MoleculeGraph Atom)
  (descriptorMap : DescriptorMap (DetectedOccurrence molecule))
  (unit : DetectedOccurrence molecule)
  {left right : RootedDigraph Atom} (iso : RootedDigraph.Iso left right)

omit [Fintype Atom] [DecidableEq Atom] in
theorem ringDuplicate_provenance_iso (node : left.Node) (distance : ℕ)
    (duplicate : (left.label node).provenance = .ringDuplicate distance) :
    (right.label (iso.toEquiv node)).provenance = .ringDuplicate distance := by
  rw [← iso.map_label node]
  exact duplicate

theorem retainedRule4aObservation_iso (node : left.Node) :
    retainedRule4aObservation molecule descriptorMap unit left node =
      retainedRule4aObservation molecule descriptorMap unit right (iso.toEquiv node) := by
  unfold retainedRule4aObservation neutralizeRingDuplicate
  rw [iso.map_label node]
  cases (right.label (iso.toEquiv node)).provenance with
  | ringDuplicate _ => rfl
  | realAtom => exact rule4aObservation_iso molecule descriptorMap unit iso node
  | multipleBondDuplicate _ => exact rule4aObservation_iso molecule descriptorMap unit iso node
  | phantom _ => exact rule4aObservation_iso molecule descriptorMap unit iso node
  | lonePair _ => exact rule4aObservation_iso molecule descriptorMap unit iso node
  | auxiliary _ => exact rule4aObservation_iso molecule descriptorMap unit iso node

theorem retainedRule4cObservation_iso (node : left.Node) :
    retainedRule4cObservation molecule descriptorMap unit left node =
      retainedRule4cObservation molecule descriptorMap unit right (iso.toEquiv node) := by
  unfold retainedRule4cObservation neutralizeRingDuplicate
  rw [iso.map_label node]
  cases (right.label (iso.toEquiv node)).provenance with
  | ringDuplicate _ => rfl
  | realAtom => exact rule4cObservation_iso molecule descriptorMap unit iso node
  | multipleBondDuplicate _ => exact rule4cObservation_iso molecule descriptorMap unit iso node
  | phantom _ => exact rule4cObservation_iso molecule descriptorMap unit iso node
  | lonePair _ => exact rule4cObservation_iso molecule descriptorMap unit iso node
  | auxiliary _ => exact rule4cObservation_iso molecule descriptorMap unit iso node

theorem retainedRule5Observation_iso (node : left.Node) :
    retainedRule5Observation molecule descriptorMap unit left node =
      retainedRule5Observation molecule descriptorMap unit right (iso.toEquiv node) := by
  unfold retainedRule5Observation neutralizeRingDuplicate
  rw [iso.map_label node]
  cases (right.label (iso.toEquiv node)).provenance with
  | ringDuplicate _ => rfl
  | realAtom => exact rule5Observation_iso molecule descriptorMap unit iso node
  | multipleBondDuplicate _ => exact rule5Observation_iso molecule descriptorMap unit iso node
  | phantom _ => exact rule5Observation_iso molecule descriptorMap unit iso node
  | lonePair _ => exact rule5Observation_iso molecule descriptorMap unit iso node
  | auxiliary _ => exact rule5Observation_iso molecule descriptorMap unit iso node

theorem retainedRankEvidence_preserved :
    RootedDigraph.Addressing.EvidencePreserved iso
      (retainedRankEvidence molecule descriptorMap unit left)
      (retainedRankEvidence molecule descriptorMap unit right) := by
  intro node
  simp only [retainedRankEvidence]
  rw [rule3Observation_iso molecule descriptorMap unit iso node,
    retainedRule4aObservation_iso molecule descriptorMap unit iso node]

theorem retainedReadingEvidence_preserved (reference : DescriptorSense) :
    RootedDigraph.Addressing.EvidencePreserved iso
      (retainedReadingEvidence molecule descriptorMap unit left reference)
      (retainedReadingEvidence molecule descriptorMap unit right reference) := by
  intro node
  simp only [retainedReadingEvidence]
  rw [rule3Observation_iso molecule descriptorMap unit iso node,
    retainedRule4aObservation_iso molecule descriptorMap unit iso node,
    eligibleSense_iso molecule descriptorMap unit iso node]

theorem retainedReadingEvidence4c_preserved (reference : DescriptorSense) :
    RootedDigraph.Addressing.EvidencePreserved iso
      (retainedReadingEvidence4c molecule descriptorMap unit left reference)
      (retainedReadingEvidence4c molecule descriptorMap unit right reference) := by
  intro node
  have base := retainedReadingEvidence_preserved molecule descriptorMap unit iso reference node
  simp only [retainedReadingEvidence4c]
  rw [base, retainedRule4cObservation_iso molecule descriptorMap unit iso node]

theorem retainedNoReferenceEvidence4c_preserved :
    RootedDigraph.Addressing.EvidencePreserved iso
      (retainedNoReferenceEvidence4c molecule descriptorMap unit left)
      (retainedNoReferenceEvidence4c molecule descriptorMap unit right) := by
  intro node
  have base := retainedRankEvidence_preserved molecule descriptorMap unit iso node
  simp only [retainedNoReferenceEvidence4c]
  rw [base, retainedRule4cObservation_iso molecule descriptorMap unit iso node]

end Transport

end
end TetraStereo.OneCenter.DeclarativeCIP

assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.NodeProvenance.isRingDuplicate_iff
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.occurrenceReading_of_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule4aObservation_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule4cObservation_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule5Observation_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule4aObservation_of_not_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule4cObservation_of_not_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule5Observation_of_not_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.not_ringDuplicate_of_realAtom
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule4aObservation_real_unavailable
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule4cObservation_real_unavailable
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule5Observation_real_unavailable
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRankEvidence_rule4b
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRankEvidence_rule4c
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRankEvidence_rule5
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReadingEvidence_rule4c
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReadingEvidence_rule5
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReadingEvidence4c_rule5
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedNoReferenceEvidence4c_rule4b
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedNoReferenceEvidence4c_rule5
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRankEvidence_eq_rankEvidence_of_not_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReadingEvidence_eq_readingEvidence_of_not_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReadingEvidence4c_eq_readingEvidence4c_of_not_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedNoReferenceEvidence4c_eq_noReferenceEvidence4c_of_not_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereoLabel_retainedRankEvidence_rule4a_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereoLabel_retainedRankEvidence_rule4a_real_unavailable
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereoLabel_retainedReadingEvidence_rule4b_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereoLabel_retainedReadingEvidence4c_rule4b_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereoLabel_retainedReadingEvidence4c_rule4c_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.stereoLabel_retainedNoReferenceEvidence4c_rule4c_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.liftObservation_retainedRule5_ringDuplicate
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule4aOnly_retainedRankEvidence_of_simpleBonded
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule4abcOnly_retainedReadingEvidence4c_of_simpleBonded
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.rule4acOnly_retainedNoReferenceEvidence4c_of_simpleBonded
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.ringDuplicate_provenance_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule4aObservation_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule4cObservation_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRule5Observation_iso
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedRankEvidence_preserved
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReadingEvidence_preserved
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedReadingEvidence4c_preserved
assert_kernel_only TetraStereo.OneCenter.DeclarativeCIP.retainedNoReferenceEvidence4c_preserved
