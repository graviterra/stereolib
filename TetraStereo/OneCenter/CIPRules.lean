import TetraStereo.OneCenter.Pseudoasymmetry

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

section

/-!
  Rule-traced CIP comparison engine.

  This module is the first engine layer: it turns the existing cycle-cut descriptor keys into
  proof-carrying comparison certificates.  The current implementation covers the rule families
  already represented by the key (`atomicNumber`, `isotopeMass`, and frontier exhaustion) and shares
  the same trace infrastructure as the Rule-5 pseudoasymmetry scaffold.

  The intended direction is that future IUPAC rules refine the trace rather than replacing this
  interface: a caller should ask for a comparison certificate, inspect its outcome, and retain the
  rule trace explaining why the comparison terminated.

  ## Pseudoasymmetric sign calibration

  `PseudoRS.ofSign` is source-calibrated in `Pseudoasymmetry.lean` (`-1 ↦ r`, `+1 ↦ s`).  The
  concrete engine lemmas below therefore read `centerSign = -1` with the Rule-5 pair `R,S` as `r`,
  while `centerSign = +1` with `R,S` is `s`.  Swapping the enantiomorphic pair reverses the
  Rule-5 orientation.
-/

namespace CIPRuleEngine

open Prod.Lex

/-- Compare priority-valued natural numbers, where larger numbers have higher CIP priority. -/
def comparePriorityNat (a b : ℕ) : Ordering :=
  if a < b then Ordering.lt else if b < a then Ordering.gt else Ordering.eq

@[simp] theorem comparePriorityNat_self (a : ℕ) :
    comparePriorityNat a a = Ordering.eq := by
  simp [comparePriorityNat]

theorem comparePriorityNat_eq_lt_of_lt {a b : ℕ} (h : a < b) :
    comparePriorityNat a b = Ordering.lt := by
  simp [comparePriorityNat, h]

theorem comparePriorityNat_eq_gt_of_lt {a b : ℕ} (h : b < a) :
    comparePriorityNat a b = Ordering.gt := by
  have hnot : ¬ a < b := Nat.not_lt_of_ge h.le
  simp [comparePriorityNat, hnot, h]

theorem comparePriorityNat_eq_eq_of_eq {a b : ℕ} (h : a = b) :
    comparePriorityNat a b = Ordering.eq := by
  subst h
  simp

/-- A single natural-number priority comparison, tagged by the rule family that produced it. -/
def priorityNatDecision (rule : CIPRuleFamily) (a b : ℕ) : CIPRuleDecision where
  rule := rule
  outcome := comparePriorityNat a b

@[simp] theorem priorityNatDecision_outcome (rule : CIPRuleFamily) (a b : ℕ) :
    (priorityNatDecision rule a b).outcome = comparePriorityNat a b :=
  rfl

/-- Rule-traced comparison of two atom labels.  Atomic number decides first; isotope mass is used
only if the atomic numbers tie. -/
def compareAtomLabelTrace (a b : MoleculeGraph.AtomLabel) : List CIPRuleDecision :=
  [priorityNatDecision CIPRuleFamily.atomicNumber (ofLex a).1 (ofLex b).1,
    priorityNatDecision CIPRuleFamily.isotopeMass (ofLex a).2 (ofLex b).2]

/-- Proof-carrying comparison of two atom labels. -/
def compareAtomLabelCertificate (a b : MoleculeGraph.AtomLabel) : CIPTraceCertificate :=
  CIPTraceCertificate.ofTrace (compareAtomLabelTrace a b)

@[simp] theorem compareAtomLabelCertificate_outcome (a b : MoleculeGraph.AtomLabel) :
    (compareAtomLabelCertificate a b).outcome =
      cipTraceOutcome (compareAtomLabelTrace a b) :=
  rfl

theorem compareAtomLabelTrace_outcome_lt_of_atomicNumber_lt
    {a b : MoleculeGraph.AtomLabel} (h : (ofLex a).1 < (ofLex b).1) :
  cipTraceOutcome (compareAtomLabelTrace a b) = Ordering.lt := by
  simp [compareAtomLabelTrace, priorityNatDecision, comparePriorityNat_eq_lt_of_lt h]

theorem compareAtomLabelTrace_outcome_gt_of_atomicNumber_lt
    {a b : MoleculeGraph.AtomLabel} (h : (ofLex b).1 < (ofLex a).1) :
  cipTraceOutcome (compareAtomLabelTrace a b) = Ordering.gt := by
  simp [compareAtomLabelTrace, priorityNatDecision, comparePriorityNat_eq_gt_of_lt h]

theorem compareAtomLabelTrace_outcome_lt_of_mass_lt
    {a b : MoleculeGraph.AtomLabel} (hz : (ofLex a).1 = (ofLex b).1)
    (hm : (ofLex a).2 < (ofLex b).2) :
  cipTraceOutcome (compareAtomLabelTrace a b) = Ordering.lt := by
  simp [compareAtomLabelTrace, priorityNatDecision, hz, comparePriorityNat_eq_lt_of_lt hm]

theorem compareAtomLabelTrace_outcome_gt_of_mass_lt
    {a b : MoleculeGraph.AtomLabel} (hz : (ofLex a).1 = (ofLex b).1)
    (hm : (ofLex b).2 < (ofLex a).2) :
  cipTraceOutcome (compareAtomLabelTrace a b) = Ordering.gt := by
  simp [compareAtomLabelTrace, priorityNatDecision, hz, comparePriorityNat_eq_gt_of_lt hm]

theorem compareAtomLabelTrace_outcome_eq_of_eq
    {a b : MoleculeGraph.AtomLabel} (h : a = b) :
    cipTraceOutcome (compareAtomLabelTrace a b) = Ordering.eq := by
  subst h
  simp [compareAtomLabelTrace, priorityNatDecision]

/-- A trace decision used when one finite expansion key is exhausted before the other. -/
def frontierExhaustionDecision (outcome : Ordering) : CIPRuleDecision where
  rule := CIPRuleFamily.frontierExhaustion
  outcome := outcome

/-- Rule-traced lexicographic comparison of cycle-cut CIP keys. -/
def compareKeyTrace : List MoleculeGraph.AtomLabel → List MoleculeGraph.AtomLabel →
    List CIPRuleDecision
  | [], [] => []
  | [], _ :: _ => [frontierExhaustionDecision Ordering.lt]
  | _ :: _, [] => [frontierExhaustionDecision Ordering.gt]
  | a :: as, b :: bs => compareAtomLabelTrace a b ++ compareKeyTrace as bs

/-- Proof-carrying lexicographic comparison of cycle-cut CIP keys. -/
def compareKeyCertificate (left right : List MoleculeGraph.AtomLabel) : CIPTraceCertificate :=
  CIPTraceCertificate.ofTrace (compareKeyTrace left right)

@[simp] theorem compareKeyCertificate_outcome
    (left right : List MoleculeGraph.AtomLabel) :
    (compareKeyCertificate left right).outcome = cipTraceOutcome (compareKeyTrace left right) :=
  rfl

@[simp] theorem compareKeyTrace_nil_nil :
    compareKeyTrace [] [] = [] :=
  rfl

@[simp] theorem compareKeyTrace_nil_cons (b : MoleculeGraph.AtomLabel)
    (bs : List MoleculeGraph.AtomLabel) :
    compareKeyTrace [] (b :: bs) = [frontierExhaustionDecision Ordering.lt] :=
  rfl

@[simp] theorem compareKeyTrace_cons_nil (a : MoleculeGraph.AtomLabel)
    (as : List MoleculeGraph.AtomLabel) :
    compareKeyTrace (a :: as) [] = [frontierExhaustionDecision Ordering.gt] :=
  rfl

@[simp] theorem compareKeyTrace_cons_cons (a b : MoleculeGraph.AtomLabel)
    (as bs : List MoleculeGraph.AtomLabel) :
    compareKeyTrace (a :: as) (b :: bs) =
      compareAtomLabelTrace a b ++ compareKeyTrace as bs :=
  rfl

theorem compareKeyTrace_outcome_lt_of_head_atomicNumber_lt
    {a b : MoleculeGraph.AtomLabel} {as bs : List MoleculeGraph.AtomLabel}
    (h : (ofLex a).1 < (ofLex b).1) :
    cipTraceOutcome (compareKeyTrace (a :: as) (b :: bs)) = Ordering.lt := by
  simp [compareKeyTrace, compareAtomLabelTrace, priorityNatDecision,
    comparePriorityNat_eq_lt_of_lt h]

theorem compareKeyTrace_outcome_gt_of_head_atomicNumber_lt
    {a b : MoleculeGraph.AtomLabel} {as bs : List MoleculeGraph.AtomLabel}
    (h : (ofLex b).1 < (ofLex a).1) :
    cipTraceOutcome (compareKeyTrace (a :: as) (b :: bs)) = Ordering.gt := by
  simp [compareKeyTrace, compareAtomLabelTrace, priorityNatDecision,
    comparePriorityNat_eq_gt_of_lt h]

theorem compareKeyTrace_outcome_eq_of_singleton_eq
    {a b : MoleculeGraph.AtomLabel} (h : a = b) :
    cipTraceOutcome (compareKeyTrace [a] [b]) = Ordering.eq := by
  subst h
  simp [compareKeyTrace, compareAtomLabelTrace, priorityNatDecision]

/-- Equal finite descriptor keys produce a tied rule trace. -/
theorem compareKeyTrace_outcome_eq_of_eq
    {left right : List MoleculeGraph.AtomLabel} (h : left = right) :
    cipTraceOutcome (compareKeyTrace left right) = Ordering.eq := by
  subst h
  induction left with
  | nil =>
      simp [compareKeyTrace]
  | cons a as ih =>
      simp [compareKeyTrace, compareAtomLabelTrace, priorityNatDecision, ih]

/-- A marker decision recording that ordinary key comparison has fallen through to a
descriptor-dependent subrule. -/
def descriptorSubruleDecision : CIPRuleDecision where
  rule := CIPRuleFamily.descriptorSubrule
  outcome := Ordering.eq

/-- The descriptor-dependent Rule-5 trace invoked after ordinary graph/key comparison ties. -/
def descriptorRule5Trace (left right : RS) : List CIPRuleDecision :=
  [descriptorSubruleDecision, rule5PairDecision left right]

@[simp] theorem descriptorRule5Trace_outcome (left right : RS) :
    cipTraceOutcome (descriptorRule5Trace left right) = rule5PairOrdering left right := by
  cases left <;> cases right <;>
    simp [descriptorRule5Trace, descriptorSubruleDecision, rule5PairDecision,
      rule5PairOrdering, cipTraceOutcome]

@[simp] theorem descriptorRule5Trace_outcome_R_S :
    cipTraceOutcome (descriptorRule5Trace RS.R RS.S) = Ordering.gt := by
  simp

@[simp] theorem descriptorRule5Trace_outcome_S_R :
    cipTraceOutcome (descriptorRule5Trace RS.S RS.R) = Ordering.lt := by
  simp

/-- Compare ordinary descriptor keys first; if and only if those rules tie, automatically invoke
the descriptor-dependent Rule-5 enantiomorphic-pair trace. -/
def compareKeyThenRule5Trace (leftKey rightKey : List MoleculeGraph.AtomLabel)
    (leftDescriptor rightDescriptor : RS) : List CIPRuleDecision :=
  let baseTrace := compareKeyTrace leftKey rightKey
  if cipTraceOutcome baseTrace = Ordering.eq then
    baseTrace ++ descriptorRule5Trace leftDescriptor rightDescriptor
  else
    baseTrace

/-- Proof-carrying key comparison with automatic Rule-5 fallthrough on ordinary ties. -/
def compareKeyThenRule5Certificate (leftKey rightKey : List MoleculeGraph.AtomLabel)
    (leftDescriptor rightDescriptor : RS) : CIPTraceCertificate :=
  CIPTraceCertificate.ofTrace
    (compareKeyThenRule5Trace leftKey rightKey leftDescriptor rightDescriptor)

@[simp] theorem compareKeyThenRule5Certificate_outcome
    (leftKey rightKey : List MoleculeGraph.AtomLabel) (leftDescriptor rightDescriptor : RS) :
    (compareKeyThenRule5Certificate leftKey rightKey leftDescriptor rightDescriptor).outcome =
      cipTraceOutcome (compareKeyThenRule5Trace leftKey rightKey leftDescriptor rightDescriptor) :=
  rfl

theorem compareKeyThenRule5Trace_outcome_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel} {leftDescriptor rightDescriptor : RS}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    cipTraceOutcome (compareKeyThenRule5Trace leftKey rightKey leftDescriptor rightDescriptor) =
      rule5PairOrdering leftDescriptor rightDescriptor := by
  simp [compareKeyThenRule5Trace, h, cipTraceOutcome_append_of_left_eq h]

theorem compareKeyThenRule5Trace_outcome_of_key_ne_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel} {leftDescriptor rightDescriptor : RS}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) ≠ Ordering.eq) :
    cipTraceOutcome (compareKeyThenRule5Trace leftKey rightKey leftDescriptor rightDescriptor) =
      cipTraceOutcome (compareKeyTrace leftKey rightKey) := by
  simp [compareKeyThenRule5Trace, h]

theorem compareKeyThenRule5Certificate_outcome_R_S_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (compareKeyThenRule5Certificate leftKey rightKey RS.R RS.S).outcome = Ordering.gt := by
  simp [compareKeyThenRule5Certificate, compareKeyThenRule5Trace_outcome_of_key_eq h]

theorem compareKeyThenRule5Certificate_outcome_S_R_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (compareKeyThenRule5Certificate leftKey rightKey RS.S RS.R).outcome = Ordering.lt := by
  simp [compareKeyThenRule5Certificate, compareKeyThenRule5Trace_outcome_of_key_eq h]

/-- Engine result for a pseudoasymmetric Rule-5 descriptor: it stores the automatically generated
comparison certificate, its sign, and the lowercase descriptor read from that signed comparison. -/
structure Rule5PseudoDescriptorEngineResult where
  comparison : CIPTraceCertificate
  comparisonSign : ℝ
  descriptor : PseudoRS

/-- Derive a lowercase pseudoasymmetric descriptor from ordinary tied keys plus descriptor-dependent
Rule 5.  The comparison is performed by `compareKeyThenRule5Certificate`, so Rule 5 is invoked
automatically exactly when the ordinary key trace ties. -/
noncomputable def rule5PseudoDescriptorEngineFromKeys (centerSign : ℝ)
    (leftKey rightKey : List MoleculeGraph.AtomLabel) (leftDescriptor rightDescriptor : RS) :
    Rule5PseudoDescriptorEngineResult :=
  let comparison := compareKeyThenRule5Certificate leftKey rightKey leftDescriptor rightDescriptor
  { comparison := comparison
    comparisonSign := orderingSign comparison.outcome
    descriptor := PseudoRS.ofSign (centerSign * orderingSign comparison.outcome) }

theorem rule5PseudoDescriptorEngineFromKeys_descriptor_eq_pseudoDescriptor_of_key_eq
    (centerSign : ℝ) {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (leftDescriptor rightDescriptor : RS)
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (rule5PseudoDescriptorEngineFromKeys centerSign leftKey rightKey
      leftDescriptor rightDescriptor).descriptor =
        pseudoDescriptor centerSign leftDescriptor rightDescriptor := by
  simp [rule5PseudoDescriptorEngineFromKeys, pseudoDescriptor, pseudoasymmetricSign,
    compareKeyThenRule5Certificate, compareKeyThenRule5Trace, h,
    cipTraceOutcome_append_of_left_eq h]

/-- Under a tied ordinary key trace the engine comparison outcome is exactly the Rule-5 pair
ordering. -/
theorem rule5PseudoDescriptorEngineFromKeys_comparison_outcome_eq_rule5PairOrdering_of_key_eq
    (centerSign : ℝ) {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (leftDescriptor rightDescriptor : RS)
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (rule5PseudoDescriptorEngineFromKeys centerSign leftKey rightKey
      leftDescriptor rightDescriptor).comparison.outcome =
        rule5PairOrdering leftDescriptor rightDescriptor := by
  simp [rule5PseudoDescriptorEngineFromKeys, compareKeyThenRule5Certificate,
    compareKeyThenRule5Trace, h, cipTraceOutcome_append_of_left_eq h]

theorem rule5PseudoDescriptorEngineFromKeys_comparison_outcome_R_S_of_key_eq
    (centerSign : ℝ) {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (rule5PseudoDescriptorEngineFromKeys centerSign leftKey rightKey RS.R RS.S).comparison.outcome =
      Ordering.gt := by
  rw [rule5PseudoDescriptorEngineFromKeys_comparison_outcome_eq_rule5PairOrdering_of_key_eq
    centerSign RS.R RS.S h]
  rfl

theorem rule5PseudoDescriptorEngineFromKeys_comparison_outcome_S_R_of_key_eq
    (centerSign : ℝ) {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (rule5PseudoDescriptorEngineFromKeys centerSign leftKey rightKey RS.S RS.R).comparison.outcome =
      Ordering.lt := by
  rw [rule5PseudoDescriptorEngineFromKeys_comparison_outcome_eq_rule5PairOrdering_of_key_eq
    centerSign RS.S RS.R h]
  rfl

/-! ### Concrete calibrated descriptors

The source calibration maps a combined sign `-1` to `r` and `+1` to `s`.  With the Rule-5 pair
`R,S` the pair sign is `+1`, so the engine descriptor is `PseudoRS.ofSign centerSign`.  With the
enantiomorphic pair swapped to `S,R` the pair sign is `-1`, so the descriptor is
`PseudoRS.ofSign (-centerSign)`. -/

theorem rule5PseudoDescriptorEngineFromKeys_R_S_descriptor_eq_ofSign_of_key_eq
    (centerSign : ℝ) {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (rule5PseudoDescriptorEngineFromKeys centerSign leftKey rightKey RS.R RS.S).descriptor =
      PseudoRS.ofSign centerSign := by
  simp [rule5PseudoDescriptorEngineFromKeys, compareKeyThenRule5Certificate,
    compareKeyThenRule5Trace, h, cipTraceOutcome_append_of_left_eq h, orderingSign,
    rule5PairOrdering]

theorem rule5PseudoDescriptorEngineFromKeys_S_R_descriptor_eq_ofSign_neg_of_key_eq
    (centerSign : ℝ) {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (rule5PseudoDescriptorEngineFromKeys centerSign leftKey rightKey RS.S RS.R).descriptor =
      PseudoRS.ofSign (-centerSign) := by
  simp [rule5PseudoDescriptorEngineFromKeys, compareKeyThenRule5Certificate,
    compareKeyThenRule5Trace, h, cipTraceOutcome_append_of_left_eq h, orderingSign,
    rule5PairOrdering]

/-- Calibrated `r` case: local source sign `-1` with the Rule-5 pair `R,S`. -/
theorem rule5PseudoDescriptorEngineFromKeys_negOne_R_S_descriptor_eq_r_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (rule5PseudoDescriptorEngineFromKeys (-1) leftKey rightKey RS.R RS.S).descriptor =
      PseudoRS.r := by
  simpa using
    rule5PseudoDescriptorEngineFromKeys_R_S_descriptor_eq_ofSign_of_key_eq (-1) h

/-- Calibrated `s` case: local source sign `+1` with the Rule-5 pair `R,S`. -/
theorem rule5PseudoDescriptorEngineFromKeys_one_R_S_descriptor_eq_s_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (rule5PseudoDescriptorEngineFromKeys 1 leftKey rightKey RS.R RS.S).descriptor =
      PseudoRS.s := by
  simpa using
    rule5PseudoDescriptorEngineFromKeys_R_S_descriptor_eq_ofSign_of_key_eq 1 h

/-- Calibrated `r` case with the enantiomorphic pair swapped: local source sign `+1` with `S,R`. -/
theorem rule5PseudoDescriptorEngineFromKeys_one_S_R_descriptor_eq_r_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (rule5PseudoDescriptorEngineFromKeys 1 leftKey rightKey RS.S RS.R).descriptor =
      PseudoRS.r := by
  simpa using
    rule5PseudoDescriptorEngineFromKeys_S_R_descriptor_eq_ofSign_neg_of_key_eq 1 h

/-- Calibrated `s` case with the enantiomorphic pair swapped: local source sign `-1` with `S,R`. -/
theorem rule5PseudoDescriptorEngineFromKeys_negOne_S_R_descriptor_eq_s_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (rule5PseudoDescriptorEngineFromKeys (-1) leftKey rightKey RS.S RS.R).descriptor =
      PseudoRS.s := by
  simpa using
    rule5PseudoDescriptorEngineFromKeys_S_R_descriptor_eq_ofSign_neg_of_key_eq (-1) h

/-- Historical name retained for downstream compatibility.  After the source calibration this is
the `centerSign = -1`, Rule-5 pair `R,S` case; the corresponding `centerSign = +1` case is `s`. -/
theorem rule5PseudoDescriptorEngineFromKeys_R_S_descriptor_eq_r_of_key_eq
    {leftKey rightKey : List MoleculeGraph.AtomLabel}
    (h : cipTraceOutcome (compareKeyTrace leftKey rightKey) = Ordering.eq) :
    (rule5PseudoDescriptorEngineFromKeys (-1) leftKey rightKey RS.R RS.S).descriptor =
      PseudoRS.r :=
  rule5PseudoDescriptorEngineFromKeys_negOne_R_S_descriptor_eq_r_of_key_eq h

end CIPRuleEngine

namespace OneCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Rule-traced comparison of two cycle-cut CIP ligand keys.  `Ordering.gt` means the first ligand
has higher priority; `Ordering.lt` means the second ligand has higher priority. -/
noncomputable def cipRuleCompareCycleCut (m : OneCenterMolecule V) (i j : Fin 4) : CIPTraceCertificate :=
  CIPRuleEngine.compareKeyCertificate (m.cipKeyCycleCut i) (m.cipKeyCycleCut j)

/-- Descriptor-facing rule-traced comparison.  This currently delegates to the cycle-cut key, which
is the descriptor-facing key used throughout the current engine. -/
noncomputable abbrev cipRuleCompareDescriptor (m : OneCenterMolecule V) (i j : Fin 4) :
    CIPTraceCertificate :=
  m.cipRuleCompareCycleCut i j

@[simp] theorem cipRuleCompareCycleCut_outcome (m : OneCenterMolecule V) (i j : Fin 4) :
    (m.cipRuleCompareCycleCut i j).outcome =
      cipTraceOutcome (CIPRuleEngine.compareKeyTrace (m.cipKeyCycleCut i) (m.cipKeyCycleCut j)) :=
  rfl

/-- The descriptor engine surface for a one-center molecule.  This bundles the descriptor key,
pairwise rule-traced comparisons, the chosen total order/permutation, and safe optional outputs
that are defined only when descriptor priorities are resolved. -/
structure CIPDescriptorEngineResult (m : OneCenterMolecule V) where
  key : Fin 4 → List MoleculeGraph.AtomLabel
  compare : Fin 4 → Fin 4 → CIPTraceCertificate
  order : List (Fin 4)
  permutation : Equiv.Perm (Fin 4)
  safeOrder? : Option (List (Fin 4))
  safePermutation? : Option (Equiv.Perm (Fin 4))

/-- Run the current descriptor engine on a one-center molecule.  The implementation is intentionally
thin: future IUPAC-rule refinements should strengthen the comparison trace behind this API without
changing the caller-facing shape. -/
noncomputable def cipDescriptorEngine (m : OneCenterMolecule V) : CIPDescriptorEngineResult m where
  key := m.cipKeyDescriptor
  compare := m.cipRuleCompareDescriptor
  order := m.cipOrderDescriptor
  permutation := m.cipPermutationDescriptor
  safeOrder? := m.cipOrderDescriptor?
  safePermutation? := m.cipPermutationDescriptor?

@[simp] theorem cipDescriptorEngine_key (m : OneCenterMolecule V) :
    m.cipDescriptorEngine.key = m.cipKeyDescriptor :=
  rfl

@[simp] theorem cipDescriptorEngine_compare (m : OneCenterMolecule V) (i j : Fin 4) :
    m.cipDescriptorEngine.compare i j = m.cipRuleCompareDescriptor i j :=
  rfl

@[simp] theorem cipDescriptorEngine_order (m : OneCenterMolecule V) :
    m.cipDescriptorEngine.order = m.cipOrderDescriptor :=
  rfl

@[simp] theorem cipDescriptorEngine_permutation (m : OneCenterMolecule V) :
    m.cipDescriptorEngine.permutation = m.cipPermutationDescriptor :=
  rfl

@[simp] theorem cipDescriptorEngine_safeOrder? (m : OneCenterMolecule V) :
    m.cipDescriptorEngine.safeOrder? = m.cipOrderDescriptor? :=
  rfl

@[simp] theorem cipDescriptorEngine_safePermutation? (m : OneCenterMolecule V) :
    m.cipDescriptorEngine.safePermutation? = m.cipPermutationDescriptor? :=
  rfl

theorem cipDescriptorEngine_safePermutation?_eq_some_of_resolved
    (m : OneCenterMolecule V) (h : m.ResolvedCIPDescriptor) :
    m.cipDescriptorEngine.safePermutation? = some m.cipPermutationDescriptor := by
  simpa using m.cipPermutationDescriptor?_eq_some_of_resolvedCIPDescriptor h

end OneCenterMolecule

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Descriptor-facing rule-traced comparison of two local ligands at a distinguished center. -/
noncomputable def cipRuleCompareDescriptorAt (m : MultiCenterMolecule V) (c : m.Center) (i j : Fin 4) :
    CIPTraceCertificate :=
  CIPRuleEngine.compareKeyCertificate (m.cipKeyDescriptorAt c i) (m.cipKeyDescriptorAt c j)

/-- Descriptor-facing local comparison with automatic Rule-5 fallthrough when the ordinary
cycle-cut key comparison ties. -/
noncomputable def cipRuleCompareDescriptorAtWithRule5 (m : MultiCenterMolecule V) (c : m.Center) (i j : Fin 4)
    (leftDescriptor rightDescriptor : RS) : CIPTraceCertificate :=
  CIPRuleEngine.compareKeyThenRule5Certificate
    (m.cipKeyDescriptorAt c i) (m.cipKeyDescriptorAt c j)
    leftDescriptor rightDescriptor

/-- Multi-center convenience wrapper for deriving a pseudoasymmetric lowercase descriptor at a
distinguished center from tied local ligand keys and descriptor-dependent Rule 5. -/
noncomputable def rule5PseudoDescriptorEngineAt (m : MultiCenterMolecule V) (cfg : m.Configuration)
    (c : m.Center) (leftLigand rightLigand : Fin 4)
    (leftDescriptor rightDescriptor : RS) : CIPRuleEngine.Rule5PseudoDescriptorEngineResult :=
  CIPRuleEngine.rule5PseudoDescriptorEngineFromKeys
    (m.configurationSign cfg c)
    (m.cipKeyDescriptorAt c leftLigand)
    (m.cipKeyDescriptorAt c rightLigand)
    leftDescriptor rightDescriptor

end MultiCenterMolecule

/-- A certificate that the pseudoasymmetric lowercase descriptor was produced by the rule engine:
ordinary local keys tied, Rule 5 was invoked, the engine produced the descriptor, and a molecular
symmetry proves the full configuration achiral. -/
structure Rule5PseudoasymmetricEngineCertificate {V : Type*} [Fintype V] [DecidableEq V]
    (m : MultiCenterMolecule V) (cfg : m.Configuration) where
  center : m.Center
  leftLigand : Fin 4
  rightLigand : Fin 4
  leftDescriptor : RS
  rightDescriptor : RS
  keyTie :
    cipTraceOutcome
      (CIPRuleEngine.compareKeyTrace
        (m.cipKeyDescriptorAt center leftLigand)
        (m.cipKeyDescriptorAt center rightLigand)) = Ordering.eq
  descriptor : PseudoRS
  descriptor_eq :
    descriptor =
      (m.rule5PseudoDescriptorEngineAt cfg center leftLigand rightLigand
        leftDescriptor rightDescriptor).descriptor
  achiral : m.AchiralConfigurationBySymmetry cfg

end
end OneCenter
end TetraStereo
