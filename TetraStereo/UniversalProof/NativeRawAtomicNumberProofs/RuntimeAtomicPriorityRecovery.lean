import TetraStereo.UniversalProof.NativeRawAtomicNumber
import TetraStereo.OneCenter.SmilesTetrahedral
import TetraStereo.OneCenter.CIPAuthoritativeBranchComparator

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule








































































/-- The independent runtime ranking domain for one cursor: a physical real-atom occurrence, an atom
index inside the parsed molecule, and an atom that does not lie on any ring at the comparison fuel.
Every component is a property of the written molecule and the cursor alone. -/
def RealOutsideCycle (mol : RawMolecule) (fuel : ℕ) (cursor : CanonicalRerootCursor) : Prop :=
  cursor.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom ∧
    cursor.node.atom < mol.atomCount ∧
    mol.atomLiesInCycle fuel cursor.node.atom = false

/-- Strictly descending atomic-number order on runtime cursors. -/
def AtomicDesc (mol : RawMolecule) (left right : CanonicalRerootCursor) : Prop :=
  mol.atomZAt right.node.atom < mol.atomZAt left.node.atom

/-! ## Honest exclusion boundaries -/

/-- Two occurrence atoms carrying the *same* actual atomic number.  This is the exact complement of
the strictness premise used by every Rule-1a bridge below.  It is an exclusion boundary: the module
claims neither a tie result nor a nonstereogenic outcome here. -/
def TiedAtomicNumber (mol : RawMolecule) (left right : CanonicalRerootCursor) : Prop :=
  mol.atomZAt left.node.atom = mol.atomZAt right.node.atom

/-- Two occurrence atoms that *both* lie on a ring at the comparison fuel.  This is the exact
complement of the acyclicity disjunction used to refute the conflict gate.  It is an exclusion
boundary: no gate value or ordering is claimed here. -/
def BothCyclic (mol : RawMolecule) (fuel : ℕ) (left right : CanonicalRerootCursor) : Prop :=
  mol.atomLiesInCycle fuel left.node.atom = true ∧
    mol.atomLiesInCycle fuel right.node.atom = true

/-- The tied case is exactly where the first-sphere comparison is `eq`: the strictness premise is
the precise boundary of the proved class, not a hidden extra assumption. -/
theorem tiedAtomicNumber_compare_eq (mol : RawMolecule) (left right : CanonicalRerootCursor)
    (tied : TiedAtomicNumber mol left right) :
    compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) = Ordering.eq := by
  have same : mol.atomZAt left.node.atom = mol.atomZAt right.node.atom := tied
  rw [same]
  exact Nat.compare_eq_eq.mpr rfl

/-- Both endpoints cyclic is exactly the failure of the gate-refutation disjunction.  The
`occurrenceRootsProvedAutomorphic_eq_false_of_acyclic` lemma cannot be applied here; no gate value
is claimed. -/
theorem bothCyclic_iff_not_acyclic (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) :
    BothCyclic mol fuel left right ↔
      ¬ (mol.atomLiesInCycle fuel left.node.atom = false ∨
        mol.atomLiesInCycle fuel right.node.atom = false) := by
  unfold BothCyclic
  cases hl : mol.atomLiesInCycle fuel left.node.atom <;>
    cases hr : mol.atomLiesInCycle fuel right.node.atom <;>
      simp

/-! ## Exact Rule-1a labels at real-atom occurrences -/


-- canonicalRule1aLabel?_realAtom is re-exported from NativeRawAtomicNumber.


/-- The uncapped authoritative Rule-1a labeler agrees at a `realAtom` node. -/
theorem canonicalRule1aLabelAuthoritative?_realAtom (mol : RawMolecule)
    (node : RawMolecule.CanonicalBranchNode)
    (h : node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom) :
    mol.canonicalRule1aLabelAuthoritative? node =
      some { numerator := mol.atomZAt node.atom, denominator := 1 } := by
  cases hp : node.provenance with
  | realAtom => simp [RawMolecule.canonicalRule1aLabelAuthoritative?, hp]
  | multipleBondDuplicate distance => simp_all
  | ringDuplicate distance => simp_all
  | phantom distance => simp_all


-- compareCIPAtomicLabel_unitValue is re-exported from NativeRawAtomicNumber.



-- compareCanonicalNodeRule?_rule1a_realAtom is re-exported from NativeRawAtomicNumber.


/-- Strict real-root atomic-label comparison for the uncapped authoritative node comparator. -/
theorem compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom (mol : RawMolecule)
    (left right : RawMolecule.CanonicalBranchNode)
    (hL : left.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.provenance = RawMolecule.CanonicalNodeProvenance.realAtom) :
    mol.compareCanonicalNodeRuleAuthoritative? RawMolecule.CanonicalRuleStage.rule1a left right =
      some (compare (mol.atomZAt left.atom) (mol.atomZAt right.atom)) := by
  have hLabelL := canonicalRule1aLabelAuthoritative?_realAtom mol left hL
  have hLabelR := canonicalRule1aLabelAuthoritative?_realAtom mol right hR
  have hNode :
      mol.compareCanonicalNodeRuleAuthoritative? RawMolecule.CanonicalRuleStage.rule1a left right =
      some (RawMolecule.compareCIPAtomicLabel
        { numerator := mol.atomZAt left.atom, denominator := 1 }
        { numerator := mol.atomZAt right.atom, denominator := 1 }) := by
    simp [RawMolecule.compareCanonicalNodeRuleAuthoritative?, hLabelL, hLabelR]
  simp [hNode, compareCIPAtomicLabel_unitValue]

/-- The Rule-1a pair law at a tied-Z pair returns `eq`, so a strict bridge conclusion is honestly
unavailable in this case. -/
theorem compareCanonicalNodeRule?_rule1a_realAtom_tied (mol : RawMolecule)
    (left right : RawMolecule.CanonicalBranchNode)
    (hL : left.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (tied : mol.atomZAt left.atom = mol.atomZAt right.atom) :
    mol.compareCanonicalNodeRule? RawMolecule.CanonicalRuleStage.rule1a left right =
      some Ordering.eq := by
  rw [compareCanonicalNodeRule?_rule1a_realAtom mol left right hL hR]
  have equal : compare (mol.atomZAt left.atom) (mol.atomZAt right.atom) = Ordering.eq := by
    rw [tied]
    exact Nat.compare_eq_eq.mpr rfl
  rw [equal]

/-! ## Source bounds for the explicitly chemical Rule-1a pair laws

The pair laws above compare `mol.atomZAt` values.  `atomZAt` returns `0` for an index that is not a
materialized atom, so alone they are computational statements.  The lemmas below add the explicit
source bound `index < mol.atomCount`, recover the actual parsed `AtomSpec`, and restate the
comparison over the *real* atomic numbers of the written molecule.  The generated-occurrence
condition (that a cursor node is a genuine reroot neighbour of a common reference root) is **not**
derivable from these hypotheses and remains an explicit open requirement. -/

/-- A materialized-atom bound: the index names a parsed atom of the written molecule. -/
def SourceBoundedAtom (mol : RawMolecule) (index : ℕ) : Prop :=
  index < mol.atomCount

instance (mol : RawMolecule) (index : ℕ) : Decidable (SourceBoundedAtom mol index) := by
  unfold SourceBoundedAtom
  infer_instance

/-- An in-bound index is an actually parsed atom. -/
theorem atomAt?_exists_of_lt_atomCount (mol : RawMolecule) (index : ℕ)
    (bound : index < mol.atomCount) :
    ∃ spec, mol.atomAt? index = some spec :=
  listGet?_exists_of_lt mol.atoms index (by simpa [RawMolecule.atomCount] using bound)

/-- An in-bound index names a materialized member of the source atom list. -/
theorem sourceBounded_mem_atoms (mol : RawMolecule) (index : ℕ)
    (bound : index < mol.atomCount) :
    ∃ spec, spec ∈ mol.atoms ∧ mol.atomAt? index = some spec := by
  obtain ⟨spec, observed⟩ := atomAt?_exists_of_lt_atomCount mol index bound
  exact ⟨spec,
    listGet?_eq_some_implies_mem mol.atoms index spec (by simpa [RawMolecule.atomAt?] using observed),
    observed⟩


-- atomZAt_eq_of_atomAt? is re-exported from NativeRawAtomicNumber.


/-- Source-bounded raw production Rule-1a pair law: with both occurrences carrying `realAtom`
provenance and in-bound atom indices, the first sphere compares the actual source atomic numbers of
the parsed molecule. -/
theorem compareCanonicalNodeRule?_rule1a_realAtom_sourceBounded (mol : RawMolecule)
    (left right : RawMolecule.CanonicalBranchNode)
    (hL : left.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hLB : left.atom < mol.atomCount) (hRB : right.atom < mol.atomCount) :
    ∃ leftSpec rightSpec,
      mol.atomAt? left.atom = some leftSpec ∧ mol.atomAt? right.atom = some rightSpec ∧
        mol.compareCanonicalNodeRule? RawMolecule.CanonicalRuleStage.rule1a left right =
          some (compare leftSpec.element.atomicNumber rightSpec.element.atomicNumber) := by
  obtain ⟨leftSpec, leftObserved⟩ := atomAt?_exists_of_lt_atomCount mol left.atom hLB
  obtain ⟨rightSpec, rightObserved⟩ := atomAt?_exists_of_lt_atomCount mol right.atom hRB
  refine ⟨leftSpec, rightSpec, leftObserved, rightObserved, ?_⟩
  rw [compareCanonicalNodeRule?_rule1a_realAtom mol left right hL hR,
    atomZAt_eq_of_atomAt? mol left.atom leftSpec leftObserved,
    atomZAt_eq_of_atomAt? mol right.atom rightSpec rightObserved]

/-- Source-bounded uncapped authoritative Rule-1a pair law, with the same actual-source-number
meaning. -/
theorem compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom_sourceBounded (mol : RawMolecule)
    (left right : RawMolecule.CanonicalBranchNode)
    (hL : left.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hLB : left.atom < mol.atomCount) (hRB : right.atom < mol.atomCount) :
    ∃ leftSpec rightSpec,
      mol.atomAt? left.atom = some leftSpec ∧ mol.atomAt? right.atom = some rightSpec ∧
        mol.compareCanonicalNodeRuleAuthoritative? RawMolecule.CanonicalRuleStage.rule1a left right =
          some (compare leftSpec.element.atomicNumber rightSpec.element.atomicNumber) := by
  obtain ⟨leftSpec, leftObserved⟩ := atomAt?_exists_of_lt_atomCount mol left.atom hLB
  obtain ⟨rightSpec, rightObserved⟩ := atomAt?_exists_of_lt_atomCount mol right.atom hRB
  refine ⟨leftSpec, rightSpec, leftObserved, rightObserved, ?_⟩
  rw [compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom mol left right hL hR,
    atomZAt_eq_of_atomAt? mol left.atom leftSpec leftObserved,
    atomZAt_eq_of_atomAt? mol right.atom rightSpec rightObserved]

/-! ## Immediate rule-major node comparison -/


-- compareCanonicalNodeThrough?_eq_of_rule1a is re-exported from NativeRawAtomicNumber.


/-- A strict Rule-1a node decision short-circuits the authoritative rule-major comparator. -/
theorem compareCanonicalNodeThroughAuthoritative?_eq_of_rule1a (mol : RawMolecule)
    (stage : RawMolecule.CanonicalRuleStage)
    (left right : RawMolecule.CanonicalBranchNode) (decision : Ordering)
    (computed :
      mol.compareCanonicalNodeRuleAuthoritative? RawMolecule.CanonicalRuleStage.rule1a left right =
        some decision)
    (strict : decision ≠ Ordering.eq) :
    mol.compareCanonicalNodeThroughAuthoritative? stage left right = some decision := by
  cases hdec : decision with
  | lt => simp [RawMolecule.compareCanonicalNodeThroughAuthoritative?, computed, hdec]
  | gt => simp [RawMolecule.compareCanonicalNodeThroughAuthoritative?, computed, hdec]
  | eq => exact absurd hdec strict

/-! ## Cursor sphere comparison -/

/-- The raw sphere comparator exposes a strict first-pair decision. -/
theorem compareCursorPairLabels_rule1a_single_real (mol : RawMolecule)
    (left right : CanonicalRerootCursor)
    (hL : left.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom) :
    compareCursorPairLabels mol RawMolecule.CanonicalRuleStage.rule1a [(left, right)] =
      some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
  have hNode := compareCanonicalNodeRule?_rule1a_realAtom mol left.node right.node hL hR
  cases hComp : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) with
  | lt => simp [compareCursorPairLabels, hNode, hComp]
  | gt => simp [compareCursorPairLabels, hNode, hComp]
  | eq => simp [compareCursorPairLabels, hNode, hComp]

/-- The uncapped authoritative sphere comparator exposes a strict first-pair decision. -/
theorem compareCursorPairLabelsAuthoritative?_rule1a_single_real (mol : RawMolecule)
    (left right : CanonicalRerootCursor)
    (hL : left.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom) :
    compareCursorPairLabelsAuthoritative? mol RawMolecule.CanonicalRuleStage.rule1a [(left, right)] =
      some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
  have hNode := compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom mol left.node right.node hL hR
  cases hComp : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) with
  | lt => simp [compareCursorPairLabelsAuthoritative?, hNode, hComp]
  | gt => simp [compareCursorPairLabelsAuthoritative?, hNode, hComp]
  | eq => simp [compareCursorPairLabelsAuthoritative?, hNode, hComp]

/-- A strict atomic-number difference already decides `compareCursorRule` on a singleton pair,
independently of the caller's recursive sibling callback. -/
theorem compareCursorRule_rule1a_single_real (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : ℕ) (left right : CanonicalRerootCursor)
    (hL : left.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hNe : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom) :
    compareCursorRule mol before RawMolecule.CanonicalRuleStage.rule1a (fuel + 1) [(left, right)] =
      some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
  have hPair := compareCursorPairLabels_rule1a_single_real mol left right hL hR
  cases hComp : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) with
  | lt => simp [compareCursorRule, hPair, hComp, RawMolecule.defaultBranchWidthCap]
  | gt => simp [compareCursorRule, hPair, hComp, RawMolecule.defaultBranchWidthCap]
  | eq => exact absurd (Nat.compare_eq_eq.mp hComp) hNe

/-- A strict atomic-number difference decides the uncapped authoritative rule comparator on a
singleton pair. -/
theorem compareCursorRuleAuthoritative?_rule1a_single_real (mol : RawMolecule)
    (before : CanonicalRerootCursor → CanonicalRerootCursor → Option Ordering)
    (fuel : ℕ) (left right : CanonicalRerootCursor)
    (hL : left.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hNe : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom) :
    compareCursorRuleAuthoritative? mol before RawMolecule.CanonicalRuleStage.rule1a (fuel + 1)
        [(left, right)] =
      some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
  have hPair := compareCursorPairLabelsAuthoritative?_rule1a_single_real mol left right hL hR
  cases hComp : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) with
  | lt => simp [compareCursorRuleAuthoritative?, hPair, hComp]
  | gt => simp [compareCursorRuleAuthoritative?, hPair, hComp]
  | eq => exact absurd (Nat.compare_eq_eq.mp hComp) hNe

/-! ## Branch-at comparison -/

/-- `compareCursorBranchAt` returns the strict atomic-number ordering at every fuel and stage. -/
theorem compareCursorBranchAt_eq_of_rule1a (mol : RawMolecule)
    (left right : CanonicalRerootCursor)
    (hL : left.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hNe : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom) :
    ∀ fuel stage, compareCursorBranchAt mol fuel stage left right =
      some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
  intro fuel
  cases fuel with
  | zero =>
      intro stage
      have hNode := compareCanonicalNodeRule?_rule1a_realAtom mol left.node right.node hL hR
      have strict : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) ≠
          Ordering.eq := fun h => hNe (Nat.compare_eq_eq.mp h)
      exact compareCanonicalNodeThrough?_eq_of_rule1a mol stage left.node right.node _ hNode strict
  | succ fuel =>
      intro stage
      have hRule := compareCursorRule_rule1a_single_real mol (compareCursorBranchAt mol fuel stage)
        fuel left right hL hR hNe
      cases hComp : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) with
      | lt => simp [compareCursorBranchAt, hRule, hComp]
      | gt => simp [compareCursorBranchAt, hRule, hComp]
      | eq => exact absurd (Nat.compare_eq_eq.mp hComp) hNe

/-- `compareCursorBranchAtAuthoritative?` returns the strict atomic-number ordering at every fuel
and stage. -/
theorem compareCursorBranchAtAuthoritative?_eq_of_rule1a (mol : RawMolecule)
    (left right : CanonicalRerootCursor)
    (hL : left.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hNe : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom) :
    ∀ fuel stage, compareCursorBranchAtAuthoritative? mol fuel stage left right =
      some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
  intro fuel
  cases fuel with
  | zero =>
      intro stage
      have hNode := compareCanonicalNodeRuleAuthoritative?_rule1a_realAtom mol left.node right.node
        hL hR
      have strict : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) ≠
          Ordering.eq := fun h => hNe (Nat.compare_eq_eq.mp h)
      exact compareCanonicalNodeThroughAuthoritative?_eq_of_rule1a mol stage left.node right.node _
        hNode strict
  | succ fuel =>
      intro stage
      have hRule := compareCursorRuleAuthoritative?_rule1a_single_real mol
        (compareCursorBranchAtAuthoritative? mol fuel stage) fuel left right hL hR hNe
      cases hComp : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) with
      | lt => simp [compareCursorBranchAtAuthoritative?, hRule, hComp]
      | gt => simp [compareCursorBranchAtAuthoritative?, hRule, hComp]
      | eq => exact absurd (Nat.compare_eq_eq.mp hComp) hNe

/-! ## The conservative automorphism conflict gate -/

/-- The legacy pairwise atom-automorphism conflict gate is impossible as soon as one endpoint is
acyclic at the comparison fuel.  The disjunction is load-bearing: for a *both-cyclic* pair the gate
may fire and this lemma does not apply (see `BothCyclic`). -/
theorem occurrenceRootsProvedAutomorphic_eq_false_of_acyclic (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (compiled : Ordering)
    (acyclic : mol.atomLiesInCycle fuel left.node.atom = false ∨
      mol.atomLiesInCycle fuel right.node.atom = false) :
    occurrenceRootsProvedAutomorphic mol fuel left right compiled = false := by
  rcases acyclic with h | h <;> cases compiled <;> simp [occurrenceRootsProvedAutomorphic, h]

/-! ## Certified constitutional stage and the complete callbacks -/

/-- The conservative production constitutional stage returns the raw strict ordering. -/
theorem certifiedConstitutionalStage?_eq_of_rule1a (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor)
    (hL : left.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hNe : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom)
    (acyclic : mol.atomLiesInCycle fuel left.node.atom = false ∨
      mol.atomLiesInCycle fuel right.node.atom = false) :
    certifiedConstitutionalStage? mol fuel left right =
      some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
  have hRaw := compareCursorBranchAt_eq_of_rule1a mol left right hL hR hNe fuel
    RawMolecule.CanonicalRuleStage.rule2
  have hGate := occurrenceRootsProvedAutomorphic_eq_false_of_acyclic mol fuel left right
    (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) acyclic
  simp [certifiedConstitutionalStage?, hRaw, hGate]

/-- The conservative authoritative constitutional stage returns the raw strict ordering. -/
theorem certifiedConstitutionalStageAuthoritative?_eq_of_rule1a (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor)
    (hL : left.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hNe : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom)
    (acyclic : mol.atomLiesInCycle fuel left.node.atom = false ∨
      mol.atomLiesInCycle fuel right.node.atom = false) :
    certifiedConstitutionalStageAuthoritative? mol fuel left right =
      some (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) := by
  have hRaw := compareCursorBranchAtAuthoritative?_eq_of_rule1a mol left right hL hR hNe fuel
    RawMolecule.CanonicalRuleStage.rule2
  have hGate := occurrenceRootsProvedAutomorphic_eq_false_of_acyclic mol fuel left right
    (compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom)) acyclic
  simp [certifiedConstitutionalStageAuthoritative?, hRaw, hGate]

/-- The complete fast occurrence callback returns the strict ordering with zero pseudo history. -/
theorem compareOccurrenceBranches?_eq_of_rule1a (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (left right : CanonicalRerootCursor)
    (hL : left.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hNe : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom)
    (acyclic : mol.atomLiesInCycle fuel left.node.atom = false ∨
      mol.atomLiesInCycle fuel right.node.atom = false) :
    compareOccurrenceBranches? mol state fuel left right =
      some { ordering := compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom),
             pseudo := false } := by
  have hCert := certifiedConstitutionalStage?_eq_of_rule1a mol fuel left right hL hR hNe acyclic
  have strict : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) ≠
      Ordering.eq := fun h => hNe (Nat.compare_eq_eq.mp h)
  cases hComp : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) with
  | lt => rw [hComp] at hCert; simp [compareOccurrenceBranches?, hCert]
  | gt => rw [hComp] at hCert; simp [compareOccurrenceBranches?, hCert]
  | eq => exact absurd hComp strict

/-- The complete authoritative occurrence callback returns the strict ordering with zero pseudo
history. -/
theorem compareOccurrenceBranchesAuthoritative?_eq_of_rule1a (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (left right : CanonicalRerootCursor)
    (hL : left.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hNe : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom)
    (acyclic : mol.atomLiesInCycle fuel left.node.atom = false ∨
      mol.atomLiesInCycle fuel right.node.atom = false) :
    compareOccurrenceBranchesAuthoritative? mol state fuel left right =
      some { ordering := compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom),
             pseudo := false } := by
  have hCert := certifiedConstitutionalStageAuthoritative?_eq_of_rule1a mol fuel left right hL hR
    hNe acyclic
  have strict : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) ≠
      Ordering.eq := fun h => hNe (Nat.compare_eq_eq.mp h)
  cases hComp : compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom) with
  | lt => rw [hComp] at hCert; simp [compareOccurrenceBranchesAuthoritative?, hCert]
  | gt => rw [hComp] at hCert; simp [compareOccurrenceBranchesAuthoritative?, hCert]
  | eq => exact absurd hComp strict

/-- The composed runtime callback (`fast` then `authoritative`) returns the strict ordering with
zero pseudo history. -/
theorem compareOccurrenceBranchesComplete?_eq_of_rule1a (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (left right : CanonicalRerootCursor)
    (hL : left.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hNe : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom)
    (acyclic : mol.atomLiesInCycle fuel left.node.atom = false ∨
      mol.atomLiesInCycle fuel right.node.atom = false) :
    compareOccurrenceBranchesComplete? mol state fuel left right =
      some { ordering := compare (mol.atomZAt left.node.atom) (mol.atomZAt right.node.atom),
             pseudo := false } := by
  simp [compareOccurrenceBranchesComplete?,
    compareOccurrenceBranches?_eq_of_rule1a mol state fuel left right hL hR hNe acyclic]

/-- Source-bounded composed runtime callback: under explicit materialized-atom bounds the strict
ordering is stated over the *actual* source atomic numbers recovered from the parsed molecule. -/
theorem compareOccurrenceBranchesComplete?_eq_of_rule1a_sourceBounded (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (left right : CanonicalRerootCursor)
    (hL : left.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hR : right.node.provenance = RawMolecule.CanonicalNodeProvenance.realAtom)
    (hNe : mol.atomZAt left.node.atom ≠ mol.atomZAt right.node.atom)
    (acyclic : mol.atomLiesInCycle fuel left.node.atom = false ∨
      mol.atomLiesInCycle fuel right.node.atom = false)
    (hLB : left.node.atom < mol.atomCount) (hRB : right.node.atom < mol.atomCount) :
    ∃ leftSpec rightSpec,
      mol.atomAt? left.node.atom = some leftSpec ∧ mol.atomAt? right.node.atom = some rightSpec ∧
        compareOccurrenceBranchesComplete? mol state fuel left right =
          some { ordering := compare leftSpec.element.atomicNumber rightSpec.element.atomicNumber,
                 pseudo := false } := by
  obtain ⟨leftSpec, leftObserved⟩ := atomAt?_exists_of_lt_atomCount mol left.node.atom hLB
  obtain ⟨rightSpec, rightObserved⟩ := atomAt?_exists_of_lt_atomCount mol right.node.atom hRB
  refine ⟨leftSpec, rightSpec, leftObserved, rightObserved, ?_⟩
  rw [compareOccurrenceBranchesComplete?_eq_of_rule1a mol state fuel left right hL hR hNe acyclic,
    atomZAt_eq_of_atomAt? mol left.node.atom leftSpec leftObserved,
    atomZAt_eq_of_atomAt? mol right.node.atom rightSpec rightObserved]

/-! ## Runtime tracked insertion and sort completeness -/

/-- Inserting a fresh-ranked cursor into a strictly descending tracked list succeeds, preserves the
multiset, keeps strict descending atomic-number order and records zero pseudo comparisons.  All
premises are independent structural properties of the input list. -/
theorem insertOccurrenceTrackedAuthoritative?_rankDomain (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) (candidate : CanonicalRerootCursor) :
    ∀ existing : List CanonicalRerootCursor,
      (candidate :: existing).Nodup →
      (∀ c ∈ candidate :: existing, RealOutsideCycle mol fuel c) →
      (∀ a ∈ candidate :: existing, ∀ b ∈ candidate :: existing,
        mol.atomZAt a.node.atom = mol.atomZAt b.node.atom → a = b) →
      existing.Pairwise (AtomicDesc mol) →
      ∃ result,
        insertOccurrenceTrackedAuthoritative? mol state fuel candidate existing = some result ∧
        result.1.Perm (candidate :: existing) ∧
        result.1.Pairwise (AtomicDesc mol) ∧
        result.2 = 0 := by
  intro existing
  induction existing with
  | nil =>
      intro _ _ _ _
      exact ⟨([candidate], 0), rfl, List.Perm.refl _, by simp, rfl⟩
  | cons head tail inductionHypothesis =>
      intro hNodup hRestr hInj hSorted
      have hNodupParts := List.nodup_cons.mp hNodup
      have hCandidateNotHead : candidate ∉ head :: tail := hNodupParts.1
      have hTailNodup : tail.Nodup := (List.nodup_cons.mp hNodupParts.2).2
      have hCandidateNotTail : candidate ∉ tail :=
        fun member => hCandidateNotHead (List.mem_cons_of_mem head member)
      have hSortedHead : ∀ x ∈ tail, AtomicDesc mol head x := (List.pairwise_cons.mp hSorted).1
      have hSortedTail : tail.Pairwise (AtomicDesc mol) := (List.pairwise_cons.mp hSorted).2
      have hSubNodup : (candidate :: tail).Nodup :=
        List.nodup_cons.mpr ⟨hCandidateNotTail, hTailNodup⟩
      have hSubRestr : ∀ c ∈ candidate :: tail, RealOutsideCycle mol fuel c := by
        intro c hc
        exact hRestr c (by
          rcases List.mem_cons.mp hc with same | other
          · exact List.mem_cons.mpr (Or.inl same)
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr other))))
      have hSubInj : ∀ a ∈ candidate :: tail, ∀ b ∈ candidate :: tail,
          mol.atomZAt a.node.atom = mol.atomZAt b.node.atom → a = b := by
        intro a ha b hb equal
        exact hInj a (by
          rcases List.mem_cons.mp ha with same | other
          · exact List.mem_cons.mpr (Or.inl same)
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr other))))
          b (by
          rcases List.mem_cons.mp hb with same | other
          · exact List.mem_cons.mpr (Or.inl same)
          · exact List.mem_cons.mpr (Or.inr (List.mem_cons.mpr (Or.inr other)))) equal
      obtain ⟨⟨insertedList, insertedCount⟩, hInsertedComputed, hInsertedPerm, hInsertedSorted,
        hInsertedZero⟩ :=
        inductionHypothesis hSubNodup hSubRestr hSubInj hSortedTail
      have hCandidateReal := hRestr candidate (by simp)
      have hHeadReal := hRestr head (by simp)
      have hDistinct : mol.atomZAt candidate.node.atom ≠ mol.atomZAt head.node.atom := by
        intro equal
        exact hCandidateNotHead (by
          have same : candidate = head := hInj candidate (by simp) head (by simp) equal
          rw [same]
          exact List.mem_cons_self)
      have hAcyclic : mol.atomLiesInCycle fuel candidate.node.atom = false ∨
          mol.atomLiesInCycle fuel head.node.atom = false := Or.inl hCandidateReal.2.2
      have hDecision := compareOccurrenceBranchesComplete?_eq_of_rule1a mol state fuel candidate head
        hCandidateReal.1 hHeadReal.1 hDistinct hAcyclic
      cases hComp : compare (mol.atomZAt candidate.node.atom) (mol.atomZAt head.node.atom) with
      | lt =>
          have hDecision' : compareOccurrenceBranchesComplete? mol state fuel candidate head =
              some { ordering := Ordering.lt, pseudo := false } := by
            simpa [hComp] using hDecision
          refine ⟨(head :: insertedList, 0 + insertedCount), ?_, ?_, ?_, ?_⟩
          · simp [insertOccurrenceTrackedAuthoritative?, hDecision', hInsertedComputed]
          · exact (List.Perm.cons head hInsertedPerm).trans (List.Perm.swap candidate head tail)
          · refine List.pairwise_cons.mpr ⟨?_, hInsertedSorted⟩
            intro other hOther
            have hOtherMem := hInsertedPerm.mem_iff.mp hOther
            rcases List.mem_cons.mp hOtherMem with same | inTail
            · rw [same]; exact Nat.compare_eq_lt.mp hComp
            · exact hSortedHead other inTail
          · change 0 + insertedCount = 0
            exact (Nat.zero_add insertedCount).trans hInsertedZero
      | gt =>
          have hDecision' : compareOccurrenceBranchesComplete? mol state fuel candidate head =
              some { ordering := Ordering.gt, pseudo := false } := by
            simpa [hComp] using hDecision
          refine ⟨(candidate :: head :: tail, 0), ?_, List.Perm.refl _, ?_, rfl⟩
          · simp [insertOccurrenceTrackedAuthoritative?, hDecision']
          · refine List.pairwise_cons.mpr ⟨?_, hSorted⟩
            intro other hOther
            rcases List.mem_cons.mp hOther with same | inTail
            · rw [same]; exact Nat.compare_eq_gt.mp hComp
            · exact Nat.lt_trans (hSortedHead other inTail) (Nat.compare_eq_gt.mp hComp)
      | eq => exact absurd (Nat.compare_eq_eq.mp hComp) hDistinct

/-- The runtime tracked occurrence sorter permutes any `Nodup` cursor list from the independent
real-acyclic domain into strict descending atomic-number order with zero pseudo comparisons. -/
theorem sortOccurrencesTrackedAuthoritative?_rankDomain (mol : RawMolecule)
    (state : OccurrenceAuxState) (fuel : ℕ) :
    ∀ cursors : List CanonicalRerootCursor,
      cursors.Nodup →
      (∀ c ∈ cursors, RealOutsideCycle mol fuel c) →
      (∀ a ∈ cursors, ∀ b ∈ cursors,
        mol.atomZAt a.node.atom = mol.atomZAt b.node.atom → a = b) →
      ∃ result,
        sortOccurrencesTrackedAuthoritative? mol state fuel cursors = some result ∧
        result.1.Perm cursors ∧
        result.1.Pairwise (AtomicDesc mol) ∧
        result.2 = 0 := by
  intro cursors
  induction cursors with
  | nil =>
      intro _ _ _
      exact ⟨([], 0), rfl, List.Perm.refl _, by simp, rfl⟩
  | cons cursor cursors inductionHypothesis =>
      intro hNodup hRestr hInj
      have hNodupParts := List.nodup_cons.mp hNodup
      have hCursorNotCursors : cursor ∉ cursors := hNodupParts.1
      have hCursorsNodup : cursors.Nodup := hNodupParts.2
      have hSubRestr : ∀ c ∈ cursors, RealOutsideCycle mol fuel c :=
        fun c member => hRestr c (List.mem_cons_of_mem cursor member)
      have hSubInj : ∀ a ∈ cursors, ∀ b ∈ cursors,
          mol.atomZAt a.node.atom = mol.atomZAt b.node.atom → a = b :=
        fun a ha b hb equal => hInj a (List.mem_cons_of_mem cursor ha)
          b (List.mem_cons_of_mem cursor hb) equal
      obtain ⟨⟨sortedList, sortedCount⟩, hSortedListComputed, hSortedListPerm, hSortedListSorted,
        hSortedListZero⟩ :=
        inductionHypothesis hCursorsNodup hSubRestr hSubInj
      have hCursorNotSorted : cursor ∉ sortedList :=
        fun member => hCursorNotCursors (hSortedListPerm.mem_iff.mp member)
      have hSortedListNodup : sortedList.Nodup := hSortedListPerm.nodup_iff.mpr hCursorsNodup
      have hInsertNodup : (cursor :: sortedList).Nodup :=
        List.nodup_cons.mpr ⟨hCursorNotSorted, hSortedListNodup⟩
      have hInsertRestr : ∀ c ∈ cursor :: sortedList, RealOutsideCycle mol fuel c := by
        intro c hc
        rcases List.mem_cons.mp hc with same | inSorted
        · exact hRestr c (List.mem_cons.mpr (Or.inl same))
        · exact hRestr c (List.mem_cons.mpr (Or.inr (hSortedListPerm.mem_iff.mp inSorted)))
      have hInsertInj : ∀ a ∈ cursor :: sortedList, ∀ b ∈ cursor :: sortedList,
          mol.atomZAt a.node.atom = mol.atomZAt b.node.atom → a = b := by
        intro a ha b hb equal
        exact hInj a (by
          rcases List.mem_cons.mp ha with same | inSorted
          · exact List.mem_cons.mpr (Or.inl same)
          · exact List.mem_cons.mpr (Or.inr (hSortedListPerm.mem_iff.mp inSorted)))
          b (by
          rcases List.mem_cons.mp hb with same | inSorted
          · exact List.mem_cons.mpr (Or.inl same)
          · exact List.mem_cons.mpr (Or.inr (hSortedListPerm.mem_iff.mp inSorted))) equal
      obtain ⟨⟨insertedList, insertedCount⟩, hInsertComputed, hInsertPerm, hInsertSorted,
        hInsertZero⟩ :=
        insertOccurrenceTrackedAuthoritative?_rankDomain mol state fuel cursor sortedList
          hInsertNodup hInsertRestr hInsertInj hSortedListSorted
      refine ⟨(insertedList, sortedCount + insertedCount), ?_, ?_, ?_, ?_⟩
      · simp [sortOccurrencesTrackedAuthoritative?, hSortedListComputed, hInsertComputed]
      · exact hInsertPerm.trans (List.Perm.cons cursor hSortedListPerm)
      · exact hInsertSorted
      · have sortedZero : sortedCount = 0 := hSortedListZero
        have insertedZero : insertedCount = 0 := hInsertZero
        change sortedCount + insertedCount = 0
        rw [sortedZero, insertedZero]

end TetraStereo.UniversalProof.NativeRawAtomicNumberProofs.RuntimeAtomicPriorityRecovery
