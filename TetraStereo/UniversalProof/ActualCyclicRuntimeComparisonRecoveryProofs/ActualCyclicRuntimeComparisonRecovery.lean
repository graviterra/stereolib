import TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery
import TetraStereo.OneCenter.CIPRule2MassData

set_option autoImplicit false
set_option maxRecDepth 10000

namespace TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.UniversalProof.NativeRawRecordBoundsProofs.GeneratedRuntimeRootRecovery














































/-! ## 1. Exact boundary of the conservative automorphism-conflict gate -/




def BothCyclic (mol : RawMolecule) (fuel : ℕ) (left right : CanonicalRerootCursor) : Prop :=
  mol.atomLiesInCycle fuel left.node.atom = true ∧
    mol.atomLiesInCycle fuel right.node.atom = true

/-- Two occurrence cursors carry the same actual atomic number.  This is the exact complement of the
strictness premise every Rule-1a bridge uses; it is an exclusion boundary, not a stereogenicity
claim. -/
def TiedAtomicNumber (mol : RawMolecule) (left right : CanonicalRerootCursor) : Prop :=
  mol.atomZAt left.node.atom = mol.atomZAt right.node.atom

/-- The necessary condition for the conservative automorphism-conflict gate to be able to return
`true`: a strict constitutional result (`compiled ≠ Ordering.eq`) at a both-cyclic pair.  This is a
necessary condition only; the gate also requires the shared generated reference frame, so the
converse is not asserted. -/
def GateCanFire (mol : RawMolecule) (fuel : ℕ) (left right : CanonicalRerootCursor)
    (compiled : Ordering) : Prop :=
  compiled ≠ Ordering.eq ∧ BothCyclic mol fuel left right




theorem bothCyclic_iff_not_acyclicDisjunction (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) :
    BothCyclic mol fuel left right ↔
      ¬ (mol.atomLiesInCycle fuel left.node.atom = false ∨
        mol.atomLiesInCycle fuel right.node.atom = false) := by
  unfold BothCyclic
  cases hl : mol.atomLiesInCycle fuel left.node.atom <;>
    cases hr : mol.atomLiesInCycle fuel right.node.atom <;>
      simp

/-- The gate is `false` at a tied constitutional result, for every pair and comparison fuel, with no
acyclicity premise.  The first conjunct of the gate body is definitionally `false` here. -/
theorem occurrenceRootsProvedAutomorphic_eq_false_of_compiled_eq (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) :
    occurrenceRootsProvedAutomorphic mol fuel left right Ordering.eq = false := by
  have h : (Ordering.eq != Ordering.eq) = false := by decide
  unfold occurrenceRootsProvedAutomorphic
  rw [h]
  simp



theorem occurrenceRootsProvedAutomorphic_eq_false_of_acyclic (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (compiled : Ordering)
    (acyclic : mol.atomLiesInCycle fuel left.node.atom = false ∨
      mol.atomLiesInCycle fuel right.node.atom = false) :
    occurrenceRootsProvedAutomorphic mol fuel left right compiled = false := by
  rcases acyclic with h | h <;> cases compiled <;> simp [occurrenceRootsProvedAutomorphic, h]

/-- Exact necessary condition: the gate can be `true` only when both endpoints are cyclic. -/
theorem occurrenceRootsProvedAutomorphic_eq_true_implies_bothCyclic (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (compiled : Ordering)
    (accepted : occurrenceRootsProvedAutomorphic mol fuel left right compiled = true) :
    BothCyclic mol fuel left right := by
  have leftTrue : mol.atomLiesInCycle fuel left.node.atom = true := by
    cases hL : mol.atomLiesInCycle fuel left.node.atom with
    | true => rfl
    | false =>
        rw [occurrenceRootsProvedAutomorphic_eq_false_of_acyclic mol fuel left right compiled
          (Or.inl hL)] at accepted
        cases accepted
  have rightTrue : mol.atomLiesInCycle fuel right.node.atom = true := by
    cases hR : mol.atomLiesInCycle fuel right.node.atom with
    | true => rfl
    | false =>
        rw [occurrenceRootsProvedAutomorphic_eq_false_of_acyclic mol fuel left right compiled
          (Or.inr hR)] at accepted
        cases accepted
  exact ⟨leftTrue, rightTrue⟩

/-- Exact necessary condition: the gate can be `true` only at a strict constitutional result. -/
theorem occurrenceRootsProvedAutomorphic_eq_true_implies_compiled_ne_eq (mol : RawMolecule)
    (fuel : ℕ) (left right : CanonicalRerootCursor) (compiled : Ordering)
    (accepted : occurrenceRootsProvedAutomorphic mol fuel left right compiled = true) :
    compiled ≠ Ordering.eq := by
  intro heq
  rw [heq] at accepted
  rw [occurrenceRootsProvedAutomorphic_eq_false_of_compiled_eq mol fuel left right] at accepted
  cases accepted

/-- Packaged necessary condition: a `true` gate lies inside `GateCanFire`. -/
theorem occurrenceRootsProvedAutomorphic_eq_true_implies_gateCanFire (mol : RawMolecule)
    (fuel : ℕ) (left right : CanonicalRerootCursor) (compiled : Ordering)
    (accepted : occurrenceRootsProvedAutomorphic mol fuel left right compiled = true) :
    GateCanFire mol fuel left right compiled :=
  ⟨occurrenceRootsProvedAutomorphic_eq_true_implies_compiled_ne_eq mol fuel left right compiled
      accepted,
    occurrenceRootsProvedAutomorphic_eq_true_implies_bothCyclic mol fuel left right compiled
      accepted⟩




theorem certifiedConstitutionalStage?_eq_of_gate_false (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor) (decision : Ordering)
    (raw : compareCursorBranchAt mol fuel RawMolecule.CanonicalRuleStage.rule2 left right =
      some decision)
    (gate : occurrenceRootsProvedAutomorphic mol fuel left right decision = false) :
    certifiedConstitutionalStage? mol fuel left right = some decision := by
  simp [certifiedConstitutionalStage?, raw, gate]

/-- General factorization of the uncapped authoritative conservative stage. -/
theorem certifiedConstitutionalStageAuthoritative?_eq_of_gate_false (mol : RawMolecule)
    (fuel : ℕ) (left right : CanonicalRerootCursor) (decision : Ordering)
    (raw : compareCursorBranchAtAuthoritative? mol fuel RawMolecule.CanonicalRuleStage.rule2
      left right = some decision)
    (gate : occurrenceRootsProvedAutomorphic mol fuel left right decision = false) :
    certifiedConstitutionalStageAuthoritative? mol fuel left right = some decision := by
  simp [certifiedConstitutionalStageAuthoritative?, raw, gate]

/-- Tied-result pass-through on the fast path: at a tied raw constitutional result the conservative
gate cannot refuse, for arbitrary endpoint cyclicity. -/
theorem certifiedConstitutionalStage?_eq_of_constitutional_eq (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor)
    (raw : compareCursorBranchAt mol fuel RawMolecule.CanonicalRuleStage.rule2 left right =
      some Ordering.eq) :
    certifiedConstitutionalStage? mol fuel left right = some Ordering.eq :=
  certifiedConstitutionalStage?_eq_of_gate_false mol fuel left right Ordering.eq raw
    (occurrenceRootsProvedAutomorphic_eq_false_of_compiled_eq mol fuel left right)

/-- Tied-result pass-through on the uncapped authoritative path: the same tied-result passthrough
with no acyclicity premise. -/
theorem certifiedConstitutionalStageAuthoritative?_eq_of_constitutional_eq (mol : RawMolecule)
    (fuel : ℕ) (left right : CanonicalRerootCursor)
    (raw : compareCursorBranchAtAuthoritative? mol fuel RawMolecule.CanonicalRuleStage.rule2
      left right = some Ordering.eq) :
    certifiedConstitutionalStageAuthoritative? mol fuel left right = some Ordering.eq :=
  certifiedConstitutionalStageAuthoritative?_eq_of_gate_false mol fuel left right Ordering.eq raw
    (occurrenceRootsProvedAutomorphic_eq_false_of_compiled_eq mol fuel left right)

/-- The fast conservative stage cannot refuse at a successful raw Rule-2 tie. -/
theorem certifiedConstitutionalStage?_ne_none_of_constitutional_eq (mol : RawMolecule) (fuel : ℕ)
    (left right : CanonicalRerootCursor)
    (raw : compareCursorBranchAt mol fuel RawMolecule.CanonicalRuleStage.rule2 left right =
      some Ordering.eq) :
    certifiedConstitutionalStage? mol fuel left right ≠ none := by
  rw [certifiedConstitutionalStage?_eq_of_constitutional_eq mol fuel left right raw]
  simp

/-- The uncapped authoritative stage cannot refuse at a successful raw Rule-2 tie. -/
theorem certifiedConstitutionalStageAuthoritative?_ne_none_of_constitutional_eq (mol : RawMolecule)
    (fuel : ℕ) (left right : CanonicalRerootCursor)
    (raw : compareCursorBranchAtAuthoritative? mol fuel RawMolecule.CanonicalRuleStage.rule2
      left right = some Ordering.eq) :
    certifiedConstitutionalStageAuthoritative? mol fuel left right ≠ none := by
  rw [certifiedConstitutionalStageAuthoritative?_eq_of_constitutional_eq mol fuel left right raw]
  simp

/-! ## 2. A concrete tied / both-cyclic actual-source witness

The witness is a three-membered all-single-bond carbon ring.  Its actual production runtime
generation at the ring atom already produces two **real**, **in-bound**, **both-cyclic** and
**atomic-number-tied** cursors, so the target boundary is inhabited by an actual source rather than
by a supplied comparator equation.
-/

/-- Stated finite comparison fuel for the witness.  It exceeds the ring length, so the actual
`ringPairCount`/`reachableAvoiding` cycle test fires; this is a *finite-fuel* cycle test, not
unrestricted graph classification. -/
def witnessFuel : ℕ := 3

/-- Three carbons joined by three ordinary single bonds (a ring).  No hydrogens and no tetrahedral
annotation are written: the witness is a comparator-level constitutional ring, not a stereocentre. -/
def ringWitness : RawMolecule where
  atoms := [AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C, AtomSpec.aliphatic Element.C]
  bonds := [{ source := 0, target := 1, kind := ParsedBondKind.single },
            { source := 1, target := 2, kind := ParsedBondKind.single },
            { source := 2, target := 0, kind := ParsedBondKind.single }]

/-- The two actual generated runtime root nodes: the ring neighbours of the ring atom `0`.  They are
exactly the production `canonicalRoot`s of the center, not detached nodes chosen by a caller. -/
def nodeLeft : CanonicalBranchNode := canonicalRoot 0 1
def nodeRight : CanonicalBranchNode := canonicalRoot 0 2

/-- The two actual generated runtime cursors of the ring atom `0`, carrying the real previous
reference root. -/
def leftCursor : CanonicalRerootCursor :=
  { node := nodeLeft, previous? := some (canonicalCenterRoot 0) }
def rightCursor : CanonicalRerootCursor :=
  { node := nodeRight, previous? := some (canonicalCenterRoot 0) }

theorem ringWitness_atomCount : ringWitness.atomCount = 3 := by decide +kernel

/-- The witness satisfies the basic admission contract. -/
theorem ringWitness_wellFormed : ringWitness.WellFormed := by
  rw [wellFormed_iff_all_bondEndpointsOK]
  decide +kernel

theorem ringWitness_bondRecordsUnique : ringWitness.BondRecordsUnique :=
  (bondRecordsUnique?_eq_true_iff ringWitness).mp (by decide +kernel)

theorem ringWitness_admissible : ringWitness.Admissible :=
  ⟨ringWitness_wellFormed, ringWitness_bondRecordsUnique⟩

/-- The written-neighbour view is exact, so the witness is a `StereochemicalAdmissible` raw
source and not a hand-crafted view with invented or omitted ligands. -/
theorem ringWitness_writtenNeighborExact : ringWitness.WrittenNeighborExact := by
  unfold RawMolecule.WrittenNeighborExact
  decide +kernel

theorem ringWitness_stereochemicalAdmissible : ringWitness.StereochemicalAdmissible :=
  ⟨ringWitness_admissible, ringWitness_writtenNeighborExact⟩

/-! ### Actual generated runtime roots -/

/-- The actual production runtime generator returns exactly the two ring-neighbour cursors. -/
theorem ringWitness_runtime_roots :
    generatedRuntimeRoots ringWitness 0 = [leftCursor, rightCursor] := by
  decide +kernel

/-- The left runtime cursor denotes a real source atom, at an in-bound index, and its materialized
specification is an ordinary aliphatic carbon. -/
theorem ringWitness_left_meaning :
    leftCursor.node.provenance = CanonicalNodeProvenance.realAtom ∧
      leftCursor.node.atom < ringWitness.atomCount ∧
      ringWitness.atomAt? leftCursor.node.atom = some (AtomSpec.aliphatic Element.C) ∧
      ringWitness.atomZAt leftCursor.node.atom = 6 :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- The right runtime cursor has the same real, in-bound, ordinary-carbon meaning. -/
theorem ringWitness_right_meaning :
    rightCursor.node.provenance = CanonicalNodeProvenance.realAtom ∧
      rightCursor.node.atom < ringWitness.atomCount ∧
      ringWitness.atomAt? rightCursor.node.atom = some (AtomSpec.aliphatic Element.C) ∧
      ringWitness.atomZAt rightCursor.node.atom = 6 :=
  ⟨rfl, by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ### Actual cycle generation and the atomic-number tie -/

theorem ringWitness_incidentAtoms_left : ringWitness.incidentAtoms leftCursor.node.atom = [0, 2] := by
  decide +kernel

/-- The actual finite path search that witnesses the ring through the left atom. -/
theorem ringWitness_reachable_avoiding_left :
    ringWitness.reachableAvoiding witnessFuel leftCursor.node.atom
        [0] [0] = [0, 2] := by
  decide +kernel

/-- The actual `ringPairCount` of the left atom is one: its two ring neighbours are joined by a path
avoiding the atom. -/
theorem ringWitness_ringPairCount_left :
    ringWitness.ringPairCount witnessFuel leftCursor.node.atom
        (ringWitness.incidentAtoms leftCursor.node.atom) = 1 := by
  decide +kernel

/-- The actual production cycle test is `true` at the stated fuel for the left cursor atom. -/
theorem ringWitness_atomLiesInCycle_left :
    ringWitness.atomLiesInCycle witnessFuel leftCursor.node.atom = true := by
  decide +kernel

/-- The actual production cycle test is `true` at the stated fuel for the right cursor atom. -/
theorem ringWitness_atomLiesInCycle_right :
    ringWitness.atomLiesInCycle witnessFuel rightCursor.node.atom = true := by
  decide +kernel

/-- The concrete witness pair is both cyclic at the stated fuel. -/
theorem ringWitness_bothCyclic : BothCyclic ringWitness witnessFuel leftCursor rightCursor :=
  ⟨ringWitness_atomLiesInCycle_left, ringWitness_atomLiesInCycle_right⟩



theorem ringWitness_atomZAt_tie : TiedAtomicNumber ringWitness leftCursor rightCursor := by
  unfold TiedAtomicNumber
  decide +kernel

/-- Both Rule-2 mass data are the frozen carbon ordinary-weight lookup, evaluated on the actual
materialized carbon specifications. -/
theorem ringWitness_mass_frozen :
    ringWitness.atomMassAt leftCursor.node.atom =
        (CIPRule2MassData.rule2MassPico? 6 none).getD 0 ∧
      ringWitness.atomMassAt rightCursor.node.atom =
        (CIPRule2MassData.rule2MassPico? 6 none).getD 0 :=
  ⟨by decide +kernel, by decide +kernel⟩

/-! ### Derived actual gate, stage and protocol results -/

/-- The actual conservative gate cannot refuse the tied witness pair at the tied compiled value. -/
theorem ringWitness_gate_at_tie :
    occurrenceRootsProvedAutomorphic ringWitness witnessFuel leftCursor rightCursor Ordering.eq =
      false :=
  occurrenceRootsProvedAutomorphic_eq_false_of_compiled_eq ringWitness witnessFuel leftCursor
    rightCursor

/-- The actual raw fast Rule-2 constitutional comparison of the tied both-cyclic witness pair ties.
This is *derived* by evaluating the production comparator, not assumed and not inferred from the
atomic-number tie alone. -/
theorem ringWitness_raw_fast :
    compareCursorBranchAt ringWitness witnessFuel RawMolecule.CanonicalRuleStage.rule2 leftCursor
        rightCursor = some Ordering.eq := by
  decide +kernel

/-- The actual raw uncapped authoritative Rule-2 constitutional comparison ties as well. -/
theorem ringWitness_raw_authoritative :
    compareCursorBranchAtAuthoritative? ringWitness witnessFuel RawMolecule.CanonicalRuleStage.rule2
        leftCursor rightCursor = some Ordering.eq := by
  decide +kernel

/-- Actual fast certified-stage result at the tied both-cyclic pair: the conservative production
constitutional stage returns the raw tie rather than refusing. -/
theorem ringWitness_certifiedStage :
    certifiedConstitutionalStage? ringWitness witnessFuel leftCursor rightCursor = some Ordering.eq :=
  certifiedConstitutionalStage?_eq_of_constitutional_eq ringWitness witnessFuel leftCursor
    rightCursor ringWitness_raw_fast

/-- Actual uncapped authoritative certified-stage result at the same pair. -/
theorem ringWitness_certifiedStageAuthoritative :
    certifiedConstitutionalStageAuthoritative? ringWitness witnessFuel leftCursor rightCursor =
      some Ordering.eq :=
  certifiedConstitutionalStageAuthoritative?_eq_of_constitutional_eq ringWitness witnessFuel
    leftCursor rightCursor ringWitness_raw_authoritative

theorem ringWitness_certifiedStage_ne_none :
    certifiedConstitutionalStage? ringWitness witnessFuel leftCursor rightCursor ≠ none := by
  rw [ringWitness_certifiedStage]
  simp

theorem ringWitness_certifiedStageAuthoritative_ne_none :
    certifiedConstitutionalStageAuthoritative? ringWitness witnessFuel leftCursor rightCursor ≠
      none := by
  rw [ringWitness_certifiedStageAuthoritative]
  simp

/-- Composed fast protocol outcome on the actual tied both-cyclic pair at the empty auxiliary
descriptor state: the tied constitutional boundary now proceeds through the descriptor stages to a
tied, non-pseudo result instead of being withheld by the legacy gate. -/
theorem ringWitness_fast_protocol :
    compareOccurrenceBranches? ringWitness ([] : OccurrenceAuxState) witnessFuel leftCursor
        rightCursor = some ({ ordering := Ordering.eq, pseudo := false } :
          OccurrenceComparison) := by
  decide +kernel

/-- The composed `fast`-then-`authoritative` entry point returns the same outcome, because the fast
path already succeeds; the authoritative fallback is never consulted. -/
theorem ringWitness_complete_protocol :
    compareOccurrenceBranchesComplete? ringWitness ([] : OccurrenceAuxState) witnessFuel leftCursor
        rightCursor = some ({ ordering := Ordering.eq, pseudo := false } :
          OccurrenceComparison) := by
  simp [compareOccurrenceBranchesComplete?, ringWitness_fast_protocol]

/-! ## 3. Precise actual API obstruction: the checked clean class excludes the target -/






theorem checked151_domain_excludes_cyclic_neighbors {molecule : RawMolecule} {center : ℕ}
    (domain : LeafNeighborDomain molecule center) {atom : ℕ}
    (member : atom ∈ recordNeighbors molecule center) (fuel : ℕ) :
    molecule.atomLiesInCycle fuel atom = false :=
  atomLiesInCycle_false_of_degree_le_one molecule atom fuel (domain.leaf member)

end TetraStereo.UniversalProof.ActualCyclicRuntimeComparisonRecoveryProofs.ActualCyclicRuntimeComparisonRecovery
