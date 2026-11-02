import TetraStereo.OneCenter.OfficialCIPEngine
import TetraStereo.OneCenter.OfficialHierarchicalDigraph
import TetraStereo.OneCenter.OfficialRuleMajorKey
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter



























































/-! ## The named legacy layer-major implementation

This section is the exact predecessor computation.  It is the old `cipOfficialCompareWithFuel` /
`cipOfficialCompare` pair from `input_context/OfficialCIPEngine.lean`, renamed so that no
declaration can be mistaken for the corrected public engine, together with the comparison-only
part of the old engine result structure (the historical claims concern the certificate and its
outcome; the corrected engine owns the order/permutation surface). -/

namespace OneCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Legacy predecessor layer-major comparison with explicit fuel.

Exact predecessor body: the official hierarchical digraph is compared sphere by sphere, with
Rules 1a, 1b and 2 interleaved per node pair inside each sphere, followed by the official
Rule 3/4/5 context fallthrough only when the digraph trace ties.  This is *not* the corrected
rule-major public comparator. -/
noncomputable def cipOfficialCompareLayerMajorWithFuel (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (fuel : ℕ)
    (i j : Fin 4) : CIPTraceCertificate :=
  m.cipOfficialHierarchicalDigraphCompareWithContext context fuel i j

/-- Legacy predecessor layer-major comparison at the predecessor default fuel
`Fintype.card V + 1`. -/
noncomputable def cipOfficialCompareLayerMajor (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (i j : Fin 4) : CIPTraceCertificate :=
  m.cipOfficialCompareLayerMajorWithFuel context (Fintype.card V + 1) i j



theorem cipOfficialCompareLayerMajorWithFuel_eq_legacyHelper (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (fuel : ℕ) (i j : Fin 4) :
    m.cipOfficialCompareLayerMajorWithFuel context fuel i j =
      m.cipOfficialHierarchicalDigraphCompareWithContext context fuel i j :=
  rfl

/-- The legacy comparator at its default fuel is the retained default helper, definitionally.
This is the predecessor analogue of the old `cipOfficialCompare_eq_hierarchicalDefault`. -/
@[simp] theorem cipOfficialCompareLayerMajor_eq_hierarchicalDefault (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) :
    m.cipOfficialCompareLayerMajor context i j =
      m.cipOfficialHierarchicalDigraphCompareWithContextDefault context i j :=
  rfl

/-- A ligand atom is never the stereocenter.  Retained locally so that the legacy stability
proofs do not depend on whether the corrected engine keeps the old helper of the same shape. -/
theorem cipOfficialCompareLayerMajor_ligandAtom_ne_center
    (m : OneCenterMolecule V) (i : Fin 4) : m.ligandAtom i ≠ m.center := by
  intro h
  have hadj := m.ligandAtom_adj i
  simp [MoleculeGraph.Adj, h, m.mol.bond_self] at hadj

/-- Trace-level stability of the legacy layer-major comparison beyond the predecessor default
fuel.  Same statement and proof shape as the frozen predecessor theorem. -/
theorem cipOfficialCompareLayerMajorWithFuel_trace_stable_default (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) (extra : ℕ) :
    (m.cipOfficialCompareLayerMajorWithFuel context ((Fintype.card V + 1) + extra) i j).trace =
      (m.cipOfficialCompareLayerMajor context i j).trace := by
  have htrace :=
    m.mol.compareOfficialHierarchicalDigraphTrace_rootFromEdge_stable_default
      (center := m.center) (left := m.ligandAtom i) (right := m.ligandAtom j)
      (m.cipOfficialCompareLayerMajor_ligandAtom_ne_center i)
      (m.cipOfficialCompareLayerMajor_ligandAtom_ne_center j) extra
  simpa [cipOfficialCompareLayerMajorWithFuel, cipOfficialCompareLayerMajor,
    cipOfficialHierarchicalDigraphCompareWithContext,
    MoleculeGraph.compareOfficialHierarchicalDigraphThenContextFrom,
    CIPRuleEngine.compareDigraphThenOfficialCertificate] using
    congrArg
      (fun trace =>
        CIPRuleEngine.compareDigraphThenOfficialTrace trace (context i) (context j))
      htrace

/-- Outcome-level stability of the legacy layer-major comparison beyond the predecessor default
fuel. -/
theorem cipOfficialCompareLayerMajorWithFuel_outcome_stable_default (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) (extra : ℕ) :
    (m.cipOfficialCompareLayerMajorWithFuel context ((Fintype.card V + 1) + extra) i j).outcome =
      (m.cipOfficialCompareLayerMajor context i j).outcome := by
  have htrace :=
    m.cipOfficialCompareLayerMajorWithFuel_trace_stable_default context i j extra
  simpa [CIPTraceCertificate.ofTrace, cipOfficialCompareLayerMajorWithFuel,
    cipOfficialCompareLayerMajor, cipOfficialHierarchicalDigraphCompareWithContext,
    MoleculeGraph.compareOfficialHierarchicalDigraphThenContextFrom,
    CIPRuleEngine.compareDigraphThenOfficialCertificate] using congrArg cipTraceOutcome htrace

/-- Comparison-only projection of the predecessor engine result.  The frozen predecessor also
carried order / permutation / safe-order fields; those are intentionally not re-instantiated
here because the historical regression concerns the comparison certificate and its outcome, and
the corrected engine owns the current order surface. -/
structure LegacyOfficialCIPEngineResult (m : OneCenterMolecule V) where
  context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext
  compare : Fin 4 → Fin 4 → CIPTraceCertificate
  stableTrace :
    ∀ i j extra,
      (m.cipOfficialCompareLayerMajorWithFuel context ((Fintype.card V + 1) + extra)
        i j).trace = (compare i j).trace
  stableOutcome :
    ∀ i j extra,
      (m.cipOfficialCompareLayerMajorWithFuel context ((Fintype.card V + 1) + extra)
        i j).outcome = (compare i j).outcome

/-- Run the legacy predecessor layer-major comparison engine. -/
noncomputable def cipOfficialEngineLayerMajor (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    LegacyOfficialCIPEngineResult m where
  context := context
  compare := m.cipOfficialCompareLayerMajor context
  stableTrace := by
    intro i j extra
    exact m.cipOfficialCompareLayerMajorWithFuel_trace_stable_default context i j extra
  stableOutcome := by
    intro i j extra
    exact m.cipOfficialCompareLayerMajorWithFuel_outcome_stable_default context i j extra

@[simp] theorem cipOfficialEngineLayerMajor_context (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    (m.cipOfficialEngineLayerMajor context).context = context :=
  rfl

@[simp] theorem cipOfficialEngineLayerMajor_compare (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) :
    (m.cipOfficialEngineLayerMajor context).compare i j =
      m.cipOfficialCompareLayerMajor context i j :=
  rfl

end OneCenterMolecule

namespace OfficialEngineRulePrecedenceFidelity

/-! ## The admitted witness graph (retained unchanged) -/

/-- Atomic numbers of the eleven witness atoms. -/
def witnessAtomZ (atom : Fin 11) : AtomicNumber :=
  match atom.val with
  | 0 => 6
  | 1 => 35
  | 2 => 17
  | 3 => 6
  | 4 => 6
  | 5 => 9
  | 6 => 1
  | 7 => 1
  | 8 => 1
  | 9 => 1
  | _ => 1

/-- Rule-2 mass observations of the eleven witness atoms (mass numbers). -/
def witnessAtomMass (atom : Fin 11) : ℕ :=
  match atom.val with
  | 0 => 12
  | 1 => 79
  | 2 => 35
  | 3 => 13
  | 4 => 12
  | 5 => 19
  | _ => 1

/-- The ten single bonds of the witness.  The list is symmetric by construction in
`witnessBond`. -/
def witnessBondPairs : List (Fin 11 × Fin 11) :=
  [(0, 1), (0, 2), (0, 3), (0, 4),
   (3, 6), (3, 7), (3, 8),
   (4, 5), (4, 9), (4, 10)]

/-- Symmetric bond-order matrix: all witness bonds are single, everything else is zero. -/
def witnessBond (left right : Fin 11) : BondOrder :=
  if left = right then 0
  else if (left, right) ∈ witnessBondPairs ∨ (right, left) ∈ witnessBondPairs then 1
  else 0

theorem witnessBond_symm (left right : Fin 11) :
    witnessBond left right = witnessBond right left := by
  by_cases same : left = right
  · subst right
    rfl
  · have reverse : right ≠ left := fun equality => same equality.symm
    simp [witnessBond, same, reverse, or_comm]

theorem witnessBond_self (atom : Fin 11) : witnessBond atom atom = 0 := by
  simp [witnessBond]

/-- The admitted raw molecular graph of the witness. -/
def witnessGraph : MoleculeGraph (Fin 11) where
  atomZ := witnessAtomZ
  atomMass := witnessAtomMass
  bond := witnessBond
  bond_symm := witnessBond_symm
  bond_self := witnessBond_self

/-- Ligand index `i` names the atom at position `i + 1`: Br, Cl, ^13CH3, ^12CH2F. -/
def witnessLigand (index : Fin 4) : Fin 11 :=
  ⟨index.val + 1, by have := index.isLt; omega⟩

@[simp] theorem witnessLigand_zero : witnessLigand 0 = 1 := rfl

@[simp] theorem witnessLigand_one : witnessLigand 1 = 2 := rfl

@[simp] theorem witnessLigand_two : witnessLigand 2 = 3 := rfl

@[simp] theorem witnessLigand_three : witnessLigand 3 = 4 := rfl

theorem witnessLigand_adj (index : Fin 4) :
    witnessGraph.Adj 0 (witnessLigand index) := by
  fin_cases index <;> decide

theorem witnessLigand_injective : Function.Injective witnessLigand := by
  intro left right equal
  apply Fin.ext
  have values := congrArg Fin.val equal
  simp only [witnessLigand] at values
  omega

theorem witnessLigand_surjective :
    ∀ atom, witnessGraph.Adj 0 atom → ∃ index, witnessLigand index = atom := by
  intro atom adjacent
  fin_cases atom
  · exact absurd adjacent (by decide)
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact absurd adjacent (by decide)
  · exact absurd adjacent (by decide)
  · exact absurd adjacent (by decide)
  · exact absurd adjacent (by decide)
  · exact absurd adjacent (by decide)
  · exact absurd adjacent (by decide)

/-- The witness admitted as a one-center molecule at atom 0. -/
def witnessMolecule : OneCenterMolecule (Fin 11) where
  mol := witnessGraph
  center := 0
  ligandAtom := witnessLigand
  ligandAtom_adj := witnessLigand_adj
  ligandAtom_injective := witnessLigand_injective
  ligandAtom_surjective := witnessLigand_surjective

/-! ## The legacy layer-major branch on the witness graph -/

/-- Root of the isotope-13 methyl ligand branch. -/
abbrev rootC13 : OfficialCIPNode (Fin 11) :=
  OfficialCIPNode.rootFromEdge 0 3

/-- Root of the isotope-12 fluoromethyl ligand branch. -/
abbrev rootC12F : OfficialCIPNode (Fin 11) :=
  OfficialCIPNode.rootFromEdge 0 4

/-- Empty Rule-3/4/5 context: this counterexample is purely constitutional. -/
abbrev witnessContext : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext :=
  fun _ => CIPRuleEngine.OfficialLigandRuleContext.empty

@[simp] theorem rootC13_label :
    witnessGraph.officialNodeAtomLabel rootC13 = toLex (6, 13) := rfl

@[simp] theorem rootC12F_label :
    witnessGraph.officialNodeAtomLabel rootC12F = toLex (6, 12) := rfl

@[simp] theorem rootC13_rule1b : rootC13.rule1bRootDistance = 1 := rfl

@[simp] theorem rootC12F_rule1b : rootC12F.rule1bRootDistance = 1 := rfl

/-- The first-sphere trace of the *legacy layer-major* comparator on the two singleton ligand
roots.  The three decisions are, in order: Rule 1a (tie, both carbon), Rule 1b (tie, both at
distance one), Rule 2 (mass 13 above mass 12).  These are graph-level facts about the retained
layer-major helpers; they do not mention any public engine. -/
theorem layerTrace_exact :
    witnessGraph.compareOfficialLayerTrace [rootC13] [rootC12F] =
      [CIPRuleEngine.priorityNatDecision CIPRuleFamily.atomicNumber 6 6,
       MoleculeGraph.duplicateRootDistanceDecision rootC13 rootC12F,
       CIPRuleEngine.priorityNatDecision CIPRuleFamily.isotopeMass 13 12] := by
  simp [MoleculeGraph.compareOfficialLayerTrace, MoleculeGraph.sortOfficialLayer,
    MoleculeGraph.compareOfficialNodeListTrace, MoleculeGraph.compareOfficialNodeTrace,
    rootC13_label, rootC12F_label]

/-- The legacy layer trace decides at the root sphere: `Ordering.gt` for the isotope-13 methyl
branch. -/
theorem layerTrace_outcome :
    cipTraceOutcome (witnessGraph.compareOfficialLayerTrace [rootC13] [rootC12F]) =
      Ordering.gt := by
  rw [layerTrace_exact]
  simp [cipTraceOutcome, CIPRuleEngine.priorityNatDecision,
    CIPRuleEngine.comparePriorityNat, MoleculeGraph.duplicateRootDistanceDecision,
    MoleculeGraph.compareCloserRootDistance, rootC13_rule1b, rootC12F_rule1b]

/-- Because the root-sphere trace is decisive, the legacy hierarchical-digraph comparator
returns that trace without descending to sphere II. -/
theorem digraphTrace_eq_layer :
    witnessGraph.compareOfficialHierarchicalDigraphTrace 12 [rootC13] [rootC12F] =
      witnessGraph.compareOfficialLayerTrace [rootC13] [rootC12F] := by
  change witnessGraph.compareOfficialHierarchicalDigraphTrace (11 + 1)
    [rootC13] [rootC12F] = witnessGraph.compareOfficialLayerTrace [rootC13] [rootC12F]
  simp [MoleculeGraph.compareOfficialHierarchicalDigraphTrace, layerTrace_outcome]

/-- The legacy hierarchical-digraph trace outcome on the two roots. -/
theorem digraphTrace_outcome :
    cipTraceOutcome
      (witnessGraph.compareOfficialHierarchicalDigraphTrace 12 [rootC13] [rootC12F]) =
        Ordering.gt := by
  rw [digraphTrace_eq_layer, layerTrace_outcome]

/-- **Legacy predecessor outcome.**  The layer-major predecessor ranks `^13CH3` (ligand index 2)
above `^12CH2F` (ligand index 3), decided by Rule 2 at the root sphere.  This is the historical
defective branch, now asserted only about the explicitly named legacy comparator
`cipOfficialCompareLayerMajor`, never about the corrected public engine. -/
theorem legacy_live_outcome_gt :
    (witnessMolecule.cipOfficialCompareLayerMajor witnessContext 2 3).outcome =
      Ordering.gt := by
  simp only [OneCenterMolecule.cipOfficialCompareLayerMajor,
    OneCenterMolecule.cipOfficialCompareLayerMajorWithFuel,
    OneCenterMolecule.cipOfficialHierarchicalDigraphCompareWithContext,
    MoleculeGraph.compareOfficialHierarchicalDigraphThenContextFrom,
    CIPRuleEngine.compareDigraphThenOfficialCertificate_outcome,
    Fintype.card_fin]
  change cipTraceOutcome
    (CIPRuleEngine.compareDigraphThenOfficialTrace
      (witnessGraph.compareOfficialHierarchicalDigraphTrace 12 [rootC13] [rootC12F])
      (witnessContext 2) (witnessContext 3)) = Ordering.gt
  rw [CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_ne_eq]
  · exact digraphTrace_outcome
  · rw [digraphTrace_outcome]
    decide

/-- Historical name preserved as a legacy-scoped alias.  Do **not** read this as a claim about
the corrected public engine. -/
theorem live_outcome_gt :
    (witnessMolecule.cipOfficialCompareLayerMajor witnessContext 2 3).outcome =
      Ordering.gt :=
  legacy_live_outcome_gt

/-- The exact legacy predecessor trace.  It exhibits Rule 2 at the root sphere as the deciding
step, with no sphere-II observation anywhere in the trace. -/
theorem legacy_live_trace_exact :
    (witnessMolecule.cipOfficialCompareLayerMajor witnessContext 2 3).trace =
      [CIPRuleEngine.priorityNatDecision CIPRuleFamily.atomicNumber 6 6,
       MoleculeGraph.duplicateRootDistanceDecision rootC13 rootC12F,
       CIPRuleEngine.priorityNatDecision CIPRuleFamily.isotopeMass 13 12] := by
  simp only [OneCenterMolecule.cipOfficialCompareLayerMajor,
    OneCenterMolecule.cipOfficialCompareLayerMajorWithFuel,
    OneCenterMolecule.cipOfficialHierarchicalDigraphCompareWithContext,
    MoleculeGraph.compareOfficialHierarchicalDigraphThenContextFrom,
    Fintype.card_fin]
  change CIPRuleEngine.compareDigraphThenOfficialTrace
    (witnessGraph.compareOfficialHierarchicalDigraphTrace 12 [rootC13] [rootC12F])
    (witnessContext 2) (witnessContext 3) =
      [CIPRuleEngine.priorityNatDecision CIPRuleFamily.atomicNumber 6 6,
       MoleculeGraph.duplicateRootDistanceDecision rootC13 rootC12F,
       CIPRuleEngine.priorityNatDecision CIPRuleFamily.isotopeMass 13 12]
  unfold CIPRuleEngine.compareDigraphThenOfficialTrace
  rw [digraphTrace_outcome]
  simp
  rw [digraphTrace_eq_layer, layerTrace_exact]

/-- Historical name preserved as a legacy-scoped alias. -/
theorem live_trace_exact :
    (witnessMolecule.cipOfficialCompareLayerMajor witnessContext 2 3).trace =
      [CIPRuleEngine.priorityNatDecision CIPRuleFamily.atomicNumber 6 6,
       MoleculeGraph.duplicateRootDistanceDecision rootC13 rootC12F,
       CIPRuleEngine.priorityNatDecision CIPRuleFamily.isotopeMass 13 12] :=
  legacy_live_trace_exact

/-- The same legacy outcome through the named predecessor engine result structure. -/
theorem legacy_live_engine_outcome_gt :
    ((witnessMolecule.cipOfficialEngineLayerMajor witnessContext).compare 2 3).outcome =
      Ordering.gt := by
  rw [OneCenterMolecule.cipOfficialEngineLayerMajor_compare]
  exact legacy_live_outcome_gt

/-- Historical name preserved as a legacy-scoped alias. -/
theorem live_engine_outcome_gt :
    ((witnessMolecule.cipOfficialEngineLayerMajor witnessContext).compare 2 3).outcome =
      Ordering.gt :=
  legacy_live_engine_outcome_gt

/-- The exact comparator call used by the **predecessor**
`Engine.OfficialStereoTransaction.certificate` (the layer-major
`cipOfficialHierarchicalDigraphCompareWithContext` at the request graph fuel, which defaults to
`atomCount + 1 = 12`).  The corrected transaction now consumes the rule-major bounded
certificate; this theorem therefore records only the legacy comparator's value on the witness. -/
theorem legacy_transaction_comparator_outcome_gt :
    (witnessMolecule.cipOfficialHierarchicalDigraphCompareWithContext
      witnessContext 12 2 3).outcome = Ordering.gt := by
  have computed := legacy_live_outcome_gt
  simp only [OneCenterMolecule.cipOfficialCompareLayerMajor,
    OneCenterMolecule.cipOfficialCompareLayerMajorWithFuel, Fintype.card_fin] at computed
  exact computed



theorem legacy_transaction_comparator_eq_withFuel :
    (witnessMolecule.cipOfficialCompareLayerMajorWithFuel witnessContext 12 2 3) =
      witnessMolecule.cipOfficialHierarchicalDigraphCompareWithContext witnessContext 12 2 3 :=
  rfl

/-- Historical name preserved as a legacy-scoped alias. -/
theorem transaction_comparator_outcome_gt :
    (witnessMolecule.cipOfficialHierarchicalDigraphCompareWithContext
      witnessContext 12 2 3).outcome = Ordering.gt :=
  legacy_transaction_comparator_outcome_gt

/-! ## The exhaustive rule-major branch (retained unchanged) -/

/-- The graph-generated official child enumerator used by the rule-major compiler.  It
enumerates exactly the neighbours of each reached atom after deleting the stored parent:
center 0 has children 1, 2, 3, 4; atom 3 has children 6, 7, 8; atom 4 has children 5, 9, 10;
all other atoms are leaves.  The tree reached from the two ligand roots never revisits an
atom, so no duplicate-leaf case arises. -/
def witnessChildren (node : OfficialCIPNode (Fin 11)) :
    List (OfficialCIPNode (Fin 11)) :=
  match node.current? with
  | none => []
  | some atom =>
      if node.isDuplicateLeaf then []
      else
        match atom.val with
        | 0 => [node.extend 1 0, node.extend 2 0, node.extend 3 0, node.extend 4 0]
        | 3 => [node.extend 6 0, node.extend 7 0, node.extend 8 0]
        | 4 => [node.extend 5 0, node.extend 9 0, node.extend 10 0]
        | _ => []

/-- The exhaustive rule-major key compiled for the `^13CH3` ligand branch. -/
def keyC13 : OfficialRuleMajorKey (Fin 11) where
  rule1a :=
    [[([], 6)],
     [([0], 1), ([1], 1), ([2], 1)]]
  rule1b :=
    [[([], 1)],
     [([0], 2), ([1], 2), ([2], 2)]]
  rule2 :=
    [[([], 13)],
     [([0], 1), ([1], 1), ([2], 1)]]
  sourceNodes :=
    [[([], rootC13)],
     [([0], OfficialCIPNode.extend rootC13 6 0),
      ([1], OfficialCIPNode.extend rootC13 7 0),
      ([2], OfficialCIPNode.extend rootC13 8 0)]]
  complete := true

/-- The exhaustive rule-major key compiled for the `^12CH2F` ligand branch.  Note that the
fluorine child is the highest-priority sphere-II child and therefore occupies slot 0. -/
def keyC12F : OfficialRuleMajorKey (Fin 11) where
  rule1a :=
    [[([], 6)],
     [([0], 9), ([1], 1), ([2], 1)]]
  rule1b :=
    [[([], 1)],
     [([0], 2), ([1], 2), ([2], 2)]]
  rule2 :=
    [[([], 12)],
     [([0], 19), ([1], 1), ([2], 1)]]
  sourceNodes :=
    [[([], rootC12F)],
     [([0], OfficialCIPNode.extend rootC12F 5 0),
      ([1], OfficialCIPNode.extend rootC12F 9 0),
      ([2], OfficialCIPNode.extend rootC12F 10 0)]]
  complete := true

/-- The authoritative compiler produces exactly `keyC13` from the `^13CH3` root. -/
theorem build_rootC13 :
    witnessGraph.buildOfficialRuleMajorKey witnessChildren 3 rootC13 = some keyC13 := rfl

/-- The authoritative compiler produces exactly `keyC12F` from the `^12CH2F` root. -/
theorem build_rootC12F :
    witnessGraph.buildOfficialRuleMajorKey witnessChildren 3 rootC12F = some keyC12F := rfl

/-- The compiled keys are source-aligned: every rule projection is a fresh projection of the
actual graph node labels and actual Rule-1b distances.  No observation is fabricated or
attached to a different sphere or parent slot. -/
theorem keyC13_sourceAligned :
    OfficialRuleMajorKey.SourceAligned witnessGraph keyC13 :=
  witnessGraph.buildOfficialRuleMajorKey_sourceAligned
    witnessChildren 3 rootC13 keyC13 build_rootC13

theorem keyC12F_sourceAligned :
    OfficialRuleMajorKey.SourceAligned witnessGraph keyC12F :=
  witnessGraph.buildOfficialRuleMajorKey_sourceAligned
    witnessChildren 3 rootC12F keyC12F build_rootC12F

/-- A decisive Rule-1a projection determines the full rule-major comparison, before any
Rule-1b or Rule-2 observation is consulted.  This is the exhaustive-rule-order semantics of
P-92.1.3 / P-92.6. -/
theorem ruleMajor_compare_eq_rule1a_of_decisive {V : Type*}
    (left right : OfficialRuleMajorKey V)
    (decisive :
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        left.rule1a right.rule1a ≠ Ordering.eq) :
    OfficialRuleMajorKey.compare left right =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        left.rule1a right.rule1a := by
  unfold OfficialRuleMajorKey.compare
  cases comparison : OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a with
  | lt => simp [compareLex, Ordering.byKey, comparison]
  | gt => simp [compareLex, Ordering.byKey, comparison]
  | eq => exact absurd comparison decisive

/-- Exhaustive Rule 1a places `^12CH2F` above `^13CH3`: the only strict difference in the
two complete addressed Rule-1a projections is at sphere II, where the fluoromethyl branch
exposes Z = 9 and the methyl branch exposes Z = 1. -/
theorem keyC12F_above_keyC13_by_rule1a :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyC12F.rule1a keyC13.rule1a = Ordering.gt := by
  decide

/-- The opposite orientation, used to compare the stored left-to-right engine order. -/
theorem keyC13_below_keyC12F_by_rule1a :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyC13.rule1a keyC12F.rule1a = Ordering.lt := by
  decide

/-- Rule 2 at the root sphere, taken in isolation, prefers `^13CH3` (mass 13 over mass 12).
This is the observation the legacy layer-major engine uses; exhaustive Rule 1a must pre-empt
it. -/
theorem keyC13_above_keyC12F_by_rule2 :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyC13.rule2 keyC12F.rule2 = Ordering.gt := by
  decide

/-- The authoritative rule-major comparator ranks `^13CH3` below `^12CH2F`.  This is the
exhaustive-rule-order side of the historical disagreement and is also the semantics of the
corrected public engine. -/
theorem ruleMajor_compare_lt :
    OfficialRuleMajorKey.compare keyC13 keyC12F = Ordering.lt := by
  rw [ruleMajor_compare_eq_rule1a_of_decisive]
  · exact keyC13_below_keyC12F_by_rule1a
  · rw [keyC13_below_keyC12F_by_rule1a]
    decide

/-- The reverse orientation of the authoritative comparator. -/
theorem ruleMajor_compare_gt_reverse :
    OfficialRuleMajorKey.compare keyC12F keyC13 = Ordering.gt := by
  rw [ruleMajor_compare_eq_rule1a_of_decisive]
  · exact keyC12F_above_keyC13_by_rule1a
  · rw [keyC12F_above_keyC13_by_rule1a]
    decide

/-- The completeness-guarded rule-major entry point also returns the strict Rule-1a outcome. -/
theorem ruleMajor_compare?_lt :
    OfficialRuleMajorKey.compare? keyC13 keyC12F = some Ordering.lt := by
  unfold OfficialRuleMajorKey.compare?
  simp [keyC13_below_keyC12F_by_rule1a]

/-- Feeding the compiler outputs directly into the authoritative comparator gives the strict
Rule-1a outcome.  No separately supplied key enters this statement. -/
theorem built_ruleMajor_compare_lt :
    (witnessGraph.buildOfficialRuleMajorKey witnessChildren 3 rootC13).bind
        (fun left =>
          (witnessGraph.buildOfficialRuleMajorKey witnessChildren 3 rootC12F).bind
            (fun right => some (OfficialRuleMajorKey.compare left right))) =
      some Ordering.lt := by
  simp [build_rootC13, build_rootC12F, ruleMajor_compare_lt]

/-! ## The same-graph historical disagreement -/














theorem legacy_official_engine_rule_precedence_counterexample :
    (witnessMolecule.cipOfficialCompareLayerMajor witnessContext 2 3).outcome = Ordering.gt ∧
    OfficialRuleMajorKey.compare keyC13 keyC12F = Ordering.lt ∧
    witnessGraph.buildOfficialRuleMajorKey witnessChildren 3 rootC13 = some keyC13 ∧
    witnessGraph.buildOfficialRuleMajorKey witnessChildren 3 rootC12F = some keyC12F ∧
    OfficialRuleMajorKey.SourceAligned witnessGraph keyC13 ∧
    OfficialRuleMajorKey.SourceAligned witnessGraph keyC12F :=
  ⟨legacy_live_outcome_gt, ruleMajor_compare_lt, build_rootC13, build_rootC12F,
    keyC13_sourceAligned, keyC12F_sourceAligned⟩

/-- Historical name preserved as a legacy-scoped alias. -/
theorem official_engine_rule_precedence_counterexample :
    (witnessMolecule.cipOfficialCompareLayerMajor witnessContext 2 3).outcome = Ordering.gt ∧
    OfficialRuleMajorKey.compare keyC13 keyC12F = Ordering.lt ∧
    witnessGraph.buildOfficialRuleMajorKey witnessChildren 3 rootC13 = some keyC13 ∧
    witnessGraph.buildOfficialRuleMajorKey witnessChildren 3 rootC12F = some keyC12F ∧
    OfficialRuleMajorKey.SourceAligned witnessGraph keyC13 ∧
    OfficialRuleMajorKey.SourceAligned witnessGraph keyC12F :=
  legacy_official_engine_rule_precedence_counterexample

/-- The source-priority requirement is derived from actual node atomic-number witnesses in
the compiled keys, not from the desired outcome.  Sphere II of the `^13CH3` branch contains
only hydrogens (Z = 1); sphere II of the `^12CH2F` branch contains fluorine (Z = 9).  The
Rule-1a projection is decisive, the Rule-2 projection points the opposite way, and the
rule-major comparator follows Rule 1a. -/
theorem source_rule1a_preempts_root_rule2 :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        keyC12F.rule1a keyC13.rule1a = Ordering.gt ∧
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        keyC13.rule2 keyC12F.rule2 = Ordering.gt ∧
      OfficialRuleMajorKey.compare keyC13 keyC12F = Ordering.lt :=
  ⟨keyC12F_above_keyC13_by_rule1a, keyC13_above_keyC12F_by_rule2, ruleMajor_compare_lt⟩

/-- The sphere-II atomic-number witnesses themselves, read from the actual graph nodes. -/
theorem sphere_two_atomic_number_witnesses :
    (ofLex (witnessGraph.officialNodeAtomLabel
        (OfficialCIPNode.extend rootC13 6 0))).1 = 1 ∧
      (ofLex (witnessGraph.officialNodeAtomLabel
        (OfficialCIPNode.extend rootC12F 5 0))).1 = 9 := by
  constructor <;> rfl

/-- The root Rule-2 masses read from the actual graph nodes. -/
theorem root_mass_witnesses :
    (ofLex (witnessGraph.officialNodeAtomLabel rootC13)).2 = 13 ∧
      (ofLex (witnessGraph.officialNodeAtomLabel rootC12F)).2 = 12 := by
  constructor <;> rfl

/-! ## Kernel-authority guards -/

assert_kernel_only OneCenterMolecule.cipOfficialCompareLayerMajorWithFuel_eq_legacyHelper
assert_kernel_only OneCenterMolecule.cipOfficialCompareLayerMajor_eq_hierarchicalDefault
assert_kernel_only OneCenterMolecule.cipOfficialCompareLayerMajor_ligandAtom_ne_center
assert_kernel_only OneCenterMolecule.cipOfficialCompareLayerMajorWithFuel_trace_stable_default
assert_kernel_only OneCenterMolecule.cipOfficialCompareLayerMajorWithFuel_outcome_stable_default
assert_kernel_only OneCenterMolecule.cipOfficialEngineLayerMajor_context
assert_kernel_only OneCenterMolecule.cipOfficialEngineLayerMajor_compare
assert_kernel_only witnessBond_symm
assert_kernel_only witnessBond_self
assert_kernel_only witnessLigand_adj
assert_kernel_only witnessLigand_injective
assert_kernel_only witnessLigand_surjective
assert_kernel_only layerTrace_exact
assert_kernel_only layerTrace_outcome
assert_kernel_only digraphTrace_eq_layer
assert_kernel_only digraphTrace_outcome
assert_kernel_only legacy_live_outcome_gt
assert_kernel_only live_outcome_gt
assert_kernel_only legacy_live_trace_exact
assert_kernel_only live_trace_exact
assert_kernel_only legacy_live_engine_outcome_gt
assert_kernel_only live_engine_outcome_gt
assert_kernel_only legacy_transaction_comparator_outcome_gt
assert_kernel_only legacy_transaction_comparator_eq_withFuel
assert_kernel_only transaction_comparator_outcome_gt
assert_kernel_only build_rootC13
assert_kernel_only build_rootC12F
assert_kernel_only keyC13_sourceAligned
assert_kernel_only keyC12F_sourceAligned
assert_kernel_only ruleMajor_compare_eq_rule1a_of_decisive
assert_kernel_only keyC12F_above_keyC13_by_rule1a
assert_kernel_only keyC13_below_keyC12F_by_rule1a
assert_kernel_only keyC13_above_keyC12F_by_rule2
assert_kernel_only ruleMajor_compare_lt
assert_kernel_only ruleMajor_compare_gt_reverse
assert_kernel_only ruleMajor_compare?_lt
assert_kernel_only built_ruleMajor_compare_lt
assert_kernel_only legacy_official_engine_rule_precedence_counterexample
assert_kernel_only official_engine_rule_precedence_counterexample
assert_kernel_only source_rule1a_preempts_root_rule2
assert_kernel_only sphere_two_atomic_number_witnesses
assert_kernel_only root_mass_witnesses

end OfficialEngineRulePrecedenceFidelity
end OneCenter
end TetraStereo
