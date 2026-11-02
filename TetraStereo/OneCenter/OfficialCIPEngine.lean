import TetraStereo.OneCenter.OfficialRuleMajorKey
import TetraStereo.OneCenter.RS
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

open TetrahedralGeometry

noncomputable section

/-!
# Canonical official-CIP engine surface (exhaustive rule-major)

The historical engine compared one breadth-first sphere at a time, applying Rules 1a, 1b and 2 to
each node pair before advancing.  That schedule lets a root-sphere Rule-2 (isotope mass) decision
pre-empt a deeper-sphere Rule-1a (atomic number) decision, which contradicts P-92.1.3 / P-92.6.
The kernel-confirmed witness `f4_rule_major_public_counterexample` exhibits exactly that failure
on `[C@](Br)(Cl)([13CH3])[12CH2F]`.

This module replaces the comparison schedule, not the constitution.  Each ligand branch rooted at
an actual `OfficialCIPNode.rootFromEdge` is compiled by the shared
`MoleculeGraph.buildOfficialRuleMajorKey` compiler from `OfficialRuleMajorKey.lean`.  The three
complete parent-addressed projections are compared in exhaustive normative order (all of Rule 1a,
then all of Rule 1b, then all of Rule 2), and the supplied Rule 3/4/5 context is consulted only
after the completed constitutional trace ties.

The bounded entry point `cipOfficialCompareWithFuel` returns `Option CIPTraceCertificate`: `none`
is an honest refusal to produce a constitutional result when a root key cannot be compiled or the
completed-key gate `OfficialRuleMajorKey.compare?` refuses.  The public
`cipOfficialCompare` remains total at the proved finite-atom bound `Fintype.card V + 1`; it
extracts the bounded result with a proof of success, never with `getD … Ordering.eq` or any other
fabricated default.  Fuel stability (`buildOfficialRuleMajorKey_fuel_stable`) is proved here from
`OfficialExpansionCompleteWithin`, so the bounded computation at any larger fuel is definitionally
the same computation and the total engine is not fuel-sensitive.
-/

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Shared rule-major solver -/

/-- Constitutional rule-major trace of two actual branch roots at explicit fuel.

Each root is compiled independently with the shared compiler.  The two compiled keys must pass the
completed-key gate `OfficialRuleMajorKey.compare?`; only then is the rule-tagged
`OfficialRuleMajorKey.compareTrace` emitted.  `none` records a failed build or a refused gate and
is never silently mapped to an equality. -/
def ruleMajorConstitutionalTraceWithFuel (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) (fuel : ℕ)
    (leftRoot rightRoot : OfficialCIPNode V) : Option (List CIPRuleDecision) :=
  match m.buildOfficialRuleMajorKey children fuel leftRoot with
  | none => none
  | some leftKey =>
      match m.buildOfficialRuleMajorKey children fuel rightRoot with
      | none => none
      | some rightKey =>
          match OfficialRuleMajorKey.compare? leftKey rightKey with
          | none => none
          | some _ => some (OfficialRuleMajorKey.compareTrace leftKey rightKey)

/-- Proof-carrying constitutional comparison followed by the existing official Rule 3/4/5
fallthrough.  The context is applied only after a completed constitutional trace exists. -/
def compareRuleMajorRootsWithFuel (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) (fuel : ℕ)
    (leftRoot rightRoot : OfficialCIPNode V)
    (leftContext rightContext : CIPRuleEngine.OfficialLigandRuleContext) :
    Option CIPTraceCertificate :=
  (m.ruleMajorConstitutionalTraceWithFuel children fuel leftRoot rightRoot).map
    fun trace =>
      CIPRuleEngine.compareDigraphThenOfficialCertificate trace leftContext rightContext

/-! ## Fuel stability of the shared compiler -/

/-- Congruence of `List.mapM` on two pointwise-equal maps.  This is structural proof support for
fuel stability; it assumes no evaluator oracle. -/
private theorem mapM_congr_on {α β : Type*} (before after : α → Option β) :
    ∀ values : List α, (∀ value ∈ values, before value = after value) →
      values.mapM before = values.mapM after
  | [], _ => rfl
  | value :: values, agree => by
      have head := agree value (by simp)
      have tail := mapM_congr_on before after values
        (fun value present => agree value (by simp [present]))
      rw [List.mapM_cons, List.mapM_cons]
      simp [head, tail]

/-- Once a branch is exhausted within `fuel`, compiling it at any larger bound produces exactly
the same key.  The induction is on `fuel`; the recursive child calls use the smaller completeness
bound, and the larger bound is only compared through the induction hypothesis. -/
theorem buildOfficialRuleMajorKey_stable_ge (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) :
    ∀ (fuel : ℕ) (node : OfficialCIPNode V),
      OfficialExpansionCompleteWithin children fuel node →
      ∀ bigger : ℕ, fuel ≤ bigger →
        m.buildOfficialRuleMajorKey children bigger node =
          m.buildOfficialRuleMajorKey children fuel node
  | 0, node, complete, bigger, _ => by
      change children node = [] at complete
      cases bigger with
      | zero => rfl
      | succ bound => simp [buildOfficialRuleMajorKey, complete]
  | fuel + 1, node, complete, bigger, bounded => by
      cases bigger with
      | zero => omega
      | succ bound =>
          have boundLe : fuel ≤ bound := by omega
          have childComplete : ∀ child, child ∈ children node →
              OfficialExpansionCompleteWithin children fuel child := by
            intro child present
            exact complete child present
          unfold buildOfficialRuleMajorKey
          dsimp only
          by_cases terminal : (children node).isEmpty = true
          · simp [terminal]
          · rw [if_neg terminal, if_neg terminal]
            have mapEq :
                (children node).mapM
                    (m.buildOfficialRuleMajorKey children bound) =
                  (children node).mapM
                    (m.buildOfficialRuleMajorKey children fuel) := by
              apply mapM_congr_on
              intro child present
              exact buildOfficialRuleMajorKey_stable_ge m children fuel child
                (childComplete child present) bound boundLe
            simp only [mapEq]

/-- Fuel stability in the form used by the public engine: adding fuel beyond an exhausted bound
cannot change the compiled key. -/
theorem buildOfficialRuleMajorKey_fuel_stable (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) (fuel extra : ℕ)
    (node : OfficialCIPNode V)
    (complete : OfficialExpansionCompleteWithin children fuel node) :
    m.buildOfficialRuleMajorKey children (fuel + extra) node =
      m.buildOfficialRuleMajorKey children fuel node :=
  buildOfficialRuleMajorKey_stable_ge m children fuel node complete
    (fuel + extra) (Nat.le_add_right fuel extra)

end MoleculeGraph

namespace OneCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A ligand atom is never the stereocenter, because it is adjacent to the stereocenter and the
bond matrix has zero diagonal. -/
theorem ligandAtom_ne_center (m : OneCenterMolecule V) (i : Fin 4) :
    m.ligandAtom i ≠ m.center := by
  intro h
  have hadj := m.ligandAtom_adj i
  simp [MoleculeGraph.Adj, h, m.mol.bond_self] at hadj

/-- The exhaustive rule-major key of one actual ligand branch root at explicit fuel. -/
def cipOfficialRuleMajorKeyWithFuel (m : OneCenterMolecule V) (fuel : ℕ) (i : Fin 4) :
    Option (OfficialRuleMajorKey V) :=
  m.mol.buildOfficialRuleMajorKey m.mol.officialCIPChildren fuel
    (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom i))

/-- The completed constitutional rule-major trace of two canonical ligand roots at explicit fuel.
`none` records a failed build or a refused completed-key comparison. -/
def cipOfficialConstitutionalTraceWithFuel (m : OneCenterMolecule V) (fuel : ℕ)
    (i j : Fin 4) : Option (List CIPRuleDecision) :=
  m.mol.ruleMajorConstitutionalTraceWithFuel m.mol.officialCIPChildren fuel
    (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom i))
    (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom j))

/-- Canonical official ligand comparison with explicit fuel.

Both actual `rootFromEdge` keys are compiled by the shared rule-major compiler and must pass
`OfficialRuleMajorKey.compare?`; the rule-tagged `compareTrace` then yields a certificate.  The
supplied Rule 3/4/5 context is applied only after this completed constitutional result. -/
def cipOfficialCompareWithFuel (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (fuel : ℕ)
    (i j : Fin 4) : Option CIPTraceCertificate :=
  m.mol.compareRuleMajorRootsWithFuel m.mol.officialCIPChildren fuel
    (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom i))
    (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom j))
    (context i) (context j)

/-- Default fuels make every actual ligand branch complete.  Existence is the separately proved
finite-atom expansion completeness of `officialCIPChildren`; nothing is assumed about the output
of the compiler. -/
theorem cipOfficialRuleMajorKey_complete_default (m : OneCenterMolecule V) (i : Fin 4) :
    ∃ key, m.cipOfficialRuleMajorKeyWithFuel (Fintype.card V + 1) i = some key ∧
      key.complete = true := by
  unfold cipOfficialRuleMajorKeyWithFuel
  exact m.mol.buildOfficialRuleMajorKey_complete_of_expansionCompleteWithin
    m.mol.officialCIPChildren (Fintype.card V + 1)
    (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom i))
    (m.mol.officialExpansionCompleteWithin_rootFromEdge_default
      (center := m.center) (ligand := m.ligandAtom i) (m.ligandAtom_ne_center i))

/-- At the default finite-atom fuel the bounded comparison never refuses: both actual roots
compile to complete keys, and complete keys are always safely comparable. -/
theorem cipOfficialCompareWithFuel_isSome_default (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) :
    (m.cipOfficialCompareWithFuel context (Fintype.card V + 1) i j).isSome = true := by
  obtain ⟨leftKey, leftComputed, leftComplete⟩ :=
    m.cipOfficialRuleMajorKey_complete_default i
  obtain ⟨rightKey, rightComputed, rightComplete⟩ :=
    m.cipOfficialRuleMajorKey_complete_default j
  obtain ⟨outcome, outcomeComputed⟩ := Option.isSome_iff_exists.mp
    (OfficialRuleMajorKey.compare?_isSome_of_complete leftKey rightKey
      leftComplete rightComplete)
  simp only [cipOfficialRuleMajorKeyWithFuel] at leftComputed rightComputed
  unfold cipOfficialCompareWithFuel MoleculeGraph.compareRuleMajorRootsWithFuel
    MoleculeGraph.ruleMajorConstitutionalTraceWithFuel
  simp only [leftComputed, rightComputed, outcomeComputed, Option.map_some,
    Option.isSome_some]

/-- Canonical total official ligand comparison at the proved stable default fuel.  The result is
obtained by proof-backed extraction from the bounded computation; no `getD` equality substitute
is used. -/
noncomputable def cipOfficialCompare (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (i j : Fin 4) : CIPTraceCertificate :=
  (m.cipOfficialCompareWithFuel context (Fintype.card V + 1) i j).get
    (m.cipOfficialCompareWithFuel_isSome_default context i j)

/-- The total default comparison is exactly the surviving branch of the bounded computation. -/
theorem cipOfficialCompareWithFuel_default_eq_some (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) :
    m.cipOfficialCompareWithFuel context (Fintype.card V + 1) i j =
      some (m.cipOfficialCompare context i j) :=
  (Option.some_get
    (m.cipOfficialCompareWithFuel_isSome_default context i j)).symm

/-- Two bounded computations agree whenever both actual roots are exhausted within the smaller
bound.  This is the fuel-stability core of the corrected engine. -/
theorem cipOfficialCompareWithFuel_stable_of_complete (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4)
    (fuel extra : ℕ)
    (leftComplete : MoleculeGraph.OfficialExpansionCompleteWithin m.mol.officialCIPChildren
      fuel (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom i)))
    (rightComplete : MoleculeGraph.OfficialExpansionCompleteWithin m.mol.officialCIPChildren
      fuel (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom j))) :
    m.cipOfficialCompareWithFuel context (fuel + extra) i j =
      m.cipOfficialCompareWithFuel context fuel i j := by
  have leftStable := MoleculeGraph.buildOfficialRuleMajorKey_fuel_stable
    m.mol m.mol.officialCIPChildren fuel extra
    (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom i)) leftComplete
  have rightStable := MoleculeGraph.buildOfficialRuleMajorKey_fuel_stable
    m.mol m.mol.officialCIPChildren fuel extra
    (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom j)) rightComplete
  unfold cipOfficialCompareWithFuel MoleculeGraph.compareRuleMajorRootsWithFuel
    MoleculeGraph.ruleMajorConstitutionalTraceWithFuel
  simp only [leftStable, rightStable]

/-- Public stability theorem: extra fuel beyond the default atom-cardinality bound cannot change
the bounded computation, and that computation is exactly the total default result. -/
theorem cipOfficialCompareWithFuel_stable_default (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) (extra : ℕ) :
    m.cipOfficialCompareWithFuel context ((Fintype.card V + 1) + extra) i j =
      some (m.cipOfficialCompare context i j) := by
  rw [m.cipOfficialCompareWithFuel_stable_of_complete context i j
    (Fintype.card V + 1) extra
    (m.mol.officialExpansionCompleteWithin_rootFromEdge_default
      (center := m.center) (ligand := m.ligandAtom i) (m.ligandAtom_ne_center i))
    (m.mol.officialExpansionCompleteWithin_rootFromEdge_default
      (center := m.center) (ligand := m.ligandAtom j) (m.ligandAtom_ne_center j))]
  exact m.cipOfficialCompareWithFuel_default_eq_some context i j

/-- Trace-level public stability theorem stated through the bounded `Option` result. -/
theorem cipOfficialCompareWithFuel_trace_stable_default (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) (extra : ℕ) :
    (m.cipOfficialCompareWithFuel context ((Fintype.card V + 1) + extra) i j).map
        (fun certificate => certificate.trace) =
      some (m.cipOfficialCompare context i j).trace := by
  rw [m.cipOfficialCompareWithFuel_stable_default context i j extra]
  rfl

/-- Outcome-level public stability theorem stated through the bounded `Option` result. -/
theorem cipOfficialCompareWithFuel_outcome_stable_default (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) (extra : ℕ) :
    (m.cipOfficialCompareWithFuel context ((Fintype.card V + 1) + extra) i j).map
        (fun certificate => certificate.outcome) =
      some (m.cipOfficialCompare context i j).outcome := by
  rw [m.cipOfficialCompareWithFuel_stable_default context i j extra]
  rfl

/-- The bounded computation at the default fuel is exactly the total comparison, so the public
engine and the explicit-fuel entry point agree at the default. -/
@[simp] theorem cipOfficialCompareWithFuel_default (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) :
    m.cipOfficialCompareWithFuel context (Fintype.card V + 1) i j =
      some (m.cipOfficialCompare context i j) :=
  m.cipOfficialCompareWithFuel_default_eq_some context i j

/-- Boolean order predicate for canonical official ligand sorting.  Exact official ties are broken
by the ligand index only to keep the executable list total; use `ResolvedOfficialCIP` before
interpreting the order as stereochemical data. -/
def cipOfficialBefore (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) : Bool :=
  match (m.cipOfficialCompare context i j).outcome with
  | Ordering.gt => true
  | Ordering.lt => false
  | Ordering.eq => decide (i ≤ j)

/-- Canonical official ligand order. -/
def cipOfficialOrder (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : List (Fin 4) :=
  (List.finRange 4).mergeSort (m.cipOfficialBefore context)

theorem cipOfficialOrder_perm_finRange (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    (m.cipOfficialOrder context).Perm (List.finRange 4) := by
  classical
  simpa [cipOfficialOrder] using
    (List.mergeSort_perm (List.finRange 4) (m.cipOfficialBefore context))

theorem length_cipOfficialOrder (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    (m.cipOfficialOrder context).length = 4 := by
  classical
  have hperm := m.cipOfficialOrder_perm_finRange context
  have := hperm.length_eq
  simpa [List.length_finRange] using this

theorem nodup_cipOfficialOrder (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    (m.cipOfficialOrder context).Nodup := by
  classical
  exact (List.nodup_finRange 4).perm (m.cipOfficialOrder_perm_finRange context).symm

theorem mem_cipOfficialOrder (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i : Fin 4) :
    i ∈ m.cipOfficialOrder context := by
  classical
  have hperm := m.cipOfficialOrder_perm_finRange context
  exact (hperm.mem_iff).2 (List.mem_finRange i)

/-- Canonical official ligand permutation. -/
def cipOfficialPermutation (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : Equiv.Perm (Fin 4) := by
  classical
  let order : List (Fin 4) := m.cipOfficialOrder context
  have hlen : order.length = 4 := by
    simpa [order] using m.length_cipOfficialOrder context
  have hnodup : order.Nodup := by
    simpa [order] using m.nodup_cipOfficialOrder context
  have hmem : ∀ i : Fin 4, i ∈ order := by
    intro i
    simpa [order] using m.mem_cipOfficialOrder context i
  exact ((Fin.castOrderIso hlen.symm).toEquiv).trans
    (List.Nodup.getEquivOfForallMemList order hnodup hmem)

/-- Canonical official priorities are resolved when every distinct ligand pair has a decisive
official rule-major comparison. -/
def ResolvedOfficialCIP (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : Prop :=
  ∀ i j : Fin 4, i ≠ j → (m.cipOfficialCompare context i j).outcome ≠ Ordering.eq

/-- Canonical official order with tie refusal. -/
noncomputable def cipOfficialOrder? (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) : Option (List (Fin 4)) :=
  by
    classical
    exact if _h : m.ResolvedOfficialCIP context then some (m.cipOfficialOrder context) else none

/-- Canonical official permutation with tie refusal. -/
noncomputable def cipOfficialPermutation? (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    Option (Equiv.Perm (Fin 4)) :=
  by
    classical
    exact
      if _h : m.ResolvedOfficialCIP context then
        some (m.cipOfficialPermutation context)
      else
        none

theorem cipOfficialOrder?_eq_some_of_resolved (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (h : m.ResolvedOfficialCIP context) :
    m.cipOfficialOrder? context = some (m.cipOfficialOrder context) := by
  classical
  simp [cipOfficialOrder?, h]

theorem cipOfficialPermutation?_eq_some_of_resolved (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (h : m.ResolvedOfficialCIP context) :
    m.cipOfficialPermutation? context = some (m.cipOfficialPermutation context) := by
  classical
  simp [cipOfficialPermutation?, h]

theorem cipOfficialPermutation?_isSome_iff_resolved (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    (m.cipOfficialPermutation? context).isSome = true ↔ m.ResolvedOfficialCIP context := by
  classical
  by_cases h : m.ResolvedOfficialCIP context
  · simp [cipOfficialPermutation?, h]
  · simp [cipOfficialPermutation?, h]

/-- Canonical official-CIP engine result for one-center molecules. -/
structure OfficialCIPEngineResult (m : OneCenterMolecule V) where
  context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext
  compare : Fin 4 → Fin 4 → CIPTraceCertificate
  order : List (Fin 4)
  permutation : Equiv.Perm (Fin 4)
  safeOrder? : Option (List (Fin 4))
  safePermutation? : Option (Equiv.Perm (Fin 4))
  stableSome :
    ∀ i j extra,
      m.cipOfficialCompareWithFuel context ((Fintype.card V + 1) + extra) i j =
        some (compare i j)
  stableTrace :
    ∀ i j extra,
      (m.cipOfficialCompareWithFuel context ((Fintype.card V + 1) + extra) i j).map
          (fun certificate => certificate.trace) =
        some (compare i j).trace
  stableOutcome :
    ∀ i j extra,
      (m.cipOfficialCompareWithFuel context ((Fintype.card V + 1) + extra) i j).map
          (fun certificate => certificate.outcome) =
        some (compare i j).outcome

/-- Run the canonical official-CIP engine. -/
noncomputable def cipOfficialEngine (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    OfficialCIPEngineResult m where
  context := context
  compare := m.cipOfficialCompare context
  order := m.cipOfficialOrder context
  permutation := m.cipOfficialPermutation context
  safeOrder? := m.cipOfficialOrder? context
  safePermutation? := m.cipOfficialPermutation? context
  stableSome := by
    intro i j extra
    exact m.cipOfficialCompareWithFuel_stable_default context i j extra
  stableTrace := by
    intro i j extra
    exact m.cipOfficialCompareWithFuel_trace_stable_default context i j extra
  stableOutcome := by
    intro i j extra
    exact m.cipOfficialCompareWithFuel_outcome_stable_default context i j extra

@[simp] theorem cipOfficialEngine_compare (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4) :
    (m.cipOfficialEngine context).compare i j = m.cipOfficialCompare context i j :=
  rfl

@[simp] theorem cipOfficialEngine_order (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    (m.cipOfficialEngine context).order = m.cipOfficialOrder context :=
  rfl

@[simp] theorem cipOfficialEngine_permutation (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) :
    (m.cipOfficialEngine context).permutation = m.cipOfficialPermutation context :=
  rfl

@[simp] theorem cipOfficialEngine_safePermutation?_eq_some_of_resolved
    (m : OneCenterMolecule V) (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (h : m.ResolvedOfficialCIP context) :
    (m.cipOfficialEngine context).safePermutation? =
      some (m.cipOfficialPermutation context) := by
  exact m.cipOfficialPermutation?_eq_some_of_resolved context h

/-- `R/S` descriptor using canonical official-CIP priorities. -/
def rsOfficial (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (g : TetrahedralGeometry.Realization) : RS :=
  RS.ofHandedness
    (TetrahedralGeometry.handedness
      (TetrahedralGeometry.reindex g.1 (m.cipOfficialPermutation context)))

/-- Official `R/S` descriptor with explicit evidence that official priorities are resolved. -/
def rsOfficialOfResolved (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (_h : m.ResolvedOfficialCIP context)
    (g : TetrahedralGeometry.Realization) : RS :=
  m.rsOfficial context g

/-- Safe official `R/S`: returns `none` if official priorities tie. -/
noncomputable def rsOfficial? (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (g : TetrahedralGeometry.Realization) : Option RS :=
  by
    classical
    exact if h : m.ResolvedOfficialCIP context then some (m.rsOfficialOfResolved context h g) else none

@[simp] theorem rsOfficialOfResolved_eq_rsOfficial (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (h : m.ResolvedOfficialCIP context) (g : TetrahedralGeometry.Realization) :
    m.rsOfficialOfResolved context h g = m.rsOfficial context g :=
  rfl

theorem rsOfficial?_eq_some_of_resolved (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (h : m.ResolvedOfficialCIP context) (g : TetrahedralGeometry.Realization) :
    m.rsOfficial? context g = some (m.rsOfficial context g) := by
  classical
  simp [rsOfficial?, h]

end OneCenterMolecule

namespace MultiCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Bounded canonical official-CIP local comparison at a distinguished center. -/
def cipOfficialCompareAtWithFuel? (m : MultiCenterMolecule V)
    (context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (center : m.Center) (fuel : ℕ) (i j : Fin 4) : Option CIPTraceCertificate :=
  (m.toOneCenterMolecule center).cipOfficialCompareWithFuel (context center) fuel i j

/-- Canonical official-CIP local comparison at a distinguished center. -/
def cipOfficialCompareAt (m : MultiCenterMolecule V)
    (context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (center : m.Center) (i j : Fin 4) : CIPTraceCertificate :=
  (m.toOneCenterMolecule center).cipOfficialCompare (context center) i j

/-- Canonical official-CIP local order at a distinguished center. -/
def cipOfficialOrderAt (m : MultiCenterMolecule V)
    (context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (center : m.Center) : List (Fin 4) :=
  (m.toOneCenterMolecule center).cipOfficialOrder (context center)

/-- Canonical official-CIP local permutation at a distinguished center. -/
def cipOfficialPermutationAt (m : MultiCenterMolecule V)
    (context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (center : m.Center) : Equiv.Perm (Fin 4) :=
  (m.toOneCenterMolecule center).cipOfficialPermutation (context center)

/-- Local official priorities are resolved at a distinguished center. -/
def ResolvedOfficialCIPAt (m : MultiCenterMolecule V)
    (context : m.Center → Fin 4 → CIPRuleEngine.OfficialLigandRuleContext)
    (center : m.Center) : Prop :=
  (m.toOneCenterMolecule center).ResolvedOfficialCIP (context center)

end MultiCenterMolecule

/-! ## Kernel-authority guards -/

assert_kernel_only MoleculeGraph.buildOfficialRuleMajorKey_stable_ge
assert_kernel_only MoleculeGraph.buildOfficialRuleMajorKey_fuel_stable
assert_kernel_only OneCenterMolecule.ligandAtom_ne_center
assert_kernel_only OneCenterMolecule.cipOfficialRuleMajorKey_complete_default
assert_kernel_only OneCenterMolecule.cipOfficialCompareWithFuel_isSome_default
assert_kernel_only OneCenterMolecule.cipOfficialCompareWithFuel_default_eq_some
assert_kernel_only OneCenterMolecule.cipOfficialCompareWithFuel_stable_of_complete
assert_kernel_only OneCenterMolecule.cipOfficialCompareWithFuel_stable_default
assert_kernel_only OneCenterMolecule.cipOfficialCompareWithFuel_trace_stable_default
assert_kernel_only OneCenterMolecule.cipOfficialCompareWithFuel_outcome_stable_default
assert_kernel_only OneCenterMolecule.cipOfficialOrder_perm_finRange
assert_kernel_only OneCenterMolecule.cipOfficialPermutation?_isSome_iff_resolved
assert_kernel_only OneCenterMolecule.rsOfficial?_eq_some_of_resolved

end
end OneCenter
end TetraStereo
