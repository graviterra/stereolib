import TetraStereo.OneCenter.OfficialCIPEngine
import TetraStereo.KernelOnly

set_option autoImplicit false

/-!
# Uniform terminal-ligand ties for the corrected official CIP engine

The corrected rule-major engine `cipOfficialCompareWithFuel` only reports a constitutional result
after both actual `OfficialCIPNode.rootFromEdge` branches compile to keys that pass the completed
key gate `OfficialRuleMajorKey.compare?`.  This module proves, uniformly for *arbitrary* molecules
and *arbitrary* fuel, that two ligand branches which are genuinely terminal under the actual
`officialCIPChildren` enumerator and whose root observations agree on the atomic-number projection,
the isotope-mass projection and the total Rule-1b root distance necessarily produce a completed
comparison certificate with outcome `Ordering.eq`, provided the two supplied descriptor contexts
are empty.

Nothing about the compiler output is assumed.  The successful key builds are derived from the
terminal-child hypothesis (`buildOfficialRuleMajorKey_of_terminal`), and the winning comparison is
derived from the actual projections of those keys (`officialRuleMajorRootKey_compare?_eq_some_eq`).
Only the three projections inspected by `OfficialRuleMajorKey.compare` are used; `sourceNodes` and
`complete` are never identified.

The one-centre adapter `OneCenterMolecule.cipOfficialCompareWithFuel_terminal_tie` maps this to
all `Fin 4` ligand pairs.  For `rootFromEdge` the Rule-1b distance is uniformly `1`, so the two
load-bearing premises supplied by chemical callers are the terminal-child equalities and the
atomic-number / isotope-mass equalities of the two ligand atoms.
-/

namespace TetraStereo
namespace OneCenter

noncomputable section

/-! ## Self-comparison of the addressed projections

These are small local copies of the structural lemmas used by the compiler-fidelity development;
they avoid importing the much larger downstream projection-fidelity module. -/

private theorem terminalTie_compareNat_self (value : ℕ) :
    OfficialRuleMajorKey.compareNat value value = Ordering.eq := by
  unfold OfficialRuleMajorKey.compareNat
  exact Std.ReflOrd.compare_self

private theorem terminalTie_compareRule1b_self (value : ℕ) :
    OfficialRuleMajorKey.compareRule1b value value = Ordering.eq := by
  unfold OfficialRuleMajorKey.compareRule1b
  exact terminalTie_compareNat_self value

private theorem terminalTie_list_compareLex_self {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq) :
    ∀ values : List α, List.compareLex cmp values values = Ordering.eq
  | [] => rfl
  | value :: values => by
      rw [List.compareLex_cons_cons, refl value]
      exact terminalTie_list_compareLex_self cmp refl values

private theorem terminalTie_compareSparseEntry_self {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (entry : OfficialSparseEntry α) :
    OfficialRuleMajorKey.compareSparseEntry cmp entry entry = Ordering.eq := by
  rcases entry with ⟨path, observation⟩
  have pathEqual :
      Ordering.byKey Prod.fst (flip (List.compareLex OfficialRuleMajorKey.compareNat))
          (path, observation) (path, observation) = Ordering.eq := by
    show List.compareLex OfficialRuleMajorKey.compareNat path path = Ordering.eq
    exact terminalTie_list_compareLex_self OfficialRuleMajorKey.compareNat
      terminalTie_compareNat_self path
  have observationEqual :
      Ordering.byKey Prod.snd cmp (path, observation) (path, observation) = Ordering.eq := by
    show cmp observation observation = Ordering.eq
    exact refl observation
  unfold OfficialRuleMajorKey.compareSparseEntry
  simp only [compareLex]
  rw [pathEqual, observationEqual]
  rfl

private theorem terminalTie_compareSparseLayer_self {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (layer : List (OfficialSparseEntry α)) :
    OfficialRuleMajorKey.compareSparseLayer cmp layer layer = Ordering.eq :=
  terminalTie_list_compareLex_self (OfficialRuleMajorKey.compareSparseEntry cmp)
    (fun entry => terminalTie_compareSparseEntry_self cmp refl entry) layer

private theorem terminalTie_compareSparseLayers_self {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq)
    (layers : List (List (OfficialSparseEntry α))) :
    OfficialRuleMajorKey.compareSparseLayers cmp layers layers = Ordering.eq :=
  terminalTie_list_compareLex_self (OfficialRuleMajorKey.compareSparseLayer cmp)
    (fun layer => terminalTie_compareSparseLayer_self cmp refl layer) layers

/-- Two keys with pointwise-equal Rule-1a, Rule-1b and Rule-2 projections compare equal under the
total rule-major comparator.  `sourceNodes` and `complete` are ignored, exactly as in the
comparator. -/
private theorem terminalTie_compare_eq_of_projection_eq {V : Type*}
    (left right : OfficialRuleMajorKey V)
    (h1a : left.rule1a = right.rule1a)
    (h1b : left.rule1b = right.rule1b)
    (h2 : left.rule2 = right.rule2) :
    OfficialRuleMajorKey.compare left right = Ordering.eq := by
  unfold OfficialRuleMajorKey.compare
  rw [compareLex_eq_eq, compareLex_eq_eq]
  refine ⟨?_, ?_, ?_⟩
  · show OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule1a right.rule1a = Ordering.eq
    rw [h1a]
    exact terminalTie_compareSparseLayers_self OfficialRuleMajorKey.compareNat
      terminalTie_compareNat_self right.rule1a
  · show OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
      left.rule1b right.rule1b = Ordering.eq
    rw [h1b]
    exact terminalTie_compareSparseLayers_self OfficialRuleMajorKey.compareRule1b
      terminalTie_compareRule1b_self right.rule1b
  · show OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      left.rule2 right.rule2 = Ordering.eq
    rw [h2]
    exact terminalTie_compareSparseLayers_self OfficialRuleMajorKey.compareNat
      terminalTie_compareNat_self right.rule2

namespace OfficialCIPNode

/-- A `rootFromEdge` node is a real atom at depth one, hence its total Rule-1b root distance is
`1`.  The distance therefore contributes no distinction between two root edges. -/
@[simp] theorem rule1bRootDistance_rootFromEdge {V : Type*} (parent current : V) :
    (rootFromEdge parent current).rule1bRootDistance = 1 :=
  rfl

end OfficialCIPNode

namespace MoleculeGraph

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The canonical root key's completeness flag is the flag passed to the constructor. -/
@[simp] theorem officialRuleMajorRootKey_complete (m : MoleculeGraph V)
    (node : OfficialCIPNode V) (complete : Bool) :
    (m.officialRuleMajorRootKey node complete).complete = complete :=
  rfl

/-- The official atom label of a `rootFromEdge` node is the raw label of its current atom. -/
@[simp] theorem officialNodeAtomLabel_rootFromEdge (m : MoleculeGraph V) (parent current : V) :
    m.officialNodeAtomLabel (OfficialCIPNode.rootFromEdge parent current) =
      m.rawCIPAtomLabel current :=
  rfl

/-- At every fuel, a node with no actual official children compiles to the canonical root key
marked complete.  This is derived from the compiler's defining equations; no key result is
assumed. -/
theorem buildOfficialRuleMajorKey_of_terminal (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) (fuel : ℕ)
    (node : OfficialCIPNode V) (terminal : children node = []) :
    m.buildOfficialRuleMajorKey children fuel node =
      some (m.officialRuleMajorRootKey node true) := by
  cases fuel with
  | zero => simp [buildOfficialRuleMajorKey, terminal]
  | succ fuel => simp [buildOfficialRuleMajorKey, terminal]

/-- Equal root observations (atomic number, isotope mass, total Rule-1b distance) make the two
canonical root keys compare equal under the exhaustive rule-major comparator. -/
theorem officialRuleMajorRootKey_compare_eq (m : MoleculeGraph V)
    (left right : OfficialCIPNode V)
    (hAtomic : (ofLex (m.officialNodeAtomLabel left)).1 =
      (ofLex (m.officialNodeAtomLabel right)).1)
    (hMass : (ofLex (m.officialNodeAtomLabel left)).2 =
      (ofLex (m.officialNodeAtomLabel right)).2)
    (hDistance : left.rule1bRootDistance = right.rule1bRootDistance) :
    OfficialRuleMajorKey.compare (m.officialRuleMajorRootKey left true)
      (m.officialRuleMajorRootKey right true) = Ordering.eq := by
  apply terminalTie_compare_eq_of_projection_eq
  · simp [hAtomic]
  · simp [hDistance]
  · simp [hMass]

/-- Under the same root-observation equalities the completed-key gate accepts the pair and
returns `Ordering.eq`; both canonical root keys carry `complete = true`. -/
theorem officialRuleMajorRootKey_compare?_eq_some_eq (m : MoleculeGraph V)
    (left right : OfficialCIPNode V)
    (hAtomic : (ofLex (m.officialNodeAtomLabel left)).1 =
      (ofLex (m.officialNodeAtomLabel right)).1)
    (hMass : (ofLex (m.officialNodeAtomLabel left)).2 =
      (ofLex (m.officialNodeAtomLabel right)).2)
    (hDistance : left.rule1bRootDistance = right.rule1bRootDistance) :
    OfficialRuleMajorKey.compare? (m.officialRuleMajorRootKey left true)
      (m.officialRuleMajorRootKey right true) = some Ordering.eq := by
  have h1a : (m.officialRuleMajorRootKey left true).rule1a =
      (m.officialRuleMajorRootKey right true).rule1a := by
    simp [hAtomic]
  have hcmp := m.officialRuleMajorRootKey_compare_eq left right hAtomic hMass hDistance
  unfold OfficialRuleMajorKey.compare?
  rw [h1a, terminalTie_compareSparseLayers_self OfficialRuleMajorKey.compareNat
    terminalTie_compareNat_self]
  dsimp only
  simp [hcmp]

/-- The actual bounded constitutional trace of two terminal roots with equal root observations is
the completed rule-major trace, obtained from the actual key builds. -/
theorem ruleMajorConstitutionalTraceWithFuel_of_terminal_tie (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) (fuel : ℕ)
    (leftRoot rightRoot : OfficialCIPNode V)
    (leftTerminal : children leftRoot = [])
    (rightTerminal : children rightRoot = [])
    (hAtomic : (ofLex (m.officialNodeAtomLabel leftRoot)).1 =
      (ofLex (m.officialNodeAtomLabel rightRoot)).1)
    (hMass : (ofLex (m.officialNodeAtomLabel leftRoot)).2 =
      (ofLex (m.officialNodeAtomLabel rightRoot)).2)
    (hDistance : leftRoot.rule1bRootDistance = rightRoot.rule1bRootDistance) :
    m.ruleMajorConstitutionalTraceWithFuel children fuel leftRoot rightRoot =
      some (OfficialRuleMajorKey.compareTrace (m.officialRuleMajorRootKey leftRoot true)
        (m.officialRuleMajorRootKey rightRoot true)) := by
  have hleft := m.buildOfficialRuleMajorKey_of_terminal children fuel leftRoot leftTerminal
  have hright := m.buildOfficialRuleMajorKey_of_terminal children fuel rightRoot rightTerminal
  have hcmp := m.officialRuleMajorRootKey_compare?_eq_some_eq leftRoot rightRoot
    hAtomic hMass hDistance
  unfold MoleculeGraph.ruleMajorConstitutionalTraceWithFuel
  rw [hleft]
  dsimp only
  rw [hright]
  dsimp only
  rw [hcmp]

/-- Uniform terminal-ligand tie at arbitrary fuel for the two-root official comparison.

Both roots are terminal under the actual child enumerator and have equal atomic-number,
isotope-mass and Rule-1b distance observations.  For empty Rule 3/4/5 contexts the corrected
bounded engine therefore returns a completed certificate whose outcome is `Ordering.eq`. -/
theorem compareRuleMajorRootsWithFuel_terminal_tie (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) (fuel : ℕ)
    (leftRoot rightRoot : OfficialCIPNode V)
    (leftTerminal : children leftRoot = [])
    (rightTerminal : children rightRoot = [])
    (hAtomic : (ofLex (m.officialNodeAtomLabel leftRoot)).1 =
      (ofLex (m.officialNodeAtomLabel rightRoot)).1)
    (hMass : (ofLex (m.officialNodeAtomLabel leftRoot)).2 =
      (ofLex (m.officialNodeAtomLabel rightRoot)).2)
    (hDistance : leftRoot.rule1bRootDistance = rightRoot.rule1bRootDistance)
    (leftContext rightContext : CIPRuleEngine.OfficialLigandRuleContext)
    (leftContextEmpty : leftContext = CIPRuleEngine.OfficialLigandRuleContext.empty)
    (rightContextEmpty : rightContext = CIPRuleEngine.OfficialLigandRuleContext.empty) :
    ∃ certificate,
      m.compareRuleMajorRootsWithFuel children fuel leftRoot rightRoot
        leftContext rightContext = some certificate ∧
      certificate.outcome = Ordering.eq := by
  have htrace := m.ruleMajorConstitutionalTraceWithFuel_of_terminal_tie children fuel
    leftRoot rightRoot leftTerminal rightTerminal hAtomic hMass hDistance
  have htraceOutcome :
      cipTraceOutcome (OfficialRuleMajorKey.compareTrace
        (m.officialRuleMajorRootKey leftRoot true)
        (m.officialRuleMajorRootKey rightRoot true)) = Ordering.eq := by
    rw [OfficialRuleMajorKey.compareTrace_outcome]
    exact m.officialRuleMajorRootKey_compare_eq leftRoot rightRoot hAtomic hMass hDistance
  refine ⟨CIPRuleEngine.compareDigraphThenOfficialCertificate
    (OfficialRuleMajorKey.compareTrace (m.officialRuleMajorRootKey leftRoot true)
      (m.officialRuleMajorRootKey rightRoot true)) leftContext rightContext, ?_, ?_⟩
  · unfold MoleculeGraph.compareRuleMajorRootsWithFuel
    rw [htrace]
    rfl
  · rw [CIPRuleEngine.compareDigraphThenOfficialCertificate_outcome]
    rw [CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_eq htraceOutcome]
    rw [leftContextEmpty, rightContextEmpty]
    exact CIPRuleEngine.compareOfficialContextTrace_self _

/-- Outcome form of the two-root terminal tie, convenient for certificate consumers. -/
theorem compareRuleMajorRootsWithFuel_terminal_tie_outcome (m : MoleculeGraph V)
    (children : OfficialCIPNode V → List (OfficialCIPNode V)) (fuel : ℕ)
    (leftRoot rightRoot : OfficialCIPNode V)
    (leftTerminal : children leftRoot = [])
    (rightTerminal : children rightRoot = [])
    (hAtomic : (ofLex (m.officialNodeAtomLabel leftRoot)).1 =
      (ofLex (m.officialNodeAtomLabel rightRoot)).1)
    (hMass : (ofLex (m.officialNodeAtomLabel leftRoot)).2 =
      (ofLex (m.officialNodeAtomLabel rightRoot)).2)
    (hDistance : leftRoot.rule1bRootDistance = rightRoot.rule1bRootDistance)
    (leftContext rightContext : CIPRuleEngine.OfficialLigandRuleContext)
    (leftContextEmpty : leftContext = CIPRuleEngine.OfficialLigandRuleContext.empty)
    (rightContextEmpty : rightContext = CIPRuleEngine.OfficialLigandRuleContext.empty) :
    (m.compareRuleMajorRootsWithFuel children fuel leftRoot rightRoot
        leftContext rightContext).map (fun certificate => certificate.outcome) =
      some Ordering.eq := by
  obtain ⟨certificate, hcomputed, houtcome⟩ :=
    m.compareRuleMajorRootsWithFuel_terminal_tie children fuel leftRoot rightRoot
      leftTerminal rightTerminal hAtomic hMass hDistance leftContext rightContext
      leftContextEmpty rightContextEmpty
  rw [hcomputed]
  simp [houtcome]

end MoleculeGraph

namespace OneCenterMolecule

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Uniform terminal-ligand tie for the corrected public one-centre comparison at arbitrary fuel.

The two actual `rootFromEdge` branches of ligands `i` and `j` are terminal under the actual
`officialCIPChildren` enumerator, the two ligand atoms carry equal atomic number and equal isotope
mass, and the two supplied descriptor contexts are empty.  Then
`cipOfficialCompareWithFuel context fuel i j` returns a completed certificate with outcome
`Ordering.eq`.  The Rule-1b distances of the two root edges are definitionally equal (`1`), so no
caller premise is required for them. -/
theorem cipOfficialCompareWithFuel_terminal_tie (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (fuel : ℕ) (i j : Fin 4)
    (leftTerminal : m.mol.officialCIPChildren
      (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom i)) = [])
    (rightTerminal : m.mol.officialCIPChildren
      (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom j)) = [])
    (atomicNumberEq : m.mol.atomZ (m.ligandAtom i) = m.mol.atomZ (m.ligandAtom j))
    (isotopeMassEq : m.mol.atomMass (m.ligandAtom i) = m.mol.atomMass (m.ligandAtom j))
    (leftContextEmpty : context i = CIPRuleEngine.OfficialLigandRuleContext.empty)
    (rightContextEmpty : context j = CIPRuleEngine.OfficialLigandRuleContext.empty) :
    ∃ certificate,
      m.cipOfficialCompareWithFuel context fuel i j = some certificate ∧
      certificate.outcome = Ordering.eq := by
  have hAtomic : (ofLex (m.mol.officialNodeAtomLabel
        (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom i)))).1 =
      (ofLex (m.mol.officialNodeAtomLabel
        (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom j)))).1 := by
    simpa [MoleculeGraph.rawCIPAtomLabel, ofLex_toLex] using atomicNumberEq
  have hMass : (ofLex (m.mol.officialNodeAtomLabel
        (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom i)))).2 =
      (ofLex (m.mol.officialNodeAtomLabel
        (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom j)))).2 := by
    simpa [MoleculeGraph.rawCIPAtomLabel, ofLex_toLex] using isotopeMassEq
  have hDistance :
      (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom i)).rule1bRootDistance =
        (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom j)).rule1bRootDistance := by
    simp
  unfold OneCenterMolecule.cipOfficialCompareWithFuel
  exact MoleculeGraph.compareRuleMajorRootsWithFuel_terminal_tie m.mol
    m.mol.officialCIPChildren fuel
    (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom i))
    (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom j))
    leftTerminal rightTerminal hAtomic hMass hDistance
    (context i) (context j) leftContextEmpty rightContextEmpty

/-- Outcome form of the one-centre terminal tie at arbitrary fuel. -/
theorem cipOfficialCompareWithFuel_terminal_tie_outcome (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (fuel : ℕ) (i j : Fin 4)
    (leftTerminal : m.mol.officialCIPChildren
      (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom i)) = [])
    (rightTerminal : m.mol.officialCIPChildren
      (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom j)) = [])
    (atomicNumberEq : m.mol.atomZ (m.ligandAtom i) = m.mol.atomZ (m.ligandAtom j))
    (isotopeMassEq : m.mol.atomMass (m.ligandAtom i) = m.mol.atomMass (m.ligandAtom j))
    (leftContextEmpty : context i = CIPRuleEngine.OfficialLigandRuleContext.empty)
    (rightContextEmpty : context j = CIPRuleEngine.OfficialLigandRuleContext.empty) :
    (m.cipOfficialCompareWithFuel context fuel i j).map
        (fun certificate => certificate.outcome) = some Ordering.eq := by
  obtain ⟨certificate, hcomputed, houtcome⟩ :=
    m.cipOfficialCompareWithFuel_terminal_tie context fuel i j leftTerminal rightTerminal
      atomicNumberEq isotopeMassEq leftContextEmpty rightContextEmpty
  rw [hcomputed]
  simp [houtcome]

/-- The total public comparison at the proved stable default fuel also returns an exact tie for
the same terminal pair with empty contexts. -/
theorem cipOfficialCompare_terminal_tie (m : OneCenterMolecule V)
    (context : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext) (i j : Fin 4)
    (leftTerminal : m.mol.officialCIPChildren
      (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom i)) = [])
    (rightTerminal : m.mol.officialCIPChildren
      (OfficialCIPNode.rootFromEdge m.center (m.ligandAtom j)) = [])
    (atomicNumberEq : m.mol.atomZ (m.ligandAtom i) = m.mol.atomZ (m.ligandAtom j))
    (isotopeMassEq : m.mol.atomMass (m.ligandAtom i) = m.mol.atomMass (m.ligandAtom j))
    (leftContextEmpty : context i = CIPRuleEngine.OfficialLigandRuleContext.empty)
    (rightContextEmpty : context j = CIPRuleEngine.OfficialLigandRuleContext.empty) :
    (m.cipOfficialCompare context i j).outcome = Ordering.eq := by
  obtain ⟨certificate, hcomputed, houtcome⟩ :=
    m.cipOfficialCompareWithFuel_terminal_tie context (Fintype.card V + 1) i j
      leftTerminal rightTerminal atomicNumberEq isotopeMassEq
      leftContextEmpty rightContextEmpty
  have hdefault := m.cipOfficialCompareWithFuel_default_eq_some context i j
  rw [hdefault] at hcomputed
  have hcertificate : m.cipOfficialCompare context i j = certificate :=
    Option.some.inj hcomputed
  rw [hcertificate, houtcome]

assert_kernel_only TetraStereo.OneCenter.MoleculeGraph.buildOfficialRuleMajorKey_of_terminal
assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.officialRuleMajorRootKey_compare?_eq_some_eq
assert_kernel_only
  TetraStereo.OneCenter.MoleculeGraph.compareRuleMajorRootsWithFuel_terminal_tie
assert_kernel_only TetraStereo.OneCenter.OneCenterMolecule.cipOfficialCompareWithFuel_terminal_tie
assert_kernel_only TetraStereo.OneCenter.OneCenterMolecule.cipOfficialCompare_terminal_tie

end OneCenterMolecule

end

end OneCenter
end TetraStereo
