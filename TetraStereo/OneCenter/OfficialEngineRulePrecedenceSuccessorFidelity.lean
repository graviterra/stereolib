import TetraStereo.OneCenter.OfficialCIPEngine
import TetraStereo.OneCenter.OfficialRuleMajorCompilerProjectionFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace OfficialEngineRulePrecedenceSuccessorFidelity

noncomputable section

/-!
# Corrected public-engine rule-precedence successor

The frozen module `OfficialEngineRulePrecedenceFidelity` records a real pre-repair defect: on the
eleven-atom witness `[C@](Br)(Cl)([13CH3])[12CH2]F` the historical public comparator returned
`Ordering.gt` for the isotope-13 methyl ligand (index 2) against the isotope-12 fluoromethyl
ligand (index 3), because a root-sphere Rule-2 (mass 13 versus 12) decision pre-empted the deeper
Rule-1a difference (fluorine, Z = 9, versus hydrogen, Z = 1).  That module is historical evidence
and must remain frozen; its `live_outcome_gt` does not typecheck against the corrected engine.

This successor module proves the repaired behaviour on the *same* witness graph, against the
*actual* corrected public engine:

* `bounded_outcome_lt`: the corrected bounded entry point
  `OneCenterMolecule.cipOfficialCompareWithFuel witnessContext 12 2 3` has outcome
  `Ordering.lt`;
* `cipOfficialCompare_outcome_lt`: the total public `OneCenterMolecule.cipOfficialCompare` has
  outcome `Ordering.lt`;
* `cipOfficialEngine_outcome_lt`: the public `cipOfficialEngine` result has the same outcome;
* `bounded_outcome_stable_default`: every larger fuel `(Fintype.card (Fin 11) + 1) + extra`
  agrees.

The proof does not assume any whole-key equality between the actual official child enumeration
and an executable enumeration.  `MoleculeGraph.officialCIPChildren` is noncomputable
(`Finset.toList` uses choice), so the explicit keys are connected to the actual compiled keys by
the pointwise permutation `officialCIPChildren_perm` and the already-integrated
`CompilerProjectionFidelity` transport of the Rule-1a/1b/2 projections and of `compare?` /
`compare`.  No result below assumes the desired `Ordering.lt`; it is derived from the explicit
graph labels and the exhaustive rule-major comparator.

No chemical universality is claimed.  This is one kernel-checked witness, not a theorem about all
molecules, all isotopes, or all substituted methyl groups.  The Rule-3/4/5 context supplied here
is the empty context: the argument is purely constitutional, and no pseudosign, geometry, or
source-calibration claim is made or touched.
-/

/-! ## The admitted witness graph -/

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

/-- The ten single bonds of the witness. -/
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

/-- Root of the isotope-13 methyl ligand branch. -/
abbrev rootC13 : OfficialCIPNode (Fin 11) :=
  OfficialCIPNode.rootFromEdge 0 3

/-- Root of the isotope-12 fluoromethyl ligand branch. -/
abbrev rootC12F : OfficialCIPNode (Fin 11) :=
  OfficialCIPNode.rootFromEdge 0 4

/-- Empty Rule-3/4/5 context: the witness is purely constitutional. -/
abbrev witnessContext : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext :=
  fun _ => CIPRuleEngine.OfficialLigandRuleContext.empty

/-! ## Explicit child enumerator and its permutation bridge

`MoleculeGraph.officialCIPChildren` is noncomputable because `Finset.toList` uses choice.  The
lemmas below prove that an explicit, computable enumerator is a pointwise permutation of it, node
by node.  This is the only bridge needed: the integrated `CompilerProjectionFidelity` module
transports the three constitutional projections and the rule-tagged trace across such a
permutation, so no whole-key equality is assumed anywhere.
-/

/-- Explicit neighbour list of each witness atom (all bonds single). -/
def witnessNeighborList (atom : Fin 11) : List (Fin 11) :=
  match atom.val with
  | 0 => [1, 2, 3, 4]
  | 1 => [0]
  | 2 => [0]
  | 3 => [0, 6, 7, 8]
  | 4 => [0, 5, 9, 10]
  | 5 => [4]
  | 6 => [3]
  | 7 => [3]
  | 8 => [3]
  | 9 => [4]
  | 10 => [4]
  | _ => []

/-- Neighbour copies with copy indices, mirroring `officialNeighborCopies`. -/
def witnessNeighborCopies (atom : Fin 11) : List (Fin 11 × ℕ) :=
  (witnessNeighborList atom).flatMap fun neighbor =>
    (List.range (witnessGraph.bond atom neighbor)).map fun copyIndex =>
      (neighbor, copyIndex)

/-- Child copies with the stored parent occurrence removed, mirroring `officialChildCopies`. -/
def witnessAllChildCopies (node : OfficialCIPNode (Fin 11)) : List (Fin 11 × ℕ) :=
  match node.current? with
  | none => []
  | some current =>
      match node.parent? with
      | none => witnessNeighborCopies current
      | some parent =>
          (witnessNeighborCopies current).filter fun copy =>
            !(copy.1 == parent && copy.2 == 0)

/-- Explicit child enumerator, mirroring `officialCIPChildren`. -/
def witnessAllChildren (node : OfficialCIPNode (Fin 11)) :
    List (OfficialCIPNode (Fin 11)) :=
  if node.isDuplicateLeaf then
    []
  else
    (witnessAllChildCopies node).map fun copy => node.extend copy.1 copy.2

theorem witnessNeighborList_nodup (atom : Fin 11) :
    (witnessNeighborList atom).Nodup := by
  fin_cases atom <;> decide

/-- Membership in the explicit neighbour list is exactly graph adjacency. -/
theorem mem_witnessNeighborList (atom neighbor : Fin 11) :
    neighbor ∈ witnessNeighborList atom ↔ witnessGraph.Adj atom neighbor := by
  fin_cases atom <;> fin_cases neighbor <;> decide

/-- The actual official neighbour-copy enumeration is a permutation of the explicit one. -/
theorem officialNeighborCopies_perm (atom : Fin 11) :
    (witnessGraph.officialNeighborCopies atom).Perm (witnessNeighborCopies atom) := by
  have listPerm :
      (witnessGraph.neighborFinset atom).toList.Perm (witnessNeighborList atom) := by
    apply List.perm_of_nodup_nodup_toFinset_eq (Finset.nodup_toList _)
    · exact witnessNeighborList_nodup atom
    · rw [Finset.toList_toFinset]
      apply Finset.ext
      intro neighbor
      simp [mem_witnessNeighborList]
  unfold MoleculeGraph.officialNeighborCopies witnessNeighborCopies
  exact List.Perm.flatMap_right
    (fun neighbor : Fin 11 =>
      (List.range (witnessGraph.bond atom neighbor)).map
        (fun copyIndex => (neighbor, copyIndex)))
    listPerm

/-- Parent-aware child-copy enumeration is permutation-equivariant node by node. -/
theorem officialChildCopies_perm (node : OfficialCIPNode (Fin 11)) :
    (witnessGraph.officialChildCopies node).Perm (witnessAllChildCopies node) := by
  cases currentEq : node.current? with
  | none =>
      simp [MoleculeGraph.officialChildCopies, witnessAllChildCopies, currentEq]
  | some current =>
      cases parentEq : node.parent? with
      | none =>
          simpa [MoleculeGraph.officialChildCopies, witnessAllChildCopies,
            currentEq, parentEq] using officialNeighborCopies_perm current
      | some parent =>
          have filtered := List.Perm.filter
            (fun copy : Fin 11 × ℕ => !(copy.1 == parent && copy.2 == 0))
            (officialNeighborCopies_perm current)
          simpa [MoleculeGraph.officialChildCopies, witnessAllChildCopies,
            currentEq, parentEq] using filtered

/-- The actual official child enumeration is a pointwise permutation of the explicit one. -/
theorem officialCIPChildren_perm (node : OfficialCIPNode (Fin 11)) :
    (witnessGraph.officialCIPChildren node).Perm (witnessAllChildren node) := by
  by_cases duplicate : node.isDuplicateLeaf = true
  · simp [MoleculeGraph.officialCIPChildren, witnessAllChildren, duplicate]
  · have notDuplicate : node.isDuplicateLeaf = false := by
      cases value : node.isDuplicateLeaf with
      | false => rfl
      | true => exact absurd value duplicate
    have mapped := List.Perm.map (fun copy : Fin 11 × ℕ => node.extend copy.1 copy.2)
      (officialChildCopies_perm node)
    simpa [MoleculeGraph.officialCIPChildren, witnessAllChildren, notDuplicate] using mapped

/-! ## Explicit rule-major keys -/

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

/-- The exhaustive rule-major key compiled for the `^12CH2F` ligand branch. -/
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

/-- The explicit compiler run for the `^13CH3` branch.  Fuel twelve is enough: the reached tree
has depth two, and the leaves terminate the recursion. -/
theorem build_rootC13 :
    witnessGraph.buildOfficialRuleMajorKey witnessAllChildren 12 rootC13 = some keyC13 := rfl

/-- The explicit compiler run for the `^12CH2F` branch. -/
theorem build_rootC12F :
    witnessGraph.buildOfficialRuleMajorKey witnessAllChildren 12 rootC12F = some keyC12F := rfl

/-- The compiled keys are source-aligned with the explicit provenance tree. -/
theorem keyC13_sourceAligned :
    OfficialRuleMajorKey.SourceAligned witnessGraph keyC13 :=
  witnessGraph.buildOfficialRuleMajorKey_sourceAligned
    witnessAllChildren 12 rootC13 keyC13 build_rootC13

theorem keyC12F_sourceAligned :
    OfficialRuleMajorKey.SourceAligned witnessGraph keyC12F :=
  witnessGraph.buildOfficialRuleMajorKey_sourceAligned
    witnessAllChildren 12 rootC12F keyC12F build_rootC12F

@[simp] theorem keyC13_rule1a_exact :
    keyC13.rule1a = [[([], 6)], [([0], 1), ([1], 1), ([2], 1)]] := rfl

@[simp] theorem keyC12F_rule1a_exact :
    keyC12F.rule1a = [[([], 6)], [([0], 9), ([1], 1), ([2], 1)]] := rfl

/-! ## Exhaustive rule order on the explicit keys -/

/-- A decisive Rule-1a projection determines the full rule-major comparison, before any Rule-1b
or Rule-2 observation is consulted.  This is the exhaustive-rule-order semantics required by
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

/-- Exhaustive Rule 1a places `^12CH2F` above `^13CH3`: the only strict difference in the two
complete addressed Rule-1a projections is at sphere II, where the fluoromethyl branch exposes
Z = 9 and the methyl branch exposes Z = 1. -/
theorem keyC12F_above_keyC13_by_rule1a :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyC12F.rule1a keyC13.rule1a = Ordering.gt := by
  decide

/-- The opposite orientation, matching the stored left-to-right engine order. -/
theorem keyC13_below_keyC12F_by_rule1a :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyC13.rule1a keyC12F.rule1a = Ordering.lt := by
  decide

/-- Rule 2 at the root sphere, taken in isolation, prefers `^13CH3` (mass 13 over mass 12).
Exhaustive Rule 1a must pre-empt it. -/
theorem keyC13_above_keyC12F_by_rule2 :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
      keyC13.rule2 keyC12F.rule2 = Ordering.gt := by
  decide

/-- The explicit rule-major comparator ranks `^13CH3` below `^12CH2F`. -/
theorem ruleMajor_compare_lt :
    OfficialRuleMajorKey.compare keyC13 keyC12F = Ordering.lt := by
  rw [ruleMajor_compare_eq_rule1a_of_decisive]
  · exact keyC13_below_keyC12F_by_rule1a
  · rw [keyC13_below_keyC12F_by_rule1a]
    decide

/-- The reverse orientation of the explicit comparator. -/
theorem ruleMajor_compare_gt_reverse :
    OfficialRuleMajorKey.compare keyC12F keyC13 = Ordering.gt := by
  rw [ruleMajor_compare_eq_rule1a_of_decisive]
  · exact keyC12F_above_keyC13_by_rule1a
  · rw [keyC12F_above_keyC13_by_rule1a]
    decide

/-- The completeness-guarded rule-major entry point returns the strict Rule-1a outcome. -/
theorem ruleMajor_compare?_lt :
    OfficialRuleMajorKey.compare? keyC13 keyC12F = some Ordering.lt := by
  decide

/-! ## The corrected actual public engine -/

/-- The default finite-atom fuel of the witness is the literal fuel used by the explicit
compiler runs. -/
theorem fuel_default_eq_twelve : Fintype.card (Fin 11) + 1 = 12 := by
  simp [Fintype.card_fin]

/-- Bounded corrected-engine outcome on the two ligand roots at explicit fuel twelve.

The actual official child enumeration is first connected to the explicit enumerator by
`officialCIPChildren_perm`; `CompilerProjectionFidelity` then transports the Rule-1a/1b/2
projections and `compare?`/`compare` to the explicit keys, where exhaustive Rule 1a decides.
The desired `Ordering.lt` is never assumed: the gate equation is transported from the explicit
`decide`-checked Rule-1a outcome. -/
theorem bounded_outcome_lt :
    (witnessMolecule.cipOfficialCompareWithFuel witnessContext 12 2 3).map
        (fun certificate => certificate.outcome) = some Ordering.lt := by
  obtain ⟨leftKey, leftComputed, _⟩ :=
    witnessMolecule.cipOfficialRuleMajorKey_complete_default 2
  obtain ⟨rightKey, rightComputed, _⟩ :=
    witnessMolecule.cipOfficialRuleMajorKey_complete_default 3
  have leftComputed12 :
      witnessGraph.buildOfficialRuleMajorKey witnessGraph.officialCIPChildren 12
        (OfficialCIPNode.rootFromEdge 0 3) = some leftKey := by
    simpa [OneCenterMolecule.cipOfficialRuleMajorKeyWithFuel, witnessMolecule,
      witnessLigand, Fintype.card_fin] using leftComputed
  have rightComputed12 :
      witnessGraph.buildOfficialRuleMajorKey witnessGraph.officialCIPChildren 12
        (OfficialCIPNode.rootFromEdge 0 4) = some rightKey := by
    simpa [OneCenterMolecule.cipOfficialRuleMajorKeyWithFuel, witnessMolecule,
      witnessLigand, Fintype.card_fin] using rightComputed
  have sameLeft :=
    CompilerProjectionFidelity.build_sameConstitution_of_children_perm
      witnessGraph witnessGraph.officialCIPChildren witnessAllChildren
      officialCIPChildren_perm 12 (OfficialCIPNode.rootFromEdge 0 3)
      leftKey keyC13 leftComputed12 build_rootC13
  have sameRight :=
    CompilerProjectionFidelity.build_sameConstitution_of_children_perm
      witnessGraph witnessGraph.officialCIPChildren witnessAllChildren
      officialCIPChildren_perm 12 (OfficialCIPNode.rootFromEdge 0 4)
      rightKey keyC12F rightComputed12 build_rootC12F
  have gate : OfficialRuleMajorKey.compare? leftKey rightKey = some Ordering.lt := by
    rw [CompilerProjectionFidelity.compare?_congr_of_sameConstitution sameLeft sameRight]
    exact ruleMajor_compare?_lt
  have compareLt : OfficialRuleMajorKey.compare leftKey rightKey = Ordering.lt :=
    OfficialRuleMajorKey.compare_eq_of_compare?_eq_some leftKey rightKey
      Ordering.lt gate
  have traceOutcome :
      cipTraceOutcome (OfficialRuleMajorKey.compareTrace leftKey rightKey) =
        Ordering.lt := by
    rw [OfficialRuleMajorKey.compareTrace_outcome, compareLt]
  simp only [OneCenterMolecule.cipOfficialCompareWithFuel]
  change ((witnessGraph.compareRuleMajorRootsWithFuel witnessGraph.officialCIPChildren 12
      rootC13 rootC12F (witnessContext 2) (witnessContext 3)).map
        (fun certificate => certificate.outcome)) = some Ordering.lt
  unfold MoleculeGraph.compareRuleMajorRootsWithFuel
    MoleculeGraph.ruleMajorConstitutionalTraceWithFuel
  simp only [leftComputed12, rightComputed12, gate, Option.map_some,
    Option.some.injEq]
  rw [CIPRuleEngine.compareDigraphThenOfficialCertificate_outcome]
  rw [CIPRuleEngine.compareDigraphThenOfficialTrace_outcome_of_digraph_ne_eq]
  · exact traceOutcome
  · rw [traceOutcome]
    decide

/-- The bounded computation at the proved default fuel has the same strict outcome. -/
theorem bounded_default_outcome_lt :
    (witnessMolecule.cipOfficialCompareWithFuel witnessContext
        (Fintype.card (Fin 11) + 1) 2 3).map
      (fun certificate => certificate.outcome) = some Ordering.lt := by
  rw [fuel_default_eq_twelve]
  exact bounded_outcome_lt

/-- The total corrected public comparison ranks ligand 2 (`^13CH3`) below ligand 3 (`^12CH2F`). -/
theorem cipOfficialCompare_outcome_lt :
    (witnessMolecule.cipOfficialCompare witnessContext 2 3).outcome = Ordering.lt := by
  have bounded := bounded_default_outcome_lt
  rw [witnessMolecule.cipOfficialCompareWithFuel_default_eq_some witnessContext 2 3] at bounded
  simpa [Option.map_some, Option.some.injEq] using bounded

/-- The trace of the total corrected public comparison evaluates to the strict Rule-1a
outcome. -/
theorem cipOfficialCompare_trace_outcome_lt :
    cipTraceOutcome (witnessMolecule.cipOfficialCompare witnessContext 2 3).trace =
      Ordering.lt := by
  rw [(witnessMolecule.cipOfficialCompare witnessContext 2 3).sound]
  exact cipOfficialCompare_outcome_lt

/-- The same strict outcome through the public `cipOfficialEngine` result structure. -/
theorem cipOfficialEngine_outcome_lt :
    ((witnessMolecule.cipOfficialEngine witnessContext).compare 2 3).outcome =
      Ordering.lt := by
  rw [OneCenterMolecule.cipOfficialEngine_compare]
  exact cipOfficialCompare_outcome_lt

/-- Any larger fuel beyond the default atom-cardinality bound agrees with the strict default
outcome. -/
theorem bounded_outcome_stable_default (extra : ℕ) :
    (witnessMolecule.cipOfficialCompareWithFuel witnessContext
        ((Fintype.card (Fin 11) + 1) + extra) 2 3).map
      (fun certificate => certificate.outcome) = some Ordering.lt := by
  rw [witnessMolecule.cipOfficialCompareWithFuel_outcome_stable_default
    witnessContext 2 3 extra]
  rw [cipOfficialCompare_outcome_lt]

/-- The exact engine-level computation that a migrated
`Engine.OfficialStereoRequest.certificate` performs when its one-center molecule is this witness,
its context is the empty witness context, its `graphFuel` is `12`, and its indices are `2` and
`3`.  The transaction module is integrated separately; this theorem fixes the value its
definitional bridge consumes. -/
theorem transaction_call_path_outcome_lt :
    (witnessMolecule.cipOfficialCompareWithFuel witnessContext 12 2 3).map
        (fun certificate => certificate.outcome) = some Ordering.lt :=
  bounded_outcome_lt

/-! ## Graph evidence and successor summary -/

/-- Sphere II of the `^13CH3` branch contains hydrogen: Z = 1, read from the actual graph node. -/
theorem deeper_hydrogen_witness :
    (ofLex (witnessGraph.officialNodeAtomLabel
      (OfficialCIPNode.extend rootC13 6 0))).1 = 1 := rfl

/-- Sphere II of the `^12CH2F` branch contains fluorine: Z = 9, read from the actual graph
node. -/
theorem deeper_fluorine_witness :
    (ofLex (witnessGraph.officialNodeAtomLabel
      (OfficialCIPNode.extend rootC12F 5 0))).1 = 9 := rfl

/-- The root Rule-2 masses read from the actual graph nodes. -/
theorem root_mass_witnesses :
    (ofLex (witnessGraph.officialNodeAtomLabel rootC13)).2 = 13 ∧
      (ofLex (witnessGraph.officialNodeAtomLabel rootC12F)).2 = 12 := by
  constructor <;> rfl

/-- The source-priority requirement is derived from actual node labels, not from the desired
outcome: Rule 1a points to `^12CH2F`, root Rule 2 points to `^13CH3`, and exhaustive rule order
follows Rule 1a. -/
theorem source_rule1a_preempts_root_rule2 :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        keyC12F.rule1a keyC13.rule1a = Ordering.gt ∧
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        keyC13.rule2 keyC12F.rule2 = Ordering.gt ∧
      OfficialRuleMajorKey.compare keyC13 keyC12F = Ordering.lt :=
  ⟨keyC12F_above_keyC13_by_rule1a, keyC13_above_keyC12F_by_rule2, ruleMajor_compare_lt⟩

/-- The corrected successor summary.  On one admitted graph, the corrected actual public engine
ranks `^13CH3` below `^12CH2F`; the explicit rule-major keys compile from the explicit
enumerator, are source-aligned, and the deeper Rule-1a difference is the deciding evidence. -/
theorem corrected_public_engine_rule_precedence :
    (witnessMolecule.cipOfficialCompare witnessContext 2 3).outcome = Ordering.lt ∧
      ((witnessMolecule.cipOfficialEngine witnessContext).compare 2 3).outcome =
        Ordering.lt ∧
      OfficialRuleMajorKey.compare keyC13 keyC12F = Ordering.lt ∧
      witnessGraph.buildOfficialRuleMajorKey witnessAllChildren 12 rootC13 = some keyC13 ∧
      witnessGraph.buildOfficialRuleMajorKey witnessAllChildren 12 rootC12F = some keyC12F ∧
      OfficialRuleMajorKey.SourceAligned witnessGraph keyC13 ∧
      OfficialRuleMajorKey.SourceAligned witnessGraph keyC12F :=
  ⟨cipOfficialCompare_outcome_lt, cipOfficialEngine_outcome_lt, ruleMajor_compare_lt,
    build_rootC13, build_rootC12F, keyC13_sourceAligned, keyC12F_sourceAligned⟩

/-! ## Kernel-authority guards -/

assert_kernel_only witnessBond_symm
assert_kernel_only witnessBond_self
assert_kernel_only witnessLigand_adj
assert_kernel_only witnessLigand_injective
assert_kernel_only witnessLigand_surjective
assert_kernel_only witnessNeighborList_nodup
assert_kernel_only mem_witnessNeighborList
assert_kernel_only officialNeighborCopies_perm
assert_kernel_only officialChildCopies_perm
assert_kernel_only officialCIPChildren_perm
assert_kernel_only build_rootC13
assert_kernel_only build_rootC12F
assert_kernel_only keyC13_sourceAligned
assert_kernel_only keyC12F_sourceAligned
assert_kernel_only keyC13_rule1a_exact
assert_kernel_only keyC12F_rule1a_exact
assert_kernel_only ruleMajor_compare_eq_rule1a_of_decisive
assert_kernel_only keyC12F_above_keyC13_by_rule1a
assert_kernel_only keyC13_below_keyC12F_by_rule1a
assert_kernel_only keyC13_above_keyC12F_by_rule2
assert_kernel_only ruleMajor_compare_lt
assert_kernel_only ruleMajor_compare_gt_reverse
assert_kernel_only ruleMajor_compare?_lt
assert_kernel_only fuel_default_eq_twelve
assert_kernel_only bounded_outcome_lt
assert_kernel_only bounded_default_outcome_lt
assert_kernel_only cipOfficialCompare_outcome_lt
assert_kernel_only cipOfficialCompare_trace_outcome_lt
assert_kernel_only cipOfficialEngine_outcome_lt
assert_kernel_only bounded_outcome_stable_default
assert_kernel_only transaction_call_path_outcome_lt
assert_kernel_only deeper_hydrogen_witness
assert_kernel_only deeper_fluorine_witness
assert_kernel_only root_mass_witnesses
assert_kernel_only source_rule1a_preempts_root_rule2
assert_kernel_only corrected_public_engine_rule_precedence

end

end OfficialEngineRulePrecedenceSuccessorFidelity
end OneCenter
end TetraStereo
