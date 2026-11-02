import TetraStereo.OneCenter.CIPRules
import TetraStereo.OneCenter.OfficialCIPEngine
import TetraStereo.OneCenter.RS
import TetraStereo.OneCenter.Toy
import Mathlib.Tactic.FinCases

set_option autoImplicit false

namespace TetraStereo
namespace Examples

open OneCenter

/-!
  A small graph model of 1-phenylethanol.

  The stereocenter is the benzylic carbon in `CH(OH)(Ph)(CH₃)(H)`.  The phenyl substituent is
  represented by a six-carbon ring with alternating bond orders; this is still not a full aromatic
  CIP formalization, but it is enough to test the current cycle-cut/frontier machinery on a real
  organic motif with a cyclic ligand.
-/

namespace OnePhenylethanol

open OneCenter.TetrahedralGeometry

inductive Atom where
  | center
  | oxygen
  | hydroxylH
  | phenyl0
  | phenyl1
  | phenyl2
  | phenyl3
  | phenyl4
  | phenyl5
  | methyl
  | methylH1
  | methylH2
  | methylH3
  | centerH
  deriving DecidableEq, Repr, Fintype

open Atom

def atomZ : Atom → AtomicNumber
  | oxygen => 8
  | hydroxylH => 1
  | methylH1 => 1
  | methylH2 => 1
  | methylH3 => 1
  | centerH => 1
  | _ => 6

/-- A Kekulé-style graph for the phenyl ring, with alternating double/single bonds. -/
def bond : Atom → Atom → BondOrder
  | center, oxygen => 1
  | oxygen, center => 1
  | oxygen, hydroxylH => 1
  | hydroxylH, oxygen => 1
  | center, phenyl0 => 1
  | phenyl0, center => 1
  | center, methyl => 1
  | methyl, center => 1
  | center, centerH => 1
  | centerH, center => 1
  | methyl, methylH1 => 1
  | methylH1, methyl => 1
  | methyl, methylH2 => 1
  | methylH2, methyl => 1
  | methyl, methylH3 => 1
  | methylH3, methyl => 1
  | phenyl0, phenyl1 => 2
  | phenyl1, phenyl0 => 2
  | phenyl1, phenyl2 => 1
  | phenyl2, phenyl1 => 1
  | phenyl2, phenyl3 => 2
  | phenyl3, phenyl2 => 2
  | phenyl3, phenyl4 => 1
  | phenyl4, phenyl3 => 1
  | phenyl4, phenyl5 => 2
  | phenyl5, phenyl4 => 2
  | phenyl5, phenyl0 => 1
  | phenyl0, phenyl5 => 1
  | _, _ => 0

def mol : MoleculeGraph Atom where
  atomZ := atomZ
  bond := bond
  bond_symm := by
    intro u v
    cases u <;> cases v <;> simp [bond]
  bond_self := by
    intro u
    cases u <;> simp [bond]

/-- Ligand index convention: `OH > phenyl > methyl > H` is expected for the current descriptor key. -/
def oneCenter : OneCenterMolecule Atom where
  mol := mol
  center := center
  ligandAtom
    | 0 => oxygen
    | 1 => phenyl0
    | 2 => methyl
    | 3 => centerH
  ligandAtom_adj := by
    intro i
    fin_cases i <;> simp [MoleculeGraph.Adj, mol, bond]
  ligandAtom_injective := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢
  ligandAtom_surjective := by
    intro v hv
    cases v <;> simp [MoleculeGraph.Adj, mol, bond] at hv ⊢
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

/-- A canonical right-handed local realization for the 1-phenylethanol stereocenter. -/
def rightRealization : TetrahedralGeometry.Realization :=
  ⟨canonicalGeometry rightHandedFrame, canonicalGeometry_nondegenerate rightHandedFrame⟩

/-- A canonical left-handed local realization for the 1-phenylethanol stereocenter. -/
def leftRealization : TetrahedralGeometry.Realization :=
  ⟨canonicalGeometry leftHandedFrame, canonicalGeometry_nondegenerate leftHandedFrame⟩

@[simp] theorem rightRealization_handedness :
    handedness rightRealization.1 = 1 := by
  simpa [rightRealization, rightHandedFrame] using
    canonicalHandedness_matches_parity rightHandedFrame

@[simp] theorem leftRealization_handedness :
    handedness leftRealization.1 = -1 := by
  simpa [leftRealization, leftHandedFrame] using
    canonicalHandedness_matches_parity leftHandedFrame

noncomputable section

open Prod.Lex

/-- This example has no descriptor-rich Rule 3/4/5 branch facts to add; the canonical official
engine therefore uses empty contexts and lets the hierarchical digraph decide. -/
def officialEmptyContext : Fin 4 → CIPRuleEngine.OfficialLigandRuleContext :=
  fun _ => CIPRuleEngine.OfficialLigandRuleContext.empty

def ligandZ : Fin 4 → AtomicNumber :=
  ![8, 6, 6, 1]

private def oxygenLabel : MoleculeGraph.AtomLabel := toLex (8, 0)
private def carbonLabel : MoleculeGraph.AtomLabel := toLex (6, 0)
private def hydrogenLabel : MoleculeGraph.AtomLabel := toLex (1, 0)

/-- First-layer descriptor labels for the stereocenter ligands:
`OH`, phenyl carbon, methyl carbon, and hydrogen. -/
private theorem cipKeyCycleCut_head? (i : Fin 4) :
    (oneCenter.cipKeyCycleCut i).head? = some (toLex (ligandZ i, 0)) := by
  fin_cases i <;>
    simp [OneCenterMolecule.cipKeyCycleCut, oneCenter, mol, ligandZ, atomZ,
      MoleculeGraph.cipKeyFromCycleCut_head?]

/-- The descriptor-facing alias exposes the same first-layer labels. -/
private theorem cipKeyDescriptor_head? (i : Fin 4) :
    (oneCenter.cipKeyDescriptor i).head? = some (toLex (ligandZ i, 0)) := by
  fin_cases i <;>
    simp [OneCenterMolecule.cipKeyDescriptor, OneCenterMolecule.cipKeyCycleCut,
      oneCenter, mol, ligandZ, atomZ, MoleculeGraph.cipKeyFromCycleCut_head?]

private theorem rawChildren_phenyl0_perm :
    (mol.rawCIPChildren center phenyl0).Perm [phenyl1, phenyl1, phenyl5] := by
  rw [MoleculeGraph.rawCIPChildren]
  rw [List.perm_iff_count]
  intro a
  cases a <;> simp [MoleculeGraph.count_rawCIPNeighborListWithMultiplicity_eq_bond, mol, bond]

private theorem rawChildren_methyl_perm :
    (mol.rawCIPChildren center methyl).Perm [methylH1, methylH2, methylH3] := by
  rw [MoleculeGraph.rawCIPChildren]
  rw [List.perm_iff_count]
  intro a
  cases a <;> simp [MoleculeGraph.count_rawCIPNeighborListWithMultiplicity_eq_bond, mol, bond]

private theorem rawCIPSortDescLabel_eq_replicate_of_perm
    {xs : List MoleculeGraph.AtomLabel} {n : ℕ} {a : MoleculeGraph.AtomLabel}
    (h : xs.Perm (List.replicate n a)) :
    MoleculeGraph.rawCIPSortDescLabel xs = List.replicate n a := by
  classical
  have hperm : (MoleculeGraph.rawCIPSortDescLabel xs).Perm (List.replicate n a) :=
    (List.mergeSort_perm xs (fun x y => decide (y ≤ x))).trans h
  have hall : ∀ b ∈ MoleculeGraph.rawCIPSortDescLabel xs, b = a := by
    intro b hb
    have hb' : b ∈ List.replicate n a := hperm.subset hb
    exact (List.mem_replicate.1 hb').2
  have hrep := (List.eq_replicate_length (a := a)).2 hall
  have hlen : (MoleculeGraph.rawCIPSortDescLabel xs).length = n := by
    simpa using hperm.length_eq
  rw [hrep, hlen]

private theorem secondLayerLabels_phenyl :
    MoleculeGraph.rawCIPSortDescLabel
      ((mol.cycleCutNextFrontier
        [({ parent := center, current := phenyl0, seen := {center} } :
          MoleculeGraph.CIPState Atom)]).map fun s => mol.rawCIPAtomLabel s.current) =
      [carbonLabel, carbonLabel, carbonLabel] := by
  rw [MoleculeGraph.cycleCutNextFrontier_eq]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [MoleculeGraph.cycleCutChildren_eq_of_current_notMem_seen]
  · have hinput :
        (List.map
          (fun s => mol.rawCIPAtomLabel s.current)
          (List.map
            (fun c => ({ parent := phenyl0, current := c, seen := insert phenyl0 {center} } :
              MoleculeGraph.CIPState Atom))
            (mol.rawCIPChildren center phenyl0))).Perm
          [carbonLabel, carbonLabel, carbonLabel] := by
      simpa [MoleculeGraph.rawCIPAtomLabel, mol, atomZ, carbonLabel] using
        (rawChildren_phenyl0_perm.map fun c => mol.rawCIPAtomLabel c)
    have hinput' :
        (List.map
          (fun s => mol.rawCIPAtomLabel s.current)
          (List.map
            (fun c => ({ parent := phenyl0, current := c, seen := insert phenyl0 {center} } :
              MoleculeGraph.CIPState Atom))
            (mol.rawCIPChildren center phenyl0))).Perm
          (List.replicate 3 carbonLabel) := by
      simpa using hinput
    have hfinal :
        MoleculeGraph.rawCIPSortDescLabel
          ((List.map
            (fun s => mol.rawCIPAtomLabel s.current)
            (List.map
              (fun c => ({ parent := phenyl0, current := c, seen := insert phenyl0 {center} } :
                MoleculeGraph.CIPState Atom))
              (mol.rawCIPChildren center phenyl0)))) =
          [carbonLabel, carbonLabel, carbonLabel] :=
      by simpa using rawCIPSortDescLabel_eq_replicate_of_perm hinput'
    simpa [MoleculeGraph.rawCIPChildren] using hfinal
  · simp

private theorem secondLayerLabels_methyl :
    MoleculeGraph.rawCIPSortDescLabel
      ((mol.cycleCutNextFrontier
        [({ parent := center, current := methyl, seen := {center} } :
          MoleculeGraph.CIPState Atom)]).map fun s => mol.rawCIPAtomLabel s.current) =
      [hydrogenLabel, hydrogenLabel, hydrogenLabel] := by
  rw [MoleculeGraph.cycleCutNextFrontier_eq]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [MoleculeGraph.cycleCutChildren_eq_of_current_notMem_seen]
  · have hinput :
        (List.map
          (fun s => mol.rawCIPAtomLabel s.current)
          (List.map
            (fun c => ({ parent := methyl, current := c, seen := insert methyl {center} } :
              MoleculeGraph.CIPState Atom))
            (mol.rawCIPChildren center methyl))).Perm
          [hydrogenLabel, hydrogenLabel, hydrogenLabel] := by
      simpa [MoleculeGraph.rawCIPAtomLabel, mol, atomZ, hydrogenLabel] using
        (rawChildren_methyl_perm.map fun c => mol.rawCIPAtomLabel c)
    have hinput' :
        (List.map
          (fun s => mol.rawCIPAtomLabel s.current)
          (List.map
            (fun c => ({ parent := methyl, current := c, seen := insert methyl {center} } :
              MoleculeGraph.CIPState Atom))
            (mol.rawCIPChildren center methyl))).Perm
          (List.replicate 3 hydrogenLabel) := by
      simpa using hinput
    have hfinal :
        MoleculeGraph.rawCIPSortDescLabel
          ((List.map
            (fun s => mol.rawCIPAtomLabel s.current)
            (List.map
              (fun c => ({ parent := methyl, current := c, seen := insert methyl {center} } :
                MoleculeGraph.CIPState Atom))
              (mol.rawCIPChildren center methyl)))) =
          [hydrogenLabel, hydrogenLabel, hydrogenLabel] :=
      by simpa using rawCIPSortDescLabel_eq_replicate_of_perm hinput'
    simpa [MoleculeGraph.rawCIPChildren] using hfinal
  · simp

private theorem cipKeyCycleCut_tail_head?_phenyl :
    (oneCenter.cipKeyCycleCut (1 : Fin 4)).tail.head? = some carbonLabel := by
  rw [OneCenterMolecule.cipKeyCycleCut]
  rw [MoleculeGraph.cipKeyFromCycleCut_eq_cycleCutKeyAux]
  have hcard : Fintype.card Atom = 14 := by decide
  rw [hcard]
  norm_num
  rw [MoleculeGraph.cycleCutKeyAux_succ]
  simp [oneCenter, mol, MoleculeGraph.rawCIPSortDescLabel]
  rw [MoleculeGraph.cycleCutKeyAux_succ]
  have hsecond := secondLayerLabels_phenyl
  simp [mol] at hsecond
  rw [hsecond]
  rfl

private theorem cipKeyCycleCut_tail_head?_methyl :
    (oneCenter.cipKeyCycleCut (2 : Fin 4)).tail.head? = some hydrogenLabel := by
  rw [OneCenterMolecule.cipKeyCycleCut]
  rw [MoleculeGraph.cipKeyFromCycleCut_eq_cycleCutKeyAux]
  have hcard : Fintype.card Atom = 14 := by decide
  rw [hcard]
  norm_num
  rw [MoleculeGraph.cycleCutKeyAux_succ]
  simp [oneCenter, mol, MoleculeGraph.rawCIPSortDescLabel]
  rw [MoleculeGraph.cycleCutKeyAux_succ]
  have hsecond := secondLayerLabels_methyl
  simp [mol] at hsecond
  rw [hsecond]
  rfl

private theorem cipKeyCycleCut_eq_cons_tail (i : Fin 4) :
    oneCenter.cipKeyCycleCut i = toLex (ligandZ i, 0) :: (oneCenter.cipKeyCycleCut i).tail := by
  apply List.eq_cons_of_mem_head?
  simp [cipKeyCycleCut_head?]

private theorem cipKeyCycleCut_tail_eq_cons_tail_of_tail_head?
    {i : Fin 4} {a : MoleculeGraph.AtomLabel}
    (h : (oneCenter.cipKeyCycleCut i).tail.head? = some a) :
    (oneCenter.cipKeyCycleCut i).tail = a :: (oneCenter.cipKeyCycleCut i).tail.tail := by
  apply List.eq_cons_of_mem_head?
  exact h

private theorem cipKeyCycleCut_lt_of_ligandZ_lt {i j : Fin 4} (h : ligandZ i < ligandZ j) :
    oneCenter.cipKeyCycleCut i < oneCenter.cipKeyCycleCut j := by
  classical
  have hi := cipKeyCycleCut_eq_cons_tail i
  have hj := cipKeyCycleCut_eq_cons_tail j
  have hlabel : (toLex (ligandZ i, 0) : MoleculeGraph.AtomLabel) < toLex (ligandZ j, 0) :=
    (Prod.Lex.toLex_lt_toLex).2 (Or.inl h)
  have hlex :
      List.Lex (· < ·)
        (toLex (ligandZ i, 0) :: (oneCenter.cipKeyCycleCut i).tail)
        (toLex (ligandZ j, 0) :: (oneCenter.cipKeyCycleCut j).tail) :=
    List.Lex.rel hlabel
  have hlt :
      (toLex (ligandZ i, 0) :: (oneCenter.cipKeyCycleCut i).tail) <
        (toLex (ligandZ j, 0) :: (oneCenter.cipKeyCycleCut j).tail) :=
    (List.lt_iff_lex_lt _ _).2 hlex
  exact lt_of_lt_of_eq (lt_of_eq_of_lt hi hlt) hj.symm

/-- The essential 1-phenylethanol CIP comparison: both ligands start with carbon, but the phenyl
branch sees ring carbons at the next layer while methyl sees hydrogens. -/
theorem cipKeyCycleCut_methyl_lt_phenyl :
    oneCenter.cipKeyCycleCut (2 : Fin 4) < oneCenter.cipKeyCycleCut (1 : Fin 4) := by
  classical
  have hphenHead :
      oneCenter.cipKeyCycleCut (1 : Fin 4) =
        carbonLabel :: (oneCenter.cipKeyCycleCut (1 : Fin 4)).tail := by
    simpa [ligandZ, carbonLabel] using cipKeyCycleCut_eq_cons_tail (1 : Fin 4)
  have hmethylHead :
      oneCenter.cipKeyCycleCut (2 : Fin 4) =
        carbonLabel :: (oneCenter.cipKeyCycleCut (2 : Fin 4)).tail := by
    simpa [ligandZ, carbonLabel] using cipKeyCycleCut_eq_cons_tail (2 : Fin 4)
  have hphenTail :=
    cipKeyCycleCut_tail_eq_cons_tail_of_tail_head? cipKeyCycleCut_tail_head?_phenyl
  have hmethylTail :=
    cipKeyCycleCut_tail_eq_cons_tail_of_tail_head? cipKeyCycleCut_tail_head?_methyl
  have hlabel : hydrogenLabel < carbonLabel := by
    have h : (toLex ((1 : ℕ), 0) : MoleculeGraph.AtomLabel) < toLex (6, 0) :=
      (Prod.Lex.toLex_lt_toLex).2 (Or.inl (by decide : (1 : ℕ) < 6))
    simpa [hydrogenLabel, carbonLabel] using h
  have hlexTail :
      List.Lex (· < ·)
        (hydrogenLabel :: (oneCenter.cipKeyCycleCut (2 : Fin 4)).tail.tail)
        (carbonLabel :: (oneCenter.cipKeyCycleCut (1 : Fin 4)).tail.tail) :=
    List.Lex.rel hlabel
  have hlex :
      List.Lex (· < ·)
        (carbonLabel :: hydrogenLabel :: (oneCenter.cipKeyCycleCut (2 : Fin 4)).tail.tail)
        (carbonLabel :: carbonLabel :: (oneCenter.cipKeyCycleCut (1 : Fin 4)).tail.tail) :=
    List.Lex.cons hlexTail
  have hlt :
      (carbonLabel :: hydrogenLabel :: (oneCenter.cipKeyCycleCut (2 : Fin 4)).tail.tail) <
        (carbonLabel :: carbonLabel :: (oneCenter.cipKeyCycleCut (1 : Fin 4)).tail.tail) :=
    (List.lt_iff_lex_lt _ _).2 hlex
  calc
    oneCenter.cipKeyCycleCut (2 : Fin 4)
        = carbonLabel :: hydrogenLabel :: (oneCenter.cipKeyCycleCut (2 : Fin 4)).tail.tail := by
            rw [hmethylHead, hmethylTail]
            rfl
    _ < carbonLabel :: carbonLabel :: (oneCenter.cipKeyCycleCut (1 : Fin 4)).tail.tail := hlt
    _ = oneCenter.cipKeyCycleCut (1 : Fin 4) := by
            rw [hphenHead, hphenTail]
            rfl

/-- The rule engine explains the essential 1-phenylethanol comparison: methyl loses to phenyl
only after the first carbon-vs-carbon layer ties and the next layer reaches hydrogen-vs-carbon. -/
theorem cipRuleCompareCycleCut_methyl_phenyl_outcome :
    (oneCenter.cipRuleCompareCycleCut (2 : Fin 4) (1 : Fin 4)).outcome = Ordering.lt := by
  classical
  have hphenHead :
      oneCenter.cipKeyCycleCut (1 : Fin 4) =
        carbonLabel :: (oneCenter.cipKeyCycleCut (1 : Fin 4)).tail := by
    simpa [ligandZ, carbonLabel] using cipKeyCycleCut_eq_cons_tail (1 : Fin 4)
  have hmethylHead :
      oneCenter.cipKeyCycleCut (2 : Fin 4) =
        carbonLabel :: (oneCenter.cipKeyCycleCut (2 : Fin 4)).tail := by
    simpa [ligandZ, carbonLabel] using cipKeyCycleCut_eq_cons_tail (2 : Fin 4)
  have hphenTail :=
    cipKeyCycleCut_tail_eq_cons_tail_of_tail_head? cipKeyCycleCut_tail_head?_phenyl
  have hmethylTail :=
    cipKeyCycleCut_tail_eq_cons_tail_of_tail_head? cipKeyCycleCut_tail_head?_methyl
  change
    (CIPRuleEngine.compareKeyCertificate
      (oneCenter.cipKeyCycleCut (2 : Fin 4))
      (oneCenter.cipKeyCycleCut (1 : Fin 4))).outcome = Ordering.lt
  rw [hmethylHead, hphenHead, hmethylTail, hphenTail]
  norm_num [CIPRuleEngine.compareKeyCertificate, CIPRuleEngine.compareKeyTrace,
    CIPRuleEngine.compareAtomLabelTrace, CIPRuleEngine.priorityNatDecision,
    CIPRuleEngine.comparePriorityNat, carbonLabel, hydrogenLabel]

theorem cipDescriptorEngine_methyl_phenyl_outcome :
    (oneCenter.cipDescriptorEngine.compare (2 : Fin 4) (1 : Fin 4)).outcome = Ordering.lt := by
  simpa using cipRuleCompareCycleCut_methyl_phenyl_outcome

/-- The canonical official engine exposes the hierarchical-digraph comparison for the same
phenyl-vs-methyl decision point. -/
theorem cipOfficialEngine_methyl_phenyl_compare_eq_default :
    (oneCenter.cipOfficialEngine officialEmptyContext).compare (2 : Fin 4) (1 : Fin 4) =
      oneCenter.cipOfficialCompare officialEmptyContext (2 : Fin 4) (1 : Fin 4) := by
  rfl

/-- In the concrete 1-phenylethanol model, the official engine's default comparison is
fuel-independent by the general finite-exhaustion theorem.  The bounded comparison now returns an
`Option`; its outcome projection is exactly the stored default certificate's outcome. -/
theorem cipOfficialEngine_methyl_phenyl_outcome_stable (extra : ℕ) :
    (oneCenter.cipOfficialCompareWithFuel officialEmptyContext
      ((Fintype.card Atom + 1) + extra) (2 : Fin 4) (1 : Fin 4)).map
        CIPTraceCertificate.outcome =
      some ((oneCenter.cipOfficialEngine officialEmptyContext).compare
        (2 : Fin 4) (1 : Fin 4)).outcome := by
  exact (oneCenter.cipOfficialEngine officialEmptyContext).stableOutcome
    (2 : Fin 4) (1 : Fin 4) extra

private def keyWithTieCycleCut (i : Fin 4) : (List MoleculeGraph.AtomLabel) ×ₗ (Fin 4) :=
  toLex (oneCenter.cipKeyCycleCut i, i)

private def descRelCycleCut (i j : Fin 4) : Prop :=
  keyWithTieCycleCut j ≤ keyWithTieCycleCut i

private theorem keyWithTieCycleCut_injective : Function.Injective keyWithTieCycleCut := by
  intro i j hij
  have : (oneCenter.cipKeyCycleCut i, i) = (oneCenter.cipKeyCycleCut j, j) := toLex.injective hij
  exact congrArg Prod.snd this

private instance : Std.Antisymm descRelCycleCut :=
  ⟨by
    intro a b hab hba
    apply keyWithTieCycleCut_injective
    dsimp [descRelCycleCut] at hab hba
    exact le_antisymm hba hab⟩

private instance : DecidableRel descRelCycleCut := by
  intro i j
  dsimp [descRelCycleCut, keyWithTieCycleCut]
  infer_instance

private instance : IsTrans (Fin 4) descRelCycleCut :=
  ⟨by
    intro a b c hab hbc
    dsimp [descRelCycleCut] at hab hbc ⊢
    exact le_trans hbc hab⟩

private instance : Std.Total descRelCycleCut :=
  ⟨by
    intro a b
    dsimp [descRelCycleCut]
    simpa [or_comm] using (le_total (keyWithTieCycleCut b) (keyWithTieCycleCut a))⟩

private theorem descRelCycleCut_of_cipKey_lt {i j : Fin 4}
    (h : oneCenter.cipKeyCycleCut j < oneCenter.cipKeyCycleCut i) :
    descRelCycleCut i j := by
  dsimp [descRelCycleCut, keyWithTieCycleCut]
  have hlt :
      (toLex (oneCenter.cipKeyCycleCut j, j) : (List MoleculeGraph.AtomLabel) ×ₗ (Fin 4)) <
        toLex (oneCenter.cipKeyCycleCut i, i) :=
    (Prod.Lex.toLex_lt_toLex).2 (Or.inl h)
  exact le_of_lt hlt

private theorem pairwise_expected_cipOrderCycleCut :
    ([0, 1, 2, 3] : List (Fin 4)).Pairwise descRelCycleCut := by
  refine (List.pairwise_cons).2 ?_
  constructor
  · intro a ha
    simp at ha
    rcases ha with rfl | rfl | rfl
    · exact descRelCycleCut_of_cipKey_lt
        (cipKeyCycleCut_lt_of_ligandZ_lt (i := (1 : Fin 4)) (j := 0) (by decide))
    · exact descRelCycleCut_of_cipKey_lt
        (cipKeyCycleCut_lt_of_ligandZ_lt (i := (2 : Fin 4)) (j := 0) (by decide))
    · exact descRelCycleCut_of_cipKey_lt
        (cipKeyCycleCut_lt_of_ligandZ_lt (i := (3 : Fin 4)) (j := 0) (by decide))
  · refine (List.pairwise_cons).2 ?_
    constructor
    · intro a ha
      simp at ha
      rcases ha with rfl | rfl
      · exact descRelCycleCut_of_cipKey_lt cipKeyCycleCut_methyl_lt_phenyl
      · exact descRelCycleCut_of_cipKey_lt
          (cipKeyCycleCut_lt_of_ligandZ_lt (i := (3 : Fin 4)) (j := 1) (by decide))
    · refine (List.pairwise_cons).2 ?_
      constructor
      · intro a ha
        simp at ha
        rcases ha with rfl
        exact descRelCycleCut_of_cipKey_lt
          (cipKeyCycleCut_lt_of_ligandZ_lt (i := (3 : Fin 4)) (j := 2) (by decide))
      · simp

private theorem perm_expected_cipOrderCycleCut :
    ([0, 1, 2, 3] : List (Fin 4)).Perm (List.finRange 4) := by
  decide

/-- The descriptor/CIP-cycle-cut key ranks the stereocenter ligands as
`OH > phenyl > methyl > H`. -/
theorem cipOrderCycleCut_eq_expected : oneCenter.cipOrderCycleCut = [0, 1, 2, 3] := by
  classical
  have hpairOrder : oneCenter.cipOrderCycleCut.Pairwise descRelCycleCut := by
    simpa [OneCenterMolecule.cipOrderCycleCut, descRelCycleCut] using
      (List.pairwise_mergeSort' (r := descRelCycleCut) (l := List.finRange 4))
  have hperm : oneCenter.cipOrderCycleCut.Perm ([0, 1, 2, 3] : List (Fin 4)) :=
    (oneCenter.cipOrderCycleCut_perm_finRange).trans perm_expected_cipOrderCycleCut.symm
  exact (List.Perm.eq_of_pairwise' hpairOrder pairwise_expected_cipOrderCycleCut hperm)

theorem cipOrderDescriptor_eq_expected : oneCenter.cipOrderDescriptor = [0, 1, 2, 3] :=
  cipOrderCycleCut_eq_expected

/-- With the ligand convention already in descending descriptor order, the CIP permutation is the
identity permutation. -/
theorem cipPermutationCycleCut_eq_one : oneCenter.cipPermutationCycleCut = 1 := by
  classical
  ext i
  fin_cases i <;>
    simp [OneCenterMolecule.cipPermutationCycleCut, cipOrderCycleCut_eq_expected]

theorem cipPermutationDescriptor_eq_one : oneCenter.cipPermutationDescriptor = 1 :=
  cipPermutationCycleCut_eq_one

theorem permHandedness_cipPermutationCycleCut :
    permHandedness oneCenter.cipPermutationCycleCut = 1 := by
  simp [cipPermutationCycleCut_eq_one]

theorem permHandedness_cipPermutationDescriptor :
    permHandedness oneCenter.cipPermutationDescriptor = 1 := by
  simp [cipPermutationDescriptor_eq_one]

theorem stereogenicByCIPCycleCut : oneCenter.StereogenicByCIPCycleCut := by
  intro i j hkey
  fin_cases i <;> fin_cases j
  · rfl
  · exact False.elim ((ne_of_gt
      (cipKeyCycleCut_lt_of_ligandZ_lt (i := (1 : Fin 4)) (j := 0) (by decide))) hkey)
  · exact False.elim ((ne_of_gt
      (cipKeyCycleCut_lt_of_ligandZ_lt (i := (2 : Fin 4)) (j := 0) (by decide))) hkey)
  · exact False.elim ((ne_of_gt
      (cipKeyCycleCut_lt_of_ligandZ_lt (i := (3 : Fin 4)) (j := 0) (by decide))) hkey)
  · exact False.elim ((ne_of_lt
      (cipKeyCycleCut_lt_of_ligandZ_lt (i := (1 : Fin 4)) (j := 0) (by decide))) hkey)
  · rfl
  · exact False.elim ((ne_of_gt cipKeyCycleCut_methyl_lt_phenyl) hkey)
  · exact False.elim ((ne_of_gt
      (cipKeyCycleCut_lt_of_ligandZ_lt (i := (3 : Fin 4)) (j := 1) (by decide))) hkey)
  · exact False.elim ((ne_of_lt
      (cipKeyCycleCut_lt_of_ligandZ_lt (i := (2 : Fin 4)) (j := 0) (by decide))) hkey)
  · exact False.elim ((ne_of_lt cipKeyCycleCut_methyl_lt_phenyl) hkey)
  · rfl
  · exact False.elim ((ne_of_gt
      (cipKeyCycleCut_lt_of_ligandZ_lt (i := (3 : Fin 4)) (j := 2) (by decide))) hkey)
  · exact False.elim ((ne_of_lt
      (cipKeyCycleCut_lt_of_ligandZ_lt (i := (3 : Fin 4)) (j := 0) (by decide))) hkey)
  · exact False.elim ((ne_of_lt
      (cipKeyCycleCut_lt_of_ligandZ_lt (i := (3 : Fin 4)) (j := 1) (by decide))) hkey)
  · exact False.elim ((ne_of_lt
      (cipKeyCycleCut_lt_of_ligandZ_lt (i := (3 : Fin 4)) (j := 2) (by decide))) hkey)
  · rfl

theorem stereogenicByCIPDescriptor : oneCenter.StereogenicByCIPDescriptor :=
  stereogenicByCIPCycleCut

theorem cipPermutationDescriptor?_eq_some :
    oneCenter.cipPermutationDescriptor? = some oneCenter.cipPermutationDescriptor := by
  exact oneCenter.cipPermutationDescriptor?_eq_some_of_resolvedCIPDescriptor
    stereogenicByCIPDescriptor

theorem chiralBySymmetry_of_descriptorCIP : oneCenter.ChiralBySymmetry :=
  oneCenter.chiralBySymmetry_of_stereogenicByCIPCycleCut stereogenicByCIPCycleCut

theorem stereoQ_exactly_two_classes :
    ∃ a b : oneCenter.StereoQ, a ≠ b ∧ ∀ q : oneCenter.StereoQ, q = a ∨ q = b :=
  oneCenter.stereoQ_exactly_two_classes_of_chiralBySymmetry chiralBySymmetry_of_descriptorCIP

/-- In the canonical right-handed local geometry, the descriptor-facing CIP assignment is `S`
under the corrected calibration (identity CIP permutation, handedness `+1`). -/
theorem rsCIP_right_eq_S : oneCenter.rsCIP rightRealization = RS.S := by
  have hhand :
      handedness (reindex rightRealization.1 oneCenter.cipPermutationCycleCut) = 1 := by
    simpa [rightRealization_handedness] using
      (TetrahedralGeometry.handedness_reindex_even
        rightRealization.1 oneCenter.cipPermutationCycleCut permHandedness_cipPermutationCycleCut)
  simp [OneCenterMolecule.rsCIP, OneCenterMolecule.rsCycleCut, hhand]

/-- Historical API key retained for downstream imports.  Its statement follows the corrected
calibration (right realization `S`); the accurate name is `rsCIP_right_eq_S`. -/
theorem rsCIP_right_eq_R : oneCenter.rsCIP rightRealization = RS.S :=
  rsCIP_right_eq_S

theorem rsCIP?_right_eq_some_S : oneCenter.rsCIP? rightRealization = some RS.S := by
  simpa [rsCIP_right_eq_S] using
    oneCenter.rsCIP?_eq_some_rsCIP_of_resolvedCIPDescriptor stereogenicByCIPDescriptor
      rightRealization

/-- Historical API key retained for downstream imports; the corrected value is `S`. -/
theorem rsCIP?_right_eq_some_R : oneCenter.rsCIP? rightRealization = some RS.S :=
  rsCIP?_right_eq_some_S

/-- In the mirror canonical local geometry, the descriptor-facing CIP assignment is `R`. -/
theorem rsCIP_left_eq_R : oneCenter.rsCIP leftRealization = RS.R := by
  have hhand :
      handedness (reindex leftRealization.1 oneCenter.cipPermutationCycleCut) = -1 := by
    simpa [leftRealization_handedness] using
      (TetrahedralGeometry.handedness_reindex_even
        leftRealization.1 oneCenter.cipPermutationCycleCut permHandedness_cipPermutationCycleCut)
  simp [OneCenterMolecule.rsCIP, OneCenterMolecule.rsCycleCut, hhand]

/-- Historical API key retained for downstream imports.  Its statement follows the corrected
calibration (left realization `R`); the accurate name is `rsCIP_left_eq_R`. -/
theorem rsCIP_left_eq_S : oneCenter.rsCIP leftRealization = RS.R :=
  rsCIP_left_eq_R

theorem rsCIP?_left_eq_some_R : oneCenter.rsCIP? leftRealization = some RS.R := by
  simpa [rsCIP_left_eq_R] using
    oneCenter.rsCIP?_eq_some_rsCIP_of_resolvedCIPDescriptor stereogenicByCIPDescriptor
      leftRealization

/-- Historical API key retained for downstream imports; the corrected value is `R`. -/
theorem rsCIP?_left_eq_some_S : oneCenter.rsCIP? leftRealization = some RS.R :=
  rsCIP?_left_eq_some_R

theorem rsCIP_left_eq_swap_rsCIP_right :
    oneCenter.rsCIP leftRealization = RS.swap (oneCenter.rsCIP rightRealization) := by
  simp [rsCIP_left_eq_R, rsCIP_right_eq_S, RS.swap]

theorem rsCIP_right_ne_rsCIP_left :
    oneCenter.rsCIP rightRealization ≠ oneCenter.rsCIP leftRealization := by
  simp [rsCIP_right_eq_S, rsCIP_left_eq_R]

/-- A branch that walks around the phenyl ring and returns to `phenyl0` is detected as a duplicate. -/
def phenylCycleReturn : CIPExpansionNode Atom :=
  ((((((CIPExpansionNode.root phenyl0).extend phenyl1).extend phenyl2).extend phenyl3).extend
      phenyl4).extend phenyl5).extend phenyl0

example : phenylCycleReturn.IsDuplicate := by
  simp [phenylCycleReturn, CIPExpansionNode.IsDuplicate, CIPExpansionNode.previous,
    CIPExpansionNode.extend, CIPExpansionNode.root]

/-- The new frontier machinery can expand the cyclic ligand while proving every branch is a
molecular walk through actual bonds. -/
example :
    mol.FrontierBranchBonded
      (mol.cipCycleCutMultiplicityFrontier 7 [CIPExpansionNode.root phenyl0]) := by
  apply mol.frontierBranchBonded_cipCycleCutMultiplicityFrontier
  intro n hn
  rcases List.mem_singleton.1 hn with rfl
  simp

end

end OnePhenylethanol

end Examples
end TetraStereo
