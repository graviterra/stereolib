/-
  ActualParsedBranchSymmetryFidelity

  Physical branch symmetry of the *actual parsed* 17-atom molecule

      C[C@@H](Cl)[C@@H]([C@@H](Cl)C)Br        (variant A, `ActualEligibleParentParityVariant.molA`)

  versus the actual runtime pseudo-asymmetry classification of the middle center (parser atom 3)
  already computed in `ActualEligibleParentParityVariant`.  The graph is
  `RawMolecule.toMoleculeGraph molA`; the three distinguished centers are the three real
  tetrahedral parser atoms 1, 3 and 4, and the ligand enumerations are the actual written-neighbour
  rows `[0,11,2,3]`, `[1,12,4,7]`, `[3,13,5,6]`.

  The independent source-symmetry relation is the accepted
  `RootedTetrahedralBranchSymmetry` relation on this molecule.  The local frame at each center is
  read off the actual parsed tetrahedral marker by a fixed even/odd gauge convention
  (`TetrahedralInputParity.clockwise` ↦ the odd frame `Equiv.swap 0 1`,
  `TetrahedralInputParity.anticlockwise` ↦ the identity).  The absolute handedness gauge is
  irrelevant to the branch relation, and the convention is *not* chosen from a desired R/S
  answer: it is a fixed parity-to-frame map applied to the parser's stored marker.

  The two carbon arms at the middle center are ligand slots 0 (parser atom 1) and 2 (parser atom 4).
  A concrete graph automorphism `armSwap` exchanges them (together with their Cl, H and methyl
  substituents) while fixing the middle atom, its H and the Br.  The induced local ligand
  permutation at the parent arm (parser atom 1) is the *odd* transposition `0 ↔ 3`; this is
  computed from the actual written-neighbour frames, not inferred from equality of marker letters.
  Consequently the two arms are mirror-related and not properly related, and the middle center is
  an actual pseudoasymmetric unit with exactly one enantiomorphic ligand pair, in agreement with
  the runtime output `(RS.R, uppercase = false)`.

  The original fixture `ConstitutionalRootStageAvailability.mol` differs only in atom 4's marker
  (and hence in the arm frame).  On the same actual graph its arm exchange is *proper* rather than
  mirror, so it is not pseudoasymmetric there; the runtime middle-center evaluation is indeed
  `none`.  This is the negative control.

  Scope.  This module compares parsed-frame graph symmetry with the actual pseudo classification.
  It does not claim a Cartesian realization, a claim about all molecular families, or absolute
  R/S/r/s letter faithfulness.  No production declaration is modified.
-/

import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.OneCenter.ActualEligibleParentParityVariant
import TetraStereo.OneCenter.P92StereogenicUnitSemantics
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace ActualParsedBranchSymmetryFidelity

noncomputable section

open RootedTetrahedralBranchSymmetry
open ConstitutionalRootStageAvailability
open ActualEligibleParentParityVariant

/-! ## 1. The actual parsed atom type and atom constants -/

/-- The actual 17-atom materialized graph's vertex type. -/
abbrev AtomA : Type := Fin molA.atomCount

/-- The actual materialized atom count. -/
theorem actual_atomCount : molA.atomCount = 17 := by decide

def atom0 : AtomA := ⟨0, by rw [actual_atomCount]; decide⟩
def atom1 : AtomA := ⟨1, by rw [actual_atomCount]; decide⟩
def atom2 : AtomA := ⟨2, by rw [actual_atomCount]; decide⟩
def atom3 : AtomA := ⟨3, by rw [actual_atomCount]; decide⟩
def atom4 : AtomA := ⟨4, by rw [actual_atomCount]; decide⟩
def atom5 : AtomA := ⟨5, by rw [actual_atomCount]; decide⟩
def atom6 : AtomA := ⟨6, by rw [actual_atomCount]; decide⟩
def atom7 : AtomA := ⟨7, by rw [actual_atomCount]; decide⟩
def atom8 : AtomA := ⟨8, by rw [actual_atomCount]; decide⟩
def atom9 : AtomA := ⟨9, by rw [actual_atomCount]; decide⟩
def atom10 : AtomA := ⟨10, by rw [actual_atomCount]; decide⟩
def atom11 : AtomA := ⟨11, by rw [actual_atomCount]; decide⟩
def atom12 : AtomA := ⟨12, by rw [actual_atomCount]; decide⟩
def atom13 : AtomA := ⟨13, by rw [actual_atomCount]; decide⟩
def atom14 : AtomA := ⟨14, by rw [actual_atomCount]; decide⟩
def atom15 : AtomA := ⟨15, by rw [actual_atomCount]; decide⟩
def atom16 : AtomA := ⟨16, by rw [actual_atomCount]; decide⟩

/-! ## 2. The actual multi-center molecule on the parsed graph

The distinguished centers are exactly the three real parsed tetrahedral atoms 1, 3, 4.  The
ligand enumerations are the actual materialized written-neighbour rows. -/

/-- The actual written-neighbour enumeration at the three real tetrahedral centers. -/
def ligandAt (c : AtomA) (i : Fin 4) : AtomA :=
  if c.1 = 1 then
    (if i = 0 then atom0 else if i = 1 then atom11 else if i = 2 then atom2 else atom3)
  else if c.1 = 3 then
    (if i = 0 then atom1 else if i = 1 then atom12 else if i = 2 then atom4 else atom7)
  else if c.1 = 4 then
    (if i = 0 then atom3 else if i = 1 then atom13 else if i = 2 then atom5 else atom6)
  else atom0

/-- The actual parsed multi-center molecule: graph `molA.toMoleculeGraph`, centers `{1,3,4}`, and
the written-neighbour ligand enumerations. -/
def actualMolecule : MultiCenterMolecule AtomA where
  mol := molA.toMoleculeGraph
  centers := {atom1, atom3, atom4}
  ligandAtom := fun c _ i => ligandAt c i
  ligandAtom_adj := by decide
  ligandAtom_injective := by decide
  ligandAtom_surjective := by decide

/-- The parser atom 1 (the parent carbon arm), as a distinguished center. -/
def centerC2 : actualMolecule.Center := ⟨atom1, by decide⟩

/-- The parser atom 3 (the middle center under evaluation), as a distinguished center. -/
def actualMiddle : actualMolecule.Center := ⟨atom3, by decide⟩

/-- The parser atom 4 (the outward carbon arm), as a distinguished center. -/
def centerC3 : actualMolecule.Center := ⟨atom4, by decide⟩

/-! ### The actual written-neighbour rows -/

theorem actual_ligand_enumerations :
    List.ofFn (fun i : Fin 4 => (actualMolecule.ligandAtomAt centerC2 i).1) = [0, 11, 2, 3] ∧
      List.ofFn (fun i : Fin 4 => (actualMolecule.ligandAtomAt actualMiddle i).1) = [1, 12, 4, 7] ∧
      List.ofFn (fun i : Fin 4 => (actualMolecule.ligandAtomAt centerC3 i).1) = [3, 13, 5, 6] := by
  decide

@[simp] theorem ligandAtomAt_centerC2_zero :
    actualMolecule.ligandAtomAt centerC2 0 = atom0 := by decide
@[simp] theorem ligandAtomAt_centerC2_one :
    actualMolecule.ligandAtomAt centerC2 1 = atom11 := by decide
@[simp] theorem ligandAtomAt_centerC2_two :
    actualMolecule.ligandAtomAt centerC2 2 = atom2 := by decide
@[simp] theorem ligandAtomAt_centerC2_three :
    actualMolecule.ligandAtomAt centerC2 3 = atom3 := by decide
@[simp] theorem ligandAtomAt_middle_zero :
    actualMolecule.ligandAtomAt actualMiddle 0 = atom1 := by decide
@[simp] theorem ligandAtomAt_middle_one :
    actualMolecule.ligandAtomAt actualMiddle 1 = atom12 := by decide
@[simp] theorem ligandAtomAt_middle_two :
    actualMolecule.ligandAtomAt actualMiddle 2 = atom4 := by decide
@[simp] theorem ligandAtomAt_middle_three :
    actualMolecule.ligandAtomAt actualMiddle 3 = atom7 := by decide
@[simp] theorem ligandAtomAt_centerC3_zero :
    actualMolecule.ligandAtomAt centerC3 0 = atom3 := by decide
@[simp] theorem ligandAtomAt_centerC3_one :
    actualMolecule.ligandAtomAt centerC3 1 = atom13 := by decide
@[simp] theorem ligandAtomAt_centerC3_two :
    actualMolecule.ligandAtomAt centerC3 2 = atom5 := by decide
@[simp] theorem ligandAtomAt_centerC3_three :
    actualMolecule.ligandAtomAt centerC3 3 = atom6 := by decide

/-! ## 3. Configuration from the actual parsed parity markers

Fixed even/odd gauge: `clockwise` is the odd frame `Equiv.swap 0 1`, and `anticlockwise` (or the
absence of a marker) is the identity frame.  The global sign of this convention is a gauge choice
and is never used to select a desired R/S answer; only its parity content enters the branch
relation. -/

/-- The fixed parity-to-frame convention (clockwise ↦ odd transposition, anticlockwise ↦ identity). -/
def frameOfParity : Option TetrahedralInputParity → Equiv.Perm (Fin 4)
  | some TetrahedralInputParity.clockwise => MultiCenterMolecule.mirrorFrame
  | _ => 1

@[simp] theorem frameOfParity_clockwise :
    frameOfParity (some TetrahedralInputParity.clockwise) = MultiCenterMolecule.mirrorFrame := rfl

@[simp] theorem frameOfParity_anticlockwise :
    frameOfParity (some TetrahedralInputParity.anticlockwise) = 1 := rfl

@[simp] theorem frameOfParity_none : frameOfParity none = 1 := rfl

/-- The actual parsed tetrahedral marker at a materialized atom. -/
def parsedParityA (a : AtomA) : Option TetrahedralInputParity :=
  (molA.atomAt? a.1).bind (fun spec => spec.tetrahedral?)

/-- The actual configuration of variant A, read from the parsed markers. -/
def actualCfg (c : actualMolecule.Center) : Equiv.Perm (Fin 4) :=
  frameOfParity (parsedParityA c.1)

/-- The materialized parsed marker at atom 1 is still clockwise (materialization preserves it). -/
theorem parsedParityA_one :
    parsedParityA atom1 = some TetrahedralInputParity.clockwise := by decide

/-- The materialized parsed marker at atom 3 is still clockwise. -/
theorem parsedParityA_three :
    parsedParityA atom3 = some TetrahedralInputParity.clockwise := by decide

/-- The materialized parsed marker at atom 4 is still clockwise (variant A). -/
theorem parsedParityA_four :
    parsedParityA atom4 = some TetrahedralInputParity.clockwise := by decide

/-- The parsed marker at center C2 is clockwise, so its local frame is odd. -/
theorem actualCfg_centerC2 : actualCfg centerC2 = MultiCenterMolecule.mirrorFrame := by
  simp [actualCfg, centerC2, parsedParityA_one]

/-- The parsed marker at the middle center is clockwise, so its local frame is odd. -/
theorem actualCfg_middle : actualCfg actualMiddle = MultiCenterMolecule.mirrorFrame := by
  simp [actualCfg, actualMiddle, parsedParityA_three]

/-- The parsed marker at center C3 is clockwise, so its local frame is odd. -/
theorem actualCfg_centerC3 : actualCfg centerC3 = MultiCenterMolecule.mirrorFrame := by
  simp [actualCfg, centerC3, parsedParityA_four]

/-- Frame/parity correspondence at C2: the computed local sign is the odd sign. -/
theorem actualCfg_sign_centerC2 :
    actualMolecule.configurationSign actualCfg centerC2 = -1 := by
  rw [MultiCenterMolecule.configurationSign, actualCfg_centerC2]
  simp [MultiCenterMolecule.mirrorFrame]

/-- Frame/parity correspondence at the middle center: the computed local sign is the odd sign. -/
theorem actualCfg_sign_middle :
    actualMolecule.configurationSign actualCfg actualMiddle = -1 := by
  rw [MultiCenterMolecule.configurationSign, actualCfg_middle]
  simp [MultiCenterMolecule.mirrorFrame]

/-- Frame/parity correspondence at C3: the computed local sign is the odd sign. -/
theorem actualCfg_sign_centerC3 :
    actualMolecule.configurationSign actualCfg centerC3 = -1 := by
  rw [MultiCenterMolecule.configurationSign, actualCfg_centerC3]
  simp [MultiCenterMolecule.mirrorFrame]

/-- In variant A the two carbon arms carry the *same* parsed local marker. -/
theorem actual_arms_same_parsed_marker :
    parsedParityA atom1 = parsedParityA atom4 ∧
      actualCfg centerC2 = actualCfg centerC3 := by
  simp [parsedParityA_one, parsedParityA_four, actualCfg_centerC2, actualCfg_centerC3]

/-! ## 4. The concrete arm-exchange graph automorphism -/

/-- The explicit arm exchange, as a product of the disjoint transpositions
`(0 6)(1 4)(2 5)(8 14)(9 15)(10 16)(11 13)`; it fixes the middle atom 3, its hydrogen 12 and the
bromine 7. -/
def armSwap : Equiv.Perm AtomA :=
  Equiv.swap atom0 atom6 * Equiv.swap atom1 atom4 * Equiv.swap atom2 atom5 *
    Equiv.swap atom8 atom14 * Equiv.swap atom9 atom15 * Equiv.swap atom10 atom16 *
      Equiv.swap atom11 atom13

@[simp] theorem armSwap_apply_atom0 : (armSwap : Equiv.Perm AtomA) atom0 = atom6 := by decide
@[simp] theorem armSwap_apply_atom1 : (armSwap : Equiv.Perm AtomA) atom1 = atom4 := by decide
@[simp] theorem armSwap_apply_atom2 : (armSwap : Equiv.Perm AtomA) atom2 = atom5 := by decide
@[simp] theorem armSwap_apply_atom3 : (armSwap : Equiv.Perm AtomA) atom3 = atom3 := by decide
@[simp] theorem armSwap_apply_atom4 : (armSwap : Equiv.Perm AtomA) atom4 = atom1 := by decide
@[simp] theorem armSwap_apply_atom5 : (armSwap : Equiv.Perm AtomA) atom5 = atom2 := by decide
@[simp] theorem armSwap_apply_atom6 : (armSwap : Equiv.Perm AtomA) atom6 = atom0 := by decide
@[simp] theorem armSwap_apply_atom7 : (armSwap : Equiv.Perm AtomA) atom7 = atom7 := by decide
@[simp] theorem armSwap_apply_atom8 : (armSwap : Equiv.Perm AtomA) atom8 = atom14 := by decide
@[simp] theorem armSwap_apply_atom9 : (armSwap : Equiv.Perm AtomA) atom9 = atom15 := by decide
@[simp] theorem armSwap_apply_atom10 : (armSwap : Equiv.Perm AtomA) atom10 = atom16 := by decide
@[simp] theorem armSwap_apply_atom11 : (armSwap : Equiv.Perm AtomA) atom11 = atom13 := by decide
@[simp] theorem armSwap_apply_atom12 : (armSwap : Equiv.Perm AtomA) atom12 = atom12 := by decide
@[simp] theorem armSwap_apply_atom13 : (armSwap : Equiv.Perm AtomA) atom13 = atom11 := by decide
@[simp] theorem armSwap_apply_atom14 : (armSwap : Equiv.Perm AtomA) atom14 = atom8 := by decide
@[simp] theorem armSwap_apply_atom15 : (armSwap : Equiv.Perm AtomA) atom15 = atom9 := by decide
@[simp] theorem armSwap_apply_atom16 : (armSwap : Equiv.Perm AtomA) atom16 = atom10 := by decide

/-- The arm exchange is nontrivial (it moves the parent arm onto the outward arm). -/
theorem armSwap_nontrivial : (armSwap : Equiv.Perm AtomA) atom1 ≠ atom1 := by decide

/-- The arm exchange preserves the actual parsed atom specification at every atom.  This is the
source-graph atom-label preservation used below, including atom mass. -/
theorem armSwap_atomAt?_eq (v : AtomA) :
    molA.atomAt? v.1 = molA.atomAt? (armSwap v).1 := by
  revert v
  decide

/-- Atom masses depend only on the parsed atom specification. -/
theorem atomMassAt_eq_of_atomAt?_eq {i j : ℕ}
    (h : molA.atomAt? i = molA.atomAt? j) :
    molA.atomMassAt i = molA.atomMassAt j := by
  simp [RawMolecule.atomMassAt, RawMolecule.atomMassAt?, h]

/-- The arm exchange preserves the actual source atom mass at every atom. -/
theorem armSwap_atomMass_eq (v : AtomA) :
    molA.toMoleculeGraph.atomMass (armSwap v) = molA.toMoleculeGraph.atomMass v := by
  simpa [RawMolecule.toMoleculeGraph] using
    (atomMassAt_eq_of_atomAt?_eq (i := v.1) (j := (armSwap v).1)
      (armSwap_atomAt?_eq v)).symm

/-- The actual arm exchange is an automorphism of the parsed molecular graph. -/
theorem armSwap_isAutomorphism :
    molA.toMoleculeGraph.IsAutomorphism armSwap := by
  refine ⟨by decide, ?_, by decide, by decide⟩
  intro v
  exact armSwap_atomMass_eq v

/-- The arm exchange preserves the actual distinguished-center set `{1,3,4}`. -/
theorem armSwap_preservesCenters :
    actualMolecule.PreservesCenters (armSwap : Equiv.Perm AtomA) := by
  unfold MultiCenterMolecule.PreservesCenters
  decide

/-- The actual arm-exchange automorphism of the parsed multi-center molecule. -/
def armSwapAut : actualMolecule.Aut :=
  ⟨armSwap, armSwap_isAutomorphism, armSwap_preservesCenters⟩

/-! ## 5. Exact ligand-branch reachability on the parsed graph

The generic root-avoiding walk helper is a local copy with a fresh namespace; the shared public
relations of `RootedTetrahedralBranchSymmetry` are imported and never redeclared. -/

namespace ActualParsedBranchWalk

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A walk in a molecular graph that avoids a fixed root atom at every vertex. -/
inductive BranchWalk (m : MoleculeGraph V) (root : V) : V → V → Prop where
  | refl {v : V} (hv : v ≠ root) : BranchWalk m root v v
  | step {u v w : V} (hu : u ≠ root) (huv : m.Adj u v)
      (tail : BranchWalk m root v w) : BranchWalk m root u w

namespace BranchWalk

theorem start_ne_root {m : MoleculeGraph V} {root v w : V}
    (hw : BranchWalk m root v w) : v ≠ root := by
  cases hw with
  | refl hv => exact hv
  | step hu _ _ => exact hu

theorem endpoint_ne_root {m : MoleculeGraph V} {root v w : V}
    (hw : BranchWalk m root v w) : w ≠ root := by
  induction hw with
  | refl hv => exact hv
  | step _ _ _ ih => exact ih

/-- Reachability principle: a vertex set containing the start, excluding the root and closed
under non-root edges contains every endpoint. -/
theorem endpoint_mem_of_closed {m : MoleculeGraph V} {root v w : V}
    (hw : BranchWalk m root v w) {S : Finset V}
    (hclosed : ∀ u ∈ S, ∀ x : V, m.Adj u x → x ≠ root → x ∈ S) :
    v ∈ S → w ∈ S := by
  induction hw with
  | refl _ => exact id
  | step hu huv htail ih =>
      intro hvS
      exact ih (hclosed _ hvS _ huv (start_ne_root htail))

end BranchWalk

/-- Convert the local root-avoiding walk helper to a simple-graph walk whose support avoids the
root. -/
theorem branchWalk_to_walk {m : MoleculeGraph V} {root u v : V}
    (hw : BranchWalk m root u v) :
    ∃ p : m.underlyingSimpleGraph.Walk u v, root ∉ p.support := by
  induction hw with
  | refl hv =>
      exact ⟨SimpleGraph.Walk.nil, by simpa using hv.symm⟩
  | step hu hadj _ ih =>
      rcases ih with ⟨p, hp⟩
      refine ⟨SimpleGraph.Walk.cons (by simpa using hadj) p, ?_⟩
      simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or]
      exact ⟨fun h => hu h.symm, hp⟩

/-- Convert a simple-graph walk avoiding the root into the local root-avoiding walk helper. -/
theorem walk_to_branchWalk {m : MoleculeGraph V} {root u v : V}
    (p : m.underlyingSimpleGraph.Walk u v) :
    root ∉ p.support → BranchWalk m root u v := by
  induction p with
  | nil =>
      intro hp
      exact BranchWalk.refl (by
        intro h
        exact hp (by simp [h]))
  | cons hadj tail ih =>
      intro hp
      rw [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at hp
      exact BranchWalk.step (fun h => hp.1 h.symm) (by simpa using hadj) (ih hp.2)

/-- The local helper proves exactly the shared branch-reachability relation. -/
theorem branchWalk_to_ligandBranchReaches {m : MultiCenterMolecule V} {c : m.Center}
    {i : Fin 4} {v : V}
    (hw : BranchWalk m.mol c.1 (m.ligandAtomAt c i) v) :
    LigandBranchReaches m c i v :=
  branchWalk_to_walk hw

/-- The attachment root is never reached inside its own ligand branch. -/
theorem ligandBranchReaches_not_root (m : MultiCenterMolecule V) (c : m.Center)
    (i : Fin 4) : ¬ LigandBranchReaches m c i c.1 := by
  rintro ⟨p, hp⟩
  exact hp p.end_mem_support

end ActualParsedBranchWalk

/-! ### The exact atoms of the two carbon-arm branches -/

/-- The atoms reachable from middle slot 0 (parser atom 1) without passing through atom 3. -/
def branchZeroAtoms : Finset AtomA := {atom1, atom0, atom11, atom2, atom8, atom9, atom10}

/-- The atoms reachable from middle slot 2 (parser atom 4) without passing through atom 3. -/
def branchTwoAtoms : Finset AtomA := {atom4, atom6, atom13, atom5, atom14, atom15, atom16}

theorem branchZeroAtoms_closed :
    ∀ u ∈ branchZeroAtoms, ∀ w : AtomA,
      actualMolecule.mol.Adj u w → w ≠ atom3 → w ∈ branchZeroAtoms := by
  decide

theorem branchTwoAtoms_closed :
    ∀ u ∈ branchTwoAtoms, ∀ w : AtomA,
      actualMolecule.mol.Adj u w → w ≠ atom3 → w ∈ branchTwoAtoms := by
  decide

theorem branchZeroAtoms_center_eq :
    ∀ a : AtomA, a ∈ branchZeroAtoms → a ∈ actualMolecule.centers → a = atom1 := by
  decide

theorem branchTwoAtoms_center_eq :
    ∀ a : AtomA, a ∈ branchTwoAtoms → a ∈ actualMolecule.centers → a = atom4 := by
  decide

/-- A one-edge root-avoiding branch walk. -/
theorem actualBranchWalk_one {root a b : AtomA}
    (ha : a ≠ root) (hb : b ≠ root)
    (hab : actualMolecule.mol.Adj a b) :
    ActualParsedBranchWalk.BranchWalk actualMolecule.mol root a b :=
  ActualParsedBranchWalk.BranchWalk.step ha hab (ActualParsedBranchWalk.BranchWalk.refl hb)

/-- A two-edge root-avoiding branch walk. -/
theorem actualBranchWalk_two {root a b c : AtomA}
    (ha : a ≠ root) (hb : b ≠ root) (hc : c ≠ root)
    (hab : actualMolecule.mol.Adj a b) (hbc : actualMolecule.mol.Adj b c) :
    ActualParsedBranchWalk.BranchWalk actualMolecule.mol root a c :=
  ActualParsedBranchWalk.BranchWalk.step ha hab
    (ActualParsedBranchWalk.BranchWalk.step hb hbc (ActualParsedBranchWalk.BranchWalk.refl hc))

/-- Exact reachability of the middle-slot-0 carbon arm. -/
theorem ligandBranchReaches_middle_zero_iff (v : AtomA) :
    LigandBranchReaches actualMolecule actualMiddle 0 v ↔ v ∈ branchZeroAtoms := by
  constructor
  · rintro ⟨p, hp⟩
    have hstart : actualMolecule.ligandAtomAt actualMiddle 0 = atom1 := ligandAtomAt_middle_zero
    have hp' : ActualParsedBranchWalk.BranchWalk actualMolecule.mol actualMiddle.1 atom1 v := by
      have := ActualParsedBranchWalk.walk_to_branchWalk p hp
      rwa [hstart] at this
    exact (ActualParsedBranchWalk.BranchWalk.endpoint_mem_of_closed hp'
      branchZeroAtoms_closed) (by simp [branchZeroAtoms])
  · intro hv
    have hstart : actualMolecule.ligandAtomAt actualMiddle 0 = atom1 := ligandAtomAt_middle_zero
    have build : ActualParsedBranchWalk.BranchWalk actualMolecule.mol actualMiddle.1 atom1 v := by
      simp only [branchZeroAtoms, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ActualParsedBranchWalk.BranchWalk.refl (by decide)
      · exact actualBranchWalk_one (root := actualMiddle.1) (a := atom1) (b := atom0)
          (by decide) (by decide) (by decide)
      · exact actualBranchWalk_one (root := actualMiddle.1) (a := atom1) (b := atom11)
          (by decide) (by decide) (by decide)
      · exact actualBranchWalk_one (root := actualMiddle.1) (a := atom1) (b := atom2)
          (by decide) (by decide) (by decide)
      · exact actualBranchWalk_two (root := actualMiddle.1) (a := atom1) (b := atom0) (c := atom8)
          (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact actualBranchWalk_two (root := actualMiddle.1) (a := atom1) (b := atom0) (c := atom9)
          (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact actualBranchWalk_two (root := actualMiddle.1) (a := atom1) (b := atom0) (c := atom10)
          (by decide) (by decide) (by decide) (by decide) (by decide)
    simpa [hstart] using ActualParsedBranchWalk.branchWalk_to_ligandBranchReaches build

/-- Exact reachability of the middle-slot-2 carbon arm. -/
theorem ligandBranchReaches_middle_two_iff (v : AtomA) :
    LigandBranchReaches actualMolecule actualMiddle 2 v ↔ v ∈ branchTwoAtoms := by
  constructor
  · rintro ⟨p, hp⟩
    have hstart : actualMolecule.ligandAtomAt actualMiddle 2 = atom4 := ligandAtomAt_middle_two
    have hp' : ActualParsedBranchWalk.BranchWalk actualMolecule.mol actualMiddle.1 atom4 v := by
      have := ActualParsedBranchWalk.walk_to_branchWalk p hp
      rwa [hstart] at this
    exact (ActualParsedBranchWalk.BranchWalk.endpoint_mem_of_closed hp'
      branchTwoAtoms_closed) (by simp [branchTwoAtoms])
  · intro hv
    have hstart : actualMolecule.ligandAtomAt actualMiddle 2 = atom4 := ligandAtomAt_middle_two
    have build : ActualParsedBranchWalk.BranchWalk actualMolecule.mol actualMiddle.1 atom4 v := by
      simp only [branchTwoAtoms, Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ActualParsedBranchWalk.BranchWalk.refl (by decide)
      · exact actualBranchWalk_one (root := actualMiddle.1) (a := atom4) (b := atom6)
          (by decide) (by decide) (by decide)
      · exact actualBranchWalk_one (root := actualMiddle.1) (a := atom4) (b := atom13)
          (by decide) (by decide) (by decide)
      · exact actualBranchWalk_one (root := actualMiddle.1) (a := atom4) (b := atom5)
          (by decide) (by decide) (by decide)
      · exact actualBranchWalk_two (root := actualMiddle.1) (a := atom4) (b := atom6) (c := atom14)
          (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact actualBranchWalk_two (root := actualMiddle.1) (a := atom4) (b := atom6) (c := atom15)
          (by decide) (by decide) (by decide) (by decide) (by decide)
      · exact actualBranchWalk_two (root := actualMiddle.1) (a := atom4) (b := atom6) (c := atom16)
          (by decide) (by decide) (by decide) (by decide) (by decide)
    simpa [hstart] using ActualParsedBranchWalk.branchWalk_to_ligandBranchReaches build

/-- The only distinguished center in the middle-slot-0 branch is the parent carbon center. -/
theorem branchReaches_middle_zero_center {d : actualMolecule.Center}
    (hd : LigandBranchReaches actualMolecule actualMiddle 0 d.1) : d = centerC2 := by
  have h : d.1 = atom1 :=
    branchZeroAtoms_center_eq d.1 ((ligandBranchReaches_middle_zero_iff d.1).1 hd) d.2
  rcases d with ⟨a, ha⟩
  simp only at h
  subst h
  exact Subtype.ext rfl

/-- The only distinguished center in the middle-slot-2 branch is the outward carbon center. -/
theorem branchReaches_middle_two_center {d : actualMolecule.Center}
    (hd : LigandBranchReaches actualMolecule actualMiddle 2 d.1) : d = centerC3 := by
  have h : d.1 = atom4 :=
    branchTwoAtoms_center_eq d.1 ((ligandBranchReaches_middle_two_iff d.1).1 hd) d.2
  rcases d with ⟨a, ha⟩
  simp only at h
  subst h
  exact Subtype.ext rfl

/-- The parent carbon center lies in its own branch. -/
theorem ligandBranchReaches_middle_zero_centerC2 :
    LigandBranchReaches actualMolecule actualMiddle 0 centerC2.1 := by
  rw [ligandBranchReaches_middle_zero_iff]
  simp [branchZeroAtoms, centerC2, atom1]

/-- The outward carbon center lies in its own branch. -/
theorem ligandBranchReaches_middle_two_centerC3 :
    LigandBranchReaches actualMolecule actualMiddle 2 centerC3.1 := by
  rw [ligandBranchReaches_middle_two_iff]
  simp [branchTwoAtoms, centerC3, atom4]

/-! ## 6. Atom-number and adjacency facts on the actual parsed graph -/

theorem atomZ_atom0 : actualMolecule.mol.atomZ atom0 = 6 := by decide
theorem atomZ_atom1 : actualMolecule.mol.atomZ atom1 = 6 := by decide
theorem atomZ_atom2 : actualMolecule.mol.atomZ atom2 = 17 := by decide
theorem atomZ_atom3 : actualMolecule.mol.atomZ atom3 = 6 := by decide
theorem atomZ_atom4 : actualMolecule.mol.atomZ atom4 = 6 := by decide
theorem atomZ_atom5 : actualMolecule.mol.atomZ atom5 = 17 := by decide
theorem atomZ_atom6 : actualMolecule.mol.atomZ atom6 = 6 := by decide
theorem atomZ_atom7 : actualMolecule.mol.atomZ atom7 = 35 := by decide
theorem atomZ_atom11 : actualMolecule.mol.atomZ atom11 = 1 := by decide
theorem atomZ_atom12 : actualMolecule.mol.atomZ atom12 = 1 := by decide
theorem atomZ_atom13 : actualMolecule.mol.atomZ atom13 = 1 := by decide

/-- The exact neighbour list of the outward carbon center on the actual graph. -/
theorem adj_centerC3_iff (x : AtomA) :
    actualMolecule.mol.Adj atom4 x ↔
      x = atom3 ∨ x = atom13 ∨ x = atom5 ∨ x = atom6 := by
  revert x
  decide

/-! ## 7. What an arbitrary root-fixing arm exchange does to the two arms

The local slot permutation induced at the parent arm is computed from the actual atom numbers and
neighbour rows; it is not inferred from equality of the stored parity markers. -/

theorem aut_atomZ_image (e : actualMolecule.Aut) (v : AtomA) :
    actualMolecule.mol.atomZ ((e : Equiv.Perm AtomA) v) =
      actualMolecule.mol.atomZ v := by
  let eMol : actualMolecule.mol.Aut := ⟨(e : Equiv.Perm AtomA), e.property.1⟩
  simpa [eMol] using MoleculeGraph.Aut.atomZ_eq (m := actualMolecule.mol) eMol v

theorem aut_adj_image_iff (e : actualMolecule.Aut) (u v : AtomA) :
    actualMolecule.mol.Adj ((e : Equiv.Perm AtomA) u) ((e : Equiv.Perm AtomA) v) ↔
      actualMolecule.mol.Adj u v := by
  let eMol : actualMolecule.mol.Aut := ⟨(e : Equiv.Perm AtomA), e.property.1⟩
  simpa [eMol] using MoleculeGraph.Aut.adj_iff (m := actualMolecule.mol) eMol u v

/-- If the image of a ligand atom is a known ligand atom at the image center, the induced local
slot index is the corresponding one. -/
theorem ligandPermAt_eq_of_image (e : actualMolecule.Aut) {c c' : actualMolecule.Center}
    (hc : actualMolecule.centerPerm e c = c') {i k : Fin 4}
    (himg : (e : Equiv.Perm AtomA) (actualMolecule.ligandAtomAt c i) =
      actualMolecule.ligandAtomAt c' k) :
    actualMolecule.ligandPermAt e c i = k := by
  have h := actualMolecule.ligandAtomAt_ligandPermAt (e := e) (c := c) i
  rw [hc] at h
  exact actualMolecule.ligandAtomAt_injective c' (h.trans himg)

/-- Any root-fixing automorphism carrying middle slot 0 to middle slot 2 carries parser atom 1
(the parent carbon arm) to parser atom 4 (the outward carbon arm). -/
theorem image_atom1_of_maps_middle_zero_two (e : actualMolecule.Aut)
    (hefix : actualMolecule.centerPerm e actualMiddle = actualMiddle)
    (hmap : actualMolecule.ligandPermAt e actualMiddle 0 = 2) :
    (e : Equiv.Perm AtomA) atom1 = atom4 := by
  have h := actualMolecule.ligandAtomAt_ligandPermAt (e := e) (c := actualMiddle) (i := 0)
  rw [hefix, hmap, ligandAtomAt_middle_zero, ligandAtomAt_middle_two] at h
  exact h.symm

/-- A root-fixing automorphism fixes the middle parser atom 3. -/
theorem aut_fixes_middle_atom (e : actualMolecule.Aut)
    (hefix : actualMolecule.centerPerm e actualMiddle = actualMiddle) :
    (e : Equiv.Perm AtomA) atom3 = atom3 := by
  have h := (centerPerm_eq_iff actualMolecule e actualMiddle).1 hefix
  simpa [actualMiddle] using h

theorem centerPerm_centerC2_eq_centerC3_of_maps_middle_zero_two (e : actualMolecule.Aut)
    (hefix : actualMolecule.centerPerm e actualMiddle = actualMiddle)
    (hmap : actualMolecule.ligandPermAt e actualMiddle 0 = 2) :
    actualMolecule.centerPerm e centerC2 = centerC3 := by
  apply Subtype.ext
  show (e : Equiv.Perm AtomA) atom1 = atom4
  exact image_atom1_of_maps_middle_zero_two e hefix hmap

theorem image_atom2_of_maps_middle_zero_two (e : actualMolecule.Aut)
    (hefix : actualMolecule.centerPerm e actualMiddle = actualMiddle)
    (hmap : actualMolecule.ligandPermAt e actualMiddle 0 = 2) :
    (e : Equiv.Perm AtomA) atom2 = atom5 := by
  have he1 := image_atom1_of_maps_middle_zero_two e hefix hmap
  have hadj : actualMolecule.mol.Adj atom4 ((e : Equiv.Perm AtomA) atom2) := by
    have himg :=
      (aut_adj_image_iff e atom1 atom2).2 (by decide : actualMolecule.mol.Adj atom1 atom2)
    simpa [he1] using himg
  have hmem := (adj_centerC3_iff ((e : Equiv.Perm AtomA) atom2)).1 hadj
  have hz : actualMolecule.mol.atomZ ((e : Equiv.Perm AtomA) atom2) = 17 := by
    rw [aut_atomZ_image e atom2, atomZ_atom2]
  rcases hmem with h | h | h | h
  · rw [h, atomZ_atom3] at hz
    norm_num at hz
  · rw [h, atomZ_atom13] at hz
    norm_num at hz
  · exact h
  · rw [h, atomZ_atom6] at hz
    norm_num at hz

theorem image_atom11_of_maps_middle_zero_two (e : actualMolecule.Aut)
    (hefix : actualMolecule.centerPerm e actualMiddle = actualMiddle)
    (hmap : actualMolecule.ligandPermAt e actualMiddle 0 = 2) :
    (e : Equiv.Perm AtomA) atom11 = atom13 := by
  have he1 := image_atom1_of_maps_middle_zero_two e hefix hmap
  have hadj : actualMolecule.mol.Adj atom4 ((e : Equiv.Perm AtomA) atom11) := by
    have himg :=
      (aut_adj_image_iff e atom1 atom11).2 (by decide : actualMolecule.mol.Adj atom1 atom11)
    simpa [he1] using himg
  have hmem := (adj_centerC3_iff ((e : Equiv.Perm AtomA) atom11)).1 hadj
  have hz : actualMolecule.mol.atomZ ((e : Equiv.Perm AtomA) atom11) = 1 := by
    rw [aut_atomZ_image e atom11, atomZ_atom11]
  rcases hmem with h | h | h | h
  · rw [h, atomZ_atom3] at hz
    norm_num at hz
  · exact h
  · rw [h, atomZ_atom5] at hz
    norm_num at hz
  · rw [h, atomZ_atom6] at hz
    norm_num at hz

theorem image_atom0_of_maps_middle_zero_two (e : actualMolecule.Aut)
    (hefix : actualMolecule.centerPerm e actualMiddle = actualMiddle)
    (hmap : actualMolecule.ligandPermAt e actualMiddle 0 = 2) :
    (e : Equiv.Perm AtomA) atom0 = atom6 := by
  have he1 := image_atom1_of_maps_middle_zero_two e hefix hmap
  have he3 := aut_fixes_middle_atom e hefix
  have hadj : actualMolecule.mol.Adj atom4 ((e : Equiv.Perm AtomA) atom0) := by
    have himg :=
      (aut_adj_image_iff e atom1 atom0).2 (by decide : actualMolecule.mol.Adj atom1 atom0)
    simpa [he1] using himg
  have hmem := (adj_centerC3_iff ((e : Equiv.Perm AtomA) atom0)).1 hadj
  have hz : actualMolecule.mol.atomZ ((e : Equiv.Perm AtomA) atom0) = 6 := by
    rw [aut_atomZ_image e atom0, atomZ_atom0]
  rcases hmem with h | h | h | h
  · have hcontra : atom0 = atom3 :=
      (e : Equiv.Perm AtomA).injective (h.trans he3.symm)
    exact absurd hcontra (by decide)
  · rw [h, atomZ_atom13] at hz
    norm_num at hz
  · rw [h, atomZ_atom5] at hz
    norm_num at hz
  · exact h

/-- The odd transposition `0 ↔ 3` carries local sign `-1`. -/
theorem permHandedness_swap_zero_three :
    permHandedness (Equiv.swap (0 : Fin 4) 3) = -1 := by
  norm_num [permHandedness, Equiv.Perm.sign_swap (by decide : (0 : Fin 4) ≠ 3)]

/-- **Induced local slot permutation at the parent arm.**  Any root-fixing automorphism sending
middle slot 0 to middle slot 2 acts on the frames at parser atom 1 by the odd transposition
`0 ↔ 3`.  This is the computed reason why equal stored marker letters on the two arms still give
mirror-related branches. -/
theorem ligandPermAt_centerC2_eq_swap (e : actualMolecule.Aut)
    (hefix : actualMolecule.centerPerm e actualMiddle = actualMiddle)
    (hmap : actualMolecule.ligandPermAt e actualMiddle 0 = 2) :
    actualMolecule.ligandPermAt e centerC2 = Equiv.swap (0 : Fin 4) 3 := by
  have hcenter := centerPerm_centerC2_eq_centerC3_of_maps_middle_zero_two e hefix hmap
  have he0 := image_atom0_of_maps_middle_zero_two e hefix hmap
  have he2 := image_atom2_of_maps_middle_zero_two e hefix hmap
  have he11 := image_atom11_of_maps_middle_zero_two e hefix hmap
  have he3 := aut_fixes_middle_atom e hefix
  have h0 : actualMolecule.ligandPermAt e centerC2 0 = 3 := by
    refine ligandPermAt_eq_of_image e hcenter (i := 0) (k := 3) ?_
    rw [ligandAtomAt_centerC2_zero, he0, ligandAtomAt_centerC3_three]
  have h1 : actualMolecule.ligandPermAt e centerC2 1 = 1 := by
    refine ligandPermAt_eq_of_image e hcenter (i := 1) (k := 1) ?_
    rw [ligandAtomAt_centerC2_one, he11, ligandAtomAt_centerC3_one]
  have h2 : actualMolecule.ligandPermAt e centerC2 2 = 2 := by
    refine ligandPermAt_eq_of_image e hcenter (i := 2) (k := 2) ?_
    rw [ligandAtomAt_centerC2_two, he2, ligandAtomAt_centerC3_two]
  have h3 : actualMolecule.ligandPermAt e centerC2 3 = 0 := by
    refine ligandPermAt_eq_of_image e hcenter (i := 3) (k := 0) ?_
    rw [ligandAtomAt_centerC2_three, he3, ligandAtomAt_centerC3_zero]
  ext i
  fin_cases i <;> simp [h0, h1, h2, h3] <;> decide

/-- The middle hydrogen slot 1 is unique by atomic number. -/
theorem middle_atomZ_ne_one_of_ne_one :
    ∀ k : Fin 4, k ≠ 1 →
      actualMolecule.mol.atomZ (actualMolecule.ligandAtomAt actualMiddle k) ≠ 1 := by
  decide

/-- The middle bromine slot 3 is unique by atomic number. -/
theorem middle_atomZ_ne_thirtyfive_of_ne_three :
    ∀ k : Fin 4, k ≠ 3 →
      actualMolecule.mol.atomZ (actualMolecule.ligandAtomAt actualMiddle k) ≠ 35 := by
  decide

/-- Every root-fixing automorphism fixes the middle hydrogen (slot 1) and bromine (slot 3). -/
theorem ligandPermAt_middle_fixes_one_three (e : actualMolecule.Aut)
    (hefix : actualMolecule.centerPerm e actualMiddle = actualMiddle) :
    actualMolecule.ligandPermAt e actualMiddle 1 = 1 ∧
      actualMolecule.ligandPermAt e actualMiddle 3 = 3 := by
  have hz1 : actualMolecule.mol.atomZ
      (actualMolecule.ligandAtomAt actualMiddle
        (actualMolecule.ligandPermAt e actualMiddle 1)) = 1 := by
    have h := actualMolecule.ligandAtomAt_ligandPermAt (e := e) (c := actualMiddle) (i := 1)
    rw [hefix] at h
    rw [h, ligandAtomAt_middle_one, aut_atomZ_image e atom12, atomZ_atom12]
  have hz3 : actualMolecule.mol.atomZ
      (actualMolecule.ligandAtomAt actualMiddle
        (actualMolecule.ligandPermAt e actualMiddle 3)) = 35 := by
    have h := actualMolecule.ligandAtomAt_ligandPermAt (e := e) (c := actualMiddle) (i := 3)
    rw [hefix] at h
    rw [h, ligandAtomAt_middle_three, aut_atomZ_image e atom7, atomZ_atom7]
  constructor
  · by_contra hne
    exact middle_atomZ_ne_one_of_ne_one (actualMolecule.ligandPermAt e actualMiddle 1) hne hz1
  · by_contra hne
    exact middle_atomZ_ne_thirtyfive_of_ne_three
      (actualMolecule.ligandPermAt e actualMiddle 3) hne hz3

/-- A non-identity arm exchange at the middle center can only be the exchange of the two carbon
slots 0 and 2. -/
theorem middle_ligandPerm_pair {e : actualMolecule.Aut}
    (hefix : actualMolecule.centerPerm e actualMiddle = actualMiddle)
    {i j : Fin 4} (hij : i ≠ j)
    (hmap : actualMolecule.ligandPermAt e actualMiddle i = j) :
    (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) := by
  have hfix := ligandPermAt_middle_fixes_one_three e hefix
  have hinj := (actualMolecule.ligandPermAt e actualMiddle).injective
  have hi : i = 0 ∨ i = 2 := by
    fin_cases i
    · exact Or.inl rfl
    · exfalso
      exact hij (hmap.symm.trans hfix.1).symm
    · exact Or.inr rfl
    · exfalso
      exact hij (hmap.symm.trans hfix.2).symm
  have hjne1 : j ≠ 1 := by
    intro hj1
    have hi1 : i = 1 := by
      apply hinj
      rw [hmap, hj1, hfix.1]
    exact hij (hi1.trans hj1.symm)
  have hjne3 : j ≠ 3 := by
    intro hj3
    have hi3 : i = 3 := by
      apply hinj
      rw [hmap, hj3, hfix.2]
    exact hij (hi3.trans hj3.symm)
  have hj : j = 0 ∨ j = 2 := by
    have hlt : j.val < 4 := j.isLt
    have h1 : j.val ≠ 1 := fun hv => hjne1 (Fin.ext hv)
    have h3 : j.val ≠ 3 := fun hv => hjne3 (Fin.ext hv)
    have hval : j.val = 0 ∨ j.val = 2 := by omega
    rcases hval with h | h
    · exact Or.inl (Fin.ext h)
    · exact Or.inr (Fin.ext h)
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · exact absurd rfl hij
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hij

/-! ## 8. The concrete arm exchange as a mirror transport -/

@[simp] theorem armSwapAut_apply (v : AtomA) :
    (armSwapAut : Equiv.Perm AtomA) v = armSwap v := rfl

theorem armSwapAut_centerPerm_middle :
    actualMolecule.centerPerm armSwapAut actualMiddle = actualMiddle := by
  apply Subtype.ext
  simp [MultiCenterMolecule.centerPerm, actualMiddle]

theorem armSwapAut_centerPerm_centerC2 :
    actualMolecule.centerPerm armSwapAut centerC2 = centerC3 := by
  apply Subtype.ext
  simp [MultiCenterMolecule.centerPerm, centerC2, centerC3]

theorem armSwapAut_ligandPerm_middle_zero_two :
    actualMolecule.ligandPermAt armSwapAut actualMiddle 0 = 2 := by
  refine ligandPermAt_eq_of_image armSwapAut armSwapAut_centerPerm_middle (i := 0) (k := 2) ?_
  rw [ligandAtomAt_middle_zero, armSwapAut_apply, armSwap_apply_atom1,
    ligandAtomAt_middle_two]

theorem ligandPermAt_centerC2_armSwap :
    actualMolecule.ligandPermAt armSwapAut centerC2 = Equiv.swap (0 : Fin 4) 3 :=
  ligandPermAt_centerC2_eq_swap armSwapAut armSwapAut_centerPerm_middle
    armSwapAut_ligandPerm_middle_zero_two

theorem permHandedness_ligandPermAt_centerC2_armSwap :
    permHandedness (actualMolecule.ligandPermAt armSwapAut centerC2) = -1 := by
  rw [ligandPermAt_centerC2_armSwap, permHandedness_swap_zero_three]

/-- The actual arm exchange is a mirror transport of middle slot 0 to middle slot 2. -/
theorem mirrorTransport_middle_zero_two :
    MirrorTransport actualMolecule actualCfg actualMiddle 0 2 := by
  unfold MirrorTransport BranchTransport
  refine ⟨armSwapAut, armSwapAut_centerPerm_middle, armSwapAut_ligandPerm_middle_zero_two, ?_⟩
  intro d hd
  rw [branchReaches_middle_zero_center hd]
  rw [armSwapAut_centerPerm_centerC2, ligandPermAt_centerC2_armSwap,
    actualCfg_sign_centerC2, actualCfg_sign_centerC3]
  norm_num [permHandedness_swap_zero_three]

/-- No proper transport of middle slot 0 to middle slot 2 exists.  The middle hydrogen and bromine
force any root-fixing arm exchange into the two carbon slots, and the induced local permutation at
the parent arm is odd, so the proper sign equation fails. -/
theorem not_properTransport_middle_zero_two :
    ¬ ProperTransport actualMolecule actualCfg actualMiddle 0 2 := by
  intro h
  unfold ProperTransport BranchTransport at h
  rcases h with ⟨e, hefix, hmap, hcond⟩
  have hcenter := centerPerm_centerC2_eq_centerC3_of_maps_middle_zero_two e hefix hmap
  have hloc := ligandPermAt_centerC2_eq_swap e hefix hmap
  have hsign := hcond centerC2 ligandBranchReaches_middle_zero_centerC2
  rw [hcenter, hloc, actualCfg_sign_centerC2, actualCfg_sign_centerC3] at hsign
  norm_num [permHandedness_swap_zero_three] at hsign

theorem not_properTransport_middle_two_zero :
    ¬ ProperTransport actualMolecule actualCfg actualMiddle 2 0 := by
  intro h
  exact not_properTransport_middle_zero_two
    (branchTransport_inverse actualMolecule actualCfg actualMiddle h)

/-- Pairwise proper-distinguishability of the four middle ligand slots for variant A. -/
theorem not_properTransport_middle_pair {i j : Fin 4} (hij : i ≠ j) :
    ¬ ProperTransport actualMolecule actualCfg actualMiddle i j := by
  intro h
  unfold ProperTransport BranchTransport at h
  rcases h with ⟨e, hefix, hmap, hcond⟩
  rcases middle_ligandPerm_pair hefix hij hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact not_properTransport_middle_zero_two ⟨e, hefix, hmap, hcond⟩
  · exact not_properTransport_middle_two_zero ⟨e, hefix, hmap, hcond⟩

/-- The two actual carbon arms are enantiomorphic. -/
theorem enantiomorphic_middle_zero_two :
    Enantiomorphic actualMolecule actualCfg actualMiddle 0 2 :=
  ⟨by decide, mirrorTransport_middle_zero_two, not_properTransport_middle_zero_two⟩

theorem enantiomorphic_middle_two_zero :
    Enantiomorphic actualMolecule actualCfg actualMiddle 2 0 :=
  enantiomorphic_symm actualMolecule actualCfg actualMiddle enantiomorphic_middle_zero_two

/-- Exactly the two orientations of the unordered pair of actual carbon arms 0 and 2 are
enantiomorphic at the middle center. -/
theorem enantiomorphic_middle_iff (i j : Fin 4) :
    Enantiomorphic actualMolecule actualCfg actualMiddle i j ↔
      (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) := by
  constructor
  · intro h
    rcases h with ⟨hij, hm, _⟩
    unfold MirrorTransport BranchTransport at hm
    rcases hm with ⟨e, hefix, hmap, _⟩
    exact middle_ligandPerm_pair hefix hij hmap
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact enantiomorphic_middle_zero_two
    · exact enantiomorphic_middle_two_zero

/-! ## 9. The actual pseudoasymmetric unit among the real parsed ligand atoms -/

/-- The four actual ligand atoms at the middle parser center. -/
def actualLigand : Fin 4 → AtomA := fun i => actualMolecule.ligandAtomAt actualMiddle i

/-- Enantiomorphy of actual ligand atoms, transported through the actual ligand enumeration. -/
def actualLigandEnant (a b : AtomA) : Prop :=
  ∃ i j : Fin 4, actualLigand i = a ∧ actualLigand j = b ∧
    Enantiomorphic actualMolecule actualCfg actualMiddle i j

theorem actualLigand_distinguishable :
    ∀ first second : Fin 4, first ≠ second →
      actualLigand first ≠ actualLigand second := by
  intro first second hne heq
  exact hne (actualMolecule.ligandAtomAt_injective actualMiddle heq)

/-- The actual parsed middle center has exactly one enantiomorphic pair of actual ligand atoms. -/
theorem exactlyOneEnantiomorphicPair_actual :
    BlueBookP92.ExactlyOneEnantiomorphicPair actualLigand actualLigandEnant := by
  refine ⟨0, 2, by decide, ?_, ?_⟩
  · exact ⟨0, 2, rfl, rfl, enantiomorphic_middle_zero_two⟩
  · intro first second hne hen
    rcases hen with ⟨i, j, hi, hj, henij⟩
    have hia : i = first := actualMolecule.ligandAtomAt_injective actualMiddle hi
    have hjb : j = second := actualMolecule.ligandAtomAt_injective actualMiddle hj
    have hen' : Enantiomorphic actualMolecule actualCfg actualMiddle first second := by
      simpa [← hia, ← hjb] using henij
    exact (enantiomorphic_middle_iff first second).1 hen'

/-- The actual middle center is a pseudoasymmetric unit in the independent P-92 sense. -/
theorem actual_isPseudoasymmetricUnit :
    BlueBookP92.IsPseudoasymmetricUnit actualLigand (fun a b : AtomA => a ≠ b)
      actualLigandEnant :=
  ⟨actualLigand_distinguishable, exactlyOneEnantiomorphicPair_actual⟩

/-- Non-vacuity of the witness: the enantiomorphic pair is a genuine pair of distinct actual
ligand atoms, and the realizing graph automorphism is nontrivial. -/
theorem actual_witness_nontrivial :
    (0 : Fin 4) ≠ 2 ∧ actualLigand 0 ≠ actualLigand 2 ∧
      (armSwapAut : Equiv.Perm AtomA) atom1 ≠ atom1 := by
  refine ⟨by decide, ?_, ?_⟩
  · intro h
    exact absurd (actualMolecule.ligandAtomAt_injective actualMiddle h) (by decide)
  · rw [armSwapAut_apply]
    exact armSwap_nontrivial

/-- **Combined agreement theorem.**  The independent physical branch symmetry of the actual parsed
17-atom graph makes the middle center a pseudoasymmetric unit with exactly one enantiomorphic pair,
and the actual already-computed production record is `(R, uppercase = false)`.  No supplied label
is a hypothesis. -/
theorem actual_parsed_pseudoasymmetry_runtime_agreement :
    BlueBookP92.IsPseudoasymmetricUnit actualLigand (fun a b : AtomA => a ≠ b)
        actualLigandEnant ∧
      (tetrahedralOccurrenceFactAuthoritative? molA fuelA middleAtom).map
        (fun fact => (fact.descriptor, fact.uppercase)) = some (RS.R, false) :=
  ⟨actual_isPseudoasymmetricUnit, c0_output_A⟩

/-! ## 10. Negative control: the original fixture's parity assignment

The original fixture differs only in atom 4's marker.  On the same actual parsed graph, we read a
configuration from the original molecule's parsed markers.  Its arm exchange is then *proper*
rather than mirror, and no middle pair is enantiomorphic; the original middle-center production
evaluation is indeed `none`. -/

/-- The parsed tetrahedral marker of the original fixture at an actual parsed atom. -/
def parsedParityOriginal (a : AtomA) : Option TetrahedralInputParity :=
  (ConstitutionalRootStageAvailability.mol.atomAt? a.1).bind (fun spec => spec.tetrahedral?)

/-- The original fixture's configuration, read from its own parsed markers on the actual graph. -/
def originalCfg (c : actualMolecule.Center) : Equiv.Perm (Fin 4) :=
  frameOfParity (parsedParityOriginal c.1)

theorem parsedParityOriginal_one :
    parsedParityOriginal atom1 = some TetrahedralInputParity.clockwise := by decide
theorem parsedParityOriginal_three :
    parsedParityOriginal atom3 = some TetrahedralInputParity.clockwise := by decide
theorem parsedParityOriginal_four :
    parsedParityOriginal atom4 = some TetrahedralInputParity.anticlockwise := by decide

theorem originalCfg_centerC2 :
    originalCfg centerC2 = MultiCenterMolecule.mirrorFrame := by
  simp [originalCfg, centerC2, parsedParityOriginal_one]

theorem originalCfg_middle :
    originalCfg actualMiddle = MultiCenterMolecule.mirrorFrame := by
  simp [originalCfg, actualMiddle, parsedParityOriginal_three]

theorem originalCfg_centerC3 : originalCfg centerC3 = 1 := by
  simp [originalCfg, centerC3, parsedParityOriginal_four]

theorem originalCfg_sign_centerC2 :
    actualMolecule.configurationSign originalCfg centerC2 = -1 := by
  rw [MultiCenterMolecule.configurationSign, originalCfg_centerC2]
  simp [MultiCenterMolecule.mirrorFrame]

theorem originalCfg_sign_middle :
    actualMolecule.configurationSign originalCfg actualMiddle = -1 := by
  rw [MultiCenterMolecule.configurationSign, originalCfg_middle]
  simp [MultiCenterMolecule.mirrorFrame]

theorem originalCfg_sign_centerC3 :
    actualMolecule.configurationSign originalCfg centerC3 = 1 := by
  rw [MultiCenterMolecule.configurationSign, originalCfg_centerC3]
  simp

/-- With the original parity assignment the same actual graph automorphism is a *proper*
transport of the two carbon arms. -/
theorem properTransport_middle_zero_two_original :
    ProperTransport actualMolecule originalCfg actualMiddle 0 2 := by
  unfold ProperTransport BranchTransport
  refine ⟨armSwapAut, armSwapAut_centerPerm_middle, armSwapAut_ligandPerm_middle_zero_two, ?_⟩
  intro d hd
  rw [branchReaches_middle_zero_center hd]
  rw [armSwapAut_centerPerm_centerC2, ligandPermAt_centerC2_armSwap,
    originalCfg_sign_centerC2, originalCfg_sign_centerC3]
  norm_num [permHandedness_swap_zero_three]

theorem properTransport_middle_two_zero_original :
    ProperTransport actualMolecule originalCfg actualMiddle 2 0 :=
  branchTransport_inverse actualMolecule originalCfg actualMiddle
    properTransport_middle_zero_two_original

/-- Under the original parity assignment no middle pair is enantiomorphic. -/
theorem not_enantiomorphic_middle_original {i j : Fin 4} (hij : i ≠ j) :
    ¬ Enantiomorphic actualMolecule originalCfg actualMiddle i j := by
  intro h
  rcases h with ⟨_, hm, hp⟩
  unfold MirrorTransport BranchTransport at hm
  rcases hm with ⟨e, hefix, hmap, _⟩
  rcases middle_ligandPerm_pair hefix hij hmap with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hp properTransport_middle_zero_two_original
  · exact hp properTransport_middle_two_zero_original

/-- Negative-control conjunction: the original arm exchange is proper, no middle pair is
enantiomorphic, and the original actual middle-center evaluation refuses. -/
theorem original_parity_proper_and_runtime_refusal :
    ProperTransport actualMolecule originalCfg actualMiddle 0 2 ∧
      (∀ i j : Fin 4, i ≠ j →
        ¬ Enantiomorphic actualMolecule originalCfg actualMiddle i j) ∧
      tetrahedralOccurrenceFactAuthoritative? mol fuelA middleAtom = none :=
  ⟨properTransport_middle_zero_two_original,
    fun i j hij => not_enantiomorphic_middle_original hij,
    by simpa [fuelA, ConstitutionalRootStageAvailability.fuel] using existing_c0_root_refused⟩

end

end ActualParsedBranchSymmetryFidelity
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards (stages 1–2) -/

assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actual_atomCount
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom0
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom1
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom2
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom3
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom4
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom5
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom6
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom7
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom8
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom9
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom10
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom11
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom12
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom13
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom14
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom15
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atom16
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandAt
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualMolecule
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.centerC2
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualMiddle
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.centerC3
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actual_ligand_enumerations
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.frameOfParity
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.frameOfParity_clockwise
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.frameOfParity_anticlockwise
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.frameOfParity_none
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.parsedParityA
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualCfg
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.parsedParityA_one
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.parsedParityA_three
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.parsedParityA_four
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualCfg_centerC2
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualCfg_middle
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualCfg_centerC3
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualCfg_sign_centerC2
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualCfg_sign_middle
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualCfg_sign_centerC3
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actual_arms_same_parsed_marker
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_nontrivial
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_atomAt?_eq
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atomMassAt_eq_of_atomAt?_eq
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_atomMass_eq
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_isAutomorphism
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_preservesCenters
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwapAut
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ActualParsedBranchWalk.BranchWalk.start_ne_root
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ActualParsedBranchWalk.BranchWalk.endpoint_ne_root
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ActualParsedBranchWalk.BranchWalk.endpoint_mem_of_closed
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ActualParsedBranchWalk.branchWalk_to_walk
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ActualParsedBranchWalk.walk_to_branchWalk
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ActualParsedBranchWalk.branchWalk_to_ligandBranchReaches
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ActualParsedBranchWalk.ligandBranchReaches_not_root
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.branchZeroAtoms
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.branchTwoAtoms
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.branchZeroAtoms_closed
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.branchTwoAtoms_closed
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.branchZeroAtoms_center_eq
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.branchTwoAtoms_center_eq
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualBranchWalk_one
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualBranchWalk_two
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandBranchReaches_middle_zero_iff
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandBranchReaches_middle_two_iff
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.branchReaches_middle_zero_center
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.branchReaches_middle_two_center
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandBranchReaches_middle_zero_centerC2
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandBranchReaches_middle_two_centerC3

/-! ### Stage 1 slot and arm-swap lemmas -/

assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandAtomAt_centerC2_zero
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandAtomAt_centerC2_one
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandAtomAt_centerC2_two
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandAtomAt_centerC2_three
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandAtomAt_middle_zero
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandAtomAt_middle_one
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandAtomAt_middle_two
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandAtomAt_middle_three
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandAtomAt_centerC3_zero
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandAtomAt_centerC3_one
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandAtomAt_centerC3_two
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandAtomAt_centerC3_three
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom0
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom1
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom2
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom3
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom4
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom5
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom6
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom7
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom8
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom9
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom10
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom11
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom12
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom13
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom14
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom15
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwap_apply_atom16

/-! ### Stage 2 branch-symmetry exports -/

assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atomZ_atom0
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atomZ_atom1
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atomZ_atom2
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atomZ_atom3
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atomZ_atom4
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atomZ_atom5
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atomZ_atom6
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atomZ_atom7
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atomZ_atom11
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atomZ_atom12
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.atomZ_atom13
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.adj_centerC3_iff
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.aut_atomZ_image
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.aut_adj_image_iff
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandPermAt_eq_of_image
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.image_atom1_of_maps_middle_zero_two
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.aut_fixes_middle_atom
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.centerPerm_centerC2_eq_centerC3_of_maps_middle_zero_two
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.image_atom2_of_maps_middle_zero_two
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.image_atom11_of_maps_middle_zero_two
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.image_atom0_of_maps_middle_zero_two
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.permHandedness_swap_zero_three
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandPermAt_centerC2_eq_swap
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.middle_atomZ_ne_one_of_ne_one
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.middle_atomZ_ne_thirtyfive_of_ne_three
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandPermAt_middle_fixes_one_three
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.middle_ligandPerm_pair
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwapAut_apply
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwapAut_centerPerm_middle
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwapAut_centerPerm_centerC2
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.armSwapAut_ligandPerm_middle_zero_two
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.ligandPermAt_centerC2_armSwap
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.permHandedness_ligandPermAt_centerC2_armSwap
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.mirrorTransport_middle_zero_two
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.not_properTransport_middle_zero_two
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.not_properTransport_middle_two_zero
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.not_properTransport_middle_pair
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.enantiomorphic_middle_zero_two
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.enantiomorphic_middle_two_zero
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.enantiomorphic_middle_iff
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualLigand
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualLigandEnant
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actualLigand_distinguishable
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.exactlyOneEnantiomorphicPair_actual
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actual_isPseudoasymmetricUnit
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actual_witness_nontrivial
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.actual_parsed_pseudoasymmetry_runtime_agreement
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.parsedParityOriginal
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.originalCfg
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.parsedParityOriginal_one
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.parsedParityOriginal_three
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.parsedParityOriginal_four
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.originalCfg_centerC2
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.originalCfg_middle
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.originalCfg_centerC3
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.originalCfg_sign_centerC2
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.originalCfg_sign_middle
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.originalCfg_sign_centerC3
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.properTransport_middle_zero_two_original
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.properTransport_middle_two_zero_original
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.not_enantiomorphic_middle_original
assert_kernel_only TetraStereo.OneCenter.ActualParsedBranchSymmetryFidelity.original_parity_proper_and_runtime_refusal
