import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion
import TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityEvidence
import TetraStereo.KernelOnly
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 8192

/-!
# A decorated hidden-parity cage: physical side and blind mirror law

The formal input `C(H)(Cl)(C*A)(C*B)`, 21 atoms, single bonds. Each arm is a stereocentre
`C*X(H)(F)` carrying a four-membered-ring cage `C1X <(O,O,O)> C3X — H` (the cage of
`LocalizedRecursiveAuxiliaryPhysicalCompletion`, moved one bond outward):

```
atom  0 1 2  3   4 5 6   7 8 9 10 11  12  13 14 15  16 17 18 19 20
      C H Cl C*A H F C1A H O O O  C3A C*B H  F  C1B H  O  O  O  C3B
```

Bonds: `0-{1,2,3,12}`; arm A `3-{4,5,6}`, `6-{8,9,10}`, `11-{7,8,9,10}`; arm B the same shifted by
nine. The detected centres are `0, 3, 6, 11, 12, 15, 20`.

**Coordinates.** Arm B's attachment atoms are the reflections `x ↦ -x` of arm A's (`C*B`, its H
and F, `C1B`), so the arm swap obeys the *mirror* sign law at `C*A ↦ C*B`. Cage A's hydrogen lies
outside its bridge plane, cage B's inside, so the bridgehead parities `s(C1X)·s(C3X)` differ.

**Physical side.** Every root-fixing automorphism carrying arm A to arm B carries `C1A, C3A` to
`C1B, C3B` with equal handedness at both (`arm_coupled`), so the parity invariant forbids every
proper and every mirror branch transport (`not_branchTransport_of_parityCoupling`): the root is
pairwise properly distinguishable and has **no** physical enantiomorphic pair.

**Blind mirror law.** At every centre reached in arm A the arm swap obeys the mirror sign law
(`C*A`) or both the occurrence and its image carry the accepted reader-free refusal witnesses
(cage bridgeheads, `cycleWitness`/`swapWitness` shape at the longer histories).

Chemical realizability of this short cage is not established (as for the undecorated cage).
-/

namespace TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.SemanticMolecule
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.MoleculeGraph
open TetraStereo.OneCenter.LocalizedCyclicPseudoInputWitness
open TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
open TetraStereo.OneCenter.CartesianPoint3
open TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryPhysicalCompletion
  (oxygen point Cage Cage.history_c1 Cage.history_c3 inComponent_closed handedness_of_cube)

/-! ## The source -/

def fluorine : SemanticAtom := { element := element 9 (by decide) (by decide) }

def Q0 : CartesianPoint3 := point 0 0 0
def Q1 : CartesianPoint3 := point 0 0 1
def Q2 : CartesianPoint3 := point 0 1 0
def Q3 : CartesianPoint3 := point 2 0 0
def Q4 : CartesianPoint3 := point 2 0 1
def Q5 : CartesianPoint3 := point 2 1 (-1)
def Q6 : CartesianPoint3 := point 4 0 0
/-- Cage A's hydrogen lies outside its bridge plane. -/
def Q7 : CartesianPoint3 := point 7 0 0
def Q8 : CartesianPoint3 := point 5 1 0
def Q9 : CartesianPoint3 := point 5 (-1) 1
def Q10 : CartesianPoint3 := point 5 (-1) (-1)
def Q11 : CartesianPoint3 := point 6 0 0
def Q12 : CartesianPoint3 := point (-2) 0 0
def Q13 : CartesianPoint3 := point (-2) 0 1
def Q14 : CartesianPoint3 := point (-2) 1 (-1)
def Q15 : CartesianPoint3 := point (-4) 0 0
/-- Cage B's hydrogen lies inside the cage, on the root side of its bridge plane. -/
def Q16 : CartesianPoint3 := point (-9 / 2) 0 0
def Q17 : CartesianPoint3 := point (-5) 1 0
def Q18 : CartesianPoint3 := point (-5) (-1) 1
def Q19 : CartesianPoint3 := point (-5) (-1) (-1)
def Q20 : CartesianPoint3 := point (-6) 0 0

def positions : List CartesianPoint3 :=
  [Q0, Q1, Q2, Q3, Q4, Q5, Q6, Q7, Q8, Q9, Q10, Q11, Q12, Q13, Q14, Q15, Q16, Q17, Q18, Q19, Q20]

def decoratedSource : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms := [carbon, hydrogen, chlorine, carbon, hydrogen, fluorine, carbon, hydrogen,
          oxygen, oxygen, oxygen, carbon, carbon, hydrogen, fluorine, carbon, hydrogen,
          oxygen, oxygen, oxygen, carbon]
        interactions :=
          [singleBond 0 1, singleBond 0 2, singleBond 0 3, singleBond 0 12,
            singleBond 3 4, singleBond 3 5, singleBond 3 6,
            singleBond 6 8, singleBond 6 9, singleBond 6 10, singleBond 7 11,
            singleBond 8 11, singleBond 9 11, singleBond 10 11,
            singleBond 12 13, singleBond 12 14, singleBond 12 15,
            singleBond 15 17, singleBond 15 18, singleBond 15 19, singleBond 16 20,
            singleBond 17 20, singleBond 18 20, singleBond 19 20] }
    spatial? := some { positions := positions } }

theorem source_structurallyWellFormed : decoratedSource.structurallyWellFormed? = true := by
  decide +kernel

theorem source_graphReady : decoratedSource.molecule.localizedCIPGraphReady? = true := by
  decide +kernel

def decoratedAuthority : CertifiedAuthoritativeChemicalInput :=
  { input := decoratedSource
    structurallyWellFormed :=
      (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff decoratedSource).mp
        source_structurallyWellFormed }

def decoratedCertified : CertifiedLocalizedCIPInput :=
  { certified := decoratedAuthority
    graphReady :=
      (decoratedSource.molecule.localizedCIPGraphReady?_eq_true_iff).mp source_graphReady }

theorem atomCount_eq : decoratedSource.molecule.atomCount = 21 := rfl

abbrev graph : MoleculeGraph (Fin 21) := decoratedCertified.moleculeGraph

theorem simple_bonded : graph.SimpleBonded := by
  intro left right adjacent
  fin_cases left <;> fin_cases right <;> first
    | exact absurd adjacent (by decide)
    | decide

theorem degree_four_iff (atom : Fin 21) :
    atom ∈ graph.tetrahedralCenterSet ↔
      atom = 0 ∨ atom = 3 ∨ atom = 6 ∨ atom = 11 ∨ atom = 12 ∨ atom = 15 ∨ atom = 20 := by
  fin_cases atom <;> decide

theorem constant_charge :
    AcyclicCutBranchAutomorphism.ConstantFormalCharge decoratedCertified.moleculeGraph := by
  refine ⟨0, ?_⟩
  intro atom
  fin_cases atom <;> decide

/-! ## Explicit automorphisms -/

def armSwapFun (atom : Fin 21) : Fin 21 :=
  if h₁ : 3 ≤ atom.val then
    if h₂ : atom.val ≤ 11 then ⟨atom.val + 9, by omega⟩
    else ⟨atom.val - 9, by have := atom.isLt; omega⟩
  else atom

private theorem armSwap_involutive : Function.Involutive armSwapFun := by
  intro atom
  fin_cases atom <;> rfl

def armSwapPerm : Equiv.Perm (Fin 21) where
  toFun := armSwapFun
  invFun := armSwapFun
  left_inv := armSwap_involutive
  right_inv := armSwap_involutive

theorem armSwap_isAutomorphism : graph.IsAutomorphism armSwapPerm := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

def armSwap : graph.Aut := ⟨armSwapPerm, armSwap_isAutomorphism⟩

def cycleAPerm : Equiv.Perm (Fin 21) := Equiv.swap 8 9 * Equiv.swap 9 10
def cycleBPerm : Equiv.Perm (Fin 21) := Equiv.swap 17 18 * Equiv.swap 18 19

theorem cycleA_isAutomorphism : graph.IsAutomorphism cycleAPerm := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

theorem cycleB_isAutomorphism : graph.IsAutomorphism cycleBPerm := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

theorem swap910_isAutomorphism : graph.IsAutomorphism (Equiv.swap 9 10) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide
theorem swap810_isAutomorphism : graph.IsAutomorphism (Equiv.swap 8 10) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide
theorem swap89_isAutomorphism : graph.IsAutomorphism (Equiv.swap 8 9) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide
theorem swap1819_isAutomorphism : graph.IsAutomorphism (Equiv.swap 18 19) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide
theorem swap1719_isAutomorphism : graph.IsAutomorphism (Equiv.swap 17 19) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide
theorem swap1718_isAutomorphism : graph.IsAutomorphism (Equiv.swap 17 18) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro atom <;> fin_cases atom <;> decide

def cycleA : graph.Aut := ⟨cycleAPerm, cycleA_isAutomorphism⟩
def cycleB : graph.Aut := ⟨cycleBPerm, cycleB_isAutomorphism⟩

/-- The bridge swap fixing a given parent bridge of the far bridgehead. -/
def otherBridgeSwap (o : Fin 21) : graph.Aut :=
  if o = 8 then ⟨Equiv.swap 9 10, swap910_isAutomorphism⟩
  else if o = 9 then ⟨Equiv.swap 8 10, swap810_isAutomorphism⟩
  else if o = 10 then ⟨Equiv.swap 8 9, swap89_isAutomorphism⟩
  else if o = 17 then ⟨Equiv.swap 18 19, swap1819_isAutomorphism⟩
  else if o = 18 then ⟨Equiv.swap 17 19, swap1719_isAutomorphism⟩
  else ⟨Equiv.swap 17 18, swap1718_isAutomorphism⟩

/-! ## The physical molecule in sorted-neighbour slots -/

noncomputable section

open LocalizedRecursiveAuxiliaryPhysicalDomain LocalizedCyclicRootPhysicalSetup
open LocalizedRecursiveAuxiliaryPhysicalInverse
open scoped Classical

abbrev decCanon : MultiCenterMolecule (Fin 21) :=
  decoratedCertified.canonicalDetectedMultiCenterMolecule

def k0 : decCanon.Center := ⟨0, (degree_four_iff 0).mpr (by decide)⟩
def k3 : decCanon.Center := ⟨3, (degree_four_iff 3).mpr (by decide)⟩
def k6 : decCanon.Center := ⟨6, (degree_four_iff 6).mpr (by decide)⟩
def k11 : decCanon.Center := ⟨11, (degree_four_iff 11).mpr (by decide)⟩
def k12 : decCanon.Center := ⟨12, (degree_four_iff 12).mpr (by decide)⟩
def k15 : decCanon.Center := ⟨15, (degree_four_iff 15).mpr (by decide)⟩
def k20 : decCanon.Center := ⟨20, (degree_four_iff 20).mpr (by decide)⟩

theorem center_cases (c : decCanon.Center) :
    c = k0 ∨ c = k3 ∨ c = k6 ∨ c = k11 ∨ c = k12 ∨ c = k15 ∨ c = k20 := by
  rcases (degree_four_iff c.1).mp c.2 with h | h | h | h | h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Or.inl (Subtype.ext h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Subtype.ext h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Subtype.ext h))))))

private theorem sorted_of_neighbors (center : Fin 21) (atoms : List (Fin 21))
    (nodup : atoms.Nodup) (pairwise : atoms.Pairwise (· ≤ ·))
    (members : ∀ atom : Fin 21, graph.Adj center atom ↔ atom ∈ atoms) :
    (graph.neighborFinset center).sort (· ≤ ·) = atoms := by
  have finsetEq : graph.neighborFinset center = atoms.toFinset := by
    ext atom
    simp only [MoleculeGraph.mem_neighborFinset, List.mem_toFinset]
    exact members atom
  rw [finsetEq]
  exact ((List.toFinset_sort (· ≤ ·) nodup).mpr pairwise)

private theorem ligand_of_sorted (center : decCanon.Center) (sorted : List (Fin 21))
    (hlist : (decoratedCertified.moleculeGraph.neighborFinset center.1).sort (· ≤ ·) = sorted)
    (hlength : sorted.length = 4) (index : Fin 4) :
    decCanon.ligandAtomAt center index = sorted.get (Fin.cast hlength.symm index) := by
  show decoratedCertified.canonicalLigandAtom center index = _
  unfold CertifiedLocalizedCIPInput.canonicalLigandAtom CertifiedLocalizedCIPInput.canonicalNeighborList
  simp [hlist]
  try rfl

private theorem sorted0 : (graph.neighborFinset 0).sort (· ≤ ·) = [1, 2, 3, 12] :=
  sorted_of_neighbors 0 _ (by decide) (by decide) (by intro a; fin_cases a <;> decide)
private theorem sorted3 : (graph.neighborFinset 3).sort (· ≤ ·) = [0, 4, 5, 6] :=
  sorted_of_neighbors 3 _ (by decide) (by decide) (by intro a; fin_cases a <;> decide)
private theorem sorted6 : (graph.neighborFinset 6).sort (· ≤ ·) = [3, 8, 9, 10] :=
  sorted_of_neighbors 6 _ (by decide) (by decide) (by intro a; fin_cases a <;> decide)
private theorem sorted11 : (graph.neighborFinset 11).sort (· ≤ ·) = [7, 8, 9, 10] :=
  sorted_of_neighbors 11 _ (by decide) (by decide) (by intro a; fin_cases a <;> decide)
private theorem sorted12 : (graph.neighborFinset 12).sort (· ≤ ·) = [0, 13, 14, 15] :=
  sorted_of_neighbors 12 _ (by decide) (by decide) (by intro a; fin_cases a <;> decide)
private theorem sorted15 : (graph.neighborFinset 15).sort (· ≤ ·) = [12, 17, 18, 19] :=
  sorted_of_neighbors 15 _ (by decide) (by decide) (by intro a; fin_cases a <;> decide)
private theorem sorted20 : (graph.neighborFinset 20).sort (· ≤ ·) = [16, 17, 18, 19] :=
  sorted_of_neighbors 20 _ (by decide) (by decide) (by intro a; fin_cases a <;> decide)

private theorem ligf (c : decCanon.Center) (sorted : List (Fin 21))
    (hlist : (decoratedCertified.moleculeGraph.neighborFinset c.1).sort (· ≤ ·) = sorted)
    (hlength : sorted.length = 4) :
    decCanon.ligandAtomAt c = fun i => sorted.get (Fin.cast hlength.symm i) :=
  funext fun i => ligand_of_sorted c sorted hlist hlength i

theorem lig0f : decCanon.ligandAtomAt k0 = ![1, 2, 3, 12] := by
  rw [ligf k0 _ sorted0 rfl]; funext i; fin_cases i <;> rfl
theorem lig3f : decCanon.ligandAtomAt k3 = ![0, 4, 5, 6] := by
  rw [ligf k3 _ sorted3 rfl]; funext i; fin_cases i <;> rfl
theorem lig6f : decCanon.ligandAtomAt k6 = ![3, 8, 9, 10] := by
  rw [ligf k6 _ sorted6 rfl]; funext i; fin_cases i <;> rfl
theorem lig11f : decCanon.ligandAtomAt k11 = ![7, 8, 9, 10] := by
  rw [ligf k11 _ sorted11 rfl]; funext i; fin_cases i <;> rfl
theorem lig12f : decCanon.ligandAtomAt k12 = ![0, 13, 14, 15] := by
  rw [ligf k12 _ sorted12 rfl]; funext i; fin_cases i <;> rfl
theorem lig15f : decCanon.ligandAtomAt k15 = ![12, 17, 18, 19] := by
  rw [ligf k15 _ sorted15 rfl]; funext i; fin_cases i <;> rfl
theorem lig20f : decCanon.ligandAtomAt k20 = ![16, 17, 18, 19] := by
  rw [ligf k20 _ sorted20 rfl]; funext i; fin_cases i <;> rfl

/-! ### Coordinates and the calibrated configuration -/

def pos (atom : Fin 21) : CartesianPoint3 := positions[atom.val]'(by simp [positions])

theorem sourcePointAt (atom : Fin 21) :
    decoratedCertified.spatialPointAt? atom = some (pos atom) := by
  rw [decoratedCertified.spatialPointAt?_eq_some_iff]
  refine ⟨⟨positions⟩, rfl, ?_⟩
  change positions[atom.val]? = some _
  exact List.getElem?_eq_getElem (by simp [positions])

/-- Oriented volume of the four ligand positions in sorted-neighbour order. -/
def ligandVolume (c : decCanon.Center) : ℚ :=
  orientedVolume (pos (decCanon.ligandAtomAt c 0)) (pos (decCanon.ligandAtomAt c 1))
    (pos (decCanon.ligandAtomAt c 2)) (pos (decCanon.ligandAtomAt c 3))

private theorem volume_of (c : decCanon.Center) (a b d e : Fin 21)
    (h : decCanon.ligandAtomAt c = ![a, b, d, e]) :
    ligandVolume c = orientedVolume (pos a) (pos b) (pos d) (pos e) := by
  simp only [ligandVolume, h]
  rfl

theorem volume_ne_zero (c : decCanon.Center) : ligandVolume c ≠ 0 := by
  rcases center_cases c with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [volume_of k0 1 2 3 12 lig0f]
    norm_num [orientedVolume, pos, positions, Q1, Q2, Q3, Q12, point]
  · rw [volume_of k3 0 4 5 6 lig3f]
    norm_num [orientedVolume, pos, positions, Q0, Q4, Q5, Q6, point]
  · rw [volume_of k6 3 8 9 10 lig6f]
    norm_num [orientedVolume, pos, positions, Q3, Q8, Q9, Q10, point]
  · rw [volume_of k11 7 8 9 10 lig11f]
    norm_num [orientedVolume, pos, positions, Q7, Q8, Q9, Q10, point]
  · rw [volume_of k12 0 13 14 15 lig12f]
    norm_num [orientedVolume, pos, positions, Q0, Q13, Q14, Q15, point]
  · rw [volume_of k15 12 17 18 19 lig15f]
    norm_num [orientedVolume, pos, positions, Q12, Q17, Q18, Q19, point]
  · rw [volume_of k20 16 17 18 19 lig20f]
    norm_num [orientedVolume, pos, positions, Q16, Q17, Q18, Q19, point]

/-- Cage A is out/out: its two bridgehead volumes have opposite signs. -/
theorem cageA_volumes : ligandVolume k6 * ligandVolume k11 < 0 := by
  rw [volume_of k6 3 8 9 10 lig6f, volume_of k11 7 8 9 10 lig11f]
  norm_num [orientedVolume, pos, positions, Q3, Q7, Q8, Q9, Q10, point]

/-- Cage B carries an inner hydrogen: its two bridgehead volumes have equal signs. -/
theorem cageB_volumes : 0 < ligandVolume k15 * ligandVolume k20 := by
  rw [volume_of k15 12 17 18 19 lig15f, volume_of k20 16 17 18 19 lig20f]
  norm_num [orientedVolume, pos, positions, Q12, Q16, Q17, Q18, Q19, point]

def decCfg : decCanon.Configuration := fun c =>
  if ligandVolume c < 0 then Equiv.swap 0 1 else 1

theorem cfgSign (c : decCanon.Center) :
    decCanon.configurationSign decCfg c = if ligandVolume c < 0 then -1 else 1 := by
  simp only [MultiCenterMolecule.configurationSign, decCfg]
  split_ifs <;> simp

private theorem sign_mul_sign {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ((if a < 0 then (-1 : ℝ) else 1) * (if b < 0 then (-1 : ℝ) else 1)) =
      if a * b < 0 then -1 else 1 := by
  rcases lt_or_gt_of_ne ha with ha' | ha' <;> rcases lt_or_gt_of_ne hb with hb' | hb'
  · have : ¬ a * b < 0 := not_lt.mpr (mul_pos_of_neg_of_neg ha' hb').le
    simp [ha', hb', this]
  · have : a * b < 0 := mul_neg_of_neg_of_pos ha' hb'
    simp [ha', not_lt.mpr hb'.le, this]
  · have : a * b < 0 := mul_neg_of_pos_of_neg ha' hb'
    simp [not_lt.mpr ha'.le, hb', this]
  · have : ¬ a * b < 0 := not_lt.mpr (mul_pos ha' hb').le
    simp [not_lt.mpr ha'.le, not_lt.mpr hb'.le, this]

/-- **The hidden parity mismatch.** -/
theorem parity_mismatch :
    decCanon.configurationSign decCfg k6 * decCanon.configurationSign decCfg k11 ≠
      decCanon.configurationSign decCfg k15 * decCanon.configurationSign decCfg k20 := by
  rw [cfgSign, cfgSign, cfgSign, cfgSign, sign_mul_sign (volume_ne_zero k6) (volume_ne_zero k11),
    sign_mul_sign (volume_ne_zero k15) (volume_ne_zero k20), if_pos cageA_volumes,
    if_neg (not_lt.mpr cageB_volumes.le)]
  norm_num

theorem canonCoordinates (c : decCanon.Center) :
    ActualPhysicalCalibratedCoordinates decoratedCertified decCanon decCfg c := by
  refine ⟨fun i => pos (decCanon.ligandAtomAt c i), fun i => sourcePointAt _,
    volume_ne_zero c, ?_⟩
  show rationalVolumeSign (ligandVolume c) = _
  rw [cfgSign]
  split_ifs with negative
  · exact rationalVolumeSign_of_neg negative
  · exact rationalVolumeSign_of_pos
      (lt_of_le_of_ne (not_lt.mp negative) (volume_ne_zero c).symm)

/-! ### No proper and no mirror transport between the two arms -/

private def graphAut (e : decCanon.Aut) : graph.Aut := ⟨e.val, e.property.1⟩

private theorem autAdj (e : decCanon.Aut) {a b : Fin 21} (h : graph.Adj a b) :
    graph.Adj (e.val a) (e.val b) :=
  (MoleculeGraph.Aut.adj_iff (m := graph) (graphAut e) a b).mpr h

private theorem autZ (e : decCanon.Aut) (atom : Fin 21) :
    graph.atomZ (e.val atom) = graph.atomZ atom :=
  MoleculeGraph.Aut.atomZ_eq (m := graph) (graphAut e) atom

/-- **Parity coupling.** A root-fixing automorphism carrying `C*A` to `C*B` carries `C1A` to `C1B`
and `C3A` to `C3B` and acts on the bridge slots of both bridgeheads by one permutation. -/
theorem arm_coupled (e : decCanon.Aut) (fixed : decCanon.centerPerm e k0 = k0)
    (moves : decCanon.ligandPermAt e k0 2 = 3) :
    decCanon.centerPerm e k6 = k15 ∧ decCanon.centerPerm e k11 = k20 ∧
      permHandedness (decCanon.ligandPermAt e k6) =
        permHandedness (decCanon.ligandPermAt e k11) := by
  have e0 : e.val 0 = 0 := congrArg Subtype.val fixed
  have transported := decCanon.ligandAtomAt_ligandPermAt (e := e) (c := k0) 2
  rw [fixed, moves, lig0f] at transported
  have e3 : e.val 3 = 12 := transported.symm
  have nb12 : ∀ x, graph.Adj 12 x → graph.atomZ x = 6 → x = 0 ∨ x = 15 := by decide
  have e6 : e.val 6 = 15 := by
    have adjacent := autAdj e (show graph.Adj 3 6 by decide)
    rw [e3] at adjacent
    rcases nb12 _ adjacent (by rw [autZ]; decide) with h | h
    · exact absurd (e.val.injective (h.trans e0.symm)) (by decide)
    · exact h
  have nb15 : ∀ x, graph.Adj 15 x → x = 12 ∨ x = 17 ∨ x = 18 ∨ x = 19 := by decide
  have nbO : ∀ o x, (o = 17 ∨ o = 18 ∨ o = 19) → graph.Adj o x → x = 15 ∨ x = 20 := by decide
  have nb20 : ∀ x, graph.Adj 20 x → graph.atomZ x = 1 → x = 16 := by decide
  have e8 : e.val 8 = 17 ∨ e.val 8 = 18 ∨ e.val 8 = 19 := by
    have adjacent := autAdj e (show graph.Adj 6 8 by decide)
    rw [e6] at adjacent
    rcases nb15 _ adjacent with h | h
    · exact absurd (e.val.injective (h.trans e3.symm)) (by decide)
    · exact h
  have e11 : e.val 11 = 20 := by
    rcases nbO _ _ e8 (autAdj e (show graph.Adj 8 11 by decide)) with h | h
    · exact absurd (e.val.injective (h.trans e6.symm)) (by decide)
    · exact h
  have e7 : e.val 7 = 16 := by
    have adjacent := autAdj e (show graph.Adj 11 7 by decide)
    rw [e11] at adjacent
    exact nb20 _ adjacent (by rw [autZ]; decide)
  have c6 : decCanon.centerPerm e k6 = k15 := Subtype.ext e6
  have c11 : decCanon.centerPerm e k11 = k20 := Subtype.ext e11
  refine ⟨c6, c11, congrArg permHandedness (Equiv.ext fun k => ?_)⟩
  have same : ∀ m : Fin 4, m ≠ 0 →
      decCanon.ligandAtomAt k20 m = decCanon.ligandAtomAt k15 m := by
    rw [lig20f, lig15f]
    decide
  apply decCanon.ligandAtomAt_injective k20
  have t6 := decCanon.ligandAtomAt_ligandPermAt (e := e) (c := k6) k
  have t11 := decCanon.ligandAtomAt_ligandPermAt (e := e) (c := k11) k
  rw [c6] at t6
  rw [c11] at t11
  rw [t11]
  have zero : decCanon.ligandPermAt e k6 0 = 0 := by
    apply decCanon.ligandAtomAt_injective k15
    have t60 := decCanon.ligandAtomAt_ligandPermAt (e := e) (c := k6) 0
    rw [c6, lig6f] at t60
    rw [t60, lig15f]
    simpa using e3
  have bridge : ∀ m : Fin 4, m ≠ 0 → decCanon.ligandPermAt e k6 m ≠ 0 := by
    intro m hm h
    apply hm
    exact (decCanon.ligandPermAt e k6).injective (h.trans zero.symm)
  by_cases hk : k = 0
  · subst hk
    rw [zero, lig20f, lig11f]
    simpa using e7.symm
  · rw [same _ (bridge k hk), t6]
    have bridges : ∀ m : Fin 4, m ≠ 0 →
        decCanon.ligandAtomAt k6 m = decCanon.ligandAtomAt k11 m := by
      rw [lig6f, lig11f]
      decide
    rw [bridges k hk]

private theorem edge36 : graph.underlyingSimpleGraph.Adj 3 6 :=
  (graph.underlyingSimpleGraph_adj 3 6).mpr (by decide)
private theorem edge68 : graph.underlyingSimpleGraph.Adj 6 8 :=
  (graph.underlyingSimpleGraph_adj 6 8).mpr (by decide)
private theorem edge811 : graph.underlyingSimpleGraph.Adj 8 11 :=
  (graph.underlyingSimpleGraph_adj 8 11).mpr (by decide)

private theorem reach6 : LigandBranchReaches decCanon k0 2 k6.1 := by
  unfold LigandBranchReaches
  rw [lig0f]
  refine ⟨SimpleGraph.Walk.cons edge36 SimpleGraph.Walk.nil, ?_⟩
  simp [k0, k6]

private theorem reach11 : LigandBranchReaches decCanon k0 2 k11.1 := by
  unfold LigandBranchReaches
  rw [lig0f]
  refine ⟨SimpleGraph.Walk.cons edge36
    (SimpleGraph.Walk.cons edge68 (SimpleGraph.Walk.cons edge811 SimpleGraph.Walk.nil)), ?_⟩
  simp [k0, k11]

theorem arms_noTransport (mirror : Bool) : ¬ BranchTransport decCanon decCfg k0 2 3 mirror :=
  not_branchTransport_of_parityCoupling decCanon decCfg k0 2 3 k6 k11 k15 k20 reach6 reach11
    arm_coupled parity_mismatch mirror

private theorem transportZ {i j : Fin 4} {mirror : Bool}
    (transport : BranchTransport decCanon decCfg k0 i j mirror) :
    graph.atomZ (decCanon.ligandAtomAt k0 j) = graph.atomZ (decCanon.ligandAtomAt k0 i) := by
  obtain ⟨e, fixed, sent, _⟩ := transport
  have action := decCanon.ligandAtomAt_ligandPermAt (e := e) (c := k0) i
  rw [fixed, sent] at action
  rw [action]
  exact autZ e _

private theorem rootZ_tie (i j : Fin 4)
    (tie : graph.atomZ (decCanon.ligandAtomAt k0 j) = graph.atomZ (decCanon.ligandAtomAt k0 i)) :
    i = j ∨ (i = 2 ∧ j = 3) ∨ (i = 3 ∧ j = 2) := by
  rw [lig0f] at tie
  revert tie
  revert i j
  decide

/-- No two distinct root branches are related by any branch transport. -/
theorem root_noTransport (i j : Fin 4) (mirror : Bool) (distinct : i ≠ j) :
    ¬ BranchTransport decCanon decCfg k0 i j mirror := by
  intro transport
  rcases rootZ_tie i j (transportZ transport) with same | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact distinct same
  · exact arms_noTransport mirror transport
  · exact arms_noTransport mirror (branchTransport_inverse decCanon decCfg k0 transport)

/-! ### The detected molecule -/

private theorem calibratedCoordinates_reindexFrames
    {input : CertifiedLocalizedCIPInput} {m : MultiCenterMolecule input.Atom}
    {cfg : m.Configuration} (tau : m.Center → Equiv.Perm (Fin 4)) (center : m.Center)
    (coordinates : ActualPhysicalCalibratedCoordinates input m cfg center) :
    ActualPhysicalCalibratedCoordinates input (m.reindexFrames tau)
      (m.reindexConfiguration tau cfg) center := by
  obtain ⟨pointAt, observed, nonzero, sign⟩ := coordinates
  refine ⟨fun i => pointAt (tau center i), ?_, ?_, ?_⟩
  · intro i
    rw [MultiCenterMolecule.reindexFrames_ligandAtomAt]
    exact observed (tau center i)
  · exact cartesianOrientedVolume_perm_ne_zero pointAt (tau center) nonzero
  · have hvec : ∀ k : Fin 4,
        RationalTetrahedralPermutation.pointVector
          (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) k = pointAt k := by
      intro k
      fin_cases k <;> rfl
    have hperm : RationalTetrahedralPermutation.permutedOrientedVolume
          (pointAt 0) (pointAt 1) (pointAt 2) (pointAt 3) (tau center) =
        CartesianPoint3.orientedVolume
          (pointAt (tau center 0)) (pointAt (tau center 1))
            (pointAt (tau center 2)) (pointAt (tau center 3)) := by
      simp only [RationalTetrahedralPermutation.permutedOrientedVolume, hvec]
    rw [← hperm, rationalVolumeSign_permutedOrientedVolume, sign,
      MultiCenterMolecule.configurationSign_reindexConfiguration]

private theorem calibratedCoordinates_congr
    {input : CertifiedLocalizedCIPInput} {m n : MultiCenterMolecule input.Atom}
    (h : m = n) (cfg : m.Configuration) (center : m.Center)
    (coordinates : ActualPhysicalCalibratedCoordinates input m cfg center) :
    ActualPhysicalCalibratedCoordinates input n
      (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) center) := by
  cases h
  exact coordinates

private theorem branchTransport_congr {m n : MultiCenterMolecule (Fin 21)} (h : m = n)
    (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) (mirror : Bool)
    (transport : BranchTransport m cfg c i j mirror) :
    BranchTransport n (Eq.mp (congrArg MultiCenterMolecule.Configuration h) cfg)
      (Eq.mp (congrArg MultiCenterMolecule.Center h) c) i j mirror := by
  cases h
  exact transport

theorem decFrameReindex :
    ∃ tau : decCanon.Center → Equiv.Perm (Fin 4),
      decCanon.reindexFrames tau = decoratedCertified.detectedMultiCenterMolecule := by
  apply decoratedCertified.exists_reindexFrames_detectedMultiCenterMolecule (m := decCanon)
  · rfl
  · rfl

def decTau : decCanon.Center → Equiv.Perm (Fin 4) := Classical.choose decFrameReindex

theorem decTau_spec :
    decCanon.reindexFrames decTau = decoratedCertified.detectedMultiCenterMolecule :=
  Classical.choose_spec decFrameReindex

/-- The calibrated configuration in the detected ligand enumeration. -/
def detectedCfg : decoratedCertified.detectedMultiCenterMolecule.Configuration :=
  Eq.mp (congrArg MultiCenterMolecule.Configuration decTau_spec)
    (decCanon.reindexConfiguration decTau decCfg)

theorem detectedCoordinates (center : decoratedCertified.detectedMultiCenterMolecule.Center) :
    ActualPhysicalCalibratedCoordinates decoratedCertified
      decoratedCertified.detectedMultiCenterMolecule detectedCfg center := by
  let center' : (decCanon.reindexFrames decTau).Center :=
    Eq.mp (congrArg MultiCenterMolecule.Center decTau_spec.symm) center
  have coordinates' := calibratedCoordinates_reindexFrames
    (input := decoratedCertified) (m := decCanon) (cfg := decCfg) decTau center'
    (canonCoordinates center')
  simpa [detectedCfg] using
    calibratedCoordinates_congr (input := decoratedCertified)
      (m := decCanon.reindexFrames decTau)
      (n := decoratedCertified.detectedMultiCenterMolecule) decTau_spec
      (decCanon.reindexConfiguration decTau decCfg) center' coordinates'

def decRoot : decoratedCertified.TetrahedralCenter :=
  ⟨(0 : Fin 21), (degree_four_iff 0).mpr (by decide)⟩

theorem detectedDomain :
    RecursiveAuxiliaryPhysicalDomain decoratedCertified detectedCfg decRoot :=
  ⟨fun center _ => Or.inr (detectedCoordinates center)⟩

theorem detectedGeometry : RootPhysicalGeometry decoratedCertified
    decoratedCertified.detectedMultiCenterMolecule detectedCfg decRoot := by
  obtain ⟨pointAt, observed, nonzero, sign⟩ := detectedCoordinates decRoot
  exact ⟨pointAt, observed, nonzero, sign⟩

/-- **No branch transport at the root of the detected molecule.** -/
theorem detected_noTransport (i j : Fin 4) (mirror : Bool) (distinct : i ≠ j) :
    ¬ BranchTransport decoratedCertified.detectedMultiCenterMolecule detectedCfg decRoot i j
      mirror := by
  intro transport
  have back := branchTransport_congr decTau_spec.symm detectedCfg decRoot i j mirror transport
  have back' : BranchTransport (decCanon.reindexFrames decTau)
      (decCanon.reindexConfiguration decTau decCfg) decRoot i j mirror := by
    simpa [detectedCfg] using back
  have reindexed : BranchTransport (decCanon.reindexFrames decTau)
      (decCanon.reindexConfiguration decTau decCfg) k0 i j mirror := back'
  have canonical := (MultiCenterMolecule.branchTransport_reindexFrames_iff decCanon decTau
    decCfg k0 i j mirror).1 reindexed
  exact root_noTransport _ _ mirror (fun same => distinct ((decTau k0).injective same)) canonical

theorem detectedPairwise : MultiCenterMolecule.PairwiseProperDistinguishable
    decoratedCertified.detectedMultiCenterMolecule detectedCfg decRoot :=
  fun i j distinct => detected_noTransport i j false distinct

/-- **The physical root has no enantiomorphic pair.** -/
theorem detectedPairCount : physicalEnantiomorphicPairCount
    decoratedCertified.detectedMultiCenterMolecule detectedCfg decRoot = 0 := by
  have noPair : ∀ i j : Fin 4,
      ¬ Enantiomorphic decoratedCertified.detectedMultiCenterMolecule detectedCfg decRoot i j :=
    fun i j pair => detected_noTransport i j true pair.1 pair.2.1
  simp [physicalEnantiomorphicPairCount, sourceEnantiomorphicPairCount, noPair]

/-! ## The mirror sign law at a reflected centre -/

def reflectX (p : CartesianPoint3) : CartesianPoint3 := point (-p.x) p.y p.z

theorem orientedVolume_reflectX (a b c d : CartesianPoint3) :
    orientedVolume (reflectX a) (reflectX b) (reflectX c) (reflectX d) =
      - orientedVolume a b c d := by
  simp only [orientedVolume, reflectX, point]
  ring

theorem rationalVolumeSign_neg (v : ℚ) : rationalVolumeSign (-v) = - rationalVolumeSign v := by
  unfold rationalVolumeSign
  rcases lt_trichotomy v 0 with h | h | h
  · have h1 : ¬ (-v < 0) := by linarith
    have h2 : 0 < -v := by linarith
    rw [if_neg h1, if_pos h2, if_pos h]
    norm_num
  · subst h
    norm_num
  · have h1 : -v < 0 := by linarith
    have h2 : ¬ v < 0 := by linarith
    rw [if_pos h1, if_neg h2, if_pos h]

/-- **Mirror law from reflected ligand positions.** If an automorphism sends every ligand of `d`
to an atom whose position is the reflection of that ligand's position, the calibrated detected
configuration obeys the mirror sign law at `d`, in whatever ligand enumeration. -/
theorem mirrorLaw_of_reflection (e : graph.Aut)
    (d : decoratedCertified.detectedMultiCenterMolecule.Center)
    (reflect : ∀ i, pos ((e : Equiv.Perm (Fin 21))
        (decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt d i)) =
      reflectX (pos (decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt d i))) :
    decoratedCertified.detectedMultiCenterMolecule.configurationSign detectedCfg d *
        permHandedness (decoratedCertified.detectedMultiCenterMolecule.ligandPermAt
          (decoratedCertified.physicalDetectedAut e) d) =
      CertifiedLocalizedCIPInput.physicalMirrorFactor true *
        decoratedCertified.detectedMultiCenterMolecule.configurationSign detectedCfg
          (decoratedCertified.detectedMultiCenterMolecule.centerPerm
            (decoratedCertified.physicalDetectedAut e) d) := by
  let m := decoratedCertified.detectedMultiCenterMolecule
  let E := decoratedCertified.physicalDetectedAut e
  obtain ⟨p, observed, _nonzero, sign⟩ := detectedCoordinates d
  obtain ⟨q, observed', _nonzero', sign'⟩ := detectedCoordinates (m.centerPerm E d)
  have hp : ∀ i, p i = pos (m.ligandAtomAt d i) := fun i =>
    Option.some.inj ((observed i).symm.trans (sourcePointAt _))
  have hq : ∀ k, q k = pos (m.ligandAtomAt (m.centerPerm E d) k) := fun k =>
    Option.some.inj ((observed' k).symm.trans (sourcePointAt _))
  let π := m.ligandPermAt E d
  have act : ∀ i, m.ligandAtomAt (m.centerPerm E d) (π i) =
      (e : Equiv.Perm (Fin 21)) (m.ligandAtomAt d i) := fun i =>
    m.ligandAtomAt_ligandPermAt (e := E) (c := d) i
  have hvec : ∀ k : Fin 4,
      RationalTetrahedralPermutation.pointVector (q 0) (q 1) (q 2) (q 3) k = q k := by
    intro k
    fin_cases k <;> rfl
  have hperm : RationalTetrahedralPermutation.permutedOrientedVolume (q 0) (q 1) (q 2) (q 3) π =
      orientedVolume (q (π 0)) (q (π 1)) (q (π 2)) (q (π 3)) := by
    simp only [RationalTetrahedralPermutation.permutedOrientedVolume, hvec]
  have permuted := rationalVolumeSign_permutedOrientedVolume (q 0) (q 1) (q 2) (q 3) π
  rw [hperm] at permuted
  have image : orientedVolume (q (π 0)) (q (π 1)) (q (π 2)) (q (π 3)) =
      - orientedVolume (p 0) (p 1) (p 2) (p 3) := by
    rw [hq, hq, hq, hq, act, act, act, act, reflect, reflect, reflect, reflect, hp, hp, hp, hp]
    exact orientedVolume_reflectX _ _ _ _
  rw [image, rationalVolumeSign_neg, sign, sign'] at permuted
  have hh := permHandedness_mul_self π
  change m.configurationSign detectedCfg d * permHandedness π =
    (-1) * m.configurationSign detectedCfg (m.centerPerm E d)
  have key : m.configurationSign detectedCfg d =
      -(m.configurationSign detectedCfg (m.centerPerm E d) * permHandedness π) := by
    rw [← permuted]
    ring
  rw [key]
  calc -(m.configurationSign detectedCfg (m.centerPerm E d) * permHandedness π) *
        permHandedness π
      = -(m.configurationSign detectedCfg (m.centerPerm E d) *
          (permHandedness π * permHandedness π)) := by ring
    _ = (-1) * m.configurationSign detectedCfg (m.centerPerm E d) := by rw [hh]; ring

/-! ## The actual evaluator frame -/

open LocalizedRuleMajorReference DeclarativeCIP
open LocalizedRecursiveAuxiliaryPhysicalTransport LocalizedRecursiveAuxiliaryPhysicalCorrectness
open LocalizedCyclicMatchedReadingPhysicalTransport LocalizedRecursiveAuxiliaryParityEvidence

abbrev decReference : LocalizedRuleMajorReference.Input where
  certified := decoratedCertified

abbrev decFrames := finalRootFrames decReference simple_bonded decRoot

abbrev decTarget : LocalizedRuleMajorReference.Occurrence decReference :=
  decoratedCertified.localizedFinalOccurrenceExecutable (carrierFuel decReference) decRoot

theorem decCenter : decFrames.center = decRoot :=
  finalRootFrames_center decReference simple_bonded decRoot

theorem decAddress : decTarget.1.address = [] :=
  decoratedCertified.localizedFinalOccurrenceExecutable_address (carrierFuel decReference) decRoot

theorem decReal : decTarget.1.node.provenance = OfficialCIPNodeProvenance.realAtom :=
  finalOccurrence_provenance_real decReference decRoot

theorem decHistory : decTarget.1.node.history = ([0] : List (Fin 21)) := by
  have facts := (rootFrame_target_facts decFrames decAddress decReal).2.1
  refine facts.trans ?_
  rw [decCenter]
  rfl

theorem dec_slot (a : Fin 21) (adjacent : graph.Adj 0 a) :
    ∃ s : Fin 4, decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
      (decFrames.detectedLigandPermutation s) = a := by
  have adjacentCenter : graph.Adj decFrames.center.1 a := by
    rw [decCenter]
    exact adjacent
  obtain ⟨k, hk⟩ := decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt_surjective
    decFrames.center a adjacentCenter
  exact ⟨decFrames.detectedLigandPermutation.symm k, by rw [Equiv.apply_symm_apply]; exact hk⟩

def slotA : Fin 4 := Classical.choose (dec_slot 3 (by decide))
def slotB : Fin 4 := Classical.choose (dec_slot 12 (by decide))

theorem slotA_spec : decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
    (decFrames.detectedLigandPermutation slotA) = (3 : Fin 21) :=
  Classical.choose_spec (dec_slot 3 (by decide))

theorem slotB_spec : decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
    (decFrames.detectedLigandPermutation slotB) = (12 : Fin 21) :=
  Classical.choose_spec (dec_slot 12 (by decide))

theorem slots_ne : slotA ≠ slotB := by
  intro same
  have atoms := slotA_spec
  rw [same, slotB_spec] at atoms
  exact absurd atoms (by decide)

theorem armSwap_root :
    (armSwap : Equiv.Perm (Fin 21)) decFrames.center.1 = decFrames.center.1 := by
  rw [decCenter]
  decide

theorem armSwap_AB : (armSwap : Equiv.Perm (Fin 21))
      (decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
        (decFrames.detectedLigandPermutation slotA)) =
    decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
      (decFrames.detectedLigandPermutation slotB) := by
  rw [slotA_spec, slotB_spec]
  decide

/-! ## Reader-free refusal witnesses at the decorated histories -/

private theorem detected_center_mem (d : decoratedCertified.detectedMultiCenterMolecule.Center) :
    d.1 ∈ graph.tetrahedralCenterSet := d.2

/-- Bridge 3-cycle at an attachment bridgehead with any fixed history. -/
theorem cycleWitness (σ : graph.Aut) (c1 c3 s t : Fin 21) (history inner : List (Fin 21))
    (basics : s ≠ t ∧ graph.Adj c1 s ∧ graph.Adj c1 t ∧ s ∉ history ∧ t ∉ history ∧
      (∀ x ∈ history, (σ : Equiv.Perm (Fin 21)) x = x) ∧ (σ : Equiv.Perm (Fin 21)) s = t)
    (closed : ∀ a b, a ∈ inner → a ∉ history → b ∉ history → graph.Adj a b → b ∈ inner)
    (start : s ∈ inner)
    (centers : ∀ x ∈ inner, x ∈ graph.tetrahedralCenterSet → x = c3)
    (fixes : (σ : Equiv.Perm (Fin 21)) c3 = c3)
    (cube : (σ : Equiv.Perm (Fin 21)) * σ * σ = 1) :
    HistoryRefusalWitness decReference detectedCfg history c1 := by
  obtain ⟨st, adjS, adjT, freshS, freshT, fixedHistory, sent⟩ := basics
  refine ⟨σ, s, t, st, adjS, adjT, freshS, freshT, fixedHistory, sent, ?_⟩
  intro d component
  have member := inComponent_closed graph history (fun x => x ∈ inner) closed component start
  have dEq : d.1 = c3 := centers _ member (detected_center_mem d)
  have fixedE : decReference.certified.detectedMultiCenterMolecule.centerPerm
      (decReference.certified.physicalDetectedAut σ) d = d := by
    apply Subtype.ext
    show (σ : Equiv.Perm (Fin 21)) d.1 = d.1
    rw [dEq]
    exact fixes
  have cubeE : decReference.certified.physicalDetectedAut σ *
      decReference.certified.physicalDetectedAut σ *
      decReference.certified.physicalDetectedAut σ = 1 := Subtype.ext cube
  rw [fixedE, handedness_of_cube _ _ d fixedE cubeE, mul_one]

/-- Bridge swap at a far bridgehead with any fixed history. -/
theorem swapWitness (σ : graph.Aut) (c3 s t : Fin 21) (history : List (Fin 21))
    (basics : s ≠ t ∧ graph.Adj c3 s ∧ graph.Adj c3 t ∧ s ∉ history ∧
      t ∉ history ∧ (∀ x ∈ history, (σ : Equiv.Perm (Fin 21)) x = x) ∧
      (σ : Equiv.Perm (Fin 21)) s = t)
    (isolated : ∀ b, b ∉ history → graph.Adj s b → False)
    (notCenter : s ∉ graph.tetrahedralCenterSet) :
    HistoryRefusalWitness decReference detectedCfg history c3 := by
  obtain ⟨st, adjS, adjT, freshS, freshT, fixedHistory, sent⟩ := basics
  refine ⟨σ, s, t, st, adjS, adjT, freshS, freshT, fixedHistory, sent, ?_⟩
  intro d component
  have member := inComponent_closed graph history (fun x => x = s)
    (fun a b ha _ hb adjacent => (isolated b hb (ha ▸ adjacent)).elim) component rfl
  exact absurd (member ▸ detected_center_mem d) notCenter

theorem cycleWitnessA :
    HistoryRefusalWitness decReference detectedCfg ([6, 3, 0] : List (Fin 21)) (6 : Fin 21) :=
  cycleWitness cycleA 6 11 8 9 [6, 3, 0] [7, 8, 9, 10, 11] (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

theorem cycleWitnessB :
    HistoryRefusalWitness decReference detectedCfg ([15, 12, 0] : List (Fin 21)) (15 : Fin 21) :=
  cycleWitness cycleB 15 20 17 18 [15, 12, 0] [16, 17, 18, 19, 20] (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)

theorem swapWitnessA (o : Fin 21) (ho : o ∈ [8, 9, 10]) :
    HistoryRefusalWitness decReference detectedCfg ([11, o, 6, 3, 0] : List (Fin 21))
      (11 : Fin 21) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact swapWitness (otherBridgeSwap 8) 11 9 10 _ (by decide) (by decide) (by decide)
  · exact swapWitness (otherBridgeSwap 9) 11 8 10 _ (by decide) (by decide) (by decide)
  · exact swapWitness (otherBridgeSwap 10) 11 8 9 _ (by decide) (by decide) (by decide)

theorem swapWitnessB (o : Fin 21) (ho : o ∈ [17, 18, 19]) :
    HistoryRefusalWitness decReference detectedCfg ([20, o, 15, 12, 0] : List (Fin 21))
      (20 : Fin 21) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact swapWitness (otherBridgeSwap 17) 20 18 19 _ (by decide) (by decide) (by decide)
  · exact swapWitness (otherBridgeSwap 18) 20 17 19 _ (by decide) (by decide) (by decide)
  · exact swapWitness (otherBridgeSwap 19) 20 17 18 _ (by decide) (by decide) (by decide)

/-! ## Simple histories through the decorated arm -/

/-- A simple chain that starts in a set `S` closed except through `p`, and ends at `p ∉ S`,
enters `p` from its unique `S`-neighbour `q`. -/
theorem stem_split {V : Type*} {adj : V → V → Prop} (S : V → Prop) (p q : V)
    (closed : ∀ a b, S a → adj a b → S b ∨ b = p) (outside : ¬ S p)
    (gate : ∀ x, S x → adj x p → x = q) :
    ∀ (l : List V) (h : V), l.Nodup → l.IsChain adj → l.head? = some h → S h →
      l.getLast? = some p → ∃ l' : List V, l = l' ++ [p] ∧ l'.Nodup ∧ l'.IsChain adj ∧
        l'.head? = some h ∧ l'.getLast? = some q := by
  intro l
  induction l with
  | nil => intro h _ _ head; simp at head
  | cons a rest ih =>
      intro h nodup chain head sh last
      simp only [List.head?_cons, Option.some.injEq] at head
      subst head
      cases rest with
      | nil =>
          simp only [List.getLast?_singleton, Option.some.injEq] at last
          subst last
          exact absurd sh outside
      | cons b t =>
          have hab := (List.isChain_cons_cons.1 chain).1
          have chainTail := (List.isChain_cons_cons.1 chain).2
          have nodupTail := (List.nodup_cons.1 nodup).2
          have aFresh := (List.nodup_cons.1 nodup).1
          rw [List.getLast?_cons_cons] at last
          rcases closed a b sh hab with sb | bp
          · obtain ⟨l', eq, nd, ch, hd, lst⟩ := ih b nodupTail chainTail rfl sb last
            cases l' with
            | nil => simp at hd
            | cons b' rest' =>
                simp only [List.head?_cons, Option.some.injEq] at hd
                subst hd
                refine ⟨a :: b' :: rest', by rw [eq]; rfl, ?_, ?_, rfl, ?_⟩
                · refine List.nodup_cons.2 ⟨fun member => aFresh ?_, nd⟩
                  rw [eq]
                  exact List.mem_append_left _ member
                · exact List.isChain_cons_cons.2 ⟨hab, ch⟩
                · rw [List.getLast?_cons_cons]
                  exact lst
          · subst bp
            cases t with
            | nil =>
                refine ⟨[a], rfl, by simp, List.isChain_singleton _, rfl, ?_⟩
                simp [gate a sh hab]
            | cons y t' =>
                exfalso
                have member : b ∈ y :: t' := by
                  rw [List.getLast?_cons_cons] at last
                  exact List.mem_of_getLast? last
                exact (List.nodup_cons.1 nodupTail).1 member

def armA : List (Fin 21) := [3, 4, 5, 6, 7, 8, 9, 10, 11]

theorem cageA' : Cage graph.Adj 3 6 11 7 [8, 9, 10] :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩

private theorem armA_closed : ∀ a b : Fin 21, a ∈ armA → graph.Adj a b → b ∈ armA ∨ b = 0 := by
  decide

private theorem armA_gate : ∀ x : Fin 21, x ∈ armA → graph.Adj x 0 → x = 3 := by
  decide

theorem history_c1A {l : List (Fin 21)} (nodup : l.Nodup) (chain : l.IsChain graph.Adj)
    (head : l.head? = some 6) (last : l.getLast? = some 0) : l = [6, 3, 0] := by
  obtain ⟨l', rfl, nd, ch, hd, lst⟩ := stem_split (fun x => x ∈ armA) 0 3 armA_closed
    (by decide) armA_gate l 6 nodup chain head (by decide) last
  rw [cageA'.history_c1 nd ch hd lst]
  rfl

theorem history_c3A {l : List (Fin 21)} (nodup : l.Nodup) (chain : l.IsChain graph.Adj)
    (head : l.head? = some 11) (last : l.getLast? = some 0) :
    ∃ o ∈ ([8, 9, 10] : List (Fin 21)), l = [11, o, 6, 3, 0] := by
  obtain ⟨l', rfl, nd, ch, hd, lst⟩ := stem_split (fun x => x ∈ armA) 0 3 armA_closed
    (by decide) armA_gate l 11 nodup chain head (by decide) last
  obtain ⟨o, ho, eq⟩ := cageA'.history_c3 nd ch hd lst
  exact ⟨o, ho, by rw [eq]; rfl⟩

/-! ## The blind mirror law of the arm swap -/

private theorem getLast?_append_of {α : Type*} (l m : List α) {a : α}
    (h : m.getLast? = some a) : (l ++ m).getLast? = some a := by
  simp [List.getLast?_append, h]

private theorem armSwap_reflects_at3 (a : Fin 21) (adjacent : graph.Adj 3 a) :
    pos ((armSwap : Equiv.Perm (Fin 21)) a) = reflectX (pos a) := by
  have cases : a = 0 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by revert a; decide
  rcases cases with rfl | rfl | rfl | rfl <;>
    simp [armSwap, armSwapPerm, armSwapFun, pos, positions, reflectX, point, Q0, Q4, Q5, Q6,
      Q13, Q14, Q15]

/-- **The arm swap is a blind mirror transport.** At the stereocentre `C*A` it obeys the mirror
sign law; at both cage bridgeheads of arm A, and at their images in arm B, the accepted reader-free
refusal witnesses hold. No reader agreement, label, order or output is assumed. -/
theorem blindMirror : BlindSignLaw decFrames slotA simple_bonded armSwap detectedCfg true := by
  rintro z ⟨cursor, cursorEq, reachable⟩ real d current
  have outwardA : IsLocalizedActualFrameOutwardCursor decoratedCertified decTarget
      (decFrames.frame.cursorAt slotA) :=
    ⟨_, (rootFramePair decFrames decAddress slotA slotA).leftAddress⟩
  obtain ⟨extra, _extraNe, history, located⟩ :=
    reached_history_inComponent simple_bonded decFrames decReal outwardA cursor reachable
  rw [cursorEq] at history located
  obtain ⟨atom, current', component⟩ := located real
  have atomEq : atom = d.1 := Option.some.inj (current'.symm.trans current)
  subst atomEq
  change RetainedCoherentSymmetry.InComponent graph decTarget.1.node.history
    (decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt decFrames.center
      (decFrames.detectedLigandPermutation slotA)) d.1 at component
  rw [slotA_spec, decHistory] at component
  have member := inComponent_closed graph [0] (fun x => x ∈ armA)
    (by decide) component (by decide)
  have facts := LocalizedActualBoundaryObservationReadback.occurrence_history_facts
    decoratedCertified z real
  have head : z.1.node.history.head? = some d.1 := facts.2.symm.trans current
  have chain : z.1.node.history.IsChain graph.Adj :=
    decoratedCertified.declarativeLocalizedOccurrence_node_history_chain
      ((decoratedCertified.mem_localizedOccurrences_iff _ z.1).mp z.2)
  have rootLast : decTarget.1.node.history.getLast? = some (0 : Fin 21) := by
    rw [decHistory]
    rfl
  have last : z.1.node.history.getLast? = some (0 : Fin 21) := by
    rw [history]
    exact getLast?_append_of extra _ rootLast
  have centersA : ∀ x ∈ armA, x ∈ graph.tetrahedralCenterSet → x = 3 ∨ x = 6 ∨ x = 11 := by
    decide
  rcases centersA d.1 member (detected_center_mem d) with h3 | h6 | h11
  · left
    apply mirrorLaw_of_reflection armSwap d
    intro i
    apply armSwap_reflects_at3
    have adjacent := decoratedCertified.detectedMultiCenterMolecule.ligandAtomAt_adj d i
    rw [h3] at adjacent
    exact adjacent
  · right
    have hist := history_c1A facts.1 chain (h6 ▸ head) last
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have aEq : a = (6 : Fin 21) := Option.some.inj (ha.symm.trans (current.trans (by rw [h6])))
      subst aEq
      rw [hist]
      exact cycleWitnessA
    · have ha' : z.1.node.current?.map (armSwap : Equiv.Perm (Fin 21)) = some a := ha
      rw [current, Option.map_some, Option.some.injEq, h6] at ha'
      subst ha'
      show HistoryRefusalWitness decReference detectedCfg
        (z.1.node.history.map (armSwap : Equiv.Perm (Fin 21))) ((armSwap : Equiv.Perm (Fin 21)) 6)
      have e1 : ([6, 3, 0] : List (Fin 21)).map (armSwap : Equiv.Perm (Fin 21)) = [15, 12, 0] := by
        decide
      have e2 : (armSwap : Equiv.Perm (Fin 21)) 6 = 15 := by decide
      rw [hist, e1, e2]
      exact cycleWitnessB
  · right
    obtain ⟨o, ho, hist⟩ := history_c3A facts.1 chain (h11 ▸ head) last
    refine ⟨fun a ha => ?_, fun a ha => ?_⟩
    · have aEq : a = (11 : Fin 21) :=
        Option.some.inj (ha.symm.trans (current.trans (by rw [h11])))
      subst aEq
      rw [hist]
      exact swapWitnessA o ho
    · have ha' : z.1.node.current?.map (armSwap : Equiv.Perm (Fin 21)) = some a := ha
      rw [current, Option.map_some, Option.some.injEq, h11] at ha'
      subst ha'
      show HistoryRefusalWitness decReference detectedCfg
        (z.1.node.history.map (armSwap : Equiv.Perm (Fin 21))) ((armSwap : Equiv.Perm (Fin 21)) 11)
      have e2 : (armSwap : Equiv.Perm (Fin 21)) 11 = 20 := by decide
      rw [hist, e2]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with rfl | rfl | rfl
      · have e1 : ([11, 8, 6, 3, 0] : List (Fin 21)).map (armSwap : Equiv.Perm (Fin 21)) =
            [20, 17, 15, 12, 0] := by decide
        rw [e1]
        exact swapWitnessB 17 (by decide)
      · have e1 : ([11, 9, 6, 3, 0] : List (Fin 21)).map (armSwap : Equiv.Perm (Fin 21)) =
            [20, 18, 15, 12, 0] := by decide
        rw [e1]
        exact swapWitnessB 18 (by decide)
      · have e1 : ([11, 10, 6, 3, 0] : List (Fin 21)).map (armSwap : Equiv.Perm (Fin 21)) =
            [20, 19, 15, 12, 0] := by decide
        rw [e1]
        exact swapWitnessB 19 (by decide)

end

end TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration

assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration.simple_bonded
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration.arm_coupled
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration.parity_mismatch
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration.detected_noTransport
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration.detectedDomain
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration.detectedPairwise
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration.detectedPairCount
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration.mirrorLaw_of_reflection
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration.stem_split
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration.history_c3A
assert_kernel_only TetraStereo.OneCenter.LocalizedRecursiveAuxiliaryParityDecoration.blindMirror
