import TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Input
import TetraStereo.OneCenter.LocalizedRetainedCoherentSymmetry
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-! Physical branch distinctions on the actual double-C3 graph. The canonical frames use
the detected degree-four inventory; configurations are explicit. No evaluator output is
assumed. Threefold rotations are even at either cage, including maps between the cages.
This is a graph/configuration result; coordinate calibration and runtime results are separate. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical

open LocalizedChemicalRingDoubleC3Input
open LocalizedActualPhysicalBranchDecision RootedTetrahedralBranchSymmetry
open RetainedCoherentSymmetry

abbrev canon := actualCanonicalMolecule (certified false)

def center0 : canon.Center := ⟨(0 : Fin 25), by change (0 : Fin 25) ∈ graph.tetrahedralCenterSet; rw [detected_inventory]; decide⟩
def centerL : canon.Center := ⟨(3 : Fin 25), by change (3 : Fin 25) ∈ graph.tetrahedralCenterSet; rw [detected_inventory]; decide⟩
def centerR : canon.Center := ⟨(14 : Fin 25), by change (14 : Fin 25) ∈ graph.tetrahedralCenterSet; rw [detected_inventory]; decide⟩

theorem center_cases (c : canon.Center) : c = center0 ∨ c = centerL ∨ c = centerR := by
  have member : c.1 ∈ graph.tetrahedralCenterSet := c.2
  rw [detected_inventory] at member
  simp only [Finset.mem_insert, Finset.mem_singleton] at member
  rcases member with h | h | h
  · exact Or.inl (Subtype.ext h)
  · exact Or.inr (Or.inl (Subtype.ext h))
  · exact Or.inr (Or.inr (Subtype.ext h))

def frame0 : Fin 4 → Fin 25 := ![1, 2, 4, 15]
def frameL : Fin 4 → Fin 25 := ![4, 5, 6, 7]
def frameR : Fin 4 → Fin 25 := ![15, 16, 17, 18]

private theorem sorted0 : (graph.neighborFinset 0).sort (· ≤ ·) = [1, 2, 4, 15] := by
  have h : graph.neighborFinset 0 = ([1, 2, 4, 15] : List (Fin 25)).toFinset := by
    ext a
    fin_cases a <;> decide +kernel
  rw [h]
  exact (List.toFinset_sort (· ≤ ·) (by decide)).mpr (by decide)

private theorem sortedL : (graph.neighborFinset 3).sort (· ≤ ·) = [4, 5, 6, 7] := by
  have h : graph.neighborFinset 3 = ([4, 5, 6, 7] : List (Fin 25)).toFinset := by
    ext a
    fin_cases a <;> decide +kernel
  rw [h]
  exact (List.toFinset_sort (· ≤ ·) (by decide)).mpr (by decide)

private theorem sortedR : (graph.neighborFinset 14).sort (· ≤ ·) = [15, 16, 17, 18] := by
  have h : graph.neighborFinset 14 = ([15, 16, 17, 18] : List (Fin 25)).toFinset := by
    ext a
    fin_cases a <;> decide +kernel
  rw [h]
  exact (List.toFinset_sort (· ≤ ·) (by decide)).mpr (by decide)

private theorem ligand_of_sorted (c : canon.Center) (sorted : List (Fin 25))
    (ordered : ((certified false).moleculeGraph.neighborFinset c.1).sort (· ≤ ·) = sorted)
    (length : sorted.length = 4) (i : Fin 4) :
    canon.ligandAtomAt c i = sorted.get (Fin.cast length.symm i) := by
  unfold canon actualCanonicalMolecule MultiCenterMolecule.ligandAtomAt
    CertifiedLocalizedCIPInput.canonicalLigandAtom CertifiedLocalizedCIPInput.canonicalNeighborList
  simp [ordered]
  rfl

theorem ligands0 (i : Fin 4) : canon.ligandAtomAt center0 i = frame0 i := by
  have h := ligand_of_sorted center0 [1, 2, 4, 15] sorted0 rfl i
  fin_cases i <;> simpa [frame0] using h

theorem ligandsL (i : Fin 4) : canon.ligandAtomAt centerL i = frameL i := by
  have h := ligand_of_sorted centerL [4, 5, 6, 7] sortedL rfl i
  fin_cases i <;> simpa [frameL] using h

theorem ligandsR (i : Fin 4) : canon.ligandAtomAt centerR i = frameR i := by
  have h := ligand_of_sorted centerR [15, 16, 17, 18] sortedR rfl i
  fin_cases i <;> simpa [frameR] using h

def leftRotationFun (a : Fin 25) : Fin 25 :=
  if a = 5 then 6 else if a = 6 then 7 else if a = 7 then 5 else
  if a = 8 then 9 else if a = 9 then 10 else if a = 10 then 8 else
  if a = 11 then 12 else if a = 12 then 13 else if a = 13 then 11 else a

def leftRotation : Equiv.Perm (Fin 25) where
  toFun := leftRotationFun
  invFun := leftRotationFun ∘ leftRotationFun
  left_inv := by intro a; fin_cases a <;> rfl
  right_inv := by intro a; fin_cases a <;> rfl

theorem leftRotation_graph : graph.IsAutomorphism leftRotation := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a <;> fin_cases a <;> decide +kernel

def leftGraphRotation : graph.Aut := ⟨leftRotation, leftRotation_graph⟩
def leftPhysicalRotation : physical.Aut := graph.detectedMultiCenterAutOfGraphAut leftGraphRotation

def exchangeFun (a : Fin 25) : Fin 25 :=
  if lower : 3 ≤ a.val then
    if upper : a.val ≤ 13 then ⟨a.val + 11, by omega⟩
    else ⟨a.val - 11, by omega⟩
  else a

def exchange : Equiv.Perm (Fin 25) where
  toFun := exchangeFun
  invFun := exchangeFun
  left_inv := by intro a; fin_cases a <;> rfl
  right_inv := by intro a; fin_cases a <;> rfl

theorem exchange_graph : graph.IsAutomorphism exchange := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a <;> fin_cases a <;> decide +kernel

def exchangeAut : canon.Aut := ⟨exchange, exchange_graph, by
  intro a
  change a ∈ graph.tetrahedralCenterSet ↔ exchange a ∈ graph.tetrahedralCenterSet
  rw [detected_inventory]
  fin_cases a <;> decide +kernel⟩

/-! Finite closure checks, followed by ordinary walk induction. -/

private theorem walk_closed {G : SimpleGraph (Fin 25)} (P : Fin 25 → Prop)
    (closed : ∀ a b, P a → G.Adj a b → P b) {a b : Fin 25} (p : G.Walk a b) :
    P a → P b := by
  induction p with
  | nil => exact id
  | @cons a b c edge tail ih => exact fun ha => ih (closed a b ha edge)

theorem left_residual_component (x : Fin 25)
    (member : InComponent graph [0, 4] 3 x) : x = 3 ∨ (5 ≤ x.val ∧ x.val ≤ 13) := by
  have closed : ∀ a b : Fin 25, (a = 3 ∨ (5 ≤ a.val ∧ a.val ≤ 13)) →
      (residualGraph graph [0, 4]).Adj a b → (b = 3 ∨ (5 ≤ b.val ∧ b.val ≤ 13)) := by
    decide +kernel
  obtain ⟨p⟩ := member.2
  exact walk_closed _ closed p (Or.inl rfl)

theorem right_residual_component (x : Fin 25)
    (member : InComponent graph [0, 15] 14 x) : x = 14 ∨ (16 ≤ x.val ∧ x.val ≤ 24) := by
  have closed : ∀ a b : Fin 25, (a = 14 ∨ (16 ≤ a.val ∧ a.val ≤ 24)) →
      (residualGraph graph [0, 15]).Adj a b → (b = 14 ∨ (16 ≤ b.val ∧ b.val ≤ 24)) := by
    decide +kernel
  obtain ⟨p⟩ := member.2
  exact walk_closed _ closed p (Or.inl rfl)

private theorem walk_avoiding_closed (P : Fin 25 → Prop)
    (closed : ∀ a b, P a → graph.Adj a b → b ≠ 0 → P b)
    {a b : Fin 25} (p : graph.underlyingSimpleGraph.Walk a b) :
    (0 : Fin 25) ∉ p.support → P a → P b := by
  induction p with
  | nil => exact fun _ ha => ha
  | @cons a b c edge tail ih =>
      intro avoid ha
      have tailAvoid : (0 : Fin 25) ∉ tail.support := fun h =>
        avoid (by rw [SimpleGraph.Walk.support_cons]; exact List.mem_cons_of_mem _ h)
      have ne : b ≠ 0 := fun h => tailAvoid (h ▸ tail.start_mem_support)
      exact ih tailAvoid (closed a b ha edge ne)

theorem left_branch_center (d : canon.Center)
    (reached : LigandBranchReaches canon center0 2 d.1) : d = centerL := by
  obtain ⟨p, avoid⟩ := reached
  have closed : ∀ a b : Fin 25, (3 ≤ a.val ∧ a.val ≤ 13) → graph.Adj a b → b ≠ 0 →
      (3 ≤ b.val ∧ b.val ≤ 13) := by decide +kernel
  have bounds := walk_avoiding_closed _ closed p avoid (by rw [ligands0]; decide)
  rcases center_cases d with h | h | h
  · subst d; norm_num [center0] at bounds
  · exact h
  · subst d; norm_num [centerR] at bounds

theorem left_branch_reaches : LigandBranchReaches canon center0 2 centerL.1 := by
  unfold LigandBranchReaches
  rw [ligands0]
  refine ⟨SimpleGraph.Walk.cons (show graph.Adj 4 3 from by decide +kernel)
    SimpleGraph.Walk.nil, ?_⟩
  simp [center0, centerL, frame0]

/-! Molecular automorphisms preserve the oriented B-O-S cycle. -/

private abbrev permutation (e : canon.Aut) : Equiv.Perm (Fin 25) :=
  (e : Equiv.Perm (certified false).Atom)

private def toGraphAut (e : canon.Aut) : graph.Aut :=
  ⟨permutation e, MultiCenterMolecule.Aut.mem_molAut (m := canon) e⟩

private theorem z_one (a : Fin 25) : graph.atomZ a = 1 ↔ a = 1 := by
  fin_cases a <;> decide +kernel
private theorem z_seventeen (a : Fin 25) : graph.atomZ a = 17 ↔ a = 2 := by
  fin_cases a <;> decide +kernel
private theorem adj_one (a : Fin 25) : graph.Adj 1 a ↔ a = 0 := by
  fin_cases a <;> decide +kernel

theorem fixed_hydrogen (e : graph.Aut) : (e : Equiv.Perm (Fin 25)) 1 = 1 :=
  (z_one _).mp ((MoleculeGraph.Aut.atomZ_eq (m := graph) e 1).trans rfl)
theorem fixed_chlorine (e : graph.Aut) : (e : Equiv.Perm (Fin 25)) 2 = 2 :=
  (z_seventeen _).mp ((MoleculeGraph.Aut.atomZ_eq (m := graph) e 2).trans rfl)
theorem fixed_root (e : graph.Aut) : (e : Equiv.Perm (Fin 25)) 0 = 0 := by
  apply (adj_one _).mp
  have h := (MoleculeGraph.Aut.adj_iff (m := graph) e 1 0).mpr (by decide +kernel)
  simpa only [fixed_hydrogen e] using h

theorem center0_fixed (e : canon.Aut) : canon.centerPerm e center0 = center0 :=
  Subtype.ext (fixed_root (toGraphAut e))

theorem center_image (e : canon.Aut) (c : canon.Center) (nonroot : c ≠ center0) :
    canon.centerPerm e c = centerL ∨ canon.centerPerm e c = centerR := by
  rcases center_cases (canon.centerPerm e c) with h | h | h
  · have same : canon.centerPerm e c = canon.centerPerm e center0 := h.trans (center0_fixed e).symm
    exact (nonroot ((canon.centerPerm e).injective same)).elim
  · exact Or.inl h
  · exact Or.inr h

private def cycleAtoms : Finset (Fin 25) := {5, 6, 7, 8, 9, 10, 11, 12, 13, 16, 17, 18, 19, 20, 21, 22, 23, 24}
private def next (a : Fin 25) : Fin 25 :=
  if a = 5 then 8 else if a = 8 then 11 else if a = 11 then 6 else
  if a = 6 then 9 else if a = 9 then 12 else if a = 12 then 7 else
  if a = 7 then 10 else if a = 10 then 13 else if a = 13 then 5 else
  if a = 16 then 19 else if a = 19 then 22 else if a = 22 then 17 else
  if a = 17 then 20 else if a = 20 then 23 else if a = 23 then 18 else
  if a = 18 then 21 else if a = 21 then 24 else if a = 24 then 16 else a
private def nextZ (a : Fin 25) : Nat :=
  if graph.atomZ a = 5 then 8 else if graph.atomZ a = 8 then 16 else
  if graph.atomZ a = 16 then 5 else 0

private theorem next_iff (a b : Fin 25) :
    graph.Adj a b ∧ graph.atomZ b = nextZ a ↔ a ∈ cycleAtoms ∧ b = next a := by
  fin_cases a <;> fin_cases b <;> decide +kernel

private theorem next_cycle (a : Fin 25) (h : a ∈ cycleAtoms) : next a ∈ cycleAtoms := by
  have finite : ∀ a : Fin 25, a ∈ cycleAtoms → next a ∈ cycleAtoms := by decide +kernel
  exact finite a h

private theorem aut_next (e : graph.Aut) (a : Fin 25) (h : a ∈ cycleAtoms) :
    (e : Equiv.Perm (Fin 25)) (next a) = next ((e : Equiv.Perm (Fin 25)) a) := by
  have color := MoleculeGraph.Aut.atomZ_eq (m := graph) e
  apply ((next_iff _ _).mp ?_).2
  obtain ⟨edge, label⟩ := (next_iff a (next a)).mpr ⟨h, rfl⟩
  refine ⟨(MoleculeGraph.Aut.adj_iff (m := graph) e a (next a)).mpr edge, ?_⟩
  rw [color (next a), label]
  simp only [nextZ, color a]

private def spokeNext (a : Fin 25) : Fin 25 :=
  if a = 5 then 6 else if a = 6 then 7 else if a = 7 then 5 else
  if a = 16 then 17 else if a = 17 then 18 else if a = 18 then 16 else a

private theorem spokeNext_eq (a : Fin 25) :
    spokeNext a = if graph.atomZ a = 5 then next (next (next a)) else a := by
  fin_cases a <;> decide +kernel

private theorem aut_spokeNext (e : graph.Aut) (a : Fin 25) :
    (e : Equiv.Perm (Fin 25)) (spokeNext a) = spokeNext ((e : Equiv.Perm (Fin 25)) a) := by
  have color := MoleculeGraph.Aut.atomZ_eq (m := graph) e a
  rw [spokeNext_eq, spokeNext_eq, color]
  split_ifs with boron
  · have finite : ∀ a : Fin 25, graph.atomZ a = 5 → a ∈ cycleAtoms := by decide +kernel
    have cycle := finite a boron
    rw [aut_next e _ (next_cycle _ (next_cycle _ cycle)),
      aut_next e _ (next_cycle _ cycle), aut_next e _ cycle]
  · rfl

private def rho : Equiv.Perm (Fin 4) := Equiv.swap 1 2 * Equiv.swap 2 3

private theorem rho_even : permHandedness rho = 1 := by
  simp [rho, permHandedness,
    Equiv.Perm.sign_swap (show (1 : Fin 4) ≠ 2 by decide),
    Equiv.Perm.sign_swap (show (2 : Fin 4) ≠ 3 by decide)]

private theorem commuting_even (p : Equiv.Perm (Fin 4))
    (commutes : ∀ i, p (rho i) = rho (p i)) : permHandedness p = 1 := by
  have finite : ∀ p : Equiv.Perm (Fin 4), (∀ i, p (rho i) = rho (p i)) →
      p = 1 ∨ p = rho ∨ p = rho * rho := by decide +kernel
  rcases finite p commutes with h | h | h
  · rw [h, permHandedness_one]
  · rw [h, rho_even]
  · rw [h, permHandedness_mul, rho_even, one_mul]

private theorem ligand_cycle (c : canon.Center) (nonroot : c ≠ center0) (i : Fin 4) :
    spokeNext (canon.ligandAtomAt c i) = canon.ligandAtomAt c (rho i) := by
  rcases center_cases c with h | h | h
  · exact (nonroot h).elim
  · subst c
    rw [ligandsL, ligandsL]
    fin_cases i <;> decide +kernel
  · subst c
    rw [ligandsR, ligandsR]
    fin_cases i <;> decide +kernel

theorem gadget_local_even (e : canon.Aut) (c : canon.Center) (nonroot : c ≠ center0) :
    permHandedness (canon.ligandPermAt e c) = 1 := by
  have targetNonroot : canon.centerPerm e c ≠ center0 := by
    intro h
    exact nonroot ((canon.centerPerm e).injective (h.trans (center0_fixed e).symm))
  apply commuting_even
  intro i
  apply canon.ligandAtomAt_injective (canon.centerPerm e c)
  calc
    canon.ligandAtomAt (canon.centerPerm e c) (canon.ligandPermAt e c (rho i)) =
        (permutation e) (canon.ligandAtomAt c (rho i)) :=
      canon.ligandAtomAt_ligandPermAt e c (rho i)
    _ = (permutation e) (spokeNext (canon.ligandAtomAt c i)) :=
      congrArg (permutation e) (ligand_cycle c nonroot i).symm
    _ = spokeNext ((permutation e) (canon.ligandAtomAt c i)) :=
      aut_spokeNext (toGraphAut e) _
    _ = spokeNext (canon.ligandAtomAt (canon.centerPerm e c) (canon.ligandPermAt e c i)) :=
      congrArg spokeNext (canon.ligandAtomAt_ligandPermAt e c i).symm
    _ = canon.ligandAtomAt (canon.centerPerm e c) (rho (canon.ligandPermAt e c i)) :=
      ligand_cycle _ targetNonroot _

private theorem root_slots (e : canon.Aut) :
    canon.ligandPermAt e center0 = 1 ∨ canon.ligandPermAt e center0 = Equiv.swap 2 3 := by
  have at0 : canon.ligandPermAt e center0 0 = 0 := by
    apply canon.ligandAtomAt_injective center0
    have h := canon.ligandAtomAt_ligandPermAt e center0 0
    rw [center0_fixed e, ligands0, ligands0] at h
    have fixed : permutation e 1 = 1 := fixed_hydrogen (toGraphAut e)
    change frame0 (canon.ligandPermAt e center0 0) = permutation e 1 at h
    rw [fixed] at h
    rw [ligands0, ligands0]
    exact h
  have at1 : canon.ligandPermAt e center0 1 = 1 := by
    apply canon.ligandAtomAt_injective center0
    have h := canon.ligandAtomAt_ligandPermAt e center0 1
    rw [center0_fixed e, ligands0, ligands0] at h
    have fixed : permutation e 2 = 2 := fixed_chlorine (toGraphAut e)
    change frame0 (canon.ligandPermAt e center0 1) = permutation e 2 at h
    rw [fixed] at h
    rw [ligands0, ligands0]
    exact h
  have finite : ∀ p : Equiv.Perm (Fin 4), p 0 = 0 → p 1 = 1 →
      p = 1 ∨ p = Equiv.swap 2 3 := by decide +kernel
  exact finite _ at0 at1

theorem root_local_parity (e : canon.Aut) :
    permHandedness (canon.ligandPermAt e center0) =
      if (permutation e) 4 = 4 then 1 else -1 := by
  have h := canon.ligandAtomAt_ligandPermAt e center0 2
  rw [center0_fixed e] at h
  rcases root_slots e with slots | slots
  · have image : (permutation e) 4 = 4 := by
      simpa [slots, ligands0, frame0] using h.symm
    simp [slots, image]
  · have image : (permutation e) 4 = 15 := by
      simpa [slots, ligands0, frame0] using h.symm
    simp [slots, image, permHandedness, Equiv.Perm.sign_swap (show (2 : Fin 4) ≠ 3 by decide)]

theorem left_to_right_of_root_slot (e : canon.Aut)
    (sent : canon.ligandPermAt e center0 2 = 3) : canon.centerPerm e centerL = centerR := by
  have frame := canon.ligandAtomAt_ligandPermAt e center0 2
  rw [center0_fixed e, sent] at frame
  have image : (permutation e) 4 = 15 := by
    simpa [ligands0, frame0] using frame.symm
  have edge := (MoleculeGraph.Aut.adj_iff (m := graph) (toGraphAut e) 4 3).mpr (by decide +kernel)
  change graph.Adj (permutation e 4) (permutation e 3) at edge
  rw [image] at edge
  rcases center_image e centerL (by decide) with h | h
  · have atom : (permutation e) 3 = 3 := congrArg Subtype.val h
    rw [atom] at edge
    exact False.elim ((show ¬ graph.Adj 15 3 by decide +kernel) edge)
  · exact h

theorem exchange_root_slot : canon.ligandPermAt exchangeAut center0 2 = 3 := by
  apply canon.ligandAtomAt_injective center0
  have h := canon.ligandAtomAt_ligandPermAt exchangeAut center0 2
  rw [center0_fixed exchangeAut] at h
  simpa [ligands0, frame0, exchangeAut, exchange, exchangeFun] using h

theorem branch_transport_iff (cfg : canon.Configuration) (mirror : Bool) :
    BranchTransport canon cfg center0 2 3 mirror ↔
      canon.configurationSign cfg centerL =
        (if mirror then -1 else 1) * canon.configurationSign cfg centerR := by
  constructor
  · rintro ⟨e, _, sent, signs⟩
    have h := signs centerL left_branch_reaches
    rw [gadget_local_even e centerL (by decide), left_to_right_of_root_slot e sent, mul_one] at h
    exact h
  · intro signs
    refine ⟨exchangeAut, center0_fixed exchangeAut, exchange_root_slot, ?_⟩
    intro d reached
    rw [left_branch_center d reached, gadget_local_even exchangeAut centerL (by decide),
      left_to_right_of_root_slot exchangeAut exchange_root_slot, mul_one]
    exact signs

theorem proper_transport_iff (cfg : canon.Configuration) :
    ProperTransport canon cfg center0 2 3 ↔
      canon.configurationSign cfg centerL = canon.configurationSign cfg centerR := by
  simpa [ProperTransport] using branch_transport_iff cfg false

theorem mirror_transport_iff (cfg : canon.Configuration) :
    MirrorTransport canon cfg center0 2 3 ↔
      canon.configurationSign cfg centerL = - canon.configurationSign cfg centerR := by
  simpa [MirrorTransport] using branch_transport_iff cfg true

theorem enantiomorphic_of_opposite (cfg : canon.Configuration)
    (opposite : canon.configurationSign cfg centerL = - canon.configurationSign cfg centerR) :
    Enantiomorphic canon cfg center0 2 3 := by
  refine ⟨by decide, (mirror_transport_iff cfg).mpr opposite, ?_⟩
  intro proper
  have same := (proper_transport_iff cfg).mp proper
  have sign := permHandedness_eq_one_or_eq_neg_one (cfg centerR)
  change canon.configurationSign cfg centerR = 1 ∨ canon.configurationSign cfg centerR = -1 at sign
  rcases sign with sign | sign <;> rw [sign] at same opposite <;> linarith

/-- The canonical result transports to any accepted reindexing of the actual detected frames. -/
theorem enantiomorphic_reindexed (cfg : canon.Configuration)
    (opposite : canon.configurationSign cfg centerL = - canon.configurationSign cfg centerR)
    (tau : canon.Center → Equiv.Perm (Fin 4)) :
    Enantiomorphic (canon.reindexFrames tau) (canon.reindexConfiguration tau cfg) center0
      ((tau center0)⁻¹ 2) ((tau center0)⁻¹ 3) := by
  rw [MultiCenterMolecule.enantiomorphic_reindexFrames_iff]
  simpa using enantiomorphic_of_opposite cfg opposite

end TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.center_cases
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.ligands0
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.ligandsL
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.ligandsR
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.leftRotation_graph
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.exchange_graph
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.left_residual_component
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.right_residual_component
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.left_branch_center
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.left_branch_reaches
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.fixed_hydrogen
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.fixed_chlorine
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.fixed_root
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.center0_fixed
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.center_image
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.gadget_local_even
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.root_local_parity
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.left_to_right_of_root_slot
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.exchange_root_slot
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.branch_transport_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.proper_transport_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.mirror_transport_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.enantiomorphic_of_opposite
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingDoubleC3Physical.enantiomorphic_reindexed
