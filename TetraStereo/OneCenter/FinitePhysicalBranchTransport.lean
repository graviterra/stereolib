import TetraStereo.OneCenter.PhysicalEnantiomorphicPairCountReindexing
import TetraStereo.OneCenter.RootedBranchFrameReindexInvariance
import TetraStereo.MultiCenter.RootedBranchTerminalTwinCompletion
import TetraStereo.OneCenter.LocalizedPhysicalCalibratedRootReader
import TetraStereo.KernelOnly
import Mathlib.Combinatorics.SimpleGraph.Paths

set_option autoImplicit false

/-!
# A total executable decision procedure for the existing physical branch relation

For an explicitly represented finite `MultiCenterMolecule V` and configuration `cfg`, this module
**computes** the accepted predicates of `RootedTetrahedralBranchSymmetry`:

* `decideBranchTransport m cfg c i j mirror = true ↔ BranchTransport m cfg c i j mirror`;
* `decideEnantiomorphic m cfg c i j = true ↔ Enantiomorphic m cfg c i j`;
* `computedPairCount m cfg c = physicalEnantiomorphicPairCount m cfg c`.

The search enumerates **one global candidate** `e : Equiv.Perm V` at a time. Each candidate is
checked for preservation of atomic number, mass, charge, every bond order and the centre set; it
must fix the root and send ligand `i` to ligand `j`. Then **every** centre reached in the deleted-root
branch of `i` must satisfy the sign equation of `BranchTransport`, all for that same candidate. So
all joint configuration constraints are kept: no per-centre or pairwise choices.

Executable ingredients, each proved equal to the existing noncomputable notion:

* `branchReachSet` (iterated neighbourhood closure with the root deleted) ↔ `LigandBranchReaches`,
  for arbitrary finite graphs including rings and inward paths (`mem_branchReachSet_iff`);
* `localFun` (index search in the image centre's ligand enumeration) = `ligandPermAt` for genuine
  automorphisms (`localFun_eq`);
* `funSign` (Mathlib's inversion product `signAux` on a function) = `Equiv.Perm.sign`
  (`funSign_perm`); the sign equation is checked in `ℤˣ`, equivalent to the real equation
  (`sign_equation_iff`). No real-number equality oracle is used.

Complexity: the reference search is exhaustive over `|V|!` permutations. That is factorial and
intended as a reference decision procedure, not an optimized canonicalizer.
-/

namespace TetraStereo.OneCenter.FinitePhysicalBranchTransport

open RootedTetrahedralBranchSymmetry

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Executable reachability with a deleted vertex -/

section Reach

variable (G : MoleculeGraph V) (avoid : V)

def reachStep (S : Finset V) : Finset V :=
  S ∪ Finset.univ.filter (fun w => w ≠ avoid ∧ ∃ u ∈ S, G.Adj u w)

def reachIter : ℕ → Finset V → Finset V
  | 0, S => S
  | n + 1, S => reachStep G avoid (reachIter n S)

theorem subset_reachStep (S : Finset V) : S ⊆ reachStep G avoid S := Finset.subset_union_left

theorem reachIter_mono (S : Finset V) {k k' : ℕ} (h : k ≤ k') :
    reachIter G avoid k S ⊆ reachIter G avoid k' S := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | step _ ih => exact ih.trans (subset_reachStep G avoid _)

theorem reachIter_sound (start : V) (hs : start ≠ avoid) :
    ∀ (n : ℕ) (v : V), v ∈ reachIter G avoid n {start} →
      ∃ p : G.underlyingSimpleGraph.Walk start v, avoid ∉ p.support := by
  intro n
  induction n with
  | zero =>
      intro v hv
      simp only [reachIter, Finset.mem_singleton] at hv
      subst hv
      refine ⟨SimpleGraph.Walk.nil, ?_⟩
      simpa using hs.symm
  | succ n ih =>
      intro v hv
      simp only [reachIter, reachStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
        true_and] at hv
      rcases hv with hv | ⟨hne, u, hu, hadj⟩
      · exact ih v hv
      · obtain ⟨p, hp⟩ := ih u hu
        have hadj' : G.underlyingSimpleGraph.Adj u v := hadj
        refine ⟨p.concat hadj', ?_⟩
        rw [SimpleGraph.Walk.support_concat]
        simp [List.concat_eq_append, hp, Ne.symm hne]

theorem reach_walk_iter (start : V) {a b : V} (p : G.underlyingSimpleGraph.Walk a b) :
    ∀ k : ℕ, avoid ∉ p.support → a ∈ reachIter G avoid k {start} →
      b ∈ reachIter G avoid (k + p.length) {start} := by
  induction p with
  | nil =>
      intro k _ ha
      simpa using ha
  | @cons u v w h p ih =>
      intro k hav ha
      have hvAvoid : v ≠ avoid := by
        intro e
        apply hav
        rw [SimpleGraph.Walk.support_cons]
        rw [← e]
        exact List.mem_cons_of_mem _ p.start_mem_support
      have hv : v ∈ reachIter G avoid (k + 1) {start} := by
        show v ∈ reachStep G avoid (reachIter G avoid k {start})
        simp only [reachStep, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨hvAvoid, u, ha, h⟩
      have hp : avoid ∉ p.support := fun member => hav (by
        rw [SimpleGraph.Walk.support_cons]
        exact List.mem_cons_of_mem _ member)
      have step := ih (k + 1) hp hv
      rw [SimpleGraph.Walk.length_cons, show k + (p.length + 1) = k + 1 + p.length by omega]
      exact step

/-- The vertices reachable from `start` by walks avoiding `avoid`, computed in `|V|` rounds. -/
def reachSet (start : V) : Finset V := reachIter G avoid (Fintype.card V) {start}

theorem mem_reachSet_iff (start : V) (hs : start ≠ avoid) (v : V) :
    v ∈ reachSet G avoid start ↔
      ∃ p : G.underlyingSimpleGraph.Walk start v, avoid ∉ p.support := by
  constructor
  · exact reachIter_sound G avoid start hs _ v
  · rintro ⟨p, hp⟩
    have hq : avoid ∉ p.bypass.support := fun member => hp (p.support_bypass_subset member)
    have hlen : p.bypass.length < Fintype.card V := p.bypass_isPath.length_lt
    have reached := reach_walk_iter G avoid start p.bypass 0 hq (by simp [reachIter])
    exact reachIter_mono G avoid {start} (by omega) reached

end Reach

section Molecule

variable (m : MultiCenterMolecule V)

/-- Executable deleted-root branch of ligand `i`. -/
def branchReachSet (c : m.Center) (i : Fin 4) : Finset V :=
  reachSet m.mol c.1 (m.ligandAtomAt c i)

theorem mem_branchReachSet_iff (c : m.Center) (i : Fin 4) (v : V) :
    v ∈ branchReachSet m c i ↔ LigandBranchReaches m c i v :=
  mem_reachSet_iff m.mol c.1 (m.ligandAtomAt c i)
    (m.mol.underlyingSimpleGraph.ne_of_adj (m.ligandAtomAt_adj c i)).symm v

/-! ## Executable local ligand parity -/

/-- Index of an atom in a centre's ligand enumeration (`3` when absent). -/
def ligIndex (d : m.Center) (a : V) : Fin 4 :=
  if m.ligandAtomAt d 0 = a then 0
  else if m.ligandAtomAt d 1 = a then 1
  else if m.ligandAtomAt d 2 = a then 2
  else 3

theorem ligIndex_eq (d : m.Center) (k : Fin 4) : ligIndex m d (m.ligandAtomAt d k) = k := by
  have inj := m.ligandAtomAt_injective d
  fin_cases k <;> simp [ligIndex, inj.eq_iff]

/-- The local ligand reindexing of a candidate permutation from `d` to `d'`. -/
def localFun (e : Equiv.Perm V) (d d' : m.Center) : Fin 4 → Fin 4 :=
  fun k => ligIndex m d' (e (m.ligandAtomAt d k))

theorem localFun_eq (E : m.Aut) (d : m.Center) :
    localFun m (E : Equiv.Perm V) d (m.centerPerm E d) = ⇑(m.ligandPermAt E d) := by
  funext k
  have h := m.ligandAtomAt_ligandPermAt (e := E) (c := d) k
  simp only [localFun]
  rw [← h, ligIndex_eq]

/-- Mathlib's inversion product, on a function. -/
def funSign (f : Fin 4 → Fin 4) : ℤˣ :=
  ∏ x ∈ Equiv.Perm.finPairsLT 4, if f x.1 ≤ f x.2 then -1 else 1

theorem signAux_eq_sign {n : ℕ} (σ : Equiv.Perm (Fin n)) :
    Equiv.Perm.signAux σ = Equiv.Perm.sign σ := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => simp
  | swap_mul f x y hxy ih =>
      rw [Equiv.Perm.signAux_mul, Equiv.Perm.sign_mul, ih, Equiv.Perm.signAux_swap hxy,
        Equiv.Perm.sign_swap hxy]

theorem funSign_perm (σ : Equiv.Perm (Fin 4)) : funSign ⇑σ = Equiv.Perm.sign σ :=
  signAux_eq_sign σ

theorem sign_equation_iff (a b c : ℤˣ) (mirror : Bool) :
    ((a : ℤ) : ℝ) * ((b : ℤ) : ℝ) = (if mirror then -1 else 1) * ((c : ℤ) : ℝ) ↔
      a * b = (if mirror then -1 else 1) * c := by
  have cast : ∀ u v : ℤˣ, ((u : ℤ) : ℝ) = ((v : ℤ) : ℝ) ↔ u = v := by
    intro u v
    rw [Int.cast_inj, Units.val_inj]
  cases mirror with
  | false =>
      simp only [Bool.false_eq_true, if_false, one_mul]
      rw [← cast]
      push_cast
      rfl
  | true =>
      simp only [if_true]
      rw [← cast]
      push_cast
      rfl

/-! ## The candidate check and the search -/

/-- Exact automorphism test of `MultiCenterMolecule.Aut`. -/
def isAutCheck (e : Equiv.Perm V) : Bool :=
  decide (((∀ v, m.mol.atomZ (e v) = m.mol.atomZ v) ∧
      (∀ v, m.mol.atomMass (e v) = m.mol.atomMass v) ∧
      (∀ v, m.mol.formalCharge (e v) = m.mol.formalCharge v) ∧
      (∀ u v, m.mol.bond (e u) (e v) = m.mol.bond u v)) ∧
    (∀ v, v ∈ m.centers ↔ e v ∈ m.centers))

theorem isAutCheck_iff (e : Equiv.Perm V) : isAutCheck m e = true ↔ e ∈ m.Aut := by
  unfold isAutCheck
  rw [decide_eq_true_iff]
  exact Iff.rfl

/-- The sign equation of `BranchTransport` at one centre, for one candidate. -/
def signOK (cfg : m.Configuration) (mirror : Bool) (e : Equiv.Perm V) (d : m.Center) : Bool :=
  if h : e d.1 ∈ m.centers then
    decide (Equiv.Perm.sign (cfg d) * funSign (localFun m e d ⟨e d.1, h⟩) =
      (if mirror then -1 else 1) * Equiv.Perm.sign (cfg ⟨e d.1, h⟩))
  else false

/-- One global candidate: automorphism, root fixed, ligand `i ↦ j`, and **all** reached sign
equations. -/
def candidateOK (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) (mirror : Bool)
    (e : Equiv.Perm V) : Bool :=
  isAutCheck m e && decide (e c.1 = c.1) &&
    decide (e (m.ligandAtomAt c i) = m.ligandAtomAt c j) &&
    decide (∀ d : m.Center, d.1 ∈ branchReachSet m c i → signOK m cfg mirror e d = true)

/-- **Executable decision of `BranchTransport`.** -/
def decideBranchTransport (cfg : m.Configuration) (c : m.Center) (i j : Fin 4)
    (mirror : Bool) : Bool :=
  decide (∃ e : Equiv.Perm V, candidateOK m cfg c i j mirror e = true)

private theorem centerPerm_val (E : m.Aut) (d : m.Center) :
    (m.centerPerm E d).1 = (E : Equiv.Perm V) d.1 := rfl

theorem decideBranchTransport_iff (cfg : m.Configuration) (c : m.Center) (i j : Fin 4)
    (mirror : Bool) :
    decideBranchTransport m cfg c i j mirror = true ↔ BranchTransport m cfg c i j mirror := by
  unfold decideBranchTransport
  rw [decide_eq_true_iff]
  constructor
  · rintro ⟨e, he⟩
    simp only [candidateOK, Bool.and_eq_true, decide_eq_true_eq] at he
    obtain ⟨⟨⟨haut, hc⟩, hi⟩, hsign⟩ := he
    let E : m.Aut := ⟨e, (isAutCheck_iff m e).mp haut⟩
    have hcE : m.centerPerm E c = c := Subtype.ext hc
    refine ⟨E, hcE, ?_, ?_⟩
    · apply m.ligandAtomAt_injective c
      have transported := m.ligandAtomAt_ligandPermAt (e := E) (c := c) i
      rw [hcE] at transported
      rw [transported]
      exact hi
    · intro d hd
      have hok := hsign d ((mem_branchReachSet_iff m c i d.1).mpr hd)
      by_cases h : e d.1 ∈ m.centers
      · rw [signOK, dif_pos h, decide_eq_true_iff] at hok
        have hcp : (⟨e d.1, h⟩ : m.Center) = m.centerPerm E d := Subtype.ext rfl
        rw [hcp, localFun_eq m E d, funSign_perm] at hok
        exact (sign_equation_iff _ _ _ mirror).mpr hok
      · rw [signOK, dif_neg h] at hok
        exact absurd hok (by decide)
  · rintro ⟨E, hcE, hiE, hsign⟩
    refine ⟨(E : Equiv.Perm V), ?_⟩
    simp only [candidateOK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨(isAutCheck_iff m E).mpr E.property, ?_⟩, ?_⟩, ?_⟩
    · have := congrArg Subtype.val hcE
      rw [centerPerm_val] at this
      exact this
    · have transported := m.ligandAtomAt_ligandPermAt (e := E) (c := c) i
      rw [hcE, hiE] at transported
      exact transported.symm
    · intro d hd
      have hrd := (mem_branchReachSet_iff m c i d.1).mp hd
      have h : (E : Equiv.Perm V) d.1 ∈ m.centers := (m.centerPerm E d).2
      rw [signOK, dif_pos h, decide_eq_true_iff]
      have hcp : (⟨(E : Equiv.Perm V) d.1, h⟩ : m.Center) = m.centerPerm E d := Subtype.ext rfl
      rw [hcp, localFun_eq m E d, funSign_perm]
      exact (sign_equation_iff _ _ _ mirror).mp (hsign d hrd)

def decideProperTransport (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) : Bool :=
  decideBranchTransport m cfg c i j false

def decideMirrorTransport (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) : Bool :=
  decideBranchTransport m cfg c i j true

theorem decideProperTransport_iff (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) :
    decideProperTransport m cfg c i j = true ↔ ProperTransport m cfg c i j :=
  decideBranchTransport_iff m cfg c i j false

theorem decideMirrorTransport_iff (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) :
    decideMirrorTransport m cfg c i j = true ↔ MirrorTransport m cfg c i j :=
  decideBranchTransport_iff m cfg c i j true

/-- **Executable decision of `Enantiomorphic`.** -/
def decideEnantiomorphic (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) : Bool :=
  decide (i ≠ j) && decideMirrorTransport m cfg c i j && !decideProperTransport m cfg c i j

theorem decideEnantiomorphic_iff (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) :
    decideEnantiomorphic m cfg c i j = true ↔ Enantiomorphic m cfg c i j := by
  have hm := decideMirrorTransport_iff m cfg c i j
  have hp := decideProperTransport_iff m cfg c i j
  unfold decideEnantiomorphic Enantiomorphic
  cases h1 : decideMirrorTransport m cfg c i j <;>
    cases h2 : decideProperTransport m cfg c i j <;> simp_all

/-- **Executable physical enantiomorphic-pair count.** -/
def computedPairCount (cfg : m.Configuration) (c : m.Center) : ℕ :=
  sourceEnantiomorphicPairCount (fun a b : Fin 4 => decideEnantiomorphic m cfg c a b = true)

theorem computedPairCount_eq (cfg : m.Configuration) (c : m.Center) :
    computedPairCount m cfg c = physicalEnantiomorphicPairCount m cfg c := by
  unfold computedPairCount physicalEnantiomorphicPairCount
  exact sourceEnantiomorphicPairCount_congr _ _
    (fun a b _ => decideEnantiomorphic_iff m cfg c a b)

/-! ## Configuration-sign congruence away from the root and terminal twins

The physical relation only reads configuration signs at reached centres and their images. Those
are never the root (`ligandBranchReaches_ne_root`; root-fixing transport). At centres with
physical terminal twins the accepted completion `branchTransport_iff_orientationAtNonTwinCenters`
removes the sign obligation. Hence two configurations with equal signs at every non-root,
non-twin centre have the same branch relations and pair count. -/

open RootedBranchTerminalTwinCompletion in
theorem hasTerminalTwins_centerPerm_iff (e : m.Aut) (d : m.Center) :
    HasTerminalTwins m (m.centerPerm e d) ↔ HasTerminalTwins m d := by
  constructor
  · rintro ⟨a, b, pair⟩
    have transported := CertifiedLocalizedCIPInput.terminalTwinPair_centerPerm pair (e⁻¹ : m.Aut)
    have centerEq : m.centerPerm (e⁻¹ : m.Aut) (m.centerPerm e d) = d := by
      apply Subtype.ext
      simp [MultiCenterMolecule.centerPerm]
    rw [centerEq] at transported
    exact ⟨_, _, transported⟩
  · rintro ⟨a, b, pair⟩
    exact ⟨_, _, CertifiedLocalizedCIPInput.terminalTwinPair_centerPerm pair e⟩

open RootedBranchTerminalTwinCompletion in
theorem branchTransport_congr_nonTwin (cfg₁ cfg₂ : m.Configuration) (c : m.Center)
    (signs : ∀ d : m.Center, d ≠ c → ¬ HasTerminalTwins m d →
      m.configurationSign cfg₁ d = m.configurationSign cfg₂ d)
    (i j : Fin 4) (mirror : Bool) :
    BranchTransport m cfg₁ c i j mirror → BranchTransport m cfg₂ c i j mirror := by
  intro transport
  rw [branchTransport_iff_orientationAtNonTwinCenters] at transport ⊢
  obtain ⟨e, hc, hi, hred⟩ := transport
  refine ⟨e, hc, hi, fun d hd twin => ?_⟩
  have dRoot : d ≠ c := fun h => ligandBranchReaches_ne_root m c i hd (congrArg Subtype.val h)
  have imageRoot : m.centerPerm e d ≠ c := fun h => dRoot ((m.centerPerm e).injective (h.trans hc.symm))
  have imageTwin : ¬ HasTerminalTwins m (m.centerPerm e d) :=
    fun h => twin ((hasTerminalTwins_centerPerm_iff m e d).mp h)
  rw [← signs d dRoot twin, ← signs _ imageRoot imageTwin]
  exact hred d hd twin

theorem physicalPairCount_congr_nonTwin (cfg₁ cfg₂ : m.Configuration) (c : m.Center)
    (signs : ∀ d : m.Center, d ≠ c → ¬ RootedBranchTerminalTwinCompletion.HasTerminalTwins m d →
      m.configurationSign cfg₁ d = m.configurationSign cfg₂ d) :
    physicalEnantiomorphicPairCount m cfg₁ c = physicalEnantiomorphicPairCount m cfg₂ c := by
  have signs' : ∀ d : m.Center, d ≠ c →
      ¬ RootedBranchTerminalTwinCompletion.HasTerminalTwins m d →
      m.configurationSign cfg₂ d = m.configurationSign cfg₁ d :=
    fun d h t => (signs d h t).symm
  have transport : ∀ i j mirror,
      BranchTransport m cfg₁ c i j mirror ↔ BranchTransport m cfg₂ c i j mirror :=
    fun i j mirror => ⟨branchTransport_congr_nonTwin m cfg₁ cfg₂ c signs i j mirror,
      branchTransport_congr_nonTwin m cfg₂ cfg₁ c signs' i j mirror⟩
  unfold physicalEnantiomorphicPairCount
  exact sourceEnantiomorphicPairCount_congr _ _ (fun a b _ => by
    unfold Enantiomorphic MirrorTransport ProperTransport
    rw [transport a b true, transport a b false])

end Molecule

end TetraStereo.OneCenter.FinitePhysicalBranchTransport

assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchTransport.mem_reachSet_iff
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchTransport.mem_branchReachSet_iff
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchTransport.localFun_eq
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchTransport.funSign_perm
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchTransport.decideBranchTransport_iff
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchTransport.decideEnantiomorphic_iff
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchTransport.computedPairCount_eq
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchTransport.hasTerminalTwins_centerPerm_iff
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchTransport.branchTransport_congr_nonTwin
assert_kernel_only TetraStereo.OneCenter.FinitePhysicalBranchTransport.physicalPairCount_congr_nonTwin
