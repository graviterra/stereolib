import TetraStereo.OneCenter.RootedTetrahedralBranchSymmetry
import TetraStereo.OneCenter.TerminalTwinConfigurationGauge

set_option autoImplicit false

/-!
# Exact physical completeness of rooted branch transport

`RootedTetrahedralBranchSymmetry.BranchTransport` asks for an actual automorphism `e` of the
multi-center molecule that fixes the root `c`, sends the ligand index `i` to `j`, and realizes a
prescribed local frame relation *at every center of the ligand branch at `i`*.

`TerminalTwinConfigurationGauge` shows that a center carrying two identical terminal ligands has
no physical local frame: swapping the two terminal atoms is an actual graph automorphism fixing
every center and acting by an odd local ligand permutation at that center.  Such a center is
therefore a frame gauge, and no orientation constraint can be physically meaningful there.

This module proves the exact reduction: `BranchTransport` is equivalent to the same orientation
constraint imposed only at branch centers that do *not* carry a physical terminal twin.  The
forward direction is immediate.  The reverse direction is constructive: given an actual
automorphism satisfying the reduced constraints, we enumerate the finite set of branch centers
where its full sign equation fails, extract for each of them a genuine terminal twin pair, assemble
those pairs into an actual `TerminalTwinFamily`, and correct the *source* by the resulting
`familyAut`.  The corrected automorphism `e * g` fixes the root, still sends `i` to `j` (the family
fixes every center and has identity local permutation at the root), and satisfies the full sign
equation: at failing centers the family supplies an odd local permutation which repairs the sign by
exactly `-`; at all other centers the family is locally trivial.

No family, correction, or desired sign equation is assumed.  No acyclicity hypothesis is used.
The result concerns the `configurationSign` relation (sign patterns), not a literal Cartesian
transformation of configurations, and it asserts nothing about which descriptor a reader should
return at a twin center.

The main results are:

* `HasTerminalTwins`: the physical twin predicate at a distinguished center;
* `ligandBranchReaches_ne_root`: a branch reachable from a ligand never reaches the root;
* `branchTransport_iff_orientationAtNonTwinCenters`: the exact reduction;
* `properTransport_iff_orientationAtNonTwinCenters` and
  `mirrorTransport_iff_orientationAtNonTwinCenters`: the two mirror specializations;
* `properTransport_of_rootFixing_of_allTerminalTwins`: if every branch center is twin-degenerate,
  every root-fixing actual branch exchange is a proper transport.
-/

namespace TetraStereo
namespace OneCenter
namespace RootedBranchTerminalTwinCompletion

noncomputable section

open RootedTetrahedralBranchSymmetry
open TerminalTwinConfigurationGauge
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### The physical twin predicate -/

/-- A distinguished center has *physical terminal twins* when two actual atoms of the molecular
graph form a `TerminalTwinPair` there.  This is a property of the complete physical graph
(labels, masses, charges, bond orders and adjacency), not a frame- or descriptor-level datum. -/
def HasTerminalTwins (m : MultiCenterMolecule V) (d : m.Center) : Prop :=
  ∃ a b : V, TerminalTwinPair m d a b

/-! ### Root avoidance of a reachable branch -/

/-- A vertex reached inside the ligand branch at `i` after deleting the root is never the root
atom itself: the witnessing walk has that vertex at its end, hence in its support, while the
support avoids the root. -/
theorem ligandBranchReaches_ne_root (m : MultiCenterMolecule V) (c : m.Center) (i : Fin 4)
    {v : V} (h : LigandBranchReaches m c i v) : v ≠ c.1 := by
  rintro rfl
  rcases h with ⟨p, hp⟩
  exact hp (SimpleGraph.Walk.end_mem_support p)

/-! ### Sign algebra -/

/-- The product of two elements of `{1, -1}` lies in `{1, -1}`. -/
private theorem pm_one_mul {x y : ℝ} (hx : x = 1 ∨ x = -1) (hy : y = 1 ∨ y = -1) :
    x * y = 1 ∨ x * y = -1 := by
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · left; norm_num
  · right; norm_num
  · right; norm_num
  · left; norm_num

/-- The mirror factor `if b then -1 else 1` is `1` or `-1`. -/
private theorem mirrorFactor_pm_one (b : Bool) :
    (if b then (-1 : ℝ) else 1) = 1 ∨ (if b then (-1 : ℝ) else 1) = -1 := by
  cases b
  · left; rfl
  · right; rfl

/-- Two unequal elements of `{1, -1}` are negatives of each other. -/
private theorem eq_neg_of_ne_of_pm_one {x z : ℝ} (hx : x = 1 ∨ x = -1)
    (hz : z = 1 ∨ z = -1) (h : x ≠ z) : x = -z := by
  rcases hx with rfl | rfl <;> rcases hz with rfl | rfl
  · exact absurd rfl h
  · norm_num
  · norm_num
  · exact absurd rfl h

/-! ### Exact reduction to non-twin branch centers -/

/-- **Exact physical gauge completeness of rooted branch transport.**

`BranchTransport m cfg c i j b` holds if and only if there is an actual automorphism `e` fixing
the root `c` and carrying the ligand index `i` to `j`, whose local frame relation holds at every
center of the `i`-branch that does *not* carry physical terminal twins.

The forward direction restricts the full transport to the non-twin centers.  In the reverse
direction the finitely many reached centers where `e`'s full sign equation fails are, by
contraposition, exactly centers with physical twins; one twin pair is selected at each, the
resulting `TerminalTwinFamily` supplies an actual source correction `g` (fixing every center and
acting oddly precisely at the failing centers), and `e * g` is the required full transport. -/
theorem branchTransport_iff_orientationAtNonTwinCenters
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (i j : Fin 4) (b : Bool) :
    BranchTransport m cfg c i j b ↔
      ∃ e : m.Aut,
        m.centerPerm e c = c ∧
        m.ligandPermAt e c i = j ∧
          ∀ d : m.Center, LigandBranchReaches m c i d.1 →
            ¬ HasTerminalTwins m d →
              m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
                (if b then -1 else 1) * m.configurationSign cfg (m.centerPerm e d) := by
  classical
  constructor
  · rintro ⟨e, hc, hi, hsign⟩
    exact ⟨e, hc, hi, fun d hd _ => hsign d hd⟩
  · rintro ⟨e, hc, hi, hred⟩
    -- The finite set of branch centers where the *full* equation of `e` fails.
    let Bad : m.Center → Prop := fun d =>
      LigandBranchReaches m c i d.1 ∧
        ¬ (m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
          (if b then -1 else 1) * m.configurationSign cfg (m.centerPerm e d))
    -- Contraposition of the reduced hypothesis: a failing reached center carries twins.
    have hbadTwins : ∀ d : m.Center, Bad d → HasTerminalTwins m d := by
      intro d hd
      by_contra hnt
      exact hd.2 (hred d hd.1 hnt)
    -- The family of selected twin pairs, indexed by the failing centers.
    let ι : Type _ := { d : m.Center // Bad d }
    let idx : ι → m.Center := fun x => x.1
    have hidx : Function.Injective idx := fun _ _ hxy => Subtype.ext hxy
    let A : ι → V := fun x => Classical.choose (hbadTwins x.1 x.2)
    let B : ι → V := fun x => Classical.choose (Classical.choose_spec (hbadTwins x.1 x.2))
    have hpair : ∀ x : ι, TerminalTwinPair m (idx x) (A x) (B x) := fun x =>
      Classical.choose_spec (Classical.choose_spec (hbadTwins x.1 x.2))
    let fam : TerminalTwinFamily m idx A B := ⟨hpair, hidx⟩
    -- All failing centers, as a duplicate-free list.
    let l : List ι := (Finset.univ : Finset ι).toList
    have hl : l.Nodup := by
      dsimp only [l]
      exact Finset.nodup_toList _
    let g : m.Aut := fam.familyAut l
    -- The family fixes every distinguished center.
    have hgCenter : ∀ d : m.Center, m.centerPerm g d = d := fun d =>
      fam.centerPerm_familyAut_apply l d
    -- Non-failing centers are absent from the family list.
    have hnotMem : ∀ d : m.Center, ¬ Bad d → d ∉ l.map idx := by
      intro d hd hmem
      rw [List.mem_map] at hmem
      rcases hmem with ⟨x, _hx, hxd⟩
      exact hd (hxd ▸ x.2)
    -- Every failing center appears in the family list.
    have hmem : ∀ d : m.Center, (hd : Bad d) → d ∈ l.map idx := by
      intro d hd
      exact List.mem_map.mpr ⟨⟨d, hd⟩, by simp [l], rfl⟩
    refine ⟨e * g, ?_, ?_, ?_⟩
    · -- The corrected automorphism still fixes the root.
      rw [RootedTetrahedralBranchSymmetry.centerPerm_mul_apply m e g c, hgCenter c, hc]
    · -- The corrected automorphism still sends ligand index `i` to `j`.
      have hnotBadC : ¬ Bad c := by
        intro hb
        exact ligandBranchReaches_ne_root m c i hb.1 rfl
      have hnotMemC : c ∉ l.map idx := hnotMem c hnotBadC
      rw [m.ligandPermAt_mul (e := e) (f := g) (c := c), hgCenter c,
        fam.ligandPermAt_familyAut_of_not_mem l c hnotMemC, mul_one, hi]
    · -- The full sign equation at every center of the source branch.
      intro d hd
      by_cases hEq : m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
          (if b then -1 else 1) * m.configurationSign cfg (m.centerPerm e d)
      · -- `e` already satisfies the equation here: the family is locally trivial at `d`.
        have hnotBad : ¬ Bad d := fun hb => hb.2 hEq
        have hnotMemD : d ∉ l.map idx := hnotMem d hnotBad
        have hgOne : m.ligandPermAt g d = 1 :=
          fam.ligandPermAt_familyAut_of_not_mem l d hnotMemD
        rw [m.ligandPermAt_mul (e := e) (f := g) (c := d),
          RootedTetrahedralBranchSymmetry.centerPerm_mul_apply m e g d,
          hgCenter d, hgOne, mul_one]
        exact hEq
      · -- The equation fails here, so `d` is a twin center and is listed in the family.
        have hbad : Bad d := ⟨hd, hEq⟩
        let x : ι := ⟨d, hbad⟩
        have hxmem : x ∈ l := by simp [l]
        have hgAt : m.ligandPermAt g d =
            Equiv.swap (fam.twin x).twinSlotA (fam.twin x).twinSlotB := by
          simpa [g, idx] using fam.ligandPermAt_familyAut_at_index l hl x hxmem
        have hgHanded : permHandedness (m.ligandPermAt g d) = -1 := by
          rw [hgAt]
          exact TerminalTwinPair.permHandedness_swap_of_ne (fam.twin x).twinSlotA_ne_twinSlotB
        rw [m.ligandPermAt_mul (e := e) (f := g) (c := d),
          RootedTetrahedralBranchSymmetry.centerPerm_mul_apply m e g d,
          hgCenter d, permHandedness_mul, hgHanded]
        have hxpm : m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) = 1 ∨
            m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) = -1 :=
          pm_one_mul (permHandedness_eq_one_or_eq_neg_one (cfg d))
            (permHandedness_eq_one_or_eq_neg_one (m.ligandPermAt e d))
        have hzpm : (if b then (-1 : ℝ) else 1) *
              m.configurationSign cfg (m.centerPerm e d) = 1 ∨
            (if b then (-1 : ℝ) else 1) *
              m.configurationSign cfg (m.centerPerm e d) = -1 :=
          pm_one_mul (mirrorFactor_pm_one b)
            (permHandedness_eq_one_or_eq_neg_one (cfg (m.centerPerm e d)))
        have hneg : m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
            -((if b then (-1 : ℝ) else 1) *
              m.configurationSign cfg (m.centerPerm e d)) :=
          eq_neg_of_ne_of_pm_one hxpm hzpm hEq
        calc m.configurationSign cfg d * (permHandedness (m.ligandPermAt e d) * -1)
            = -(m.configurationSign cfg d * permHandedness (m.ligandPermAt e d)) := by ring
          _ = -(-((if b then (-1 : ℝ) else 1) *
                m.configurationSign cfg (m.centerPerm e d))) := by rw [hneg]
          _ = (if b then (-1 : ℝ) else 1) *
                m.configurationSign cfg (m.centerPerm e d) := by ring

/-! ### Specializations -/

/-- Proper (non-mirror) transport reduces exactly to the orientation relation at branch centers
without physical terminal twins. -/
theorem properTransport_iff_orientationAtNonTwinCenters
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) :
    ProperTransport m cfg c i j ↔
      ∃ e : m.Aut,
        m.centerPerm e c = c ∧
        m.ligandPermAt e c i = j ∧
          ∀ d : m.Center, LigandBranchReaches m c i d.1 →
            ¬ HasTerminalTwins m d →
              m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
                m.configurationSign cfg (m.centerPerm e d) := by
  simpa [ProperTransport] using
    branchTransport_iff_orientationAtNonTwinCenters m cfg c i j false

/-- Mirror (improper) transport reduces exactly to the orientation relation with a global sign
inversion at branch centers without physical terminal twins. -/
theorem mirrorTransport_iff_orientationAtNonTwinCenters
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center) (i j : Fin 4) :
    MirrorTransport m cfg c i j ↔
      ∃ e : m.Aut,
        m.centerPerm e c = c ∧
        m.ligandPermAt e c i = j ∧
          ∀ d : m.Center, LigandBranchReaches m c i d.1 →
            ¬ HasTerminalTwins m d →
              m.configurationSign cfg d * permHandedness (m.ligandPermAt e d) =
                -m.configurationSign cfg (m.centerPerm e d) := by
  simpa [MirrorTransport] using
    branchTransport_iff_orientationAtNonTwinCenters m cfg c i j true

/-- If every center of the source ligand branch carries physical terminal twins, then *every*
actual branch exchange fixing the root and carrying `i` to `j` is a proper transport, for every
configuration: no orientation constraint survives on such a branch. -/
theorem properTransport_of_rootFixing_of_allTerminalTwins
    (m : MultiCenterMolecule V) (cfg : m.Configuration) (c : m.Center)
    (e : m.Aut) (i j : Fin 4)
    (hc : m.centerPerm e c = c) (hij : m.ligandPermAt e c i = j)
    (htwins : ∀ d : m.Center, LigandBranchReaches m c i d.1 → HasTerminalTwins m d) :
    ProperTransport m cfg c i j := by
  rw [properTransport_iff_orientationAtNonTwinCenters]
  refine ⟨e, hc, hij, ?_⟩
  intro d hd hnt
  exact absurd (htwins d hd) hnt

/-! ### Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.RootedBranchTerminalTwinCompletion.HasTerminalTwins
assert_kernel_only TetraStereo.OneCenter.RootedBranchTerminalTwinCompletion.ligandBranchReaches_ne_root
assert_kernel_only TetraStereo.OneCenter.RootedBranchTerminalTwinCompletion.branchTransport_iff_orientationAtNonTwinCenters
assert_kernel_only TetraStereo.OneCenter.RootedBranchTerminalTwinCompletion.properTransport_iff_orientationAtNonTwinCenters
assert_kernel_only TetraStereo.OneCenter.RootedBranchTerminalTwinCompletion.mirrorTransport_iff_orientationAtNonTwinCenters
assert_kernel_only TetraStereo.OneCenter.RootedBranchTerminalTwinCompletion.properTransport_of_rootFixing_of_allTerminalTwins

end

end RootedBranchTerminalTwinCompletion
end OneCenter
end TetraStereo
