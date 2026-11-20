import TetraStereo.OneCenter.LocalizedChemicalRingRankedReconstruction
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
The finite reconstruction can choose witnesses whose earlier path vertices have LOWER
rank and whose other remaining component vertices have HIGHER rank. The existing rank
interface records only the second clause. The first clause identifies exactly which
boundary centers may be changed later in a physical correction induction; fixing a
boundary atom is not mistaken for preserving its frame orientation.

This is a strengthening of the general finite construction, not an additional molecule
restriction. It supplies no missing-label semantics or physical correcting symmetry.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingPrefixRankedReconstruction

open RetainedCoherentSymmetry RetainedRingSymmetryReconstruction BoundaryComponentReconstruction
open LocalizedChemicalRingRankedReconstruction
noncomputable section
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Both sides of the witness's deletion order are retained under the same isomorphism. -/
structure PrefixRankedWitnessIso {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) where
  iso : BoundaryComponentIso m Bs Bt v w
  rank : V → Nat
  witnessPath : ∀ x, InComponent m Bs v x →
    ∃ p : {p : List V // ResidualObsPath m Bs v p},
      pathTerminal p.1 p.2.nonempty = x ∧ (e.toEquiv p).1 = p.1.map iso.toFun ∧
      (∀ y ∈ p.1.dropLast, rank y < rank x) ∧
      ∀ y, InComponent m (Bs ++ p.1.dropLast) x y → y ≠ x → rank x < rank y

def PrefixRankedWitnessIso.toRanked {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    {e : ResidualPathTreeEquiv m Bs Bt v w} (ranked : PrefixRankedWitnessIso e) :
    RankedWitnessIso e where
  iso := ranked.iso
  rank := ranked.rank
  witnessPath := by
    intro x hx
    obtain ⟨p, terminal, image, _, remaining⟩ := ranked.witnessPath x hx
    exact ⟨p, terminal, image, remaining⟩

/-- All finite faithful residual path equivalences admit the strengthened reconstruction. -/
theorem exists_prefixRankedWitnessIso_le (m : MoleculeGraph V) (n : Nat) :
    ∀ {Bs Bt : List V} {v w : V} (e : ResidualPathTreeEquiv m Bs Bt v w), v ∉ Bs →
      compCard m Bs v + compCard m Bt w ≤ n → Nonempty (PrefixRankedWitnessIso e) := by
  induction n with
  | zero =>
      intro Bs Bt v w e hv bound
      have := compCard_pos m hv
      omega
  | succ n ih =>
      intro Bs Bt v w e hv bound
      have hw := target_root_outside e hv
      have hchild : ∀ x : Entries m Bs v,
          Nonempty (PrefixRankedWitnessIso (childResidualPathTreeEquiv e hv x.2)) := by
        intro x
        have hy := childOf_adj e hv x.2
        have h1 := compCard_child_le m hv
          (show (residualGraph m Bs).Adj v x.1 from ⟨hv, x.2.2, x.2.1⟩)
        have h2 := compCard_child_le m hw
          (show (residualGraph m Bt).Adj w (childOf e hv x.1) from ⟨hw, hy.2, hy.1⟩)
        exact ih (childResidualPathTreeEquiv e hv x.2)
          (by rw [not_mem_append_singleton]; exact ⟨x.2.2, (ne_of_adj m x.2.1).symm⟩)
          (by omega)
      let W : ∀ x : Entries m Bs v,
          PrefixRankedWitnessIso (childResidualPathTreeEquiv e hv x.2) := fun x => Classical.choice (hchild x)
      obtain ⟨f, hf⟩ := exists_component_bijection_of_entryEquiv
        (entryOwner m Bs v) (entryOwner m Bt w) (childEntryEquiv e hv)
        (entryOwner_fiber_pos m Bs v) (entryOwner_fiber_pos m Bt w)
        (fun x => entryOwner_fiber_card_eq x (childEntryEquiv e hv x) (W x).iso)
      choose wit hwitE hwitF using hf
      let D : ChildGlueData m Bs Bt v w :=
        { pair := f
          src := fun a => (wit a).1
          tgt := fun a => childOf e hv (wit a).1
          src_entry := fun a => (wit a).2
          tgt_entry := fun a => childOf_adj e hv (wit a).2
          src_comp := fun a => congrArg Subtype.val (hwitE a)
          tgt_comp := fun a => congrArg Subtype.val (hwitF a)
          iso := fun a => (W (wit a)).iso }
      let ranks : Touched m Bs v → V → Nat := fun a => (W (wit a)).rank
      refine ⟨⟨D.glue hv hw e.len_eq (entry_atomZ_eq e hv) (entry_atomMass_eq e hv)
        (entry_formalCharge_eq e hv) (entry_boundary_eq e hv), glueRank D ranks, ?_⟩⟩
      intro x hx
      by_cases hxv : x = v
      · subst x
        refine ⟨⟨[v], obs_singleton m hv⟩, pathTerminal_singleton v, ?_, ?_, ?_⟩
        · show (e.toEquiv ⟨[v], obs_singleton m hv⟩).1 = [v].map D.toFun
          rw [singleton_image e hv, List.map_cons, List.map_nil, D.toFun_entry]
        · simp
        · intro y member different
          have member' : InComponent m Bs v y := by simpa using member
          obtain ⟨a, ha⟩ := D.exists_src_owner hv member' different
          rw [glueRank_entry, glueRank_child D ranks a y ha]
          omega
      · obtain ⟨a, ha⟩ := D.exists_src_owner hv hx hxv
        obtain ⟨q, terminal, image, previous, ranked⟩ := (W (wit a)).witnessPath x ha
        refine ⟨⟨v :: q.1, obs_cons_child m hv (wit a).2.1 (wit a).2.2 q.2⟩,
          (pathTerminal_cons_ne v q.1 q.2.nonempty).trans terminal, ?_, ?_, ?_⟩
        · show (e.toEquiv ⟨v :: q.1, obs_cons_child m hv (wit a).2.1 (wit a).2.2 q.2⟩).1 =
            (v :: q.1).map D.toFun
          rw [childPathMap_parent_image e hv (wit a).2 q, List.map_cons, D.toFun_entry]
          congr 1
          change (childPathMap e hv (wit a).2 q).1 = q.1.map (W (wit a)).iso.toFun at image
          rw [image]
          exact List.map_congr_left fun u hu =>
            (D.toFun_eq_child a (obsPath_mem_inComponent q.2 hu)).symm
        · intro y member
          rw [List.dropLast_cons_of_ne_nil q.2.nonempty] at member
          rcases List.mem_cons.mp member with entry | before
          · subst y
            rw [glueRank_entry, glueRank_child D ranks a x ha]
            omega
          · have memberChild := obsPath_mem_inComponent q.2 ((List.dropLast_sublist q.1).mem before)
            rw [glueRank_child D ranks a y memberChild, glueRank_child D ranks a x ha]
            exact Nat.add_lt_add_right (previous y before) 1
        · intro y member different
          have cut : InComponent m ((Bs ++ [v]) ++ q.1.dropLast) x y := by
            simpa only [List.dropLast_cons_of_ne_nil q.2.nonempty, List.cons_append,
              List.append_assoc, List.singleton_append] using member
          have weakened : InComponent m (Bs ++ [v]) x y :=
            component_weaken (by intro z hz; exact List.mem_append_left _ hz) cut
          have sameChild : InComponent m (Bs ++ [v]) (D.src a) y :=
            ⟨ha.1, ha.2.trans weakened.2⟩
          rw [glueRank_child D ranks a x ha, glueRank_child D ranks a y sameChild]
          exact Nat.add_lt_add_right (ranked y cut different) 1

theorem exists_prefixRankedWitnessIso {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (outside : v ∉ Bs) : Nonempty (PrefixRankedWitnessIso e) :=
  exists_prefixRankedWitnessIso_le m _ e outside le_rfl


omit [Fintype V] [DecidableEq V] in
/-- A center at least as late as the current witness cannot be an earlier prefix vertex.
Only the original fixed boundary remains exceptional. -/
theorem outside_extended_boundary_of_rank {B : List V}
    {rank : V → Nat} {path : List V} {x y : V}
    (prefixLower : ∀ z ∈ path.dropLast, rank z < rank x)
    (outside : y ∉ B) (later : rank x ≤ rank y) : y ∉ B ++ path.dropLast := by
  intro member
  rcases List.mem_append.mp member with old | earlier
  · exact outside old
  · have := prefixLower y earlier
    omega

end
end TetraStereo.OneCenter.LocalizedChemicalRingPrefixRankedReconstruction

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPrefixRankedReconstruction.PrefixRankedWitnessIso.toRanked
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPrefixRankedReconstruction.exists_prefixRankedWitnessIso_le
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPrefixRankedReconstruction.exists_prefixRankedWitnessIso
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPrefixRankedReconstruction.outside_extended_boundary_of_rank
