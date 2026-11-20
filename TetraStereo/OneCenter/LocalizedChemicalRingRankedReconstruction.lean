import TetraStereo.OneCenter.DeclarativeCIPBoundaryComponentReconstruction
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! Reconstruction witnesses can be chosen with a finite deletion rank. At the witness of
an atom, every other atom still in its residual component has a strictly greater rank.
This is structural data for an orientation induction; no orientation or label semantics is
assumed. It does not require the path equivalence to descend on every path. -/
namespace TetraStereo.OneCenter.LocalizedChemicalRingRankedReconstruction

open RetainedCoherentSymmetry RetainedRingSymmetryReconstruction BoundaryComponentReconstruction
noncomputable section
open scoped Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem component_weaken {m : MoleculeGraph V} {B C : List V} {x y : V}
    (subset : B ⊆ C) (member : InComponent m C x y) : InComponent m B x y := by
  have mono : residualGraph m C ≤ residualGraph m B := by
    intro a b edge
    exact ⟨fun ha => edge.1 (subset ha), fun hb => edge.2.1 (subset hb), edge.2.2⟩
  exact ⟨fun hx => member.1 (subset hx), member.2.mono mono⟩

/-- A witnessed isomorphism with a global finite rank controlling each witness's remaining
component. The boundary used here excludes only the witness's final vertex. -/
structure RankedWitnessIso {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) where
  iso : BoundaryComponentIso m Bs Bt v w
  rank : V → Nat
  witnessPath : ∀ x, InComponent m Bs v x →
    ∃ p : {p : List V // ResidualObsPath m Bs v p},
      pathTerminal p.1 p.2.nonempty = x ∧ (e.toEquiv p).1 = p.1.map iso.toFun ∧
      ∀ y, InComponent m (Bs ++ p.1.dropLast) x y → y ≠ x → rank x < rank y

def RankedWitnessIso.toWitnessed {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    {e : ResidualPathTreeEquiv m Bs Bt v w} (ranked : RankedWitnessIso e) :
    WitnessedBoundaryComponentIso e where
  iso := ranked.iso
  witnessPath := by
    intro x hx
    obtain ⟨p, terminal, image, _⟩ := ranked.witnessPath x hx
    exact ⟨p, terminal, image⟩

def glueRank {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (D : ChildGlueData m Bs Bt v w) (ranks : Touched m Bs v → V → Nat) (x : V) : Nat :=
  if h : ∃ a, InComponent m (Bs ++ [v]) (D.src a) x then ranks (Classical.choose h) x + 1 else 0

theorem glueRank_child {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (D : ChildGlueData m Bs Bt v w) (ranks : Touched m Bs v → V → Nat)
    (a : Touched m Bs v) (x : V) (member : InComponent m (Bs ++ [v]) (D.src a) x) :
    glueRank D ranks x = ranks a x + 1 := by
  have found : ∃ b, InComponent m (Bs ++ [v]) (D.src b) x := ⟨a, member⟩
  rw [glueRank, dif_pos found]
  have owner : Classical.choose found = a := D.src_owner_unique (Classical.choose_spec found) member
  rw [owner]

theorem glueRank_entry {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (D : ChildGlueData m Bs Bt v w) (ranks : Touched m Bs v → V → Nat) :
    glueRank D ranks v = 0 := by
  apply dif_neg
  rintro ⟨a, member⟩
  exact inComponent_not_mem m member (by simp)

/-- The existing component matching construction admits a choice of witnesses with a
strict deletion rank. Child component ranks are lifted by one under the same glued map. -/
theorem exists_rankedWitnessIso_le (m : MoleculeGraph V) (n : Nat) :
    ∀ {Bs Bt : List V} {v w : V} (e : ResidualPathTreeEquiv m Bs Bt v w), v ∉ Bs →
      compCard m Bs v + compCard m Bt w ≤ n → Nonempty (RankedWitnessIso e) := by
  induction n with
  | zero =>
      intro Bs Bt v w e hv bound
      have := compCard_pos m hv
      omega
  | succ n ih =>
      intro Bs Bt v w e hv bound
      have hw := target_root_outside e hv
      have hchild : ∀ x : Entries m Bs v,
          Nonempty (RankedWitnessIso (childResidualPathTreeEquiv e hv x.2)) := by
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
          RankedWitnessIso (childResidualPathTreeEquiv e hv x.2) := fun x => Classical.choice (hchild x)
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
        refine ⟨⟨[v], obs_singleton m hv⟩, pathTerminal_singleton v, ?_, ?_⟩
        · show (e.toEquiv ⟨[v], obs_singleton m hv⟩).1 = [v].map D.toFun
          rw [singleton_image e hv, List.map_cons, List.map_nil, D.toFun_entry]
        · intro y member different
          have member' : InComponent m Bs v y := by simpa using member
          obtain ⟨a, ha⟩ := D.exists_src_owner hv member' different
          rw [glueRank_entry, glueRank_child D ranks a y ha]
          omega
      · obtain ⟨a, ha⟩ := D.exists_src_owner hv hx hxv
        obtain ⟨q, terminal, image, ranked⟩ := (W (wit a)).witnessPath x ha
        refine ⟨⟨v :: q.1, obs_cons_child m hv (wit a).2.1 (wit a).2.2 q.2⟩,
          (pathTerminal_cons_ne v q.1 q.2.nonempty).trans terminal, ?_, ?_⟩
        · show (e.toEquiv ⟨v :: q.1, obs_cons_child m hv (wit a).2.1 (wit a).2.2 q.2⟩).1 =
            (v :: q.1).map D.toFun
          rw [childPathMap_parent_image e hv (wit a).2 q, List.map_cons, D.toFun_entry]
          congr 1
          change (childPathMap e hv (wit a).2 q).1 = q.1.map (W (wit a)).iso.toFun at image
          rw [image]
          exact List.map_congr_left fun u hu =>
            (D.toFun_eq_child a (obsPath_mem_inComponent q.2 hu)).symm
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

theorem exists_rankedWitnessIso {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (outside : v ∉ Bs) : Nonempty (RankedWitnessIso e) :=
  exists_rankedWitnessIso_le m _ e outside le_rfl

/-- Induction at realizing occurrence histories. The induction hypothesis covers every
other vertex still reachable after the witness prefix has been deleted. No hypothesis about
the original equivalence on arbitrary permutation-mapped paths is needed. -/
theorem RankedWitnessIso.induction {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    {e : ResidualPathTreeEquiv m Bs Bt v w} (ranked : RankedWitnessIso e)
    (P : V → Prop)
    (step : ∀ x, InComponent m Bs v x →
      ∀ p : {p : List V // ResidualObsPath m Bs v p},
        pathTerminal p.1 p.2.nonempty = x → (e.toEquiv p).1 = p.1.map ranked.iso.toFun →
        (∀ y, InComponent m (Bs ++ p.1.dropLast) x y → y ≠ x → P y) → P x) :
    ∀ x, InComponent m Bs v x → P x := by
  let maximum := Finset.univ.sup ranked.rank
  have bound (x : V) : ranked.rank x ≤ maximum := Finset.le_sup (Finset.mem_univ x)
  intro x member
  generalize measureEq : maximum - ranked.rank x = measure
  induction measure using Nat.strong_induction_on generalizing x with
  | h measure ih =>
      obtain ⟨p, terminal, image, ordered⟩ := ranked.witnessPath x member
      apply step x member p terminal image
      intro y remaining different
      have greater := ordered y remaining different
      have residual : InComponent m Bs x y :=
        component_weaken (by intro z hz; exact List.mem_append_left _ hz) remaining
      have original : InComponent m Bs v y := ⟨member.1, member.2.trans residual.2⟩
      exact ih (maximum - ranked.rank y) (by have := bound y; omega) y original rfl

end
end TetraStereo.OneCenter.LocalizedChemicalRingRankedReconstruction

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedReconstruction.component_weaken
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedReconstruction.exists_rankedWitnessIso_le
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedReconstruction.exists_rankedWitnessIso
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRankedReconstruction.RankedWitnessIso.induction
