import TetraStereo.OneCenter.LocalizedChemicalRingForcedComponentMatching
import TetraStereo.OneCenter.LocalizedChemicalRingColoredReconstruction
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-!
Any prescribed residual path correspondence extends to a single witnessed molecular
component isomorphism. The chosen next entry is forced into the component matching;
all other components retain their usual realizing witnesses. Induction on the prescribed
path length retains its entire image, rather than only its endpoint.

The resulting isomorphism may differ from a previous reconstruction. Physical signs
of that previous map are not asserted to survive this choice.
-/
namespace TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathReconstruction

open RetainedCoherentSymmetry RetainedRingSymmetryReconstruction BoundaryComponentReconstruction
open LocalizedChemicalRingForcedComponentMatching LocalizedChemicalRingColoredReconstruction

noncomputable section
open scoped Classical
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A prescribed path can be realized without losing the one-witness-per-atom
property used to transport terminal colors and the inherited reference. -/
theorem exists_forced_witness_le (m : MoleculeGraph V) (n : Nat) :
    ∀ {Bs Bt : List V} {v w : V} (e : ResidualPathTreeEquiv m Bs Bt v w)
      (_outside : v ∉ Bs) (p : List V) (valid : ResidualObsPath m Bs v p),
      p.length ≤ n → ∃ W : WitnessedBoundaryComponentIso e,
        (e.toEquiv ⟨p, valid⟩).1 = p.map W.iso.toFun := by
  induction n with
  | zero =>
      intro Bs Bt v w e outside p valid bound
      have empty : p = [] := List.eq_nil_of_length_eq_zero (Nat.eq_zero_of_le_zero bound)
      exact False.elim (valid.nonempty empty)
  | succ n ih =>
      intro Bs Bt v w e outside p valid bound
      cases p with
      | nil => exact False.elim (valid.nonempty rfl)
      | cons head rest =>
          have atEntry : head = v := by simpa only [List.head?_cons, Option.some.injEq] using valid.head
          subst head
          cases rest with
          | nil =>
              let W := witnessedBoundaryComponentIso e outside
              refine ⟨W, ?_⟩
              rw [singleton_image e outside, List.map_cons, List.map_nil, W.iso.entry]
          | cons x tail =>
              let chosen : Entries m Bs v :=
                ⟨x, valid.chain.1, valid.outside x (by simp)⟩
              let q : {q : List V // ResidualObsPath m (Bs ++ [v]) x q} :=
                ⟨x :: tail, obs_tail m valid (by simp)⟩
              have childOutside (entry : Entries m Bs v) : entry.1 ∉ Bs ++ [v] := by
                rw [not_mem_append_singleton]
                exact ⟨entry.2.2, (ne_of_adj m entry.2.1).symm⟩
              obtain ⟨Q, imageQ⟩ := ih (childResidualPathTreeEquiv e outside chosen.2)
                (childOutside chosen) q.1 q.2 (by simpa only [q, List.length_cons] using Nat.le_of_succ_le_succ bound)
              let original : ∀ entry : Entries m Bs v,
                  WitnessedBoundaryComponentIso (childResidualPathTreeEquiv e outside entry.2) :=
                fun entry => witnessedBoundaryComponentIso
                  (childResidualPathTreeEquiv e outside entry.2) (childOutside entry)
              let W := Function.update original chosen Q
              obtain ⟨f, wit, _, chosenWitness, owners⟩ := exists_component_bijection_forced_entry
                (entryOwner m Bs v) (entryOwner m Bt w) (childEntryEquiv e outside)
                (entryOwner_fiber_pos m Bs v) (entryOwner_fiber_pos m Bt w)
                (fun entry => entryOwner_fiber_card_eq entry (childEntryEquiv e outside entry)
                  (W entry).iso) chosen
              let D : ChildGlueData m Bs Bt v w :=
                { pair := f
                  src := fun a => (wit a).1
                  tgt := fun a => childOf e outside (wit a).1
                  src_entry := fun a => (wit a).2
                  tgt_entry := fun a => childOf_adj e outside (wit a).2
                  src_comp := fun a => congrArg Subtype.val (owners a).1
                  tgt_comp := fun a => congrArg Subtype.val (owners a).2
                  iso := fun a => (W (wit a)).iso }
              let whole : WitnessedBoundaryComponentIso e :=
                { iso := D.glue outside (target_root_outside e outside) e.len_eq
                    (entry_atomZ_eq e outside) (entry_atomMass_eq e outside)
                    (entry_formalCharge_eq e outside) (entry_boundary_eq e outside)
                  witnessPath := by
                    intro atom member
                    by_cases same : atom = v
                    · refine ⟨⟨[v], obs_singleton m outside⟩,
                        (pathTerminal_singleton v).trans same.symm, ?_⟩
                      show (e.toEquiv ⟨[v], obs_singleton m outside⟩).1 = [v].map D.toFun
                      rw [singleton_image e outside, List.map_cons, List.map_nil, D.toFun_entry]
                    · obtain ⟨owner, atOwner⟩ := D.exists_src_owner outside member same
                      obtain ⟨path, terminal, image⟩ := (W (wit owner)).witnessPath atom atOwner
                      refine ⟨⟨v :: path.1,
                        obs_cons_child m outside (wit owner).2.1 (wit owner).2.2 path.2⟩,
                        (pathTerminal_cons_ne v path.1 path.2.nonempty).trans terminal, ?_⟩
                      show (e.toEquiv ⟨v :: path.1,
                        obs_cons_child m outside (wit owner).2.1 (wit owner).2.2 path.2⟩).1 =
                        (v :: path.1).map D.toFun
                      rw [childPathMap_parent_image e outside (wit owner).2 path,
                        List.map_cons, D.toFun_entry]
                      congr 1
                      change (childPathMap e outside (wit owner).2 path).1 =
                        path.1.map (W (wit owner)).iso.toFun at image
                      rw [image]
                      exact List.map_congr_left fun u hu =>
                        (D.toFun_eq_child owner (obsPath_mem_inComponent path.2 hu)).symm }
              refine ⟨whole, ?_⟩
              change (e.toEquiv ⟨v :: q.1, valid⟩).1 = (v :: q.1).map D.toFun
              rw [childPathMap_parent_image e outside chosen.2 q, List.map_cons, D.toFun_entry]
              congr 1
              change (childPathMap e outside chosen.2 q).1 = q.1.map Q.iso.toFun at imageQ
              rw [imageQ]
              apply List.map_congr_left
              intro u member
              have atChosen : InComponent m (Bs ++ [v]) (D.src (entryOwner m Bs v chosen)) u := by
                change InComponent m (Bs ++ [v]) (wit (entryOwner m Bs v chosen)).1 u
                rw [chosenWitness]
                exact obsPath_mem_inComponent q.2 member
              have agreement := D.toFun_eq_child (entryOwner m Bs v chosen) atChosen
              have childAgreement : (W (wit (entryOwner m Bs v chosen))).iso.toFun u =
                  Q.iso.toFun u := by
                rw [chosenWitness]
                simp only [W, Function.update_self]
              exact childAgreement.symm.trans agreement.symm

/-- No prescribed correspondence or isomorphism is supplied beyond the actual path-tree
image: every finite residual path has a full witnessed extension. -/
theorem exists_forced_witness {m : MoleculeGraph V} {Bs Bt : List V} {v w : V}
    (e : ResidualPathTreeEquiv m Bs Bt v w) (outside : v ∉ Bs)
    (p : {p : List V // ResidualObsPath m Bs v p}) :
    ∃ W : WitnessedBoundaryComponentIso e, (e.toEquiv p).1 = p.1.map W.iso.toFun :=
  exists_forced_witness_le m p.1.length e outside p.1 p.2 le_rfl

/-- With one common boundary, the prescribed path is realized by an actual molecular
automorphism preserving every terminal color seen by the path equivalence. -/
theorem exists_forced_color_preserving_aut {C : Type*}
    {m : MoleculeGraph V} {B : List V} {a b : V}
    (e : ResidualPathTreeEquiv m B B a b) (outside : a ∉ B)
    (color : V → C) (preserved : TerminalColorPreserved e color)
    (p : {p : List V // ResidualObsPath m B a p}) :
    ∃ π : Equiv.Perm V, m.IsAutomorphism π ∧ (∀ z ∈ B, π z = z) ∧
      π a = b ∧ (∀ z, color (π z) = color z) ∧
      (∀ z, ¬ InComponent m B a z → ¬ InComponent m B b z → π z = z) ∧
      (e.toEquiv p).1 = p.1.map π := by
  obtain ⟨W, forced⟩ := exists_forced_witness e outside p
  have outsideB := target_root_outside e outside
  let π := componentExchangePerm W.iso outside outsideB
  refine ⟨π, componentExchangePerm_isAutomorphism W.iso outside outsideB, ?_, ?_, ?_, ?_, ?_⟩
  · intro z present
    rw [componentExchangePerm_apply]
    exact exchange_of_none W.iso (fun h => inComponent_not_mem m h present)
      (fun h => inComponent_not_mem m h present)
  · rw [componentExchangePerm_apply, exchange_of_a W.iso (inComponent_self m outside)]
    exact W.iso.entry
  · intro z
    exact componentExchange_color_eq e W color preserved z
  · intro z left right
    exact exchange_of_none W.iso left right
  · rw [forced]
    apply List.map_congr_left
    intro z present
    exact (exchange_of_a W.iso (obsPath_mem_inComponent p.2 present)).symm

end
end TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathReconstruction

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathReconstruction.exists_forced_witness_le
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathReconstruction.exists_forced_witness
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingPrescribedPathReconstruction.exists_forced_color_preserving_aut
