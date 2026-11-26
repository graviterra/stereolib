import TetraStereo.Engine.RingOxaziridineNitrogen
import TetraStereo.Engine.RingSecondShellDecision

/-! Constitutional O > ring-carbon > N-alkyl-carbon order for the recognized
oxaziridine graph class. The order is derived from records and physical bonds. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOxaziridineRootOrder
open OneCenter
open RingOxaziridineNitrogen
open RingAtomicNeighborOrder (atomicNumber neighbors)
open RingSecondShellDecision (adjacent shell signature)
attribute [local instance] lexOrd

private theorem atomic_of_good (m : RawMolecule) (n : Nat) (z : Element)
    (good : atomIs m n z = true) : atomicNumber m n = z.atomicNumber := by
  cases h : m.atoms[n]? with
  | none => simp [atomIs,h] at good
  | some a =>
    have facts : (a.element = z ∧ a.charge = 0) ∧ (!a.aromatic) = true := by
      simpa only [atomIs,h,Option.any_some,Bool.and_eq_true,beq_iff_eq] using good
    have eq : a.element = z := facts.1.1
    simp [atomicNumber,h,eq]

private theorem sorted_desc (xs : List Nat) : (RingAtomicSecondShell.sorted xs).Pairwise (· ≥ ·) :=
  (List.pairwise_mergeSort (le := fun a b : Nat => decide (b ≤ a))
    (fun _ _ _ h k => decide_eq_true (le_trans (of_decide_eq_true k) (of_decide_eq_true h)))
    (fun a b => by simpa using le_total b a) xs).imp (fun h => of_decide_eq_true h)

private theorem shell_mem (m : RawMolecule) (n a z : Nat) :
    z ∈ shell m n a ↔ ∃ v ∈ adjacent m n a, atomicNumber m v = z := by
  unfold shell RingAtomicSecondShell.sorted
  rw [(List.mergeSort_perm ..).mem_iff]
  exact List.mem_map

private theorem shell_dominates (m : RawMolecule) (n c k : Nat)
    (oxygen : 8 ∈ shell m n c) (small : ∀ z ∈ shell m n k, z ≤ 6) :
    shell m n k < shell m n c := by
  have sorted := sorted_desc ((adjacent m n c).map (atomicNumber m))
  change (shell m n c).Pairwise (· ≥ ·) at sorted
  cases hc : shell m n c with
  | nil => simp [hc] at oxygen
  | cons a as =>
    have high : 8 ≤ a := by
      rw [hc] at oxygen sorted
      rcases List.mem_cons.mp oxygen with rfl | mem
      · exact le_rfl
      · exact (List.pairwise_cons.mp sorted).1 8 mem
    cases hk : shell m n k with
    | nil => exact List.Lex.nil
    | cons b bs =>
      have low : b ≤ 6 := small b (by simp [hk])
      exact List.Lex.rel (by omega)

/-- The recognized graph provides its own strict descending two-shell order. -/
theorem strict_signatures (m : RawMolecule) (n : Fin m.atomCount)
    (pattern : Pattern (fun v z => atomIs m v.val z)
      (fun (u v : Fin m.atomCount) => m.bondOrder u.val v.val) n) :
    ∃ o c k : Fin m.atomCount,
      o ≠ c ∧ o ≠ k ∧ c ≠ k ∧
      (∀ v : Fin m.atomCount, 0 < m.bondOrder n.val v.val ↔ v = o ∨ v = c ∨ v = k) ∧
      signature m n.val k.val < signature m n.val c.val ∧
      signature m n.val c.val < signature m n.val o.val ∧
      atomIs m o.val .O = true ∧ atomIs m c.val .C = true ∧ atomIs m k.val .C = true ∧
      m.bondOrder o.val c.val = 1 := by
  obtain ⟨gn,o,no,go,nob,c,nc,oc,gc,ncb,ocb,k,nk,ok,ck,gk,nkb,ns,os,cs,ks,external⟩ := pattern
  dsimp only at ocb
  have zo := atomic_of_good m o.val .O go
  have zc := atomic_of_good m c.val .C gc
  have zk := atomic_of_good m k.val .C gk
  have ringO : 8 ∈ shell m n.val c.val := by
    apply (shell_mem m n.val c.val 8).mpr
    refine ⟨o.val, ?_, zo⟩
    simp only [adjacent,List.mem_filter,List.mem_range,Bool.and_eq_true,bne_iff_ne,decide_eq_true_eq]
    exact ⟨o.isLt,fun h => no (Fin.ext h.symm),by rw [m.bondOrder_symm,ocb]; decide⟩
  have small : ∀ z ∈ shell m n.val k.val, z ≤ 6 := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := (shell_mem m n.val k.val z).mp hz
    simp only [adjacent,List.mem_filter,List.mem_range,Bool.and_eq_true,bne_iff_ne,decide_eq_true_eq] at hv
    rcases external ⟨v,hv.1⟩ hv.2.2 with eq | carbon | hydrogen
    · exact (hv.2.1 (congrArg Fin.val eq)).elim
    · rw [atomic_of_good m v .C carbon]; decide
    · rw [atomic_of_good m v .H hydrogen]; decide
  refine ⟨o,c,k,oc,ok,ck,ns,?_,?_,go,gc,gk,ocb⟩
  · simp only [signature,zk,zc]
    exact List.Lex.cons (List.Lex.rel (shell_dominates m n.val c.val k.val ringO small))
  · simp only [signature,zc,zo]
    exact List.Lex.rel (List.Lex.rel (by decide : (6:Nat) < 8))

/-- The graph-only neighbor inventory is the derived O, ring-C, alkyl-C row,
strictly descending in the same physical signatures used by the public reader. -/
theorem descending_row_with_roles (m : RawMolecule) (n : Fin m.atomCount)
    (pattern : Pattern (fun v z => atomIs m v.val z)
      (fun (u v : Fin m.atomCount) => m.bondOrder u.val v.val) n) :
    ∃ o c k : Nat, (neighbors m n.val).Perm [o,c,k] ∧
      ([o,c,k].map (signature m n.val)).Pairwise (· > ·) ∧
      atomIs m o .O = true ∧ atomIs m c .C = true ∧ atomIs m k .C = true ∧
      m.bondOrder o c = 1 := by
  obtain ⟨o,c,k,oc,ok,ck,all,kc,co,go,gc,gk,ocb⟩ := strict_signatures m n pattern
  have oc' : o.val ≠ c.val := fun h => oc (Fin.ext h)
  have ok' : o.val ≠ k.val := fun h => ok (Fin.ext h)
  have ck' : c.val ≠ k.val := fun h => ck (Fin.ext h)
  refine ⟨o.val,c.val,k.val,?_,?_,go,gc,gk,ocb⟩
  · have nd : (neighbors m n.val).Nodup :=
      (RingStereoSiblingPass.legal_order (atomicNumber m) _).perm.nodup_iff.mpr
        ((List.nodup_range).filter _)
    apply (List.perm_ext_iff_of_nodup nd (by simp [oc',ok',ck'])).mpr
    intro v
    rw [RingAtomicNeighborOrder.mem_neighbors]
    simp only [List.mem_cons,List.mem_nil_iff,or_false]
    constructor
    · rintro ⟨bound,bond⟩
      rcases (all ⟨v,bound⟩).mp bond with eq | eq | eq
      · exact Or.inl (congrArg Fin.val eq)
      · exact Or.inr (Or.inl (congrArg Fin.val eq))
      · exact Or.inr (Or.inr (congrArg Fin.val eq))
    · rintro (rfl | rfl | rfl)
      · exact ⟨o.isLt,(all o).mpr (Or.inl rfl)⟩
      · exact ⟨c.isLt,(all c).mpr (Or.inr (Or.inl rfl))⟩
      · exact ⟨k.isLt,(all k).mpr (Or.inr (Or.inr rfl))⟩
  · simpa [List.pairwise_cons] using
      And.intro (And.intro co (lt_trans kc co)) kc

/-- The strict row alone, when witness roles are not needed. -/
theorem descending_row (m : RawMolecule) (n : Fin m.atomCount)
    (pattern : Pattern (fun v z => atomIs m v.val z)
      (fun (u v : Fin m.atomCount) => m.bondOrder u.val v.val) n) :
    ∃ o c k : Nat, (neighbors m n.val).Perm [o,c,k] ∧
      ([o,c,k].map (signature m n.val)).Pairwise (· > ·) := by
  obtain ⟨o,c,k,perm,strict,_⟩ := descending_row_with_roles m n pattern
  exact ⟨o,c,k,perm,strict⟩

/-- Executable recognition also records which physical IDs fill each role. -/
theorem descending_row_with_roles_of_constrained (m : RawMolecule) (n : Nat)
    (recognized : constrainedRaw m n = true) :
    ∃ o c k : Nat, (neighbors m n).Perm [o,c,k] ∧
      ([o,c,k].map (signature m n)).Pairwise (· > ·) ∧
      atomIs m o .O = true ∧ atomIs m c .C = true ∧ atomIs m k .C = true ∧
      m.bondOrder o c = 1 := by
  unfold constrainedRaw at recognized
  split at recognized
  · rename_i bound
    exact descending_row_with_roles m ⟨n,bound⟩ (of_decide_eq_true recognized)
  · contradiction

/-- Executable recognition supplies the physical row without a caller ranking. -/
theorem descending_row_of_constrained (m : RawMolecule) (n : Nat)
    (recognized : constrainedRaw m n = true) :
    ∃ o c k : Nat, (neighbors m n).Perm [o,c,k] ∧
      ([o,c,k].map (signature m n)).Pairwise (· > ·) := by
  unfold constrainedRaw at recognized
  split at recognized
  · rename_i bound
    exact descending_row m ⟨n,bound⟩ (of_decide_eq_true recognized)
  · contradiction

end TetraStereo.Engine.RingOxaziridineRootOrder
assert_kernel_only TetraStereo.Engine.RingOxaziridineRootOrder.descending_row_of_constrained
