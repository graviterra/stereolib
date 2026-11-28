import TetraStereo.Engine.RingOxaziridineRootOrder

/-! The two measured N-chloroaziridine constitutions order the bonded ligands
Cl > methyl-bearing carbon > methylene even when carbon hydrogens are omitted. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingChloroaziridineOrder
open OneCenter
open RingOxaziridineNitrogen (atomIs)
open RingChloroaziridineNitrogen (Pattern constrainedRaw)
open RingAtomicNeighborOrder (atomicNumber neighbors)
open RingSecondShellDecision (adjacent shell signature)
open private atomic_of_good sorted_desc shell_mem from TetraStereo.Engine.RingOxaziridineRootOrder
attribute [local instance] lexOrd

private theorem carbon_compare (hi lo : List Nat) (sorted : hi.Pairwise (· ≥ ·))
    (small : ∀ z ∈ lo, z ≤ 6) (more : lo.count 6 < hi.count 6) : lo < hi := by
  induction hi generalizing lo with
  | nil => simp at more
  | cons a as ih =>
    obtain ⟨top,tail⟩ := List.pairwise_cons.mp sorted
    have mem : 6 ∈ a :: as := List.count_pos_iff.mp (by omega)
    have high : 6 ≤ a := by
      rcases List.mem_cons.mp mem with h | h
      · omega
      · exact top 6 h
    cases lo with
    | nil => exact List.Lex.nil
    | cons b bs =>
      have low := small b (by simp)
      by_cases eq : b = a
      · have ha : a = 6 := by omega
        subst b
        subst a
        exact List.Lex.cons (ih bs tail (fun z h => small z (by simp [h])) (by simpa using more))
      · exact List.Lex.rel (by omega)

private theorem mem_adj {m : RawMolecule} {n a v : Nat} :
    v ∈ adjacent m n a ↔ v < m.atomCount ∧ v ≠ n ∧ 0 < m.bondOrder a v := by
  simp [adjacent]

private theorem shell_decompose (m : RawMolecule) (n a v : Nat) (hv : v ∈ adjacent m n a) :
    (shell m n a).Perm (atomicNumber m v :: (((adjacent m n a).erase v).map (atomicNumber m))) := by
  exact (List.mergeSort_perm ..).trans ((List.perm_cons_erase hv).map _)

theorem descending_row_with_roles (m : RawMolecule) (n : Fin m.atomCount)
    (pattern : Pattern (fun v z => atomIs m v.val z)
      (fun (u v : Fin m.atomCount) => m.bondOrder u.val v.val) n) :
    ∃ cl c d : Nat, (neighbors m n.val).Perm [cl,c,d] ∧
      ([cl,c,d].map (signature m n.val)).Pairwise (· > ·) ∧
      atomIs m cl .Cl = true ∧ atomIs m c .C = true ∧ atomIs m d .C = true ∧
      m.bondOrder c d = 1 := by
  obtain ⟨gn,cl,gcl,ncl,_,c,gc,nc,d,gd,cd,nd,edge,ns,ds,x,gx,xd,cx,y,_,_,_,_,_,_⟩ := pattern
  dsimp only at ns ds ncl nc nd edge cx
  have zn : atomicNumber m n.val = 7 := atomic_of_good m _ .N gn
  have zcl : atomicNumber m cl.val = 17 := atomic_of_good m _ .Cl gcl
  have zc : atomicNumber m c.val = 6 := atomic_of_good m _ .C gc
  have zd : atomicNumber m d.val = 6 := atomic_of_good m _ .C gd
  have zx : atomicNumber m x.val = 6 := atomic_of_good m _ .C gx
  have unequal (i j : Fin m.atomCount) (h : atomicNumber m i.val ≠ atomicNumber m j.val) :
      i.val ≠ j.val := fun eq => h (congrArg _ eq)
  have dmem : d.val ∈ adjacent m n.val c.val :=
    mem_adj.mpr ⟨d.isLt,unequal d n (by omega),by rw [edge]; decide⟩
  have cmem : c.val ∈ adjacent m n.val d.val :=
    mem_adj.mpr ⟨c.isLt,unequal c n (by omega),by rw [m.bondOrder_symm,edge]; decide⟩
  have xmem : x.val ∈ adjacent m n.val c.val :=
    mem_adj.mpr ⟨x.isLt,unequal x n (by omega),by rw [cx]; decide⟩
  have high : 2 ≤ (shell m n.val c.val).count 6 := by
    rw [(shell_decompose m _ _ _ dmem).count_eq,zd,List.count_cons_self]
    have xe : x.val ∈ (adjacent m n.val c.val).erase d.val :=
      (List.mem_erase_of_ne (fun h => xd (Fin.ext h))).mpr xmem
    have six : 0 < (((adjacent m n.val c.val).erase d.val).map (atomicNumber m)).count 6 :=
      List.count_pos_iff.mpr (List.mem_map.mpr ⟨x.val,xe,zx⟩)
    omega
  have hydrogen (v : Nat) (h : v ∈ adjacent m n.val d.val) (ne : v ≠ c.val) :
      atomicNumber m v = 1 := by
    obtain ⟨bound,diff,bond⟩ := mem_adj.mp h
    rcases ds ⟨v,bound⟩ bond with eq | eq | hg
    · exact (diff (congrArg Fin.val eq)).elim
    · exact (ne (congrArg Fin.val eq)).elim
    · exact atomic_of_good m v .H hg
  have low : (shell m n.val d.val).count 6 = 1 := by
    rw [(shell_decompose m _ _ _ cmem).count_eq,zc,List.count_cons_self]
    have nodup : (adjacent m n.val d.val).Nodup := List.nodup_range.filter _
    have no : 6 ∉ (((adjacent m n.val d.val).erase c.val).map (atomicNumber m)) := by
      intro h
      obtain ⟨v,hv,zv⟩ := List.mem_map.mp h
      have hne : v ≠ c.val := by
        rintro rfl
        exact nodup.not_mem_erase hv
      have := hydrogen v (List.mem_of_mem_erase hv) hne
      omega
    simp [List.count_eq_zero_of_not_mem no]
  have small : ∀ z ∈ shell m n.val d.val, z ≤ 6 := by
    intro z hz
    obtain ⟨v,hv,rfl⟩ := (shell_mem ..).mp hz
    by_cases eq : v = c.val
    · simp [eq,zc]
    · rw [hydrogen v hv eq]; decide
  have dc : signature m n.val d.val < signature m n.val c.val := by
    simp only [signature,zd,zc]
    exact List.Lex.cons (List.Lex.rel (carbon_compare _ _ (sorted_desc _) small (by omega)))
  have cc : signature m n.val c.val < signature m n.val cl.val := by
    simp only [signature,zc,zcl]
    exact List.Lex.rel (List.Lex.rel (by decide : (6:Nat) < 17))
  have clc := unequal cl c (by omega)
  have cld := unequal cl d (by omega)
  have cd' : c.val ≠ d.val := fun h => cd (Fin.ext h)
  refine ⟨cl.val,c.val,d.val,?_,?_,gcl,gc,gd,edge⟩
  · have nodup : (neighbors m n.val).Nodup :=
      (RingStereoSiblingPass.legal_order (atomicNumber m) _).perm.nodup_iff.mpr
        (List.nodup_range.filter _)
    apply (List.perm_ext_iff_of_nodup nodup (by simp [clc,cld,cd'])).mpr
    intro v
    rw [RingAtomicNeighborOrder.mem_neighbors]
    simp only [List.mem_cons,List.mem_nil_iff,or_false]
    constructor
    · rintro ⟨bound,bond⟩
      rcases ns ⟨v,bound⟩ bond with eq | eq | eq
      · exact Or.inl (congrArg Fin.val eq)
      · exact Or.inr (Or.inl (congrArg Fin.val eq))
      · exact Or.inr (Or.inr (congrArg Fin.val eq))
    · rintro (rfl | rfl | rfl)
      · exact ⟨cl.isLt,by rw [ncl]; decide⟩
      · exact ⟨c.isLt,by rw [nc]; decide⟩
      · exact ⟨d.isLt,by rw [nd]; decide⟩
  · simpa [List.pairwise_cons] using And.intro (And.intro cc (lt_trans dc cc)) dc

theorem descending_row_of_constrained (m : RawMolecule) (n : Nat) (recognized : constrainedRaw m n = true) :
    ∃ cl c d : Nat, (neighbors m n).Perm [cl,c,d] ∧
      ([cl,c,d].map (signature m n)).Pairwise (· > ·) ∧
      atomIs m cl .Cl = true ∧ atomIs m c .C = true ∧ atomIs m d .C = true ∧
      m.bondOrder c d = 1 := by
  unfold constrainedRaw at recognized
  split at recognized
  · exact descending_row_with_roles m _ (of_decide_eq_true recognized)
  · contradiction
theorem descending_row_with_roles_of_constrained (m : RawMolecule) (n : Nat) (recognized : constrainedRaw m n = true) :
    ∃ cl c d : Nat, (neighbors m n).Perm [cl,c,d] ∧
      ([cl,c,d].map (signature m n)).Pairwise (· > ·) ∧
      atomIs m cl .Cl = true ∧ atomIs m c .C = true ∧ atomIs m d .C = true := by
  obtain ⟨cl,c,d,p,h,hcl,hc,hd,_⟩ := descending_row_of_constrained m n recognized
  exact ⟨cl,c,d,p,h,hcl,hc,hd⟩
end TetraStereo.Engine.RingChloroaziridineOrder
assert_kernel_only TetraStereo.Engine.RingChloroaziridineOrder.descending_row_of_constrained
