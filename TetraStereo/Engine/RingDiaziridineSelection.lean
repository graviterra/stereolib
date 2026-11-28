import TetraStereo.Engine.RingOxaziridineNitrogen
import TetraStereo.Engine.RingAtomicNeighborOrder

/-! Either pyramidal nitrogen in the matched N,N′-dialkyldiaziridine ring
recognizes the other. Each has exactly the three physical neighbors used by
public pyramidal publication. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingDiaziridineSelection
open OneCenter
open LocalizedChemicalRing (Input)
open RingOxaziridineNitrogen (atomIs)
open RingDialkyldiaziridine (Pattern constrainedRaw)

private theorem raw_iff {g : RawMolecule} {n : Nat} (hn : n < g.atomCount) :
    constrainedRaw g n = true ↔ Pattern (fun (a : Fin g.atomCount) z => atomIs g a.val z)
      (fun a b => g.bondOrder a.val b.val) ⟨n,hn⟩ := by
  simp [constrainedRaw,hn,RingDialkyldiaziridine.test]

private theorem inside {g : RawMolecule} {n : Nat} (yes : constrainedRaw g n = true) :
    n < g.atomCount := by
  unfold constrainedRaw at yes
  split at yes <;> simp_all

/-- A positive decision at either N supplies a distinct, singly bonded partner
whose own independent structural check is positive. -/
theorem partner {g : RawMolecule} {n : Nat} (yes : constrainedRaw g n = true) :
    ∃ m : Fin g.atomCount, n ≠ m.val ∧ g.bondOrder n m.val = 1 ∧ constrainedRaw g m.val = true := by
  have hn := inside yes
  obtain ⟨ng,m,mg,ne,nm,c,cg,nc,mc,ring,a,ac,na,al,neigh,b,bc,ba,mb,bl,meigh⟩ :=
    (raw_iff hn).mp yes
  refine ⟨m,fun eq => ne (Fin.ext eq),nm,(raw_iff m.isLt).mpr ?_⟩
  refine ⟨mg,⟨n,hn⟩,ng,ne.symm,(g.bondOrder_symm _ _).trans nm,c,cg,mc,nc,?_,
    b,bc,mb,bl,meigh,a,ac,ba.symm,na,al,neigh⟩
  intro v ed
  obtain ⟨single,roles⟩ := ring v ed
  exact ⟨single,roles.elim (fun h => Or.inr (Or.inl h)) (fun h => h.elim Or.inl (Or.inr ∘ Or.inr))⟩

private theorem typed_ne {g : RawMolecule} {u w : Nat}
    (n : atomIs g u .N = true) (c : atomIs g w .C = true) : u ≠ w := by
  rintro rfl
  cases h : g.atoms[u]? with
  | none => simp [atomIs,h] at n
  | some a => simp [atomIs,h] at n c; simp [n.1.1] at c

/-- The actual raw neighbor list at a three-coordinate site, up to order. -/
theorem neighbors_perm {g : RawMolecule} {n : Nat} {m c k : Fin g.atomCount}
    (mc : m.val ≠ c.val) (mk : m.val ≠ k.val) (ck : c.val ≠ k.val)
    (nm : g.bondOrder n m.val = 1) (nc : g.bondOrder n c.val = 1) (nk : g.bondOrder n k.val = 1)
    (around : ∀ v : Fin g.atomCount, 0 < g.bondOrder n v.val → v = m ∨ v = c ∨ v = k) :
    (RingAtomicNeighborOrder.neighbors g n).Perm [m.val,c.val,k.val] := by
  have nd : [m.val,c.val,k.val].Nodup := by simp [mc,mk,ck]
  have nr := RingStereoSiblingPass.legal_order (RingAtomicNeighborOrder.atomicNumber g)
    ((List.range g.atomCount).filter fun v => 0 < g.bondOrder n v)
  have native : (RingAtomicNeighborOrder.neighbors g n).Nodup :=
    nr.perm.nodup_iff.mpr ((List.nodup_range).filter _)
  apply (List.perm_ext_iff_of_nodup native nd).mpr
  intro v
  rw [RingAtomicNeighborOrder.mem_neighbors]
  simp only [List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · rintro ⟨hv,ed⟩
    exact (around ⟨v,hv⟩ ed).imp (congrArg Fin.val) (fun h => h.imp (congrArg Fin.val) (congrArg Fin.val))
  · rintro (rfl|rfl|rfl)
    · exact ⟨m.isLt,by rw [nm]; decide⟩
    · exact ⟨c.isLt,by rw [nc]; decide⟩
    · exact ⟨k.isLt,by rw [nk]; decide⟩

/-- Exact coordination number from the motif itself. -/
theorem degree {i : Input} (a : i.certified.Atom) (motif : constrainedRaw i.molecule a.val = true) :
    Fintype.card (i.certified.moleculeGraph.Neighbor a) = 3 := by
  obtain ⟨_,m,mg,_,nm,c,cg,nc,_,_,k,kc,nk,alkyl,around,_⟩ := (raw_iff (inside motif)).mp motif
  have ck : c.val ≠ k.val := fun e => kc (Fin.ext e.symm)
  have perm := neighbors_perm (typed_ne mg cg) (typed_ne mg alkyl.1) ck nm nc nk around
  exact (RingAtomicNeighborOrder.degree_eq i a).trans perm.length_eq

theorem selected {i : Input} (a : i.certified.Atom) (motif : constrainedRaw i.molecule a.val = true) :
    RingPyramidalPublication.phosphorus i a = true := by
  have record := ((raw_iff (inside motif)).mp motif).1
  cases w : i.molecule.atoms[a.val]? with
  | none => simp [atomIs,w] at record
  | some atom =>
    have fields : (atom.element = .N ∧ atom.charge = 0) ∧ atom.aromatic = false := by
      simpa [atomIs,w] using record
    simp [RingPyramidalPublication.phosphorus,w,fields.1.1,fields.1.2,fields.2,degree a motif,
      RingPyramidalNitrogen.constrained,RingPyramidalNitrogen.constrainedRaw,motif]

theorem both {i : Input} (a : i.certified.Atom) (motif : constrainedRaw i.molecule a.val = true) :
    ∃ b : i.certified.Atom, a ≠ b ∧ i.molecule.bondOrder a.val b.val = 1 ∧
      RingPyramidalPublication.phosphorus i a = true ∧ RingPyramidalPublication.phosphorus i b = true := by
  obtain ⟨m,ne,single,recognized⟩ := partner motif
  let b := (RingBridgeheadNitrogen.rawAtomEquiv i).symm m
  exact ⟨b,fun eq => ne (congrArg Fin.val eq),single,selected a motif,selected b recognized⟩

end TetraStereo.Engine.RingDiaziridineSelection
assert_kernel_only TetraStereo.Engine.RingDiaziridineSelection.partner
assert_kernel_only TetraStereo.Engine.RingDiaziridineSelection.degree
assert_kernel_only TetraStereo.Engine.RingDiaziridineSelection.both
