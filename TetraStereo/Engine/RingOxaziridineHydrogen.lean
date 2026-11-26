import TetraStereo.Engine.RingOxaziridineNitrogen
import TetraStereo.Engine.RingProducedHydrogenGraphs
import TetraStereo.Engine.RingHydrogenNeighbors

/-! Hydrogen completion preserves the oxaziridine motif provided its N/O atoms
receive no appended hydrogen. Explicit hydrogen overrides make this prerequisite
necessary even when their existing graph degrees are three and two. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOxaziridineHydrogen
open OneCenter
open RingHydrogenCompletion
open RingOxaziridineNitrogen
open OrdinaryHydrogenSpellings.Production
variable {m out : RawMolecule} {g pos : SpatialConfiguration}

private theorem old_atom (cert : Certified m g out pos) (a : Fin m.atomCount) (z : Element) :
    atomIs out a.val z = atomIs m a.val z := by
  have bound : a.val < out.atomCount := lt_of_lt_of_le a.isLt cert.atomCount_le
  have ha := List.getElem?_eq_getElem a.isLt (l := m.atoms)
  have hb := List.getElem?_eq_getElem bound (l := out.atoms)
  obtain ⟨element,_,charge,aromatic,_⟩ := cert.atom_fields a.isLt ha hb
  simp only [atomIs,ha,hb,Option.any_some,element,charge,aromatic]

private theorem no_fresh (cert : Certified m g out pos) (a : Fin m.atomCount)
    (zero : missing m a.val = 0) (v : Fin out.atomCount) (fresh : m.atomCount ≤ v.val) :
    out.bondOrder a.val v.val = 0 := by
  obtain ⟨parent,found,row⟩ := cert.fresh_row fresh v.isLt
  have absent : a.val ∉ addedParents m := by
    rw [← List.count_eq_zero, RingPyramidalChoices.addedParents_count m a.val a.isLt,zero]
  have ne : a.val ≠ parent := by
    intro eq
    exact absent (eq ▸ List.mem_of_getElem? found)
  rw [out.bondOrder_symm,certified_fresh_bond cert v fresh parent row
    ⟨a.val,lt_of_lt_of_le a.isLt cert.atomCount_le⟩,if_neg ne]

/-- A sharp, source-only prerequisite: no hydrogen is planned at the selected N
or any adjacent oxygen. It does not constrain additions elsewhere. -/
def NoRingHydrogens (m : RawMolecule) (n : Nat) : Prop :=
  missing m n = 0 ∧ ∀ o : Fin m.atomCount,
    atomIs m o.val .O = true → m.bondOrder n o.val = 1 → missing m o.val = 0

/-- Every recognized role keeps its original identifier under an independently
certified ordinary-H completion. Other atoms may gain arbitrary ordinary H leaves. -/
theorem pattern_preserved (cert : Certified m g out pos) (n : Fin m.atomCount)
    (ready : NoRingHydrogens m n.val)
    (pattern : Pattern (fun a z => atomIs m a.val z)
      (fun (a b : Fin m.atomCount) => m.bondOrder a.val b.val) n) :
    Pattern (fun a z => atomIs out a.val z)
      (fun (a b : Fin out.atomCount) => out.bondOrder a.val b.val)
      ⟨n.val,lt_of_lt_of_le n.isLt cert.atomCount_le⟩ := by
  let lift (a : Fin m.atomCount) : Fin out.atomCount :=
    ⟨a.val,lt_of_lt_of_le a.isLt cert.atomCount_le⟩
  change Pattern _ _ (lift n)
  have injective : Function.Injective lift := fun a b eq => Fin.ext (congrArg (fun x : Fin out.atomCount => x.val) eq)
  have old (a b : Fin m.atomCount) : out.bondOrder (lift a).val (lift b).val =
      m.bondOrder a.val b.val := certified_old_bond cert _ _ a.isLt b.isLt
  rcases pattern with ⟨nn,o,no,oo,bno,c,nc,oc,cc,bnc,boc,k,nk,ok,ck,kk,bnk,nrow,orow,cs,ks,alk⟩
  have oxygenZero := ready.2 o oo bno
  refine ⟨(old_atom cert n .N).trans nn,lift o,?_,(old_atom cert o .O).trans oo,?_,
    lift c,?_,?_,(old_atom cert c .C).trans cc,?_,?_,lift k,?_,?_,?_,
    (old_atom cert k .C).trans kk,?_,?_,?_,?_,?_,?_⟩
  all_goals dsimp only
  · exact fun eq => no (injective eq)
  · exact (old n o).trans bno
  · exact fun eq => nc (injective eq)
  · exact fun eq => oc (injective eq)
  · exact (old n c).trans bnc
  · exact (old o c).trans boc
  · exact fun eq => nk (injective eq)
  · exact fun eq => ok (injective eq)
  · exact fun eq => ck (injective eq)
  · exact (old n k).trans bnk
  · intro v
    by_cases hv : v.val < m.atomCount
    · let u : Fin m.atomCount := ⟨v.val,hv⟩
      have same : lift u = v := Fin.ext rfl
      rw [← same,old,nrow]
      simp only [injective.eq_iff]
    · have fresh : m.atomCount ≤ v.val := Nat.le_of_not_gt hv
      rw [no_fresh cert n ready.1 v fresh]
      have ne (a : Fin m.atomCount) : v ≠ lift a := by intro eq; have := congrArg Fin.val eq; dsimp [lift] at this; omega
      simp [ne]
  · intro v
    by_cases hv : v.val < m.atomCount
    · let u : Fin m.atomCount := ⟨v.val,hv⟩
      have same : lift u = v := Fin.ext rfl
      rw [← same,old,orow]
      simp only [injective.eq_iff]
    · have fresh : m.atomCount ≤ v.val := Nat.le_of_not_gt hv
      rw [no_fresh cert o oxygenZero v fresh]
      have ne (a : Fin m.atomCount) : v ≠ lift a := by intro eq; have := congrArg Fin.val eq; dsimp [lift] at this; omega
      simp [ne]
  · intro v
    by_cases hv : v.val < m.atomCount
    · rw [certified_old_bond cert c.val v.val c.isLt hv]
      exact cs ⟨v.val,hv⟩
    · rw [out.bondOrder_symm]
      exact certified_fresh_bond_le_one cert v.val c.val (Nat.le_of_not_gt hv)
  · intro v
    by_cases hv : v.val < m.atomCount
    · rw [certified_old_bond cert k.val v.val k.isLt hv]
      exact ks ⟨v.val,hv⟩
    · rw [out.bondOrder_symm]
      exact certified_fresh_bond_le_one cert v.val k.val (Nat.le_of_not_gt hv)
  · intro v positive
    by_cases hv : v.val < m.atomCount
    · let u : Fin m.atomCount := ⟨v.val,hv⟩
      have same : lift u = v := Fin.ext rfl
      have before : 0 < m.bondOrder k.val u.val := by
        rw [← old k u]; simpa [same] using positive
      rcases alk u before with eq | carbon | hydrogen
      · exact Or.inl (by rw [← same,eq])
      · exact Or.inr (Or.inl (by rw [← same]; exact (old_atom cert u .C).trans carbon))
      · exact Or.inr (Or.inr (by rw [← same]; exact (old_atom cert u .H).trans hydrogen))
    · exact Or.inr (Or.inr (by simp [atomIs,cert.fresh_atom (Nat.le_of_not_gt hv) v.isLt,AtomSpec.aliphatic]))

/-- Raw recognizer persistence with the precise zero-addition prerequisite. -/
theorem constrainedRaw_preserved (cert : Certified m g out pos) (n : Nat)
    (ready : NoRingHydrogens m n) (recognized : constrainedRaw m n = true) :
    constrainedRaw out n = true := by
  unfold constrainedRaw at recognized ⊢
  split at recognized
  · rename_i bound
    rw [dif_pos (lt_of_lt_of_le bound cert.atomCount_le)]
    change decide (Pattern _ _ _) = true
    apply decide_eq_true
    exact pattern_preserved cert ⟨n,bound⟩ ready (of_decide_eq_true recognized)
  · contradiction
/-- A structurally recognized graph can nevertheless carry an inconsistent
explicit N-H override. Raw graph recognition alone cannot discharge the
zero-addition prerequisite. -/
def overrideWitness : RawMolecule where
  atoms := [{AtomSpec.aliphatic .N with explicitHydrogens? := some 1},
    AtomSpec.aliphatic .O,AtomSpec.aliphatic .C,AtomSpec.aliphatic .C]
  bonds := [⟨0,1,.single⟩,⟨1,2,.single⟩,⟨2,0,.single⟩,⟨0,3,.single⟩]

theorem override_recognized : constrainedRaw overrideWitness 0 = true := by decide +kernel

theorem override_adds_nitrogen_hydrogen : missing overrideWitness 0 = 1 := by decide +kernel

end TetraStereo.Engine.RingOxaziridineHydrogen
assert_kernel_only TetraStereo.Engine.RingOxaziridineHydrogen.pattern_preserved
assert_kernel_only TetraStereo.Engine.RingOxaziridineHydrogen.constrainedRaw_preserved

assert_kernel_only TetraStereo.Engine.RingOxaziridineHydrogen.override_recognized
assert_kernel_only TetraStereo.Engine.RingOxaziridineHydrogen.override_adds_nitrogen_hydrogen
