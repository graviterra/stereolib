import TetraStereo.Engine.RingOxaziridineHydrogen

/-! Ordinary hydrogens can be added at any carbon in the recognized ring or
methyl groups. The N and its bonded chlorine must retain their heavy-atom coordination. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingChloroaziridineHydrogen
open OneCenter RingHydrogenCompletion RingChloroaziridineNitrogen
open RingOxaziridineNitrogen (atomIs)
open OrdinaryHydrogenSpellings.Production
open private old_atom no_fresh from TetraStereo.Engine.RingOxaziridineHydrogen
variable {m out : RawMolecule} {g pos : SpatialConfiguration}

def NoExtraH (m : RawMolecule) (n : Nat) : Prop :=
  missing m n = 0 ∧ ∀ cl : Fin m.atomCount,
    atomIs m cl.val .Cl = true → m.bondOrder n cl.val = 1 → missing m cl.val = 0

theorem pattern_preserved (cert : Certified m g out pos) (n : Fin m.atomCount)
    (stable : NoExtraH m n.val)
    (hit : Pattern (fun a z => atomIs m a.val z) (fun (a b : Fin m.atomCount) => m.bondOrder a.val b.val) n) :
    Pattern (fun a z => atomIs out a.val z) (fun (a b : Fin out.atomCount) => out.bondOrder a.val b.val)
      ⟨n.val,lt_of_lt_of_le n.isLt cert.atomCount_le⟩ := by
  let lift (a : Fin m.atomCount) : Fin out.atomCount := ⟨a.val,lt_of_lt_of_le a.isLt cert.atomCount_le⟩
  change Pattern _ _ (lift n)
  have inj : Function.Injective lift := fun _ _ eq => Fin.ext (congrArg (fun v : Fin out.atomCount => v.val) eq)
  have edge (a b : Fin m.atomCount) : out.bondOrder (lift a).val (lift b).val = m.bondOrder a.val b.val :=
    certified_old_bond cert _ _ a.isLt b.isLt
  have good (a : Fin m.atomCount) (z : Element) : atomIs out (lift a).val z = atomIs m a.val z :=
    old_atom cert a z
  have neighbors (a : Fin m.atomCount) (P : Fin out.atomCount → Prop)
      (original : ∀ u : Fin m.atomCount, 0 < m.bondOrder a.val u.val → P (lift u))
      (added : ∀ v : Fin out.atomCount, m.atomCount ≤ v.val → 0 < out.bondOrder (lift a).val v.val → P v) :
      ∀ v : Fin out.atomCount, 0 < out.bondOrder (lift a).val v.val → P v := by
    intro v hv
    by_cases old : v.val < m.atomCount
    · let u : Fin m.atomCount := ⟨v.val,old⟩
      have eq : lift u = v := Fin.ext rfl
      apply eq ▸ original u
      rwa [← edge,eq]
    · exact added v (Nat.le_of_not_lt old) hv
  have freshH (v : Fin out.atomCount) (hv : m.atomCount ≤ v.val) : atomIs out v.val .H = true := by
    simp [atomIs,cert.fresh_atom hv v.isLt,AtomSpec.aliphatic]
  have forbidden (a : Fin m.atomCount) (zero : missing m a.val = 0)
      (v : Fin out.atomCount) (hv : m.atomCount ≤ v.val) (bond : 0 < out.bondOrder (lift a).val v.val) : False := by
    have no := no_fresh cert a zero v hv
    exact (Nat.ne_of_gt bond) no
  obtain ⟨nn,cl,cc,ncl,clrow,c,cr,nc,d,dr,cd,nd,cdb,nrow,drow,x,xr,xd,cx,y,yr,yd,cy,crow,xrow,yrow⟩ := hit
  refine ⟨(good n _).trans nn,lift cl,(good cl _).trans cc,(edge ..).trans ncl,?_,
    lift c,(good c _).trans cr,(edge ..).trans nc,lift d,(good d _).trans dr,fun eq => cd (inj eq),
    (edge ..).trans nd,(edge ..).trans cdb,?_,?_,lift x,(good x _).trans xr,fun eq => xd (inj eq),
    (edge ..).trans cx,lift y,(good y _).trans yr,fun eq => yd (inj eq),(edge ..).trans cy,?_,?_,?_⟩
  · apply neighbors
    · exact fun u h => congrArg lift (clrow u h)
    · exact fun v hv h => (forbidden cl (stable.2 cl cc ncl) v hv h).elim
  · apply neighbors
    · intro u h
      simpa only [inj.eq_iff] using nrow u h
    · exact fun v hv h => (forbidden n stable.1 v hv h).elim
  · apply neighbors
    · intro u h
      simpa only [inj.eq_iff,good] using drow u h
    · exact fun v hv _ => Or.inr (Or.inr (freshH v hv))
  · apply neighbors
    · intro u h
      simpa only [inj.eq_iff,good] using crow u h
    · exact fun v hv _ => Or.inr (Or.inr (Or.inr (Or.inr (freshH v hv))))
  · apply neighbors
    · intro u h
      simpa only [inj.eq_iff,good] using xrow u h
    · exact fun v hv _ => Or.inr (freshH v hv)
  · apply neighbors
    · intro u h
      simpa only [inj.eq_iff,good] using yrow u h
    · exact fun v hv _ => Or.inr (freshH v hv)

theorem recognized (cert : Certified m g out pos) (n : Nat) (stable : NoExtraH m n)
    (source : constrainedRaw m n = true) : constrainedRaw out n = true := by
  unfold constrainedRaw at source ⊢
  split at source
  · rename_i bounded
    rw [dif_pos (lt_of_lt_of_le bounded cert.atomCount_le)]
    exact decide_eq_true (pattern_preserved cert ⟨n,bounded⟩ stable (of_decide_eq_true source))
  · contradiction

end TetraStereo.Engine.RingChloroaziridineHydrogen
assert_kernel_only TetraStereo.Engine.RingChloroaziridineHydrogen.recognized
