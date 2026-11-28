import TetraStereo.Engine.RingOxaziridineRootOrder
import TetraStereo.Engine.RingPyramidalTwoShell
import TetraStereo.Engine.RingDiaziridineSelection
import TetraStereo.Engine.RingHydrogenPlacementExact

/-! Local CIP order at either pyramidal nitrogen of a dialkyldiaziridine.
The adjacent nitrogen wins by atomic number. The ring carbon leads back to N
where the alkyl carbon has only C or H, so Rule 1a also breaks the carbon tie. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingDiaziridineOrder
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingAtomicNeighborOrder (atomicNumber neighbors)
open RingOxaziridineNitrogen (atomIs)
open RingSecondShellDecision (adjacent shell signature)
open LocalizedGenericMarkedRecalculation (readback?)
open private atomic_of_good sorted_desc shell_mem from TetraStereo.Engine.RingOxaziridineRootOrder

/-- A local incidence certificate. All other atoms and all carbon hydrogen
spellings are unrestricted provided the listed alkyl neighbors are C or H. -/
structure SiteRoles (m : RawMolecule) (n other ring alkyl : Nat) : Prop where
  row : (neighbors m n).Perm [other, ring, alkyl]
  nitrogen : atomIs m other .N = true
  ringCarbon : atomIs m ring .C = true
  alkylCarbon : atomIs m alkyl .C = true
  closes : other ∈ adjacent m n ring
  aliphatic : ∀ v ∈ adjacent m n alkyl, atomIs m v .C = true ∨ atomIs m v .H = true

theorem descending {m : RawMolecule} {n other ring alkyl : Nat} (cert : SiteRoles m n other ring alkyl) :
    ([other,ring,alkyl].map (signature m n)).Pairwise (· > ·) := by
  have n7 : atomicNumber m other = 7 := atomic_of_good m _ _ cert.nitrogen
  have c6 : atomicNumber m ring = 6 := atomic_of_good m _ _ cert.ringCarbon
  have k6 : atomicNumber m alkyl = 6 := atomic_of_good m _ _ cert.alkylCarbon
  have high := (shell_mem m n ring 7).mpr ⟨other,cert.closes,n7⟩
  have bound (z : Nat) (mem : z ∈ shell m n alkyl) : z ≤ 6 := by
    obtain ⟨v,hv,rfl⟩ := (shell_mem ..).mp mem
    rcases cert.aliphatic v hv with h | h <;> rw [atomic_of_good m _ _ h] <;> decide
  have sorted := sorted_desc ((adjacent m n ring).map (atomicNumber m))
  change (shell m n ring).Pairwise (· ≥ ·) at sorted
  have cWins : shell m n alkyl < shell m n ring := by
    cases hr : shell m n ring with
    | nil => simp [hr] at high
    | cons a as =>
      rw [hr] at high sorted
      have top : 7 ≤ a := (List.mem_cons.mp high).elim (fun eq => eq.le)
        ((List.pairwise_cons.mp sorted).1 7)
      cases hk : shell m n alkyl with
      | nil => exact List.Lex.nil
      | cons b bs => exact List.Lex.rel (lt_of_le_of_lt (bound b (by simp [hk])) (by omega))
  have kc : signature m n alkyl < signature m n ring := by
    simp only [signature,k6,c6]
    exact List.Lex.cons (List.Lex.rel cWins)
  have cn : signature m n ring < signature m n other := by
    simp only [signature,c6,n7]
    exact List.Lex.rel (List.Lex.rel (by decide : (6:Nat) < 7))
  simpa [List.pairwise_cons] using And.intro (And.intro cn (lt_trans kc cn)) kc

/-- Extract the ordered physical roles from the executable structural test,
without assuming an earlier-priority comparison or an auxiliary store. -/
theorem roles_of_recognized {m : RawMolecule} {n : Nat}
    (motif : RingDialkyldiaziridine.constrainedRaw m n = true) :
    ∃ other ring alkyl, SiteRoles m n other ring alkyl := by
  unfold RingDialkyldiaziridine.constrainedRaw at motif
  split at motif
  next nBound =>
    obtain ⟨_,o,go,no,bo,c,gc,bc,oc,_,a,ac,ba,ga,ns,_⟩ := of_decide_eq_true motif
    dsimp only at bo bc oc ba
    have otherRing : o.val ≠ c.val := by
      intro h
      have eq := congrArg (atomicNumber m) h
      rw [atomic_of_good m _ _ go,atomic_of_good m _ _ gc] at eq
      contradiction
    have otherAlkyl : o.val ≠ a.val := by
      intro h
      have eq := congrArg (atomicNumber m) h
      rw [atomic_of_good m _ _ go,atomic_of_good m _ _ ga.1] at eq
      contradiction
    have ca : c.val ≠ a.val := fun eq => ac (Fin.ext eq.symm)
    refine ⟨o.val,c.val,a.val,?_,go,gc,ga.1,?_,?_⟩
    · exact RingDiaziridineSelection.neighbors_perm otherRing otherAlkyl ca bo bc ba ns
    · simp only [adjacent,List.mem_filter,List.mem_range,Bool.and_eq_true,bne_iff_ne,decide_eq_true_eq]
      exact ⟨o.isLt,fun eq => no (Fin.ext eq.symm),by rw [m.bondOrder_symm,oc]; decide⟩
    · intro v hv
      simp only [adjacent,List.mem_filter,List.mem_range,Bool.and_eq_true,bne_iff_ne,decide_eq_true_eq] at hv
      rcases (ga.2.2 ⟨v,hv.1⟩ hv.2.2).2 with eq|hydrogen|carbon
      · exact (hv.2.1 (congrArg Fin.val eq)).elim
      · exact Or.inr hydrogen
      · exact Or.inl carbon.1
  next => contradiction

theorem root {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (n : i.certified.Atom) (selected : RingPyramidalPublication.phosphorus i n = true)
    {other ring alkyl : Nat} (cert : SiteRoles i.molecule n.val other ring alkyl) :
    RingChemicalGraphProof.root i n = some
      ((readback? (LocalizedChemicalRingPhysicalSense.inputGeometry i.certified)
        [other,ring,alkyl,n.val]).map fun h => (.chiral h,.chiral h.swap)) :=
  RingPyramidalTwoShell.root_of_graph_order geom n selected _ cert.row (descending cert)

/-- The hand is read using only the four original heavy-atom coordinates. -/
def labels (g : SpatialConfiguration) (n other ring alkyl : Nat) : Option RingNestedActivePair.Labels :=
  (readback? (RingWrittenPHReadings.geometry g) [other,ring,alkyl,n]).map fun h => (.chiral h,.chiral h.swap)

open private row? from TetraStereo.Engine.RingChemicalReport
open private raw_iff inside from TetraStereo.Engine.RingDiaziridineSelection

theorem closed_row {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (closed : RingHydrogenCompletion.plan i.molecule = []) (n : i.certified.Atom)
    (motif : RingDialkyldiaziridine.constrainedRaw i.molecule n.val = true)
    {o c k : Nat} (r : SiteRoles i.molecule n.val o c k) :
    RingHydrogenReport.fromRaw? i.molecule i.spatial [n.val] = some [(n.val,labels i.spatial n.val o c k)] := by
  have h := root geom n (RingDiaziridineSelection.selected n motif) r
  rw [RingWrittenPHReadings.inputGeometry_eq] at h
  rw [show [n.val] = [n].map Fin.val from rfl,RingWrittenPHReadings.fromRaw_closed_report i closed geom]
  unfold RingChemicalReport.report?
  simp only [List.mapM_cons,List.mapM_nil,row?,h,Option.map_some,bind,pure]
  rfl

private theorem original {m out : RawMolecule} {g pos : SpatialConfiguration}
    (cert : RingHydrogenCompletion.Certified m g out pos) {n : Nat} {z : Element}
    (heavy : z ≠ .H) (h : atomIs out n z = true) : n < m.atomCount := by
  by_contra! fresh
  have lt : n < out.atomCount := by
    by_contra! absent
    simp [atomIs,List.getElem?_eq_none (by exact absent : out.atoms.length ≤ n)] at h
  have newAtom := cert.fresh_atom fresh lt
  simp [atomIs,newAtom,AtomSpec.aliphatic,Ne.symm heavy] at h

/-- Read the fully public raw nitrogen row from its constitutional roles, for
any admitted hydrogen preparation and all generated placements. -/
theorem raw {m out : RawMolecule} {g pos : SpatialConfiguration} {src base : Input}
    (admit : LocalizedChemicalRing.admitRawSpatial? m g = some src)
    (sourceGeom : LocalizedChemicalRing.coordinatesAdmitted src = true)
    (done : RingHydrogenCompletion.prepare? m g = some (out,pos))
    (prepared : LocalizedChemicalRing.admitRawSpatial? out pos = some base)
    (baseGeom : LocalizedChemicalRing.coordinatesAdmitted base = true) {n : Nat}
    (motif : RingDialkyldiaziridine.constrainedRaw out n = true) :
    ∃ o c k, SiteRoles out n o c k ∧ RingHydrogenReport.fromRaw? m g [n] = some [(n,labels g n o c k)] := by
  obtain ⟨o,c,k,r⟩ := roles_of_recognized motif
  refine ⟨o,c,k,r,?_⟩
  have cert := RingHydrogenCompletion.prepare?_certified done
  have nlt := original cert (by decide : Element.N ≠ .H) (((raw_iff (inside motif)).mp motif).1)
  have olt := original cert (by decide : Element.N ≠ .H) r.nitrogen
  have clt := original cert (by decide : Element.C ≠ .H) r.ringCarbon
  have klt := original cert (by decide : Element.C ≠ .H) r.alkylCarbon
  rw [RingSpatialTransport.public_search admit sourceGeom done [n] (by simpa using nlt)]
  apply (RingHydrogenReport.search?_iff ..).mpr
  intro points hp
  let x : SpatialConfiguration := ⟨points⟩
  have hx : x ∈ RingPyramidalChoices.variants m g out pos := List.mem_map.mpr ⟨points,hp,rfl⟩
  obtain ⟨j,aj,gj⟩ := RingSpatialTransport.variant_admission cert prepared hx
  obtain ⟨jm,jg⟩ := RingChemicalReport.admission_fields aj
  let a : j.certified.Atom := ⟨n,by
    rw [j.molecule.toSemanticMolecule?_atomCount _ j.agreement.1,jm]
    exact Nat.lt_of_lt_of_le nlt cert.atomCount_le⟩
  have result := closed_row (gj.trans baseGeom) (jm ▸ RingHydrogenCompletion.prepare?_closed done) a
    (by simpa [jm,a] using motif) (o := o) (c := c) (k := k) (by simpa only [jm,a] using r)
  simp only [jm,jg,a,RingHydrogenReport.fromRaw_closed_eq (RingHydrogenCompletion.prepare?_closed done)] at result
  have fixed (idx : Nat) (old : idx < m.atomCount) : x.positions[idx]? = g.positions[idx]? :=
    (RingPyramidalChoices.variants_original hx old).trans (cert.positions_getElem? old)
  have same : labels x n o c k = labels g n o c k := by
    simp only [labels,readback?,List.mapM_cons,List.mapM_nil,RingWrittenPHReadings.geometry,
      fixed n nlt,fixed o olt,fixed c clt,fixed k klt]
  exact same ▸ result

open CartesianPoint3

/-- Oriented height above the common N–N–C plane, scaled by its area. -/
def side (n b c p : CartesianPoint3) := orientedVolume b c p n

private theorem reverse_side (n b c p : CartesianPoint3) : side b n c p = -side n b c p := by
  simp only [side,orientedVolume]
  ring

/-- For two nonplanar nitrogens, their Rule 1a hands coincide precisely when
the substituents are on opposite sides of their common ring plane. -/
theorem trans_iff {n b c p q : CartesianPoint3} (a : side n b c p ≠ 0) (d : side n b c q ≠ 0) :
    side n b c p * side n b c q < 0 ↔
    descriptorOfOrientedVolume? (side n b c p) = descriptorOfOrientedVolume? (side b n c q) := by
  rw [reverse_side n b c q]
  rcases lt_or_gt_of_ne a with ha | ha <;> rcases lt_or_gt_of_ne d with hb | hb <;>
    simp [descriptorOfOrientedVolume?,mul_neg_iff,ha,hb,not_lt_of_gt ha,not_lt_of_gt hb]

end TetraStereo.Engine.RingDiaziridineOrder
assert_kernel_only TetraStereo.Engine.RingDiaziridineOrder.root
assert_kernel_only TetraStereo.Engine.RingDiaziridineOrder.trans_iff
assert_kernel_only TetraStereo.Engine.RingDiaziridineOrder.raw
