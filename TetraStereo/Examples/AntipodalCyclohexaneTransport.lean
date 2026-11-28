import TetraStereo.Examples.AntipodalCyclohexaneHands

/-! Coordinate transport for fully written cyclohexane-1,4-diol. Away from
the two hydroxyl-bearing carbons each tetrahedral center has terminal H twins. -/
set_option autoImplicit false
namespace TetraStereo.Examples.AntipodalCyclohexaneTransport
open OneCenter Engine LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open AntipodalCyclohexaneHands (molecule frameRow opposite)
open RingWrittenPHReadings (geometry)
open RingAtomicNeighborOrder (neighbors degree_eq)
open private bound toAtom from TetraStereo.Engine.RingAtomicNeighborOrder
open private frame_perm from TetraStereo.Examples.DecalinFrames
open private graphRows from TetraStereo.Examples.AntipodalCyclohexaneHands

def Selected (v : Nat) := v = 0 ∨ v = 3

def SignsAgree (x y : SpatialConfiguration) : Prop :=
  ∀ r : Fin 2, readback? (geometry x) (frameRow r) = readback? (geometry y) (frameRow r)

private def leaf (v : Nat) := if v < 3 then 7+2*v else 8+2*v

private def incident (a : Nat) := (List.range molecule.atomCount).filter fun n => 0 < molecule.bondOrder a n

private theorem four_only : ∀ a : Fin 20, (neighbors molecule a.val).length = 4 → a.val < 6 := by
  have finite : ∀ a : Fin 20, (incident a.val).length = 4 → a.val < 6 := by decide +kernel
  exact fun a h => finite a ((RingStereoSiblingPass.legal_order _ _).perm.length_eq.symm.trans h)

private theorem no_pyramids : ∀ a : Fin 20, RingAtomicNeighborOrder.neutralPyramidal molecule a.val = false := by
  decide +kernel

private theorem closed : RingHydrogenCompletion.plan molecule = [] := by decide +kernel

private theorem hydrogens : ∀ c : Fin 6, c.val ≠ 0 → c.val ≠ 3 →
    (molecule.atoms[leaf c.val]?).map RingRawRenumbering.molecularRecord =
      (molecule.atoms[leaf c.val + 1]?).map RingRawRenumbering.molecularRecord ∧
    ∀ b : Fin 20,
      molecule.bondOrder (leaf c.val) b.val = (if b.val = c.val then 1 else 0) ∧
      molecule.bondOrder (leaf c.val + 1) b.val = (if b.val = c.val then 1 else 0) := by
  decide +kernel

private theorem atom_bound {i : Input} (raw : i.molecule = molecule) (a : i.certified.Atom) : a.val < 20 := by
  simpa only [raw] using bound i a

private theorem twin {i : Input} (raw : i.molecule = molecule) (c : i.certified.TetrahedralCenter)
    (off : ¬ Selected c.val.val) (root : i.certified.Atom) (atRoot : Selected root.val) :
    ∃ p : RingHydrogenSpelling.TwinPair i, p.c = c ∧ root ≠ p.u ∧ root ≠ p.v := by
  let a := c.val.val
  have degree := (i.certified.moleculeGraph.mem_tetrahedralCenterSet c.val).mp c.property
  change Fintype.card (i.certified.moleculeGraph.Neighbor c.val) = 4 at degree
  rw [degree_eq,raw] at degree
  have hi : a < 6 := four_only ⟨a,atom_bound raw _⟩ degree
  have spec := hydrogens ⟨a,hi⟩ (fun h => off (Or.inl h)) (fun h => off (Or.inr h))
  have small : leaf a + 1 < 20 := by unfold leaf; split <;> omega
  let u := toAtom i (leaf a) (by rw [raw]; change leaf a < 20; omega)
  let v := toAtom i (leaf a + 1) (by rw [raw]; exact small)
  have eu : u.val = leaf a := rfl
  have ev : v.val = leaf a + 1 := rfl
  let p : RingHydrogenSpelling.TwinPair i := {
    c := c, u := u, v := v
    distinct := fun eq => by have h := congrArg Fin.val eq; rw [eu,ev] at h; omega
    records := by rw [eu,ev,raw]; exact spec.1
    lu := fun b => by rw [eu,raw]; simpa only [Fin.ext_iff] using (spec.2 ⟨b.val,atom_bound raw b⟩).1
    lv := fun b => by rw [ev,raw]; simpa only [Fin.ext_iff] using (spec.2 ⟨b.val,atom_bound raw b⟩).2 }
  have high : 3 < leaf a := by unfold leaf; split <;> omega
  refine ⟨p,rfl,?_,?_⟩
  · intro h
    have eq : root.val = leaf a := (congrArg Fin.val h).trans eu
    rcases atRoot with h|h <;> omega
  · intro h
    have eq : root.val = leaf a + 1 := (congrArg Fin.val h).trans ev
    rcases atRoot with h|h <;> omega

theorem residual {i : Input} (raw : i.molecule = molecule) (x : SpatialConfiguration)
    (same : SignsAgree i.spatial x) (root : i.certified.Atom) (selected : Selected root.val) :
    RingTwinCoordinateTransport.ResidualAgreement i x root := by
  intro q on missed
  constructor
  · intro fr
    by_cases h : Selected fr.center.val.val
    · obtain ⟨r,atCenter⟩ : ∃ r : Fin 2, fr.center.val.val = opposite r := by
        rcases h with h|h
        · exact ⟨1,h⟩
        · exact ⟨0,h⟩
      have perm := frame_perm fr
      rw [raw,atCenter] at perm
      exact LocalizedMarkedMolecularConfiguration.readback_perm_congr (frameRow r) _
        (by unfold frameRow; split <;> decide) (by unfold frameRow; split <;> rfl)
        (perm.trans (graphRows r)) (same r)
    · have hit := (RingRootTwinDecision.detected_iff i root fr.center).mpr (twin raw fr.center h root selected)
      obtain ⟨p,hp⟩ := Option.isSome_iff_exists.mp hit
      exact (missed (by simp [RingRootTwinDecision.direct,fr.recognized,on,hp])).elim
  · intro a hp
    have gate : RingAtomicNeighborOrder.neutralPyramidal i.molecule a.val = true := (Bool.and_eq_true_iff.mp (RingPhysicalFrameBridge.focusP_phosphorus hp)).1
    have eq := no_pyramids ⟨a.val,atom_bound raw a⟩
    rw [raw] at gate
    simp [gate] at eq

theorem state {i : Input} (raw : i.molecule = molecule) (x : SpatialConfiguration)
    (full : x.positions.length = RingSpatialTransport.size i)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (moved : LocalizedChemicalRing.coordinatesAdmitted (RingSpatialTransport.atGeometry i x full) = true)
    (same : SignsAgree i.spatial x) (q : RingActivePairs.Site i) (selected : Selected q.val.root.val) :
    RingChemicalGraphProof.state i q = RingChemicalGraphProof.state (RingSpatialTransport.atGeometry i x full)
      (RingSpatialTransport.reindexSite i x full q) :=
  RingTwinCoordinateTransport.state i x full admit moved (residual raw x same _ selected) q rfl

theorem unselected {i : Input} (raw : i.molecule = molecule)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) (v : i.certified.Atom) (off : ¬ Selected v.val) :
    RingChemicalGraphProof.root i v = some none := by
  by_cases four : Fintype.card (i.certified.moleculeGraph.Neighbor v) = 4
  · let c : i.certified.TetrahedralCenter := ⟨v,(i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mpr four⟩
    let z := toAtom i 0 (by rw [raw]; decide)
    obtain ⟨p,hp,_,_⟩ := twin raw c off z (Or.inl rfl)
    have result := p.root_refusal admit
    rw [hp] at result
    exact result
  · have inactive : ¬ RingEligibleGraph.Eligible (RingPyramidalPublication.eligible i) (RingGroupedReport.origin i v) := by
      rintro ⟨_,b,current,on⟩
      obtain rfl : v = b := Option.some.inj current
      have ng : RingAtomicNeighborOrder.neutralPyramidal i.molecule v.val = false := raw ▸ no_pyramids ⟨v.val,atom_bound raw v⟩
      have notP : RingPyramidalPublication.phosphorus i v = false := by
        change (RingAtomicNeighborOrder.neutralPyramidal i.molecule v.val && _) = false
        simp [ng]
      simp [RingPyramidalPublication.eligible,four,notP] at on
    exact (RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i) v).trans
      ((RingChemicalGraphProof.state_eq i _).trans (RingChemicalGraphProof.skips i _ _ inactive))

theorem root {i : Input} (raw : i.molecule = molecule) (x : SpatialConfiguration)
    (full : x.positions.length = RingSpatialTransport.size i)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (moved : LocalizedChemicalRing.coordinatesAdmitted (RingSpatialTransport.atGeometry i x full) = true)
    (same : SignsAgree i.spatial x) (a : i.certified.Atom) :
    RingChemicalGraphProof.root i a = RingChemicalGraphProof.root (RingSpatialTransport.atGeometry i x full) a := by
  let j := RingSpatialTransport.atGeometry i x full
  by_cases selected : Selected a.val
  · have roots (u : Input) (v : u.certified.Atom) :
        RingChemicalGraphProof.root u v = RingChemicalGraphProof.state u (RingGroupedReport.origin u v) :=
      RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips u) v
    rw [roots,roots,←RingSpatialTransport.reindex_origin i x full]
    exact state raw x full admit moved same _ selected
  · exact (unselected raw admit a selected).trans ((unselected (i := j) raw moved a selected).symm)

open private row? from TetraStereo.Engine.RingChemicalReport

/-- All atom requests are included. Invalid IDs fail on both tables and every
off-center atom returns the same completed refusal. -/
theorem raw_report {i j : Input} (left : i.molecule = molecule) (right : j.molecule = molecule)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (admit' : LocalizedChemicalRing.coordinatesAdmitted j = true)
    (same : SignsAgree i.spatial j.spatial) (ids : List Nat) :
    RingHydrogenReport.fromRaw? molecule i.spatial ids = RingHydrogenReport.fromRaw? molecule j.spatial ids := by
  have graph := left.trans right.symm
  let full := RingSpatialTransport.full_at_other graph
  let target := RingSpatialTransport.atGeometry i j.spatial full
  have moved : LocalizedChemicalRing.coordinatesAdmitted target = true := by
    rw [show target = j from RingSpatialTransport.eq_atGeometry graph]; exact admit'
  have accepted := RingSpatialTransport.readmit i
  rw [left] at accepted
  have accepted' := RingSpatialTransport.readmit target
  change LocalizedChemicalRing.admitRawSpatial? i.molecule j.spatial = some target at accepted'
  rw [left] at accepted'
  cases found : RingMolecularReport.resolve i ids with
  | none =>
    have failed : RingMolecularReport.resolve target ids = none := found
    simp [RingHydrogenReport.fromRaw_closed_eq closed,RingChemicalReport.fromRaw?,accepted,accepted',found,failed]
  | some vs =>
    rw [← (RingMolecularReport.resolve_iff i ids vs).mp found]
    have l := RingWrittenPHReadings.fromRaw_closed_report i (left ▸ closed) admit vs
    have r := RingWrittenPHReadings.fromRaw_closed_report target (left ▸ closed) moved vs
    rw [left] at l
    change RingHydrogenReport.fromRaw? i.molecule j.spatial _ = _ at r
    rw [left] at r
    refine l.trans (Eq.trans ?_ r.symm)
    apply RingFrameTransport.mapM_congr_mem
    intro a _
    exact congrArg (Option.map (fun v => (a.val,v))) (root left j.spatial full admit moved same a)

/-- The four ordered pairs of definite R/S readings suffice to cover all
admitted geometries, without assuming any reference reports or root labels. -/
theorem four_sign_classes {i : Input} (raw : i.molecule = molecule)
    (admit : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    ∃ a b : RS, readback? (geometry i.spatial) (frameRow 0) = some a ∧
      readback? (geometry i.spatial) (frameRow 1) = some b ∧
      ∀ (j : Input), j.molecule = molecule → LocalizedChemicalRing.coordinatesAdmitted j = true →
        readback? (geometry j.spatial) (frameRow 0) = some a →
        readback? (geometry j.spatial) (frameRow 1) = some b →
        ∀ ids, RingHydrogenReport.fromRaw? molecule i.spatial ids = RingHydrogenReport.fromRaw? molecule j.spatial ids := by
  obtain ⟨a,ha⟩ := Option.isSome_iff_exists.mp (AntipodalCyclohexaneHands.nonflat raw admit 0)
  obtain ⟨b,hb⟩ := Option.isSome_iff_exists.mp (AntipodalCyclohexaneHands.nonflat raw admit 1)
  refine ⟨a,b,ha,hb,?_⟩
  intro j raw' ok ja jb ids
  apply raw_report raw raw' admit ok _ ids
  intro r
  fin_cases r
  · exact ha.trans ja.symm
  · exact hb.trans jb.symm

end TetraStereo.Examples.AntipodalCyclohexaneTransport
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneTransport.state
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneTransport.unselected
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneTransport.four_sign_classes
