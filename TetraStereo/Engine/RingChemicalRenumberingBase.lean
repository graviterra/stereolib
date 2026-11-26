import TetraStereo.Engine.RingOxaziridineNitrogenTransport
import TetraStereo.Engine.RingRawRenumbering
import TetraStereo.Engine.RingFrameTransport

set_option autoImplicit false
namespace TetraStereo.Engine.RingReportRenumber
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingRawRenumbering (AtomMap)
open RingRawRenumbering.AtomMap (arm site carrier)
open RingPyramidalPublication (focusP phosphorus)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingFrameTransport (senseOf)
variable {i j : Input}

def renameId (r : AtomMap i j) (n : Nat) : Nat :=
  if h : n < i.certified.certified.input.molecule.atomCount then (r.atoms ⟨n,h⟩).val else n

@[simp] theorem rename_val (r : AtomMap i j) (a : i.certified.Atom) : renameId r a.val = (r.atoms a).val := by
  simp [renameId,a.isLt]

theorem id_current (r : AtomMap i j) (q : Arm i) :
    ((arm r q).occurrence.val.node.current?.map Fin.val) =
      (q.occurrence.val.node.current?.map Fin.val).map (renameId r) := by
  change (q.occurrence.val.node.current?.map r.atoms).map Fin.val = _
  cases q.occurrence.val.node.current? <;> simp

theorem frame_perm (r : AtomMap i j) (q : Site i) :
    ((RingRetainedAuxiliary.frame i.certified q).map (arm r)).Perm
      (RingRetainedAuxiliary.frame j.certified (site r q)) := by
  exact (carrier r).children ⟨q,none⟩ (by intro s h; cases h)

theorem geometry_id (r : AtomMap i j) (n : Nat) :
    inputGeometry i.certified n = inputGeometry j.certified (renameId r n) := by
  have sizeEq : i.certified.certified.input.molecule.atomCount = j.certified.certified.input.molecule.atomCount := by
    simpa using Fintype.card_congr r.atoms
  by_cases h : n < i.certified.certified.input.molecule.atomCount
  · let a : i.certified.Atom := ⟨n,h⟩
    change inputGeometry i.certified a.val = inputGeometry j.certified (renameId r a.val)
    simp [LocalizedChemicalRingPhysicalSense.inputGeometry_val,spatialPointAt?,i.spatial_eq,j.spatial_eq,r.positions]
  · have k : ¬n < j.certified.certified.input.molecule.atomCount := by omega
    simp [inputGeometry,renameId,h,k]

theorem read_ids (r : AtomMap i j) (rev : Bool) (xs : List Nat) :
    senseOf (inputGeometry i.certified) rev xs =
      senseOf (inputGeometry j.certified) rev (xs.map (renameId r)) := by
  have lookup : xs.mapM (inputGeometry i.certified) = (xs.map (renameId r)).mapM (inputGeometry j.certified) := by
    induction xs with
    | nil => rfl
    | cons x xs ih => simp only [List.map_cons,List.mapM_cons,geometry_id r x,ih]
  have actual : readback? (inputGeometry i.certified) xs = readback? (inputGeometry j.certified) (xs.map (renameId r)) :=
    congrArg (fun v => v.bind descriptorOfPriorityOrderedPoints?) lookup
  cases rev <;> simp [senseOf,readback_mirror,actual]

def neighbors (r : AtomMap i j) (a : i.certified.Atom) :
    i.certified.moleculeGraph.Neighbor a ≃ j.certified.moleculeGraph.Neighbor (r.atoms a) where
  toFun b := ⟨r.atoms b.val,(r.adj a b.val).mp b.property⟩
  invFun b := ⟨r.atoms.symm b.val,(r.adj a _).mpr (by simpa using b.property)⟩
  left_inv _ := Subtype.ext (r.atoms.symm_apply_apply _)
  right_inv _ := Subtype.ext (r.atoms.apply_symm_apply _)

theorem phosphorus_atom (r : AtomMap i j) (a : i.certified.Atom) :
    phosphorus j (r.atoms a) = phosphorus i a := by
  let selected (bridgehead : Bool) (record : RingRawRenumbering.MolecularRecord) :=
    ((record.element == .P || record.element == .As || record.element == .Sb) ||
      (record.element == .N && bridgehead)) && record.charge == 0 && !record.aromatic
  have projected (v : Option AtomSpec) (bridgehead : Bool) :
      v.any (fun atom => ((atom.element == .P || atom.element == .As || atom.element == .Sb) ||
        (atom.element == .N && bridgehead)) && atom.charge == 0 && !atom.aromatic) =
        (v.map RingRawRenumbering.molecularRecord).any (selected bridgehead) := by cases v <;> rfl
  simp only [phosphorus,projected,r.records,← Fintype.card_congr (neighbors r a)]
  rw [RingPyramidalNitrogen.constrained_atomMap r a]

theorem focus_atom (r : AtomMap i j) (q : Site i) :
    focusP j (site r q) = (focusP i q).map r.atoms := by
  unfold focusP
  change (if q.val.node.provenance = .realAtom then
    (q.val.node.current?.map r.atoms).filter (phosphorus j) else none) = _
  split_ifs <;> cases q.val.node.current? <;> simp [Option.filter,phosphorus_atom]

theorem site_origin (r : AtomMap i j) (a : i.certified.Atom) :
    site r (RingGroupedReport.origin i a) = RingGroupedReport.origin j (r.atoms a) :=
  RingGroupedReport.origin_unique _ rfl

open RingActiveDistanceSchedule (View Rule Visible distance height frozen evaluate)

theorem frozen_site (r : AtomMap i j) (q : Site i) (s : View i) (t : View j)
    (earlier : ∀ v, Visible q v → s v = t (site r v)) (v : Site i) :
    frozen s q v = frozen t (site r q) (site r v) := by
  by_cases on : v.val.root = q.val.root
  · have on' : (site r v).val.root = (site r q).val.root := ((RingRawRenumbering.AtomMap.presentation r).root q v).mpr on
    by_cases ok : Visible q v
    · have ok' := (RingRawRenumbering.AtomMap.visible r q v).mpr ok
      simp only [frozen,if_neg (not_not_intro on),if_neg (not_not_intro on'),if_pos ok.2,if_pos ok'.2,earlier v ok]
    · have off : ¬(distance q < distance v ∧ v.val.node.current? ≠ some q.val.root) := fun cond => ok ⟨on,cond⟩
      have off' : ¬(distance (site r q) < distance (site r v) ∧ (site r v).val.node.current? ≠ some (site r q).val.root) :=
        fun h => ok ((RingRawRenumbering.AtomMap.visible r q v).mp ⟨on',h⟩)
      simp only [frozen,if_neg (not_not_intro on),if_neg (not_not_intro on'),if_neg off,if_neg off']
  · have off : (site r v).val.root ≠ (site r q).val.root := mt ((RingRawRenumbering.AtomMap.presentation r).root q v).mp on
    simp only [frozen,if_pos on,if_pos off]

open RingNestedActivePair (Frame)
open RingGroupedCentre (cursor)
open RingActivePairReport (Slot)

theorem frame_incident (r : AtomMap i j) {q : Site i} {x : Frame i q} {y : Frame j (site r q)}
    (p : RingGeometryTransport.FrameMap x y)
    (occ : ∀ u, p.carrier.domain u → (p.carrier.image u).occurrence = site r u.occurrence) (k : Slot) :
    arm r (cursor x k) = cursor y (p.slots k) := by
  have e := (occ _ (p.covers k)).symm.trans (congrArg _ (p.incident k))
  exact congrArg (fun t : Site j => (⟨t,some (site r q)⟩ : Arm j)) e
end TetraStereo.Engine.RingReportRenumber
