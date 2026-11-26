import TetraStereo.Engine.RingHydrogenReport
import TetraStereo.Engine.RingHydrogenNeighbors

set_option autoImplicit false
namespace TetraStereo.Engine.RingWrittenPHReadings
open OneCenter RingHydrogenCompletion RingPyramidalChoices
open CertifiedLocalizedCIPInput (descriptorOfOrientedVolume? descriptorOfPriorityOrderedPoints?)
open LocalizedGenericMarkedRecalculation (Geometry readback? mirror)
open RationalTetrahedralPermutation (pointVector permutedOrientedVolume)

/-- An explicit geometry on the completed graph. Only selected terminal P-bound hydrogens
may move, and each one gives a nondegenerate pyramidal frame. -/
structure Placement (m : RawMolecule) (g : SpatialConfiguration) (out : RawMolecule)
    (pos written : SpatialConfiguration) : Prop where
  full : written.positions.length = pos.positions.length
  fixed : ∀ k, (∀ s ∈ sites m g out pos, s.hydrogen ≠ k) → written.positions[k]? = pos.positions[k]?
  hand : ∀ s ∈ sites m g out pos, ∃ h, written.positions[s.hydrogen]? = some h ∧
    CartesianPoint3.orientedVolume s.firstPoint s.secondPoint h s.center ≠ 0

def geometry (g : SpatialConfiguration) : Geometry := fun n => g.positions[n]?

def oriented (g : SpatialConfiguration) (rev : Bool) : Geometry :=
  if rev then mirror (geometry g) else geometry g

def order (ids : Fin 4 → Nat) (π : Equiv.Perm (Fin 4)) :=
  [ids (π 0),ids (π 1),ids (π 2),ids (π 3)]

def row (s : Site) : Fin 4 → Nat := ![s.first,s.second,s.hydrogen,s.parent]

private theorem row_readback (s : Site) (geom : Geometry) (h : Point)
    (first : geom s.first = some s.firstPoint) (second : geom s.second = some s.secondPoint)
    (hydrogen : geom s.hydrogen = some h) (parent : geom s.parent = some s.center)
    (π : Equiv.Perm (Fin 4)) :
    readback? geom (order (row s) π) =
      descriptorOfOrientedVolume? (permutedOrientedVolume s.firstPoint s.secondPoint h s.center π) := by
  have get (k : Fin 4) : geom (row s k) = some (pointVector s.firstPoint s.secondPoint h s.center k) := by
    fin_cases k
    · exact first
    · exact second
    · exact hydrogen
    · exact parent
  simp only [readback?,order,List.mapM_cons,get]
  rfl

theorem original_position {m out : RawMolecule} {g pos w : SpatialConfiguration}
    (p : Placement m g out pos w) (cert : Certified m g out pos) {k : Nat} (hk : k < m.atomCount) :
    w.positions[k]? = g.positions[k]? := by
  refine (p.fixed _ ?_).trans (cert.positions_getElem? hk)
  intro s hs eqn
  obtain ⟨_,_,valid⟩ := sites_valid hs
  have ge := valid.hydrogen_ge
  omega

/-- One enumerated full coordinate table reproduces every local phosphorus hand
from the supplied hydrogen coordinates, in the original and reflected geometries,
for all 24 orders at every selected site. Every unselected position agrees as well. -/
theorem represent_readbacks {m out : RawMolecule} {g pos w : SpatialConfiguration}
    (p : Placement m g out pos w) (cert : Certified m g out pos) :
    ∃ x ∈ variants m g out pos,
      (∀ k, (∀ s ∈ sites m g out pos, s.hydrogen ≠ k) → w.positions[k]? = x.positions[k]?) ∧
      ∀ s ∈ sites m g out pos, ∀ rev π,
        readback? (oriented w rev) (order (row s) π) =
        readback? (oriented x rev) (order (row s) π) := by
  let written (s : Site) := w.positions[s.hydrogen]?.getD zeroVector
  have seen s (hs : s ∈ sites m g out pos) :
      w.positions[s.hydrogen]? = some (written s) ∧
      CartesianPoint3.orientedVolume s.firstPoint s.secondPoint (written s) s.center ≠ 0 := by
    obtain ⟨h,atH,nz⟩ := p.hand s hs
    simpa [written,atH] using nz
  obtain ⟨x,hx,rep⟩ := variants_represent_positions m out g pos written fun s hs => (seen s hs).2
  refine ⟨x,hx,fun k hk => (p.fixed k hk).trans (variants_getElem?_of_not_site hx hk).symm,?_⟩
  intro s hs rev π
  obtain ⟨h,xh,equal⟩ := rep s hs
  obtain ⟨xp,xf,xs,_⟩ := variants_site_frame cert hx hs
  obtain ⟨n,_,valid⟩ := sites_valid hs
  obtain ⟨hp,_,_,_,_,cp,fp,sp,_,_,_,_,_,pn,fn',sn⟩ := valid
  have wp : geometry w s.parent = some s.center := hp ▸ (original_position p cert pn).trans cp
  have wf := (original_position p cert fn').trans fp
  have ws := (original_position p cert sn).trans sp
  have bare : readback? (geometry w) (order (row s) π) = readback? (geometry x) (order (row s) π) :=
    (row_readback s _ _ wf ws (seen s hs).1 wp π).trans
      ((equal π).symm.trans (row_readback s _ _ xf xs xh xp π).symm)
  cases rev <;> simp [oriented,LocalizedGenericMarkedRecalculation.readback_mirror,bare]

end TetraStereo.Engine.RingWrittenPHReadings
assert_kernel_only TetraStereo.Engine.RingWrittenPHReadings.represent_readbacks

namespace TetraStereo.Engine.RingWrittenPHReadings
open OneCenter RingHydrogenCompletion RingPyramidalChoices
open LocalizedGenericMarkedRecalculation (readback?)
open LocalizedChemicalRing (Input)

/-- Every order on four tetrahedral ligands and every pyramidal order with the
center in the phantom slot, on both geometries. -/
structure PhysicalAgreement (i : Input) (w x : SpatialConfiguration) : Prop where
  tetra : ∀ (c : i.certified.TetrahedralCenter)
    (d : Fin 4 ≃ i.certified.moleculeGraph.Neighbor c.val) rev (π : Equiv.Perm (Fin 4)),
    readback? (oriented w rev) (order (fun k => (d k).val.val) π) =
    readback? (oriented x rev) (order (fun k => (d k).val.val) π)
  phosphorus : ∀ (a : i.certified.Atom), RingPyramidalPublication.phosphorus i a = true →
    ∀ (d : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a) rev,
    readback? (oriented w rev) (order (phosphorusFrameIds d) 1) =
    readback? (oriented x rev) (order (phosphorusFrameIds d) 1)

private theorem readback_of_points {w x : SpatialConfiguration} (ids : Fin 4 → Nat)
    (same : ∀ k, w.positions[ids k]? = x.positions[ids k]?) (rev : Bool) (π : Equiv.Perm (Fin 4)) :
    readback? (oriented w rev) (order ids π) = readback? (oriented x rev) (order ids π) := by
  have bare : readback? (geometry w) (order ids π) = readback? (geometry x) (order ids π) := by
    simp only [readback?,order,List.mapM_cons,List.mapM_nil,geometry,same]
  cases rev <;> simp [oriented,LocalizedGenericMarkedRecalculation.readback_mirror,bare]

theorem represent_all_centers {m out : RawMolecule} {g pos w : SpatialConfiguration}
    (p : Placement m g out pos w) (cert : Certified m g out pos)
    (i : Input) (same : i.molecule = out) :
    ∃ x ∈ variants m g out pos, PhysicalAgreement i w x := by
  obtain ⟨x,hx,fixed,reads⟩ := represent_readbacks p cert
  refine ⟨x,hx,?_,?_⟩
  · intro c d rev π
    exact readback_of_points _ (fun k => fixed _ (fun s hs =>
      (selected_hydrogen_ne_tetra_ligand cert hs i same c (d k)).symm)) rev π
  · intro a ph d rev
    rcases phosphorus_frame_dichotomy cert i same a ph d with untouched | ⟨s,hs,π,located⟩
    · exact readback_of_points _ (fun k => fixed _ (fun s hs => (untouched s hs k).symm)) rev 1
    · have ids : order (phosphorusFrameIds d) 1 = order (row s) π := by
        simp only [order,Equiv.Perm.one_apply,located,selectedFrameIds,row]
      rw [ids]
      exact reads s hs rev π

end TetraStereo.Engine.RingWrittenPHReadings
assert_kernel_only TetraStereo.Engine.RingWrittenPHReadings.represent_all_centers
