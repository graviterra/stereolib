import TetraStereo.Engine.RingHydrogenPlacementExact

/-! One canonical determinant per center and coordinate transport across atom numberings. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingNumberedHydrogenGeometry
open OneCenter
open LocalizedChemicalRing (Input)
open RingSpatialTransport
variable {i j : Input}

/-- Pull the source coordinate table through an arbitrary atom bijection. Every target
atom receives exactly the source point of its inverse image. -/
def sourcePoint (i : Input) (a : i.certified.Atom) : CartesianPoint3 :=
  i.spatial.positions[a.val]'(by rw [full_original i]; exact a.isLt)

def reindexed (i j : Input) (e : i.certified.Atom ≃ j.certified.Atom) : SpatialConfiguration :=
  ⟨List.ofFn fun b : j.certified.Atom => sourcePoint i (e.symm b)⟩

@[simp] theorem reindexed_full (e : i.certified.Atom ≃ j.certified.Atom) :
    (reindexed i j e).positions.length = size j := List.length_ofFn

@[simp] theorem sourcePoint_lookup (a : i.certified.Atom) :
    i.spatial.positions[a.val]? = some (sourcePoint i a) := by
  simp [sourcePoint]

@[simp] theorem reindexed_lookup (e : i.certified.Atom ≃ j.certified.Atom) (b : j.certified.Atom) :
    (reindexed i j e).positions[b.val]? = i.spatial.positions[(e.symm b).val]? := by
  simp [reindexed,b.isLt]

@[simp] theorem reindexed_lookup_image (e : i.certified.Atom ≃ j.certified.Atom) (a : i.certified.Atom) :
    (reindexed i j e).positions[(e a).val]? = i.spatial.positions[a.val]? := by
  rw [reindexed_lookup,e.symm_apply_apply]

theorem reindexed_lookup_nat (e : i.certified.Atom ≃ j.certified.Atom) (n : Nat) :
    (reindexed i j e).positions[n]? =
      if h : n < size j then i.spatial.positions[(e.symm ⟨n,h⟩).val]? else none := by
  by_cases h : n < size j
  · rw [dif_pos h]
    exact reindexed_lookup e ⟨n,h⟩
  · rw [dif_neg h]
    exact List.getElem?_eq_none (by rw [reindexed_full]; omega)

/-- A structurally admitted target with the exact pulled-back source coordinates. -/
def withSourceGeometry (i j : Input) (e : i.certified.Atom ≃ j.certified.Atom) : Input :=
  atGeometry j (reindexed i j e) (reindexed_full e)

@[simp] theorem withSourceGeometry_spatial (e : i.certified.Atom ≃ j.certified.Atom) :
    (withSourceGeometry i j e).spatial = reindexed i j e := rfl

@[simp] theorem withSourceGeometry_molecule (e : i.certified.Atom ≃ j.certified.Atom) :
    (withSourceGeometry i j e).molecule = j.molecule := rfl

theorem readmit_reindexed (e : i.certified.Atom ≃ j.certified.Atom) :
    LocalizedChemicalRing.admitRawSpatial? j.molecule (reindexed i j e) =
      some (withSourceGeometry i j e) := admit_atGeometry j _ _

theorem geometry_lookup (e : i.certified.Atom ≃ j.certified.Atom) (b : j.certified.Atom) :
    LocalizedChemicalRingPhysicalSense.inputGeometry (withSourceGeometry i j e).certified b.val =
      LocalizedChemicalRingPhysicalSense.inputGeometry i.certified (e.symm b).val := by
  rw [LocalizedChemicalRingPhysicalSense.inputGeometry_val,
    LocalizedChemicalRingPhysicalSense.inputGeometry_val]
  simp only [OneCenter.CertifiedLocalizedCIPInput.spatialPointAt?,
    (withSourceGeometry i j e).spatial_eq,i.spatial_eq,withSourceGeometry_spatial]
  exact reindexed_lookup e b

theorem coordinatesAdmitted_eq (e : i.certified.Atom ≃ j.certified.Atom)
    (agree : RingWrittenPHReadings.PhysicalAgreement j j.spatial (reindexed i j e)) :
    LocalizedChemicalRing.coordinatesAdmitted (withSourceGeometry i j e) =
      LocalizedChemicalRing.coordinatesAdmitted j :=
  RingWrittenPHReadings.coordinates_of_physicalAgreement j (reindexed i j e) (reindexed_full e) agree

/-- Native raw outputs agree for every Nat request under physical frame agreement,
including invalid IDs and global coordinate-admission rejection. -/
theorem native_eq (e : i.certified.Atom ≃ j.certified.Atom)
    (closed : RingHydrogenCompletion.plan j.molecule = [])
    (agree : RingWrittenPHReadings.PhysicalAgreement j j.spatial (reindexed i j e)) (ids : List Nat) :
    RingHydrogenReport.fromRaw? (withSourceGeometry i j e).molecule
      (withSourceGeometry i j e).spatial ids =
    RingHydrogenReport.fromRaw? j.molecule j.spatial ids :=
  (RingWrittenPHReadings.fromRaw_physicalAgreement j closed (reindexed i j e) (reindexed_full e) agree ids).symm

end TetraStereo.Engine.RingNumberedHydrogenGeometry
assert_kernel_only TetraStereo.Engine.RingNumberedHydrogenGeometry.reindexed_lookup
assert_kernel_only TetraStereo.Engine.RingNumberedHydrogenGeometry.native_eq

namespace TetraStereo.Engine.RingWrittenPHReadings
open OneCenter RingPyramidalChoices
open LocalizedChemicalRing (Input)
open LocalizedGenericMarkedRecalculation
variable {i : Input}

/-- Any permutation of a four-position frame is determined by one raw hand, including
missing coordinates and zero volume. -/
theorem order_readback_congr {g h : Geometry} (ids : Fin 4 → Nat)
    (same : readback? g (order ids 1) = readback? h (order ids 1)) (π : Equiv.Perm (Fin 4)) :
    readback? g (order ids π) = readback? h (order ids π) := by
  have selection (xs : List (Fin 4)) :
      atomsAt? [ids 0,ids 1,ids 2,ids 3] (xs.map Fin.val) = some (xs.map ids) := by
    have lookup (k : Fin 4) : [ids 0,ids 1,ids 2,ids 3][k.val]? = some (ids k) := by fin_cases k <;> rfl
    induction xs with
    | nil => rfl
    | cons k ks ih =>
      unfold atomsAt? at ih ⊢
      simp only [List.map_cons,List.mapM_cons,lookup,ih]
      rfl
  have permutation : ((List.finRange 4).map (fun k => (π k).val)).Perm [0,1,2,3] := by
    exact π.map_finRange_perm.map Fin.val
  have left := LocalizedMarkedConfigurationTransport.reordered_readback_partial g ids _ permutation
  have right := LocalizedMarkedConfigurationTransport.reordered_readback_partial h ids _ permutation
  have select := selection ((List.finRange 4).map π)
  simp only [List.map_map,Function.comp_def] at select
  rw [select] at left right
  have row : ((List.finRange 4).map fun k => ids (π k)) = order ids π := rfl
  rw [row] at left right
  change readback? g (order ids π) = _ at left
  change readback? h (order ids π) = _ at right
  rw [left,right]
  change readback? g [ids 0,ids 1,ids 2,ids 3] = readback? h [ids 0,ids 1,ids 2,ids 3] at same
  rw [same]

noncomputable def tetraEnumeration (i : Input) (c : i.certified.TetrahedralCenter) :
    Fin 4 ≃ i.certified.moleculeGraph.Neighbor c.val :=
  Equiv.ofBijective (i.certified.canonicalLigandNeighbor c) (i.certified.canonicalLigandNeighbor_bijective c)

noncomputable def phosphorusEnumeration (i : Input) (a : i.certified.Atom)
    (hp : RingPyramidalPublication.phosphorus i a = true) :
    Fin 3 ≃ i.certified.moleculeGraph.Neighbor a :=
  (Fintype.equivFinOfCardEq (by
    simp only [RingPyramidalPublication.phosphorus,Bool.and_eq_true,decide_eq_true_eq] at hp
    exact hp.2)).symm

/-- One written determinant per tetrahedral centre and per eligible phosphorus,
using fixed neighbour enumerations. No mirror or permutation is assumed. -/
def CanonicalPhysicalAgreement (i : Input) (w x : SpatialConfiguration) : Prop :=
  (∀ c, readback? (geometry w) (order (fun k => ((tetraEnumeration i c) k).val.val) 1) =
    readback? (geometry x) (order (fun k => ((tetraEnumeration i c) k).val.val) 1)) ∧
  (∀ a hp, readback? (geometry w) (order (phosphorusFrameIds (phosphorusEnumeration i a hp)) 1) =
    readback? (geometry x) (order (phosphorusFrameIds (phosphorusEnumeration i a hp)) 1))

theorem phosphorus_order_reindex {a : i.certified.Atom}
    (d d₀ : Fin 3 ≃ i.certified.moleculeGraph.Neighbor a) :
    ∃ π : Equiv.Perm (Fin 4), π 3 = 3 ∧
      ∀ k, phosphorusFrameIds d k = phosphorusFrameIds d₀ (π k) := by
  suffices range : ∀ k, ∃ v, phosphorusFrameIds d k = phosphorusFrameIds d₀ v by
    obtain ⟨π,hπ⟩ := exists_perm_of_injective_range_subset _ _ (phosphorusFrameIds_injective d) range
    refine ⟨π,?_,hπ⟩
    apply phosphorusFrameIds_injective d₀
    exact (hπ 3).symm

  have range (v : Fin 3) : ∃ k : Fin 4, (d v).val.val = phosphorusFrameIds d₀ k := by
    obtain ⟨k,hk⟩ := d₀.surjective (d v)
    fin_cases k
    · exact ⟨0,congrArg (fun n => n.val.val) hk.symm⟩
    · exact ⟨1,congrArg (fun n => n.val.val) hk.symm⟩
    · exact ⟨2,congrArg (fun n => n.val.val) hk.symm⟩
  intro k
  fin_cases k
  · exact range 0
  · exact range 1
  · exact range 2
  · exact ⟨3,rfl⟩

theorem canonicalPhysicalAgreement_iff (w x : SpatialConfiguration) :
    CanonicalPhysicalAgreement i w x ↔ PhysicalAgreement i w x := by
  constructor
  · rintro ⟨tetra,phos⟩
    constructor
    · intro c d rev π
      let d₀ := tetraEnumeration i c
      let σ : Equiv.Perm (Fin 4) := d.trans d₀.symm
      have row : order (fun k => (d k).val.val) π = order (fun k => (d₀ k).val.val) (π.trans σ) := by
        simp [order,σ]
      have read := order_readback_congr _ (tetra c) (π.trans σ)
      rw [←row] at read
      cases rev <;> simp [oriented,readback_mirror,read]
    · intro a hp d rev
      obtain ⟨π,_,hπ⟩ := phosphorus_order_reindex d (phosphorusEnumeration i a hp)
      have row : order (phosphorusFrameIds d) 1 = order (phosphorusFrameIds (phosphorusEnumeration i a hp)) π := by
        simp only [order,Equiv.Perm.one_apply,hπ]
      have read := order_readback_congr _ (phos a hp) π
      rw [←row] at read
      cases rev <;> simp [oriented,readback_mirror,read]
  · intro pa
    constructor
    · intro c
      exact pa.tetra c (tetraEnumeration i c) false 1
    · intro a hp
      exact pa.phosphorus a hp (phosphorusEnumeration i a hp) false

end TetraStereo.Engine.RingWrittenPHReadings
assert_kernel_only TetraStereo.Engine.RingWrittenPHReadings.canonicalPhysicalAgreement_iff
