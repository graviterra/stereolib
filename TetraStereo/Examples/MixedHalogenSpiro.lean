import TetraStereo.Engine.PublicAPI

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 40000
set_option Elab.async false

namespace TetraStereo.Examples.MixedHalogenSpiro
open OneCenter Engine LocalizedGenericMarkedRecalculation RingChemicalPriority Recursive

/-- Each methine of the first cyclopropane bears fluorine, and each
methine of the second bears chlorine. The two rings share carbon zero. -/
def molecule : RawMolecule := {CentresRingSpiroCasing.molecule with
  atoms := List.replicate 5 (.aliphatic .C) ++ List.replicate 2 (.aliphatic .F) ++
    List.replicate 2 (.aliphatic .Cl) ++ List.replicate 4 (.aliphatic .H)}

def geometry : Geometry := fun i => CentresRingSpiroCasing.spatial.positions[i]?

/-- Exchanging F and H at peripheral carbon 1 inverts its configuration. -/
def inverted : Geometry := fun i => geometry (if i = 5 then 9 else if i = 9 then 5 else i)

structure Observation where
  verdict : Option Reading
  publications : Nat
  reversals : Nat
  actual : List (List Nat)
  reflected : List (List Nat)
  eligible : List Nat
  deriving DecidableEq, Repr

def inspect (g : Geometry) : Option Observation := do
  let c ← deriveRingReferenceOccurrence? molecule g 2 3 [0]
  let f := (← c.frame? 2).toMolecularFrame
  let table := ReferenceFrame.entries f.rows
  return ⟨c.verdict,c.published.length,f.reversals,ReferenceFrame.orders f.ids table false,
    ReferenceFrame.orders f.ids table true,ReferenceFrame.marks f.ids table⟩

/-- Chlorinated arms outrank fluorinated arms. Within each pair the two
orders reverse, giving an even permutation and hence an uppercase letter. -/
theorem original : inspect geometry = some
    ⟨some ⟨.R,.S⟩,8,2,[[3,4,1,2]],[[4,3,2,1]],[]⟩ := by decide +kernel

theorem reflected : inspect (mirror geometry) = some
    ⟨some ⟨.S,.R⟩,8,2,[[4,3,2,1]],[[3,4,1,2]],[]⟩ := by decide +kernel

/-- The fluorinated pair becomes equivalent under one local inversion.
The chlorinated pair still reverses; neither geometry has a strict order. -/
theorem one_inversion : inspect inverted = some ⟨none,8,1,[],[],[1,2]⟩ := by decide +kernel

private def positions (g : Geometry) : SpatialConfiguration :=
  ⟨(List.range molecule.atoms.length).filterMap g⟩

/-- The public request sends the configuration of the selected carbon. -/
def centralRequest (g : Geometry) : Option String := do
  let input ← LocalizedChemicalRing.admitRawSpatial? molecule (positions g)
  (CentresRing.request input [0]).toOption

private def originalInput :=
  (LocalizedChemicalRing.admitRawSpatial? molecule (positions geometry)).get (by decide +kernel)
private def invertedInput :=
  (LocalizedChemicalRing.admitRawSpatial? molecule (positions inverted)).get (by decide +kernel)

open LocalizedChemicalRingPhysicalAdmission LocalizedActualPhysicalBranchDecision
open CertifiedLocalizedCIPInput

/-- List enumeration gives the same canonical order as sorting the graph neighbor set. -/
private def neighbors (i : CertifiedLocalizedCIPInput) (a : i.Atom) : List i.Atom :=
  (List.finRange _).filter fun b => decide (i.moleculeGraph.Adj a b)

private theorem canonical_neighbors (i : CertifiedLocalizedCIPInput) (c : i.TetrahedralCenter) :
    i.canonicalNeighborList c = neighbors i c.1 := by
  apply (Finset.sortedLT_sort _).eq_of_mem_iff
  · exact ((List.sortedLT_finRange _).pairwise.sublist (List.filter_sublist ..)).sortedLT
  · intro x
    simp [neighbors, Finset.mem_sort, MoleculeGraph.mem_neighborFinset]

private def directVolume (i : CertifiedLocalizedCIPInput) (xs : List i.Atom) : Option ℚ := do
  let a ← i.spatialPointAt? (← xs[0]?)
  let b ← i.spatialPointAt? (← xs[1]?)
  let c ← i.spatialPointAt? (← xs[2]?)
  let d ← i.spatialPointAt? (← xs[3]?)
  return CartesianPoint3.orientedVolume a b c d

private theorem coordinates_of_neighbor_volumes (i : LocalizedChemicalRing.Input)
    (h : ∀ a : i.certified.Atom, (neighbors i.certified a).length = 4 →
      (directVolume i.certified (neighbors i.certified a)).any (· != 0) = true) :
    LocalizedChemicalRing.coordinatesAdmitted i = true := by
  apply decide_eq_true
  intro c
  let z : i.certified.TetrahedralCenter := c
  have four := i.certified.canonicalNeighborList_length z
  have proof := h z.1 (canonical_neighbors _ z ▸ four)
  rw [← canonical_neighbors _ z] at proof
  have eqn : directVolume i.certified (i.certified.canonicalNeighborList z) = coordinateVolume? i.certified c := by
    unfold directVolume coordinateVolume?
    simp only [List.getElem?_eq_getElem (by omega : 0 < (i.certified.canonicalNeighborList z).length),
      List.getElem?_eq_getElem (by omega : 1 < (i.certified.canonicalNeighborList z).length),
      List.getElem?_eq_getElem (by omega : 2 < (i.certified.canonicalNeighborList z).length),
      List.getElem?_eq_getElem (by omega : 3 < (i.certified.canonicalNeighborList z).length)]
    rfl
  rw [eqn] at proof
  unfold centerAdmitted
  cases hv : coordinateVolume? i.certified c <;> simp_all

private theorem center_zero_mem_inventory (i : LocalizedChemicalRing.Input) (center : i.certified.Atom)
    (hz : center.val = 0) (hw : center ∈ i.certified.tetrahedralCenterSet) :
    (CentresRing.inventory i).contains 0 = true := by
  apply List.contains_iff_mem.mpr
  apply List.mem_map.mpr
  exact ⟨⟨center,hw⟩,(i.certified.mem_canonicalTetrahedralCenters_iff _).mpr hw,hz⟩

private theorem originalCoordinates : LocalizedChemicalRing.coordinatesAdmitted originalInput = true :=
  coordinates_of_neighbor_volumes _ (by decide +kernel)
private theorem invertedCoordinates : LocalizedChemicalRing.coordinatesAdmitted invertedInput = true :=
  coordinates_of_neighbor_volumes _ (by decide +kernel)
private theorem originalInventory : (CentresRing.inventory originalInput).contains 0 = true :=
  center_zero_mem_inventory _ ⟨0,by decide +kernel⟩ rfl (by decide +kernel)
private theorem invertedInventory : (CentresRing.inventory invertedInput).contains 0 = true :=
  center_zero_mem_inventory _ ⟨0,by decide +kernel⟩ rfl (by decide +kernel)

private theorem originalAdmission : LocalizedChemicalRing.admitRawSpatial? molecule (positions geometry) = some originalInput :=
  (Option.some_get _).symm
private theorem invertedAdmission : LocalizedChemicalRing.admitRawSpatial? molecule (positions inverted) = some invertedInput :=
  (Option.some_get _).symm

private theorem requests :
    centralRequest geometry = centralRequest inverted ∧ (centralRequest geometry).isSome = true := by
  unfold centralRequest
  rw [originalAdmission,invertedAdmission]
  change (CentresRing.request originalInput [0]).toOption = (CentresRing.request invertedInput [0]).toOption ∧
    (CentresRing.request originalInput [0]).toOption.isSome = true
  have memOriginal := List.contains_iff_mem.mp originalInventory
  have memInverted := List.contains_iff_mem.mp invertedInventory
  have originalFrame : frameAtoms? originalInput.molecule (canonicalCenterRoot 0) =
      some [1,2,3,4] := by decide +kernel
  have invertedFrame : frameAtoms? invertedInput.molecule (canonicalCenterRoot 0) =
      some [1,2,3,4] := by decide +kernel
  have originalRead : readback? (LocalizedChemicalRingPhysicalSense.inputGeometry originalInput.certified)
      [1,2,3,4] = some .R := by decide +kernel
  have invertedRead : readback? (LocalizedChemicalRingPhysicalSense.inputGeometry invertedInput.certified)
      [1,2,3,4] = some .R := by decide +kernel
  simp [CentresRing.request, originalCoordinates, invertedCoordinates, memOriginal, memInverted,
    List.mapM_cons, List.mapM_nil, originalFrame, invertedFrame, originalRead, invertedRead]
  exact ⟨rfl,rfl⟩

/-- Both coordinate inputs pass the public gates and serialize identically. -/
theorem sparse_request_collision :
    centralRequest geometry = centralRequest inverted ∧
    (centralRequest geometry).isSome = true ∧
    (∀ i : Fin 13, (positions geometry).positions[i.val]? = geometry i ∧
      (positions inverted).positions[i.val]? = inverted i) := by
  exact ⟨requests.1,requests.2,by decide +kernel⟩

/-- Even a perfect decoder of the selected center's request cannot recover
its molecular verdict on both configurations. The unlisted fluorinated
carbon changes what can be assigned at the listed spiro center. -/
theorem no_central_request_decoder :
    ¬ ∃ decode : String → Option Reading, ∀ g ∈ [geometry,inverted],
      (centralRequest g).map decode = (inspect g).map Observation.verdict := by
  rintro ⟨decode,h⟩
  have a := h geometry (List.mem_cons_self ..)
  have b := h inverted (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  rw [sparse_request_collision.1, original] at a
  rw [one_inversion] at b
  exact (by decide : (some (some ⟨.R,.S⟩) : Option (Option Reading)) ≠ some none) (a.symm.trans b)

end TetraStereo.Examples.MixedHalogenSpiro

assert_kernel_only TetraStereo.Examples.MixedHalogenSpiro.original
assert_kernel_only TetraStereo.Examples.MixedHalogenSpiro.reflected
assert_kernel_only TetraStereo.Examples.MixedHalogenSpiro.one_inversion
assert_kernel_only TetraStereo.Examples.MixedHalogenSpiro.sparse_request_collision
assert_kernel_only TetraStereo.Examples.MixedHalogenSpiro.no_central_request_decoder
