import TetraStereo.Engine.RingRankedPathOrder
import TetraStereo.Engine.RingRule4bFirstDifference
import TetraStereo.Engine.RingRule4bHandOrbit
import TetraStereo.Engine.RingSignedInventoryLayers

/-! The complete ranked path rows preserve strict Rule 4b order and ties,
including when an uppercase donor is an ancestor of another donor. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingRule4bPathOrder
open OneCenter RingStereoSiblingPass RingFullPathPairs RingRule5Shape RingRule5SeedExchange
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)
open private Good Good.mk Good.edge slotKind grow_row slot_descending nextSlots root_good from
  TetraStereo.Engine.RingRule4bPathDecoding

private theorem endpoint {i f r rev d} (ready : @RingGroupedStereo.Ready i f r) :
    RingRankedPathOrder.Endpoint (fun s n => Good f r rev s d n) (likeAt i r rev)
      (fun n slot => RingUnitTypeTransitions.emits (slotKind d n slot)) := by
  intro s n v good
  obtain ⟨vv,on,p,k,len,_,edge,kind⟩ := good
  exact ⟨p,k,len,edge,(RingUnitTypeTransitions.emits_exact ready rev
    (⟨v.cursor,vv,on⟩ : RingUnitTypeTransitions.Carrier f) s).trans (congrArg RingUnitTypeTransitions.emits kind)⟩

private theorem next_order {i f r rev s d n row blocks next} (ready : @RingGroupedStereo.Ready i f r)
    (good : ∀ v ∈ row, Good f r rev s d n v)
    (grow : List.Forall₂ ((stage i r rev []).Expansion (likeAt i r rev s)) row blocks)
    (sort : Legal FullVisit.path blocks.flatten next) :
    (∀ v ∈ next, Good f r rev s d (n+1) v) ∧
    next.map (fun v => eraseEndpoint v.path) =
      order id ((row.map FullVisit.path).flatMap (nextSlots f r rev d n)) := by
  obtain ⟨gn,perm⟩ := grow_row ready good grow sort
  have legal : Legal id _ _ := ⟨perm,by simpa using slot_descending gn sort.descending⟩
  exact ⟨gn,by simpa using ((legal_iff ..).mp legal).2⟩

/-- Compare the first differing sphere, then the first differently ranked path in that
sphere. The procedure agrees in both strict directions and on ties at arbitrary depth. -/
theorem layers_compare {i f r rev s t} (ready : @RingGroupedStereo.Ready i f r)
    {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (tie : RingUnitTypeTransitions.key i r rev a = RingUnitTypeTransitions.key i r rev b)
    {out out' rows rows'}
    (left : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev s))
      [Oracle.root (likeAt i r rev s) a] out rows)
    (right : Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev t))
      [Oracle.root (likeAt i r rev t) b] out' rows') :
    compare (out.filterMap (fun v => likeAt i r rev s v.cursor))
      (out'.filterMap (fun v => likeAt i r rev t v.cursor)) = compare rows rows' := by
  apply RingRankedPathOrder.walk_compare (stage i r rev [])
    (endpoint (d := RingUnitTypeTransitions.key i r rev a) ready) (nextSlots f r rev _)
    (fun _ _ _ _ _ => next_order ready) left right 0
  · intro v hv
    obtain rfl := List.mem_singleton.mp hv
    exact root_good va oa rfl
  · intro v hv
    obtain rfl := List.mem_singleton.mp hv
    exact root_good vb ob tie.symm
  · simp [Oracle.root,eraseEndpoint,stripBit_step]

open RingStereoSphereInventory (Inventory inventory? reading)
open RingSignedInventoryLayers (projectInventory)
open private sign from TetraStereo.Engine.RingFullPathPairs

private theorem fixed_read {i f r rev s} (ready : @RingGroupedStereo.Ready i f r)
    {a : Arm i} (va : Valid a) (oa : On f a) {inv : Inventory}
    (hit : inventory? i r rev [] a = some inv) :
    pairs? i r rev s a = some (reading s inv) ∧
    ∃ out, Layers FullVisit.path ((stage i r rev []).Expansion (likeAt i r rev s))
      [Oracle.root (likeAt i r rev s) a] out (projectInventory s inv) ∧
      out.filterMap (fun v => likeAt i r rev s v.cursor) = reading s inv := by
  have read := RingStereoSphereInventory.reading_exact i r rev [] s a
  rw [hit] at read
  have got : pairs? i r rev s a = some (reading s inv) := read.symm
  obtain ⟨w,hw,eqn⟩ := source_exact ready rev s a va oa
  obtain rfl := Option.some.inj (hw.symm.trans got)
  obtain ⟨out,walk,bits⟩ := (eqn _).mpr rfl
  obtain ⟨rows,rec⟩ := record walk
  exact ⟨got,out,(RingSignedInventoryLayers.inventory_layers r rev [] s a hit rec).symm ▸ rec,bits.symm⟩

theorem inventory_compare {i f r rev} (ready : @RingGroupedStereo.Ready i f r)
    {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (tie : RingUnitTypeTransitions.key i r rev a = RingUnitTypeTransitions.key i r rev b)
    {x y : Inventory} (hx : inventory? i r rev [] a = some x) (hy : inventory? i r rev [] b = some y)
    (s t : RS) :
    compare (reading s x) (reading t y) = compare (projectInventory s x) (projectInventory t y) := by
  obtain ⟨_,u,ru,bu⟩ := fixed_read (s := s) ready va oa hx
  obtain ⟨_,v,rv,bv⟩ := fixed_read (s := t) ready vb ob hy
  simpa only [bu,bv] using layers_compare ready va vb oa ob tie ru rv

/-- A reference is selected by the ordered path populations alone. -/
private def preferred (x : Inventory) : RS :=
  if compare (projectInventory .R x) (projectInventory .S x) = .lt then .S else .R

private theorem prefer_eq {i f r rev} (ready : @RingGroupedStereo.Ready i f r) {a : Arm i}
    (va : Valid a) (oa : On f a) {x : Inventory} (h : inventory? i r rev [] a = some x) :
    max (reading .R x) (reading .S x) = reading (preferred x) x := by
  have cmp := inventory_compare ready va va oa oa rfl h h .R .S
  have law (u v : List Bool) : compare u v = .lt ↔ u < v :=
    DeclarativeCIP.compareLex_eq_lt_iff_of compare (fun _ _ => by decide +revert)
      (fun _ _ => Std.compare_eq_eq_iff_eq) u v
  unfold preferred
  rw [←cmp]
  split
  next lt => exact max_eq_right ((law _ _).mp lt).le
  next ge => exact max_eq_left (le_of_not_gt (mt (law _ _).mpr ge))

/-- Use the lexicographically larger of the two reference projections. -/
def canonical (x : Inventory) := projectInventory (preferred x) x

/-- The entire preferred-reference comparison is the order of the canonical
ranked sphere tables under the same through-4a hypothesis. -/
theorem canonical_compare {i f r rev} (ready : @RingGroupedStereo.Ready i f r)
    {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (tie : RingUnitTypeTransitions.key i r rev a = RingUnitTypeTransitions.key i r rev b)
    {x y : Inventory} (hx : inventory? i r rev [] a = some x) (hy : inventory? i r rev [] b = some y) :
    compare (max (reading .R x) (reading .S x)) (max (reading .R y) (reading .S y)) =
      compare (canonical x) (canonical y) := by
  rw [prefer_eq ready va oa hx,prefer_eq ready vb ob hy]
  exact inventory_compare ready va vb oa ob tie hx hy _ _

private theorem total {i f r rev} (ready : @RingGroupedStereo.Ready i f r)
    {a : Arm i} (va : Valid a) (oa : On f a) : ∃ x, inventory? i r rev [] a = some x := by
  obtain ⟨w,hw,_⟩ := source_exact ready rev .R a va oa
  have h := RingStereoSphereInventory.reading_exact i r rev [] .R a
  change _ = pairs? i r rev .R a at h
  rw [hw] at h
  exact (Option.map_eq_some_iff.mp h).imp (fun _ p => p.1)

/-- On every pair that enters Rule 4b on the public store, directly compare the
two canonical tables of paths. There is no ancestry or branch-exchange premise. -/
theorem public_order {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (rev : Bool) {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b) :
    let r := RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f
    RingUnitTypeTransitions.key i r rev a = RingUnitTypeTransitions.key i r rev b →
      ∃ x y, inventory? i r rev [] a = some x ∧ inventory? i r rev [] b = some y ∧
        hanson? i r rev a b = some (sign (compare (canonical x) (canonical y))) := by
  intro r tie
  have ready : RingGroupedStereo.Ready f r := RingChemicalGraphProof.ready geom f
  obtain ⟨x,hx⟩ := total (rev := rev) ready va oa
  obtain ⟨y,hy⟩ := total (rev := rev) ready vb ob
  refine ⟨x,y,hx,hy,?_⟩
  simp only [hanson?,(fixed_read (s := .R) ready va oa hx).1,(fixed_read (s := .S) ready va oa hx).1,
    (fixed_read (s := .R) ready vb ob hy).1,(fixed_read (s := .S) ready vb ob hy).1,
    Option.bind_eq_bind,Option.bind_some,Option.pure_def,RingOccurrenceStereo.fourLists_order]
  rw [canonical_compare ready va vb oa ob tie hx hy]

end TetraStereo.Engine.RingRule4bPathOrder
assert_kernel_only TetraStereo.Engine.RingRule4bPathOrder.layers_compare
assert_kernel_only TetraStereo.Engine.RingRule4bPathOrder.public_order
