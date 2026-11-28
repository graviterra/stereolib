import TetraStereo.Engine.RingRankedPathOrder
import TetraStereo.Engine.RingRule5Tie
import TetraStereo.Engine.RingSignedInventoryLayers
import TetraStereo.Engine.RingChemicalGraphProof

/-! The complete ranked path rows preserve strict Rule 5 order and ties,
including when an uppercase donor is an ancestor of another donor. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingRule5PathOrder
open OneCenter RingStereoSiblingPass RingFullPathPairs RingRule5Shape RingRule5SeedExchange
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingRetainedReferenceGroup (Path)
open private Good Good.mk Good.edge slotKind grow_row slot_descending nextSlots root_good from
  TetraStereo.Engine.RingRule5Tie

private theorem endpoint {i f r rev d} (ready : @RingGroupedStereo.Ready i f r) :
    RingRankedPathOrder.Endpoint (fun s n => Good f r rev s d n) (likeAt i r rev)
      (fun n slot => RingRule5Shape.emits (slotKind d n slot)) := by
  intro s n v good
  obtain ⟨vv,on,p,k,len,_,edge,kind⟩ := good
  exact ⟨p,k,len,edge,(RingRule5Shape.emits_exact ready rev
    (⟨v.cursor,vv,on⟩ : RingRule5Shape.Carrier f) s).trans (congrArg RingRule5Shape.emits kind)⟩

private theorem next_order {i f r rev s d n row blocks next} (ready : @RingGroupedStereo.Ready i f r)
    (good : ∀ v ∈ row, Good f r rev s d n v)
    (grow : List.Forall₂ ((stage i r rev [.lowercase]).Expansion (likeAt i r rev s)) row blocks)
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
    (tie : RingRule5Shape.key i r rev a = RingRule5Shape.key i r rev b)
    {out out' rows rows'}
    (left : Layers FullVisit.path ((stage i r rev [.lowercase]).Expansion (likeAt i r rev s))
      [Oracle.root (likeAt i r rev s) a] out rows)
    (right : Layers FullVisit.path ((stage i r rev [.lowercase]).Expansion (likeAt i r rev t))
      [Oracle.root (likeAt i r rev t) b] out' rows') :
    compare (out.filterMap (fun v => likeAt i r rev s v.cursor))
      (out'.filterMap (fun v => likeAt i r rev t v.cursor)) = compare rows rows' := by
  apply RingRankedPathOrder.walk_compare (stage i r rev [.lowercase])
    (endpoint (d := RingRule5Shape.key i r rev a) ready) (nextSlots f r rev _)
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


private theorem fixed_read {i f r rev s} (ready : @RingGroupedStereo.Ready i f r)
    {a : Arm i} (va : Valid a) (oa : On f a) {inv : Inventory}
    (hit : inventory? i r rev [.lowercase] a = some inv) :
    RingFullPathRule5.word? i r rev s a = some (reading s inv) ∧
    ∃ out, Layers FullVisit.path ((stage i r rev [.lowercase]).Expansion (likeAt i r rev s))
      [Oracle.root (likeAt i r rev s) a] out (projectInventory s inv) ∧
      out.filterMap (fun v => likeAt i r rev s v.cursor) = reading s inv := by
  have read := RingStereoSphereInventory.reading_exact i r rev [.lowercase] s a
  rw [hit] at read
  have got : RingFullPathRule5.word? i r rev s a = some (reading s inv) := read.symm
  obtain ⟨w,hw,eqn⟩ := RingFullPathRule5.word_exact rev (RingOccurrenceStereo.rank_total ready rev [.lowercase]) s a va oa
  obtain rfl := Option.some.inj (hw.symm.trans got)
  obtain ⟨out,walk,bits⟩ := (eqn _).mpr rfl
  obtain ⟨rows,rec⟩ := record walk
  exact ⟨got,out,(RingSignedInventoryLayers.inventory_layers r rev [.lowercase] s a hit rec).symm ▸ rec,bits.symm⟩

theorem inventory_compare {i f r rev} (ready : @RingGroupedStereo.Ready i f r)
    {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (tie : RingRule5Shape.key i r rev a = RingRule5Shape.key i r rev b)
    {x y : Inventory} (hx : inventory? i r rev [.lowercase] a = some x) (hy : inventory? i r rev [.lowercase] b = some y)
    (s t : RS) :
    compare (reading s x) (reading t y) = compare (projectInventory s x) (projectInventory t y) := by
  obtain ⟨_,u,ru,bu⟩ := fixed_read (s := s) ready va oa hx
  obtain ⟨_,v,rv,bv⟩ := fixed_read (s := t) ready vb ob hy
  simpa only [bu,bv] using layers_compare ready va vb oa ob tie ru rv

private theorem total {i f r rev} (ready : @RingGroupedStereo.Ready i f r)
    {a : Arm i} (va : Valid a) (oa : On f a) :
    ∃ x, inventory? i r rev [.lowercase] a = some x := by
  obtain ⟨w,hw,_⟩ := RingFullPathRule5.word_exact rev
    (RingOccurrenceStereo.rank_total ready rev [.lowercase]) .R a va oa
  have h := RingStereoSphereInventory.reading_exact i r rev [.lowercase] .R a
  change _ = RingFullPathRule5.word? i r rev .R a at h
  rw [hw] at h
  exact (Option.map_eq_some_iff.mp h).imp (fun _ p => p.1)

/-- Both fixed seed comparisons, including their combined signed score, follow
from the two ranked path tables on the public frozen reader. -/
theorem public_order {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (f : Site i) (rev : Bool) {a b : Arm i} (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b) :
    let r := RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f
    key i r rev a = key i r rev b →
      ∃ x y, inventory? i r rev [.lowercase] a = some x ∧ inventory? i r rev [.lowercase] b = some y ∧
        (∀ s : RS, RingFullPathRule5.word? i r rev s a = some (reading s x) ∧
          RingFullPathRule5.word? i r rev s b = some (reading s y) ∧
          compare (reading s x) (reading s y) = compare (projectInventory s x) (projectInventory s y)) ∧
        RingFullPathRule5.score? i r rev a b = some (RingOccurrenceStereo.fixedScore
          (compare (projectInventory .R x) (projectInventory .R y))
          (compare (projectInventory .S x) (projectInventory .S y))) := by
  intro r tie
  have ready : RingGroupedStereo.Ready f r := RingChemicalGraphProof.ready geom f
  obtain ⟨x,hx⟩ := total (rev := rev) ready va oa
  obtain ⟨y,hy⟩ := total (rev := rev) ready vb ob
  have cmp := inventory_compare ready va vb oa ob tie hx hy
  refine ⟨x,y,hx,hy,fun s => ⟨(fixed_read ready va oa hx).1,(fixed_read ready vb ob hy).1,cmp s s⟩,?_⟩
  simp [RingFullPathRule5.score?,(fixed_read (s := .R) ready va oa hx).1,
    (fixed_read (s := .S) ready va oa hx).1,(fixed_read (s := .R) ready vb ob hy).1,
    (fixed_read (s := .S) ready vb ob hy).1,cmp]

end TetraStereo.Engine.RingRule5PathOrder
assert_kernel_only TetraStereo.Engine.RingRule5PathOrder.layers_compare
assert_kernel_only TetraStereo.Engine.RingRule5PathOrder.public_order
