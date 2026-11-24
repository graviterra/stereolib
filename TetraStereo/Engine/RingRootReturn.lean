import TetraStereo.Engine.RingRootReturnPath
import TetraStereo.OneCenter.LocalizedActualOutwardRule1bEquivalence
import TetraStereo.OneCenter.LocalizedActualBoundaryPathRealization

/-! # Original-root Rule 6 from the molecular root-duplicate count -/

set_option autoImplicit false
namespace TetraStereo.Engine.RingRootReturn
open OneCenter CertifiedLocalizedCIPInput
attribute [local instance] lexOrd
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm)
open RingActivePairReport (Slot)
open RingNestedActivePair (Frame)
open RingGroupedCentre (cursor)
open RingGroupedReport (origin)
open RingRetainedChemicalTrace (Reaches)
open LocalizedActualBoundaryPathRealization (mem_executableOfficialCIPChildren_iff)

theorem root_arm {i : Input} {r : i.certified.Atom} (fr : Frame i (origin i r)) (j : Slot) :
    ∃ x : i.certified.Atom, i.certified.moleculeGraph.Adj r x ∧
      (cursor fr j).occurrence.val.node = OfficialCIPNode.rootFromEdge r x ∧
      LocalizedCumulativeDecoratedTree.LocalizedRerootCursorIncomingParent i.certified (cursor fr j) ∧
      RingGroupedTrials.atom fr j = x.val := by
  let f := origin i r
  let q := cursor fr j
  have adj := (fr.direction j).property
  change i.certified.LocalizedCarrierTreeAdjacent q.occurrence.val f.val at adj
  have addr : f.val.address = [] := rfl
  obtain ⟨root,h | ⟨len,drop⟩⟩ := adj
  · simp [addr] at h
  have n : q.occurrence.val.address.length = 1 := by simpa [addr] using len.symm
  obtain ⟨slot,hs⟩ := List.length_eq_one_iff.mp n
  have path : q.occurrence.val.address = f.val.address ++ [slot] := hs
  obtain ⟨node,mem,eqn⟩ := i.certified.declarativeLocalizedOccurrence_immediate_child
    ((i.certified.mem_localizedOccurrences_iff _ _).mp f.property)
    ((i.certified.mem_localizedOccurrences_iff _ _).mp q.occurrence.property) root slot path
  have seen : q.occurrence.val.node = node := congrArg LocalizedCIPOccurrenceFrame.node eqn
  have listed : node ∈ i.certified.executableOfficialCIPChildren (OfficialCIPNode.root r) :=
    List.fst_mem_of_mem_zipIdx mem
  obtain ⟨x,hx,edge,_⟩ := (mem_executableOfficialCIPChildren_iff i.certified i.single _ rfl rfl _).mp listed
  have ne : x ≠ r := fun h => i.certified.moleculeGraph.underlyingSimpleGraph.loopless.irrefl r (h ▸ edge)
  have term : q.occurrence.val.node = OfficialCIPNode.rootFromEdge r x := by
    rw [seen,hx]
    simp [OfficialCIPNode.extend,OfficialCIPNode.rootFromEdge,OfficialCIPNode.root,OfficialCIPNode.childProvenance,ne]
  refine ⟨x,edge,term,⟨f,rfl,root.symm,drop,len⟩,?_⟩
  have point := fr.point_at j
  change q.occurrence.val.node.current?.map Fin.val = some (RingGroupedTrials.atom fr j) at point
  rw [term] at point
  exact (Option.some.inj point).symm

private def State {i : Input} (r x : i.certified.Atom) (q : Arm i) : Prop :=
  LocalizedCumulativeDecoratedTree.LocalizedRerootCursorIncomingParent i.certified q ∧ r ∈ q.occurrence.val.node.history ∧
  (q.occurrence.val.node.provenance = .realAtom ∨ q.occurrence.val.node.isDuplicateLeaf = true) ∧
  ∃ a, q.occurrence.val.node.current? = some a ∧
    ((a = r ∧ q.occurrence.val.node.isDuplicateLeaf = true) ∨
      ∃ w : i.certified.moleculeGraph.underlyingSimpleGraph.Walk x a, r ∉ w.support)

private theorem step {i : Input} {r x : i.certified.Atom} {q u : Arm i}
    (h : State r x q) (mem : u ∈ i.certified.executableLocalizedRerootChildren q) : State r x u := by
  obtain ⟨inc,hist,kind,a,current,way⟩ := h
  have eqs := LocalizedActualOutwardRule1bEquivalence.outwardChildren_nodes_perm_executable i.certified
    (Nat.le_succ _) q inc (i.certified.executableLocalizedRerootChildren_declarative q)
  have member := eqs.mem_iff.mp (List.mem_map_of_mem (f := fun c : Arm i => c.occurrence.val.node) mem)
  have leaf : q.occurrence.val.node.isDuplicateLeaf ≠ true := by
    intro bad
    simp [CertifiedLocalizedCIPInput.executableOfficialCIPChildren,bad] at member
  obtain ⟨y,hy,edge,_⟩ := (mem_executableOfficialCIPChildren_iff i.certified i.single _ current
    (kind.resolve_right leaf) _).mp member
  change u.occurrence.val.node = q.occurrence.val.node.extend y 0 at hy
  obtain ⟨walk,avoids⟩ := way.resolve_left (fun h => leaf h.2)
  have valid := i.certified.localizedRerootCursorValid_of_incoming q inc
  obtain ⟨prev,hp,_,_,len⟩ := inc
  obtain ⟨drop,d,root,previous,_⟩ := i.certified.outward_edge q u
    valid
    prev hp (by omega) mem
  refine ⟨⟨q.occurrence,previous,root.symm,drop.symm,d.symm⟩,?_,?_,y,?_,?_⟩
  · simp [hy,hist]
  · by_cases old : y ∈ q.occurrence.val.node.history <;>
      simp [hy,OfficialCIPNode.extend,OfficialCIPNode.childProvenance,old,OfficialCIPNode.isDuplicateLeaf,
        OfficialCIPNodeProvenance.isDuplicateLeaf]
  · rw [hy]; rfl
  · by_cases back : y = r
    · subst y
      exact Or.inl ⟨rfl,by simp [hy,OfficialCIPNode.isDuplicateLeaf,OfficialCIPNode.extend,
        OfficialCIPNode.childProvenance,hist,OfficialCIPNodeProvenance.isDuplicateLeaf]⟩
    · exact Or.inr ⟨walk.concat edge,by simpa [SimpleGraph.Walk.support_concat,Ne.symm back] using avoids⟩

theorem walk_of_reach {i : Input} {r x y : i.certified.Atom} {q v : Arm i}
    (start : q.occurrence.val.node = OfficialCIPNode.rootFromEdge r x)
    (inc : LocalizedCumulativeDecoratedTree.LocalizedRerootCursorIncomingParent i.certified q) (hx : x ≠ r) (hy : y ≠ r)
    (reach : Reaches i q v) (found : v.occurrence.val.node.current? = some y) :
    ∃ w : i.certified.moleculeGraph.underlyingSimpleGraph.Walk x y, r ∉ w.support := by
  have initial : State r x q := by
    refine ⟨inc,?_,Or.inl ?_,x,?_,Or.inr ⟨.nil,?_⟩⟩
    · simp [start,OfficialCIPNode.rootFromEdge]
    · simp [start,OfficialCIPNode.rootFromEdge]
    · simp [start,OfficialCIPNode.rootFromEdge]
    · simpa using Ne.symm hx
  have along {a b : Arm i} (p : Reaches i a b) : State r x a → State r x b := by
    induction p with
    | here => exact id
    | descend member _ ih => exact fun st => ih (step st member)
  obtain ⟨_,_,_,a,obs,way⟩ := along reach initial
  obtain rfl := Option.some.inj (obs.symm.trans found)
  exact way.resolve_left (fun h => hy h.1)


/-- Count each origin-zero closure at its actual address in this original digraph once. -/
def rootCopies (i : Input) (r : i.certified.Atom) :=
  (RingActiveDistanceSchedule.sites i).filter fun s =>
    s.val.root == r && s.val.node.provenance == .ringDuplicate 0

theorem mem_rootCopies {i : Input} {r : i.certified.Atom} (q : RingActivePairs.Site i) :
    q ∈ rootCopies i r ↔ q.val.root = r ∧ q.val.node.provenance = .ringDuplicate 0 := by
  simp [rootCopies,RingActiveDistanceSchedule.sites]

theorem rootCopies_nodup (i : Input) (r : i.certified.Atom) : (rootCopies i r).Nodup :=
  (List.Nodup.attach (i.certified.localizedOccurrences_nodup _)).filter _

private theorem coordinates {i : Input} {q u : Arm i}
    (inc : LocalizedCumulativeDecoratedTree.LocalizedRerootCursorIncomingParent i.certified q)
    (reach : Reaches i q u) :
    u.occurrence.val.root = q.occurrence.val.root ∧ q.occurrence.val.address <+: u.occurrence.val.address := by
  induction reach with
  | here => exact ⟨rfl,List.prefix_refl _⟩
  | @descend q c t edge _ ih =>
    have valid := i.certified.localizedRerootCursorValid_of_incoming q inc
    obtain ⟨prev,hp,_,_,len⟩ := inc
    obtain ⟨drop,d,root,previous,_⟩ := i.certified.outward_edge q c valid prev hp (by omega) edge
    obtain ⟨rt,p⟩ := ih ⟨q.occurrence,previous,root.symm,drop.symm,d.symm⟩
    have nonempty : c.occurrence.val.address ≠ [] := by intro e; simp [e] at d
    have pref : q.occurrence.val.address <+: c.occurrence.val.address :=
      ⟨[c.occurrence.val.address.getLast nonempty],by rw [← drop,List.dropLast_concat_getLast]⟩
    exact ⟨rt.trans root,pref.trans p⟩

/-- Distinct returning arms supply distinct carrier occurrences even when all callbacks
point to the same atom. The first sibling slot of the address distinguishes the witnesses. -/
theorem returning_le_copies {i : Input} {r : i.certified.Atom} {fr : Frame i (origin i r)} {read}
    (arms : RingGroupedCentre.Arms fr read) :
    ((List.finRange 4).filter (RingPromotionCut.rootFlag arms)).length ≤ (rootCopies i r).length := by
  classical
  let js := (List.finRange 4).filter (RingPromotionCut.rootFlag arms)
  have witness (j : Slot) (member : j ∈ js) :
      ∃ s ∈ rootCopies i r, (cursor fr j).occurrence.val.address <+: s.val.address := by
    obtain ⟨v,reach,tag⟩ := (RingPromotionCut.rootFlag_iff arms j).mp (List.mem_filter.mp member).2
    obtain ⟨_,_,_,inc,_⟩ := root_arm fr j
    obtain ⟨rt,p⟩ := coordinates inc reach
    have atRoot : v.occurrence.val.root = r := rt.trans (fr.direction j).property.1
    exact ⟨v.occurrence,(mem_rootCopies _).mpr ⟨atRoot,tag⟩,p⟩
  let pick (j : Slot) := if h : j ∈ js then (witness j h).choose else origin i r
  have spec (j : Slot) (h : j ∈ js) : pick j ∈ rootCopies i r ∧
      (cursor fr j).occurrence.val.address <+: (pick j).val.address := by
    simpa only [pick,dif_pos h] using (witness j h).choose_spec
  have count : js.toFinset.card ≤ (rootCopies i r).toFinset.card := by
    apply Finset.card_le_card_of_injOn pick
    · intro j h
      exact List.mem_toFinset.mpr (spec j (List.mem_toFinset.mp h)).1
    · intro j hj k hk eqn
      by_contra ne
      have pj := (spec j (List.mem_toFinset.mp hj)).2
      have pk := (spec k (List.mem_toFinset.mp hk)).2
      rw [eqn] at pj
      have one (n : Slot) : (cursor fr n).occurrence.val.address.length = 1 := by
        obtain ⟨_,_,_,⟨prev,prevEq,_,_,len⟩,_⟩ := root_arm fr n
        change some (origin i r) = some prev at prevEq
        obtain rfl := Option.some.inj prevEq
        exact len.symm
      exact (fr.incident ne).2.1 ((List.prefix_iff_eq_take.mp pj).trans
        ((congrArg (fun n => (pick k).val.address.take n) ((one j).trans (one k).symm)).trans
          (List.prefix_iff_eq_take.mp pk).symm))
  exact (List.toFinset_card_of_nodup ((List.nodup_finRange 4).filter _)) ▸
    count.trans (rootCopies i r).toFinset_card_le

private theorem chain_of_support {i : Input} {x : i.certified.Atom} (tail : List i.certified.Atom)
    (h : List.IsChain i.certified.moleculeGraph.Adj (x :: tail)) :
    RingRootReturnPath.chainLinked i.certified x tail := by
  induction tail generalizing x with
  | nil => trivial
  | cons y ys ih =>
    exact ⟨(List.isChain_cons_cons.mp h).1,ih (List.isChain_cons_cons.mp h).2⟩

private theorem return_of_walk {i : Input} {r x y : i.certified.Atom} {fr : Frame i (origin i r)}
    (j : Slot) (node : (cursor fr j).occurrence.val.node = OfficialCIPNode.rootFromEdge r x)
    (xy : x ≠ y) (close : i.certified.moleculeGraph.Adj r y)
    (w : i.certified.moleculeGraph.underlyingSimpleGraph.Walk x y) (avoid : r ∉ w.support) :
    ∃ v, Reaches i (cursor fr j) v ∧ v.occurrence.val.node.provenance = .ringDuplicate 0 := by
  let p := w.bypass
  have nd := w.bypass_isPath.support_nodup
  have outside : r ∉ p.support := fun mem => avoid (w.support_bypass_subset mem)
  have shape : p.support = x :: p.support.tail := by
    simpa only [p.head_support] using (List.cons_head_tail (l := p.support) (by simp)).symm
  have last : RingRootReturnPath.chainEnd x p.support.tail = y := by
    rw [RingRootReturnPath.chainEnd_eq_getLast]
    simpa only [← shape] using p.getLast_support
  have nonempty : p.support.tail ≠ [] := by
    intro zero
    rw [zero] at last
    exact xy last
  obtain ⟨_,_,_,⟨prev,hprev,_,_,hlen⟩,_⟩ := root_arm fr j
  change some (origin i r) = some prev at hprev
  obtain rfl := Option.some.inj hprev
  refine RingRootReturnPath.arm_edge_root_return (cursor fr j) node hlen.symm ?_ p.support.tail nonempty ?_ ?_ ?_
  · intro previous he
    change some (origin i r) = some previous at he
    obtain rfl := Option.some.inj he
    exact Nat.zero_le _
  · apply chain_of_support
    rw [← shape]
    exact p.isChain_adj_support
  · rw [← shape]
    exact List.nodup_cons.mpr ⟨outside,nd⟩
  · rw [last]
    exact i.certified.moleculeGraph.underlyingSimpleGraph.symm close

/-- The arm contains an addressed duplicate of the original root. -/
def Returns {i : Input} (q : Arm i) : Prop :=
  ∃ v, Reaches i q v ∧ v.occurrence.val.node.provenance = .ringDuplicate 0

/-- A different marked neighbor reached in this original-root arm forces an
origin-zero duplicate down both the traversed and marked arm. -/
theorem cross_arm_closures {i : Input} {r : i.certified.Atom} (fr : Frame i (origin i r))
    {j s : Slot} (ne : j ≠ s) {v : Arm i}
    (reach : Reaches i (cursor fr j) v)
    (hit : v.occurrence.val.node.current?.map Fin.val = some (RingGroupedTrials.atom fr s)) :
    Returns (cursor fr j) ∧ Returns (cursor fr s) := by
  obtain ⟨x,ex,nx,ix,_⟩ := root_arm fr j
  obtain ⟨y,ey,ny,iy,ay⟩ := root_arm fr s
  have found : v.occurrence.val.node.current? = some y := by
    rw [ay] at hit
    obtain ⟨b,h,e⟩ := Option.map_eq_some_iff.mp hit
    exact h.trans (congrArg some (Fin.ext e))
  have exr : x ≠ r := fun h => i.certified.moleculeGraph.underlyingSimpleGraph.loopless.irrefl r (h ▸ ex)
  have eyr : y ≠ r := fun h => i.certified.moleculeGraph.underlyingSimpleGraph.loopless.irrefl r (h ▸ ey)
  have xy : x ≠ y := by
    intro eqn
    have ids := fr.physical.nodup_iff.mpr
      (List.Nodup.map (Fin.val_injective.comp (i.certified.canonicalLigandAtom_injective fr.center)) (List.nodup_finRange 4))
    have ax := fr.point_at j
    have by' := fr.point_at s
    change (cursor fr j).occurrence.val.node.current?.map Fin.val = _ at ax
    change (cursor fr s).occurrence.val.node.current?.map Fin.val = _ at by'
    rw [nx] at ax
    rw [ny,← eqn] at by'
    have equal := ids.get_inj_iff.mp (Option.some.inj (ax.symm.trans by'))
    have same := congrArg (fun k : Fin fr.ids.length => k.val) equal
    exact ne (Fin.ext same)
  obtain ⟨w,avoid⟩ := walk_of_reach nx ix exr eyr reach found
  exact ⟨return_of_walk j nx xy ey w avoid,
    return_of_walk s ny xy.symm ex w.reverse (by simpa using avoid)⟩

/-- Read the graph witnesses in the two molecular Rule 1b columns. -/
theorem cross_arm_returns {i : Input} {r : i.certified.Atom} {fr : Frame i (origin i r)} {read}
    (a : RingGroupedCentre.Arms fr read) {j s : Slot} (ne : j ≠ s) {v : Arm i}
    (reach : Reaches i (cursor fr j) v)
    (hit : v.occurrence.val.node.current?.map Fin.val = some (RingGroupedTrials.atom fr s)) :
    RingPromotionCut.rootFlag a j = true ∧ RingPromotionCut.rootFlag a s = true := by
  obtain ⟨left,right⟩ := cross_arm_closures fr ne reach hit
  exact ⟨(RingPromotionCut.rootFlag_iff a j).mpr left,(RingPromotionCut.rootFlag_iff a s).mpr right⟩

/-- Below the threshold the grouped evaluator can use the ordinary orientation.
This identity includes strict orders, a single tied pair and all promotion-eligible partitions. -/
theorem index_of_few_copies {i : Input} {r : i.certified.Atom} {fr : Frame i (origin i r)} {read}
    (a : RingGroupedCentre.Arms fr read) (ready : RingGroupedStereo.Ready (origin i r) read)
    (few : (rootCopies i r).length < 3) :
    RingOrientation.index a = RingOrientation.orientation (a.key false) := by
  by_cases gate : (RingGroupedOrders.marks a).length < 3
  · simp [RingOrientation.index,gate]
  have cert : RingPromotionCut.Check a := by
    refine ⟨by omega,le_trans (returning_le_copies a) (by omega),?_⟩
    intro s j off
    apply (RingPromotionCut.sameBits_neutral_iff _ _ (RingGroupedCentre.valid fr j)).mpr
    intro v reach hit
    have ne : j ≠ s := fun eqn => off (Or.inl eqn.symm)
    obtain ⟨hj,hs⟩ := cross_arm_returns a ne reach hit
    exact off (Or.inr ⟨hs,hj⟩)
  obtain ⟨s,hs⟩ := List.exists_mem_of_ne_nil _ (show RingGroupedOrders.marks a ≠ [] by intro h; simp [h] at gate)
  obtain ⟨t,ne,same⟩ := (RingGroupedOrders.marked_iff a s false).mp hs
  rw [RingPromotionCut.check_index ready cert,(RingOrientation.orientation_zero _).mpr (fun inj => ne (inj same))]

/-- Complete two-geometry publication without any Rule 6 trial at an original root
with fewer than three actual root duplicates. The earlier-rule ranking supplies the casing. -/
theorem publication_of_few_copies {i : Input} {r : i.certified.Atom}
    (c : RingGeometryCertificates.Context i (origin i r)) (few : (rootCopies i r).length < 3) :
    RingGroupedPublication.state i (origin i r) = some (RingGeometryCriterion.Signature.mk
      (RingOrientation.baseline c.fr * RingOrientation.orientation (c.arms.key false))
      (RingGeometryCriterion.reversals c.arms)).letters := by
  have ready : RingGroupedStereo.Ready (origin i r) c.read := by
    rw [c.geometric,RingGeometryCriterion.rootReader_exact c.coordinates]
    exact RingGroupedPublication.ready (RingGroupedGeometry.physical c.coordinates) _
  rw [← index_of_few_copies c.arms ready few]
  obtain ⟨s,hs,pub,_⟩ := RingGeometryCriterion.at_centre c.coordinates _ c.fr.recognized
  rw [RingGeometryCriterion.state_eq c.coordinates,← RingGeometryCriterion.rootReader_exact c.coordinates _,← c.geometric] at hs
  simp [RingGeometryCriterion.signature?,c.frame,c.profiles] at hs
  cases hs
  exact pub

open RingActiveDistanceSchedule (height distance frozen snapshot table)

/-- Stop after the depth-one batch. The original root has not been evaluated. -/
private def beforeRoot (i : Input) (r : i.certified.Atom) :=
  let selected : RingActiveDistanceSchedule.Rule i := fun q read =>
    if q.val.root = r then RingGeometryCriterion.rule i q read else none
  frozen (snapshot (table selected (height i))) (origin i r)

private theorem beforeRoot_exact (i : Input) (r : i.certified.Atom) :
    beforeRoot i r = frozen (RingGeometryCriterion.rootState i r) (origin i r) := by
  unfold beforeRoot RingGeometryCriterion.rootState RingGeometryCriterion.rootTable
  simp only [RingActiveDistanceSchedule.snapshot_table]
  funext t
  have zero : distance (origin i r) = 0 := rfl
  by_cases same : distance t = 0 <;>
    simp [frozen,zero,RingActiveDistanceSchedule.pass,RingActiveDistanceSchedule.batch_at,same]

/-- At the original root, skip promotions below the graph threshold. Auxiliary
publications use their existing frozen schedule, including their own promotion decisions. -/
def rootByCount (i : Input) (r : i.certified.Atom) : RingActiveDistanceSchedule.Cell :=
  let q := origin i r
  if i.certified.localizedOccurrenceDescriptorCenter? q = none then some none else do
    let fr ← RingNestedActivePair.frame? i q
    let read := beforeRoot i r
    let a ← RingGroupedCentre.arms? fr read
    let score := if (rootCopies i r).length < 3 then RingOrientation.orientation (a.key false)
      else RingOrientation.index a
    return (RingGeometryCriterion.Signature.mk (RingOrientation.baseline fr * score)
      (RingGeometryCriterion.reversals a)).letters

/-- Every admitted coordinate input and every requested atom has the same exact
publication under the count-based original-root rule. No frame or locality witness is supplied. -/
theorem rootByCount_exact (i : Input) (coords : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (r : i.certified.Atom) : rootByCount i r = RingGroupedPublication.state i (origin i r) := by
  let q := origin i r
  let read := RingActiveDistanceSchedule.frozen (RingGroupedPublication.state i) q
  have ready : RingGroupedStereo.Ready q read :=
    RingGroupedPublication.ready (RingGroupedGeometry.physical coords) q
  have law := RingActiveDistanceSchedule.evaluate_eq (RingGeometryCriterion.rule i) q
  have state : RingActiveDistanceSchedule.evaluate (RingGeometryCriterion.rule i) = RingGroupedPublication.state i :=
    (RingActiveDistanceSchedule.snapshot_table ..).symm.trans (RingGeometryCriterion.state_eq coords)
  rw [state] at law
  rw [law]
  have same := RingGeometryCriterion.rootReader_exact coords q
  change RingActiveDistanceSchedule.frozen (RingGeometryCriterion.rootState i r) q = read at same
  unfold rootByCount RingGeometryCriterion.rule
  dsimp only [q] at same ⊢
  rw [beforeRoot_exact,same]
  by_cases absent : i.certified.localizedOccurrenceDescriptorCenter? (origin i r) = none
  · simp [absent]
  · simp only [absent,if_false,RingGeometryCriterion.signature?]
    change (RingNestedActivePair.frame? i q >>= _) = (Option.map _ (RingNestedActivePair.frame? i q >>= _))
    cases hf : RingNestedActivePair.frame? i q with
    | none => rfl
    | some fr =>
      change (RingGroupedCentre.arms? fr read >>= _) = Option.map _ (RingGroupedCentre.arms? fr read >>= _)
      cases ha : RingGroupedCentre.arms? fr read with
      | none => rfl
      | some a =>
        by_cases few : (rootCopies i r).length < 3
        · simp [few,index_of_few_copies a ready few]
        · simp [few]

end TetraStereo.Engine.RingRootReturn

assert_kernel_only TetraStereo.Engine.RingRootReturn.cross_arm_closures
assert_kernel_only TetraStereo.Engine.RingRootReturn.cross_arm_returns
assert_kernel_only TetraStereo.Engine.RingRootReturn.publication_of_few_copies
assert_kernel_only TetraStereo.Engine.RingRootReturn.rootByCount_exact
