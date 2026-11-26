import TetraStereo.Engine.RingRule5Shape
import TetraStereo.Engine.RingPathRankTransport

/-! # Reconstructing the unlabelled part of a Rule 4b sphere

A complete through-4a priority determines which occurrences contribute a
bit and the whole multiset of priorities of their children. -/
set_option autoImplicit false

namespace TetraStereo.Engine.RingUnitTypeTransitions
open OneCenter RingStereoSiblingPass RingRetainedSeedFrames
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedStereoRefinement (Derives priority)
open RingRetainedChemicalTrace (Word)

abbrev kids (i : Input) (q : Arm i) := i.certified.executableLocalizedRerootChildren q
abbrev Valid {i : Input} (q : Arm i) := i.certified.LocalizedRerootCursorValid q
abbrev On {i : Input} (f : Site i) (q : Arm i) := q.occurrence.val.root = f.val.root

def key (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) : List Word :=
  ((priority i r rev [] q).map Branch.deep).getD []

/-- The fourth component is the Rule 4a word. Its first entry is the unit
class at the occurrence. Only class 2 contributes to the fixed-reference word. -/
abbrev emits := RingRule5Shape.emits

theorem emits_of_reading {i r rev q k} (h : Derives i r rev [] q k) (s : RS) :
    (RingFullPathPairs.likeAt i r rev s q).isSome = emits k.deep := by
  cases h with
  | node _ seen _ _ _ _ _ _ =>
    unfold RingFullPathPairs.likeAt RingFullPathPairs.handAt
    rw [seen]
    have status (lab : Option LocalizedTetrahedralRSPseudoDescriptor) :
        ((RingNestedActivePair.upper lab).map (· == s)).isSome =
          (some (RingNestedActivePair.unit lab) == some 2) := by
      rcases lab with _ | (h | h) <;> rfl
    exact status _

/-- Visibility is fixed by the through-4a endpoint type, independently of
input, reader, geometry and fixed reference hand. -/
theorem emits_tied_readings {i j : Input} {r : Reader i} {t : Reader j}
    {rev mir : Bool} {q : Arm i} {p : Arm j} {a b : Branch}
    (left : Derives i r rev [] q a) (right : Derives j t mir [] p b)
    (tie : a.deep = b.deep) (s u : RS) :
    (RingFullPathPairs.likeAt i r rev s q).isSome =
      (RingFullPathPairs.likeAt j t mir u p).isSome :=
  (emits_of_reading left s).trans ((congrArg emits tie).trans (emits_of_reading right u).symm)

private theorem key_state {i f r rev} (ready : @RingGroupedStereo.Ready i f r)
    (t : State i r rev) (on : On f t.q) : key i r rev t.q = (unit t).deep := by
  obtain ⟨k,h⟩ := RingOccurrenceStereo.rank_total ready rev [] t.q t.valid on
  change priority i r rev [] t.q = some k at h
  obtain rfl := RingRetainedStereoRefinement.unique [] _ _ _
    (RingRetainedStereoRefinement.source _ _ h) t.source.unit
  simp [key,h]

/-- Every successful molecular base priority has exactly four rule components. -/
theorem key_length {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (q : Arm i) (valid : Valid q) (on : On f q) :
    (key i r rev q).length = 4 := by
  obtain ⟨b,hb⟩ := RingOccurrenceStereo.rank_total ready rev [] q valid on
  change priority i r rev [] q = some b at hb
  have size := (RingRetainedSeedFrames.sizes [] q b (RingRetainedStereoRefinement.source [] q hb)).2
  simpa [key,hb] using size

private theorem row_perm {i f r rev} (ready : @RingGroupedStereo.Ready i f r)
    {a : State i r rev} {sh de : List (State i r rev)} (row : Directed unit a sh de)
    (on : ∀ c ∈ de, On f c.q) :
    (de.map (Deep unit)).Perm ((kids i a.q).map (key i r rev)) := by
  obtain ⟨xs,native,_,second⟩ := row
  have p : (de.map State.q).Perm (kids i a.q) :=
    (second.perm.map State.q).trans (List.Perm.of_eq native)
  have eqn : de.map (Deep unit) = (de.map State.q).map (key i r rev) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c hc
    exact (key_state ready c (on c hc)).symm
  exact eqn ▸ p.map _

/-- Every legal through-4a tie determines the entire unlabelled child
population and whether the tied occurrences emit, for either fixed seed. -/
theorem same_children_across {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    {j : Input} {g : Site j} {t : Reader j} (other : RingGroupedStereo.Ready g t)
    (rev mir : Bool) (a : Arm i) (b : Arm j) (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On g b)
    (tie : key i r rev a = key j t mir b) :
    (((kids i a).map (key i r rev)).Perm ((kids j b).map (key j t mir))) ∧
      ∀ s, (RingFullPathPairs.likeAt i r rev s a).isSome =
        (RingFullPathPairs.likeAt j t mir s b).isSome := by
  obtain ⟨x,rfl⟩ := RingOccurrenceStereo.state_at ready rev va oa
  obtain ⟨y,rfl⟩ := RingOccurrenceStereo.state_at other mir vb ob
  have same := (key_state ready x oa).symm.trans (tie.trans (key_state other y ob))
  obtain ⟨sx,dx,rx,_,cx⟩ := RingOccurrenceStereo.next_row ready unit (fun t => t.source.unit) x oa
  obtain ⟨sy,dy,ry,_,cy⟩ := RingOccurrenceStereo.next_row other unit (fun t => t.source.unit) y ob
  have px := row_perm ready rx (fun c hc => (cx c hc).1)
  have py := row_perm other ry (fun c hc => (cy c hc).1)
  obtain ⟨xs,nx,lx,dx'⟩ := rx
  obtain ⟨ys,ny,ly,dy'⟩ := ry
  have reads {i : Input} {r : Reader i} {rev : Bool} {z : State i r rev} {zs : List (State i r rev)}
      (native : Native z zs) :
      List.Forall₂ (RingRetainedUnitPass.Reading i r rev) (kids i z.q) (zs.map unit) := by
    change zs.map State.q = kids i z.q at native
    rw [← native,List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
    intro t _
    exact t.source.unit
  have aligned := RingPathRankTransport.sibling_keys x.source.unit y.source.unit same
    (reads nx) (reads ny)
  have leftPerm := dx'.perm.map (Deep unit)
  have rightPerm := (dy'.perm.map (Deep unit)).symm
  have aligned' : (xs.map (Deep unit)).Perm (ys.map (Deep unit)) := by
    simpa only [Deep,List.map_map,Function.comp_def] using aligned
  have childPerm : (dx.map (Deep unit)).Perm (dy.map (Deep unit)) :=
    leftPerm.trans (aligned'.trans rightPerm)
  exact ⟨px.symm.trans (childPerm.trans py),fun s =>
    (emits_of_reading x.source.unit s).trans ((congrArg emits same).trans (emits_of_reading y.source.unit s).symm)⟩

theorem same_children {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (a b : Arm i) (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (tie : key i r rev a = key i r rev b) :
    (((kids i a).map (key i r rev)).Perm ((kids i b).map (key i r rev))) ∧
      ∀ s, (RingFullPathPairs.likeAt i r rev s a).isSome =
        (RingFullPathPairs.likeAt i r rev s b).isSome :=
  same_children_across ready ready rev rev a b va vb oa ob tie

/-- All finite walks in this carrier stay on the chosen original root. -/
abbrev Carrier {i : Input} (f : Site i) := RingRule5Shape.Carrier f

def children {i : Input} {f : Site i} (q : Carrier f) : List (Carrier f) :=
  (kids i q.val).attach.map fun c => ⟨c.val,
    i.certified.localizedRerootChild_valid _ _ _ (i.certified.executableLocalizedRerootChildren_declarative _) c.property,
    (i.certified.localizedRerootChildren_root_eq _ _ _ (i.certified.executableLocalizedRerootChildren_declarative _)
      c.property).trans q.property.2⟩

theorem children_val {i : Input} {f : Site i} (q : Carrier f) :
    (children q).map Subtype.val = kids i q.val := by simp [children,List.map_map,Function.comp_def]

def kind {i : Input} {f : Site i} (r : Reader i) (rev : Bool) (q : Carrier f) :=
  key i r rev q.val

/-- A decoder can determine the next sphere from the parent's key alone.
The representative used to define this function has no effect on its value. -/
noncomputable def offspring {i : Input} (f : Site i) (r : Reader i) (rev : Bool) (d : List Word) :
    List (List Word) := open Classical in
  if h : ∃ q : Carrier f, kind r rev q = d then
    order id ((children h.choose).map (kind r rev))
  else []

theorem offspring_exact {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (q : Carrier f) :
    (offspring f r rev (kind r rev q)).Perm ((children q).map (kind r rev)) := by
  have h : ∃ p : Carrier f, kind r rev p = kind r rev q := ⟨q,rfl⟩
  unfold offspring
  rw [dif_pos h]
  have shape := (same_children ready rev h.choose.val q.val h.choose.property.1 q.property.1
    h.choose.property.2 q.property.2 h.choose_spec).1
  have childRow (p : Carrier f) : (children p).map (kind r rev) = (kids i p.val).map (key i r rev) := by
    rw [← children_val p,List.map_map]
    rfl
  exact (legal_order id _).perm.trans (by simpa only [childRow] using shape)

theorem emits_exact {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (q : Carrier f) (s : RS) :
    (RingFullPathPairs.likeAt i r rev s q.val).isSome = emits (kind r rev q) := by
  obtain ⟨state,hs⟩ := RingOccurrenceStereo.state_at ready rev q.property.1 q.property.2
  have on : On f state.q := hs ▸ q.property.2
  simpa only [kind,← hs,key_state ready state on] using emits_of_reading state.source.unit s

open RingRetainedReferenceGroup (Path)
open RingFullPathPairs (stepKey stripBit)

/-- Forget only the final like/unlike marker. The previously decoded prefix
is the position of the parent in the preceding sphere. -/
abbrev eraseEndpoint := RingRule5Shape.eraseEndpoint
abbrev erase_snoc := RingRule5Shape.erase_snoc
abbrev erase_monotone := @RingRule5Shape.erase_monotone

/-- Expansion of an actual visit gives exactly the branch slots predicted
by the through-4a key, before the next set of emitted bits is consumed. -/
theorem expansion_slots {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (s : RS) (parent : RingFullPathPairs.FullVisit i)
    (valid : Valid parent.cursor) (on : On f parent.cursor) (out : List (RingFullPathPairs.FullVisit i))
    (expansion : (RingFullPathPairs.stage i r rev []).Expansion
      (RingFullPathPairs.likeAt i r rev s) parent out) :
    (out.map (fun v => eraseEndpoint v.path)).Perm
      ((offspring f r rev (key i r rev parent.cursor)).map (fun k => parent.path ++ [k])) := by
  let q : Carrier f := ⟨parent.cursor,valid,on⟩
  let raw := kids i parent.cursor
  have each (c : Arm i) (hc : c ∈ raw) :
      ∀ v, (RingFullPathPairs.stage i r rev []).Child
        (RingFullPathPairs.likeAt i r rev s) parent c v →
        eraseEndpoint v.path = parent.path ++ [key i r rev c] := by
    have frame := i.certified.executableLocalizedRerootChildren_declarative parent.cursor
    have vc := i.certified.localizedRerootChild_valid _ _ _ frame hc
    have oc := (i.certified.localizedRerootChildren_root_eq _ _ _ frame hc).trans on
    obtain ⟨b,hb⟩ := RingOccurrenceStereo.rank_total ready rev [] c vc oc
    change priority i r rev [] c = some b at hb
    rintro v ⟨k,read,rfl⟩
    obtain rfl := RingRetainedStereoRefinement.unique [] c k b read
      (RingRetainedStereoRefinement.source _ _ hb)
    simp [erase_snoc,key,hb]
  have mapped : out.map (fun v => eraseEndpoint v.path) =
      raw.map (fun c => parent.path ++ [key i r rev c]) := by
    change List.Forall₂ _ raw out at expansion
    generalize raw = cs at each expansion ⊢
    induction expansion with
    | nil => rfl
    | cons h _ ih =>
      simp only [List.map_cons]
      exact congrArg₂ List.cons (each _ List.mem_cons_self _ h) (ih (fun c hc => each c (.tail _ hc)))
  have p := (offspring_exact ready rev q).symm.map (fun k => parent.path ++ [k])
  rw [mapped]
  simpa only [← children_val q,List.map_map,kind,Function.comp_def,raw,q] using p

end TetraStereo.Engine.RingUnitTypeTransitions
assert_kernel_only TetraStereo.Engine.RingUnitTypeTransitions.emits_tied_readings
assert_kernel_only TetraStereo.Engine.RingUnitTypeTransitions.key_length
assert_kernel_only TetraStereo.Engine.RingUnitTypeTransitions.same_children_across
assert_kernel_only TetraStereo.Engine.RingUnitTypeTransitions.same_children
assert_kernel_only TetraStereo.Engine.RingUnitTypeTransitions.offspring_exact
assert_kernel_only TetraStereo.Engine.RingUnitTypeTransitions.emits_exact
assert_kernel_only TetraStereo.Engine.RingUnitTypeTransitions.expansion_slots
