import TetraStereo.Engine.RingMarkedTypeRecovery

/-! Marking refines earlier ties without changing any complete row width. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMarkedLayout
open OneCenter CertifiedLocalizedCIPInput RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedStereoRefinement (Derives)
open RingRetainedChemicalTrace (Framed Word)
open RingRule5Shape (Valid On kids)
open private lower_earlier framed from TetraStereo.Engine.RingRetainedSeedFrames
open private key_state from TetraStereo.Engine.RingRule5Shape
open private mapped from TetraStereo.Engine.RingMarkedTypeRecovery

private theorem lower_key {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {q : Arm i} {p : Branch}
    (valid : Valid q) (on : On f q) (h : Derives i r false [.lowercase] q p) :
    p.deep = RingRule5Shape.key i r false q := by
  obtain ⟨k,hk⟩ := RingOccurrenceStereo.rank_total ready false [.lowercase] q valid on
  change RingRetainedStereoRefinement.priority i r false [.lowercase] q = some k at hk
  have eqn := RingRetainedStereoRefinement.unique _ _ _ _ h
    (RingRetainedStereoRefinement.source _ _ hk)
  simp [eqn,RingRule5Shape.key,hk]

private theorem lower_eq {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {a b : Arm i} {p t : Branch}
    (va : Valid a) (vb : Valid b) (oa : On f a) (ob : On f b)
    (ha : Derives i r false [.lowercase] a p) (hb : Derives i r false [.lowercase] b t)
    (tie : p.deep = t.deep) : p = t := by
  obtain ⟨sa,ea⟩ := RingOccurrenceStereo.state_at ready false va oa
  obtain ⟨sb,eb⟩ := RingOccurrenceStereo.state_at ready false vb ob
  have pa := RingRetainedStereoRefinement.unique _ _ _ _ ha (ea ▸ sa.source.lower)
  have pb := RingRetainedStereoRefinement.unique _ _ _ _ hb (eb ▸ sb.source.lower)
  exact pa.trans ((lower_earlier (a := sa) (b := sb)
    (by change sa.profile.lower.deep = sb.profile.lower.deep; rw [← pa,← pb]; exact tie)).2.trans pb.symm)

private noncomputable def decode {i : Input} (f : Site i) (r : Reader i) (d : List Word) : Branch :=
  open Classical in
  if h : ∃ (q : Arm i) (p : Branch), Valid q ∧ On f q ∧ Derives i r false [.lowercase] q p ∧ p.deep = d
  then h.choose_spec.choose else ⟨[],[],0,[]⟩

private theorem decode_exact {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {q : Arm i} {p : Branch}
    (valid : Valid q) (on : On f q) (h : Derives i r false [.lowercase] q p) :
    decode f r p.deep = p := by
  classical
  have ex : ∃ (q : Arm i) (b : Branch), Valid q ∧ On f q ∧ Derives i r false [.lowercase] q b ∧ b.deep = p.deep :=
    ⟨q,p,valid,on,h,rfl⟩
  unfold decode
  rw [dif_pos ex]
  obtain ⟨v,o,src,key⟩ := ex.choose_spec.choose_spec
  exact lower_eq ready v valid o on src h key

private noncomputable abbrev previous {i : Input} (f : Site i) (r : Reader i) (b : Branch) := decode f r b.priorDeep

private theorem previous_info {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {q : Arm i} {atom : Nat} {b : Branch}
    (valid : Valid q) (on : On f q) (h : RingGroupedMark.Reading i r atom q b) :
    (previous f r b).shallow = b.priorHead ∧ (previous f r b).deep = b.priorDeep ∧
      b.priorHead.length = 5 ∧ b.priorDeep.length = 5 ∧
      Framed 2 (previous f r b).levels := by
  cases h with
  | node prior look all sub first second =>
    have eqn := decode_exact ready valid on prior
    have size := RingRetainedSeedFrames.sizes [.lowercase] _ _ prior
    simp only [RingRetainedStereoRefinement.extend,previous,eqn]
    exact ⟨True.intro,True.intro,size.1,size.2,framed _ prior⟩

private def widths (ls : Layers) := ls.map (List.map List.length)

private theorem widths_interleave (a b : Layers) :
    widths (RingChildKeyRecovery.interleave a b) =
      RingChildKeyRecovery.interleave (widths a) (widths b) := by
  induction a generalizing b with
  | nil => rfl
  | cons a as ih => cases b with
    | nil => rfl
    | cons b bs =>
      simpa only [widths,RingChildKeyRecovery.interleave,List.map_cons,List.map_append] using
        congrArg (List.cons (a.map List.length ++ b.map List.length)) (ih bs)

private theorem widths_forest (f : Branch → Branch) (ds : List Branch)
    (each : ∀ b ∈ ds, widths b.levels = widths (f b).levels) :
    widths ((ds.map Branch.levels).foldr RingChildKeyRecovery.interleave []) =
      widths (((ds.map f).map Branch.levels).foldr RingChildKeyRecovery.interleave []) := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons,List.foldr_cons,widths_interleave]
    rw [each d List.mem_cons_self,ih (fun b hb => each b (.tail _ hb))]

private theorem widths_rows (f : Branch → Branch) (sh de : List Branch)
    (each : ∀ b ∈ de, widths b.levels = widths (f b).levels) :
    widths (rows sh de) = widths (rows (sh.map f) (de.map f)) := by
  exact congrArg₂ List.cons (by simp [List.length_map]) (widths_forest f de each)

/-- Marking preserves every sphere boundary and every shallow/deep row width. -/
theorem layer_widths {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {q : Arm i} {atom : Nat} {m p : Branch}
    (valid : Valid q) (on : On f q) (mark : RingGroupedMark.Reading i r atom q m)
    (prior : Derives i r false [.lowercase] q p) :
    m.levels.map (List.map List.length) = p.levels.map (List.map List.length) := by
  induction mark generalizing p with
  | @node q p0 cs sh de before look all sub first second ih =>
    obtain rfl := RingRetainedStereoRefinement.unique _ _ _ _ before prior
    have frame := i.certified.executableLocalizedRerootChildren_declarative q
    have vc (c : Arm i) (hc : c ∈ kids i q) : Valid c :=
      i.certified.localizedRerootChild_valid _ _ _ frame hc
    have oc (c : Arm i) (hc : c ∈ kids i q) : On f c :=
      (i.certified.localizedRerootChildren_root_eq _ _ _ frame hc).trans on
    let prev := previous f r
    have source (b : Branch) (hb : b ∈ cs) :
        ∃ c ∈ kids i q, look c = some b := RingRetainedUnitPass.forOutput all hb
    have info (b : Branch) (hb : b ∈ cs) :
        (prev b).shallow = b.priorHead ∧ (prev b).deep = b.priorDeep ∧
        b.priorHead.length = 5 ∧ b.priorDeep.length = 5 ∧ Framed 2 (prev b).levels := by
      obtain ⟨c,hc,hit⟩ := source b hb
      exact previous_info ready (vc c hc) (oc c hc) (sub c hc hit)
    obtain ⟨s,d,⟨row⟩⟩ := RingRetainedStereoRefinement.decomposition before
    have childprev (c : Arm i) (hc : c ∈ kids i q) (b : Branch) (hit : look c = some b) :
        prev b = decode f r (RingRule5Shape.key i r false c) := by
      cases sub c hc hit with
      | node low _ _ _ _ _ =>
        exact congrArg (decode f r) (lower_key ready (vc c hc) (oc c hc) low)
    have ma := mapped all prev (fun c => decode f r (RingRule5Shape.key i r false c)) childprev
    have mb := mapped row.complete id (fun c => decode f r (RingRule5Shape.key i r false c)) (by
      intro c hc b hit
      have src := row.derived c hc hit
      have decoded := decode_exact ready (vc c hc) (oc c hc) src
      simpa only [id,← lower_key ready (vc c hc) (oc c hc) src] using decoded.symm)
    have native : cs.map prev = row.native := ma.trans (by simpa only [List.map_id] using mb.symm)
    have legal {κ : Type} [LinearOrder κ] (old new : Branch → List κ)
        (agree : ∀ b ∈ cs, (new b).take 5 = old b) {out : List Branch}
        (h : Legal new cs out) : Legal (fun b => old b) cs out := by
      refine ⟨h.perm,List.pairwise_map.mpr ?_⟩
      apply (List.pairwise_map.mp h.descending).imp_of_mem
      intro a b ha hb less
      simpa only [agree a (h.perm.mem_iff.mp ha),agree b (h.perm.mem_iff.mp hb)] using
        RingChildKeyRecovery.take_le less 5
    have la := legal (fun b => (prev b).shallow) Branch.shallow (by
      intro b hb
      have h := info b hb
      simpa only [Branch.shallow,← h.2.2.1,List.take_left] using h.1.symm) first
    have ld := legal (fun b => (prev b).deep) Branch.deep (by
      intro b hb
      have h := info b hb
      simpa only [Branch.deep,← h.2.2.2.1,List.take_left] using h.2.1.symm) second
    have mla : Legal Branch.shallow row.native (sh.map prev) := by
      rw [← native]
      exact ⟨la.perm.map prev,by simpa only [List.map_map] using la.descending⟩
    have mld : Legal Branch.deep row.native (de.map prev) := by
      rw [← native]
      exact ⟨ld.perm.map prev,by simpa only [List.map_map] using ld.descending⟩
    have lowlayout := row.layout.trans (rows_unique row.shallow row.deep mla mld (by
      intro b hb
      obtain ⟨c,hc,hit⟩ := RingRetainedUnitPass.forOutput row.complete hb
      exact framed _ (row.derived c hc hit)))
    change widths (rows sh de) = widths p0.levels
    rw [lowlayout]
    apply widths_rows prev sh de
    intro b hb
    have hcs := second.perm.mem_iff.mp hb
    obtain ⟨c,hc,hit⟩ := source b hcs
    cases reading : sub c hc hit with
    | node low look' all' sub' first' second' =>
      have decoded := decode_exact ready (vc c hc) (oc c hc) low
      simpa only [prev,previous,RingRetainedStereoRefinement.extend,decoded] using
        ih c hc hit (vc c hc) (oc c hc) low

/-- The entire marked word has exactly the through-4c row-length layout,
independently of the promoted atom and including duplicate occurrences. -/
theorem word_lengths {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {q : Arm i} {atom : Nat} {m p : Branch}
    (valid : Valid q) (on : On f q) (mark : RingGroupedMark.Reading i r atom q m)
    (prior : Derives i r false [.lowercase] q p) :
    m.word.map List.length = p.word.map List.length := by
  have layers := layer_widths ready valid on mark prior
  simpa only [Branch.word,List.map_cons,List.length_singleton,List.map_flatten] using
    congrArg (fun ls => 1 :: ls.flatten) layers
/-- The same complete layer layout holds on either geometry. -/
theorem geometry_layer_widths {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {rev : Bool} {q : Arm i} {atom : Nat} {m p : Branch}
    (valid : Valid q) (on : On f q) (mark : RingGroupedMark.OnGeometry i r rev atom q m)
    (prior : Derives i r rev [.lowercase] q p) :
    m.levels.map (List.map List.length) = p.levels.map (List.map List.length) := by
  cases rev with
  | false => exact layer_widths ready valid on mark prior
  | true =>
    exact layer_widths ready valid on mark.reflect
      (RingRetainedStereoRefinement.mirror [.lowercase] _ _ prior)

/-- The complete word layout is likewise independent of geometry and atom. -/
theorem geometry_word_lengths {i : Input} {f : Site i} {r : Reader i}
    (ready : RingGroupedStereo.Ready f r) {rev : Bool} {q : Arm i} {atom : Nat} {m p : Branch}
    (valid : Valid q) (on : On f q) (mark : RingGroupedMark.OnGeometry i r rev atom q m)
    (prior : Derives i r rev [.lowercase] q p) :
    m.word.map List.length = p.word.map List.length := by
  have layers := geometry_layer_widths ready valid on mark prior
  simpa only [Branch.word,List.map_cons,List.length_singleton,List.map_flatten] using
    congrArg (fun ls => 1 :: ls.flatten) layers
end TetraStereo.Engine.RingMarkedLayout
assert_kernel_only TetraStereo.Engine.RingMarkedLayout.layer_widths
assert_kernel_only TetraStereo.Engine.RingMarkedLayout.word_lengths
assert_kernel_only TetraStereo.Engine.RingMarkedLayout.geometry_layer_widths
assert_kernel_only TetraStereo.Engine.RingMarkedLayout.geometry_word_lengths
