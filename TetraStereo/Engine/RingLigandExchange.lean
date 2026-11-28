import TetraStereo.Engine.RingFullPathKeyTransport
import TetraStereo.Engine.RingBranchMatching
import TetraStereo.Engine.RingChemicalGraphProof

/-! Refusal from exchangeable retained ligand trees at a tetrahedral occurrence.
Matched trees may branch to arbitrary depth. Sibling order and atom IDs may differ. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingLigandExchange
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActivePairReport (Slot)
open RingNestedActivePair (Frame Reader)
open RingGroupedCentre (cursor)
open RingGeometryExchange (Carrier Frozen Marked)
open RingFullPathTrialReadings (MarkWords Outcome trialKey trials)

/-- The carrier matches the observed subtrees, including frozen stereo reads.
Every nomination outside its two endpoints preserves the elementary marked-atom
bits throughout this match. This permits repeated occurrences of the same atom. -/
structure Exchange {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (u v : Slot) where
  different : u ≠ v
  carrier : Carrier i i
  start : carrier.domain (cursor fr u)
  target : carrier.image (cursor fr u) = cursor fr v
  frozen : Frozen carrier r r
  other : ∀ s : Slot, s ≠ u → s ≠ v →
    Marked carrier (RingGroupedTrials.atom fr s) (RingGroupedTrials.atom fr s)

/-- Deleting any one nominated slot leaves an exchangeable pair. This covers
both three equivalent arms and two independent pairs. -/
def Covered {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) : Prop :=
  ∀ s : Slot, ∃ u v : Slot, s ≠ u ∧ s ≠ v ∧ Nonempty (Exchange fr r u v)

/-- Pairwise exchanges of three arms suffice even if the fourth arm differs. -/
theorem covered_of_three {i : Input} {f : Site i} {fr : Frame i f} {r : Reader i}
    {a b c : Slot} (ab : Exchange fr r a b) (bc : Exchange fr r b c)
    (ac : Exchange fr r a c) : Covered fr r := by
  intro s
  by_cases ha : s = a
  · subst s
    exact ⟨b,c,ab.different,ac.different,⟨bc⟩⟩
  by_cases hb : s = b
  · subst s
    exact ⟨a,c,ha,bc.different,⟨ac⟩⟩
  exact ⟨a,b,ha,hb,⟨ab⟩⟩

/-- Two disjoint pairs suffice even if the pairs have different constitutions. -/
theorem covered_of_pairs {i : Input} {f : Site i} {fr : Frame i f} {r : Reader i}
    {a b c d : Slot} (ab : Exchange fr r a b) (cd : Exchange fr r c d)
    (ac : a ≠ c) (ad : a ≠ d) (bc : b ≠ c) (bd : b ≠ d) : Covered fr r := by
  intro s
  by_cases ha : s = a
  · subst s
    exact ⟨c,d,ac,ad,⟨cd⟩⟩
  by_cases hb : s = b
  · subst s
    exact ⟨c,d,bc,bd,⟨cd⟩⟩
  exact ⟨a,b,ha,hb,⟨ab⟩⟩

/-- In separated arms an external nominee is absent from both subtrees.
The elementary mark transport then follows for every occurrence, including
ring duplicates. No ranks or marked comparison outputs are needed. -/
def separated {i : Input} {f : Site i} {fr : Frame i f} {r : Reader i}
    {u v : Slot} (hne : u ≠ v) (c : Carrier i i) (start : c.domain (cursor fr u))
    (target : c.image (cursor fr u) = cursor fr v) (frozen : Frozen c r r)
    (outside : ∀ s : Slot, s ≠ u → s ≠ v → ∀ q, c.domain q →
      (q.occurrence.val.node.current?.map Fin.val ≠ some (RingGroupedTrials.atom fr s)) ∧
      ((c.image q).occurrence.val.node.current?.map Fin.val ≠ some (RingGroupedTrials.atom fr s))) :
    Exchange fr r u v where
  different := hne
  carrier := c
  start := start
  target := target
  frozen := frozen
  other := by
    intro s hu hv q hq
    obtain ⟨l,r⟩ := outside s hu hv q hq
    simp [RingGroupedMark.bit,beq_eq_false_iff_ne.mpr l,beq_eq_false_iff_ne.mpr r]

/-- A record-preserving molecular graph automorphism supplies all subtree
correspondences. Fixed external nominees preserve every occurrence of their
mark, even when a ring gives access to that nominee from both arms. -/
noncomputable def ofAutomorphism {i : Input} {f : Site i} {fr : Frame i f}
    {u v : Slot} (hne : u ≠ v) (e : i.certified.moleculeGraph.Aut)
    (records : RingGeometryAutomorphism.Records e)
    (focus : RingGeometryAutomorphism.site e f = f)
    (target : i.certified.transportCursor i.single e (cursor fr u) = cursor fr v)
    (fixed : ∀ s : Slot, s ≠ u → s ≠ v → ∃ a : i.certified.Atom,
      a.val = RingGroupedTrials.atom fr s ∧ e.val a = a)
    (prior : ∀ q, RingActiveDistanceSchedule.Visible f q →
      RingChemicalGraphProof.state i q = RingChemicalGraphProof.state i (RingGeometryAutomorphism.site e q)) :
    Exchange fr (RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f) u v where
  different := hne
  carrier := RingGeometryAutomorphism.carrier e records
  start := by
    intro prev hp
    obtain rfl := Option.some.inj hp
    exact (fr.direction u).property.1.symm
  target := target
  frozen := by
    intro q _
    simpa only [focus] using RingGeometryAutomorphism.frozen_transport e f q.occurrence prior
  other := by
    intro s hu hv
    obtain ⟨a,id,unchanged⟩ := fixed s hu hv
    have bit := RingGeometryAutomorphism.mark e records a
    change Marked _ a.val (e.val a).val at bit
    rwa [unchanged,id] at bit

/-- A primitive exchange can be chosen independently for each nomination.
These are the very same certificates used by the grouped evaluator. -/
def PerNomination {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) :=
  ∀ s : Slot, ∃ u v : Slot, u ≠ v ∧ Nonempty (RingGeometryExchange.Exchange fr r s u v)

theorem perNomination_of_covered {i : Input} {f : Site i} {fr : Frame i f} {r : Reader i}
    (covered : Covered fr r) : PerNomination fr r := by
  intro s
  obtain ⟨u,v,hu,hv,⟨e⟩⟩ := covered s
  exact ⟨u,v,e.different,⟨⟨e.carrier,e.start,e.target,e.frozen,e.other s hu hv⟩⟩⟩

private theorem residual {i : Input} {f : Site i} {fr : Frame i f} {r : Reader i}
    (covered : PerNomination fr r) (m : Option Slot) (ks : Slot → RingFullPathEligibility.Key)
    (actual : ∀ s, RingFullPathEligibility.Reads i r false (cursor fr s) (ks s))
    (ws : Slot → RingRetainedChemicalTrace.Word) (words : MarkWords fr r false m ws) :
    Outcome fr false (fun s => trialKey (ks s) (ws s)) none := by
  obtain ⟨u,v,ne,⟨e⟩⟩ := covered (m.getD 0)
  have keys := RingFullPathKeyTransport.reads_transport e.carrier e.frozen false e.atLigand
    (actual u) (e.other.symm ▸ actual v)
  have same : ws u = ws v := by
    cases m with
    | none => exact (words u).trans (words v).symm
    | some s =>
      obtain ⟨a,ha,wa⟩ := words u
      obtain ⟨b,hb,wb⟩ := words v
      have eqn := e.carrier.mark e.frozen e.selected e.atLigand ha (e.other.symm ▸ hb)
      exact wa.trans ((congrArg RingStereoSiblingPass.Branch.word eqn).trans wb.symm)
  exact .tie ne (by rw [keys,same])

/-- The molecular publisher returns completed absence, including every Rule 6
nomination, on any ready reader satisfying the subtree observations. -/
theorem publish_refusal {i : Input} {f : Site i} (fr : Frame i f) {r : Reader i}
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (tetra : RingPyramidalPublication.focusP i f = none)
    (ready : RingGroupedStereo.Ready f r) (covered : PerNomination fr r) :
    RingPyramidalPublication.publish i f r = some none := by
  have all (rev : Bool) : ∃ ks : Slot → RingFullPathEligibility.Key,
      ∀ s, RingFullPathEligibility.Reads i r rev (cursor fr s) (ks s) := by
    have each (s : Slot) := RingFullPathEligibility.key_exact ready rev (cursor fr s)
      (RingGroupedCentre.valid fr s) (fr.direction s).property.1
    choose ks _ unique using each
    exact ⟨ks,fun s => (unique s _).mpr rfl⟩
  obtain ⟨ks,hk⟩ := all false
  obtain ⟨ms,hm⟩ := all true
  let hands := (trials ks).map (fun _ => (none : Option RS))
  have complete : List.Forall₂ (fun m h => ∃ ws, MarkWords fr r false m ws ∧
      Outcome fr false (fun s => trialKey (ks s) (ws s)) h) (trials ks) hands := by
    apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro m _
    obtain ⟨ws,_,eqn⟩ := RingFullPathTrialReadings.mark_exact fr ready false m
    have words := (eqn ws).mpr rfl
    exact ⟨ws,words,residual covered m ks hk ws words⟩
  have source := RingFullPathPublication.Source.centre fr ks ms hk hm hands complete
  have no : RingFullPathPublication.letters ks ms hands = none := by
    simp [hands,RingFullPathPublication.letters,LocalizedChemicalRingPromotionAggregation.readingBalance,
      LocalizedChemicalRingPromotionAggregation.readingScore,
      RingChemicalPriority.ReferenceFrame.survivingHand]
  rw [no] at source
  obtain ⟨v,hv,exactness⟩ := RingFullPathPublication.source_exact geom ready
  rw [RingPyramidalPublication.publish,tetra,RingFullPathConstitution.fast_local geom ready,hv,
    ← (exactness none).mp source]

theorem state_refusal {i : Input} {f : Site i} (fr : Frame i f)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (tetra : RingPyramidalPublication.focusP i f = none)
    (covered : Covered fr (RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f)) :
    RingChemicalGraphProof.state i f = some none :=
  (RingChemicalGraphProof.state_eq i f).trans
    (publish_refusal fr geom tetra (RingChemicalGraphProof.ready geom f) (perNomination_of_covered covered))

/-- Four proposed atom renamings are checked against the actual retained
occurrences on the supplied reader. The checker reads no final ranks or ballots. -/
def check {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (p : Slot → RingBranchMatching.Proposal) : Bool :=
  (List.finRange 4).all fun s => (p s).left != (p s).right &&
    (RingBranchMatching.find? fr r s (p s).left (p s).right (p s).rename).isSome

theorem check_sound {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (p : Slot → RingBranchMatching.Proposal) (ok : check fr r p = true) :
    PerNomination fr r := by
  intro s
  obtain ⟨ne,hit⟩ := Bool.and_eq_true_iff.mp (List.all_eq_true.mp ok s (List.mem_finRange s))
  exact ⟨_,_,bne_iff_ne.mp ne,⟨Option.get _ hit⟩⟩

theorem checked_state {i : Input} {f : Site i} (fr : Frame i f)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (tetra : RingPyramidalPublication.focusP i f = none) (p : Slot → RingBranchMatching.Proposal)
    (ok : check fr (RingActiveDistanceSchedule.frozen (RingChemicalGraphProof.state i) f) p = true) :
    RingChemicalGraphProof.state i f = some none :=
  (RingChemicalGraphProof.state_eq i f).trans
    (publish_refusal fr geom tetra (RingChemicalGraphProof.ready geom f) (check_sound _ _ p ok))

end TetraStereo.Engine.RingLigandExchange
assert_kernel_only TetraStereo.Engine.RingLigandExchange.publish_refusal
assert_kernel_only TetraStereo.Engine.RingLigandExchange.state_refusal
assert_kernel_only TetraStereo.Engine.RingLigandExchange.checked_state
