import TetraStereo.Engine.RingOriginTripleArms
import TetraStereo.Engine.RingOriginMetricReport

/-! Three identical terminal graph neighbors leave an unmarked pair in every trial. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginTripleFrame
open OneCenter
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingNestedActivePair (Frame Reader)
open RingHydrogenSpelling (TwinPair twinCandidate)
open RingGroupedCentre (cursor)
open RingOriginTetrahedralTrials (wordsWith)
open RingOriginMetricReport (marks)

/-- Only raw records, terminal bond rows, and exclusion of the original root are tested. -/
def Candidate {i : Input} {f : Site i} (fr : Frame i f)
    (u v w : i.certified.Atom) : Prop :=
  twinCandidate i fr.center u v ∧ twinCandidate i fr.center u w ∧
    twinCandidate i fr.center v w ∧ f.val.root ≠ u ∧ f.val.root ≠ v ∧ f.val.root ≠ w

instance {i : Input} {f : Site i} (fr : Frame i f) (u v w : i.certified.Atom) :
    Decidable (Candidate fr u v w) := by unfold Candidate; infer_instance

structure Triple {i : Input} {f : Site i} (fr : Frame i f) where
  u : i.certified.Atom
  v : i.certified.Atom
  w : i.certified.Atom
  facts : Candidate fr u v w

/-- Search the four physical graph neighbors, without evaluating priorities or ballots. -/
def find? {i : Input} {f : Site i} (fr : Frame i f) : Option (Triple fr) :=
  let ns := (List.finRange 4).map (i.certified.canonicalLigandAtom fr.center)
  ns.findSome? fun u => ns.findSome? fun v => ns.findSome? fun w =>
    if h : Candidate fr u v w then some ⟨u,v,w,h⟩ else none

def check {i : Input} {f : Site i} (fr : Frame i f) : Bool := (find? fr).isSome

theorem check_sound {i : Input} {f : Site i} (fr : Frame i f) (h : check fr = true) :
    Nonempty (Triple fr) := ⟨(find? fr).get h⟩

private def pairOf {i : Input} (c : i.certified.TetrahedralCenter)
    (u v : i.certified.Atom) (h : twinCandidate i c u v) : TwinPair i :=
  ⟨c,u,v,h.1,h.2.1,h.2.2.1,h.2.2.2⟩

namespace Triple
variable {i : Input} {f : Site i} {fr : Frame i f}

def basePair (t : Triple fr) : TwinPair i := pairOf fr.center t.u t.v t.facts.1

theorem base_facts (t : Triple fr) : (t.basePair).c = fr.center ∧
    f.val.root ≠ t.basePair.u ∧ f.val.root ≠ t.basePair.v :=
  ⟨rfl,t.facts.2.2.2.1,t.facts.2.2.2.2.1⟩

/-- Select two of the three atoms after excluding the actual nominated atom ID. -/
def pair (t : Triple fr) (mark : Nat) : TwinPair i :=
  if mark = t.u.val then pairOf fr.center t.v t.w t.facts.2.2.1
  else if mark = t.v.val then pairOf fr.center t.u t.w t.facts.2.1
  else t.basePair

theorem pair_facts (t : Triple fr) (mark : Nat) :
    (t.pair mark).c = fr.center ∧ f.val.root ≠ (t.pair mark).u ∧
    f.val.root ≠ (t.pair mark).v ∧ mark ≠ (t.pair mark).u.val ∧ mark ≠ (t.pair mark).v.val := by
  have uv : t.u.val ≠ t.v.val := fun h => t.facts.1.1 (Fin.ext h)
  have uw : t.u.val ≠ t.w.val := fun h => t.facts.2.1.1 (Fin.ext h)
  have vw : t.v.val ≠ t.w.val := fun h => t.facts.2.2.1.1 (Fin.ext h)
  have ou := t.facts.2.2.2.1
  have ov := t.facts.2.2.2.2.1
  have ow := t.facts.2.2.2.2.2
  unfold pair
  split
  · rename_i hit
    exact ⟨rfl,ov,ow,by simpa only [hit] using uv,by simpa only [hit] using uw⟩
  · rename_i away
    split
    · rename_i hit
      exact ⟨rfl,ou,ow,by simpa only [hit] using Ne.symm uv,by simpa only [hit] using vw⟩
    · rename_i awayV
      exact ⟨rfl,ou,ov,away,awayV⟩

theorem selected_slots (t : Triple fr) (r : Reader i) (ready : RingGroupedStereo.Ready f r)
    (mark : Nat) : ∃ u v : Fin 4, u ≠ v ∧
      RingOriginFullKeys.active i f r false (cursor fr u) =
        RingOriginFullKeys.active i f r false (cursor fr v) ∧
      RingOriginMarkWords.word? i f r mark (cursor fr u) =
        RingOriginMarkWords.word? i f r mark (cursor fr v) := by
  let p := t.pair mark
  obtain ⟨center,ou,ov,mu,mv⟩ := t.pair_facts mark
  have au : i.certified.moleculeGraph.Adj fr.center.val p.u := by
    rw [← center]
    exact i.certified.moleculeGraph.adj_symm.mpr ((p.supportU p.c.val).mpr rfl)
  have av : i.certified.moleculeGraph.Adj fr.center.val p.v := by
    rw [← center]
    exact i.certified.moleculeGraph.adj_symm.mpr ((p.supportV p.c.val).mpr rfl)
  obtain ⟨u,hu⟩ := RingOriginTwinFrame.slot_exists fr p.u au
  obtain ⟨v,hv⟩ := RingOriginTwinFrame.slot_exists fr p.v av
  refine ⟨u,v,?_,(RingOriginTwinFrame.twin_keys p fr center.symm ou ov r ready false u v hu hv).2,
    RingOriginTripleArms.twin_mark_eq p fr center.symm ou ov r ready u v hu hv mark mu mv⟩
  intro eqn
  subst v
  exact p.distinct (Option.some.inj (hu.symm.trans hv))

/-- Every optional nomination leaves two distinct equal full-key and marked-word slots. -/
theorem ties (t : Triple fr) (r : Reader i) (ready : RingGroupedStereo.Ready f r) :
    ∀ m : Option (Fin 4), ∃ u v : Fin 4, u ≠ v ∧
      RingOriginFullKeys.active i f r false (cursor fr u) =
        RingOriginFullKeys.active i f r false (cursor fr v) ∧
      (wordsWith fr (marks i f r) m).map (fun ws => ws u) =
        (wordsWith fr (marks i f r) m).map (fun ws => ws v) := by
  intro m
  obtain ⟨u,v,ne,keys,words⟩ := t.selected_slots r ready ((m.map (RingGroupedTrials.atom fr)).getD 0)
  refine ⟨u,v,ne,keys,?_⟩
  cases m with
  | none => rfl
  | some s =>
    simp only [Option.map_some,Option.getD_some] at words
    cases hw : wordsWith fr (marks i f r) (some s) with
    | none => rfl
    | some ws =>
      change RingActivePairReport.four? (fun k =>
        marks i f r (some (RingGroupedTrials.atom fr s)) (cursor fr k)) = some ws at hw
      have hu := RingActivePairReport.four_at hw u
      have hv := RingActivePairReport.four_at hw v
      change RingOriginMarkWords.word? i f r (RingGroupedTrials.atom fr s) (cursor fr u) = some (ws u) at hu
      change RingOriginMarkWords.word? i f r (RingGroupedTrials.atom fr s) (cursor fr v) = some (ws v) at hv
      exact congrArg some (Option.some.inj (hu.symm.trans (words.trans hv)))

end Triple
end TetraStereo.Engine.RingOriginTripleFrame

assert_kernel_only TetraStereo.Engine.RingOriginTripleFrame.check_sound
assert_kernel_only TetraStereo.Engine.RingOriginTripleFrame.Triple.pair_facts
assert_kernel_only TetraStereo.Engine.RingOriginTripleFrame.Triple.ties
