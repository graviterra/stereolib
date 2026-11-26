import TetraStereo.Engine.RingFrameTransport
import TetraStereo.Engine.RingStereoKeyCoordinates

set_option autoImplicit false
namespace TetraStereo.Engine.RingSpatialTransport
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (View Rule frozen evaluate Visible distance height)
open RingGroupedReport (origin)
open RingPyramidalPublication (publish)

section
variable (i : Input) (g : SpatialConfiguration) (full : g.positions.length = size i)
local notation "J" => atGeometry i g full

/-- An actual fresh admission preserves the ordered occurrence address and its entire node. -/
def reindexSite : Site i ≃ Site J :=
  sameMoleculeOccurrenceEquiv (a := i.certified) (b := (J).certified) rfl _

local notation "E" => reindexSite i g full

theorem reindex_origin (a : i.certified.Atom) : E (origin i a) = origin J a :=
  RingGroupedReport.origin_unique _ rfl

theorem reindex_frozen (s : View J) (q u : Site i) :
    frozen s (E q) (E u) = frozen (fun v => s (E v)) q u := by
  unfold frozen
  rfl

/-- Pull an independently evaluated rule back along the actual molecular occurrence equivalence. -/
def pullRule (rule : Rule J) : Rule i := fun q r => rule (E q) (fun u => r ((E).symm u))

theorem evaluate_pull (rule : Rule J) :
    evaluate (pullRule i g full rule) = fun q => evaluate rule (E q) := by
  symm
  apply RingActiveDistanceSchedule.unique
  intro q
  rw [RingActiveDistanceSchedule.evaluate_eq rule (E q)]
  apply congrArg (rule (E q))
  funext u
  obtain ⟨v,rfl⟩ := (E).surjective u
  simpa only [Equiv.symm_apply_apply] using reindex_frozen i g full (evaluate rule) q v

/-- A local disagreement between two independently run rules with identical frozen
readings at every corresponding occurrence, witnessed on the original root's digraph. -/
def LocalDisagreement (left : Rule i) (right : Rule J) (q : Site i) : Prop :=
  (∀ u, frozen (evaluate left) q u = frozen (evaluate right) (E q) (E u)) ∧
    left q (frozen (evaluate left) q) ≠ right (E q) (frozen (evaluate right) (E q))

theorem deepest_disagreement (left : Rule i) (right : Rule J) (start : Site i)
    (ne : evaluate left start ≠ evaluate right (E start)) :
    ∃ q, (q = start ∨ Visible start q) ∧ LocalDisagreement i g full left right q := by
  classical
  suffices go : ∀ n (u : Site i), height i - distance u = n →
      evaluate left u ≠ evaluate right (E u) →
      ∃ q, (q = u ∨ Visible u q) ∧ LocalDisagreement i g full left right q from go _ start rfl ne
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u depth differs
    by_cases down : ∃ v, Visible u v ∧ evaluate left v ≠ evaluate right (E v)
    · obtain ⟨v,vis,vne⟩ := down
      have upper := RingActiveDistanceSchedule.distance_bound v
      have lower := vis.2.1
      obtain ⟨q,loc,fail⟩ := ih _ (by omega) v rfl vne
      exact ⟨q,Or.inr (loc.elim (fun eqn => eqn ▸ vis) (Visible.trans vis)),fail⟩
    · refine ⟨u,Or.inl rfl,?_,?_⟩
      · intro v
        rw [reindex_frozen]
        exact congrFun (RingFrameTransport.frozen_congr u (fun t h => by
          by_contra bad
          exact down ⟨t,h,bad⟩)) v
      · simpa only [← RingActiveDistanceSchedule.evaluate_eq] using differs

/-- A difference in native reports after independently admitting replacement coordinates
always has a local chemical witness on a requested root, with equal prior readings. -/
theorem native_report_disagreement (atoms : List i.certified.Atom)
    (ne : RingChemicalReport.report? i atoms ≠ RingChemicalReport.report? J atoms) :
    ∃ a ∈ atoms, ∃ q : Site i, (q = origin i a ∨ Visible (origin i a) q) ∧
      LocalDisagreement i g full (publish i) (publish J) q := by
  classical
  have witness : ∃ a ∈ atoms, RingChemicalGraphProof.root i a ≠ RingChemicalGraphProof.root J a := by
    by_contra! no
    apply ne
    apply RingFrameTransport.mapM_congr_mem
    intro a ha
    exact congrArg (Option.map fun v => (a.val,v)) (no a ha)
  obtain ⟨a,ha,unlike⟩ := witness
  refine ⟨a,ha,deepest_disagreement i g full _ _ (origin i a) ?_⟩
  rw [reindex_origin]
  simpa only [RingChemicalGraphProof.root,
    RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips _)] using unlike

end
end TetraStereo.Engine.RingSpatialTransport
assert_kernel_only TetraStereo.Engine.RingSpatialTransport.evaluate_pull
assert_kernel_only TetraStereo.Engine.RingSpatialTransport.native_report_disagreement

namespace TetraStereo.Engine.RingSpatialTransport
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Frame Reader)
open RingActivePairReport (Slot)
open RingFrameTransport
variable (i : Input) (g : SpatialConfiguration) (full : g.positions.length = size i)
local notation "J" => atGeometry i g full
local notation "E" => reindexSite i g full

abbrev reindexArm (a : Arm i) : Arm J :=
  sameMoleculeCursor (a := i.certified) (b := (J).certified) rfl a
local notation "A" => reindexArm i g full

theorem frame_list (q : Site i) :
    RingRetainedAuxiliary.frame (J).certified (E q) = (RingRetainedAuxiliary.frame i.certified q).map A :=
  (sameMolecule_retained_frame_map (a := i.certified) (b := (J).certified) rfl q).symm

theorem recognized_center (q : Site i) :
    (J).certified.localizedOccurrenceDescriptorCenter? (E q) = i.certified.localizedOccurrenceDescriptorCenter? q := by
  apply Option.ext
  intro c
  rw [(J).certified.localizedOccurrenceDescriptorCenter?_eq_some_iff,i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff]
  rfl

theorem focusP_reindex (q : Site i) :
    RingPyramidalPublication.focusP J (E q) = RingPyramidalPublication.focusP i q := rfl

theorem frame_atoms_eq {q : Site i} (x : Frame i q) (y : Frame J (E q)) (ks : List Slot) :
    y.atoms ks = x.atoms ks := by
  have hy := y.actualAtoms
  rw [frame_list,List.mapM_map] at hy
  have ids : y.ids = x.ids := Option.some.inj (hy.symm.trans x.actualAtoms)
  have getSame (a b : List Nat) (eqn : a = b) (n : Nat) (ha : n < a.length) (hb : n < b.length) :
      a[n] = b[n] := by subst b; rfl
  exact List.map_congr_left (fun k _ => getSame _ _ ids k _ _)

theorem frame_cursor_eq {q : Site i} (x : Frame i q) (y : Frame J (E q)) (k : Slot) :
    RingGroupedCentre.cursor y k = A (RingGroupedCentre.cursor x k) := by
  have arm : y.arm k = A (x.arm k) := by
    unfold Frame.arm
    simp only [List.get_eq_getElem]
    generalize_proofs h
    rw [getElem_congr_coll (frame_list i g full q)]
    simp
  change (⟨(y.arm k).occurrence,some (E q)⟩ : Arm J) = _
  rw [arm]
  rfl

private theorem mark_words_eq {k f} (fr : @Frame k f) (r : Reader k) (s : Slot) :
    RingFullPathTrialReadings.markWords? fr r (some s) =
      (RingActivePairReport.four? (fun t => RingGroupedMark.arm? k r (RingGroupedTrials.atom fr s)
        (RingGroupedCentre.cursor fr t))).map (fun es t => (es t).2.word) := by
  unfold RingFullPathTrialReadings.markWords? RingGroupedTrials.marking?
  cases e : RingActivePairReport.four? _ with
  | none => simp [e]
  | some es =>
    simp [Option.attach_eq_some _ ⟨es,e⟩]
    rfl

theorem tetra_reindex (G : Geometry) (q : Site i) (r : Reader i) (s : Reader J)
    (keys : ∀ rev t, RingFullPathEligibility.key? J s rev (A t) = RingFullPathEligibility.key? i r rev t)
    (marks : ∀ n t, RingGroupedMark.arm? J s n (A t) = RingGroupedMark.arm? i r n t) :
    tetraG J G (E q) s = tetraG i G q r := by
  cases h : i.certified.localizedOccurrenceDescriptorCenter? q with
  | none =>
    have off {u : Input} {z : Site u} (hh : u.certified.localizedOccurrenceDescriptorCenter? z = none) :
        RingNestedActivePair.frame? u z = none := by
      cases got : RingNestedActivePair.frame? u z with
      | none => rfl
      | some fr => exact nomatch hh.symm.trans fr.recognized
    simp [tetraG,off h,off ((recognized_center i g full q).trans h)]
  | some c =>
    obtain ⟨x,hx⟩ := RingGroupedGeometry.frame_exists h
    obtain ⟨y,hy⟩ := RingGroupedGeometry.frame_exists ((recognized_center i g full q).trans h)
    have cur := frame_cursor_eq i g full x y
    have pts := frame_atoms_eq i g full x y
    have keyeq (rev) : RingFullPathPublication.keys? y s rev = RingFullPathPublication.keys? x r rev := by
      unfold RingFullPathPublication.keys?
      simp only [cur,keys]
    have markeq (n) : RingFullPathTrialReadings.markWords? y s n = RingFullPathTrialReadings.markWords? x r n := by
      cases n with
      | none => rfl
      | some t => simp only [mark_words_eq,cur,RingGroupedTrials.atom,pts,marks]
    have handeq : readTrialG y G = readTrialG x G := by
      funext w
      simp only [readTrialG,pts]
    simp only [tetraG,hx,hy,centreG,keyeq,readingsG,cur,keys,
      readingsWithG,markeq,handeq]
end TetraStereo.Engine.RingSpatialTransport
assert_kernel_only TetraStereo.Engine.RingSpatialTransport.tetra_reindex

namespace TetraStereo.Engine.RingSpatialTransport
open OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingActiveDistanceSchedule (View)
open RingPyramidalPublication
open RingFrameTransport
open LocalizedGenericMarkedRecalculation
section
variable (i : Input) (g : SpatialConfiguration) (full : g.positions.length = size i)

def mapLigand (x : Ligand i) : Ligand (atGeometry i g full) := ⟨(sameMoleculeCursor (a := i.certified) (b := (atGeometry i g full).certified) rfl) x.arm,x.atom,x.priority⟩

variable (r : View i) (r' : View (atGeometry i g full))
variable (keys : ∀ (rev : Bool) (t : Arm i),
  RingFullPathEligibility.key? (atGeometry i g full) r' rev ((sameMoleculeCursor (a := i.certified) (b := (atGeometry i g full).certified) rfl) t) = RingFullPathEligibility.key? i r rev t)
variable (marks : ∀ (id : Nat) (t : Arm i),
  RingGroupedMark.arm? (atGeometry i g full) r' id ((sameMoleculeCursor (a := i.certified) (b := (atGeometry i g full).certified) rfl) t) = RingGroupedMark.arm? i r id t)

include keys in
theorem ligandOf_across (rev : Bool) (t : Arm i) :
    ligandOf (atGeometry i g full) r' rev ((sameMoleculeCursor (a := i.certified) (b := (atGeometry i g full).certified) rfl) t) = (ligandOf i r rev t).map (mapLigand i g full) := by
  unfold ligandOf
  rw [keys rev t]
  change t.occurrence.val.node.current?.bind _ = _
  cases t.occurrence.val.node.current? <;> cases RingFullPathEligibility.key? i r rev t <;> rfl

theorem mapM_option_map {α β γ : Type} (f : α → Option β) (h : β → γ) (xs : List α) :
    xs.mapM (fun x => (f x).map h) = (xs.mapM f).map (List.map h) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.mapM_cons,ih]
    cases f x <;> cases xs.mapM f <;> rfl

include keys in
theorem ligands_across (q : Site i) (rev : Bool) :
    ligands? (atGeometry i g full) ((reindexSite i g full) q) r' rev = (ligands? i q r rev).map (List.map (mapLigand i g full)) := by
  rw [ligands_unfold,ligands_unfold]
  have frames := sameMolecule_retained_frame_map (a := i.certified) (b := (atGeometry i g full).certified) rfl q
  change (RingRetainedAuxiliary.frame i.certified q).map (sameMoleculeCursor (a := i.certified) (b := (atGeometry i g full).certified) rfl) = RingRetainedAuxiliary.frame ((atGeometry i g full)).certified ((reindexSite i g full) q) at frames
  rw [← frames,List.mapM_map]
  simp only [Function.comp_def,ligandOf_across i g full r r' keys]
  exact mapM_option_map _ _ _

include marks in
theorem rowOf_across (mark : Option Nat) (x : Ligand i) :
    rowOf (atGeometry i g full) r' mark (mapLigand i g full x) = rowOf i r mark x := by
  unfold rowOf markWord?
  cases mark with
  | none => rfl
  | some id =>
    change ((RingGroupedMark.arm? (atGeometry i g full) r' id ((sameMoleculeCursor (a := i.certified) (b := (atGeometry i g full).certified) rfl) x.arm)).map _).bind _ = _
    rw [marks id x.arm]
    rfl

include marks in
theorem trialS_across (sense : List Nat → Option RS) (a : i.certified.Atom)
    (xs : List (Ligand i)) (mark : Option Nat) :
    trialS sense r' a (xs.map (mapLigand i g full)) mark = trialS sense r a xs mark := by
  unfold trialS
  rw [List.mapM_map]
  simp only [Function.comp_def,rowOf_across i g full r r' marks]

theorem marksOf_across (xs : List (Ligand i)) :
    marksOf (xs.map (mapLigand i g full)) = marksOf xs := by
  match xs with
  | [] | [_] | [_,_] | [_,_,_] | _ :: _ :: _ :: _ :: _ => rfl

include keys marks in
theorem handsS_across (sense : List Nat → Option RS) (q : Site i)
    (a : i.certified.Atom) (rev : Bool) :
    handsS sense (atGeometry i g full) ((reindexSite i g full) q) r' a rev = handsS sense i q r a rev := by
  unfold handsS
  rw [ligands_across i g full r r' keys]
  cases ligands? i q r rev with
  | none => rfl
  | some xs =>
    simp only [Option.map_some,Option.bind_some,marksOf_across]
    apply congrArg (fun f => (marksOf xs).mapM f)
    funext mark
    exact trialS_across i g full r r' marks sense a xs mark

include keys marks in
theorem pLabelsG_across (G : Geometry) (q : Site i) (a : i.certified.Atom) :
    pLabelsG (atGeometry i g full) G ((reindexSite i g full) q) r' a = pLabelsG i G q r a := by
  unfold pLabelsG
  have frames := sameMolecule_retained_frame_map (a := i.certified) (b := (atGeometry i g full).certified) rfl q
  have lengths := congrArg List.length frames
  change ((RingRetainedAuxiliary.frame i.certified q).map (sameMoleculeCursor (a := i.certified) (b := (atGeometry i g full).certified) rfl)).length = (RingRetainedAuxiliary.frame ((atGeometry i g full)).certified ((reindexSite i g full) q)).length at lengths
  rw [List.length_map] at lengths
  rw [← lengths,handsS_across i g full r r' keys marks,handsS_across i g full r r' keys marks]
end
end TetraStereo.Engine.RingSpatialTransport
assert_kernel_only TetraStereo.Engine.RingSpatialTransport.pLabelsG_across

namespace TetraStereo.Engine.RingSpatialTransport
open OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingFrameTransport
open RingActiveDistanceSchedule (View evaluate)
variable (i : Input) (g : SpatialConfiguration) (full : g.positions.length = size i)
local notation "J" => atGeometry i g full
local notation "E" => reindexSite i g full
local notation "A" => reindexArm i g full

theorem publish_reindex_of_priorities (G : Geometry) (q : Site i) (r : View i) (s : View J)
    (keys : ∀ rev t, RingFullPathEligibility.key? J s rev (A t) = RingFullPathEligibility.key? i r rev t)
    (marks : ∀ n t, RingGroupedMark.arm? J s n (A t) = RingGroupedMark.arm? i r n t) :
    publishG J G (E q) s = publishG i G q r := by
  unfold publishG
  rw [focusP_reindex]
  cases RingPyramidalPublication.focusP i q with
  | none => exact tetra_reindex i g full G q r s keys marks
  | some a => exact congrArg some (pLabelsG_across i g full r s keys marks G q a)

theorem stateG_reindex_of_rule (G : Geometry)
    (localEq : ∀ (q : Site i) (r : View i) (s : View J), (∀ u, s (E u) = r u) →
      publishG J G (E q) s = publishG i G q r) :
    ∀ q : Site i, stateG J G (E q) = stateG i G q := by
  have rules : pullRule i g full (publishG J G) = publishG i G := by
    funext q r
    apply localEq
    intro u
    simp only [Equiv.symm_apply_apply]
  have eqn := evaluate_pull i g full (publishG J G)
  rw [rules] at eqn
  exact fun q => (congrFun eqn q).symm

theorem reportG_reindex_of_state (G : Geometry)
    (eqn : ∀ q : Site i, stateG J G (E q) = stateG i G q) (as : List i.certified.Atom) :
    reportG J G as = reportG i G as := by
  apply mapM_congr_mem
  intro a _
  have roots := eqn (RingGroupedReport.origin i a)
  rw [reindex_origin,←rootG_exact,←rootG_exact] at roots
  exact congrArg (Option.map fun v => (a.val,v)) roots

theorem publish_reindex (G : Geometry) (q : Site i) (r : View i) (s : View J)
    (same : ∀ u, s (E u) = r u) : publishG J G (E q) s = publishG i G q r :=
  publish_reindex_of_priorities i g full G q r s
    (RingStereoKeyCoordinates.key_atGeometry i g full r s same)
    (RingStereoKeyCoordinates.marked_arm_atGeometry i g full r s same)

/-- Reading one coordinate map on two independently admitted copies of the same molecule
gives exactly the same complete recursive state at every original occurrence. -/
theorem stateG_reindex (G : Geometry) (q : Site i) : stateG J G (E q) = stateG i G q :=
  stateG_reindex_of_rule i g full G (publish_reindex i g full G) q

theorem reportG_reindex (G : Geometry) (atoms : List i.certified.Atom) :
    reportG J G atoms = reportG i G atoms :=
  reportG_reindex_of_state i g full G (stateG_reindex i g full G) atoms

end TetraStereo.Engine.RingSpatialTransport
assert_kernel_only TetraStereo.Engine.RingSpatialTransport.stateG_reindex
assert_kernel_only TetraStereo.Engine.RingSpatialTransport.reportG_reindex
