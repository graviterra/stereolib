import TetraStereo.Engine.RingChemicalGraphProof
import TetraStereo.Engine.RingHydrogenReport

/-!
# Transport of ring labels between coordinate maps on one fixed topology

One `Input` is fixed throughout: its graph, occurrences, frames, ligand keys and Rule 6 mark
words never change. Only the coordinate map `g : Geometry` read by the *final hand readback*
of the local publisher is a parameter.

* `publishG i g`  : the full-path tetrahedral rule and the pyramidal phosphorus rule, with every
                    `readback?` taken on `g` (and on `mirror g`) instead of `inputGeometry`.
* `stateG`, `rootG`, `reportG` : the distance schedule, bonded-path root and row report of
                    that rule.
* `SiteAgree i g g' q` : raw hypothesis on coordinates only. The tetrahedral frame of `q` has
                    the same hand in its written order, and a phosphorus focus has the same
                    hand on each order of its three bonded atoms.
* `rootG_transport`, `reportG_transport` : two coordinate maps that agree on the frames of the
                    sites in the digraph of the requested root give the same recursive root.
                    No equality of keys, ranks, local publications or reports is assumed.
* `stateG_input`, `rootG_input`, `reportG_input` : at `inputGeometry i.certified` these are
                    `RingChemicalGraphProof.state`, `.root` and `RingChemicalReport.report?`.
* `root_frame_transport`, `report_frame_transport`, `correct_iff_reportG` : the public
                    evaluator against any other coordinate map on the same input.
* `LocalCoordinates`, `root_translate` : sufficient conditions in raw coordinates.

The coordinate equivalence between separately admitted inputs is proved in
`RingCoordinateReportTransport`. `RingHydrogenPlacementExact` applies it to the raw API.
-/
set_option autoImplicit false

namespace TetraStereo.Engine.RingFrameTransport
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Frame Reader Labels)
open RingActivePairReport (Slot)
open RingActiveDistanceSchedule (View Cell frozen evaluate Visible distance height)
open RingStereoSiblingPass (Legal order legal_order)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key key?)
open RingFullPathTrialReadings (trialKey trials markWords?)
open RingFullPathPublication (keys? letters)
open RingPyramidalPublication
open RingGroupedReport (Report)

/-! ## List traversals -/

theorem mapM_congr_mem {α β : Type} (f f' : α → Option β) (xs : List α)
    (same : ∀ x ∈ xs, f x = f' x) : xs.mapM f = xs.mapM f' := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.mapM_cons,List.mapM_cons,same x (List.mem_cons.mpr (Or.inl rfl)),
      ih (fun y hy => same y (List.mem_cons_of_mem _ hy))]

theorem mapM_map {α β γ : Type} {f : α → Option β} {p : β → γ} {k : α → γ}
    (sound : ∀ a b, f a = some b → p b = k a) (xs : List α) (ys : List β)
    (got : xs.mapM f = some ys) : ys.map p = xs.map k := by
  induction xs generalizing ys with
  | nil =>
    simp at got
    subst got
    rfl
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons,hx] at got
    | some b =>
      cases hr : xs.mapM f with
      | none => simp [List.mapM_cons,hx,hr] at got
      | some bs =>
        simp [List.mapM_cons,hx,hr] at got
        subst got
        rw [List.map_cons,List.map_cons,sound x b hx,ih bs hr]

theorem mapM_filterMap {α β γ : Type} {f : α → Option β} {p : β → γ} {k : α → Option γ}
    (sound : ∀ a b, f a = some b → k a = some (p b)) (xs : List α) (ys : List β)
    (got : xs.mapM f = some ys) : ys.map p = xs.filterMap k := by
  induction xs generalizing ys with
  | nil =>
    simp at got
    subst got
    rfl
  | cons x xs ih =>
    cases hx : f x with
    | none => simp [List.mapM_cons,hx] at got
    | some b =>
      cases hr : xs.mapM f with
      | none => simp [List.mapM_cons,hx,hr] at got
      | some bs =>
        simp [List.mapM_cons,hx,hr] at got
        subst got
        rw [List.map_cons,List.filterMap_cons_some (sound x b hx),ih bs hr]

/-- A readback depends only on the coordinates of the atoms it lists. -/
theorem readback_congr {g g' : Geometry} {ids : List Nat} (same : ∀ n ∈ ids, g n = g' n) :
    readback? g ids = readback? g' ids := by
  unfold readback?
  rw [mapM_congr_mem g g' ids same]

/-! ## Tetrahedral rule with an abstract trial reader -/

/-- `RingFullPathTrialReadings.readingsWith` with the coordinate reading of one trial
supplied by the caller. -/
def readingsWithG {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (read : (Slot → List (List Word)) → Option RS) (ks : Slot → Key) :
    Option (List (Option Slot × Option RS)) :=
  (trials ks).mapM fun s => do
    let ws ← markWords? fr r s
    return (s,read (fun k => trialKey (ks k) (ws k)))

def readingsG {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (read : (Slot → List (List Word)) → Option RS) :
    Option (List (Option Slot × Option RS)) := do
  let ks ← RingActivePairReport.four? fun k => key? i r false (RingGroupedCentre.cursor fr k)
  readingsWithG fr r read ks

/-- `RingFullPathPublication.centre?` with the coordinate reading abstracted. Both key rows
and all mark words are read exactly as before, from the frozen reader alone. -/
def centreG {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (read : (Slot → List (List Word)) → Option RS) : Cell :=
  (keys? fr r false).bind fun ks => (keys? fr r true).bind fun ms =>
    (readingsG fr r read).map fun out => letters ks ms (out.map Prod.snd)

/-- The full-path centre rule is the abstract rule at its own trial reader. -/
theorem centre_abstract {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) :
    RingFullPathPublication.centre? fr r =
      centreG fr r (RingFullPathTrialReadings.readTrial fr false) := rfl

/-- Physical reading of one trial on the coordinate map `g`: no hand on a tie, otherwise
the four frame carriers in descending priority. -/
def readTrialG {i : Input} {f : Site i} (fr : Frame i f) (g : Geometry)
    (w : Slot → List (List Word)) : Option RS :=
  if ((List.finRange 4).map w).Nodup then readback? g (fr.atoms (order w (List.finRange 4)))
  else none

/-- Every order of the four frame carriers is determined by the written order. -/
theorem frame_hand {i : Input} {f : Site i} (fr : Frame i f) {g g' : Geometry}
    (same : readback? g (fr.atoms (List.finRange 4)) = readback? g' (fr.atoms (List.finRange 4)))
    (row : List Slot) (perm : row.Perm (List.finRange 4)) :
    readback? g (fr.atoms row) = readback? g' (fr.atoms row) :=
  (RingOrientation.frame_read fr g ⟨row,perm⟩).trans
    ((congrArg (fun base : Option RS =>
      if RingJointObservations.parity ⟨row,perm⟩ then base else base.map RS.swap) same).trans
      (RingOrientation.frame_read fr g' ⟨row,perm⟩).symm)

/-- Two coordinate maps giving one hand to the written frame give the same reading to
every trial, whatever its keys and mark words are. -/
theorem readTrialG_congr {i : Input} {f : Site i} (fr : Frame i f) {g g' : Geometry}
    (same : readback? g (fr.atoms (List.finRange 4)) = readback? g' (fr.atoms (List.finRange 4))) :
    readTrialG fr g = readTrialG fr g' := by
  funext w
  unfold readTrialG
  by_cases nd : ((List.finRange 4).map w).Nodup
  · rw [if_pos nd,if_pos nd]
    exact frame_hand fr same (order w (List.finRange 4)) (legal_order w (List.finRange 4)).perm
  · rw [if_neg nd,if_neg nd]

/-- On the admitted input coordinates the parameterized reading is the evaluator's. -/
theorem readTrialG_input {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} (fr : Frame i f) (w : Slot → List (List Word)) :
    readTrialG fr (inputGeometry i.certified) w = RingFullPathTrialReadings.readTrial fr false w := by
  apply (RingFullPathTrialReadings.read_exact geom fr false w _).mp
  by_cases nd : ((List.finRange 4).map w).Nodup
  · have inj : Function.Injective w := fun j k eqn =>
      List.inj_on_of_nodup_map nd (List.mem_finRange j) (List.mem_finRange k) eqn
    have canon := legal_order w (List.finRange 4)
    obtain ⟨h,hh⟩ := Option.isSome_iff_exists.mp (RingGroupedGeometry.calibrated geom fr _ canon.perm)
    have value : readTrialG fr (inputGeometry i.certified) w = some h := by
      unfold readTrialG
      rw [if_pos nd]
      exact hh
    have seen : RingFullPathTrialReadings.hand? fr false (order w (List.finRange 4)) = some h := by
      simpa only [RingFullPathTrialReadings.hand?,Bool.false_eq_true,if_false] using hh
    rw [value]
    exact .hand inj canon seen
  · have value : readTrialG fr (inputGeometry i.certified) w = none := by
      unfold readTrialG
      rw [if_neg nd]
    have notInj : ¬ Function.Injective w := fun inj => nd ((List.nodup_finRange 4).map inj)
    rw [value]
    unfold Function.Injective at notInj
    push_neg at notInj
    obtain ⟨j,k,tied,ne⟩ := notInj
    exact .tie ne tied

theorem centreG_input {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {f : Site i} (fr : Frame i f) (r : Reader i) :
    centreG fr r (readTrialG fr (inputGeometry i.certified)) = RingFullPathPublication.centre? fr r := by
  have reader : readTrialG fr (inputGeometry i.certified) =
      RingFullPathTrialReadings.readTrial fr false := funext (readTrialG_input geom fr)
  rw [reader]
  exact (centre_abstract fr r).symm

/-! ## Pyramidal rule with an abstract sense -/

/-- Reading of a list of carriers on `g` or on its mirror image. -/
def senseOf (g : Geometry) (rev : Bool) : List Nat → Option RS :=
  readback? (if rev then mirror g else g)

theorem senseOf_congr {g g' : Geometry} {ids : List Nat}
    (same : readback? g ids = readback? g' ids) (rev : Bool) :
    senseOf g rev ids = senseOf g' rev ids := by
  cases rev
  · exact same
  · show readback? (mirror g) ids = readback? (mirror g') ids
    rw [readback_mirror,readback_mirror,same]

def ligAtom {i : Input} (x : Ligand i) : Nat := x.atom

/-- Coordinate carriers of the bonded directions at an occurrence. -/
def ligandIds (i : Input) (q : Site i) : List Nat :=
  (RingRetainedAuxiliary.frame i.certified q).filterMap fun t =>
    t.occurrence.val.node.current?.map Fin.val

def ligandOf (i : Input) (r : View i) (rev : Bool) (arm : Arm i) : Option (Ligand i) :=
  arm.occurrence.val.node.current?.bind fun atom =>
    (key? i r rev arm).bind fun priority => some ⟨arm,atom.val,priority⟩

theorem ligands_unfold (i : Input) (q : Site i) (r : View i) (rev : Bool) :
    ligands? i q r rev = (RingRetainedAuxiliary.frame i.certified q).mapM (ligandOf i r rev) := rfl

theorem ligandOf_atom {i : Input} {r : View i} {rev : Bool} {arm : Arm i} {x : Ligand i}
    (h : ligandOf i r rev arm = some x) :
    arm.occurrence.val.node.current?.map Fin.val = some (ligAtom x) := by
  cases hc : arm.occurrence.val.node.current? with
  | none => simp [ligandOf,hc] at h
  | some atom =>
    cases hk : key? i r rev arm with
    | none => simp [ligandOf,hc,hk] at h
    | some p =>
      have built : some (⟨arm,atom.val,p⟩ : Ligand i) = some x := by
        simpa [ligandOf,hc,hk] using h
      rw [← Option.some.inj built]
      rfl

/-- The ligand row of an occurrence carries exactly its bonded atoms, in frame order. -/
theorem ligands_ids {i : Input} {q : Site i} {r : View i} {rev : Bool} {xs : List (Ligand i)}
    (got : ligands? i q r rev = some xs) : xs.map ligAtom = ligandIds i q :=
  mapM_filterMap (f := ligandOf i r rev) (p := ligAtom)
    (k := fun t : Arm i => t.occurrence.val.node.current?.map Fin.val)
    (fun _ _ h => ligandOf_atom h) _ xs ((ligands_unfold i q r rev).symm.trans got)

def markWord? (i : Input) (r : View i) (mark : Option Nat) (arm : Arm i) : Option Word :=
  match mark with
  | none => some []
  | some id => (RingGroupedMark.arm? i r id arm).map fun b => b.2.word

def rowOf (i : Input) (r : View i) (mark : Option Nat) (x : Ligand i) :
    Option (Nat × List (List Word)) :=
  (markWord? i r mark x.arm).bind fun word => some (x.atom,trialKey x.priority word)

theorem rowOf_atom {i : Input} {r : View i} {mark : Option Nat} {x : Ligand i}
    {row : Nat × List (List Word)} (h : rowOf i r mark x = some row) : row.1 = ligAtom x := by
  cases hw : markWord? i r mark x.arm with
  | none => simp [rowOf,hw] at h
  | some word =>
    have built : some (x.atom,trialKey x.priority word) = some row := by
      simpa [rowOf,hw] using h
    exact (congrArg Prod.fst (Option.some.inj built)).symm

def finishS (sense : List Nat → Option RS) (a : Nat) (rows : List (Nat × List (List Word))) :
    Option (Option RS) :=
  if !(rows.map Prod.snd).Nodup then some none
  else some (sense ((order Prod.snd rows).map Prod.fst ++ [a]))

/-- `RingPyramidalPublication.trial?` with the coordinate sense supplied by the caller. -/
def trialS {i : Input} (sense : List Nat → Option RS) (r : View i) (a : i.certified.Atom)
    (xs : List (Ligand i)) (mark : Option Nat) : Option (Option RS) :=
  Option.bind (xs.mapM (rowOf i r mark)) (finishS sense a.val)

theorem trial_input {i : Input} (r : View i) (a : i.certified.Atom) (rev : Bool)
    (xs : List (Ligand i)) (mark : Option Nat) :
    trial? r a rev xs mark = trialS (senseOf (inputGeometry i.certified) rev) r a xs mark := by
  first
    | rfl
    | (cases mark <;> rfl)

/-- A trial reads only orders of the ligand atoms followed by the centre. -/
theorem trialS_congr {i : Input} (sense sense' : List Nat → Option RS) (r : View i)
    (a : i.certified.Atom) (xs : List (Ligand i)) (mark : Option Nat)
    (same : ∀ row : List Nat, row.Perm (xs.map ligAtom) →
      sense (row ++ [a.val]) = sense' (row ++ [a.val])) :
    trialS sense r a xs mark = trialS sense' r a xs mark := by
  unfold trialS
  cases hrows : xs.mapM (rowOf i r mark) with
  | none => rfl
  | some rows =>
    have ids : rows.map Prod.fst = xs.map ligAtom :=
      mapM_map (f := rowOf i r mark) (p := Prod.fst) (k := ligAtom)
        (fun _ _ h => rowOf_atom h) xs rows hrows
    have perm : ((order Prod.snd rows).map Prod.fst).Perm (xs.map ligAtom) :=
      ((legal_order Prod.snd rows).perm.map Prod.fst).trans (List.Perm.of_eq ids)
    show finishS sense a.val rows = finishS sense' a.val rows
    unfold finishS
    rw [same _ perm]

def marksOf {i : Input} (xs : List (Ligand i)) : List (Option Nat) :=
  match xs with
  | [x,y,z] => if x.priority == y.priority && y.priority == z.priority then
      [some x.atom,some y.atom,some z.atom] else [none]
  | _ => []

/-- `RingPyramidalPublication.hands?` with the coordinate sense supplied by the caller. -/
def handsS (sense : List Nat → Option RS) (i : Input) (q : Site i) (r : View i)
    (a : i.certified.Atom) (rev : Bool) : Option (List (Option RS)) :=
  Option.bind (ligands? i q r rev) fun xs => (marksOf xs).mapM (trialS sense r a xs)

theorem hands_input (i : Input) (q : Site i) (r : View i) (a : i.certified.Atom) (rev : Bool) :
    hands? i q r a rev = handsS (senseOf (inputGeometry i.certified) rev) i q r a rev := by
  have step : hands? i q r a rev = Option.bind (ligands? i q r rev)
      (fun xs => (marksOf xs).mapM (trial? r a rev xs)) := rfl
  have fn : (fun xs : List (Ligand i) => (marksOf xs).mapM (trial? r a rev xs)) =
      fun xs => (marksOf xs).mapM (trialS (senseOf (inputGeometry i.certified) rev) r a xs) :=
    funext fun xs => congrArg (fun t => (marksOf xs).mapM t)
      (funext fun mark => trial_input r a rev xs mark)
  exact step.trans (congrArg (Option.bind (ligands? i q r rev)) fn)

theorem handsS_congr (sense sense' : List Nat → Option RS) (i : Input) (q : Site i) (r : View i)
    (a : i.certified.Atom) (rev : Bool)
    (same : ∀ row : List Nat, row.Perm (ligandIds i q) →
      sense (row ++ [a.val]) = sense' (row ++ [a.val])) :
    handsS sense i q r a rev = handsS sense' i q r a rev := by
  unfold handsS
  cases hx : ligands? i q r rev with
  | none => rfl
  | some xs =>
    have ids : xs.map ligAtom = ligandIds i q := ligands_ids hx
    have fn : trialS sense r a xs = trialS sense' r a xs := funext fun mark =>
      trialS_congr sense sense' r a xs mark
        (fun row perm => same row (perm.trans (List.Perm.of_eq ids)))
    show (marksOf xs).mapM (trialS sense r a xs) = (marksOf xs).mapM (trialS sense' r a xs)
    exact congrArg (fun t => (marksOf xs).mapM t) fn

/-- `RingPyramidalPublication.pLabels` reading the phantom hand on `g` and on `mirror g`. -/
def pLabelsG (i : Input) (g : Geometry) (q : Site i) (r : View i) (a : i.certified.Atom) :
    Option Labels := do
  guard ((RingRetainedAuxiliary.frame i.certified q).length = 3)
  let hs ← handsS (senseOf g false) i q r a false
  let ms ← handsS (senseOf g true) i q r a true
  RingFullPathPublication.crossed hs ms

theorem pLabelsG_input (i : Input) (q : Site i) (r : View i) (a : i.certified.Atom) :
    pLabelsG i (inputGeometry i.certified) q r a = pLabels i q r a := by
  unfold pLabelsG RingPyramidalPublication.pLabels
  rw [hands_input i q r a false,hands_input i q r a true]

theorem pLabelsG_congr (i : Input) {g g' : Geometry} (q : Site i) (r : View i)
    (a : i.certified.Atom)
    (same : ∀ row : List Nat, row.Perm (ligandIds i q) →
      readback? g (row ++ [a.val]) = readback? g' (row ++ [a.val])) :
    pLabelsG i g q r a = pLabelsG i g' q r a := by
  unfold pLabelsG
  rw [handsS_congr (senseOf g false) (senseOf g' false) i q r a false
      (fun row perm => senseOf_congr (same row perm) false),
    handsS_congr (senseOf g true) (senseOf g' true) i q r a true
      (fun row perm => senseOf_congr (same row perm) true)]

/-! ## The parameterized local publisher -/

def tetraG (i : Input) (g : Geometry) (q : Site i) (r : View i) : Cell :=
  match RingNestedActivePair.frame? i q with
  | none => some none
  | some fr => centreG fr r (readTrialG fr g)

/-- Local publication on the fixed topology of `i`, reading every hand on `g`. -/
def publishG (i : Input) (g : Geometry) (q : Site i) (r : View i) : Cell :=
  match focusP i q with
  | some a => some (pLabelsG i g q r a)
  | none => tetraG i g q r

theorem publishG_phosphorus {i : Input} (g : Geometry) {q : Site i} {a : i.certified.Atom}
    (hp : focusP i q = some a) (r : View i) : publishG i g q r = some (pLabelsG i g q r a) := by
  simp [publishG,hp]

theorem publishG_tetra {i : Input} (g : Geometry) {q : Site i} (hp : focusP i q = none)
    (r : View i) : publishG i g q r = tetraG i g q r := by
  simp [publishG,hp]

theorem tetraG_absent {i : Input} (g : Geometry) {q : Site i}
    (hf : RingNestedActivePair.frame? i q = none) (r : View i) : tetraG i g q r = some none := by
  simp [tetraG,hf]

theorem tetraG_centre {i : Input} (g : Geometry) {q : Site i} {fr : Frame i q}
    (hf : RingNestedActivePair.frame? i q = some fr) (r : View i) :
    tetraG i g q r = centreG fr r (readTrialG fr g) := by
  simp [tetraG,hf]

/-- Agreement of two coordinate maps on the local frame of one occurrence. Both clauses
compare raw coordinate readings. Neither mentions a key, a rank or a label. -/
def SiteAgree (i : Input) (g g' : Geometry) (q : Site i) : Prop :=
  (∀ fr : Frame i q,
    readback? g (fr.atoms (List.finRange 4)) = readback? g' (fr.atoms (List.finRange 4))) ∧
  (∀ a : i.certified.Atom, focusP i q = some a → ∀ row : List Nat, row.Perm (ligandIds i q) →
    readback? g (row ++ [a.val]) = readback? g' (row ++ [a.val]))

/-- Local transport: on agreeing frames the two rules coincide on every reader. -/
theorem publishG_congr {i : Input} {g g' : Geometry} {q : Site i} (agree : SiteAgree i g g' q)
    (r : View i) : publishG i g q r = publishG i g' q r := by
  cases hp : focusP i q with
  | some a =>
    exact (publishG_phosphorus g hp r).trans
      ((congrArg some (pLabelsG_congr i q r a (agree.2 a hp))).trans
        (publishG_phosphorus g' hp r).symm)
  | none =>
    refine (publishG_tetra g hp r).trans (Eq.trans ?_ (publishG_tetra g' hp r).symm)
    cases hf : RingNestedActivePair.frame? i q with
    | none => exact (tetraG_absent g hf r).trans (tetraG_absent g' hf r).symm
    | some fr =>
      exact (tetraG_centre g hf r).trans
        ((congrArg (centreG fr r) (readTrialG_congr fr (agree.1 fr))).trans
          (tetraG_centre g' hf r).symm)

/-- Ineligible occurrences are skipped on every coordinate map. -/
theorem skipsG (i : Input) (g : Geometry) :
    RingEligibleGraph.SkipsIneligible (eligible i) (publishG i g) := by
  intro q r no
  have hp : focusP i q = none := by
    unfold focusP
    split
    · rename_i real
      cases h : q.val.node.current? with
      | none => rfl
      | some a =>
        have off : phosphorus i a = false := by
          cases he : phosphorus i a
          · rfl
          · exact (no ⟨real,a,h,by simp [eligible,he]⟩).elim
        simp [Option.filter,off]
    · rfl
  have absent : i.certified.localizedOccurrenceDescriptorCenter? q = none := by
    cases h : i.certified.localizedOccurrenceDescriptorCenter? q with
    | none => rfl
    | some c =>
      obtain ⟨real,atom⟩ := (i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff q c).mp h
      exact (no ⟨real,c.val,atom,by
        simp only [eligible, Bool.or_eq_true, decide_eq_true_eq]
        exact Or.inl ((i.certified.moleculeGraph.mem_tetrahedralCenterSet _).mp c.property)⟩).elim
  have hf : RingNestedActivePair.frame? i q = none := by
    cases h : RingNestedActivePair.frame? i q with
    | none => rfl
    | some fr => exact nomatch absent.symm.trans fr.recognized
  exact (publishG_tetra g hp r).trans (tetraG_absent g hf r)

/-! ## Recursive state, root and report on a coordinate map -/

def stateG (i : Input) (g : Geometry) : View i := evaluate (publishG i g)

theorem stateG_eq (i : Input) (g : Geometry) (q : Site i) :
    stateG i g q = publishG i g q (frozen (stateG i g) q) :=
  RingActiveDistanceSchedule.evaluate_eq _ _

theorem frozen_congr {i : Input} {s t : View i} (q : Site i)
    (deeper : ∀ u, Visible q u → s u = t u) : frozen s q = frozen t q := by
  funext u
  unfold frozen
  split_ifs with off allowed
  · rfl
  · exact deeper u ⟨of_not_not off,allowed⟩
  · rfl

/-- Simultaneous transport of every publication in one original digraph. The induction
runs from the greatest distance toward the root. At each occurrence the frozen readers of
the two schedules coincide by induction, and the local rules coincide by `publishG_congr`. -/
theorem stateG_transport {i : Input} {g g' : Geometry} (q : Site i)
    (agree : ∀ u : Site i, u.val.root = q.val.root → SiteAgree i g g' u) :
    stateG i g q = stateG i g' q := by
  suffices h : ∀ n (u : Site i), u.val.root = q.val.root → height i - distance u = n →
      stateG i g u = stateG i g' u from h _ q rfl rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u on depth
    have same : frozen (stateG i g) u = frozen (stateG i g') u :=
      frozen_congr u (fun v vis => by
        have upper := RingActiveDistanceSchedule.distance_bound v
        have down := vis.2.1
        exact ih _ (by omega) v (vis.1.trans on) rfl)
    exact (stateG_eq i g u).trans
      ((congrArg (publishG i g u) same).trans
        ((publishG_congr (agree u on) _).trans (stateG_eq i g' u).symm))

/-- Bonded-path root on the coordinate map `g`. -/
def rootG (i : Input) (g : Geometry) (a : i.certified.Atom) : Cell :=
  RingEligibleGraph.root i (eligible i) (publishG i g) a

theorem rootG_exact (i : Input) (g : Geometry) (a : i.certified.Atom) :
    rootG i g a = stateG i g (RingGroupedReport.origin i a) :=
  RingEligibleGraph.root_exact (publishG i g) (skipsG i g) a

/-- **Root transport.** Two coordinate maps agreeing on the local frames of the
occurrences in the digraph of `a` give the same complete recursive root cell,
including a completed refusal and an unresolved cell. -/
theorem rootG_transport {i : Input} {g g' : Geometry} (a : i.certified.Atom)
    (agree : ∀ u : Site i, u.val.root = a → SiteAgree i g g' u) : rootG i g a = rootG i g' a :=
  (rootG_exact i g a).trans
    ((stateG_transport (RingGroupedReport.origin i a) (fun u on =>
      agree u (on.trans (RingGroupedReport.origin_address i a).1))).trans
      (rootG_exact i g' a).symm)

def reportG (i : Input) (g : Geometry) (atoms : List i.certified.Atom) : Option Report :=
  atoms.mapM fun a => (rootG i g a).map fun v => (a.val,v)

/-- **Report transport.** Agreement is required only in the digraphs of requested atoms. -/
theorem reportG_transport {i : Input} {g g' : Geometry} (atoms : List i.certified.Atom)
    (agree : ∀ u : Site i, u.val.root ∈ atoms → SiteAgree i g g' u) :
    reportG i g atoms = reportG i g' atoms := by
  show atoms.mapM (fun a => (rootG i g a).map fun v => (a.val,v)) =
    atoms.mapM (fun a => (rootG i g' a).map fun v => (a.val,v))
  exact mapM_congr_mem _ _ atoms (fun a mem =>
    congrArg (Option.map fun v => (a.val,v))
      (rootG_transport a (fun u on => agree u (by rw [on]; exact mem))))

/-! ## Instantiation at the coordinates of the input -/

/-- On every ready reader the parameterized rule at the input coordinates is the
publication rule of `RingChemicalGraphProof`, including its constitutional early exit. -/
theorem publishG_input {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {r : View i} (ready : RingGroupedStereo.Ready q r) :
    publishG i (inputGeometry i.certified) q r = publish i q r := by
  cases hp : focusP i q with
  | some a =>
    have right : publish i q r = some (pLabels i q r a) := by simp [publish,hp]
    exact (publishG_phosphorus _ hp r).trans
      ((congrArg some (pLabelsG_input i q r a)).trans right.symm)
  | none =>
    have fast : publish i q r = RingFullPathConstitution.fastPublish i q r := by simp [publish,hp]
    have full : publish i q r = RingFullPathPublication.publish? i q r :=
      fast.trans (RingFullPathConstitution.fast_local geom ready)
    refine (publishG_tetra _ hp r).trans (Eq.trans ?_ full.symm)
    cases hf : RingNestedActivePair.frame? i q with
    | none =>
      have pub : RingFullPathPublication.publish? i q r = some none := by
        simp [RingFullPathPublication.publish?,hf]
      exact (tetraG_absent _ hf r).trans pub.symm
    | some fr =>
      have pub : RingFullPathPublication.publish? i q r = RingFullPathPublication.centre? fr r := by
        simp [RingFullPathPublication.publish?,hf]
      exact (tetraG_centre _ hf r).trans ((centreG_input geom fr r).trans pub.symm)

theorem stateG_input {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    stateG i (inputGeometry i.certified) = RingChemicalGraphProof.state i :=
  (RingActiveDistanceSchedule.unique (publishG i (inputGeometry i.certified))
    (RingChemicalGraphProof.state i) (fun q =>
      (RingChemicalGraphProof.state_eq i q).trans
        (publishG_input geom (RingChemicalGraphProof.ready geom q)).symm)).symm

theorem rootG_input {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (a : i.certified.Atom) :
    rootG i (inputGeometry i.certified) a = RingChemicalGraphProof.root i a :=
  (rootG_exact i _ a).trans
    ((congrFun (stateG_input geom) (RingGroupedReport.origin i a)).trans
      (RingEligibleGraph.root_exact (publish i) (RingChemicalGraphProof.skips i) a).symm)

theorem reportG_input {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (atoms : List i.certified.Atom) :
    reportG i (inputGeometry i.certified) atoms = RingChemicalReport.report? i atoms := by
  have rows : RingChemicalReport.report? i atoms =
      atoms.mapM (fun a => (RingChemicalGraphProof.root i a).map fun v => (a.val,v)) := rfl
  refine Eq.trans ?_ rows.symm
  show atoms.mapM (fun a => (rootG i (inputGeometry i.certified) a).map fun v => (a.val,v)) =
    atoms.mapM (fun a => (RingChemicalGraphProof.root i a).map fun v => (a.val,v))
  exact mapM_congr_mem _ _ atoms (fun a _ =>
    congrArg (Option.map fun v => (a.val,v)) (rootG_input geom a))

/-! ## Headlines against the public evaluator -/

/-- **Public root under a change of coordinates.** The root computed by
`RingChemicalGraphProof.root` on the admitted input is the root of the same topology read on
any coordinate map `g` that agrees with the input on the local frames in the digraph of `a`.
The hypotheses are admission of the input coordinates and raw frame readings only. -/
theorem root_frame_transport {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (g : Geometry) (a : i.certified.Atom)
    (agree : ∀ u : Site i, u.val.root = a → SiteAgree i (inputGeometry i.certified) g u) :
    RingChemicalGraphProof.root i a = rootG i g a :=
  (rootG_input geom a).symm.trans (rootG_transport a agree)

theorem report_frame_transport {i : Input}
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (g : Geometry)
    (atoms : List i.certified.Atom)
    (agree : ∀ u : Site i, u.val.root ∈ atoms → SiteAgree i (inputGeometry i.certified) g u) :
    RingChemicalReport.report? i atoms = reportG i g atoms :=
  (reportG_input geom atoms).symm.trans (reportG_transport atoms agree)

/-- The independent graph specification of the public report holds of exactly the rows
computed on any agreeing coordinate map. -/
theorem correct_iff_reportG {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (g : Geometry) (atoms : List i.certified.Atom)
    (agree : ∀ u : Site i, u.val.root ∈ atoms → SiteAgree i (inputGeometry i.certified) g u)
    (rows : Report) : RingChemicalReport.Correct i atoms rows ↔ reportG i g atoms = some rows := by
  have same := report_frame_transport geom g atoms agree
  rw [← same]
  exact (RingChemicalReport.report_iff i geom atoms rows).symm

/-! ## Sufficient conditions in raw coordinates -/

/-- The two maps give the same point to each atom of the local frame: the four ligands of a
tetrahedral occurrence, or a phosphorus and its three bonded atoms. Every other atom may
move freely, including atoms outside the molecule's index range. -/
def LocalCoordinates (i : Input) (g g' : Geometry) (q : Site i) : Prop :=
  (∀ fr : Frame i q, ∀ n ∈ fr.atoms (List.finRange 4), g n = g' n) ∧
  (∀ a : i.certified.Atom, focusP i q = some a →
    g a.val = g' a.val ∧ ∀ n ∈ ligandIds i q, g n = g' n)

theorem LocalCoordinates.agree {i : Input} {g g' : Geometry} {q : Site i}
    (same : LocalCoordinates i g g' q) : SiteAgree i g g' q := by
  refine ⟨fun fr => readback_congr (same.1 fr),fun a hp row perm => readback_congr ?_⟩
  intro n mem
  rcases List.mem_append.mp mem with inRow | last
  · exact (same.2 a hp).2 n (perm.mem_iff.mp inRow)
  · rw [List.mem_singleton.mp last]
    exact (same.2 a hp).1

/-- A coordinate map that keeps the points of every local frame in the digraph of `a`
leaves the public root unchanged. -/
theorem root_local_coordinates {i : Input}
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (g : Geometry)
    (a : i.certified.Atom)
    (same : ∀ u : Site i, u.val.root = a → LocalCoordinates i (inputGeometry i.certified) g u) :
    RingChemicalGraphProof.root i a = rootG i g a :=
  root_frame_transport geom g a (fun u on => (same u on).agree)

/-! ### A global change of coordinates: translation -/

def translate (v p : CartesianPoint3) : CartesianPoint3 := ⟨p.x+v.x,p.y+v.y,p.z+v.z⟩

/-- Apply one map of space to every located atom. -/
def moved (T : CartesianPoint3 → CartesianPoint3) (geom : Geometry) : Geometry :=
  fun atom => (geom atom).map T

theorem volume_translate (v a b c d : CartesianPoint3) :
    CartesianPoint3.orientedVolume (translate v a) (translate v b) (translate v c) (translate v d) =
      CartesianPoint3.orientedVolume a b c d := by
  simp only [CartesianPoint3.orientedVolume,translate]
  ring

theorem descriptor_translate (v : CartesianPoint3) : ∀ points : List CartesianPoint3,
    descriptorOfPriorityOrderedPoints? (points.map (translate v)) =
      descriptorOfPriorityOrderedPoints? points
  | [] => rfl
  | [_] => rfl
  | [_,_] => rfl
  | [_,_,_] => rfl
  | [a,b,c,d] => congrArg descriptorOfOrientedVolume? (volume_translate v a b c d)
  | _ :: _ :: _ :: _ :: _ :: _ => rfl

theorem mapM_moved (T : CartesianPoint3 → CartesianPoint3) (geom : Geometry) (atoms : List Nat) :
    atoms.mapM (moved T geom) = (atoms.mapM geom).map (List.map T) := by
  induction atoms with
  | nil => rfl
  | cons atom tail ih =>
      simp only [List.mapM_cons, moved, ih]
      cases geom atom <;> cases tail.mapM geom <;> rfl

theorem readback_translate (v : CartesianPoint3) (geom : Geometry) (atoms : List Nat) :
    readback? (moved (translate v) geom) atoms = readback? geom atoms := by
  unfold readback?
  rw [mapM_moved]
  cases atoms.mapM geom with
  | none => rfl
  | some points =>
    exact descriptor_translate v points

theorem translate_agree (i : Input) (g : Geometry) (v : CartesianPoint3) (q : Site i) :
    SiteAgree i g (moved (translate v) g) q :=
  ⟨fun _ => (readback_translate v g _).symm,fun _ _ _ _ => (readback_translate v g _).symm⟩

/-- Translating every atom leaves every public root unchanged. No frame, key or label
hypothesis remains. -/
theorem root_translate {i : Input} (geom : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (v : CartesianPoint3) (a : i.certified.Atom) :
    RingChemicalGraphProof.root i a =
      rootG i (moved (translate v) (inputGeometry i.certified)) a :=
  root_frame_transport geom _ a (fun u _ => translate_agree i _ v u)

end TetraStereo.Engine.RingFrameTransport

assert_kernel_only TetraStereo.Engine.RingFrameTransport.rootG_transport
assert_kernel_only TetraStereo.Engine.RingFrameTransport.reportG_transport
assert_kernel_only TetraStereo.Engine.RingFrameTransport.stateG_input
assert_kernel_only TetraStereo.Engine.RingFrameTransport.root_frame_transport
assert_kernel_only TetraStereo.Engine.RingFrameTransport.report_frame_transport
assert_kernel_only TetraStereo.Engine.RingFrameTransport.correct_iff_reportG
assert_kernel_only TetraStereo.Engine.RingFrameTransport.root_translate
