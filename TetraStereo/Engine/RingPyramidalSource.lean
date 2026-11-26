import TetraStereo.Engine.RingPyramidalPublication

/-! # Independent chemical source for tricoordinate phosphorus

P-93.3.4.1: a pyramidal phosphorus has three bonded ligands and a phantom of
permanently lowest rank on the side of P away from them.

The relation `Source` below never mentions the executable publication. It is
assembled from

* the three incident directions of the occurrence in the molecular digraph
  and the atom carried by each of them (`Directions`);
* the independently derived molecular priorities
  `RingFullPathEligibility.Reads` on each geometry;
* the Rule 6 trials: one ordinary trial, or one trial for each ligand atom
  when all three real ligands tie (`trials`), with the mark words read by the
  declarative `RingGroupedMark.OnGeometry` (`MarkWords`);
* for each trial, a tie or any legal descending order of the three ligands
  read against the phantom point (`Outcome`, `Sense`);
* cancellation of opposite votes on each geometry and the crossed pair of
  surviving hands (`RingFullPathPublication.crossed`).

`source_iff` proves that on every ready reader this relation has exactly one
value, the value of `RingPyramidalPublication.pLabels`.

The executable `Ligand`, `ligands?`, `trial?` and `hands?` of
`RingPyramidalPublication` occur only in the proofs. -/
set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.Engine.RingPyramidalSource
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader Labels)
open RingStereoSiblingPass (Legal order legal_order)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key Reads key?)
open RingFullPathTrialReadings (trialKey)
open RingFullPathPublication (crossed)
open RingPyramidalPublication (Ligand ligands? trial? hands? pLabels phantomPoint)

/-! ## Source vocabulary -/

/-- The three ligand positions of a pyramidal centre. -/
def slots : List (Fin 3) := [0,1,2]

/-- The three real incident directions of an occurrence: its complete frame
in the digraph, and the atom carried by each direction. The direction toward
the root is included when the occurrence is an auxiliary one. -/
structure Directions (i : Input) (q : Site i) where
  arm : Fin 3 → Arm i
  atom : Fin 3 → i.certified.Atom
  incident : RingRetainedAuxiliary.frame i.certified q = [arm 0,arm 1,arm 2]
  real : ∀ k, (arm k).occurrence.val.node.current? = some (atom k)

/-- Coordinate carrier of a ligand. -/
def atomId {i : Input} {q : Site i} (d : Directions i q) (k : Fin 3) : Nat := (d.atom k).val

/-- The original coordinates, or their mirror image. -/
def geometry (i : Input) (rev : Bool) : Geometry :=
  if rev then mirror (inputGeometry i.certified) else inputGeometry i.certified

/-- Hand of three ligands `x`, `y`, `z` in descending rank around the centre
`p`, with the phantom as the fourth and lowest point. A hand is read exactly
when all four atoms are located and the three ligands are not coplanar with
the phantom. Missing coordinates and a degenerate plane both read no hand. -/
def Sense (g : Geometry) (p x y z : Nat) (v : Option RS) : Prop :=
  ∀ h, v = some h ↔ ∃ a b c o, g x = some a ∧ g y = some b ∧ g z = some c ∧ g p = some o ∧
    descriptorOfPriorityOrderedPoints? [a,b,c,phantomPoint a b c o] = some h

/-- The phantom never ties with a real ligand. Rule 6 therefore applies
exactly when all three real ligands tie, with one trial for each of them.
Every other pattern receives the single ordinary trial. -/
def trials (ks : Fin 3 → Key) : List (Option (Fin 3)) :=
  if ks 0 = ks 1 ∧ ks 1 = ks 2 then [some 0,some 1,some 2] else [none]

/-- The ordinary trial carries no mark. A promotion trial marks every
occurrence of the atom of the selected ligand in each of the three branches. -/
def MarkWords {i : Input} {q : Site i} (d : Directions i q) (r : Reader i) (rev : Bool) :
    Option (Fin 3) → (Fin 3 → Word) → Prop
  | none,ws => ∀ k, ws k = []
  | some s,ws => ∀ k, ∃ b, RingGroupedMark.OnGeometry i r rev (atomId d s) (d.arm k) b ∧ ws k = b.word

/-- A tie among the three real ligands yields no hand. A strict order reads
any legal descending row of the three ligands against the phantom. -/
inductive Outcome {i : Input} {q : Site i} (d : Directions i q) (a : i.certified.Atom) (rev : Bool)
    (w : Fin 3 → List (List Word)) : Option RS → Prop where
  | tie {j k} (different : j ≠ k) (same : w j = w k) : Outcome d a rev w none
  | read (j k l : Fin 3) {v} (strictOrder : Function.Injective w) (legal : Legal w slots [j,k,l])
      (sense : Sense (geometry i rev) a.val (atomId d j) (atomId d k) (atomId d l) v) :
      Outcome d a rev w v

/-- All trial hands of one geometry, from any molecular reading of the three
ordinary keys, any admissible mark words and any legal coordinate row. -/
def Ballots {i : Input} {q : Site i} (d : Directions i q) (r : Reader i) (a : i.certified.Atom)
    (rev : Bool) (ks : Fin 3 → Key) (hands : List (Option RS)) : Prop :=
  (∀ j, Reads i r rev (d.arm j) (ks j)) ∧
    List.Forall₂ (fun s v => ∃ ws, MarkWords d r rev s ws ∧
      Outcome d a rev (fun j => trialKey (ks j) (ws j)) v) (trials ks) hands

/-- Independent local specification at a phosphorus atom `a`. An occurrence
without three real incident directions has no label. Otherwise both physical
configurations are read separately and their surviving hands are crossed. -/
inductive Source (i : Input) (q : Site i) (r : Reader i) (a : i.certified.Atom) :
    Option Labels → Prop where
  | absent (unframed : ¬ Nonempty (Directions i q)) : Source i q r a none
  | centre (d : Directions i q) {x y : Fin 3 → Key} {actual reflected : List (Option RS)}
      (original : Ballots d r a false x actual) (mirrored : Ballots d r a true y reflected) :
      Source i q r a (crossed actual reflected)

/-! ## The three directions -/

private theorem mem_slots (k : Fin 3) : k ∈ slots := by
  revert k
  decide

private theorem slots_nodup : slots.Nodup := by
  decide

private theorem some_of_ne_none {α : Type} {o : Option α} (h : o ≠ none) : ∃ x, o = some x := by
  cases o with
  | none => exact (h rfl).elim
  | some x => exact ⟨x,rfl⟩

theorem Directions.three {i : Input} {q : Site i} (d : Directions i q) :
    (RingRetainedAuxiliary.frame i.certified q).length = 3 :=
  congrArg List.length d.incident

theorem Directions.mem {i : Input} {q : Site i} (d : Directions i q) (k : Fin 3) :
    d.arm k ∈ RingRetainedAuxiliary.frame i.certified q := by
  have listed : d.arm k ∈ slots.map d.arm := List.mem_map.mpr ⟨k,mem_slots k,rfl⟩
  rw [d.incident]
  exact listed

theorem Directions.valid {i : Input} {q : Site i} (d : Directions i q) (k : Fin 3) :
    i.certified.LocalizedRerootCursorValid (d.arm k) :=
  i.certified.localizedRerootChild_valid (⟨q,none⟩ : Arm i) (d.arm k) _
    (i.certified.executableLocalizedRerootChildren_declarative (⟨q,none⟩ : Arm i)) (d.mem k)

theorem Directions.rooted {i : Input} {q : Site i} (d : Directions i q) (k : Fin 3) :
    (d.arm k).occurrence.val.root = q.val.root :=
  i.certified.localizedRerootChildren_root_eq (⟨q,none⟩ : Arm i) (d.arm k) _
    (i.certified.executableLocalizedRerootChildren_declarative (⟨q,none⟩ : Arm i)) (d.mem k)

/-- The frame and its atoms determine the three directions. -/
theorem Directions.unique {i : Input} {q : Site i} (d e : Directions i q) : d = e := by
  obtain ⟨arm,atom,incident,real⟩ := d
  obtain ⟨arm',atom',incident',real'⟩ := e
  have listed : slots.map arm = slots.map arm' := incident.symm.trans incident'
  have arms : arm = arm' := funext fun k => List.map_inj_left.mp listed k (mem_slots k)
  subst arms
  have atoms : atom = atom' := funext fun k => Option.some.inj ((real k).symm.trans (real' k))
  subst atoms
  rfl

/-- Frame facts sufficient for the three directions: exactly three incident
directions, each carrying an atom. -/
theorem directions_of {i : Input} {q : Site i}
    (shape : (RingRetainedAuxiliary.frame i.certified q).length = 3)
    (real : ∀ t : Arm i, t ∈ RingRetainedAuxiliary.frame i.certified q →
      t.occurrence.val.node.current? ≠ none) : Nonempty (Directions i q) := by
  obtain ⟨x,y,z,listed⟩ := List.length_eq_three.mp shape
  have member (t : Arm i) (h : t ∈ [x,y,z]) : t.occurrence.val.node.current? ≠ none := by
    apply real t
    rw [listed]
    exact h
  obtain ⟨ax,hx⟩ := some_of_ne_none (member x (by simp))
  obtain ⟨ay,hy⟩ := some_of_ne_none (member y (by simp))
  obtain ⟨az,hz⟩ := some_of_ne_none (member z (by simp))
  exact ⟨⟨![x,y,z],![ax,ay,az],listed,by
    intro k
    fin_cases k <;> (first | exact hx | exact hy | exact hz)⟩⟩

/-! ## Coordinate reading against the phantom -/

private theorem option_eq {α : Type} {u v : Option α} (h : ∀ a, u = some a ↔ v = some a) : u = v := by
  cases u with
  | none =>
    cases v with
    | none => rfl
    | some b => exact (h b).mpr rfl
  | some a => exact ((h a).mp rfl).symm

/-- Reading the three ligands with P itself as the fourth point has the
sign of the phantom on the P side of their plane. -/
private theorem readback_phantom (g : Geometry) (p x y z : Nat) :
    readback? g [x,y,z,p] =
      (g x).bind fun a => (g y).bind fun b => (g z).bind fun c => (g p).bind fun o =>
        descriptorOfPriorityOrderedPoints? [a,b,c,phantomPoint a b c o] := by
  cases hx : g x <;> cases hy : g y <;> cases hz : g z <;> cases hp : g p <;>
    simp [readback?,List.mapM_cons,List.mapM_nil,hx,hy,hz,hp,RingPyramidalPublication.phantom_hand]

private theorem read_some (g : Geometry) (p x y z : Nat) (h : RS) :
    readback? g [x,y,z,p] = some h ↔
      ∃ a b c o, g x = some a ∧ g y = some b ∧ g z = some c ∧ g p = some o ∧
        descriptorOfPriorityOrderedPoints? [a,b,c,phantomPoint a b c o] = some h := by
  rw [readback_phantom]
  constructor
  · intro eqn
    obtain ⟨a,ha,eqn⟩ := Option.bind_eq_some_iff.mp eqn
    obtain ⟨b,hb,eqn⟩ := Option.bind_eq_some_iff.mp eqn
    obtain ⟨c,hc,eqn⟩ := Option.bind_eq_some_iff.mp eqn
    obtain ⟨o,ho,eqn⟩ := Option.bind_eq_some_iff.mp eqn
    exact ⟨a,b,c,o,ha,hb,hc,ho,eqn⟩
  · rintro ⟨a,b,c,o,ha,hb,hc,ho,eqn⟩
    rw [ha,hb,hc,ho]
    exact eqn

/-- The declarative phantom reading is the determinant reading with P as
the fourth point. -/
theorem sense_exact (g : Geometry) (p x y z : Nat) (v : Option RS) :
    Sense g p x y z v ↔ v = readback? g [x,y,z,p] := by
  constructor
  · intro s
    exact option_eq fun h => (s h).trans (read_some g p x y z h).symm
  · intro eqn
    subst eqn
    intro h
    exact read_some g p x y z h

/-! ## One trial -/

private theorem legal_unique {α κ : Type} [LinearOrder κ] {key : α → κ} {xs a b : List α}
    (inj : ∀ x ∈ xs, ∀ y ∈ xs, key x = key y → x = y)
    (left : Legal key xs a) (right : Legal key xs b) : a = b :=
  List.Perm.eq_of_pairwise
    (fun x y hx hy xy yx =>
      inj x (left.perm.mem_iff.mp hx) y (right.perm.mem_iff.mp hy) (le_antisymm yx xy))
    (List.pairwise_map.mp left.descending) (List.pairwise_map.mp right.descending)
    (left.perm.trans right.perm.symm)

private theorem nodup_injective {κ : Type} (w : Fin 3 → κ) :
    [w 0,w 1,w 2].Nodup ↔ Function.Injective w := by
  constructor
  · intro nd j k eqn
    have listed : (slots.map w).Nodup := nd
    exact List.inj_on_of_nodup_map listed (mem_slots j) (mem_slots k) eqn
  · intro inj
    have listed : (slots.map w).Nodup := List.Nodup.map inj slots_nodup
    exact listed

/-- Carrier and trial key of one ligand. -/
def entry {i : Input} {q : Site i} (d : Directions i q) (w : Fin 3 → List (List Word)) (k : Fin 3) :
    Nat × List (List Word) := (atomId d k,w k)

def entries {i : Input} {q : Site i} (d : Directions i q) (w : Fin 3 → List (List Word)) :
    List (Nat × List (List Word)) := [entry d w 0,entry d w 1,entry d w 2]

/-- Deterministic value of one trial: no hand on a tie, otherwise the sorted
carriers read with P as the fourth point. -/
def readTrial {i : Input} {q : Site i} (d : Directions i q) (a : i.certified.Atom) (rev : Bool)
    (w : Fin 3 → List (List Word)) : Option RS :=
  if [w 0,w 1,w 2].Nodup then
    readback? (geometry i rev) ((order Prod.snd (entries d w)).map Prod.fst ++ [a.val])
  else none

private theorem map_fst_entries {i : Input} {q : Site i} (d : Directions i q)
    (w : Fin 3 → List (List Word)) (xs : List (Fin 3)) :
    (xs.map (entry d w)).map Prod.fst = xs.map (atomId d) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => exact congrArg (List.cons (atomId d x)) ih

/-- Sorting the carrier rows is sorting the three positions. -/
private theorem order_entries {i : Input} {q : Site i} (d : Directions i q)
    (w : Fin 3 → List (List Word)) (inj : Function.Injective w) :
    (order Prod.snd (entries d w)).map Prod.fst = (order w slots).map (atomId d) := by
  have canon := legal_order w slots
  have lifted : Legal Prod.snd (entries d w) ((order w slots).map (entry d w)) :=
    ⟨canon.perm.map (entry d w),
      List.pairwise_map.mpr (List.pairwise_map.mpr (List.pairwise_map.mp canon.descending))⟩
  have distinct : ∀ x ∈ entries d w, ∀ y ∈ entries d w, x.2 = y.2 → x = y := by
    intro x hx y hy eqn
    obtain ⟨j,_,rfl⟩ := List.mem_map.mp (show x ∈ slots.map (entry d w) from hx)
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp (show y ∈ slots.map (entry d w) from hy)
    have same : w j = w k := eqn
    exact congrArg (entry d w) (inj same)
  have same := legal_unique distinct (legal_order Prod.snd (entries d w)) lifted
  exact (congrArg (List.map Prod.fst) same).trans (map_fst_entries d w _)

/-- Every source outcome of a trial is its deterministic value. -/
theorem read_exact {i : Input} {q : Site i} (d : Directions i q) (a : i.certified.Atom) (rev : Bool)
    (w : Fin 3 → List (List Word)) (v : Option RS) :
    Outcome d a rev w v ↔ v = readTrial d a rev w := by
  by_cases inj : Function.Injective w
  · have nd : [w 0,w 1,w 2].Nodup := (nodup_injective w).mpr inj
    have canon := legal_order w slots
    have three : (order w slots).length = 3 := canon.perm.length_eq
    obtain ⟨j,k,l,row⟩ := List.length_eq_three.mp three
    have ids : (order Prod.snd (entries d w)).map Prod.fst = [atomId d j,atomId d k,atomId d l] :=
      (order_entries d w inj).trans (congrArg (List.map (atomId d)) row)
    have value : readTrial d a rev w =
        readback? (geometry i rev) [atomId d j,atomId d k,atomId d l,a.val] := by
      unfold readTrial
      rw [if_pos nd]
      exact congrArg (fun xs => readback? (geometry i rev) (xs ++ [a.val])) ids
    have sorted : Legal w slots [j,k,l] := by
      rw [← row]
      exact canon
    rw [value]
    constructor
    · intro o
      cases o with
      | tie different same => exact (different (inj same)).elim
      | read j' k' l' _ legal sense =>
        have same := legal_unique (fun x _ y _ eqn => inj eqn) legal sorted
        simp only [List.cons.injEq, and_true] at same
        obtain ⟨rfl,rfl,rfl⟩ := same
        exact (sense_exact _ _ _ _ _ _).mp sense
    · intro eqn
      subst eqn
      exact .read j k l inj sorted ((sense_exact _ _ _ _ _ _).mpr rfl)
  · have nd : ¬ [w 0,w 1,w 2].Nodup := fun h => inj ((nodup_injective w).mp h)
    have value : readTrial d a rev w = none := by
      unfold readTrial
      rw [if_neg nd]
    rw [value]
    constructor
    · intro o
      cases o with
      | tie _ _ => rfl
      | read _ _ _ strictOrder _ _ => exact (inj strictOrder).elim
    · intro eqn
      subst eqn
      unfold Function.Injective at inj
      push_neg at inj
      obtain ⟨j,k,same,ne⟩ := inj
      exact .tie ne same

/-! ## The executable calculation in closed form

Everything below this line concerns the proof of agreement. -/

private theorem mapM_one {α β : Type} (f : α → Option β) {a : α} {x : β} (ha : f a = some x) :
    [a].mapM f = some [x] := by
  simp [List.mapM_cons,List.mapM_nil,ha]

private theorem mapM_three {α β : Type} (f : α → Option β) {a b c : α} {x y z : β}
    (ha : f a = some x) (hb : f b = some y) (hc : f c = some z) : [a,b,c].mapM f = some [x,y,z] := by
  simp [List.mapM_cons,List.mapM_nil,ha,hb,hc]

private theorem mapM_none {α β : Type} (f : α → Option β) {xs : List α} {x : α}
    (member : x ∈ xs) (lost : f x = none) : xs.mapM f = none := by
  induction xs with
  | nil => cases member
  | cons y ys ih =>
    rcases List.mem_cons.mp member with rfl | later
    · simp [List.mapM_cons,lost]
    · cases hy : f y with
      | none => simp [List.mapM_cons,hy]
      | some b => simp [List.mapM_cons,hy,ih later]

private def ligandOf (i : Input) (r : Reader i) (rev : Bool) (arm : Arm i) : Option (Ligand i) :=
  arm.occurrence.val.node.current?.bind fun atom =>
    (key? i r rev arm).bind fun priority => some ⟨arm,atom.val,priority⟩

private def markWord? (i : Input) (r : Reader i) (mark : Option Nat) (arm : Arm i) : Option Word :=
  match mark with
  | none => some []
  | some id => (RingGroupedMark.arm? i r id arm).map fun b => b.2.word

private def rowOf (i : Input) (r : Reader i) (mark : Option Nat) (x : Ligand i) :
    Option (Nat × List (List Word)) :=
  (markWord? i r mark x.arm).bind fun word => some (x.atom,trialKey x.priority word)

private def finish {i : Input} (a : i.certified.Atom) (rev : Bool)
    (rows : List (Nat × List (List Word))) : Option (Option RS) :=
  if !(rows.map Prod.snd).Nodup then some none
  else some (readback? (geometry i rev) ((order Prod.snd rows).map Prod.fst ++ [a.val]))

private def marksOf {i : Input} (xs : List (Ligand i)) : List (Option Nat) :=
  match xs with
  | [x,y,z] => if x.priority == y.priority && y.priority == z.priority then
      [some x.atom,some y.atom,some z.atom] else [none]
  | _ => []

private def trialsOf {i : Input} (r : Reader i) (a : i.certified.Atom) (rev : Bool)
    (xs : List (Ligand i)) : Option (List (Option RS)) :=
  (marksOf xs).mapM (trial? r a rev xs)

/-- The three definitional unfoldings of the executable calculation. Each
side is the same term after the `do` notation is expanded. -/
private theorem ligands_unfold (i : Input) (q : Site i) (r : Reader i) (rev : Bool) :
    ligands? i q r rev = (RingRetainedAuxiliary.frame i.certified q).mapM (ligandOf i r rev) := rfl

private theorem trial_unfold {i : Input} (r : Reader i) (a : i.certified.Atom) (rev : Bool)
    (xs : List (Ligand i)) (mark : Option Nat) :
    trial? r a rev xs mark = Option.bind (xs.mapM (rowOf i r mark)) (finish a rev) := by
  first
    | rfl
    | (cases mark <;> rfl)

private theorem hands_unfold (i : Input) (q : Site i) (r : Reader i) (a : i.certified.Atom)
    (rev : Bool) : hands? i q r a rev = Option.bind (ligands? i q r rev) (trialsOf r a rev) := rfl

private def lig {i : Input} {q : Site i} (d : Directions i q) (ks : Fin 3 → Key) (k : Fin 3) :
    Ligand i := ⟨d.arm k,atomId d k,ks k⟩

private def ligs {i : Input} {q : Site i} (d : Directions i q) (ks : Fin 3 → Key) :
    List (Ligand i) := [lig d ks 0,lig d ks 1,lig d ks 2]

private theorem ligands_eval {i : Input} {q : Site i} (d : Directions i q) (r : Reader i)
    (rev : Bool) (ks : Fin 3 → Key) (keys : ∀ k, key? i r rev (d.arm k) = some (ks k)) :
    ligands? i q r rev = some (ligs d ks) := by
  have one (k : Fin 3) : ligandOf i r rev (d.arm k) = some (lig d ks k) := by
    simp [ligandOf,d.real k,keys k,lig,atomId]
  have all : [d.arm 0,d.arm 1,d.arm 2].mapM (ligandOf i r rev) = some (ligs d ks) :=
    mapM_three (ligandOf i r rev) (one 0) (one 1) (one 2)
  rw [ligands_unfold,d.incident]
  exact all

private theorem finish_entries {i : Input} {q : Site i} (d : Directions i q) (a : i.certified.Atom)
    (rev : Bool) (w : Fin 3 → List (List Word)) :
    finish a rev (entries d w) = some (readTrial d a rev w) := by
  by_cases nd : [w 0,w 1,w 2].Nodup
  · have listed : ((entries d w).map Prod.snd).Nodup := nd
    have off : ¬ (!decide (((entries d w).map Prod.snd).Nodup)) = true := by simp [listed]
    unfold finish readTrial
    rw [if_neg off,if_pos nd]
  · have listed : ¬ ((entries d w).map Prod.snd).Nodup := nd
    have on : (!decide (((entries d w).map Prod.snd).Nodup)) = true := by simp [listed]
    unfold finish readTrial
    rw [if_pos on,if_neg nd]

private theorem trial_eval {i : Input} {q : Site i} (d : Directions i q) (r : Reader i)
    (a : i.certified.Atom) (rev : Bool) (ks : Fin 3 → Key) (mark : Option Nat) (ws : Fin 3 → Word)
    (words : ∀ k, markWord? i r mark (d.arm k) = some (ws k)) :
    trial? r a rev (ligs d ks) mark = some (readTrial d a rev fun k => trialKey (ks k) (ws k)) := by
  have row (k : Fin 3) :
      rowOf i r mark (lig d ks k) = some (entry d (fun k => trialKey (ks k) (ws k)) k) := by
    simp [rowOf,lig,words k,entry]
  have rows : (ligs d ks).mapM (rowOf i r mark) = some (entries d fun k => trialKey (ks k) (ws k)) :=
    mapM_three (rowOf i r mark) (row 0) (row 1) (row 2)
  have bound : Option.bind ((ligs d ks).mapM (rowOf i r mark)) (finish a rev) =
      finish a rev (entries d fun k => trialKey (ks k) (ws k)) :=
    congrArg (fun o => Option.bind o (finish a rev)) rows
  exact (trial_unfold r a rev (ligs d ks) mark).trans
    (bound.trans (finish_entries d a rev fun k => trialKey (ks k) (ws k)))

private theorem marks_ligs {i : Input} {q : Site i} (d : Directions i q) (ks : Fin 3 → Key) :
    marksOf (ligs d ks) = if ks 0 == ks 1 && ks 1 == ks 2 then
      [some (atomId d 0),some (atomId d 1),some (atomId d 2)] else [none] := rfl

/-- With the three ordinary keys and all mark words computed, the executable
ballot list is the deterministic value of each source trial, in order. -/
private theorem hands_eval {i : Input} {q : Site i} (d : Directions i q) (r : Reader i)
    (a : i.certified.Atom) (rev : Bool) (ks : Fin 3 → Key) (words : Option (Fin 3) → Fin 3 → Word)
    (keys : ∀ k, key? i r rev (d.arm k) = some (ks k))
    (marks : ∀ s k, markWord? i r (s.map (atomId d)) (d.arm k) = some (words s k)) :
    hands? i q r a rev = some ((trials ks).map fun s =>
      readTrial d a rev fun k => trialKey (ks k) (words s k)) := by
  have start : hands? i q r a rev = trialsOf r a rev (ligs d ks) :=
    (hands_unfold i q r a rev).trans
      (congrArg (fun o => Option.bind o (trialsOf r a rev)) (ligands_eval d r rev ks keys))
  have each (s : Option (Fin 3)) : trial? r a rev (ligs d ks) (s.map (atomId d)) =
      some (readTrial d a rev fun k => trialKey (ks k) (words s k)) :=
    trial_eval d r a rev ks (s.map (atomId d)) (words s) (marks s)
  refine start.trans ?_
  show (marksOf (ligs d ks)).mapM (trial? r a rev (ligs d ks)) = _
  by_cases tied : ks 0 = ks 1 ∧ ks 1 = ks 2
  · have cond : (ks 0 == ks 1 && ks 1 == ks 2) = true := by
      rw [Bool.and_eq_true]
      exact ⟨beq_iff_eq.mpr tied.1,beq_iff_eq.mpr tied.2⟩
    have ms : marksOf (ligs d ks) = [some (atomId d 0),some (atomId d 1),some (atomId d 2)] := by
      rw [marks_ligs d ks,if_pos cond]
    have ts : trials ks = [some 0,some 1,some 2] := by
      unfold trials
      rw [if_pos tied]
    rw [ms,ts]
    exact mapM_three (trial? r a rev (ligs d ks)) (each (some 0)) (each (some 1)) (each (some 2))
  · have cond : ¬ (ks 0 == ks 1 && ks 1 == ks 2) = true := by
      intro h
      rw [Bool.and_eq_true] at h
      exact tied ⟨beq_iff_eq.mp h.1,beq_iff_eq.mp h.2⟩
    have ms : marksOf (ligs d ks) = [none] := by
      rw [marks_ligs d ks,if_neg cond]
    have ts : trials ks = [none] := by
      unfold trials
      rw [if_neg tied]
    rw [ms,ts]
    exact mapM_one (trial? r a rev (ligs d ks)) (each none)

/-! ## Mark words -/

/-- On a ready reader every trial has exactly one admissible family of mark
words, and it is the family the executable trial reads. -/
private theorem mark_exact {i : Input} {q : Site i} {r : Reader i} (d : Directions i q)
    (ready : RingGroupedStereo.Ready q r) (rev : Bool) (s : Option (Fin 3)) :
    ∃ ws : Fin 3 → Word, (∀ k, markWord? i r (s.map (atomId d)) (d.arm k) = some (ws k)) ∧
      ∀ other, MarkWords d r rev s other ↔ other = ws := by
  cases s with
  | none =>
    exact ⟨fun _ => [],fun _ => rfl,fun _ => ⟨fun h => funext h,fun h k => congrFun h k⟩⟩
  | some s =>
    have each (k : Fin 3) := RingGroupedMark.arm_ready ready (atomId d s) (d.arm k) (d.valid k) (d.rooted k)
    choose e computed using each
    have src (k : Fin 3) : RingGroupedMark.OnGeometry i r rev (atomId d s) (d.arm k) (e k).2 := by
      cases rev
      · exact (RingGroupedMark.arm_source (computed k)).2
      · exact RingGroupedMark.OnGeometry.reflect (RingGroupedMark.arm_source (computed k)).2
    refine ⟨fun k => (e k).2.word,
      fun k => congrArg (Option.map fun b : RingGroupedMark.Entry => b.2.word) (computed k),
      fun other => ⟨?_,?_⟩⟩
    · intro h
      funext k
      obtain ⟨b,hb,eqn⟩ := h k
      exact eqn.trans (congrArg RingStereoSiblingPass.Branch.word (hb.unique (src k)))
    · intro eqn k
      subst eqn
      exact ⟨_,src k,rfl⟩

/-! ## Ballots of one geometry -/

private theorem column {α β : Type} {P : α → β → Prop} (g : α → β) {xs : List α} {hs : List β}
    (rel : List.Forall₂ P xs hs) (only : ∀ s w, P s w → w = g s) : hs = xs.map g := by
  induction rel with
  | nil => rfl
  | cons head _ ih => exact congrArg₂ List.cons (only _ _ head) ih

private theorem rows {α β : Type} {P : α → β → Prop} (g : α → β) (xs : List α)
    (all : ∀ s, P s (g s)) : List.Forall₂ P xs (xs.map g) := by
  induction xs with
  | nil => exact .nil
  | cons x xs ih =>
    show List.Forall₂ P (x :: xs) (g x :: xs.map g)
    exact .cons (all x) ih

/-- On a ready reader the source judgments of one geometry determine the
three ordinary keys and the complete ballot list. Both are the values read
by the executable calculation. -/
theorem ballots_exact {i : Input} {q : Site i} {r : Reader i} (d : Directions i q)
    (ready : RingGroupedStereo.Ready q r) (a : i.certified.Atom) (rev : Bool) :
    ∃ (ks : Fin 3 → Key) (hands : List (Option RS)), hands? i q r a rev = some hands ∧
      ∀ k hs, Ballots d r a rev k hs ↔ k = ks ∧ hs = hands := by
  have each (k : Fin 3) :=
    RingFullPathEligibility.key_exact ready rev (d.arm k) (d.valid k) (d.rooted k)
  choose ks got onlyKey using each
  choose words computed onlyWords using mark_exact d ready rev
  refine ⟨ks,_,hands_eval d r a rev ks words got computed,?_⟩
  intro k hs
  constructor
  · rintro ⟨reads,all⟩
    have sameKeys : k = ks := funext fun j => (onlyKey j _).mp (reads j)
    subst sameKeys
    refine ⟨rfl,column _ all ?_⟩
    rintro s w ⟨ws,marked,seen⟩
    have sameWords : ws = words s := (onlyWords s ws).mp marked
    subst sameWords
    exact (read_exact d a rev _ w).mp seen
  · rintro ⟨sameKeys,sameHands⟩
    subst sameKeys
    subst sameHands
    refine ⟨fun j => (onlyKey j _).mpr rfl,rows _ _ fun s => ?_⟩
    exact ⟨words s,(onlyWords s _).mpr rfl,(read_exact d a rev _ _).mpr rfl⟩

/-! ## Agreement with the publication -/

private theorem labels_framed {i : Input} {q : Site i} {r : Reader i} {a : i.certified.Atom}
    (shape : (RingRetainedAuxiliary.frame i.certified q).length = 3) {hs ms : List (Option RS)}
    (actual : hands? i q r a false = some hs) (reflected : hands? i q r a true = some ms) :
    pLabels i q r a = crossed hs ms := by
  unfold RingPyramidalPublication.pLabels
  simp [shape,guard,actual,reflected]

/-- Without three real incident directions the publication is absent. This
needs no hypothesis on the reader. -/
theorem unframed_labels {i : Input} (q : Site i) (r : Reader i) (a : i.certified.Atom)
    (unframed : ¬ Nonempty (Directions i q)) : pLabels i q r a = none := by
  by_cases shape : (RingRetainedAuxiliary.frame i.certified q).length = 3
  · obtain ⟨t,member,missing⟩ : ∃ t : Arm i, t ∈ RingRetainedAuxiliary.frame i.certified q ∧
        t.occurrence.val.node.current? = none := by
      by_contra all
      push_neg at all
      exact unframed (directions_of shape all)
    have gone : ligands? i q r false = none := by
      rw [ligands_unfold]
      exact mapM_none (ligandOf i r false) member (by simp [ligandOf,missing])
    have lost : hands? i q r a false = none :=
      (hands_unfold i q r a false).trans
        (congrArg (fun o => Option.bind o (trialsOf r a false)) gone)
    unfold RingPyramidalPublication.pLabels
    simp [shape,guard,lost]
  · simp [RingPyramidalPublication.pLabels,shape,guard]

/-- Read both ballot populations of a framed phosphorus on a ready reader.
The source judgments determine the keys and ballots of each geometry, and
the publication is the crossed pair of their surviving hands. -/
theorem framed_labels {i : Input} {q : Site i} {r : Reader i} (d : Directions i q)
    (ready : RingGroupedStereo.Ready q r) (a : i.certified.Atom) :
    ∃ (x y : Fin 3 → Key) (hs ms : List (Option RS)),
      (∀ k h, Ballots d r a false k h ↔ k = x ∧ h = hs) ∧
      (∀ k h, Ballots d r a true k h ↔ k = y ∧ h = ms) ∧
      pLabels i q r a = crossed hs ms := by
  obtain ⟨x,hs,hx,ex⟩ := ballots_exact d ready a false
  obtain ⟨y,ms,hy,ey⟩ := ballots_exact d ready a true
  exact ⟨x,y,hs,ms,ex,ey,labels_framed d.three hx hy⟩

/-- With three real directions the absent case of the source is excluded. -/
theorem framed_iff {i : Input} {q : Site i} {r : Reader i} (d : Directions i q)
    (a : i.certified.Atom) (v : Option Labels) :
    Source i q r a v ↔ ∃ (x y : Fin 3 → Key) (hs ms : List (Option RS)),
      Ballots d r a false x hs ∧ Ballots d r a true y ms ∧ v = crossed hs ms := by
  constructor
  · intro src
    cases src with
    | absent unframed => exact (unframed ⟨d⟩).elim
    | centre d' original mirrored =>
      have same : d' = d := Directions.unique d' d
      subst same
      exact ⟨_,_,_,_,original,mirrored,rfl⟩
  · rintro ⟨x,y,hs,ms,original,mirrored,eqn⟩
    subst eqn
    exact .centre d original mirrored

/-- **Equivalence theorem.** On every ready reader the independent source
relation holds of exactly the value computed by the phosphorus publication.
No frame hypothesis is needed: an occurrence without three real incident
directions is absent on both sides. -/
theorem source_iff {i : Input} {q : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready q r)
    (a : i.certified.Atom) (v : Option Labels) : Source i q r a v ↔ pLabels i q r a = v := by
  by_cases framed : Nonempty (Directions i q)
  · obtain ⟨d⟩ := framed
    obtain ⟨x,y,hs,ms,ex,ey,value⟩ := framed_labels d ready a
    rw [value,framed_iff d a v]
    constructor
    · rintro ⟨x',y',hs',ms',original,mirrored,eqn⟩
      obtain ⟨_,sameActual⟩ := (ex _ _).mp original
      obtain ⟨_,sameReflected⟩ := (ey _ _).mp mirrored
      rw [eqn,sameActual,sameReflected]
    · intro eqn
      exact ⟨x,y,hs,ms,(ex _ _).mpr ⟨rfl,rfl⟩,(ey _ _).mpr ⟨rfl,rfl⟩,eqn.symm⟩
  · rw [unframed_labels q r a framed]
    constructor
    · intro src
      cases src with
      | absent _ => rfl
      | centre d _ _ => exact (framed ⟨d⟩).elim
    · intro eqn
      subst eqn
      exact .absent framed

/-- Existence and uniqueness of the source value, in the form of the
tetrahedral `RingFullPathPublication.source_exact`. -/
theorem source_exact {i : Input} {q : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready q r)
    (a : i.certified.Atom) : ∃ v, pLabels i q r a = v ∧ ∀ w, Source i q r a w ↔ w = v :=
  ⟨_,rfl,fun w => (source_iff ready a w).trans eq_comm⟩

theorem source_unique {i : Input} {q : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready q r)
    (a : i.certified.Atom) {v w : Option Labels} (left : Source i q r a v) (right : Source i q r a w) :
    v = w :=
  ((source_iff ready a v).mp left).symm.trans ((source_iff ready a w).mp right)

theorem source_total {i : Input} {q : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready q r)
    (a : i.certified.Atom) : ∃ v, Source i q r a v :=
  ⟨_,(source_iff ready a _).mpr rfl⟩

/-- Every selected phosphorus has an inhabited three-neighbor source frame.
Consequently every published refusal there also has two actual ballot lists. -/
theorem selected_framed {i : Input} {q : Site i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a) : Nonempty (Directions i q) := by
  obtain ⟨bij,atoms,three⟩ := RingPyramidalPublication.focusP_neighbors selected
  apply directions_of three
  intro t ht
  rw [atoms ⟨t,ht⟩]
  simp

def Framed (i : Input) (q : Site i) (r : Reader i) (a : i.certified.Atom) (v : Option Labels) : Prop :=
  ∃ (d : Directions i q) (x y : Fin 3 → Key) (hs ms : List (Option RS)),
    Ballots d r a false x hs ∧ Ballots d r a true y ms ∧ v = crossed hs ms

theorem selected_iff {i : Input} {q : Site i} {r : Reader i} {a : i.certified.Atom}
    (selected : RingPyramidalPublication.focusP i q = some a) (ready : RingGroupedStereo.Ready q r)
    (v : Option Labels) : Framed i q r a v ↔ pLabels i q r a = v := by
  rw [← source_iff ready a v]
  constructor
  · rintro ⟨d,x,y,hs,ms,hx,hy,h⟩
    exact (framed_iff d a v).mpr ⟨x,y,hs,ms,hx,hy,h⟩
  · intro h
    obtain ⟨d⟩ := selected_framed selected
    exact ⟨d,(framed_iff d a v).mp h⟩

end TetraStereo.Engine.RingPyramidalSource
assert_kernel_only TetraStereo.Engine.RingPyramidalSource.sense_exact
assert_kernel_only TetraStereo.Engine.RingPyramidalSource.read_exact
assert_kernel_only TetraStereo.Engine.RingPyramidalSource.ballots_exact
assert_kernel_only TetraStereo.Engine.RingPyramidalSource.source_iff
assert_kernel_only TetraStereo.Engine.RingPyramidalSource.selected_iff
