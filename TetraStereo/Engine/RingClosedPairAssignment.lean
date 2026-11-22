import TetraStereo.Engine.RingClosedPairGroup
import TetraStereo.Engine.RingMolecularSchedule

set_option autoImplicit false
namespace TetraStereo.Engine.RingClosedPairAssignment
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Site)
open RingActivePairReport (Matrix Ranking Slot)
open RingNestedActivePair (Frame Labels Reader)

/-- Consume one fixed deeper publication state and issue all non-diagonal
comparisons, including both directions of every closed mixed pair. -/
def source {i f} (fr : Frame i f) (read : Reader i) (a b : Slot) :=
  RingClosedPairGroup.score? i f (fr.arm a).occurrence (fr.arm b).occurrence read

structure Assignment (i : Input) (f : Site i) (read : Reader i) where
  frame : Frame i f
  matrix : Matrix (source frame read)
  actual : Ranking matrix false
  reflected : Ranking matrix true
  hand : RS
  mirrorHand : RS
  physical : readback? (inputGeometry i.certified) (frame.atoms actual.slots) = some hand
  mirrorPhysical : readback? (mirror (inputGeometry i.certified)) (frame.atoms reflected.slots) = some mirrorHand

def fromReader? (i : Input) (f : Site i) (read : Reader i) : Option (Assignment i f read) := do
  let fr ← RingNestedActivePair.frame? i f
  let m ← RingActivePairReport.matrix? (source fr read)
  let a ← RingActivePairReport.rank? m false
  let b ← RingActivePairReport.rank? m true
  let ⟨h,hh⟩ ← (readback? (inputGeometry i.certified) (fr.atoms a.slots)).attach
  let ⟨k,hk⟩ ← (readback? (mirror (inputGeometry i.certified)) (fr.atoms b.slots)).attach
  return ⟨fr,m,a,b,h,k,hh,hk⟩

def frozen (i : Input) (f : Site i) : Reader i := RingNestedActivePair.masked f
  (RingActiveDistanceSchedule.snapshot (RingMolecularSchedule.publicationTable i f.val.root))

def assign? (i : Input) (f : Site i) := fromReader? i f (frozen i f)

def Assignment.labels {i f read} (a : Assignment i f read) : Labels :=
  (RingNestedActivePair.label a.hand a.mirrorHand,RingNestedActivePair.label a.mirrorHand a.hand)

theorem Assignment.edge {i f read} (a : Assignment i f read) (u v : Slot) (h : u ≠ v) :
    RingNestedActivePair.Edge i f (a.frame.arm u).occurrence (a.frame.arm v).occurrence read (a.matrix.get u v) ∨
    ∃ c : RingClosedPairGroup.Certificate i f (a.frame.arm u).occurrence (a.frame.arm v).occurrence read,
      c.score = a.matrix.get u v := RingClosedPairGroup.issued (a.matrix.found u v h)

/-- A visible publication used by this public evaluation has a finite
molecular derivation in the same original-root history. -/
theorem frozen_source {i f q v} (on : RingNestedActivePair.Eligible (i := i) f q)
    (hit : frozen i f q = some v) : RingMolecularSchedule.Derivation i q v := by
  rw [frozen,RingMolecularSchedule.table_readback] at hit
  have found : RingMolecularSchedule.atRoot i f.val.root q = some v := by
    simpa [RingNestedActivePair.masked,on,on.1] using hit
  exact RingMolecularSchedule.derivation q on.1 found

open RingActiveDistanceSchedule

/-- Only an unresolved cell tries the additional molecular edge theorem. Each
step reads the same original-root publication state frozen for this distance. -/
def publish? (i : Input) (q : Site i) (s : View i) : Option (Option Labels) :=
  (RingNestedActivePair.publish? i q s).orElse fun _ =>
    (fromReader? i q (RingNestedActivePair.masked q s)).map (some ∘ Assignment.labels)

private theorem publish_congr (i : Input) (q : Site i) {a b : View i}
    (agree : ∀ t, RingNestedActivePair.Eligible q t → a t = b t) :
    publish? i q a = publish? i q b := by
  unfold publish?
  rw [RingNestedActivePair.publish_congr i q agree,RingNestedActivePair.masked_congr q agree]

private def onRoot (i : Input) (root : i.certified.Atom) : Rule i := fun q s =>
  if q.val.root = root then publish? i q s else none

def atRoot (i : Input) (root : i.certified.Atom) := evaluate (onRoot i root)
def publicationTable (i : Input) (root : i.certified.Atom) : Table i :=
  table (onRoot i root) (height i+1)

theorem table_readback (i : Input) (root : i.certified.Atom) :
    snapshot (publicationTable i root) = atRoot i root := snapshot_table ..

theorem atRoot_eq {i : Input} {root : i.certified.Atom} {q : Site i} (on : q.val.root = root) :
    atRoot i root q = publish? i q (atRoot i root) := by
  change evaluate (onRoot i root) q = _
  rw [evaluate_eq]
  simp only [onRoot,on,if_true]
  apply publish_congr
  intro t vis
  simp [RingActiveDistanceSchedule.frozen,vis.1,vis.2.1,vis.2.2,distance,atRoot]

/-- The old cell's exact publication/refusal or the new full signed frame
is retained with strictly deeper derivations for every visible known cell. -/
inductive Derivation (i : Input) : Site i → Option Labels → Prop where
  | existing {q v} (s : View i) (issued : RingNestedActivePair.publish? i q s = some v)
      (deeper : ∀ t w, Visible q t → s t = some w → Derivation i t w) : Derivation i q v
  | group {q} (s : View i) (a : Assignment i q (RingNestedActivePair.masked q s))
      (issued : fromReader? i q (RingNestedActivePair.masked q s) = some a)
      (deeper : ∀ t w, Visible q t → s t = some w → Derivation i t w) :
      Derivation i q (some a.labels)

theorem derivation {i : Input} {root : i.certified.Atom} (q : Site i)
    (on : q.val.root = root) {v} (found : atRoot i root q = some v) : Derivation i q v := by
  suffices done : ∀ n (q : Site i), height i - distance q = n → q.val.root = root →
      ∀ v, atRoot i root q = some v → Derivation i q v from done _ q rfl on _ found
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q eqn on v hit
    have deeper (t : Site i) (w) (vis : Visible q t) (seen : atRoot i root t = some w) : Derivation i t w := by
      have upper := distance_bound t
      have lt := vis.2.1
      exact ih _ (by omega) t rfl (vis.1.trans on) w seen
    rw [atRoot_eq on] at hit
    cases old : RingNestedActivePair.publish? i q (atRoot i root) with
    | some val =>
      have eqv : val = v := Option.some.inj (by simpa [publish?,old] using hit)
      exact eqv ▸ Derivation.existing _ old deeper
    | none =>
      obtain ⟨a,ha,hv⟩ := Option.map_eq_some_iff.mp
        (by simpa [publish?,old] using hit :
         (fromReader? i q (RingNestedActivePair.masked q (atRoot i root))).map (some ∘ Assignment.labels) = some v)
      exact hv ▸ Derivation.group _ a ha deeper

end TetraStereo.Engine.RingClosedPairAssignment
assert_kernel_only TetraStereo.Engine.RingClosedPairAssignment.Assignment.edge
assert_kernel_only TetraStereo.Engine.RingClosedPairAssignment.frozen_source
assert_kernel_only TetraStereo.Engine.RingClosedPairAssignment.assign?
assert_kernel_only TetraStereo.Engine.RingClosedPairAssignment.derivation
assert_kernel_only TetraStereo.Engine.RingClosedPairAssignment.table_readback
