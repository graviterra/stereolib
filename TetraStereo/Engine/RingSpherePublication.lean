import TetraStereo.Engine.RingSphereMagnitude
import TetraStereo.Engine.RingClosedGroupTie

set_option autoImplicit false

namespace TetraStereo.Engine.RingSpherePublication
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingNestedActivePair (Frame Reader Labels masked)
open RingActivePairReport (Matrix Ranking)
open LocalizedChemicalRingPhysicalSense (inputGeometry)

/-- The complete matrix refers to the same original occurrence and the
same frozen state for all twelve directed comparisons. -/
def edges {i f} (fr : Frame i f) (read : Reader i) : RingActivePairReport.Reader :=
  fun x y => RingSpherePriority.edge? i f (fr.arm x).occurrence (fr.arm y).occurrence read

structure Ranked {i f} (fr : Frame i f) {read : Reader i} (m : Matrix (edges fr read)) where
  actual : Ranking m false
  reflected : Ranking m true
  hand : RS
  mirrorHand : RS
  physical : readback? (inputGeometry i.certified) (fr.atoms actual.slots) = some hand
  mirrorPhysical : readback? (mirror (inputGeometry i.certified)) (fr.atoms reflected.slots) = some mirrorHand

def Ranked.labels {i f fr read m} (r : @Ranked i f fr read m) : Labels :=
  (RingNestedActivePair.label r.hand r.mirrorHand,RingNestedActivePair.label r.mirrorHand r.hand)

theorem Ranked.casing {i f fr read m} (r : @Ranked i f fr read m) :
    r.labels.1 = if RingActivePairReport.reversals m % 2 = 0 then .chiral r.hand
      else .pseudoasymmetric (pseudoRSOfRS r.hand) :=
  fr.label_by_reversals r.actual r.reflected r.physical r.mirrorPhysical

/-- Count the six actual molecular magnitudes. A score of magnitude two
changes the relative rank on reflection; its parity determines casing. -/
theorem Ranked.casing_by_magnitude {i f fr read m} (r : @Ranked i f fr read m) :
    r.labels.1 = if RingActivePairReport.doubled m % 2 = 0 then .chiral r.hand
      else .pseudoasymmetric (pseudoRSOfRS r.hand) := by
  have equal : RingActivePairReport.reversals m = RingActivePairReport.doubled m := by
    apply (List.Perm.refl _).countP_congr
    intro p mem
    have value := RingSpherePriority.edge_values (m.found p.1 p.2
      (ne_of_lt ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp mem)))
    let s := m.get p.1 p.2
    change s ∈ RingActivePairs.molecularValues at value
    change (decide (0 < s.1) != decide (0 < s.2)) = (s.1.natAbs == 2)
    simp only [RingActivePairs.molecularValues,List.mem_cons,List.not_mem_nil,or_false] at value
    rcases value with h | h | h | h | h <;> rw [h] <;> decide
  rw [← equal]
  exact r.casing

private def ranked? {i f} (fr : Frame i f) {read : Reader i} (m : Matrix (edges fr read)) : Option (Ranked fr m) := do
  let a ← RingActivePairReport.rank? m false
  let b ← RingActivePairReport.rank? m true
  let ⟨h,hp⟩ ← (readback? (inputGeometry i.certified) (fr.atoms a.slots)).attach
  let ⟨k,kp⟩ ← (readback? (mirror (inputGeometry i.certified)) (fr.atoms b.slots)).attach
  return ⟨a,b,h,k,hp,kp⟩

inductive Decision (i : Input) (f : Site i) (read : Reader i) : Option Labels → Type where
  | prior {v} (issued : RingClosedGroupTie.publish? i f read = some v) : Decision i f read v
  | ranked (fr : Frame i f) (m : Matrix (edges fr (masked f read))) (r : Ranked fr m) :
      Decision i f read (some r.labels)
  | refused (fr : Frame i f) (m : Matrix (edges fr (masked f read))) (r : RingOrdinaryPairRefusal.Certificate m) :
      Decision i f read none

private def extra? (i : Input) (f : Site i) (read : Reader i) :
    Option ((v : Option Labels) × Decision i f read v) := do
  let fr ← RingNestedActivePair.frame? i f
  let m ← RingActivePairReport.matrix? (edges fr (masked f read))
  if let some r := ranked? fr m then return ⟨some r.labels,.ranked fr m r⟩
  let r ← RingOrdinaryPairRefusal.find? m
  return ⟨none,.refused fr m r⟩

def certify? (i : Input) (f : Site i) (read : Reader i) : Option ((v : Option Labels) × Decision i f read v) :=
  match h : RingClosedGroupTie.publish? i f read with
  | some v => some ⟨v,.prior h⟩
  | none => extra? i f read

def publish? (i : Input) (f : Site i) (read : Reader i) := (certify? i f read).map Sigma.fst

theorem preserves {i f read v} (found : RingClosedGroupTie.publish? i f read = some v) :
    publish? i f read = some v := by
  unfold publish? certify?
  split <;> rename_i heq
  · simp only [Option.map_some]; exact heq.symm.trans found
  · exact nomatch heq.symm.trans found

/-- A certified ordinary tie fills a previously unresolved publication. The
single tied pair precludes success of the ranked branch on either geometry. -/
theorem publish_of_ordinary {i f read} {fr : Frame i f} {m : Matrix (edges fr (masked f read))}
    {c : RingOrdinaryPairRefusal.Certificate m}
    (previous : RingClosedGroupTie.publish? i f read = none)
    (frame : RingNestedActivePair.frame? i f = some fr)
    (matrix : RingActivePairReport.matrix? (edges fr (masked f read)) = some m)
    (found : RingOrdinaryPairRefusal.find? m = some c) : publish? i f read = some none := by
  have noRank : ranked? fr m = none := by
    cases h : ranked? fr m with
    | none => rfl
    | some r => exact False.elim (c.no_ranking false ⟨r.actual⟩)
  unfold publish? certify?
  split <;> rename_i h
  · exact nomatch h.symm.trans previous
  · simp only [extra?,frame,Option.bind_eq_bind,Option.bind_some,matrix,noRank,found,
      Option.pure_def,Option.map_some]

theorem issued {i f read v} (found : publish? i f read = some v) : Nonempty (Decision i f read v) := by
  obtain ⟨⟨w,d⟩,_,rfl⟩ := Option.map_eq_some_iff.mp found
  exact ⟨d⟩

open RingActiveDistanceSchedule (Rule View frozen evaluate distance height Visible)

private def rule (i : Input) (root : i.certified.Atom) : Rule i := fun q read =>
  if q.val.root = root then publish? i q read else none

/-- Feed each newly certified result into the next shallower distance batch
on its original carrier. Unknown cells remain explicit throughout the pass. -/
def atRoot (i : Input) (root : i.certified.Atom) := evaluate (rule i root)

/-- Materialize once when several original addresses will be queried. -/
def publicationTable (i : Input) (root : i.certified.Atom) : RingActiveDistanceSchedule.Table i :=
  RingActiveDistanceSchedule.table (rule i root) (height i + 1)

theorem table_readback (i : Input) (root : i.certified.Atom) :
    RingActiveDistanceSchedule.snapshot (publicationTable i root) = atRoot i root :=
  RingActiveDistanceSchedule.snapshot_table ..

theorem atRoot_eq {i root} {q : Site i} (on : q.val.root = root) :
    atRoot i root q = publish? i q (frozen (atRoot i root) q) := by
  change evaluate (rule i root) q = _
  rw [RingActiveDistanceSchedule.evaluate_eq]
  simp only [rule,on,if_true,atRoot]

/-- Every published label and every certified absence has a finite derivation.
For a visible occurrence the reader in the local certificate is tied exactly
to its deeper derivation. -/
inductive Derivation (i : Input) : Site i → Option Labels → Prop where
  | step {q v} (read : Reader i) (issued : Decision i q read v)
      (earlier : ∀ t w, Visible q t → read t = some w → Derivation i t w) : Derivation i q v

theorem derivation {i : Input} {root : i.certified.Atom} {q : Site i} {v}
    (on : q.val.root = root) (hit : atRoot i root q = some v) : Derivation i q v := by
  suffices h : ∀ n (t : Site i), height i - distance t = n → t.val.root = root →
      ∀ w, atRoot i root t = some w → Derivation i t w from h _ q rfl on v hit
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t depth on w seen
    rw [atRoot_eq on] at seen
    obtain ⟨d⟩ := issued seen
    apply Derivation.step _ d
    intro s z vis earlier
    have observed : atRoot i root s = some z := by simpa [frozen,vis.1,vis.2.1,vis.2.2] using earlier
    have upper := RingActiveDistanceSchedule.distance_bound s
    have deeper := vis.2.1
    exact ih _ (by omega) s rfl (vis.1.trans on) z observed

end TetraStereo.Engine.RingSpherePublication

assert_kernel_only TetraStereo.Engine.RingSpherePublication.Ranked.casing
assert_kernel_only TetraStereo.Engine.RingSpherePublication.preserves
assert_kernel_only TetraStereo.Engine.RingSpherePublication.issued
assert_kernel_only TetraStereo.Engine.RingSpherePublication.atRoot_eq
assert_kernel_only TetraStereo.Engine.RingSpherePublication.derivation

assert_kernel_only TetraStereo.Engine.RingSpherePublication.Ranked.casing_by_magnitude
assert_kernel_only TetraStereo.Engine.RingSpherePublication.table_readback
assert_kernel_only TetraStereo.Engine.RingSpherePublication.publish_of_ordinary
