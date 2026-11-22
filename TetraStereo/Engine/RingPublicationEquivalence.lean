import TetraStereo.Engine.RingJointObservations
import TetraStereo.Engine.RingActiveDistanceSchedule

set_option autoImplicit false

namespace TetraStereo.Engine.RingPublicationEquivalence
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Rule View Cell frozen evaluate)
open RingJointObservations (Joint physical canonicalFrame)
open RingActivePairReport (changes)

/-- Agreement of the two local policies is tested on the original occurrences and the
frozen state attained by the first evaluation alone. -/
theorem evaluate_eq_iff {i : Input} (a b : Rule i) : evaluate a = evaluate b ↔
    ∀ q, a q (frozen (evaluate a) q) = b q (frozen (evaluate a) q) := by
  constructor
  · intro same q
    calc
      _ = evaluate a q := (RingActiveDistanceSchedule.evaluate_eq a q).symm
      _ = evaluate b q := congrFun same q
      _ = b q (frozen (evaluate b) q) := RingActiveDistanceSchedule.evaluate_eq b q
      _ = _ := by rw [same]
  · intro localAgreement
    exact RingActiveDistanceSchedule.unique b (evaluate a) fun q =>
      (RingActiveDistanceSchedule.evaluate_eq a q).trans (localAgreement q)



private theorem frozen_of_visible {i : Input} {a b : View i} (q : Site i)
    (agree : ∀ t, RingActiveDistanceSchedule.Visible q t → a t = b t) : frozen a q = frozen b q := by
  funext t
  unfold frozen
  split_ifs with other earlier
  · rfl
  · exact agree t ⟨not_ne_iff.mp other,earlier⟩
  · rfl

/-- A genuine discrepancy has a same-root witness whose deeper visible rows agree under
both policies. Both implementations encounter literally the same input snapshot there.
Differences caused by an earlier propagated publication can thus be traced to a local
cause without assuming coverage or ranks at every address. -/
theorem divergence_frontier {i : Input} (a b : Rule i) (q : Site i) (diff : evaluate a q ≠ evaluate b q) :
    ∃ t, (t = q ∨ RingActiveDistanceSchedule.Visible q t) ∧
      (∀ d, RingActiveDistanceSchedule.Visible t d → evaluate a d = evaluate b d) ∧
      frozen (evaluate a) t = frozen (evaluate b) t ∧
      a t (frozen (evaluate a) t) ≠ b t (frozen (evaluate a) t) := by
  suffices descent : ∀ n (u : Site i), RingActiveDistanceSchedule.height i - RingActiveDistanceSchedule.distance u = n →
      evaluate a u ≠ evaluate b u → ∃ t, (t = u ∨ RingActiveDistanceSchedule.Visible u t) ∧
      (∀ d, RingActiveDistanceSchedule.Visible t d → evaluate a d = evaluate b d) ∧
      frozen (evaluate a) t = frozen (evaluate b) t ∧
      a t (frozen (evaluate a) t) ≠ b t (frozen (evaluate a) t) from descent _ q rfl diff
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro u grade different
    classical
    by_cases same : ∀ d, RingActiveDistanceSchedule.Visible u d → evaluate a d = evaluate b d
    · have snapshot := frozen_of_visible u same
      refine ⟨u,Or.inl rfl,same,snapshot,?_⟩
      intro equal
      exact different ((RingActiveDistanceSchedule.evaluate_eq a u).trans
        (equal.trans ((congrArg (b u) snapshot).trans (RingActiveDistanceSchedule.evaluate_eq b u).symm)))
    · push_neg at same
      obtain ⟨d,vis,bad⟩ := same
      have lower := vis.2.1
      have upper := RingActiveDistanceSchedule.distance_bound d
      obtain ⟨t,relation,rest⟩ := ih _ (by omega) d rfl bad
      rcases relation with rfl | deeper
      · exact ⟨_,Or.inr vis,rest⟩
      · exact ⟨_,Or.inr (vis.trans deeper),rest⟩

private theorem unwritten {i : Input} (r : Rule i) : ∀ k (q : Site i),
    RingActiveDistanceSchedule.distance q + k ≤ RingActiveDistanceSchedule.height i →
    RingActiveDistanceSchedule.pass r k q = none
  | 0,_,_ => rfl
  | k+1,q,bound => by
    rw [RingActiveDistanceSchedule.pass,RingActiveDistanceSchedule.batch_at,if_neg (by omega)]
    exact unwritten r k q (by omega)

private theorem all_passes {i : Input} {a b : Rule i} (same : evaluate a = evaluate b)
    (k : Nat) (limit : k ≤ RingActiveDistanceSchedule.height i + 1) :
    RingActiveDistanceSchedule.pass a k = RingActiveDistanceSchedule.pass b k := by
  funext q
  by_cases complete : RingActiveDistanceSchedule.height i < RingActiveDistanceSchedule.distance q + k
  · exact (RingActiveDistanceSchedule.pass_stable a limit (Nat.le_refl _) q complete).symm.trans
      ((congrFun same q).trans (RingActiveDistanceSchedule.pass_stable b limit (Nat.le_refl _) q complete))
  · rw [unwritten a k q (by omega),unwritten b k q (by omega)]

/-- The same condition recovers the literal rows of every intermediate materialized
table, including sites that remained unresolved and all certified absences. -/
theorem tables_eq_iff {i : Input} (a b : Rule i) :
    (∀ k, k ≤ RingActiveDistanceSchedule.height i + 1 →
      RingActiveDistanceSchedule.table a k = RingActiveDistanceSchedule.table b k) ↔
    ∀ q, a q (frozen (evaluate a) q) = b q (frozen (evaluate a) q) := by
  rw [← evaluate_eq_iff]
  constructor
  · intro tables
    apply (RingActiveDistanceSchedule.snapshot_table a _).symm.trans
    exact (congrArg RingActiveDistanceSchedule.snapshot (tables _ (Nat.le_refl _))).trans
      (RingActiveDistanceSchedule.snapshot_table b _)
  · intro same k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro bound
      simp only [RingActiveDistanceSchedule.table]
      apply congrArg₂ List.append _ (ih (by omega))
      apply List.map_congr_left
      intro q mem
      have atDepth : RingActiveDistanceSchedule.distance q = RingActiveDistanceSchedule.height i - k :=
        beq_iff_eq.mp (List.mem_filter.mp mem).2
      have nxt := congrFun (all_passes same (k+1) bound) q
      simp only [RingActiveDistanceSchedule.pass,RingActiveDistanceSchedule.batch_at,if_pos atDepth] at nxt
      simp only [RingActiveDistanceSchedule.snapshot_table]
      exact congrArg (Prod.mk q) nxt

/-- A chronological program may carry a scalar across rows at the same distance.
The caller supplies a total addressed record of its exact operational output, including
explicit missing evidence at each unexecuted occurrence. -/
theorem chronology_iff {i : Input} {H : Type} (output : View i) (hist : Site i → H)
    (observed : Site i → H → Cell) (recorded : ∀ q, output q = observed q (hist q))
    (b : Rule i) : output = evaluate b ↔ ∀ q, observed q (hist q) = b q (frozen output q) := by
  constructor
  · intro same q
    rw [← recorded q, same]
    exact RingActiveDistanceSchedule.evaluate_eq b q
  · intro checked
    exact RingActiveDistanceSchedule.unique b output fun q => (recorded q).trans (checked q)


/-- Unexecuted original occurrences can be represented by missing history. They then
contribute the explicit unresolved cell, never a proved refusal. -/
theorem partial_chronology_iff {i : Input} {H : Type} (output : View i) (hist : Site i → Option H)
    (observed : Site i → H → Cell) (recorded : ∀ q, output q = (hist q).bind (observed q))
    (b : Rule i) : output = evaluate b ↔ ∀ q, (hist q).bind (observed q) = b q (frozen output q) :=
  chronology_iff output hist (fun q event => event.bind (observed q)) recorded b

def reflectLabel : LocalizedAuxiliaryLabel → LocalizedAuxiliaryLabel
  | .chiral s => .chiral s.swap
  | .pseudoasymmetric pseudo => .pseudoasymmetric pseudo

theorem reflected_geometry (a b : Option RS) :
    caseFromMirror? b a = (caseFromMirror? a b).map reflectLabel := by
  rcases a with _ | (_ | _) <;> rcases b with _ | (_ | _) <;> rfl

def paired (s : Option LocalizedAuxiliaryLabel) : Cell :=
  s.map fun v => some (v,reflectLabel v)

private theorem paired_injective : Function.Injective paired := by
  intro a b eqn
  cases a <;> cases b <;> simp_all [paired]

/-- A recognized ranked original occurrence reads both orders on the coordinates of
the very same canonical tetrahedron. The reflected publication reads the hands in reverse. -/
def rankedCell {i : Input} (c : i.certified.TetrahedralCenter) (j : Joint) : Cell :=
  paired (physical (inputGeometry i.certified) (canonicalFrame c) (.ranked j))

theorem rankedCell_reads {i : Input} (c : i.certified.TetrahedralCenter) (j : Joint) :
    let g := inputGeometry i.certified
    let ids := canonicalFrame c
    let actual := RingJointObservations.read g ids j.1
    let reflected := RingJointObservations.read (mirror g) ids j.2
    rankedCell c j = (do
      let x ← caseFromMirror? actual reflected
      let y ← caseFromMirror? reflected actual
      return some (x,y)) := by
  let a := RingJointObservations.read (inputGeometry i.certified) (canonicalFrame c) j.1
  let b := RingJointObservations.read (mirror (inputGeometry i.certified)) (canonicalFrame c) j.2
  change paired (caseFromMirror? a b) = (do
    let x ← caseFromMirror? a b
    let y ← caseFromMirror? b a
    return some (x,y))
  rw [reflected_geometry a b]
  cases caseFromMirror? a b <;> rfl

private theorem ranked_present {i : Input} (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (c : i.certified.TetrahedralCenter) (j : Joint) : ∃ h, rankedCell c j = some (some (h,reflectLabel h)) := by
  obtain ⟨base,calib⟩ := RingJointObservations.calibration i c admit
  unfold rankedCell
  rw [calib]
  cases base <;> cases a : RingJointObservations.parity j.1 <;> cases b : RingJointObservations.parity j.2 <;>
    simp [RingJointObservations.letter,RingJointObservations.observable,RingJointObservations.oriented,paired,
      a,b,caseFromMirror?,RS.swap,pseudoRSOfRS]

theorem rankedCell_eq_iff {i : Input} (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    (c : i.certified.TetrahedralCenter) (j k : Joint) : rankedCell c j = rankedCell c k ↔
    changes j.1.val k.1.val % 2 = 0 ∧ changes j.2.val k.2.val % 2 = 0 := by
  unfold rankedCell
  rw [paired_injective.eq_iff,RingJointObservations.ranked_agreement i c admit]

/-- The meaning of a justified refusal is policy-specific. Rank evidence fixes the
recognized occurrence center and its original canonical ligand slots on both geometries.
Chemical admissibility of a particular strategy's ranks is a separate premise. -/
inductive Decision {i : Input} (q : Site i) (JustifiedRefusal : Site i → Prop) where
  | missing
  | refused (justified : JustifiedRefusal q)
  | ranked (c : i.certified.TetrahedralCenter)
      (center : i.certified.localizedOccurrenceDescriptorCenter? q = some c) (j : Joint)

def cell {i : Input} {q : Site i} {R : Site i → Prop} : Decision q R → Cell
  | .missing => none
  | .refused _ => some none
  | .ranked c _ j => rankedCell c j

def Compatible {i : Input} {q : Site i} {R S : Site i → Prop} : Decision q R → Decision q S → Prop
  | .missing,.missing | .refused _,.refused _ => True
  | .ranked _ _ j,.ranked _ _ k => changes j.1.val k.1.val % 2 = 0 ∧ changes j.2.val k.2.val % 2 = 0
  | _,_ => False

theorem cell_eq_iff {i : Input} (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {q : Site i} {R S : Site i → Prop} (x : Decision q R) (y : Decision q S) :
    cell x = cell y ↔ Compatible x y := by
  cases x with
  | missing | refused =>
    cases y with
    | missing | refused => simp [cell,Compatible]
    | ranked c _ j => obtain ⟨h,got⟩ := ranked_present admit c j; simp [cell,Compatible,got]
  | ranked c declared j =>
    cases y with
    | missing | refused => obtain ⟨h,got⟩ := ranked_present admit c j; simp [cell,Compatible,got]
    | ranked c' d k =>
      obtain rfl := Option.some.inj (declared.symm.trans d)
      exact rankedCell_eq_iff admit c j k

abbrev Strategy (i : Input) (R : Site i → Prop) := (q : Site i) → View i → Decision q R

def rule {i R} (a : Strategy i R) : Rule i := fun q snapshot => cell (a q snapshot)

/-- Equal parity of the named molecular slots on *each* geometry suffices even if either
strategy chooses different pair orderings, and is necessary wherever both rank. Agreement
also requires that both refuse or both remain unresolved at the same original address. -/
theorem ranked_schedule_iff {i : Input} (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {R S : Site i → Prop} (a : Strategy i R) (b : Strategy i S) :
    evaluate (rule a) = evaluate (rule b) ↔ ∀ q,
      let snapshot := frozen (evaluate (rule a)) q
      Compatible (a q snapshot) (b q snapshot) := by
  rw [evaluate_eq_iff]
  exact forall_congr' fun _ => cell_eq_iff admit _ _

/-- The carried history may contain an old reference, discovery order, or other imperative
state. Only an operationally justified history and its exact publications at the original
occurrences support this comparison with a frozen strategy. -/
theorem carried_ranked_iff {i : Input} (admit : LocalizedChemicalRing.coordinatesAdmitted i = true)
    {H : Type} {R S : Site i → Prop} (out : View i) (hist : Site i → H)
    (chronological : (q : Site i) → H → Decision q R)
    (recorded : ∀ q, out q = cell (chronological q (hist q))) (b : Strategy i S) :
    out = evaluate (rule b) ↔ ∀ q, Compatible (chronological q (hist q)) (b q (frozen out q)) := by
  rw [chronology_iff out hist (fun q h => cell (chronological q h)) recorded]
  exact forall_congr' fun _ => cell_eq_iff admit _ _

end TetraStereo.Engine.RingPublicationEquivalence

assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.evaluate_eq_iff
assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.divergence_frontier
assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.tables_eq_iff
assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.chronology_iff
assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.partial_chronology_iff
assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.reflected_geometry
assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.rankedCell_reads
assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.rankedCell_eq_iff
assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.cell_eq_iff
assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.ranked_schedule_iff
assert_kernel_only TetraStereo.Engine.RingPublicationEquivalence.carried_ranked_iff
