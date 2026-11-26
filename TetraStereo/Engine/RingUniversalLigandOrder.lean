import TetraStereo.Engine.RingGlobalComparison
import TetraStereo.Engine.RingPairwisePublication
import TetraStereo.Engine.RingPyramidalPairwise

/-! Whole reports from pairwise ligand priorities. An alternative may replace
every strict comparison on either geometry and in every promotion trial. It
inherits molecular occurrences, available frames, physical IDs and read availability. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingUniversalLigandOrder
open OneCenter LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell View frozen height)
open RingActivePairReport (Slot)
open RingPyramidalPublication (focusP)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
namespace Tetra
abbrev Data := RingPairwisePublication.Data
end Tetra
namespace Pyramidal
abbrev Data := RingPyramidalPairwise.Data
abbrev Row := RingPyramidalPairwise.Row
end Pyramidal

inductive Trial (α : Type) where
  | ordinary
  | marked (mark : Option α)

/-- Directed strict comparison on one geometry, between two positions in a
physical ligand row. Two false directions express equality. -/
inductive Query where
  | tetra (reflected : Bool) (trial : Trial Slot) (left right : Slot)
  | pyramidal (reflected : Bool) (trial : Trial Nat) (left right : Nat)

abbrev Answers := Query → Bool

inductive Observation (i : Input) (q : Site i) where
  | tetra (frame : Option (RingPairwisePublication.FrameData i q))
  | pyramidal (a : i.certified.Atom) (data : Pyramidal.Data)

def observe (i : Input) (q : Site i) (r : View i) : Observation i q :=
  match focusP i q with
  | none => .tetra (RingPairwisePublication.extract? i q r)
  | some a => .pyramidal a (RingPyramidalPairwise.nativeData i q r)

def interpret {i : Input} {q : Site i} : Observation i q → Cell
  | .tetra frame => frame.bind (RingPairwisePublication.frameDataPublish (inputGeometry i.certified))
  | .pyramidal a d => some (d.publish (inputGeometry i.certified) a.val)

def patchDir (answer : Answers) (rev : Bool) (s : Trial Slot)
    (native : RingPairwisePublication.Directions) : RingPairwisePublication.Directions :=
  fun a b => if a = b then native a b else answer (.tetra rev s a b)

def patchRow (answer : Answers) (rev : Bool) (s : Trial Nat) (row : Pyramidal.Row) : Pyramidal.Row :=
  {row with less := fun a b => if a = b then row.less a b else answer (.pyramidal rev s a.val b.val)}

def patchT (d : Tetra.Data) (answer : Answers) : Tetra.Data where
  ordinary rev := patchDir answer rev .ordinary (d.ordinary rev)
  marked rev mark := (d.marked rev mark).map (patchDir answer rev (.marked mark))

def patchP (d : Pyramidal.Data) (answer : Answers) : Pyramidal.Data where
  shape := d.shape
  ordinary rev := (d.ordinary rev).map (patchRow answer rev .ordinary)
  marked rev mark := (d.marked rev mark).map (patchRow answer rev (.marked mark))

def replace {i : Input} {q : Site i} (answer : Answers) : Observation i q → Observation i q
  | .tetra (some (some (fr,d))) => .tetra (some (some (fr,patchT d answer)))
  | .pyramidal a d => .pyramidal a (patchP d answer)
  | other => other

/-- Each fact names distinct positions in an available native comparison matrix.
No fact is emitted for absent frames, missing reads or out-of-bounds slots. -/
inductive Fact {i : Input} {q : Site i} : Observation i q → Query → Bool → Prop where
  | tetra {fr : RingNestedActivePair.Frame i q} {d : Tetra.Data} (rev : Bool) (a b : Slot) (ne : a ≠ b) : Fact (.tetra (some (some (fr,d))))
      (.tetra rev .ordinary a b) (d.ordinary rev a b)
  | tetraMarked {fr : RingNestedActivePair.Frame i q} {d : Tetra.Data} (rev : Bool) (mark : Option Slot) {w : RingPairwisePublication.Directions} (present : d.marked rev mark = some w) (a b) (ne : a ≠ b) :
      Fact (.tetra (some (some (fr,d)))) (.tetra rev (.marked mark) a b) (w a b)
  | pyramidal {focus : i.certified.Atom} {d : Pyramidal.Data} (rev : Bool) {w : Pyramidal.Row} (present : d.ordinary rev = some w) (a b : Fin w.size) (ne : a ≠ b) :
      Fact (.pyramidal focus d) (.pyramidal rev .ordinary a.val b.val) (w.less a b)
  | pyramidalMarked {focus : i.certified.Atom} {d : Pyramidal.Data} (rev : Bool) (mark : Option Nat) {w : Pyramidal.Row} (present : d.marked rev mark = some w)
      (a b : Fin w.size) (ne : a ≠ b) :
      Fact (.pyramidal focus d) (.pyramidal rev (.marked mark) a.val b.val) (w.less a b)

private theorem row_eq (ans : Answers) (rev : Bool) (s : Trial Nat) (w : Pyramidal.Row)
    (agree : ∀ a b : Fin w.size, a ≠ b → ans (.pyramidal rev s a.val b.val) = w.less a b) :
    patchRow ans rev s w = w := by
  have e : (patchRow ans rev s w).less = w.less := by
    funext a b
    by_cases same : a = b <;> simp [patchRow,same,agree]
  cases w
  exact congrArg (RingPyramidalPairwise.Row.mk _ _) e

theorem replace_eq {i : Input} {q : Site i} (o : Observation i q) (ans : Answers)
    (agree : ∀ t b, Fact o t b → ans t = b) : replace ans o = o := by
  cases o with
  | tetra frame =>
    rcases frame with _ | (_ | ⟨fr,d⟩) <;> try rfl
    have ordinary : (patchT d ans).ordinary = d.ordinary := by
      funext v a b
      by_cases h : a = b
      · simp [patchT,patchDir,h]
      · exact (if_neg h).trans (agree _ _ (.tetra v a b h))
    have marked : (patchT d ans).marked = d.marked := by
      funext v s
      change (d.marked v s).map _ = _
      cases h : d.marked v s with
      | none => rfl
      | some w =>
        apply congrArg some
        funext a b
        by_cases eqn : a = b
        · simp [patchDir,eqn]
        · exact (if_neg eqn).trans (agree _ _ (.tetraMarked v s h a b eqn))
    have e : patchT d ans = d := by cases d; exact congrArg₂ RingPairwisePublication.Data.mk ordinary marked
    change Observation.tetra (some (some (fr,patchT d ans))) = _
    rw [e]
  | pyramidal a d =>
    have ordinary : (patchP d ans).ordinary = d.ordinary := by
      funext v
      change (d.ordinary v).map _ = _
      cases h : d.ordinary v with
      | none => rfl
      | some w => exact congrArg some (row_eq ans v .ordinary w (fun a b eqn => agree _ _ (.pyramidal v h a b eqn)))
    have marked : (patchP d ans).marked = d.marked := by
      funext v s
      change (d.marked v s).map _ = _
      cases h : d.marked v s with
      | none => rfl
      | some w => exact congrArg some (row_eq ans v (.marked s) w (fun a b eqn => agree _ _ (.pyramidalMarked v s h a b eqn)))
    have e : patchP d ans = d := by cases d; exact congrArg₂ (RingPyramidalPairwise.Data.mk _) ordinary marked
    exact congrArg (Observation.pyramidal a) e


def interface (i : Input) (valid : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    RingGlobalComparison.Interface i where
  Data := Observation i
  native := observe i
  interpret := fun _ => interpret
  reachable q := by
    let r := frozen (RingChemicalGraphProof.state i) q
    let g := inputGeometry i.certified
    have localEq : interpret (observe i q r) = RingFrameTransport.publishG i g q r := by
      cases hit : focusP i q with
      | none => simpa only [observe,hit,interpret] using
          (RingPairwisePublication.publishG_exact g q r hit).symm
      | some a => simpa only [observe,hit,interpret] using
          (RingPyramidalPairwise.publishG_native g hit r).symm
    exact localEq.trans (RingFrameTransport.publishG_input valid (RingChemicalGraphProof.ready valid q))

abbrev Oracle (i : Input) := Site i → View i → Answers

variable {i : Input} (valid : LocalizedChemicalRing.coordinatesAdmitted i = true) (other : Oracle i)

def source : RingGlobalComparison.Source (interface i valid) :=
  fun q r => replace (other q r) (observe i q r)

abbrev rows := RingGlobalComparison.rows (interface i valid) (source valid other)
abbrev report := RingGlobalComparison.report (interface i valid) (source valid other)

/-- A directed ligand comparison on an actual root or auxiliary occurrence,
after both evaluators have committed identical lists of addressed cells. -/
def Witness (a : i.certified.Atom) (k : Nat) (q : Site i) : Prop :=
  RingGlobalComparison.Called i a k q ∧ rows valid other a k = RingSphereStore.rows i a k ∧
    RingGlobalComparison.rule (interface i valid) (source valid other) q (RingGlobalComparison.prior i a k) ≠
      RingPyramidalPublication.publish i q (RingGlobalComparison.prior i a k) ∧
    ∃ t b, Fact (observe i q (RingGlobalComparison.prior i a k)) t b ∧
      other q (RingGlobalComparison.prior i a k) t ≠ b

theorem witness_of_difference {a : i.certified.Atom} {k : Nat} {q : Site i}
    (d : RingGlobalComparison.Difference (interface i valid) (source valid other) a k q) :
    Witness valid other a k q := by
  refine ⟨d.1,d.2.1,d.2.2.1,?_⟩
  by_contra! no
  apply d.2.2.2
  exact replace_eq _ _ no

theorem rows_or_witness (a : i.certified.Atom) (k : Nat) (bound : k ≤ height i + 1) :
    rows valid other a k = RingSphereStore.rows i a k ∨ ∃ n < k, ∃ q, Witness valid other a n q := by
  rcases RingGlobalComparison.rows_or_difference (interface i valid) (source valid other) a k bound with
    same | ⟨n,lt,q,d⟩
  · exact Or.inl same
  · exact Or.inr ⟨n,lt,q,witness_of_difference valid other d⟩

theorem report_disagreement (atoms : List i.certified.Atom)
    (bad : report valid other atoms ≠ RingChemicalReport.report? i atoms) :
    ∃ a ∈ atoms, ∃ k ≤ height i + 1, ∃ q, Witness valid other a k q := by
  obtain ⟨a,mem,k,bound,q,d⟩ := RingGlobalComparison.report_disagreement
    (interface i valid) (source valid other) atoms bad
  exact ⟨a,mem,k,bound,q,witness_of_difference valid other d⟩

/-- Agreement on comparisons in reachable reads suffices simultaneously for
the complete materialized stores and the public typed report. -/
theorem exact_of_comparisons
    (agree : ∀ (a : i.certified.Atom) k q, RingGlobalComparison.Called i a k q →
      ∀ t b, Fact (observe i q (RingGlobalComparison.prior i a k)) t b →
        other q (RingGlobalComparison.prior i a k) t = b) :
    (∀ a k, k ≤ height i + 1 → rows valid other a k = RingSphereStore.rows i a k) ∧
      ∀ atoms, report valid other atoms = RingChemicalReport.report? i atoms := by
  have exclude : ∀ a k q, ¬ Witness valid other a k q := by
    rintro a k q ⟨call,_,_,t,b,f,wrong⟩
    exact wrong (agree a k q call t b f)
  constructor
  · intro a k bound
    exact (rows_or_witness valid other a k bound).resolve_right (by
      rintro ⟨n,_,q,w⟩; exact exclude a n q w)
  · intro atoms
    by_contra bad
    obtain ⟨a,_,k,_,q,w⟩ := report_disagreement valid other atoms bad
    exact exclude a k q w

/-- Every possible replacement of ligand order refuses a root that has neither
an admitted pyramidal focus nor a tetrahedral frame. -/
theorem unrecognized_root (a : i.certified.Atom)
    (hp : focusP i (RingGroupedReport.origin i a) = none)
    (hf : RingNestedActivePair.frame? i (RingGroupedReport.origin i a) = none) :
    RingGlobalComparison.root (interface i valid) (source valid other) a = some none := by
  simp [RingGlobalComparison.root,RingGlobalComparison.rule,interface,source,observe,hp,
    RingPairwisePublication.extract?,hf,replace,interpret,RingPairwisePublication.frameDataPublish]

end TetraStereo.Engine.RingUniversalLigandOrder
assert_kernel_only TetraStereo.Engine.RingUniversalLigandOrder.exact_of_comparisons
assert_kernel_only TetraStereo.Engine.RingUniversalLigandOrder.report_disagreement
assert_kernel_only TetraStereo.Engine.RingUniversalLigandOrder.unrecognized_root
