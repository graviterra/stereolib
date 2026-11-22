import TetraStereo.Engine.RingActiveDistanceSchedule
import TetraStereo.Engine.RingNestedActivePair

set_option autoImplicit false

namespace TetraStereo.Engine.RingMolecularSchedule
open OneCenter CertifiedLocalizedCIPInput RingActivePairs
open RingActiveDistanceSchedule
open LocalizedChemicalRing (Input)

private def onRoot (i : Input) (root : i.certified.Atom) : Rule i := fun q table =>
  if q.val.root = root then RingNestedActivePair.publish? i q table else none

/-- All intermediate values indexed by original occurrence, for one original molecular
digraph. Partial values stay explicit, including at the original root. -/
def atRoot (i : Input) (root : i.certified.Atom) := evaluate (onRoot i root)

/-- Keep this value for multiple queries against a single original digraph. -/
def publicationTable (i : Input) (root : i.certified.Atom) : Table i :=
  table (onRoot i root) (height i+1)

theorem table_readback (i : Input) (root : i.certified.Atom) :
    snapshot (publicationTable i root) = atRoot i root := snapshot_table ..

theorem atRoot_eq {i : Input} {root : i.certified.Atom} {q : Site i} (on : q.val.root = root) :
    atRoot i root q = RingNestedActivePair.publish? i q (atRoot i root) := by
  change evaluate (onRoot i root) q = _
  rw [evaluate_eq]
  simp only [onRoot,on,if_true]
  apply RingNestedActivePair.publish_congr
  intro t vis
  simp [frozen,vis.1,vis.2.1,vis.2.2,distance,atRoot]

/-- A molecular derivation contains no oracle for positive auxiliary labels. A nested
case carries the original cursor frame, both actual rankings and their two coordinate
readbacks. Every known entry in its eligible observation scope has a smaller derivation. -/
inductive Derivation (i : Input) : Site i → Option RingNestedActivePair.Labels → Prop where
  | absent {q} (absent : ∀ c, ¬i.certified.RealTetrahedralCenterNode q.val.node c) :
      Derivation i q none
  | refusal {q} (s : View i) (why : RingNestedActivePair.Refusal i q (RingNestedActivePair.masked q s))
      (deeper : ∀ t v, Visible q t → s t = some v → Derivation i t v) : Derivation i q none
  | constitutional {q s} (actual : RingRetainedAuxiliary.read? i q = some s) :
      Derivation i q (some (.chiral s,.chiral s.swap))
  | ranked {q} (s : View i)
      (a : RingNestedActivePair.Assignment i q (RingNestedActivePair.masked q s))
      (found : RingNestedActivePair.assign? i q (RingNestedActivePair.masked q s) = some a)
      (deeper : ∀ t v, Visible q t → s t = some v → Derivation i t v) :
      Derivation i q (some a.labels)

/-- Published absences include structural non-centers and a fully checked silent
pair at a four-coordinate unmarked occurrence. -/
theorem structural_absence_iff {i : Input} {root : i.certified.Atom} {q : Site i} (on : q.val.root = root) :
    atRoot i root q = some none ↔ RingNestedActivePair.Absent i q (atRoot i root) := by
  rw [atRoot_eq on]
  exact RingNestedActivePair.absence_source

/-- Each molecular publication or known absence has a finite proof, across arbitrarily
many nested comparisons and including both geometries. -/
theorem derivation {i : Input} {root : i.certified.Atom} (q : Site i)
    (on : q.val.root = root) {v} (hit : atRoot i root q = some v) : Derivation i q v := by
  suffices h : ∀ n (q : Site i), height i - distance q = n → q.val.root = root →
      ∀ v, atRoot i root q = some v → Derivation i q v from h _ q rfl on _ hit
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro q rank on v out
    rw [atRoot_eq on] at out
    cases v with
    | none =>
      rcases RingNestedActivePair.absence_source.mp out with structural | ⟨_,proved⟩
      · exact .absent structural
      · obtain ⟨w,_⟩ := proved
        apply Derivation.refusal _ w
        intro t v vis seen
        have upper := distance_bound t
        have lt := vis.2.1
        exact ih _ (by omega) t rfl (vis.1.trans on) v seen
    | some labels =>
      rcases RingNestedActivePair.publication_source out with ⟨s,found,rfl⟩ | ⟨a,found,rfl⟩
      · exact .constitutional found
      · apply Derivation.ranked _ a found
        intro t v vis seen
        have upper := distance_bound t
        have lt := vis.2.1
        exact ih _ (by omega) t rfl (vis.1.trans on) v seen

/-- Every positive scheduled observation has the physical mirror behavior of its claimed
case. This holds even when other addresses of the same original digraph are unresolved. -/
theorem mirror_label {i : Input} {root : i.certified.Atom} {q : Site i} (on : q.val.root = root)
    {v : RingNestedActivePair.Labels} (hit : atRoot i root q = some (some v)) :
    RingNestedActivePair.consistent v = true := by
  rw [atRoot_eq on] at hit
  rcases RingNestedActivePair.publication_source hit with ⟨s,_,rfl⟩ | ⟨a,_,rfl⟩
  · cases s <;> rfl
  · exact a.casing.2.2

/-- These are actual unresolved original addresses at which every eligible deeper
publication is already known. This diagnostic never substitutes absence for a failure. -/
private def frontierIn {i : Input} (root : i.certified.Atom) (xs : List (Site i)) (rows : Table i) :
    List (Site i) :=
  xs.filter fun q => decide (q.val.root = root) && (snapshot rows q).isNone &&
    xs.all (fun t => !(decide (Visible q t)) || (snapshot rows t).isSome)

def frontier (i : Input) (root : i.certified.Atom) : List (Site i) :=
  frontierIn root (sites i) (publicationTable i root)

theorem mem_frontier {i : Input} {root : i.certified.Atom} {q : Site i} :
    q ∈ frontier i root ↔ q.val.root = root ∧ atRoot i root q = none ∧
    ∀ t, Visible q t → (atRoot i root t).isSome = true := by
  have allSites (t : Site i) : t ∈ sites i := List.mem_attach ..
  classical
  simp [frontier, frontierIn, table_readback, List.all_eq_true, allSites, and_assoc, ← imp_iff_not_or]

/-- Every failure leads to a calculable, same-root first missing chemical proof. -/
theorem failure_has_frontier {i : Input} {root : i.certified.Atom} (q : Site i)
    (on : q.val.root = root) (unknown : atRoot i root q = none) :
    ∃ t ∈ frontier i root, t = q ∨ Visible q t := by
  obtain ⟨t,below,stuck,known⟩ := obstruction_of_uncovered (onRoot i root) q unknown
  have scope : t.val.root = root := below.elim (fun same => same ▸ on) (fun vis => vis.1.trans on)
  exact ⟨t,mem_frontier.mpr ⟨scope,(evaluate_eq (onRoot i root) t).trans stuck,known⟩,below⟩

/-- Root-local coverage is equivalent to exhausting the executable obstruction inventory. -/
theorem complete_iff {i : Input} (root : i.certified.Atom) :
    (∀ q : Site i, q.val.root = root → (atRoot i root q).isSome = true) ↔ frontier i root = [] := by
  constructor
  · intro full
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro q mem
    obtain ⟨on,unknown,_⟩ := mem_frontier.mp mem
    simpa [unknown] using full q on
  · intro empty q on
    cases h : atRoot i root q with
    | some => rfl
    | none =>
      obtain ⟨t,mem,_⟩ := failure_has_frontier q on h
      simp [empty] at mem

/-- Localize the actual comparator gap at a frontier row. Simply adding recursion depth
cannot fix these rows: the direct retained publication failed and both-geometry assignment
still failed with every relevant deeper molecular value available. -/
theorem frontier_gap {i : Input} {root : i.certified.Atom} {q : Site i} (listed : q ∈ frontier i root) :
    RingRetainedAuxiliary.publication? i q = none ∧
    RingNestedActivePair.assign? i q (RingNestedActivePair.masked q (atRoot i root)) = none ∧
    ∀ t, Visible q t → ∃ v, atRoot i root t = some v ∧ Derivation i t v := by
  obtain ⟨on,unknown,known⟩ := mem_frontier.mp listed
  rw [atRoot_eq on] at unknown
  cases h : RingRetainedAuxiliary.publication? i q with
  | some v => cases v <;> simp [RingNestedActivePair.publish?,h] at unknown
  | none =>
    refine ⟨rfl,?_,?_⟩
    · apply RingNestedActivePair.later_missing
      simpa [RingNestedActivePair.publish?,h] using unknown
    · intro t vis
      obtain ⟨v,found⟩ := Option.isSome_iff_exists.mp (known t vis)
      exact ⟨v,found,derivation t (vis.1.trans on) found⟩

/-- Source coverage can only fail at a real tetrahedral occurrence, and a deepest
witness has every potentially visible publication or structural absence justified. -/
theorem frontier_center {i : Input} {root : i.certified.Atom} {q : Site i} (listed : q ∈ frontier i root) :
    ∃ c, i.certified.RealTetrahedralCenterNode q.val.node c := by
  obtain ⟨on,missing,_⟩ := mem_frontier.mp listed
  by_contra! absent
  rw [(structural_absence_iff on).mpr (Or.inl absent)] at missing
  contradiction

end TetraStereo.Engine.RingMolecularSchedule

assert_kernel_only TetraStereo.Engine.RingMolecularSchedule.atRoot_eq
assert_kernel_only TetraStereo.Engine.RingMolecularSchedule.derivation
assert_kernel_only TetraStereo.Engine.RingMolecularSchedule.failure_has_frontier
assert_kernel_only TetraStereo.Engine.RingMolecularSchedule.complete_iff
assert_kernel_only TetraStereo.Engine.RingMolecularSchedule.frontier_gap

assert_kernel_only TetraStereo.Engine.RingMolecularSchedule.mirror_label

assert_kernel_only TetraStereo.Engine.RingMolecularSchedule.structural_absence_iff
assert_kernel_only TetraStereo.Engine.RingMolecularSchedule.frontier_center

assert_kernel_only TetraStereo.Engine.RingMolecularSchedule.table_readback
