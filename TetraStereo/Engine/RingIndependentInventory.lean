import TetraStereo.Engine.RingChemicalGraphProof
import Mathlib.Data.List.MinMax

/-! Independent selection inventories and local publications on a common molecular graph. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingIndependentInventory
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActiveDistanceSchedule (Cell View Rule distance height frozen evaluate Visible)
open RingEligibleGraph (Eligible Inventory candidate)

structure Policy (i : Input) where
  eligible : i.certified.Atom → Bool
  primitive : Rule i

def Policy.rule {i : Input} (p : Policy i) : Rule i := fun q r =>
  if Eligible p.eligible q then p.primitive q r else some none

theorem Policy.skips {i : Input} (p : Policy i) :
    RingEligibleGraph.SkipsIneligible p.eligible p.rule := by
  intro q r off
  simp [Policy.rule,off]

/-- A meaningful selection change has a selected publication different from known
absence. In particular, unresolved `none` is distinguished from refused `some none`. -/
def LocalDifference {i : Input} (p s : Policy i) (q : Site i) (r : View i) : Prop :=
  (Eligible p.eligible q ∧ ¬ Eligible s.eligible q ∧ p.primitive q r ≠ some none) ∨
  (¬ Eligible p.eligible q ∧ Eligible s.eligible q ∧ s.primitive q r ≠ some none) ∨
  (Eligible p.eligible q ∧ Eligible s.eligible q ∧ p.primitive q r ≠ s.primitive q r)

theorem local_difference {i : Input} (p s : Policy i) (q : Site i) (r : View i)
    (bad : p.rule q r ≠ s.rule q r) : LocalDifference p s q r := by
  by_cases hp : Eligible p.eligible q <;> by_cases hs : Eligible s.eligible q
  · exact Or.inr (Or.inr ⟨hp,hs,by simpa [Policy.rule,hp,hs] using bad⟩)
  · exact Or.inl ⟨hp,hs,by simpa [Policy.rule,hp,hs] using bad⟩
  · exact Or.inr (Or.inl ⟨hp,hs,Ne.symm (by simpa [Policy.rule,hp,hs] using bad)⟩)
  · simp [Policy.rule,hp,hs] at bad

/-- A deepest discrepancy reads identical frozen stores. It stays on the same
original root, at the queried occurrence or a strictly visible dependency. -/
theorem deepest_difference {i : Input} (p s : Policy i) (q : Site i)
    (bad : evaluate p.rule q ≠ evaluate s.rule q) :
    ∃ t, (t = q ∨ Visible q t) ∧
      frozen (evaluate p.rule) t = frozen (evaluate s.rule) t ∧
      LocalDifference p s t (frozen (evaluate p.rule) t) := by
  suffices all : ∀ n (a : Site i), height i - distance a = n →
      evaluate p.rule a ≠ evaluate s.rule a →
      ∃ t, (t = a ∨ Visible a t) ∧
        frozen (evaluate p.rule) t = frozen (evaluate s.rule) t ∧
        LocalDifference p s t (frozen (evaluate p.rule) t) from all _ q rfl bad
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a rank mismatch
    classical
    by_cases agree : ∀ b, Visible a b → evaluate p.rule b = evaluate s.rule b
    · have readers : frozen (evaluate p.rule) a = frozen (evaluate s.rule) a := by
        funext b
        unfold frozen
        split_ifs with off visible
        · rfl
        · exact agree b ⟨not_ne_iff.mp off,visible⟩
        · rfl
      refine ⟨a,Or.inl rfl,readers,local_difference p s a _ ?_⟩
      rw [RingActiveDistanceSchedule.evaluate_eq,RingActiveDistanceSchedule.evaluate_eq,←readers] at mismatch
      exact mismatch
    · push_neg at agree
      obtain ⟨b,visible,mismatch⟩ := agree
      have upper := RingActiveDistanceSchedule.distance_bound b
      obtain ⟨t,step,readers,localBad⟩ := ih _ (by have := visible.2.1; omega) b rfl mismatch
      refine ⟨t,?_,readers,localBad⟩
      rcases step with rfl | next
      · exact Or.inr visible
      · exact Or.inr (visible.trans next)

/-- Independent queue enumerations may contain different refused centres. Their
materialized tables have identical lookup semantics after every bounded sphere. -/
theorem stored_semantics_above {i : Input} (p s : Policy i) (root : i.certified.Atom)
    (left right : Nat → List (Site i))
    (li : Inventory p.eligible root left) (ri : Inventory s.eligible root right)
    (k : Nat) (bound : k ≤ height i + 1)
    (same : ∀ q, height i < distance q + k → evaluate p.rule q = evaluate s.rule q) :
    RingSphereQueue.viewOf (RingSphereQueue.stored p.rule root left (height i) k) =
      RingSphereQueue.viewOf (RingSphereQueue.stored s.rule root right (height i) k) := by
  rw [RingSphereQueue.stored_eq,RingSphereQueue.stored_eq]
  funext q
  rw [RingEligibleGraph.run_exact p.skips li k bound q,
    RingEligibleGraph.run_exact s.skips ri k bound q]
  have absent (u : Policy i) (off : ¬ Eligible u.eligible q) : evaluate u.rule q = some none :=
    (RingActiveDistanceSchedule.evaluate_eq u.rule q).trans (u.skips q _ off)
  by_cases reached : height i < distance q + k
  · have sameHere := same q reached
    by_cases on : q.val.root = root
    · by_cases original : q.val.node.current? = some root
      · simp [candidate,original]
      · by_cases hp : Eligible p.eligible q <;> by_cases hs : Eligible s.eligible q
        · simp [candidate,on,original,hp,hs,sameHere]
        · have empty := absent s hs
          have other : evaluate p.rule q = some none := sameHere.trans empty
          simp [candidate,on,original,hp,hs,other]
        · have empty := absent p hp
          have other : evaluate s.rule q = some none := sameHere.symm.trans empty
          simp [candidate,on,original,hp,hs,other]
        · simp [candidate,on,original,hp,hs]
    · simp [candidate,on]
  · simp [reached]

theorem stored_semantics {i : Input} (p s : Policy i)
    (same : evaluate p.rule = evaluate s.rule) (root : i.certified.Atom)
    (left right : Nat → List (Site i))
    (li : Inventory p.eligible root left) (ri : Inventory s.eligible root right)
    (k : Nat) (bound : k ≤ height i + 1) :
    RingSphereQueue.viewOf (RingSphereQueue.stored p.rule root left (height i) k) =
      RingSphereQueue.viewOf (RingSphereQueue.stored s.rule root right (height i) k) :=
  stored_semantics_above p s root left right li ri k bound (fun q _ => congrFun same q)

/-- Agreement compares primitive cells only where both select; a selection
mismatch is harmless exactly when the selected primitive publishes known absence. -/
def Agreement {i : Input} (p s : Policy i) : Prop :=
  ∀ q, ¬ LocalDifference p s q (frozen (evaluate p.rule) q)

theorem evaluate_eq_of_agreement {i : Input} (p s : Policy i) (agree : Agreement p s) :
    evaluate p.rule = evaluate s.rule := by
  apply RingActiveDistanceSchedule.unique s.rule (evaluate p.rule)
  intro q
  rw [RingActiveDistanceSchedule.evaluate_eq]
  by_contra bad
  exact agree q (local_difference p s q _ bad)

theorem stored_semantics_of_agreement {i : Input} (p s : Policy i) (agree : Agreement p s)
    (root : i.certified.Atom) (left right : Nat → List (Site i))
    (li : Inventory p.eligible root left) (ri : Inventory s.eligible root right)
    (k : Nat) (bound : k ≤ height i + 1) :
    RingSphereQueue.viewOf (RingSphereQueue.stored p.rule root left (height i) k) =
      RingSphereQueue.viewOf (RingSphereQueue.stored s.rule root right (height i) k) :=
  stored_semantics p s (evaluate_eq_of_agreement p s agree) root left right li ri k bound

/-- Root disagreement for independently selected executable inventories. -/
theorem root_difference {i : Input} (p s : Policy i) (a : i.certified.Atom)
    (bad : RingEligibleGraph.root i p.eligible p.rule a ≠
      RingEligibleGraph.root i s.eligible s.rule a) :
    ∃ t, (t = RingGroupedReport.origin i a ∨ Visible (RingGroupedReport.origin i a) t) ∧
      frozen (evaluate p.rule) t = frozen (evaluate s.rule) t ∧
      LocalDifference p s t (frozen (evaluate p.rule) t) := by
  rw [RingEligibleGraph.root_exact p.rule p.skips,RingEligibleGraph.root_exact s.rule s.skips] at bad
  exact deepest_difference p s _ bad

/-- Native molecular selection and publication form one instance, without a
coordinate or classification-agreement assumption. -/
def native (i : Input) : Policy i := ⟨RingPyramidalPublication.eligible i,RingPyramidalPublication.publish i⟩

theorem native_rule (i : Input) : (native i).rule = RingPyramidalPublication.publish i := by
  funext q r
  by_cases selected : Eligible (RingPyramidalPublication.eligible i) q
  · simp [native,Policy.rule,selected]
  · simpa [native,Policy.rule,selected] using (RingChemicalGraphProof.skips i q r selected).symm


/-- Native comparison at any occurrence, including the original requested root. -/
theorem native_difference (i : Input) (s : Policy i) (q : Site i)
    (bad : RingChemicalGraphProof.state i q ≠ evaluate s.rule q) :
    ∃ t, (t = q ∨ Visible q t) ∧
      frozen (RingChemicalGraphProof.state i) t = frozen (evaluate s.rule) t ∧
      LocalDifference (native i) s t (frozen (RingChemicalGraphProof.state i) t) := by
  have result := deepest_difference (native i) s q
  have mismatch : evaluate (native i).rule q ≠ evaluate s.rule q := by
    simpa only [native_rule,RingChemicalGraphProof.state] using bad
  simpa only [native_rule,RingChemicalGraphProof.state] using result mismatch


/-- A single short-circuit pass over the finite occurrence inventory. The native
state is computed once and shared by every frozen reader; the alternative is
called only as a local primitive and never recursively evaluated by this scan. -/
def scan (i : Input) (s : Policy i) : Option (Site i) :=
  let cached := RingChemicalGraphProof.state i
  (RingActiveDistanceSchedule.sites i).find? fun q =>
    decide (s.rule q (frozen cached q) ≠ cached q)

theorem scan_none_iff_outputs (i : Input) (s : Policy i) :
    scan i s = none ↔ ∀ q, s.rule q (frozen (RingChemicalGraphProof.state i) q) =
      RingChemicalGraphProof.state i q := by
  simp only [scan,List.find?_eq_none,decide_eq_true_eq,not_ne_iff]
  exact ⟨fun h q => h q (List.mem_attach ..),fun h q _ => h q⟩

/-- Boolean certificate for the short-circuit scan. -/
def check (i : Input) (s : Policy i) : Bool := (scan i s).isNone

theorem check_true_iff_outputs (i : Input) (s : Policy i) :
    check i s = true ↔ ∀ q, s.rule q (frozen (RingChemicalGraphProof.state i) q) =
      RingChemicalGraphProof.state i q := by
  simpa only [check,Option.isNone_iff_eq_none] using scan_none_iff_outputs i s

/-- Equality of the independently recursive states is decided without executing
alternative recursion. This includes every occurrence, ties and coverage failures. -/
theorem scan_none_iff_states (i : Input) (s : Policy i) :
    scan i s = none ↔ RingChemicalGraphProof.state i = evaluate s.rule := by
  rw [scan_none_iff_outputs]
  constructor
  · intro h
    exact RingActiveDistanceSchedule.unique s.rule (RingChemicalGraphProof.state i) (fun q => (h q).symm)
  · intro h q
    rw [h]
    exact (RingActiveDistanceSchedule.evaluate_eq s.rule q).symm

theorem check_true_iff_states (i : Input) (s : Policy i) :
    check i s = true ↔ RingChemicalGraphProof.state i = evaluate s.rule := by
  simpa only [check,Option.isNone_iff_eq_none] using scan_none_iff_states i s

/-- A returned address witnesses an actual primitive/selection disagreement on
the identical shared native reader. This need not be the deepest discrepancy. -/
theorem scan_some (i : Input) (s : Policy i) (q : Site i) (found : scan i s = some q) :
    s.rule q (frozen (RingChemicalGraphProof.state i) q) ≠ RingChemicalGraphProof.state i q ∧
    LocalDifference (native i) s q (frozen (RingChemicalGraphProof.state i) q) := by
  unfold scan at found
  have hit := List.find?_some found
  have bad : s.rule q (frozen (RingChemicalGraphProof.state i) q) ≠ RingChemicalGraphProof.state i q :=
    of_decide_eq_true hit
  refine ⟨bad,local_difference (native i) s q _ ?_⟩
  rw [native_rule,←RingChemicalGraphProof.state_eq]
  exact Ne.symm bad

/-- Passing the finite scan certifies all semantic sparse snapshots for any
independent enumerations, and every actual executable root result. -/
theorem scan_pass_exact (i : Input) (s : Policy i) (passed : scan i s = none) :
    (∀ (root : i.certified.Atom) (left right : Nat → List (Site i)),
      Inventory (native i).eligible root left → Inventory s.eligible root right →
      ∀ k, k ≤ height i + 1 →
        RingSphereQueue.viewOf (RingSphereQueue.stored (native i).rule root left (height i) k) =
        RingSphereQueue.viewOf (RingSphereQueue.stored s.rule root right (height i) k)) ∧
    ∀ a, RingChemicalGraphProof.root i a = RingEligibleGraph.root i s.eligible s.rule a := by
  have same : evaluate (native i).rule = evaluate s.rule := by
    simpa only [native_rule,RingChemicalGraphProof.state] using (scan_none_iff_states i s).mp passed
  constructor
  · intro root left right li ri k bound
    exact stored_semantics (native i) s same root left right li ri k bound
  · intro a
    rw [RingChemicalGraphProof.root,RingEligibleGraph.root_exact _ (RingChemicalGraphProof.skips i),
      RingEligibleGraph.root_exact s.rule s.skips]
    simpa only [native_rule] using congrFun same (RingGroupedReport.origin i a)

/-- All detectable primitive disagreements, compared on a single computed state. -/
def conflicts (i : Input) (s : Policy i) : List (Site i) :=
  let nativeState := RingChemicalGraphProof.state i
  (RingActiveDistanceSchedule.sites i).filter fun q =>
    decide (s.rule q (frozen nativeState q) ≠ nativeState q)

theorem mem_conflicts {i : Input} {s : Policy i} {q : Site i} :
    q ∈ conflicts i s ↔ s.rule q (frozen (RingChemicalGraphProof.state i) q) ≠
      RingChemicalGraphProof.state i q := by
  have present : q ∈ RingActiveDistanceSchedule.sites i := List.mem_attach ..
  simp [conflicts,present]

/-- Choose a discrepancy in the earliest outside-in sphere on any root. -/
def diagnose? (i : Input) (s : Policy i) := (conflicts i s).argmax distance

theorem diagnose_none_iff_states (i : Input) (s : Policy i) :
    diagnose? i s = none ↔ RingChemicalGraphProof.state i = evaluate s.rule := by
  rw [diagnose?,List.argmax_eq_none,←scan_none_iff_states,scan_none_iff_outputs]
  simp [List.eq_nil_iff_forall_not_mem,mem_conflicts]

/-- The returned occurrence sees identical independently computed readers. All
strictly deeper publications agree, even across different center inventories. -/
theorem diagnose_some {i : Input} {s : Policy i} {q : Site i} (found : diagnose? i s = some q) :
    (∀ t, distance q < distance t → RingChemicalGraphProof.state i t = evaluate s.rule t) ∧
    frozen (RingChemicalGraphProof.state i) q = frozen (evaluate s.rule) q ∧
    RingChemicalGraphProof.state i q ≠ evaluate s.rule q ∧
    LocalDifference (native i) s q (frozen (RingChemicalGraphProof.state i) q) := by
  have selected : q ∈ (conflicts i s).argmax distance := found
  have bad := mem_conflicts.mp (List.argmax_mem selected)
  have higher (t : Site i) (lt : distance q < distance t) :
      RingChemicalGraphProof.state i t = evaluate s.rule t := by
    by_contra diff
    obtain ⟨u,step,_,why⟩ := native_difference i s t diff
    have conflict : u ∈ conflicts i s := by
      apply mem_conflicts.mpr
      rw [RingChemicalGraphProof.state_eq i u,←native_rule i]
      rcases why with ⟨on,off,h⟩ | ⟨off,on,h⟩ | ⟨on,both,h⟩
      · simp [Policy.rule,on,off,Ne.symm h]
      · simp [Policy.rule,on,off,h]
      · simp [Policy.rule,on,both,Ne.symm h]
    have upper := List.le_of_mem_argmax conflict selected
    rcases step with rfl | visible
    · exact Nat.not_lt_of_ge upper lt
    · exact Nat.not_lt_of_ge upper (lt.trans visible.2.1)
  have readers : frozen (RingChemicalGraphProof.state i) q = frozen (evaluate s.rule) q := by
    funext t
    unfold frozen
    split_ifs with _ ok
    · rfl
    · exact higher t ok.1
    · rfl
  refine ⟨higher,readers,?_,local_difference (native i) s q _ ?_⟩
  · rw [RingActiveDistanceSchedule.evaluate_eq s.rule q,←readers]
    exact Ne.symm bad
  · rw [native_rule,←RingChemicalGraphProof.state_eq]
    exact Ne.symm bad

/-- All earlier committed stores have equal lookup at every address for every
root, even when the two policies enumerate different centers. -/
theorem diagnose_prior_stores {i : Input} {s : Policy i} {q : Site i} (found : diagnose? i s = some q)
    (root : i.certified.Atom) (left right : Nat → List (Site i))
    (li : Inventory (native i).eligible root left) (ri : Inventory s.eligible root right)
    (k : Nat) (earlier : k ≤ height i - distance q) :
    RingSphereQueue.viewOf (RingSphereQueue.stored (native i).rule root left (height i) k) =
      RingSphereQueue.viewOf (RingSphereQueue.stored s.rule root right (height i) k) := by
  apply stored_semantics_above (native i) s root left right li ri k (by omega)
  intro t reached
  rw [native_rule]
  apply (diagnose_some found).1
  have upper := RingActiveDistanceSchedule.distance_bound q
  omega

end TetraStereo.Engine.RingIndependentInventory
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.deepest_difference
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.stored_semantics
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.root_difference
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.native_rule
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.evaluate_eq_of_agreement
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.stored_semantics_of_agreement
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.native_difference
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.scan_none_iff_outputs
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.scan_none_iff_states
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.scan_some
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.scan_pass_exact
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.check_true_iff_states
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.check_true_iff_outputs
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.diagnose_some
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.diagnose_none_iff_states
assert_kernel_only TetraStereo.Engine.RingIndependentInventory.diagnose_prior_stores
