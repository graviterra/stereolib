import TetraStereo.Engine.RingTwoPairPriority

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority
open OneCenter LocalizedGenericMarkedRecalculation Recursive

variable {m : RawMolecule} {p : List Nat} {omitted : List (List Nat)}
    {e : Experiment m p omitted} {mat : Matrix e}

/-- Compare the two members of each pair with the same promoted atom.
The partition lists the senior pair first on the original geometry. -/
def Matrix.aligned (mat : Matrix e) (mark a b c d : Nat) : Bool :=
  mat.strict mark false a b == mat.strict mark false c d

private theorem geometry_of_orders (g : Geometry) {a b c d : Nat} {other : List Nat}
    (exchange : swapBlocks? [a,b,c,d] = some other) :
    geometric g [a,b,c,d] other = (readback? g [a,b,c,d]).map (fun h => ⟨h,h.swap⟩) := by
  obtain rfl := Option.some.inj exchange
  unfold geometric
  rw [readback_mirror,LocalizedMarkedTerminalGaugeSwap.readback_swap24 g c b a d,
    LocalizedMarkedTerminalGaugeSwap.readback_swap13 g a b c d]
  cases h : readback? g [a,b,c,d] with
  | none => rfl
  | some hand => cases hand <;> rfl

/-- The reference hand is read once in partition order. Flipping exactly
one molecular pair reverses it. Flipping neither or both preserves it. -/
theorem Trial.reading_of_pair_preferences (t : Trial mat) (partition : Partition mat)
    {a b c d : Nat} (slots : partition.order = [a,b,c,d]) (g : Geometry) :
    geometric g t.actual t.reflected = (readback? g [a,b,c,d]).map fun base =>
      let hand := if mat.aligned t.mark a b c d then base else base.swap
      ⟨hand,hand.swap⟩ := by
  have order := t.actual_of_pair_preferences partition slots
  have exchange := t.swap
  rw [order] at exchange ⊢
  cases x : mat.strict t.mark false a b <;> cases y : mat.strict t.mark false c d <;>
    simp only [Matrix.aligned,x,y,pairOrder,Bool.false_eq_true,if_false,if_true,List.cons_append,
      List.nil_append] at exchange ⊢
  all_goals rw [geometry_of_orders g exchange]
  · rw [LocalizedMarkedTerminalGaugeSwap.readback_swap12 g a b d c,
      LocalizedMarkedTerminalGaugeSwap.readback_swap34 g a b c d]
    cases h : readback? g [a,b,c,d] with
    | none => rfl
    | some hand => cases hand <;> rfl
  · rw [LocalizedMarkedTerminalGaugeSwap.readback_swap12 g a b c d]
    cases readback? g [a,b,c,d] <;> rfl
  · rw [LocalizedMarkedTerminalGaugeSwap.readback_swap34 g a b c d]
    cases readback? g [a,b,c,d] <;> rfl
  · rfl

/-- Given a nondegenerate reference geometry, any two fully ranked
promotions give the same two-geometry reading exactly when the parities of
their two independent pair preferences agree. No consensus is assumed. -/
theorem Trial.same_reading_iff (u v : Trial mat) (partition : Partition mat)
    {a b c d : Nat} (slots : partition.order = [a,b,c,d]) (g : Geometry) {base : RS}
    (nondegenerate : readback? g [a,b,c,d] = some base) :
    geometric g u.actual u.reflected = geometric g v.actual v.reflected ↔
      mat.aligned u.mark a b c d = mat.aligned v.mark a b c d := by
  rw [u.reading_of_pair_preferences partition slots,v.reading_of_pair_preferences partition slots,nondegenerate]
  cases mat.aligned u.mark a b c d <;> cases mat.aligned v.mark a b c d <;> cases base <;> decide

open LocalizedChemicalRingPromotionAggregation

/-- The signed balance of the actual molecular readings is fixed by the
counts of aligned and opposed within-pair preferences for these marks. -/
theorem balance_of_pair_preferences (trials : List (Trial mat)) (partition : Partition mat)
    {a b c d : Nat} (slots : partition.order = [a,b,c,d]) (g : Geometry) {base : RS}
    (nondegenerate : readback? g [a,b,c,d] = some base) :
    let aligned := trials.countP fun t => mat.aligned t.mark a b c d
    let opposed := trials.countP fun t => !mat.aligned t.mark a b c d
    readingBalance (trials.map fun t => (geometric g t.actual t.reflected).map Reading.actual) =
      if base = .R then (aligned : Int) - opposed else (opposed : Int) - aligned := by
  dsimp only
  induction trials with
  | nil => cases base <;> rfl
  | cons t ts ih =>
    rw [List.map_cons,t.reading_of_pair_preferences partition slots,nondegenerate]
    unfold readingBalance at ih ⊢
    cases side : mat.aligned t.mark a b c d <;> cases base <;>
      simp [side,readingScore,RS.swap] at ih ⊢ <;> omega

/-- Exact cancellation under the proposed signed-sum policy for any
population of completed two-pair trials. For four marks a refusal has two
aligned and two opposed readings. -/
theorem cancellation_iff_equal_counts (trials : List (Trial mat)) (partition : Partition mat)
    {a b c d : Nat} (slots : partition.order = [a,b,c,d]) (g : Geometry) {base : RS}
    (nondegenerate : readback? g [a,b,c,d] = some base) :
    completedAggregate (trials.map fun t => (geometric g t.actual t.reflected).map Reading.actual) = some none ↔
      (trials.countP fun t => mat.aligned t.mark a b c d) =
      (trials.countP fun t => !mat.aligned t.mark a b c d) := by
  unfold completedAggregate DeclarativeCIP.ProductionOccurrenceRules456.promotionAggregate
  rw [completed_balance,balance_of_pair_preferences trials partition slots g nondegenerate]
  cases base <;> simp only [if_true,reduceCtorEq,if_false] <;> split
  all_goals first | (split <;> simp <;> omega) | (simp; omega)

/-- A complete population can be inspected as soon as its reference
geometry has a hand, regardless of whether its marks agree. -/
structure PopulationReading {m p omitted} {e : Experiment m p omitted} (c : Classified e) (g : Geometry) where
  reference : RS
  coordinates : readback? g c.partition.order = some reference

def Classified.read? {cExp : Experiment m p omitted} (c : Classified cExp) (g : Geometry) :
    Option (PopulationReading c g) := do
  let ⟨hand,h⟩ ← (readback? g c.partition.order).attach
  return ⟨hand,h⟩

def Partition.preserves (part : Partition mat) (k : Nat) : Bool :=
  match part.order with
  | [a,b,c,d] => mat.aligned k a b c d
  | _ => false

theorem Partition.four_slots (part : Partition mat) :
    ∃ a b c d, part.order = [a,b,c,d] := by
  have h := part.classes
  unfold Matrix.partitionOK at h
  split at h
  · exact ⟨_,_,_,_,by assumption⟩
  · contradiction

variable {c : Classified e} {g : Geometry}

def PopulationReading.atMark (s : PopulationReading c g) (k : Nat) : Reading :=
  let hand := if c.partition.preserves k then s.reference else s.reference.swap
  ⟨hand,hand.swap⟩

theorem PopulationReading.geometric (s : PopulationReading c g) (t : Trial c.matrix) :
    Recursive.geometric g t.actual t.reflected = some (s.atMark t.mark) := by
  obtain ⟨a,b,x,y,slots⟩ := c.partition.four_slots
  have base := s.coordinates
  rw [slots] at base
  simp [t.reading_of_pair_preferences c.partition slots,base,atMark,Partition.preserves,slots]

/-- Return exactly one signed reading for each eligible atom, in incident
order. Every row equals geometric readback from its two unique priority orders. -/
def PopulationReading.votes (s : PopulationReading c g) :=
  (e.arms.map Arm.ligand).map fun k => (k,s.atMark k)

theorem PopulationReading.votes_from_trials (s : PopulationReading c g) :
    (c.partition.trials.map fun t => (t.mark,Recursive.geometric g t.actual t.reflected)) =
      (s.votes.map fun v => (v.1,some v.2)) := by
  simp only [s.geometric, votes,List.map_map,Function.comp_def]
  simpa only [List.map_map,Function.comp_def] using
    congrArg (List.map fun k => (k,some (s.atMark k))) c.partition.marks

def PopulationReading.proposed (s : PopulationReading c g) :=
  completedAggregate (s.votes.map fun v => some v.2.actual)

theorem PopulationReading.proposed_cancels_iff (s : PopulationReading c g) :
    s.proposed = some none ↔
      (e.arms.countP fun arm => c.partition.preserves arm.ligand) =
      (e.arms.countP fun arm => !c.partition.preserves arm.ligand) := by
  obtain ⟨a,b,x,y,slots⟩ := c.partition.four_slots
  have h := cancellation_iff_equal_counts c.partition.trials c.partition slots g (slots ▸ s.coordinates)
  have marks := c.partition.marks
  have votes := congrArg (List.map (fun v : Nat × Option Reading => v.2.map Reading.actual)) s.votes_from_trials
  simp only [List.map_map,Function.comp_def,Option.map_some] at votes
  rw [votes] at h
  have count (f : Nat → Bool) : c.partition.trials.countP (fun t => f t.mark) =
      e.arms.countP (fun a => f a.ligand) := by
    simpa only [List.countP_map,Function.comp_def] using congrArg (List.countP f) marks
  simpa only [PopulationReading.proposed,Partition.preserves,slots,
    count (fun k => c.matrix.aligned k a b x y),count (fun k => !c.matrix.aligned k a b x y)] using h

/-- The normal assignment procedure emits precisely the unanimous reading
of the four chemically derived votes. Mixed votes remain inspectable. -/
theorem PopulationReading.certificate_iff (s : PopulationReading c g) (r : Reading) :
    (c.certificate? g).map Certificate.reading = some r ↔
      ∀ k ∈ e.arms.map Arm.ligand, s.atMark k = r := by
  have every : (∀ t ∈ c.partition.trials, s.atMark t.mark = r) ↔
      ∀ k ∈ e.arms.map Arm.ligand, s.atMark k = r := by
    rw [← c.partition.marks]
    simp
  rw [← every]
  unfold Classified.certificate?
  cases first : c.partition.trials.head? with
  | none =>
    have size := congrArg List.length c.partition.marks
    simp [List.head?_eq_none_iff.mp first,e.four] at size
  | some t =>
    have member := List.mem_of_head? first
    have observed := s.geometric t
    simp only [first,Option.bind_eq_bind,Option.bind_some,observed]
    split
    · rename_i unanimous
      constructor
      · intro accepted
        have same : s.atMark t.mark = r := by simpa using accepted
        exact fun u inside => (Option.some.inj ((s.geometric u).symm.trans (unanimous u inside))).trans same
      · intro agree
        simpa using agree t member
    · rename_i different
      constructor
      · intro impossible; contradiction
      · intro agree
        exact (different (fun u inside => (s.geometric u).trans
          (congrArg some ((agree u inside).trans (agree t member).symm)))).elim

/-- An accepted assignment identifies all four public votes, with their
original ligand identifiers. -/
theorem Classified.votes_of_accepted (c : Classified e) {g : Geometry} {r : Reading}
    (accepted : (c.certificate? g).map Certificate.reading = some r) :
    (c.read? g).map PopulationReading.votes = some ((e.arms.map Arm.ligand).map (·,r)) := by
  cases observed : readback? g c.partition.order with
  | none =>
    obtain ⟨a,b,x,y,slots⟩ := c.partition.four_slots
    rw [slots] at observed
    unfold Classified.certificate? at accepted
    cases first : c.partition.trials.head? with
    | none => simp [first] at accepted
    | some t => simp [first,t.reading_of_pair_preferences c.partition slots,observed] at accepted
  | some h =>
    let s : PopulationReading c g := ⟨h,observed⟩
    have actual : c.read? g = some s := by
      simp [Classified.read?,Option.attach,observed,s]
    rw [actual,Option.map_some]
    exact congrArg some (List.map_congr_left fun k hk => congrArg (k,·) ((s.certificate_iff r).mp accepted k hk))

end TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.Trial.actual_of_pair_preferences
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.Trial.reading_of_pair_preferences
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.Trial.same_reading_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.balance_of_pair_preferences
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.cancellation_iff_equal_counts
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.PopulationReading.votes_from_trials
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.PopulationReading.certificate_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.PopulationReading.proposed_cancels_iff
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.Promotion.TwoPairPriority.Classified.votes_of_accepted
