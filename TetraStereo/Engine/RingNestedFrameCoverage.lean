import TetraStereo.Engine.RingFrameCoverage

set_option autoImplicit false

namespace TetraStereo.Engine.RingChemicalPriority.ReferenceFrame
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation Recursive

/-- A previously visited atom can occur as a duplicate or as the edge toward
the parent. It cannot be a new real outward auxiliary occurrence. -/
theorem no_outward_return {m : RawMolecule} {p : List Nat} {i : Nat}
    (seen : i ∈ p) : occurrence? m (p ++ [i]) = none := by
  cases p with
  | nil => simp at seen
  | cons a ps =>
    let next (n : RawMolecule.CanonicalBranchNode) (j : Nat) :=
      (m.canonicalChildren n).find? fun child => child.atom == j && !child.forcedLeaf
    have one : occurrence? m ((a :: ps) ++ [i]) = (occurrence? m (a :: ps)).bind (fun c => next c i) := by
      by_cases bound : a < m.atomCount <;>
        simp [occurrence?,guard,bound,next,List.foldlM_append,List.foldlM_cons]
    rw [one]
    cases found : occurrence? m (a :: ps) with
    | none => rfl
    | some n =>
      change next n i = none
      cases edge : next n i with
      | none => rfl
      | some child =>
        have sel : (m.canonicalChildren n).find? (fun c => c.atom == i && !c.forcedLeaf) = some child := edge
        have both := Bool.and_eq_true_iff.mp (List.find?_some (p := fun c => c.atom == i && !c.forcedLeaf) (a := child) sel)
        have atId := eq_of_beq both.1
        have real : child.forcedLeaf = false := by simpa using both.2
        have fresh := (mem_canonicalChildren m n child (List.mem_of_find?_eq_some sel)).2.1 real
        have addr := OccurrenceSchedule.occurrence_address found
        have member : i ∈ n.history := List.mem_reverse.mp (addr ▸ seen)
        exact False.elim (fresh (atId ▸ member))

private theorem prior_fixed {m g p i j} (b : Basis m g p i j) (old : i ∈ p ∨ j ∈ p) :
    b.initial.1 = b.initial.2 ∧ b.initial.1 ≠ .eq := by
  have cannot (pair : ReferenceDistance.Pair m p i j) : False := by
    rcases old with h | h
    · have found := pair.left.reached
      rw [no_outward_return h] at found
      contradiction
    · have found := pair.right.reached
      rw [no_outward_return h] at found
      contradiction
  cases b with
  | atomic _ _ _ _ _ w _ | fourth _ w _ => cases w <;> simp [Basis.initial]
  | constitution c strict => exact ⟨rfl,strict⟩
  | stereo pair _ _ _ | tied pair _ => exact False.elim (cannot pair)

/-- If a compared ligand is a prior atom on the rooted path, the current
outward-inventory rule can only certify a fixed strict relation to a distinct
ligand. This constrains both mirror reversal and promotion eligibility. -/
theorem prior_comparison {m g p} (rows : List (Row m g p)) {i j : Nat}
    (old : i ∈ p ∨ j ∈ p) (ne : i ≠ j) :
    orderAt (entries rows) false i j = orderAt (entries rows) true i j ∧
      orderAt (entries rows) false i j ≠ some .eq := by
  simp only [orderAt,if_neg ne,Bool.false_eq_true,if_false,if_true]
  induction rows with
  | nil => simp [entries]
  | cons r rs ih =>
    by_cases eqn : (i,j) = (r.i,r.j)
    · have hk := beq_iff_eq.mpr eqn
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj eqn
      simpa [entries,List.lookup_cons,hk] using prior_fixed r.basis old
    · simpa [entries,List.lookup_cons,beq_eq_false_iff_ne.mpr eqn] using ih

theorem prior_not_eligible {m g p} (f : MolecularFrame m g p) {i} (old : i ∈ p) :
    i ∉ marks f.ids (entries f.rows) := by
  intro marked
  obtain ⟨j,_,good⟩ := List.any_eq_true.mp (List.mem_filter.mp marked).2
  obtain ⟨ne,equal⟩ := Bool.and_eq_true_iff.mp good
  exact (prior_comparison f.rows (Or.inl old) (bne_iff_ne.mp ne)).2 (eq_of_beq equal)

private theorem reached_parent {m g pre k a} (f : MolecularFrame m g (pre ++ [k,a])) : k ∈ f.ids := by
  have h := congrArg List.reverse (OccurrenceSchedule.occurrence_address f.reached)
  have hist : f.focus.history = a :: k :: pre.reverse := by simpa using h
  have real : f.focus.forcedLeaf = false := by
    by_contra bad
    have leaf : f.focus.forcedLeaf = true := by simpa using bad
    have h4 := f.four
    rw [f.incident] at h4
    simp [occurrenceLigandCursors,CanonicalRerootCursor.children,leaf] at h4
  rw [f.incident]
  cases tail : pre.reverse with
  | nil => simp [occurrenceLigandCursors,CanonicalRerootCursor.children,CanonicalRerootCursor.neighbors,
      canonicalOriginalParent?,real,hist,tail]
  | cons b xs => simp [occurrenceLigandCursors,CanonicalRerootCursor.children,CanonicalRerootCursor.neighbors,
      canonicalOriginalParent?,real,hist,tail]

/-- All successful promotions at a proper auxiliary occurrence have zero
unmarked pair reversals under the outward-inventory comparison rules. Any
incident ancestor is ineligible; the three remaining ligands must tie. -/
theorem Frame.nested_reversals {m g pre k a} (f : Frame m g (pre ++ [k,a])) :
    f.reversals = 0 := by
  obtain ⟨u,v,w,z,perm,uv,rest⟩ := f.tie_shape
  have old : k ∈ pre ++ [k,a] := by simp
  have has : k ∈ [u,v,w,z] := perm.mem_iff.mpr (reached_parent f.toMolecularFrame)
  have dist := perm.nodup_iff.mpr f.distinct
  simp only [List.nodup_cons,List.mem_cons,not_or,List.not_mem_nil,not_false_eq_true,
    List.nodup_nil,and_true] at dist
  have outside {x y : Nat} (ne : x ≠ y)
      (tie : orderAt (entries f.rows) false x y = some .eq) : k ≠ x ∧ k ≠ y := by
    constructor
    · rintro rfl
      exact (prior_comparison f.rows (Or.inl old) ne).2 tie
    · rintro rfl
      exact (prior_comparison f.rows (Or.inr old) ne).2 tie
  have h1 := outside dist.1.1 uv
  rcases rest with uw | wz
  · have h2 := outside dist.1.2.1 uw
    have kz : k = z := by simpa [h1.1,h1.2,h2.2] using has
    subst z
    have ord := (prior_comparison f.rows (Or.inr old) dist.1.2.2).1
    simp [f.three_tied_reversals perm uv uw,crossed,ord]
  · have h2 := outside dist.2.2 wz
    simp [h1.1,h1.2,h2.1,h2.2] at has

theorem Population.nested_signedDescriptor {m g pre k a}
    (s : Population m g (pre ++ [k,a])) :
    s.signedDescriptor = (survivingHand (OneCenter.LocalizedChemicalRingPromotionAggregation.readingBalance
      (s.hands false))).map (fun h => .chiral h) := by
  simp [s.signedDescriptor_eq,s.frame.nested_reversals]

end TetraStereo.Engine.RingChemicalPriority.ReferenceFrame

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.no_outward_return
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.prior_comparison
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.prior_not_eligible
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Frame.nested_reversals
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.nested_signedDescriptor

namespace TetraStereo.Engine.RingChemicalPriority.ReferenceFrame
open OneCenter LocalizedGenericMarkedRecalculation Recursive
open LocalizedMarkedTerminalGaugeSwap (readback_swap12 readback_swap23 readback_swap34)

/-- Under the three-ligand promotion, the singleton can be senior or junior.
The bit records which of the two unmarked ligands precedes its partner. -/
def threeOrder (senior : Bool) (d a b c : Nat) (forward : Bool) : List Nat :=
  if senior then if forward then [d,a,b,c] else [d,a,c,b]
  else if forward then [a,b,c,d] else [a,c,b,d]

private theorem cycle_order (g : Geometry) (senior : Bool) (d a b c : Nat) :
    readback? g (threeOrder senior d b c a true) = readback? g (threeOrder senior d a b c true) := by
  cases senior
  · change readback? g [b,c,a,d] = readback? g [a,b,c,d]
    rw [readback_swap23 g b a c d,readback_swap12 g a b c d]
    cases readback? g [a,b,c,d] with
    | none => rfl
    | some h => cases h <;> rfl
  · change readback? g [d,b,c,a] = readback? g [d,a,b,c]
    rw [readback_swap34 g d b a c,readback_swap23 g d a b c]
    cases readback? g [d,a,b,c] with
    | none => rfl
    | some h => cases h <;> rfl

private theorem cycle_bit (g : Geometry) (s : Bool) (d a b c : Nat) (forward : Bool) :
    readback? g (threeOrder s d b c a forward) = readback? g (threeOrder s d a b c forward) := by
  cases forward
  · change readback? g (threeOrder s d b a c true) = readback? g (threeOrder s d a c b true)
    exact (cycle_order g s d b a c).symm
  · exact cycle_order g s d a b c

private theorem nested_trial {m g pre k a} {f : Frame m g (pre ++ [k,a])}
    (t : Trial f) {order : List Nat} (ranked : orders f.ids t.table false = [order]) :
    ∃ h : RS, readback? g order = some h ∧ t.outcome.reading? = some ⟨h,h.swap⟩ := by
  cases out : t.outcome with
  | tied i j ne mem tie no => simp [no false] at ranked
  | assigned l r hl hr read observed =>
    have same : l = order := by simpa [hl] using ranked
    subst order
    have raw := (t.chemical_letter hl hr observed).1
    have mirrored := t.mirror_hand
    simp only [Trial.hand?,out,Outcome.reading?,Option.map_some,f.nested_reversals] at mirrored
    have opposite : read.reflected = read.actual.swap := by simpa using mirrored
    refine ⟨read.actual,raw,?_⟩
    cases read
    simp_all [Outcome.reading?]

/-- The three marked orders are recovered from the actual pair tables. Each
remaining branch occupies the next position under exactly one promotion. -/
structure CyclicRunners {m g p} (s : Population m g p) where
  first : Trial s.frame
  second : Trial s.frame
  third : Trial s.frame
  complete : s.trials.Perm [first,second,third]
  distinct : [first.mark,second.mark,third.mark].Nodup
  singleton : Nat
  senior : Bool
  x : Bool
  y : Bool
  z : Bool
  firstOrder : orders s.frame.ids first.table false =
    [threeOrder senior singleton first.mark second.mark third.mark x]
  secondOrder : orders s.frame.ids second.table false =
    [threeOrder senior singleton second.mark third.mark first.mark y]
  thirdOrder : orders s.frame.ids third.table false =
    [threeOrder senior singleton third.mark first.mark second.mark z]
  runners : [if x then second.mark else third.mark,
    if y then third.mark else first.mark, if z then first.mark else second.mark].Nodup

/-- Three completed strict nested promotions agree whenever each unmarked
ligand comes next once. This conclusion requires only marked molecular orders
and holds for all coordinates and all spellings of the atoms. -/
theorem Population.nested_consensus_of_cyclic_runners {m g pre k a}
    (s : Population m g (pre ++ [k,a])) (r : CyclicRunners s) :
    ∃ h : RS, s.consensus? = some (some ⟨h,h.swap⟩) := by
  have bits : r.x = r.y ∧ r.y = r.z := by
    have ok := r.runners
    cases x : r.x <;> cases y : r.y <;> cases z : r.z <;> simp_all
  obtain ⟨x,hx,rx⟩ := nested_trial r.first r.firstOrder
  obtain ⟨y,hy,ry⟩ := nested_trial r.second r.secondOrder
  obtain ⟨z,hz,rz⟩ := nested_trial r.third r.thirdOrder
  rw [← bits.1,cycle_bit,hx] at hy
  rw [← bits.2,← bits.1,cycle_bit,cycle_bit,hx] at hz
  obtain rfl : x = y := Option.some.inj hy
  obtain rfl : x = z := Option.some.inj hz
  refine ⟨x,(s.consensus_iff _).mpr ?_⟩
  intro t ht
  have inside := r.complete.mem_iff.mp ht
  simp only [List.mem_cons,List.not_mem_nil,or_false] at inside
  rcases inside with rfl | rfl | rfl <;> assumption

end TetraStereo.Engine.RingChemicalPriority.ReferenceFrame

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.nested_consensus_of_cyclic_runners

namespace TetraStereo.Engine.RingChemicalPriority.ReferenceFrame
open OneCenter LocalizedGenericMarkedRecalculation Recursive
open LocalizedChemicalRingPromotionAggregation
open LocalizedMarkedTerminalGaugeSwap (readback_swap12 readback_swap23 readback_swap34)

/-- Recover each vote directly from the sorted molecular incidences. A
persistent tie has no strict order and contributes no geometric hand. -/
theorem Trial.hand_from_actual_order {m g p} {f : Frame m g p} (t : Trial f) :
    t.hand? false = (orders f.ids t.table false).head?.bind (readback? g) := by
  cases out : t.outcome with
  | tied i j ne inside survives no => simp [Trial.hand?,out,Outcome.reading?,no false]
  | assigned a b ha hb r obs =>
    simp [Trial.hand?,out,Outcome.reading?,ha,(t.chemical_letter ha hb obs).1]

private theorem quarter_turn (g : Geometry) (a b c d : Nat) :
    readback? g [c,a,d,b] = (readback? g [a,b,c,d]).map RS.swap := by
  rw [readback_swap34 g c a b d,readback_swap12 g a c b d,readback_swap23 g a b c d]
  cases readback? g [a,b,c,d] with
  | none => rfl
  | some h => cases h <;> rfl

/-- Four eligible promotions with this cyclic pattern of strict orders
cancel on every geometry, in any enumeration of the marks. Only the
molecular orders enter the hypothesis. No handedness is assumed. -/
theorem Population.four_cycle_refuses {m g p} (s : Population m g p) {a b c d : Nat}
    (cycle : (s.trials.map (fun t => (orders s.frame.ids t.table false).head?)).Perm
      [some [a,b,c,d],some [c,a,d,b],some [d,c,b,a],some [b,d,a,c]]) :
    s.signedDescriptor = none := by
  apply s.signedDescriptor_none_iff.mpr
  have perm := cycle.map (fun order : Option (List Nat) => order.bind (readback? g))
  have h := readingBalance_perm perm
  simp only [List.map_map,Function.comp_def,← Trial.hand_from_actual_order,
    List.map_cons,List.map_nil,Option.bind_some] at h
  change readingBalance (s.hands false) = _ at h
  rw [h,quarter_turn g a b c d,quarter_turn g d c b a]
  cases readback? g [a,b,c,d] with
  | none => cases readback? g [d,c,b,a] with
    | none => rfl
    | some k => cases k <;> rfl
  | some j => cases readback? g [d,c,b,a] with
    | none => cases j <;> rfl
    | some k => cases j <;> cases k <;> rfl

end TetraStereo.Engine.RingChemicalPriority.ReferenceFrame

assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Trial.hand_from_actual_order
assert_kernel_only TetraStereo.Engine.RingChemicalPriority.ReferenceFrame.Population.four_cycle_refuses
