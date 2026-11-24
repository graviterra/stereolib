import TetraStereo.Engine.RingGroupedReport

set_option autoImplicit false

namespace TetraStereo.Engine.RingOrientation
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open LocalizedChemicalRing (Input)
open RingActivePairs (Site)
open RingActivePairReport (Slot Matrix Ranking)
open RingNestedActivePair (Frame Labels Reader)
open RingGroupedCentre (Arms)
open RingGroupedOrders (wins trialMatrix marks)
open RingGroupedTrials (Outcome Decision Marking)
open RingRetainedChemicalTrace (Word)
open LocalizedChemicalRingPhysicalSense (inputGeometry)
open LocalizedChemicalRingPromotionAggregation (readingScore readingBalance)
open RingChemicalPriority.ReferenceFrame (survivingHand)
attribute [local instance] lexOrd

/-- Orientation relative to the four written slots. A repeated priority makes
the alternating sign zero. Every inverted unordered pair reverses the sign. -/
def orientation {α : Type} [Ord α] (key : Slot → α) : Int :=
  let pairs := LocalizedChemicalRing.ConstitutionalPartition.pairs
  if pairs.any (fun p => compare (key p.1) (key p.2) == .eq) then 0
  else if pairs.countP (fun p => compare (key p.1) (key p.2) == .lt) % 2 = 0 then 1 else -1

/-- Materialize each molecular ligand word once per mark. -/
private def cachedOrientation {α : Type} [Ord α] (key : Slot → α) : Int :=
  let a := key 0
  let b := key 1
  let c := key 2
  let d := key 3
  let orders := [compare a b,compare a c,compare a d,compare b c,compare b d,compare c d]
  if orders.any (· == .eq) then 0 else if orders.countP (· == .lt) % 2 = 0 then 1 else -1

@[csimp] theorem orientation_cached : @orientation = @cachedOrientation := by
  funext α inst key
  let edges := LocalizedChemicalRing.ConstitutionalPartition.pairs.map (fun p => compare (key p.1) (key p.2))
  change orientation key = if edges.any (· == .eq) then 0 else if edges.countP (· == .lt) % 2 = 0 then 1 else -1
  simp only [edges,orientation,List.any_map,List.countP_map,Function.comp_def]

theorem orientation_zero {α : Type} [Ord α] [Std.LawfulEqOrd α] (key : Slot → α) :
    orientation key = 0 ↔ ¬ Function.Injective key := by
  unfold orientation
  dsimp only
  split_ifs with tie even
  · obtain ⟨p,mem,tied⟩ := List.any_eq_true.mp tie
    have lt := (LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp mem
    exact ⟨fun _ h => (ne_of_lt lt) (h (Std.compare_eq_eq_iff_eq.mp (beq_iff_eq.mp tied))), fun _ => rfl⟩
  all_goals
    have inj : Function.Injective key := by
      intro j k eqn
      by_contra ne
      have impossible (a b : Slot) (lt : a < b) (same : key a = key b) : False := by
        apply tie
        apply List.any_eq_true.mpr
        exact ⟨(a,b),(LocalizedChemicalRing.ConstitutionalPartition.pairs_spec _).mpr lt,by simp [same]⟩
      rcases lt_or_gt_of_ne ne with h | h
      · exact impossible j k h eqn
      · exact impossible k j h eqn.symm
    simp [inj]

theorem frame_read {i f} (fr : Frame i f) (g : Geometry) (o : RingJointObservations.Order) :
    readback? g (fr.atoms o.val) = if RingJointObservations.parity o then
      readback? g (fr.atoms (List.finRange 4)) else (readback? g (fr.atoms (List.finRange 4))).map RS.swap := by
  let atom (k : Slot) := (fr.atoms [k]).head!
  have lookup (k : Slot) : [atom 0,atom 1,atom 2,atom 3][k.val]? = some (atom k) := by fin_cases k <;> rfl
  have select (xs : List Slot) :
      atomsAt? [atom 0,atom 1,atom 2,atom 3] (xs.map Fin.val) = some (fr.atoms xs) := by
    induction xs with
    | nil => rfl
    | cons k ks ih =>
      unfold atomsAt? at ih ⊢
      simp only [List.map_cons,List.mapM_cons,lookup,ih]
      rfl
  have h := LocalizedMarkedConfigurationTransport.reordered_readback_partial g atom (o.val.map Fin.val)
    (show (o.val.map Fin.val).Perm [0,1,2,3] from o.property.map Fin.val)
  rw [select] at h
  exact h

private theorem rank_sign {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge)
    (rev : Bool) (w : Slot → Word) (r : Ranking (trialMatrix m w) rev) :
    orientation (wins a rev w) = if RingJointObservations.parity ⟨r.slots,r.perm⟩ then 1 else -1 := by
  let mat := trialMatrix m w
  let key := wins a rev w
  have strict := (RingGroupedOrders.rank_iff mat rev key (RingGroupedOrders.trial_order a m rev w)).mp
    (show (RingActivePairReport.rank? mat rev).isSome = true by rw [RingActivePairReport.rank_of r]; rfl)
  have no : ¬ LocalizedChemicalRing.ConstitutionalPartition.pairs.any
      (fun p => compare (key p.1) (key p.2) == .eq) = true := by
    rintro h
    obtain ⟨p,hp,v⟩ := List.any_eq_true.mp h
    exact (ne_of_lt ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp hp))
      (strict (Std.compare_eq_eq_iff_eq.mp (beq_iff_eq.mp v)))
  have cmp {j k : Slot} (ne : j ≠ k) :
      compare (key j) (key k) = .lt ↔ r.slots.idxOf k < r.slots.idxOf j := by
    rw [Std.OrientedCmp.eq_swap (cmp := compare),Ordering.swap_eq_lt,← RingGroupedOrders.trial_order a m rev w,Int.compare_eq_gt]
    simpa [RingOrdinaryPairRefusal.score,ne.symm] using (r.before_iff ne.symm).symm
  have count := (List.Perm.refl LocalizedChemicalRing.ConstitutionalPartition.pairs).countP_congr
    (p := fun p => compare (key p.1) (key p.2) == .lt)
    (p' := fun p => decide (r.slots.idxOf p.2 < r.slots.idxOf p.1))
    (fun p hp => Bool.eq_iff_iff.mpr (by
      simpa only [beq_iff_eq,decide_eq_true_eq] using
        cmp (ne_of_lt ((LocalizedChemicalRing.ConstitutionalPartition.pairs_spec p).mp hp))))
  have parity : ∀ ss ∈ (List.finRange 4).permutations',
      decide (LocalizedChemicalRing.ConstitutionalPartition.pairs.countP
        (fun p => decide (ss.idxOf p.2 < ss.idxOf p.1)) % 2 = 0) =
      RawMolecule.permutationIsEven (ss.map Fin.val) := by decide +kernel
  change orientation key = _
  unfold orientation
  dsimp only
  rw [if_neg no,count]
  have e := parity _ (List.mem_permutations'.mpr r.perm)
  change _ = if RawMolecule.permutationIsEven _ then _ else _
  rw [← e]
  simp

def baseline {i f} (fr : Frame i f) :=
  readingScore (readback? (inputGeometry i.certified) (fr.atoms (List.finRange 4)))

/-- This sign needs neither a proposed order nor the hand of a promoted trial. -/
theorem trial_score {i f fr read a m w} (o : @Outcome i f fr read a m w) :
    readingScore (o.hands.map Prod.fst) = baseline fr * orientation (wins a false w) := by
  cases o with
  | tied tie =>
    obtain ⟨j,k,ne,eqn⟩ := tie
    rw [(orientation_zero _).mpr (fun inj => ne (inj (eqn false))),mul_zero]
    rfl
  | ranked r s h k hp hq =>
    rw [rank_sign a m false w r]
    rw [frame_read fr _ ⟨r.slots,r.perm⟩] at hp
    cases even : RingJointObservations.parity ⟨r.slots,r.perm⟩ <;>
      cases base : readback? (inputGeometry i.certified) (fr.atoms (List.finRange 4)) with
      | none => simp [even,base] at hp
      | some b => cases b <;> cases h <;> simp_all [baseline,Outcome.hands,readingScore,RS.swap]

/-- The mark word uses only the occurrence tree below the physical ligand,
with the one chosen atom distinguished throughout the tree. -/
def markedWord {i f} (fr : Frame i f) (read : Reader i) (s k : Slot) : Word :=
  ((RingGroupedMark.arm? i read (RingGroupedTrials.atom fr s) (RingGroupedCentre.cursor fr k)).map
    (fun e => e.2.word)).getD []

private theorem word_eq {i f fr read s} (mark : @Marking i f fr read s)
    (ready : RingGroupedStereo.Ready f read) : mark.word = markedWord fr read s := by
  funext k
  obtain ⟨e,found⟩ := RingGroupedMark.arm_ready ready (RingGroupedTrials.atom fr s) (RingGroupedCentre.cursor fr k)
    (RingGroupedCentre.valid fr k) (fr.direction k).property.1
  have eqn := (mark.source k).unique (RingGroupedMark.arm_source found).2
  simp only [markedWord,found,Option.map_some,Option.getD_some,Marking.word,eqn]

/-- Excess of even strict orders over odd strict orders, with a zero for every
unresolved mark. Computed from the six pair comparisons of each mark. -/
def index {i f fr read} (a : @Arms i f fr read) : Int :=
  if (marks a).length < 3 then orientation (a.key false)
  else ((marks a).map fun s => orientation (wins a false (markedWord fr read s))).sum

theorem balance_from_geometry {i f fr read a m} (d : @Decision i f fr read a m)
    (ready : RingGroupedStereo.Ready f read) : d.balance false = baseline fr * index a := by
  cases d with
  | ordinary few o =>
    have obs := trial_score o
    have cmp (j k : Slot) : compare (wins a false RingGroupedTrials.OrdinaryWord j)
        (wins a false RingGroupedTrials.OrdinaryWord k) = compare (a.key false j) (a.key false k) := by
      change (compare _ _).then .eq = _
      exact Ordering.then_eq
    simpa only [Decision.balance,Decision.population,readingBalance,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,add_zero,index,if_pos few,orientation,cmp] using obs
  | promoted full ts listed =>
    have each (t : (s : Slot) × RingGroupedTrials.Trial a m s) :
        readingScore (t.2.outcome.hands.map Prod.fst) =
        baseline fr * orientation (wins a false (markedWord fr read t.1)) := by
      rw [← word_eq t.2.marking ready]
      exact trial_score t.2.outcome
    unfold Decision.balance readingBalance
    simp only [Decision.population,List.map_map]
    have h : ¬ (marks a).length < 3 := by omega
    rw [index,if_neg h,← listed,List.map_map]
    clear listed
    change (ts.map (fun t => readingScore (t.2.outcome.hands.map Prod.fst))).sum =
      baseline fr * (ts.map (fun t => orientation (wins a false (markedWord fr read t.1)))).sum
    induction ts with
    | nil => simp
    | cons t rest ih =>
      simp only [List.map_cons,List.sum_cons,mul_add] at ih ⊢
      rw [each,ih]

private theorem baseline_ne_zero {i f} (fr : Frame i f)
    (coordinates : LocalizedChemicalRing.coordinatesAdmitted i = true) : baseline fr ≠ 0 := by
  have valid := RingGroupedGeometry.calibrated coordinates fr _ (List.Perm.refl (List.finRange 4))
  unfold baseline
  cases obs : readback? (inputGeometry i.certified) (fr.atoms (List.finRange 4)) with
  | none => simp [obs] at valid
  | some hand => cases hand <;> decide

/-- Under coordinate admission, the raw comparisons alone determine whether
the centre issues a descriptor. No trial hand is an input to the index. -/
theorem refusal_iff {i f fr read a m} (d : @Decision i f fr read a m)
    (ready : RingGroupedStereo.Ready f read)
    (coordinates : LocalizedChemicalRing.coordinatesAdmitted i = true) :
    d.letters = none ↔ index a = 0 := by
  rw [d.refusal_iff,balance_from_geometry d ready,mul_eq_zero]
  simp [baseline_ne_zero fr coordinates]

/-- With an unreadable written frame, every strict order lacks a physical
hand. A trial can still complete when it establishes an enduring ligand tie. -/
theorem unreadable_trial_iff {i f fr read} (a : @Arms i f fr read) (m : Matrix a.edge)
    (w : Slot → Word)
    (flat : readback? (inputGeometry i.certified) (fr.atoms (List.finRange 4)) = none) :
    (RingGroupedTrials.outcome? a m w).isSome = true ↔ ¬Function.Injective (wins a false w) := by
  constructor
  · intro found
    obtain ⟨outcome,_⟩ := Option.isSome_iff_exists.mp found
    cases outcome with
    | tied witness =>
      obtain ⟨j,k,ne,h⟩ := witness
      exact fun inj => ne (inj (h false))
    | ranked r _ _ _ physical _ =>
      rw [frame_read fr _ ⟨r.slots,r.perm⟩,flat] at physical
      split at physical <;> contradiction
  · intro tied
    have witness : ∃ j k, j ≠ k ∧ wins a false w j = wins a false w k := by
      by_contra no
      exact tied (fun {j k} eqn => by by_contra ne; exact no ⟨j,k,ne,eqn⟩)
    simp [RingGroupedTrials.outcome?,witness]

theorem unreadable_completion {i f fr read a m} (d : @Decision i f fr read a m)
    (ready : RingGroupedStereo.Ready f read)
    (flat : readback? (inputGeometry i.certified) (fr.atoms (List.finRange 4)) = none) :
    d.letters = none := by
  rw [d.refusal_iff,balance_from_geometry d ready]
  simp [baseline,flat,readingScore]

end TetraStereo.Engine.RingOrientation
assert_kernel_only TetraStereo.Engine.RingOrientation.balance_from_geometry
assert_kernel_only TetraStereo.Engine.RingOrientation.refusal_iff
assert_kernel_only TetraStereo.Engine.RingOrientation.unreadable_trial_iff
