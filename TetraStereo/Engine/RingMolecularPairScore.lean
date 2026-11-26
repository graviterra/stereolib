import TetraStereo.Engine.RingBinaryPairScore
import TetraStereo.Engine.RingPairWordPopulation
import TetraStereo.Engine.RingUnitWordPopulation
import TetraStereo.Engine.RingChemicalGraphProof

/-! Hanson et al. (2018), Figure 8, encode each fixed-reference reading as an
unsigned binary integer. The molecular unit-class prefix determines when the
resulting integers may be compared. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingMolecularPairScore
open OneCenter RingStereoSiblingPass
open LocalizedChemicalRing (Input)
open RingActivePairs (Arm Site)
open RingNestedActivePair (Reader)
open RingRetainedChemicalTrace (Word)
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey bitWord)
open RingRetainedReferenceGroup (Listing Hit)
open RingBinaryPairScore (value)
attribute [local instance] lexOrd

/-- Independently ordered fixed-reference readings and an inventory of the
chiral occurrences in the original arm. The field `hand` describes the Rule 4a
branch before either reference is chosen. -/
structure Evidence (i : Input) (r : Reader i) (rev : Bool) (q : Arm i) (k : Key) where
  hand : Branch
  hits : List Hit
  right : List Bool
  left : List Bool
  classRead : RingRetainedUnitPass.Reading i r false q hand
  inventory : Listing i r q hits
  rRead : RingFullPathPairs.FullSource i r rev .R q right
  sRead : RingFullPathPairs.FullSource i r rev .S q left
  fixedRead : RingFullPathRule5.Word i r rev .R q k.fixedR
  earlier : k.throughFourA = hand.deep
  best : k.bestFourB = max right left

theorem evidence {i : Input} {f : Site i} {r : Reader i} (ready : RingGroupedStereo.Ready f r)
    {rev : Bool} (q : Arm i) (valid : i.certified.LocalizedRerootCursorValid q)
    (rooted : q.occurrence.val.root = f.val.root) {k : Key} (read : Reads i r rev q k) :
    Nonempty (Evidence i r rev q k) := by
  obtain ⟨p,hp⟩ := RingGroupedStereo.arm_ready ready q valid rooted
  obtain ⟨u,_,ar,as',_,du,_,hr,hs,hf,rfl⟩ := read
  obtain ⟨c,computed⟩ := RingOccurrenceStereo.rank_total ready false [] q valid rooted
  change RingRetainedUnitPass.atArm i r q = some c at computed
  have aligned := RingRetainedUnitPass.Reading.unique du (RingRetainedUnitPass.source i r rev _ _ computed)
  subst u
  exact ⟨⟨c,_,ar,as',RingRetainedUnitPass.source i r false _ _ computed,
    (RingGroupedStereo.arm_source hp).hits,hr,hs,hf,rfl,rfl⟩⟩

variable {i j : Input} {r : Reader i} {t : Reader j} {v w : Bool} {a : Arm i} {b : Arm j} {x y : Key}

/-- Exact number of chiral emissions, computable before either reference word. -/
def width (key : Key) : Nat :=
  RingUnitWordPopulation.serializedPopulation (key.throughFourA.getLast?.getD [])

/-- The complete Rule 4a word alone determines the length for either seed at
both pair-comparison stages, even when their traversal orders differ. -/
theorem source_width (l : Evidence i r v a x) (s : RS) (bits : List Bool) :
    (RingFullPathPairs.FullSource i r v s a bits ∨ RingFullPathRule5.Word i r v s a bits) →
      bits.length = width x := by
  have count := RingUnitWordPopulation.Listing.serializedPopulation l.inventory l.classRead
  have size : l.hits.length = width x := by simpa [width,l.earlier,Branch.deep] using count
  rintro (h | h)
  · exact (RingPairWordPopulation.word_length l.inventory h).trans size
  · exact (RingPairWordPopulation.rule5_length l.inventory h).trans size

theorem four_widths (l : Evidence i r v a x) (h : Evidence j t w b y)
    (tie : x.throughFourA = y.throughFourA) :
    l.right.length = l.hits.length ∧ l.left.length = l.hits.length ∧
    h.right.length = l.hits.length ∧ h.left.length = l.hits.length := by
  have widths := RingUnitWordPopulation.Listing.length_eq l.inventory h.inventory l.classRead h.classRead
    (l.earlier.symm.trans (tie.trans h.earlier))
  exact ⟨RingPairWordPopulation.word_length l.inventory l.rRead,
    RingPairWordPopulation.word_length l.inventory l.sRead,
    (RingPairWordPopulation.word_length h.inventory h.rRead).trans widths.symm,
    (RingPairWordPopulation.word_length h.inventory h.sRead).trans widths.symm⟩

private theorem max_length {p q : List Bool} {n : Nat} (hp : p.length = n) (hq : q.length = n) :
    (max p q).length = n := by
  rcases le_total p q with le | le
  · rwa [max_eq_right le]
  · rwa [max_eq_left le]

/-- Compare the two pairs of independently ordered binary integers exactly as
in Figure 8. All four widths follow from the preceding molecular tie. -/
theorem four_scores (l : Evidence i r v a x) (h : Evidence j t w b y)
    (tie : x.throughFourA = y.throughFourA) :
    compare x.bestFourB y.bestFourB =
      compare (max (value l.right) (value l.left)) (max (value h.right) (value h.left)) := by
  obtain ⟨lr,ls,hr,hs⟩ := four_widths l h tie
  rw [l.best,h.best,← RingBinaryPairScore.value_max _ _ (lr.trans ls.symm),
    ← RingBinaryPairScore.value_max _ _ (hr.trans hs.symm)]
  exact (RingBinaryPairScore.compare_value _ _ ((max_length lr ls).trans (max_length hr hs).symm)).symm

/-- Preserve all later rules and the supplied active marks. Only the two
fixed-reference bit fields are expressed as ordinary natural numbers. -/
def numericKey (k : Key) (mark : Word) : List (List Word) :=
  [k.throughFourA,[[[value k.bestFourB]]],[k.fourC],[[[value k.fixedR]]],[mark]]

theorem trial_score (l : Evidence i r v a x) (h : Evidence j t w b y) (m n : Word) :
    compare (trialKey x m) (trialKey y n) = compare (numericKey x m) (numericKey y n) := by
  unfold trialKey numericKey
  conv_lhs => rw [List.compare_cons_cons]
  conv_rhs => rw [List.compare_cons_cons]
  cases first : compare x.throughFourA y.throughFourA with
  | lt => rfl
  | gt => rfl
  | eq =>
    have tie := Std.compare_eq_eq_iff_eq.mp first
    obtain ⟨lr,ls,hr,hs⟩ := four_widths l h tie
    have bw : x.bestFourB.length = y.bestFourB.length := by
      rw [l.best,h.best]
      exact (max_length lr ls).trans (max_length hr hs).symm
    have counts := RingUnitWordPopulation.Listing.length_eq l.inventory h.inventory l.classRead h.classRead
      (l.earlier.symm.trans (tie.trans h.earlier))
    have fw := (RingPairWordPopulation.rule5_length l.inventory l.fixedRead).trans
      (counts.trans (RingPairWordPopulation.rule5_length h.inventory h.fixedRead).symm)
    simp [List.compare_cons_cons,RingBinaryPairScore.compare_bits,
      RingBinaryPairScore.compare_value _ _ bw,RingBinaryPairScore.compare_value _ _ fw]

/-- Every rooted ligand pair of every ready call, on either geometry. This
includes every promoted trial. No earlier tie, width, key, or final comparison
is an input to the theorem. -/
theorem all_ligands {i : Input} {r : Reader i} {f : Site i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (a b : Arm i) (va : i.certified.LocalizedRerootCursorValid a)
    (vb : i.certified.LocalizedRerootCursorValid b) (ra : a.occurrence.val.root = f.val.root)
    (rb : b.occurrence.val.root = f.val.root) :
    ∃ x y, RingFullPathEligibility.key? i r rev a = some x ∧ RingFullPathEligibility.key? i r rev b = some y ∧
      ∀ m n, compare (trialKey x m) (trialKey y n) = compare (numericKey x m) (numericKey y n) := by
  obtain ⟨x,hx,sx⟩ := RingFullPathEligibility.key_exact ready rev a va ra
  obtain ⟨y,hy,sy⟩ := RingFullPathEligibility.key_exact ready rev b vb rb
  obtain ⟨l⟩ := evidence ready a va ra ((sx x).mpr rfl)
  obtain ⟨h⟩ := evidence ready b vb rb ((sy y).mpr rfl)
  exact ⟨x,y,hx,hy,trial_score l h⟩

private theorem list_lt {α : Type} [LinearOrder α] [Ord α]
    (lt : ∀ x y : α, compare x y = .lt ↔ x < y)
    (eqn : ∀ x y : α, compare x y = .eq ↔ x = y) (a b : List α) :
    compare a b = .lt ↔ a < b := DeclarativeCIP.compareLex_eq_lt_iff_of compare lt eqn a b

private theorem trial_lt (a b : List (List Word)) : compare a b = .lt ↔ a < b := by
  apply list_lt _ (fun _ _ => Std.compare_eq_eq_iff_eq)
  intro x y
  apply list_lt _ (fun _ _ => Std.compare_eq_eq_iff_eq)
  intro x y
  apply list_lt _ (fun _ _ => Std.compare_eq_eq_iff_eq)
  intro x y
  exact list_lt (fun _ _ => Nat.compare_eq_lt) (fun _ _ => Std.compare_eq_eq_iff_eq) x y

theorem key_lt {i : Input} {r : Reader i} {f : Site i} (ready : RingGroupedStereo.Ready f r)
    (rev : Bool) (a b : Arm i) (va : i.certified.LocalizedRerootCursorValid a)
    (vb : i.certified.LocalizedRerootCursorValid b) (ra : a.occurrence.val.root = f.val.root)
    (rb : b.occurrence.val.root = f.val.root) {x y : Key}
    (ha : RingFullPathEligibility.key? i r rev a = some x)
    (hb : RingFullPathEligibility.key? i r rev b = some y) (m n : Word) :
    trialKey x m < trialKey y n ↔ numericKey x m < numericKey y n := by
  obtain ⟨u,v,hu,hv,eqn⟩ := all_ligands ready rev a b va vb ra rb
  obtain rfl := Option.some.inj (ha.symm.trans hu)
  obtain rfl := Option.some.inj (hb.symm.trans hv)
  rw [← trial_lt,← trial_lt,eqn]

end TetraStereo.Engine.RingMolecularPairScore
assert_kernel_only TetraStereo.Engine.RingMolecularPairScore.source_width
assert_kernel_only TetraStereo.Engine.RingMolecularPairScore.four_widths
assert_kernel_only TetraStereo.Engine.RingMolecularPairScore.four_scores
assert_kernel_only TetraStereo.Engine.RingMolecularPairScore.all_ligands
