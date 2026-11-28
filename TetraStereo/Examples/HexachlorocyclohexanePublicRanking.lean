import TetraStereo.Engine.RingOppositeHandSequences
import TetraStereo.Examples.HexachlorocyclohexanePublicWords
import TetraStereo.Examples.HexachlorocyclohexaneEarlierTie
import TetraStereo.Examples.AntipodalCyclohexaneRanking

/-! Actual four-slot order on every carbon of fully written hexachlorocyclohexane. -/
set_option autoImplicit false
namespace TetraStereo.Examples.HexachlorocyclohexanePublicRanking
open Engine OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingGroupedTrials (atom)
open RingGroupedCentre (cursor)
open RingGroupedReport (origin)
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey)
open BlueBookHexachlorocyclohexane (molecule site exchange)
open HexachlorocyclohexaneFamily (fixedFrame forwardSite hand)
open HexachlorocyclohexaneSignedOrder (winner direction fields trial_order signedWord)
open AntipodalCyclohexaneWords (publicRead)
open HexachlorocyclohexanePublicWords (ring_word)
open AntipodalCyclohexaneRanking (slotNumber compare_distinct_atoms)
open LocalizedGenericMarkedRecalculation (readback?)
open private frame_perm from TetraStereo.Examples.DecalinFrames
open private graphRows from TetraStereo.Examples.HexachlorocyclohexanePublicStore
open private slot_injective from TetraStereo.Engine.RingAtomicFramePriority
attribute [local instance] lexOrd

private def row (r : Fin 6) (win : Bool) := if win
  then [r.val+6,(r.val+1)%6,(r.val+5)%6,r.val+12] else fixedFrame r.val
def ranked (r : Fin 6) (p : Fin 32) (rev : Bool) := row r (winner p rev)

private abbrev z := RingAtomicNeighborOrder.atomicNumber molecule
private theorem member {i : Input} (graph : i.molecule = molecule) (root : i.certified.Atom)
    (r : Fin 6) (atRoot : root.val = r.val) (fr : RingNestedActivePair.Frame i (origin i root))
    (s : Fin 4) : atom fr s ∈ fixedFrame r.val := by
  have perm := frame_perm fr
  have same : root = fr.center.val := Option.some.inj
    ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).2
  rw [graph,←same,atRoot] at perm
  exact (perm.trans (graphRows r.val r.isLt)).mem_iff.mp (List.mem_map_of_mem (List.mem_finRange s))

private theorem positions (r : Fin 6) (win : Bool) : ∀ a ∈ fixedFrame r.val, ∀ b ∈ fixedFrame r.val,
    (z a ≠ z b → compare (z a) (z b) = compare ((row r win).idxOf b) ((row r win).idxOf a)) ∧
    (a ≠ b → z a = z b → (a = site r true 1 ∧ b = site r false 1) ∨
      (b = site r true 1 ∧ a = site r false 1)) := by
  fin_cases r <;> cases win <;> decide +kernel

private theorem exchange_arms (r : Fin 6) : exchange r.val (site r true 1) = site r false 1 := by
  fin_cases r <;> decide +kernel

private theorem arm_order (r : Fin 6) (win : Bool) :
    (if win then Ordering.gt else .lt) = compare ((row r win).idxOf (site r false 1))
      ((row r win).idxOf (site r true 1)) := by fin_cases r <;> cases win <;> decide +kernel

private theorem opposite_words (p : Fin 32) (rev : Bool) :
    let w := signedWord p true rev .R
    signedWord p true rev .S = RingOppositeHandSequences.complement w ∧
    signedWord p false rev .R = RingOppositeHandSequences.opposite w ∧
    signedWord p false rev .S = RingOppositeHandSequences.complement (RingOppositeHandSequences.opposite w) := by
  fin_cases p <;> cases rev <;> decide +kernel

/-- The arbitrary-length classification applies directly to the completed native
trial keys on the two ring arms, with arbitrary nominated-atom words. -/
theorem path_trial {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (r : Fin 6) (atRoot : root.val = r.val) (fr : RingNestedActivePair.Frame i (origin i root))
    (u v : Fin 4) (U : atom fr u = site r true 1) (V : atom fr v = site r false 1)
    (p : Fin 32) (signs : ∀ k, readback? (RingWrittenPHReadings.geometry i.spatial)
      (fixedFrame (forwardSite r k)) = some (hand p k)) (rev : Bool) (x y : Key)
    (hx : RingFullPathEligibility.key? i (publicRead i root) rev (cursor fr u) = some x)
    (hy : RingFullPathEligibility.key? i (publicRead i root) rev (cursor fr v) = some y)
    (m n : RingRetainedChemicalTrace.Word) :
    let w := HexachlorocyclohexaneSignedOrder.signedWord p true rev .R
    compare (trialKey x m) (trialKey y n) =
      (if w = RingOppositeHandSequences.opposite w then compare m n else
       if w = w.reverse then (if w.head? = some true then .gt else .lt)
       else compare (RingOppositeHandSequences.paired w)
         (RingOppositeHandSequences.paired (RingOppositeHandSequences.opposite w))) ∧
    compare (trialKey x m) (trialKey y n) = direction p rev := by
  have crossed : exchange r.val (atom fr u) = atom fr v := by rw [U,V,exchange_arms]
  obtain ⟨xx,yy,hxx,hyy,early,lower⟩ :=
    HexachlorocyclohexaneEarlierTie.earlier graph geom root r atRoot fr u v crossed rev
  obtain rfl := Option.some.inj (hxx.symm.trans hx)
  obtain rfl := Option.some.inj (hyy.symm.trans hy)
  have left := ring_word graph geom root r atRoot fr u true U rev p signs
  have right := ring_word graph geom root r atRoot fr v false V rev p signs
  obtain ⟨swapL,opp,swapR⟩ := opposite_words p rev
  have L : RingOppositeHandSequences.Readings (publicRead i root) rev (cursor fr u) (signedWord p true rev .R) :=
    ⟨left [] .R,(left [] .S).trans (congrArg some swapL),left [.lowercase] .R⟩
  have R : RingOppositeHandSequences.Readings (publicRead i root) rev (cursor fr v)
      (RingOppositeHandSequences.opposite (signedWord p true rev .R)) :=
    ⟨(right [] .R).trans (congrArg some opp),(right [] .S).trans (congrArg some swapR),
      (right [.lowercase] .R).trans (congrArg some opp)⟩
  exact ⟨RingOppositeHandSequences.from_readings L R hx hy early lower m n,
    trial_order p rev _ _ early lower (fields p true rev hx (left []) (left [.lowercase] .R))
      (fields p false rev hy (right []) (right [.lowercase] .R)) m n⟩

/-- Compare the native keys of any two actual ligands, including a ligand
with itself. The five auxiliary signs are measured in fixed molecular frames. -/
theorem frame_order {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (r : Fin 6) (atRoot : root.val = r.val) (fr : RingNestedActivePair.Frame i (origin i root))
    (p : Fin 32) (signs : ∀ k, readback? (RingWrittenPHReadings.geometry i.spatial)
      (fixedFrame (forwardSite r k)) = some (hand p k))
    (rev : Bool) (ks : Fin 4 → Key)
    (got : RingFullPathPublication.keys? fr (publicRead i root) rev = some ks) (a b : Fin 4) :
    compare (trialKey (ks a) []) (trialKey (ks b) []) =
      compare ((ranked r p rev).idxOf (atom fr b)) ((ranked r p rev).idxOf (atom fr a)) := by
  have key (s : Fin 4) : RingFullPathEligibility.key? i (publicRead i root) rev (cursor fr s) = some (ks s) :=
    RingActivePairReport.four_at got s
  have reads (s : Fin 4) : Reads i (publicRead i root) rev (cursor fr s) (ks s) := by
    obtain ⟨k,hk,exactK⟩ := RingFullPathEligibility.key_exact (RingChemicalGraphProof.ready geom _)
      rev (cursor fr s) (RingGroupedCentre.valid fr s) (fr.direction s).property.1
    exact (exactK _).mpr (Option.some.inj ((key s).symm.trans hk))
  have forward (u v : Fin 4) (U : atom fr u = site r true 1) (V : atom fr v = site r false 1) :
      compare (trialKey (ks u) []) (trialKey (ks v) []) =
        compare ((ranked r p rev).idxOf (atom fr v)) ((ranked r p rev).idxOf (atom fr u)) := by
    have ord := (path_trial graph geom root r atRoot fr u v U V p signs rev _ _ (key u) (key v) [] []).2
    rw [U,V]
    exact ord.trans (arm_order r (winner p rev))
  by_cases same : atom fr a = atom fr b
  · have eq : a = b := slot_injective fr (Subtype.ext (Fin.ext (by
        simpa only [RingAtomicFramePriority.slotNeighbor_val] using same)))
    subst b
    simp
  have pos := positions r (winner p rev) _ (member graph root r atRoot fr a) _ (member graph root r atRoot fr b)
  by_cases diff : z (atom fr a) ≠ z (atom fr b)
  · have different : slotNumber fr a ≠ slotNumber fr b := by
      unfold slotNumber
      rw [graph]
      exact diff
    have ord := compare_distinct_atoms fr (reads a) (reads b) different [] []
    unfold slotNumber at ord
    rw [graph] at ord
    exact ord.trans (pos.1 diff)
  rcases pos.2 same (of_not_not diff) with ⟨A,B⟩ | ⟨B,A⟩
  · exact forward a b A B
  · calc
      _ = (compare (trialKey (ks b) []) (trialKey (ks a) [])).swap := Std.OrientedCmp.eq_swap ..
      _ = _ := congrArg Ordering.swap (forward b a B A)
      _ = _ := (Std.OrientedCmp.eq_swap ..).symm

end TetraStereo.Examples.HexachlorocyclohexanePublicRanking
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicRanking.frame_order
assert_kernel_only TetraStereo.Examples.HexachlorocyclohexanePublicRanking.path_trial
