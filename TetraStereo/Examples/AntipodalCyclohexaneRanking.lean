import TetraStereo.Examples.AntipodalCyclohexaneWords
import TetraStereo.Examples.AntipodalCyclohexaneEarlierTie

/-! At either hydroxyl-bearing carbon, atomic number decides the oxygen and
hydrogen positions. The two methylene arms are ranked by their remote hands. -/
set_option autoImplicit false
namespace TetraStereo.Examples.AntipodalCyclohexaneRanking
open Engine OneCenter CertifiedLocalizedCIPInput
open LocalizedChemicalRing (Input)
open RingGroupedTrials (atom)
open RingGroupedCentre (cursor)
open RingGroupedReport (origin)
open RingFullPathEligibility (Key Reads)
open RingFullPathTrialReadings (trialKey)
open RingRetainedChemicalTrace (Word)
open AntipodalCyclohexaneWords (ringArm publicRead ring_word)
open AntipodalCyclohexaneHands (molecule frameRow)
open LocalizedGenericMarkedRecalculation (readback?)
open private frame_perm from TetraStereo.Examples.DecalinFrames
open private slot_injective from TetraStereo.Engine.RingAtomicFramePriority
attribute [local instance] lexOrd

def ranked (r : Fin 2) (far : RS) : List Nat :=
  let l := ringArm r 0
  let t := ringArm r 1
  let o := if r.val = 0 then 6 else 13
  let h := if r.val = 0 then 7 else 14
  if far = .R then [o,l,t,h] else [o,t,l,h]

private abbrev z := RingAtomicNeighborOrder.atomicNumber molecule
private def arms (r : Fin 2) : List Nat := if r.val = 0 then [6,1,5,7] else [13,4,2,14]

private theorem neighbors (r : Fin 2) : (RingAtomicNeighborOrder.neighbors molecule (3*r.val)).Perm (arms r) := by
  apply (RingStereoSiblingPass.legal_order _ _).perm.trans
  fin_cases r <;> decide +kernel

private theorem member {i : Input} (graph : i.molecule = molecule) (root : i.certified.Atom)
    (r : Fin 2) (atRoot : root.val = 3*r.val) (fr : RingNestedActivePair.Frame i (origin i root))
    (s : Fin 4) : atom fr s ∈ arms r := by
  have perm := frame_perm fr
  have same : root = fr.center.val := Option.some.inj
    ((i.certified.localizedOccurrenceDescriptorCenter?_eq_some_iff _ _).mp fr.recognized).2
  rw [graph,←same,atRoot] at perm
  exact (perm.trans (neighbors r)).mem_iff.mp (List.mem_map_of_mem (List.mem_finRange s))

private theorem atomic_head {i : Input} {f : RingActivePairs.Site i} (fr : RingNestedActivePair.Frame i f)
    (s : Fin 4) :
    ∃ tail, (RingRetainedChemicalPreorder.keyFor (fr.direction s)).atomic.word =
      [RingAtomicNeighborOrder.atomicNumber i.molecule (atom fr s)] :: tail := by
  let a := (RingAtomicFramePriority.slotNeighbor fr s).val
  let k := RingRetainedChemicalPreorder.keyFor (fr.direction s)
  have hit := RingRetainedChemicalPreorder.read_key (fr.direction s)
  have written := RingAtomicNeighborOrder.written i a
  have number := RingPyramidalConstitution.key_atomic (q := cursor fr s)
    (RingAtomicFramePriority.slot_current fr s) written hit
  have row := ((RingRetainedChemicalTrace.key_source hit).formed .atomic).2
  simp only [RingRetainedChemicalTrace.Key.column,RingRetainedChemicalTrace.Observation.atStage] at row
  have id : a.val = atom fr s := RingAtomicFramePriority.slotNeighbor_val fr s
  rw [←id,RingAtomicNeighborOrder.atomicNumber,written]
  exact ⟨_,by simpa only [number] using row⟩

abbrev slotNumber {i : Input} {f : RingActivePairs.Site i} (fr : RingNestedActivePair.Frame i f) (s : Fin 4) :=
  RingAtomicNeighborOrder.atomicNumber i.molecule (atom fr s)

/-- Distinct first-atom numbers decide the full trial, including arbitrary marks. -/
theorem compare_distinct_atoms {i : Input} {f : RingActivePairs.Site i}
    (fr : RingNestedActivePair.Frame i f) {a b : Fin 4}
    {read : RingNestedActivePair.Reader i} {rev : Bool} {x y : Key}
    (rx : Reads i read rev (cursor fr a) x) (ry : Reads i read rev (cursor fr b) y)
    (different : slotNumber fr a ≠ slotNumber fr b) (m n : Word) :
    compare (trialKey x m) (trialKey y n) = compare (slotNumber fr a) (slotNumber fr b) := by
  obtain ⟨u,hu⟩ := RingFullPathConstitution.through_extends fr rx
  obtain ⟨v,hv⟩ := RingFullPathConstitution.through_extends fr ry
  obtain ⟨_,ha⟩ := atomic_head fr a
  obtain ⟨_,hb⟩ := atomic_head fr b
  simp only [trialKey,hu,hv,RingFullPathConstitution.word,RingRetainedChemicalPreorder.orderWord,
    ha,hb,List.cons_append,List.compare_cons_cons]
  cases eqn : compare (slotNumber fr a) (slotNumber fr b) with
  | lt => rfl
  | gt => rfl
  | eq => exact (different (compare_eq_iff_eq.mp eqn)).elim

def handAt (h : RS) (s : Fin 2) := if s.val = 0 then h else h.swap

private theorem positions : ∀ (r : Fin 2) (h : RS), ∀ a ∈ arms r, ∀ b ∈ arms r,
    (z a ≠ z b → compare (z a) (z b) = compare ((ranked r h).idxOf b) ((ranked r h).idxOf a)) ∧
    (a ≠ b → z a = z b → ∃ s t : Fin 2, a = ringArm r s ∧ b = ringArm r t ∧ s ≠ t) := by decide +kernel

private theorem exchanged : ∀ (r s t : Fin 2), s ≠ t →
    AntipodalCyclohexaneEarlierTie.exchange (ringArm r s) = ringArm r t := by decide +kernel

private theorem signed_order : ∀ (r s t : Fin 2) (h : RS), s ≠ t →
    let x := RingFullPathTrialReadings.bitWord [handAt h s == .R]
    let y := RingFullPathTrialReadings.bitWord [handAt h t == .R]
    compare [x] [y] ≠ .eq ∧ compare [x] [y] =
      compare ((ranked r h).idxOf (ringArm r t)) ((ranked r h).idxOf (ringArm r s)) := by decide +kernel

private theorem fields {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (r : Fin 2) (atRoot : root.val = 3*r.val) (fr : RingNestedActivePair.Frame i (origin i root))
    (a : Fin 4) (s : Fin 2) (id : atom fr a = ringArm r s)
    (h : RS) (sense : readback? (RingWrittenPHReadings.geometry i.spatial)
      (frameRow r) = some h)
    (rev : Bool) (k : Key) (got : RingFullPathEligibility.key? i (publicRead i root) rev (cursor fr a) = some k) :
    k.bestFourB = [true] ∧ k.fixedR = [handAt (if rev then h.swap else h) s == .R] := by
  let value := handAt (if rev then h.swap else h) s
  have R := ring_word graph geom root r atRoot fr a s id rev h sense [] .R
  have S := ring_word graph geom root r atRoot fr a s id rev h sense [] .S
  have F := ring_word graph geom root r atRoot fr a s id rev h sense [.lowercase] .R
  change RingFullPathPairs.pairs? _ _ _ _ _ = some [value == .R] at R
  change RingFullPathPairs.pairs? _ _ _ _ _ = some [value == .S] at S
  change RingFullPathRule5.word? _ _ _ _ _ = some [value == .R] at F
  unfold RingFullPathEligibility.key? at got
  rw [R,S,F] at got
  cases u : RingRetainedStereoRefinement.priority i (publicRead i root) rev [] (cursor fr a) <;>
    cases l : RingRetainedStereoRefinement.priority i (publicRead i root) rev [.lowercase] (cursor fr a) <;>
    simp [u,l] at got
  subst k
  exact ⟨by cases value <;> rfl,rfl⟩

/-- All earlier rule components agree on the two ring arms. The
fixed-R words are opposite singleton bits, for both geometry readings. -/
theorem deciding_rule {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (r : Fin 2) (atRoot : root.val = 3*r.val) (fr : RingNestedActivePair.Frame i (origin i root))
    (a b : Fin 4) (left right : Fin 2) (distinct : left ≠ right)
    (A : atom fr a = ringArm r left) (B : atom fr b = ringArm r right)
    (h : RS) (sense : readback? (RingWrittenPHReadings.geometry i.spatial) (frameRow r) = some h)
    (rev : Bool) :
    let g := if rev then h.swap else h
    ∃ x y, RingFullPathEligibility.key? i (publicRead i root) rev (cursor fr a) = some x ∧
      RingFullPathEligibility.key? i (publicRead i root) rev (cursor fr b) = some y ∧
      x.throughFourA = y.throughFourA ∧ x.bestFourB = [true] ∧ y.bestFourB = [true] ∧
      x.fourC = y.fourC ∧ x.fixedR = [handAt g left == .R] ∧ y.fixedR = [handAt g right == .R] := by
  have cross : AntipodalCyclohexaneEarlierTie.exchange (atom fr a) = atom fr b := by
    rw [A,B,exchanged r left right distinct]
  obtain ⟨x,y,hx,hy,early,lower⟩ :=
    AntipodalCyclohexaneEarlierTie.earlier graph geom root r atRoot fr a b cross rev
  obtain ⟨a4,a5⟩ := fields graph geom root r atRoot fr a left A h sense rev x hx
  obtain ⟨b4,b5⟩ := fields graph geom root r atRoot fr b right B h sense rev y hy
  exact ⟨x,y,hx,hy,early,a4,b4,lower,a5,b5⟩

/-- Strict native priority at both hydroxyl-bearing carbons on either geometry. This compares
the completed public keys from every actual slot, including self-comparisons. -/
theorem frame_order {i : Input} (graph : i.molecule = molecule)
    (geom : LocalizedChemicalRing.coordinatesAdmitted i = true) (root : i.certified.Atom)
    (r : Fin 2) (atRoot : root.val = 3*r.val) (fr : RingNestedActivePair.Frame i (origin i root))
    (h : RS) (sense : readback? (RingWrittenPHReadings.geometry i.spatial)
      (frameRow r) = some h)
    (rev : Bool) (ks : Fin 4 → Key)
    (got : RingFullPathPublication.keys? fr (publicRead i root) rev = some ks) (a b : Fin 4) :
    compare (trialKey (ks a) []) (trialKey (ks b) []) =
      compare ((ranked r (if rev then h.swap else h)).idxOf (atom fr b))
        ((ranked r (if rev then h.swap else h)).idxOf (atom fr a)) := by
  let g := if rev then h.swap else h
  have key (s : Fin 4) : RingFullPathEligibility.key? i (publicRead i root) rev (cursor fr s) = some (ks s) :=
    RingActivePairReport.four_at got s
  have reads (s : Fin 4) : Reads i (publicRead i root) rev (cursor fr s) (ks s) := by
    obtain ⟨k,hk,exactK⟩ := RingFullPathEligibility.key_exact (RingChemicalGraphProof.ready geom _)
      rev (cursor fr s) (RingGroupedCentre.valid fr s) (fr.direction s).property.1
    exact (exactK _).mpr (Option.some.inj ((key s).symm.trans hk))
  have pos := positions r g _ (member graph root r atRoot fr a) _ (member graph root r atRoot fr b)
  by_cases same : atom fr a = atom fr b
  · have eq : a = b := slot_injective fr (Subtype.ext (Fin.ext (by
        simpa only [RingAtomicFramePriority.slotNeighbor_val] using same)))
    subst b
    simp
  by_cases diff : z (atom fr a) ≠ z (atom fr b)
  · have different : RingAtomicNeighborOrder.atomicNumber i.molecule (atom fr a) ≠
        RingAtomicNeighborOrder.atomicNumber i.molecule (atom fr b) := graph ▸ diff
    have ord := compare_distinct_atoms fr (reads a) (reads b) different [] []
    unfold slotNumber at ord
    rw [graph] at ord
    exact ord.trans (pos.1 diff)
  obtain ⟨s,t,A,B,ne⟩ := pos.2 same (of_not_not diff)
  obtain ⟨x,y,hx,hy,early,a4,b4,lower,a5,b5⟩ :=
    deciding_rule graph geom root r atRoot fr a b s t ne A B h sense rev
  have ex : x = ks a := Option.some.inj (hx.symm.trans (key a))
  have ey : y = ks b := Option.some.inj (hy.symm.trans (key b))
  subst x
  subst y
  obtain ⟨strict,dir⟩ := signed_order r s t g ne
  simp only [trialKey,early,lower,a4,b4,a5,b5,List.compare_cons_cons,Std.ReflCmp.compare_self,Ordering.eq_then]
  change _ = compare ((ranked r g).idxOf (atom fr b)) ((ranked r g).idxOf (atom fr a))
  rw [A,B,←dir]
  cases c : compare [RingFullPathTrialReadings.bitWord [handAt g s == .R]]
      [RingFullPathTrialReadings.bitWord [handAt g t == .R]] <;> simp_all [g]

end TetraStereo.Examples.AntipodalCyclohexaneRanking
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneRanking.frame_order
assert_kernel_only TetraStereo.Examples.AntipodalCyclohexaneRanking.deciding_rule
