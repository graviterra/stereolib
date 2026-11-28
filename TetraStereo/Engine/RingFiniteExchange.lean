import Mathlib.Data.Fintype.Pi
import TetraStereo.OneCenter.LocalizedRule3DemandDiscoveryAcyclic
import TetraStereo.Engine.RingObservedTreeMatch

/-! An exhaustive reference decision for the existence of an observed molecular
subtree correspondence. An entry is indexed by the whole source cursor,
including its incoming cut. Every reference to that cursor therefore shares
one image. This search enumerates all partial functions; it is intended for
the finite existence theorem, not for routine molecular evaluation. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingFiniteExchange
open LocalizedChemicalRing (Input)
open RingActivePairs (Site Arm)
open RingActivePairReport (Slot)
open RingNestedActivePair (Frame Reader)
open RingGeometryExchange (Carrier Frozen Exchange)
open RingGroupedCentre (cursor)
open RingRetainedChemicalTrace (observation?)

private instance arms (i : Input) : Fintype (Arm i) :=
  i.certified.localizedRerootCursorFintype (i.certified.certified.input.molecule.atomCount + 1)

private abbrev children {i : Input} (q : Arm i) := i.certified.executableLocalizedRerootChildren q
private abbrev Table (i j : Input) := Arm i → Option (Arm j)
private def marked {i : Input} (m : Option Nat) (q : Arm i) := m.elim 0 (fun a => RingGroupedMark.bit a q)

/-- Elementary conditions for a single finite partial function. The target
default only extends the image to arguments outside the proposed support. -/
private def Valid {i j : Input} (left : Reader i) (right : Reader j)
    (m n : Option Nat) (src : Arm i) (dst : Arm j) (t : Table i j) : Prop :=
  let image := fun q => (t q).getD dst
  t src = some dst ∧ ∀ q, (t q).isSome = true →
    (∀ a ∈ children q, (t a).isSome = true) ∧
    ((children q).map image).Perm (children (image q)) ∧
    observation? i q (children q).isEmpty = observation? j (image q) (children (image q)).isEmpty ∧
    left q.occurrence = right (image q).occurrence ∧ marked m q = marked n (image q)

private instance {i j : Input} (left : Reader i) (right : Reader j)
    (m n : Option Nat) (src : Arm i) (dst : Arm j) (t : Table i j) :
    Decidable (Valid left right m n src dst t) := by unfold Valid; infer_instance

/-- Exhaustive enumeration of finite partial cursor maps. No depth limit,
candidate ranking, atom renaming or proposed matching is an input. -/
def existsMatch {i j : Input} (left : Reader i) (right : Reader j)
    (m n : Option Nat) (src : Arm i) (dst : Arm j) : Bool :=
  decide (∃ t : Table i j, Valid left right m n src dst t)

/-- Exact semantics, including shared cursors and multiplicities of children.
The correspondence may be between two different molecules and readers. -/
theorem existsMatch_iff {i j : Input} (left : Reader i) (right : Reader j)
    (m n : Option Nat) (src : Arm i) (dst : Arm j) :
    existsMatch left right m n src dst = true ↔
      ∃ c : Carrier i j, c.domain src ∧ c.image src = dst ∧ Frozen c left right ∧
        ∀ q, c.domain q → marked m q = marked n (c.image q) := by
  unfold existsMatch
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨t,atRoot,each⟩
    let c : Carrier i j := {
      image := fun q => (t q).getD dst
      domain := fun q => (t q).isSome = true
      below := fun q h => (each q h).1
      children := fun q h => (each q h).2.1
      observation := fun q h => (each q h).2.2.1 }
    exact ⟨c,by change (t src).isSome = true; simp [atRoot],
      by change (t src).getD dst = dst; simp [atRoot],
      fun q h => (each q h).2.2.2.1,fun q h => (each q h).2.2.2.2⟩
  · rintro ⟨c,start,target,frozen,bits⟩
    classical
    let t : Table i j := fun q => if c.domain q then some (c.image q) else none
    have on (q : Arm i) : (t q).isSome = true ↔ c.domain q := by simp [t]
    have agrees (q : Arm i) (h : c.domain q) : (t q).getD dst = c.image q := by simp [t,h]
    refine ⟨t,by simp [t,start,target],?_⟩
    intro q included
    have h := (on q).mp included
    have sub (a : Arm i) (ha : a ∈ children q) := c.below q h a ha
    have eqMap : (children q).map (fun a => (t a).getD dst) = (children q).map c.image :=
      List.map_congr_left fun a ha => agrees a (sub a ha)
    simp only [eqMap,agrees q h]
    exact ⟨fun a ha => (on a).mpr (sub a ha),c.children q h,c.observation q h,frozen q h,bits q h⟩

/-- Decide precisely the primitive marked exchange used by the public refusal theorem. -/
def exchange {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (s u v : Slot) : Bool :=
  let m := some (RingGroupedTrials.atom fr s)
  existsMatch r r m m (cursor fr u) (cursor fr v)

theorem exchange_iff {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (s u v : Slot) :
    exchange fr r s u v = true ↔ Nonempty (Exchange fr r s u v) := by
  unfold exchange
  rw [existsMatch_iff]
  exact ⟨fun ⟨c,start,target,frozen,bits⟩ => ⟨⟨c,start,target,frozen,bits⟩⟩,
    fun ⟨e⟩ => ⟨e.carrier,e.atLigand,e.other,e.frozen,e.selected⟩⟩

/-- Fast triage. Different observed subtree signatures rule out an exchange.
A checked functional matching proves one exists. A proposed alignment that
fails its independent check leaves the answer open. -/
def quick? {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (s u v : Slot) :
    Option Bool :=
  match RingObservedTreeMatch.propose fr r (some (RingGroupedTrials.atom fr s)) u v with
  | none => some false
  | some rows =>
    match RingBranchMatching.check? fr r s u v rows with
    | some _ => some true
    | none => none

theorem quick_sound {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i)
    (s u v : Slot) {b : Bool} (hit : quick? fr r s u v = some b) :
    b = true ↔ Nonempty (Exchange fr r s u v) := by
  unfold quick? at hit
  cases proposal : RingObservedTreeMatch.propose fr r (some (RingGroupedTrials.atom fr s)) u v with
  | none =>
    obtain rfl : false = b := Option.some.inj (by simpa only [proposal] using hit)
    constructor
    · intro h; contradiction
    · rintro ⟨e⟩
      have present := RingObservedTreeMatch.propose_of_exchange e
      simp [proposal] at present
  | some rows =>
    cases check : RingBranchMatching.check? fr r s u v rows with
    | none => simp [proposal,check] at hit
    | some e =>
      obtain rfl : true = b := Option.some.inj (by simpa only [proposal,check] using hit)
      exact iff_of_true rfl ⟨e⟩

/-- Exact marked-pair decision. Evaluate the exhaustive search only when
the proposed alignment exists but fails the functional carrier check. -/
def decidePair {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (s u v : Slot) : Bool :=
  match quick? fr r s u v with
  | some verdict => verdict
  | none => exchange fr r s u v

theorem decidePair_iff {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (s u v : Slot) :
    decidePair fr r s u v = true ↔ Nonempty (Exchange fr r s u v) := by
  unfold decidePair
  cases h : quick? fr r s u v with
  | none => exact exchange_iff fr r s u v
  | some b => exact quick_sound fr r s u v h

/-- The unmarked correspondence checks exactly the molecular and frozen observations. -/
theorem unmarked_iff {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (u v : Slot) :
    existsMatch r r none none (cursor fr u) (cursor fr v) = true ↔
      Nonempty (RingObservedTreeMatch.Unmarked fr r u v) := by
  rw [existsMatch_iff]
  exact ⟨fun ⟨c,start,target,frozen,_⟩ => ⟨⟨c,start,target,frozen⟩⟩,
    fun ⟨e⟩ => ⟨e.carrier,e.start,e.target,e.frozen,fun _ _ => rfl⟩⟩

/-- A negative verdict excludes every functional exchange for this mark and pair. -/
theorem no_exchange_iff {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) (s u v : Slot) :
    exchange fr r s u v = false ↔ ¬ Nonempty (Exchange fr r s u v) := by
  rw [← exchange_iff,Bool.eq_false_iff]

/-- Exhaustive reference decision for the entire per-nomination certificate.
The fast tree matcher remains preferable when producing concrete witnesses. -/
def allNominations {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) : Bool :=
  (List.finRange 4).all fun s => (List.finRange 4).any fun u => (List.finRange 4).any fun v =>
    u != v && decidePair fr r s u v

theorem allNominations_iff {i : Input} {f : Site i} (fr : Frame i f) (r : Reader i) :
    allNominations fr r = true ↔ RingLigandExchange.PerNomination fr r := by
  simp [allNominations,RingLigandExchange.PerNomination,decidePair_iff,bne_iff_ne]

end TetraStereo.Engine.RingFiniteExchange

assert_kernel_only TetraStereo.Engine.RingFiniteExchange.existsMatch
assert_kernel_only TetraStereo.Engine.RingFiniteExchange.existsMatch_iff
assert_kernel_only TetraStereo.Engine.RingFiniteExchange.exchange_iff
assert_kernel_only TetraStereo.Engine.RingFiniteExchange.unmarked_iff
assert_kernel_only TetraStereo.Engine.RingFiniteExchange.allNominations_iff
assert_kernel_only TetraStereo.Engine.RingFiniteExchange.quick_sound
assert_kernel_only TetraStereo.Engine.RingFiniteExchange.decidePair_iff
