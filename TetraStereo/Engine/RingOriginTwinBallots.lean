import TetraStereo.Engine.RingPairwisePublication
import TetraStereo.Engine.RingPromotionSymmetry

/-! Finite refusal certificates for origin twins. Missing comparison coverage is
not a completed refusal. Strict trials cancel by parity of their actual rows. -/
set_option autoImplicit false
namespace TetraStereo.Engine.RingOriginTwinBallots
open OneCenter CertifiedLocalizedCIPInput LocalizedGenericMarkedRecalculation
open RingActivePairReport (Slot)
open RingPairwisePublication
open LocalizedChemicalRingPromotionAggregation (readingBalance)

/-- Exchange nominations, retaining the unmarked trial. -/
def move (a b : Slot) : Option Slot → Option Slot := Option.map (Equiv.swap a b)

def rowParity (d : Directions) : Bool :=
  RingJointObservations.parity ⟨rows d, rows_perm d⟩

def TrialValid (d : Data) (a b : Slot) (s : Option Slot) : Prop :=
  match d.marked false s, d.marked false (move a b s) with
  | some x, some y =>
    (strictData x = false ∧ strictData y = false) ∨
      (strictData x = true ∧ strictData y = true ∧ rowParity x ≠ rowParity y)
  | _, _ => False

instance (d : Data) (a b : Slot) (s : Option Slot) : Decidable (TrialValid d a b s) := by
  unfold TrialValid
  split <;> infer_instance

/-- Finite obligations only: ordinary tie, coverage, nomination transport and
opposite strict-row parity. The reflected matrices need no extra assumptions. -/
def Valid (d : Data) (a b : Slot) : Prop :=
  a ≠ b ∧ tied (d.ordinary false) a b = true ∧
  ((trials (d.ordinary false)).map (move a b)).Perm (trials (d.ordinary false)) ∧
  ∀ s ∈ trials (d.ordinary false), TrialValid d a b s

private theorem trial_valid {d : Data} {a b : Slot} {s : Option Slot}
    (h : TrialValid d a b s) : ∃ x y,
    d.marked false s = some x ∧ d.marked false (move a b s) = some y ∧
    ((strictData x = false ∧ strictData y = false) ∨
      (strictData x = true ∧ strictData y = true ∧ rowParity x ≠ rowParity y)) := by
  cases hx : d.marked false s <;> cases hy : d.marked false (move a b s) <;>
    simp_all [TrialValid]

instance (d : Data) (a b : Slot) : Decidable (Valid d a b) := by
  unfold Valid
  infer_instance

/-- Executable finite checker; no aggregate score or published label is checked. -/
def check (d : Data) (a b : Slot) : Bool := decide (Valid d a b)

theorem check_sound (d : Data) (a b : Slot) (ok : check d a b = true) : Valid d a b :=
  of_decide_eq_true ok

private theorem collect {A B : Type} (xs : List A) (f : A → Option B) (v : A → B)
    (complete : ∀ a ∈ xs, f a = some (v a)) : xs.mapM f = some (xs.map v) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.mapM_cons,List.map_cons]
    rw [complete a List.mem_cons_self,ih (fun b hb => complete b (List.mem_cons_of_mem a hb))]
    rfl

/-- The physical readback is determined by one baseline and the permutation
parity of each legal row. This includes a missing geometric baseline. -/
theorem refusal (d : Data) (a b : Slot) (valid : Valid d a b)
    (sense : Bool → List Slot → Option RS) (baseline : Option RS)
    (physical : ∀ x : Directions, sense false (rows x) =
      if rowParity x then baseline else baseline.map RS.swap) :
    d.publish sense = some none := by
  let read (s : Option Slot) : Option RS :=
    (d.marked false s).bind fun x => ballot x (sense false)
  have opposite : ∀ s ∈ trials (d.ordinary false),
      read (move a b s) = (read s).map RS.swap := by
    intro s hs
    obtain ⟨x,y,hx,hy,cases⟩ := trial_valid (valid.2.2.2 s hs)
    change ((d.marked false (move a b s)).bind _) = ((d.marked false s).bind _).map RS.swap
    rw [hx,hy]
    simp only [Option.bind_some]
    rcases cases with ⟨nx,ny⟩ | ⟨sx,sy,odd⟩
    · simp [ballot,nx,ny]
    · simp only [ballot,sx,sy,ite_true,physical]
      cases px : rowParity x <;> cases py : rowParity y <;>
        simp_all [Option.map_map]
      all_goals cases baseline with
        | none => rfl
        | some h => cases h <;> rfl
  have zero := RingChemicalPriority.ReferenceFrame.zero_of_opposite_transport
    (trials (d.ordinary false)) read (move a b) valid.2.2.1 opposite
  have ballots : d.ballots sense = some ((trials (d.ordinary false)).map fun s => (s,read s)) := by
    apply collect
    intro s hs
    obtain ⟨x,y,hx,hy,_⟩ := trial_valid (valid.2.2.2 s hs)
    simp [read,hx]
  unfold Data.publish
  rw [ballots]
  simp only [Option.map_some,List.map_map,Function.comp_def]
  unfold Data.letters
  change some ((RingChemicalPriority.ReferenceFrame.survivingHand
    (readingBalance ((trials (d.ordinary false)).map read))).map _) = _
  rw [zero]
  rfl

/-- Concrete geometry discharges the baseline law for every sorted trial row. -/
theorem frame_refusal {i : LocalizedChemicalRing.Input} {q : RingActivePairs.Site i}
    (fr : RingNestedActivePair.Frame i q) (g : Geometry) (d : Data) (a b : Slot)
    (valid : Valid d a b) :
    d.publish (fun _ row => readback? g (fr.atoms row)) = some none := by
  apply refusal d a b valid _ (readback? g (fr.atoms (List.finRange 4)))
  intro x
  exact RingOrientation.frame_read fr g ⟨rows x,rows_perm x⟩

assert_kernel_only frame_refusal
assert_kernel_only refusal
assert_kernel_only check_sound
end TetraStereo.Engine.RingOriginTwinBallots
