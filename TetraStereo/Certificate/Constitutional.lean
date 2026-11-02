import Mathlib.Data.List.FinRange

set_option autoImplicit false

namespace TetraStereo.Certificate.Constitutional

/-!
Executable certificates for a deliberately bounded constitutional slice.  The independent
relation below requires a first unequal observed number after actual earlier ties.  Exhausting
the supplied observations never establishes priority.  A successful check concerns the supplied
observations; `ConstitutionalSource` separately binds them to actual source occurrences.
-/

structure Four (α : Type) where
  a : α
  b : α
  c : α
  d : α
  deriving DecidableEq, Repr

def Four.toList {α : Type} (values : Four α) : List α :=
  [values.a, values.b, values.c, values.d]

def Four.get {α : Type} (values : Four α) (index : Fin 4) : α :=
  if index = 0 then values.a else if index = 1 then values.b
  else if index = 2 then values.c else values.d

def Four.map {α β : Type} (f : α → β) (values : Four α) : Four β :=
  ⟨f values.a, f values.b, f values.c, f values.d⟩

/-- Strict priority comes from an observed first difference, never from a shorter observation. -/
def FirstDifference : List Nat → List Nat → Prop
  | left :: leftRest, right :: rightRest =>
      right < left ∨ (left = right ∧ FirstDifference leftRest rightRest)
  | _, _ => False

instance firstDifferenceDecidable (left right : List Nat) :
    Decidable (FirstDifference left right) := by
  cases left with
  | nil => exact isFalse (by simp [FirstDifference])
  | cons first rest =>
    cases right with
    | nil => exact isFalse (by simp [FirstDifference])
    | cons other others =>
      have := firstDifferenceDecidable rest others
      exact inferInstanceAs (Decidable (other < first ∨
        (first = other ∧ FirstDifference rest others)))

theorem FirstDifference.asymm {left right : List Nat}
    (forward : FirstDifference left right) : ¬ FirstDifference right left := by
  induction left generalizing right with
  | nil => simp [FirstDifference] at forward
  | cons first rest induction =>
    cases right with
    | nil => simp [FirstDifference] at forward
    | cons other others =>
      simp only [FirstDifference] at forward ⊢
      rcases forward with higher | ⟨equal, later⟩
      · rintro (lower | ⟨equal, _⟩) <;> omega
      · subst other
        rintro (lower | ⟨_, laterReverse⟩)
        · exact Nat.lt_irrefl _ lower
        · exact induction later laterReverse

structure LigandPrefix where
  rootAtomicNumber : Nat
  /-- `none` means unobserved, whereas `some []` is an observed empty child multiset. -/
  children : Option (List Nat)
  deriving DecidableEq, Repr

/-- Children, when supplied, are the entire sorted immediate sphere. -/
def LigandPrefix.WellFormed (observation : LigandPrefix) : Prop :=
  match observation.children with
  | none => True
  | some children => children.Pairwise (fun left right => right ≤ left)

instance (observation : LigandPrefix) : Decidable observation.WellFormed := by
  unfold LigandPrefix.WellFormed
  split <;> infer_instance

/-- Rule 1a first compares roots, then a complete supplied immediate sphere after equal roots. -/
def PrefixAbove (left right : LigandPrefix) : Prop :=
  right.rootAtomicNumber < left.rootAtomicNumber ∨
    (left.rootAtomicNumber = right.rootAtomicNumber ∧
      match left.children, right.children with
      | some leftChildren, some rightChildren => FirstDifference leftChildren rightChildren
      | _, _ => False)

instance (left right : LigandPrefix) : Decidable (PrefixAbove left right) := by
  unfold PrefixAbove
  cases left.children <;> cases right.children <;> infer_instance

theorem PrefixAbove.asymm {left right : LigandPrefix}
    (forward : PrefixAbove left right) : ¬ PrefixAbove right left := by
  rcases forward with higher | ⟨equal, later⟩
  · rintro (lower | ⟨equal, _⟩) <;> omega
  · rintro (lower | ⟨_, reverse⟩)
    · omega
    · cases leftChildren : left.children <;> cases rightChildren : right.children <;>
        simp only [leftChildren, rightChildren] at later reverse
      exact FirstDifference.asymm later reverse

structure RankingCertificate where
  highestFirst : Four Nat
  deriving DecidableEq, Repr

inductive RankingError where
  | outOfRange
  | repeatedSlot
  | unsortedObservation
  | incompleteOrNonStrict
  deriving DecidableEq, Repr

def decodeRanking (certificate : RankingCertificate) : Option (Four (Fin 4)) :=
  if ha : certificate.highestFirst.a < 4 then
    if hb : certificate.highestFirst.b < 4 then
      if hc : certificate.highestFirst.c < 4 then
        if hd : certificate.highestFirst.d < 4 then
          some ⟨⟨_, ha⟩, ⟨_, hb⟩, ⟨_, hc⟩, ⟨_, hd⟩⟩
        else none
      else none
    else none
  else none

def ConstitutionalRanks (observations : Four LigandPrefix)
    (ranking : Four (Fin 4)) : Prop :=
  ranking.toList.Pairwise (fun left right =>
    PrefixAbove (observations.get left) (observations.get right))

instance (observations : Four LigandPrefix) (ranking : Four (Fin 4)) :
    Decidable (ConstitutionalRanks observations ranking) :=
  inferInstanceAs (Decidable (ranking.toList.Pairwise _))

def checkRanking (observations : Four LigandPrefix) (certificate : RankingCertificate) :
    Except RankingError (Four (Fin 4)) :=
  match decodeRanking certificate with
  | none => .error .outOfRange
  | some ranking =>
    if ranking.toList.Nodup then
      if observations.toList.all (fun observation => decide observation.WellFormed) then
        if ConstitutionalRanks observations ranking then .ok ranking
        else .error .incompleteOrNonStrict
      else .error .unsortedObservation
    else .error .repeatedSlot

theorem four_distinct_cover : ∀ a b c d : Fin 4, [a, b, c, d].Nodup →
    ∀ slot : Fin 4, slot = a ∨ slot = b ∨ slot = c ∨ slot = d := by decide +kernel

theorem Four.perm_finRange (slots : Four (Fin 4)) (distinct : slots.toList.Nodup) :
    slots.toList.Perm (List.finRange 4) := by
  apply (List.perm_ext_iff_of_nodup distinct (List.nodup_finRange 4)).mpr
  intro slot
  simp only [List.mem_finRange, iff_true]
  rcases four_distinct_cover _ _ _ _ distinct slot with rfl | rfl | rfl | rfl <;>
    simp [Four.toList]

/-- Soundness is relative to the independent first-difference relation, not checker success. -/
theorem checkRanking_sound (observations : Four LigandPrefix) (certificate : RankingCertificate)
    (ranking : Four (Fin 4)) (accepted : checkRanking observations certificate = .ok ranking) :
    ranking.toList.Perm (List.finRange 4) ∧
      (∀ observation ∈ observations.toList, observation.WellFormed) ∧
      ConstitutionalRanks observations ranking := by
  unfold checkRanking at accepted
  split at accepted
  · contradiction
  · rename_i proposed decoded
    split at accepted
    · rename_i distinct
      split at accepted
      · rename_i well
        split at accepted
        · rename_i ordered
          cases accepted
          exact ⟨ranking.perm_finRange distinct,
            by simpa only [List.all_eq_true, decide_eq_true_eq] using well, ordered⟩
        · contradiction
      · contradiction
    · contradiction

def identityCertificate : RankingCertificate := ⟨⟨0, 1, 2, 3⟩⟩
def identityRanking : Four (Fin 4) := ⟨0, 1, 2, 3⟩

def ringObservations : Four LigandPrefix :=
  ⟨⟨9, none⟩, ⟨6, some [17, 6, 1]⟩, ⟨6, some [6, 1, 1]⟩, ⟨1, none⟩⟩

def nitrileObservations : Four LigandPrefix :=
  ⟨⟨9, none⟩, ⟨6, some [7, 7, 7]⟩, ⟨6, some [7, 6, 1]⟩, ⟨1, none⟩⟩

def secondSphereObservations : Four LigandPrefix :=
  ⟨⟨9, none⟩, ⟨6, some [6, 1, 1]⟩, ⟨6, some [1, 1, 1]⟩, ⟨1, none⟩⟩

theorem ring_checked : checkRanking ringObservations identityCertificate = .ok identityRanking := by
  rfl

theorem nitrile_checked : checkRanking nitrileObservations identityCertificate = .ok identityRanking := by
  rfl

theorem second_sphere_checked :
    checkRanking secondSphereObservations identityCertificate = .ok identityRanking := by
  rfl

theorem repeated_slot_rejected :
    checkRanking nitrileObservations ⟨⟨0, 1, 1, 3⟩⟩ = .error .repeatedSlot := by rfl

theorem out_of_range_rejected :
    checkRanking nitrileObservations ⟨⟨0, 1, 2, 4⟩⟩ = .error .outOfRange := by rfl

theorem missing_sphere_rejected :
    checkRanking { nitrileObservations with b := ⟨6, none⟩ } identityCertificate =
      .error .incompleteOrNonStrict := by rfl

theorem missing_duplicate_rejected :
    checkRanking { nitrileObservations with b := ⟨6, some [7]⟩ } identityCertificate =
      .error .incompleteOrNonStrict := by rfl

theorem skipped_earlier_difference_rejected :
    checkRanking { nitrileObservations with b := ⟨6, some [6, 6, 6]⟩ }
      identityCertificate = .error .incompleteOrNonStrict := by rfl

theorem unsorted_sphere_rejected :
    checkRanking { nitrileObservations with b := ⟨6, some [7, 6, 7]⟩ }
      identityCertificate = .error .unsortedObservation := by rfl

theorem inverted_ranking_rejected :
    checkRanking nitrileObservations ⟨⟨0, 2, 1, 3⟩⟩ =
      .error .incompleteOrNonStrict := by rfl

end TetraStereo.Certificate.Constitutional
