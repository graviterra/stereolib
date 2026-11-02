import TetraStereo.OneCenter.AuthoritativeSingleWedgeOccurrenceReadiness

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

/-! A finite four-role sorting lemma. Roles are H=0, left carbon=1, Br=2, right
carbon=3. This does not assert that a source has this comparison table: the actual
family must derive that table independently, including every prior-rule tie. -/

namespace TetraStereo.UniversalProof.NextFrontier.ParsedParityRoleSort

open TetraStereo.OneCenter
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput

def roleRank (leftLabel rightLabel : RS) (role : Fin 4) : Nat :=
  if role = 0 then 0 else if role = 2 then 3 else
    if (if role = 1 then leftLabel else rightLabel) = .R then 2 else 1

def roleDecision (leftLabel rightLabel : RS) (first second : Fin 4) :
    ConstitutionalRule5Comparison :=
  { ordering := compare (roleRank leftLabel rightLabel first)
      (roleRank leftLabel rightLabel second)
    pseudo := decide ((first = 1 ∧ second = 3 ∨ first = 3 ∧ second = 1) ∧
      leftLabel ≠ rightLabel) }

def roleCallback (roles : Fin 4 → Fin 4) (leftLabel rightLabel : RS)
    (first second : Fin 4) : Option ConstitutionalDescriptorHierarchyComparison :=
  some (aromaticCanonicalRule3Through5DescriptorComparison
    (roleDecision leftLabel rightLabel (roles first) (roles second)))

def expectedRoles (leftLabel : RS) : List (Fin 4) :=
  if leftLabel = .R then [2, 1, 3, 0] else [2, 3, 1, 0]

def roleCoherent (roles : Fin 4 → Fin 4) (leftLabel rightLabel : RS) :
    List (Fin 4) → Bool
  | [] => true
  | first :: rest =>
      rest.all (fun second =>
        (roleDecision leftLabel rightLabel (roles first) (roles second)).ordering == .gt) &&
      roleCoherent roles leftLabel rightLabel rest

theorem roleCoherent_iff (roles : Fin 4 → Fin 4) (leftLabel rightLabel : RS) :
    ∀ order, roleCoherent roles leftLabel rightLabel order = true ↔
      order.Pairwise (fun first second =>
        (roleDecision leftLabel rightLabel (roles first) (roles second)).ordering = .gt)
  | [] => by simp [roleCoherent]
  | first :: rest => by
      rw [roleCoherent, Bool.and_eq_true, List.all_eq_true, List.pairwise_cons,
        roleCoherent_iff]
      simp

/-- All 24 placements of four distinct roles have the same physical order and one
pseudo comparison for opposite arms. Equal arm labels force actual sort refusal. -/
theorem role_sort_summary (roles : Fin 4 → Fin 4) (injective : Function.Injective roles)
    (leftLabel rightLabel : RS) :
    (sortFourLocalizedLigandsTracked (roleCallback roles leftLabel rightLabel)).map
      (fun result => (result.highestFirst.map roles, result.pseudoComparisons,
        roleCoherent roles leftLabel rightLabel result.highestFirst)) =
      if leftLabel = rightLabel then none else some (expectedRoles leftLabel, 1, true) := by
  cases leftLabel <;> cases rightLabel <;> revert injective roles <;> decide +kernel

private theorem actual_sort_eq (source : AuthoritativeChemicalInput) {fuel : Nat}
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame fuel)
    (roles : Fin 4 → Fin 4) (leftLabel rightLabel : RS)
    (compared : ∀ first second, first ≠ second →
      source.compareAromaticCanonicalOccurrenceRule3Through5At keys first second =
        roleDecision leftLabel rightLabel (roles first) (roles second)) :
    source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys =
      sortFourLocalizedLigandsTracked (roleCallback roles leftLabel rightLabel) := by
  apply sortLocalizedLigandsTrackedFrom_eq_of_callback_ne
    (source.compareAromaticCanonicalOccurrenceRule3Through5At? keys)
    (roleCallback roles leftLabel rightLabel)
  · intro first second different
    simp only [compareAromaticCanonicalOccurrenceRule3Through5At?, roleCallback,
      compared first second different]
  · exact List.nodup_finRange 4

private theorem actual_pairwise (source : AuthoritativeChemicalInput) {fuel : Nat}
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame fuel)
    (roles : Fin 4 → Fin 4) (leftLabel rightLabel : RS)
    (compared : ∀ first second, first ≠ second →
      source.compareAromaticCanonicalOccurrenceRule3Through5At keys first second =
        roleDecision leftLabel rightLabel (roles first) (roles second)) :
    ∀ order : List (Fin 4), order.Nodup →
      order.Pairwise (fun first second =>
        (roleDecision leftLabel rightLabel (roles first) (roles second)).ordering = .gt) →
      order.Pairwise (fun first second =>
        (source.compareAromaticCanonicalOccurrenceRule3Through5At keys first second).ordering = .gt) := by
  intro order
  induction order with
  | nil => intro _ _; exact List.Pairwise.nil
  | cons first rest ih =>
      intro distinct ordered
      have fresh := (List.nodup_cons.mp distinct).1
      have tailDistinct := (List.nodup_cons.mp distinct).2
      have headOrder := (List.pairwise_cons.mp ordered).1
      have tailOrder := (List.pairwise_cons.mp ordered).2
      apply List.pairwise_cons.mpr
      refine ⟨?_, ih tailDistinct tailOrder⟩
      intro second member
      have different : first ≠ second := by rintro rfl; exact fresh member
      rw [compared first second different]
      exact headOrder second member

/-- A proved actual comparison table yields the production safe sort, physical role
order, and exact pseudo count. No sorting success or coherence is supplied. -/
theorem actual_safe_sort_opposite (source : AuthoritativeChemicalInput) {fuel : Nat}
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame fuel)
    (roles : Fin 4 → Fin 4) (injective : Function.Injective roles)
    (leftLabel rightLabel : RS) (opposite : leftLabel ≠ rightLabel)
    (compared : ∀ first second, first ≠ second →
      source.compareAromaticCanonicalOccurrenceRule3Through5At keys first second =
        roleDecision leftLabel rightLabel (roles first) (roles second)) :
    ∃ tracked,
      source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = some tracked ∧
      tracked.highestFirst.map roles = expectedRoles leftLabel ∧
      tracked.pseudoComparisons = 1 := by
  have summary := role_sort_summary roles injective leftLabel rightLabel
  rw [if_neg opposite] at summary
  cases computed : sortFourLocalizedLigandsTracked (roleCallback roles leftLabel rightLabel) with
  | none => simp [computed] at summary
  | some tracked =>
      simp only [computed, Option.map_some, Option.some.injEq, Prod.mk.injEq] at summary
      have actual : source.aromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys =
          some tracked := (actual_sort_eq source keys roles leftLabel rightLabel compared).trans computed
      have perm := sortFourLocalizedLigandsTracked_perm
        (roleCallback roles leftLabel rightLabel) tracked computed
      have distinct := perm.symm.nodup (List.nodup_finRange 4)
      have coherent := (source.aromaticCanonicalOccurrenceRule3Through5OrderCoherent_eq_true_iff
        keys tracked.highestFirst).mpr
          (actual_pairwise source keys roles leftLabel rightLabel compared tracked.highestFirst
            distinct ((roleCoherent_iff roles leftLabel rightLabel tracked.highestFirst).mp summary.2.2))
      refine ⟨tracked, ?_, summary.1, summary.2.1⟩
      simp only [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?, actual,
        Bind.bind, Option.bind, coherent, ite_true]

/-- Equal actual arm labels refuse the central sort for every placement of the roles. -/
theorem actual_safe_sort_equal (source : AuthoritativeChemicalInput) {fuel : Nat}
    (keys : source.AromaticCanonicalOccurrenceRule3Through5KeyFrame fuel)
    (roles : Fin 4 → Fin 4) (injective : Function.Injective roles) (label : RS)
    (compared : ∀ first second, first ≠ second →
      source.compareAromaticCanonicalOccurrenceRule3Through5At keys first second =
        roleDecision label label (roles first) (roles second)) :
    source.safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder? keys = none := by
  have summary := role_sort_summary roles injective label label
  rw [if_pos rfl] at summary
  have absent : sortFourLocalizedLigandsTracked (roleCallback roles label label) = none := by
    cases computed : sortFourLocalizedLigandsTracked (roleCallback roles label label) with
    | none => rfl
    | some tracked => simp [computed] at summary
  have actual := (actual_sort_eq source keys roles label label compared).trans absent
  simp only [safeAromaticCanonicalOccurrenceRule3Through5TrackedOrder?, actual,
    Bind.bind, Option.bind]

end TetraStereo.UniversalProof.NextFrontier.ParsedParityRoleSort
