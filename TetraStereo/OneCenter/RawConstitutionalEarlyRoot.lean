import TetraStereo.OneCenter.ConstitutionalRootStageAvailability
import TetraStereo.OneCenter.RawFramedConstitutionalIndependence
import TetraStereo.UniversalProof.NextFrontier.FramedDescriptorSorting
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxRecDepth 10000

/-!
  RawConstitutionalEarlyRoot

  A computable early-root gate for the actual `RawMolecule` / `SmilesTetrahedral` occurrence
  pipeline, placed *before* the full auxiliary-state builder.

  ## What is checked

  For the actual original root `canonicalCenterRoot center` this module resolves

  * the actual shared framed profile `FrameRuntime.profile? mol root` (which contains the
    center-owned `CanonicalComparisonFrame.Frame`), and
  * the actual four-ligand occurrence frame `occurrenceLigandFrame? mol root`,

  and requires

  1. the frame roots are `Nodup`, and
  2. every distinct ordered pair of frame roots is *strictly* decided by the actual framed
     `FrameRuntime.compareBranch? ... CanonicalRuleStage.rule2 true` comparison (no `none`,
     no `Ordering.eq`).

  Condition 2 is evaluated by `pairwiseStrictRule2?`, which calls the production comparator
  directly.  No comparator, sort, frame, profile, or descriptor formula is copied or
  approximated.

  ## What is proved

  The general independence theorem is the canonical published one in
  `TetraStereo.OneCenter.RawFramedConstitutionalIndependence`
  (`framedOccurrenceFactAuthoritative?_state_independent`).  This module imports it and only
  supplies:

  * soundness of the computable Boolean gate (`earlyConstitutionalRootGate?_sound`);
  * the conversion of the gate's `PairwiseStrictOn` plus `Nodup` output to the canonical
    `RootsConstitutionallySeparated` hypothesis;
  * the gate-corollary `earlyConstitutionalRootGate?_independence`, which instantiates the
    canonical theorem at the original root and compares any state with the empty state.

  There is no duplicated generic independence proof here.

  ## Facade

  `tetrahedralOccurrenceFactEarlyRoot?` is a *companion* entry point, not a production migration:

  * if the gate succeeds, it runs the existing `framedOccurrenceFactAuthoritative?` at the empty
    state and packs the resulting `OccurrenceAuxFact` using the same packing formula as the public
    entry point with the empty state;
  * otherwise it calls the unchanged public `tetrahedralOccurrenceFactAuthoritative?`, i.e. the
    original full-auxiliary-state fallback.

  Chemical descriptor semantics are preserved: on the early path the descriptor, uppercase flag,
  decisive-rule slot and priority positions are those of the same `OccurrenceAuxFact` that the
  full-state path produces.  The diagnostic fields `evidenceSize` and `descriptorDependentPairs`
  are honest for the empty state used on the early path, so they generally differ from the
  full-state diagnostics.  Missing auxiliary facts are never interpreted as a nonchiral label.
-/

namespace TetraStereo
namespace OneCenter
namespace RawConstitutionalEarlyRoot

open RawMolecule
open TetraStereo.OneCenter.ConstitutionalRootStageAvailability
open TetraStereo.OneCenter.RawFramedConstitutionalIndependence

/-! ## Strict framed constitutional comparisons -/

/-- The actual framed Rule-2 comparison of two occurrence-root cursors is strict: it returns a
definite ordering other than constitutional equality. -/
def StrictRule2 (mol : RawMolecule) (profile : FrameRuntime.Profile) (fuel : ℕ)
    (left right : CanonicalRerootCursor) : Prop :=
  ∃ order : Ordering, order ≠ Ordering.eq ∧
    FrameRuntime.compareBranch? mol profile true fuel CanonicalRuleStage.rule2
      (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) = some order

/-- Computable version of `StrictRule2`, calling the actual production comparator. -/
def strictRule2B (mol : RawMolecule) (profile : FrameRuntime.Profile) (fuel : ℕ)
    (left right : CanonicalRerootCursor) : Bool :=
  match FrameRuntime.compareBranch? mol profile true fuel CanonicalRuleStage.rule2
      (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) with
  | some Ordering.lt => true
  | some Ordering.gt => true
  | _ => false

theorem strictRule2B_sound (mol : RawMolecule) (profile : FrameRuntime.Profile) (fuel : ℕ)
    (left right : CanonicalRerootCursor)
    (h : strictRule2B mol profile fuel left right = true) :
    StrictRule2 mol profile fuel left right := by
  unfold strictRule2B at h
  cases hc : FrameRuntime.compareBranch? mol profile true fuel CanonicalRuleStage.rule2
      (FrameRuntime.Cursor.actual left) (FrameRuntime.Cursor.actual right) with
  | none => simp [hc] at h
  | some order =>
      cases order with
      | lt => exact ⟨Ordering.lt, by decide, hc⟩
      | gt => exact ⟨Ordering.gt, by decide, hc⟩
      | eq => simp [hc] at h

/-- Every distinct ordered pair of frame roots is strictly decided by the actual framed Rule-2
comparison. -/
def PairwiseStrictOn (mol : RawMolecule) (profile : FrameRuntime.Profile) (fuel : ℕ)
    (roots : List CanonicalRerootCursor) : Prop :=
  ∀ left, left ∈ roots → ∀ right, right ∈ roots → left ≠ right →
    StrictRule2 mol profile fuel left right

/-- Computable pairwise strictness test.  The diagonal is never compared; both orientations of
each distinct unordered pair are required to be strict. -/
def pairwiseStrictRule2? (mol : RawMolecule) (profile : FrameRuntime.Profile) (fuel : ℕ) :
    List CanonicalRerootCursor → Bool
  | [] => true
  | left :: rest =>
      rest.all (fun right =>
        strictRule2B mol profile fuel left right &&
          strictRule2B mol profile fuel right left) &&
      pairwiseStrictRule2? mol profile fuel rest

theorem pairwiseStrictRule2?_sound (mol : RawMolecule) (profile : FrameRuntime.Profile)
    (fuel : ℕ) :
    ∀ roots : List CanonicalRerootCursor,
      pairwiseStrictRule2? mol profile fuel roots = true →
        PairwiseStrictOn mol profile fuel roots := by
  intro roots
  induction roots with
  | nil =>
      intro _ left hleft
      simp at hleft
  | cons head tail ih =>
      intro h right hright other hother hne
      simp only [pairwiseStrictRule2?] at h
      rw [Bool.and_eq_true_iff] at h
      obtain ⟨hrow, hrest⟩ := h
      rw [List.all_eq_true] at hrow
      rcases List.mem_cons.mp hright with hrightHead | hrightTail
      · subst right
        rcases List.mem_cons.mp hother with hotherHead | hotherTail
        · subst other
          exact absurd rfl hne
        · exact strictRule2B_sound mol profile fuel head other
            (Bool.and_eq_true_iff.mp (hrow other hotherTail)).1
      · rcases List.mem_cons.mp hother with hotherHead | hotherTail
        · subst other
          exact strictRule2B_sound mol profile fuel right head
            (Bool.and_eq_true_iff.mp (hrow right hrightTail)).2
        · exact ih hrest right hrightTail other hotherTail hne

/-- The computable gate's output, `Nodup` plus pairwise strictness, is exactly the canonical
`RootsConstitutionallySeparated` hypothesis consumed by the published independence theorem. -/
theorem rootsConstitutionallySeparated_of_pairwise
    (mol : RawMolecule) (profile : FrameRuntime.Profile) (fuel : ℕ)
    (roots : List CanonicalRerootCursor)
    (hnodup : roots.Nodup) (hstrict : PairwiseStrictOn mol profile fuel roots) :
    RootsConstitutionallySeparated mol profile fuel roots :=
  ⟨hnodup, hstrict⟩

/-! ## Computable early-root gate -/

/-- Computable gate executed before the full auxiliary-state builder.  It resolves the actual
profile and the actual four-ligand occurrence frame at the original root and succeeds exactly
when the roots are duplicate-free and every distinct ordered pair is strictly decided by the
actual framed Rule-2 comparator. -/
def earlyConstitutionalRootGate? (mol : RawMolecule) (fuel center : ℕ) :
    Option (FrameRuntime.Profile × List CanonicalRerootCursor) := do
  let profile ← FrameRuntime.profile? mol (canonicalCenterRoot center)
  let roots ← occurrenceLigandFrame? mol (canonicalCenterRoot center)
  if roots.Nodup then
    if pairwiseStrictRule2? mol profile fuel roots = true then
      some (profile, roots)
    else
      none
  else
    none

theorem earlyConstitutionalRootGate?_sound
    (mol : RawMolecule) (fuel center : ℕ)
    (profile : FrameRuntime.Profile) (roots : List CanonicalRerootCursor)
    (hg : earlyConstitutionalRootGate? mol fuel center = some (profile, roots)) :
    FrameRuntime.profile? mol (canonicalCenterRoot center) = some profile ∧
      occurrenceLigandFrame? mol (canonicalCenterRoot center) = some roots ∧
      roots.Nodup ∧ PairwiseStrictOn mol profile fuel roots := by
  unfold earlyConstitutionalRootGate? at hg
  dsimp only [Bind.bind] at hg
  cases hp : FrameRuntime.profile? mol (canonicalCenterRoot center) with
  | none =>
      rw [hp, Option.bind_none] at hg
      simp at hg
  | some p =>
      rw [hp, Option.bind_some] at hg
      cases hr : occurrenceLigandFrame? mol (canonicalCenterRoot center) with
      | none =>
          rw [hr, Option.bind_none] at hg
          simp at hg
      | some rs =>
          rw [hr, Option.bind_some] at hg
          by_cases hnd : rs.Nodup
          · rw [if_pos hnd] at hg
            by_cases hst : pairwiseStrictRule2? mol p fuel rs = true
            · rw [if_pos hst] at hg
              have hpair : (p, rs) = (profile, roots) := Option.some.inj hg
              have hpEq : p = profile := congrArg Prod.fst hpair
              have hrEq : rs = roots := congrArg Prod.snd hpair
              cases hpEq
              cases hrEq
              exact ⟨rfl, rfl, hnd, pairwiseStrictRule2?_sound mol profile fuel roots hst⟩
            · rw [if_neg hst] at hg
              simp at hg
          · rw [if_neg hnd] at hg
            simp at hg

/-- Gate hypothesis at an arbitrary node implies that the existing framed evaluator is
independent of the auxiliary state, by the canonical published theorem. -/
theorem earlyRootGate_independence
    (mol : RawMolecule) (fuel : ℕ) (node : CanonicalBranchNode)
    (profile : FrameRuntime.Profile) (roots : List CanonicalRerootCursor)
    (hprofile : FrameRuntime.profile? mol node = some profile)
    (hroots : occurrenceLigandFrame? mol node = some roots)
    (hnodup : roots.Nodup)
    (hstrict : PairwiseStrictOn mol profile fuel roots)
    (state : OccurrenceAuxState) :
    framedOccurrenceFactAuthoritative? mol fuel state node =
      framedOccurrenceFactAuthoritative? mol fuel [] node :=
  framedOccurrenceFactAuthoritative?_state_independent mol fuel node profile roots state []
    hprofile hroots (rootsConstitutionallySeparated_of_pairwise mol profile fuel roots hnodup
      hstrict)

/-- The computable gate at the original root implies that the existing framed evaluator is
independent of the auxiliary state there. -/
theorem earlyConstitutionalRootGate?_independence
    (mol : RawMolecule) (fuel center : ℕ)
    (profile : FrameRuntime.Profile) (roots : List CanonicalRerootCursor)
    (hg : earlyConstitutionalRootGate? mol fuel center = some (profile, roots))
    (state : OccurrenceAuxState) :
    framedOccurrenceFactAuthoritative? mol fuel state (canonicalCenterRoot center) =
      framedOccurrenceFactAuthoritative? mol fuel [] (canonicalCenterRoot center) := by
  obtain ⟨hprofile, hroots, hnodup, hstrict⟩ :=
    earlyConstitutionalRootGate?_sound mol fuel center profile roots hg
  exact earlyRootGate_independence mol fuel (canonicalCenterRoot center) profile roots
    hprofile hroots hnodup hstrict state

/-! ## Companion facade -/

/-- Early-path result from the existing framed evaluator at the empty state.  The packing formula
is exactly the public formula with an empty auxiliary state, so the diagnostic fields honestly
record that no auxiliary occurrence was consulted. -/
def tetrahedralOccurrenceFactEarlyRoot? (mol : RawMolecule) (fuel center : ℕ) :
    Option RawDescriptorFact :=
  match earlyConstitutionalRootGate? mol fuel center with
  | some _ =>
      (framedOccurrenceFactAuthoritative? mol fuel [] (canonicalCenterRoot center)).map fun fact =>
        { atom := center
          descriptor := fact.descriptor
          uppercase := fact.uppercase
          evidenceSize := max 1 ([] : OccurrenceAuxState).length
          decisiveRule? := none
          descriptorDependentPairs := ([] : OccurrenceAuxState).length
          priorityPositions := fact.priorityPositions }
  | none => tetrahedralOccurrenceFactAuthoritative? mol fuel center

/-- With a successful gate, the facade is exactly the existing framed evaluator at `[]` under the
public packing formula. -/
theorem earlyRootFacade_success
    (mol : RawMolecule) (fuel center : ℕ)
    (profile : FrameRuntime.Profile) (roots : List CanonicalRerootCursor)
    (hg : earlyConstitutionalRootGate? mol fuel center = some (profile, roots))
    (fact : OccurrenceAuxFact)
    (hfact : framedOccurrenceFactAuthoritative? mol fuel [] (canonicalCenterRoot center) =
      some fact) :
    tetrahedralOccurrenceFactEarlyRoot? mol fuel center =
      some { atom := center
             descriptor := fact.descriptor
             uppercase := fact.uppercase
             evidenceSize := max 1 ([] : OccurrenceAuxState).length
             decisiveRule? := none
             descriptorDependentPairs := ([] : OccurrenceAuxState).length
             priorityPositions := fact.priorityPositions } := by
  simp [tetrahedralOccurrenceFactEarlyRoot?, hg, hfact]

/-- When the gate refuses, the companion facade is the unchanged old public full-auxiliary
fallback. -/
theorem tetrahedralOccurrenceFactEarlyRoot?_fallback
    (mol : RawMolecule) (fuel center : ℕ)
    (h : earlyConstitutionalRootGate? mol fuel center = none) :
    tetrahedralOccurrenceFactEarlyRoot? mol fuel center =
      tetrahedralOccurrenceFactAuthoritative? mol fuel center := by
  simp [tetrahedralOccurrenceFactEarlyRoot?, h]

/-- The fields that constitute the chemical descriptor semantics of a public descriptor fact. -/
structure DescriptorChemicalView where
  atom : ℕ
  descriptor : RS
  uppercase : Bool
  decisiveRule? : Option CIPRuleFamily
  priorityPositions : List ℕ
  deriving DecidableEq, Repr

/-- Project the chemical descriptor fields, discarding the diagnostic counts. -/
def descriptorChemicalView (fact : RawDescriptorFact) : DescriptorChemicalView :=
  { atom := fact.atom
    descriptor := fact.descriptor
    uppercase := fact.uppercase
    decisiveRule? := fact.decisiveRule?
    priorityPositions := fact.priorityPositions }

/-- On early success, the companion facade preserves the full public chemical descriptor
semantics, while its honest empty-state diagnostics are recorded separately. -/
theorem earlyRootFacade_chemical_correct
    (mol : RawMolecule) (fuel center : ℕ)
    (profile : FrameRuntime.Profile) (roots : List CanonicalRerootCursor)
    (hg : earlyConstitutionalRootGate? mol fuel center = some (profile, roots))
    (fullFact : RawDescriptorFact)
    (hfull : tetrahedralOccurrenceFactAuthoritative? mol fuel center = some fullFact) :
    ∃ earlyFact : RawDescriptorFact,
      tetrahedralOccurrenceFactEarlyRoot? mol fuel center = some earlyFact ∧
      descriptorChemicalView earlyFact = descriptorChemicalView fullFact ∧
      earlyFact.evidenceSize = max 1 ([] : OccurrenceAuxState).length ∧
      earlyFact.descriptorDependentPairs = ([] : OccurrenceAuxState).length := by
  obtain ⟨hprofile, hroots, hnodup, hstrict⟩ :=
    earlyConstitutionalRootGate?_sound mol fuel center profile roots hg
  unfold tetrahedralOccurrenceFactAuthoritative? at hfull
  dsimp only [Bind.bind] at hfull
  cases hbuild : buildOccurrenceAuxStateFullyAuthoritative? mol fuel center with
  | none =>
      rw [hbuild, Option.bind_none] at hfull
      simp at hfull
  | some state =>
      rw [hbuild, Option.bind_some] at hfull
      cases hocc : occurrenceFactAuthoritative? mol fuel state (canonicalCenterRoot center) with
      | none =>
          rw [hocc, Option.bind_none] at hfull
          simp at hfull
      | some fact =>
          rw [hocc, Option.bind_some] at hfull
          have hfullEq : fullFact =
              { atom := center
                descriptor := fact.descriptor
                uppercase := fact.uppercase
                evidenceSize := max 1 state.length
                decisiveRule? := none
                descriptorDependentPairs := state.length
                priorityPositions := fact.priorityPositions } :=
            (Option.some.inj hfull).symm
          have hoccFramed : framedOccurrenceFactAuthoritative? mol fuel state
              (canonicalCenterRoot center) = some fact := by
            rw [← occurrenceFactAuthoritative?_eq_framed_of_profile_some mol fuel state
              (canonicalCenterRoot center) profile hprofile]
            exact hocc
          have hstateIndep := earlyRootGate_independence mol fuel
            (canonicalCenterRoot center) profile roots hprofile hroots hnodup hstrict state
          have hempty : framedOccurrenceFactAuthoritative? mol fuel []
              (canonicalCenterRoot center) = some fact := by
            rw [← hstateIndep]
            exact hoccFramed
          have hfacade := earlyRootFacade_success mol fuel center profile roots hg fact hempty
          refine ⟨{ atom := center
                    descriptor := fact.descriptor
                    uppercase := fact.uppercase
                    evidenceSize := max 1 ([] : OccurrenceAuxState).length
                    decisiveRule? := none
                    descriptorDependentPairs := ([] : OccurrenceAuxState).length
                    priorityPositions := fact.priorityPositions }, hfacade, ?_, rfl, rfl⟩
          rw [hfullEq]
          rfl

/-- The public authoritative entry point is untouched by this companion module. -/
theorem tetrahedralOccurrenceFact?_unchanged (mol : RawMolecule) (fuel center : ℕ) :
    tetrahedralOccurrenceFact? mol fuel center =
      tetrahedralOccurrenceFactAuthoritative? mol fuel center := rfl

/-! ## Concrete evaluation on the actual pipeline molecule -/

/-- The actual C2 profile resolves. -/
theorem c2_profile :
    FrameRuntime.profile? mol (canonicalCenterRoot c2Atom) = some c2Profile :=
  profiles_resolve.1

/-- The actual C2 occurrence frame resolves to the four-ligand cursor list. -/
theorem c2_frame :
    occurrenceLigandFrame? mol (canonicalCenterRoot c2Atom) =
      some (occurrenceLigandCursors mol (canonicalCenterRoot c2Atom)) :=
  frame_membership.2.2.2.1

/-- The existing framed evaluator at the empty state returns the C2 occurrence fact. -/
theorem c2_framed_empty_fact :
    framedOccurrenceFactAuthoritative? mol fuel [] (canonicalCenterRoot c2Atom) =
      some c2Fact := by
  rw [← occurrenceFactAuthoritative?_eq_framed_of_profile_some mol fuel []
    (canonicalCenterRoot c2Atom) c2Profile c2_profile]
  exact c2_empty_state_facts.2.1

/-- The actual C2 frame is pairwise strictly ranked by the framed Rule-2 comparator. -/
theorem c2_pairwiseStrict :
    pairwiseStrictRule2? mol c2Profile fuel
      (occurrenceLigandCursors mol (canonicalCenterRoot c2Atom)) = true := by
  decide

/-- The computable early-root gate fires at the original root C2. -/
theorem c2_earlyRootGate :
    earlyConstitutionalRootGate? mol fuel c2Atom =
      some (c2Profile, occurrenceLigandCursors mol (canonicalCenterRoot c2Atom)) := by
  have hnodup : (occurrenceLigandCursors mol (canonicalCenterRoot c2Atom)).Nodup :=
    frame_membership.2.1
  unfold earlyConstitutionalRootGate?
  dsimp only [Bind.bind]
  rw [c2_profile, Option.bind_some, c2_frame, Option.bind_some, if_pos hnodup,
    if_pos c2_pairwiseStrict]

/-- Honest early-path descriptor fact at C2: `R`, with empty-state diagnostics. -/
def c2EarlyFact : RawDescriptorFact :=
  { atom := c2Atom
    descriptor := c2Fact.descriptor
    uppercase := c2Fact.uppercase
    evidenceSize := max 1 ([] : OccurrenceAuxState).length
    decisiveRule? := none
    descriptorDependentPairs := ([] : OccurrenceAuxState).length
    priorityPositions := c2Fact.priorityPositions }

/-- The companion facade returns the early fact at C2 without building the full auxiliary state. -/
theorem c2_earlyFacade :
    tetrahedralOccurrenceFactEarlyRoot? mol fuel c2Atom = some c2EarlyFact := by
  rw [earlyRootFacade_success mol fuel c2Atom c2Profile
    (occurrenceLigandCursors mol (canonicalCenterRoot c2Atom)) c2_earlyRootGate c2Fact
    c2_framed_empty_fact]
  rfl

/-- The early descriptor at C2 is `R`. -/
theorem c2_early_descriptor_R :
    (tetrahedralOccurrenceFactEarlyRoot? mol fuel c2Atom).map
        (fun fact => fact.descriptor) = some RS.R := by
  rw [c2_earlyFacade]
  rfl

/-- Early and full public paths agree on the complete chemical descriptor semantics. -/
theorem c2_early_chemicalView_eq :
    (tetrahedralOccurrenceFactEarlyRoot? mol fuel c2Atom).map descriptorChemicalView =
      (tetrahedralOccurrenceFactAuthoritative? mol fuel c2Atom).map descriptorChemicalView := by
  rw [c2_earlyFacade, production_fact_c2]
  rfl

/-- The diagnostics of the early path are those of the empty state. -/
theorem c2_early_evidenceSize : c2EarlyFact.evidenceSize = 1 := by decide

theorem c2_early_descriptorDependentPairs :
    c2EarlyFact.descriptorDependentPairs = 0 := by decide

/-- The full public path records two descriptor-dependent auxiliary occurrences. -/
theorem c2_full_evidenceSize : c2ProductionFact.evidenceSize = 2 := by decide

theorem c2_full_descriptorDependentPairs :
    c2ProductionFact.descriptorDependentPairs = 2 := by decide

/-- The honest empty-state diagnostics differ from the full-auxiliary diagnostics at C2. -/
theorem c2_early_diagnostics_differ :
    c2EarlyFact.evidenceSize ≠ c2ProductionFact.evidenceSize ∧
      c2EarlyFact.descriptorDependentPairs ≠ c2ProductionFact.descriptorDependentPairs := by
  decide

/-- The unchanged old public full-auxiliary result at C2, retained as the fallback semantics. -/
theorem c2_full_pipeline_unchanged :
    tetrahedralOccurrenceFactAuthoritative? mol fuel c2Atom = some c2ProductionFact :=
  production_fact_c2

end RawConstitutionalEarlyRoot
end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.RawConstitutionalEarlyRoot.strictRule2B_sound
assert_kernel_only TetraStereo.OneCenter.RawConstitutionalEarlyRoot.pairwiseStrictRule2?_sound
assert_kernel_only
  TetraStereo.OneCenter.RawConstitutionalEarlyRoot.rootsConstitutionallySeparated_of_pairwise
assert_kernel_only
  TetraStereo.OneCenter.RawConstitutionalEarlyRoot.earlyConstitutionalRootGate?_sound
assert_kernel_only
  TetraStereo.OneCenter.RawConstitutionalEarlyRoot.earlyRootGate_independence
assert_kernel_only
  TetraStereo.OneCenter.RawConstitutionalEarlyRoot.earlyConstitutionalRootGate?_independence
assert_kernel_only TetraStereo.OneCenter.RawConstitutionalEarlyRoot.earlyRootFacade_success
assert_kernel_only
  TetraStereo.OneCenter.RawConstitutionalEarlyRoot.tetrahedralOccurrenceFactEarlyRoot?_fallback
assert_kernel_only
  TetraStereo.OneCenter.RawConstitutionalEarlyRoot.earlyRootFacade_chemical_correct
assert_kernel_only
  TetraStereo.OneCenter.RawConstitutionalEarlyRoot.tetrahedralOccurrenceFact?_unchanged
assert_kernel_only TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_profile
assert_kernel_only TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_frame
assert_kernel_only TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_framed_empty_fact
assert_kernel_only TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_pairwiseStrict
assert_kernel_only TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_earlyRootGate
assert_kernel_only TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_earlyFacade
assert_kernel_only TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_early_descriptor_R
assert_kernel_only TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_early_chemicalView_eq
assert_kernel_only TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_early_evidenceSize
assert_kernel_only
  TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_early_descriptorDependentPairs
assert_kernel_only TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_full_evidenceSize
assert_kernel_only
  TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_full_descriptorDependentPairs
assert_kernel_only
  TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_early_diagnostics_differ
assert_kernel_only
  TetraStereo.OneCenter.RawConstitutionalEarlyRoot.c2_full_pipeline_unchanged
