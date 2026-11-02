import TetraStereo.OneCenter.Rule4bInheritedRankFrontier

/-!
# Rule 4b first-chiral selection: optimality and success characterisation

This module proves the structural selector-correctness facts that
`TetraStereo.Rule4bInheritedRankFrontier` leaves open.  It contains no chemistry: every statement
is about the generic cursor/comparator/evidence interface of the supplied helper.

The three completed obligations are:

1. **Least candidate rank.**  `minPath?` does not merely return some member of its input (the
   supplied `minPath?_mem`); it returns a lexicographically least member.  This is
   `minPath?_le`.

2. **Exact layer evidence.**  `selectLayerChoice?` returns the least candidate rank path and
   exactly the complete population of uppercase evidence carried at that path, with multiplicity
   and without deduplication.  This is `selectLayerChoice?_path_le` together with
   `selectLayerChoice?_evidence` and its membership characterisation
   `mem_selectLayerChoice?_evidence_iff`.

3. **First successfully classified chiral sphere.**  The recursive `selectChoice?` is
   characterised exactly by the positive certificate `Selects`: every sphere visited before the
   selected one is fully classified and silent, the selected sphere is fully classified and
   carries uppercase evidence, and an empty frontier is exhausted without evidence.  This is
   `selectChoice?_eq_some_iff_selects`, for arbitrary finite fuel.  Consequently an unavailable
   observation on any silently reachable sphere refuses the whole selection instead of being
   skipped (`selectChoice?_eq_none_of_silentReach_resolve_none`,
   `selectChoice?_some_no_reachable_resolve_none`).

Nothing here assumes that the chosen path is minimal, that the chosen layer is first, or that a
particular chemistry-level comparator is lawful.  The statements quantify over the actual
definitions of the helper.  Comparator laws are needed only where the helper itself needs them and
are not used by these selector statements.
-/

set_option autoImplicit false

namespace TetraStereo.Rule4bFirstChiralSelectionOptimality

open TetraStereo.Rule4bInheritedRankFrontier

universe u v

variable {Cursor : Type u} {Descriptor : Type v}
variable {spec : FrontierSpec Cursor Descriptor}

/-! ## 1. `minPath?` is a least-element selector -/

/-- The `List.foldl` used by `minPath?` is a running minimum: its result is below the initial
value and below every element that was folded.  No order law is assumed beyond what Lean's core
list order provides; the argument is the definitional one used by the fold. -/
theorem foldl_minPath_le (init : List Nat) :
    ∀ (ps : List (List Nat)),
      ps.foldl (fun best q => if q < best then q else best) init ≤ init ∧
        ∀ q ∈ ps, ps.foldl (fun best q => if q < best then q else best) init ≤ q
  | [] => by
      constructor
      · exact List.le_refl init
      · intro q hq
        simp at hq
  | q :: qs => by
      simp only [List.foldl_cons]
      have hstep_init : (if q < init then q else init) ≤ init := by
        by_cases hlt : q < init
        · rw [if_pos hlt]
          exact List.le_of_lt hlt
        · rw [if_neg hlt]
          exact List.le_refl init
      have hstep_q : (if q < init then q else init) ≤ q := by
        by_cases hlt : q < init
        · rw [if_pos hlt]
          exact List.le_refl q
        · rw [if_neg hlt]
          exact (List.not_lt (l₁ := q) (l₂ := init)).2 hlt
      have ih := foldl_minPath_le (if q < init then q else init) qs
      constructor
      · exact List.le_trans ih.1 hstep_init
      · intro r hr
        rcases List.mem_cons.mp hr with rfl | hmem
        · exact List.le_trans ih.1 hstep_q
        · exact ih.2 r hmem

/-- `minPath?` returns a lexicographically least member of its input.  This upgrades the supplied
`minPath?_mem`, which establishes only membership. -/
theorem minPath?_le {ps : List (List Nat)} {p : List Nat}
    (h : minPath? ps = some p) : ∀ q ∈ ps, p ≤ q := by
  cases ps with
  | nil => simp [minPath?] at h
  | cons r rs =>
      simp only [minPath?] at h
      have hp : rs.foldl (fun best q => if q < best then q else best) r = p :=
        Option.some_inj.1 h
      intro q hq
      rw [← hp]
      rcases List.mem_cons.mp hq with hqr | hmem
      · rw [hqr]
        exact (foldl_minPath_le r rs).1
      · exact (foldl_minPath_le r rs).2 q hmem

/-- Combined least-element statement: the result of `minPath?` is a member of the input and is
below every member of the input. -/
theorem minPath?_isLeast {ps : List (List Nat)} {p : List Nat}
    (h : minPath? ps = some p) :
    p ∈ ps ∧ ∀ q ∈ ps, p ≤ q :=
  ⟨minPath?_mem h, minPath?_le h⟩

/-- `minPath?` fails exactly on the empty list. -/
theorem minPath?_eq_none_iff {ps : List (List Nat)} :
    minPath? ps = none ↔ ps = [] := by
  cases ps with
  | nil => simp [minPath?]
  | cons p ps => simp [minPath?]

/-! ## 2. Layer selection: least path and exact evidence population -/

/-- The rank paths that carry uppercase evidence on a resolved sphere, in resolution order and
with multiplicity. -/
def candidatePaths (classified : List (RankedCursor Cursor × Option Descriptor)) :
    List (List Nat) :=
  (layerCandidates classified).map fun entry => entry.1.rankPath

/-- Membership in `layerCandidates` is exactly being an uppercase entry of the resolved sphere. -/
theorem mem_layerCandidates_iff {classified : List (RankedCursor Cursor × Option Descriptor)}
    {rc : RankedCursor Cursor} {d : Descriptor} :
    (rc, d) ∈ layerCandidates classified ↔ (rc, some d) ∈ classified := by
  unfold layerCandidates
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨rc', ev⟩, hentry, hsome⟩
    cases ev with
    | none => cases hsome
    | some d' =>
        have hpair : (rc', d') = (rc, d) := Option.some_inj.1 hsome
        simp only [Prod.mk.injEq] at hpair
        obtain ⟨rfl, rfl⟩ := hpair
        exact hentry
  · intro h
    exact ⟨(rc, some d), h, by simp⟩

/-- Membership in `evidenceAtPath` is exactly being an uppercase entry of the resolved sphere at
the requested rank path. -/
theorem mem_evidenceAtPath_iff {classified : List (RankedCursor Cursor × Option Descriptor)}
    {path : List Nat} {d : Descriptor} :
    d ∈ evidenceAtPath classified path ↔
      ∃ rc : RankedCursor Cursor, (rc, some d) ∈ classified ∧ rc.rankPath = path := by
  unfold evidenceAtPath
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨rc, ev⟩, hentry, hsome⟩
    cases ev with
    | none => cases hsome
    | some d' =>
        dsimp only at hsome
        by_cases hpath : rc.rankPath = path
        · rw [if_pos hpath] at hsome
          have hd : d' = d := Option.some_inj.1 hsome
          rw [hd] at hentry
          exact ⟨rc, hentry, hpath⟩
        · rw [if_neg hpath] at hsome
          cases hsome
  · rintro ⟨rc, hentry, hpath⟩
    exact ⟨(rc, some d), hentry, by simp [hpath]⟩

/-- `selectLayerChoice?` fails exactly when the sphere carries no uppercase evidence. -/
theorem selectLayerChoice?_eq_none_iff
    {classified : List (RankedCursor Cursor × Option Descriptor)} :
    selectLayerChoice? classified = none ↔ layerCandidates classified = [] := by
  constructor
  · intro h
    unfold selectLayerChoice? at h
    rw [Option.map_eq_none_iff] at h
    exact List.map_eq_nil_iff.mp (minPath?_eq_none_iff.mp h)
  · intro h
    unfold selectLayerChoice?
    rw [h]
    rfl

/-- The path selected by `selectLayerChoice?` belongs to the candidate paths. -/
theorem selectLayerChoice?_path_mem
    {classified : List (RankedCursor Cursor × Option Descriptor)}
    {choice : FrontierChoice Descriptor}
    (h : selectLayerChoice? classified = some choice) :
    choice.rankPath ∈ candidatePaths classified := by
  unfold selectLayerChoice? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨path, hmin, hchoice⟩ := h
  have hmem : path ∈ (layerCandidates classified).map (fun entry => entry.1.rankPath) :=
    minPath?_mem hmin
  rw [← hchoice]
  simpa [candidatePaths] using hmem

/-- The path selected by `selectLayerChoice?` is lexicographically least among all candidate
paths.  This is the leastness statement that `selectLayerChoice?_path_mem` does not give. -/
theorem selectLayerChoice?_path_le
    {classified : List (RankedCursor Cursor × Option Descriptor)}
    {choice : FrontierChoice Descriptor}
    (h : selectLayerChoice? classified = some choice) :
    ∀ path ∈ candidatePaths classified, choice.rankPath ≤ path := by
  unfold selectLayerChoice? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨least, hmin, hchoice⟩ := h
  intro path hpath
  have hpath' : path ∈ (layerCandidates classified).map (fun entry => entry.1.rankPath) := by
    simpa [candidatePaths] using hpath
  have hle : least ≤ path := minPath?_le hmin path hpath'
  rw [← hchoice]
  simpa using hle

/-- Leastness phrased directly for an uppercase entry: the selected path is below the rank path of
every uppercase occurrence on the sphere. -/
theorem selectLayerChoice?_path_le_of_candidate
    {classified : List (RankedCursor Cursor × Option Descriptor)}
    {choice : FrontierChoice Descriptor}
    (h : selectLayerChoice? classified = some choice)
    {rc : RankedCursor Cursor} {d : Descriptor}
    (hmem : (rc, d) ∈ layerCandidates classified) :
    choice.rankPath ≤ rc.rankPath := by
  apply selectLayerChoice?_path_le h
  simp only [candidatePaths, List.mem_map]
  exact ⟨(rc, d), hmem, rfl⟩

/-- The selected evidence is exactly `evidenceAtPath` at the selected path: a `filterMap` that
maps each matching uppercase entry to one descriptor, so multiplicity and comparator ties are
preserved. -/
theorem selectLayerChoice?_evidence
    {classified : List (RankedCursor Cursor × Option Descriptor)}
    {choice : FrontierChoice Descriptor}
    (h : selectLayerChoice? classified = some choice) :
    choice.evidence = evidenceAtPath classified choice.rankPath := by
  unfold selectLayerChoice? at h
  rw [Option.map_eq_some_iff] at h
  obtain ⟨path, _hmin, hchoice⟩ := h
  rw [← hchoice]

/-- Exact evidence population: a descriptor occurs in the selected evidence iff an uppercase
occurrence carrying it exists on the resolved sphere at the selected path.  Together with
`selectLayerChoice?_evidence` this is the "exactly all uppercase evidence at that rank, with
multiplicity" statement. -/
theorem mem_selectLayerChoice?_evidence_iff
    {classified : List (RankedCursor Cursor × Option Descriptor)}
    {choice : FrontierChoice Descriptor}
    (h : selectLayerChoice? classified = some choice) {d : Descriptor} :
    d ∈ choice.evidence ↔
      ∃ rc : RankedCursor Cursor, (rc, some d) ∈ classified ∧ rc.rankPath = choice.rankPath := by
  rw [selectLayerChoice?_evidence h]
  exact mem_evidenceAtPath_iff

/-- Every uppercase occurrence at the selected path contributes its descriptor to the selected
evidence (multiplicity-preserving direction). -/
theorem mem_selectLayerChoice?_evidence_of_entry
    {classified : List (RankedCursor Cursor × Option Descriptor)}
    {choice : FrontierChoice Descriptor}
    (h : selectLayerChoice? classified = some choice)
    {rc : RankedCursor Cursor} {d : Descriptor}
    (hentry : (rc, some d) ∈ classified) (hpath : rc.rankPath = choice.rankPath) :
    d ∈ choice.evidence :=
  (mem_selectLayerChoice?_evidence_iff h).2 ⟨rc, hentry, hpath⟩

/-! ## 3. The recursive selector returns the first successfully classified chiral sphere

`Selects` is the positive certificate for the actual recursion.  Its constructors mirror the
success branches of `selectChoice?`:

* `exhausted`: the frontier is empty, so there is no evidence;
* `selected`: the current nonempty sphere is fully classified and carries at least one uppercase
  occurrence; the least evidence-bearing path of that sphere is selected;
* `descended`: the current nonempty sphere is fully classified but silent (no uppercase
  occurrence), and the search descends one sphere with one unit of fuel.

There is no constructor that skips an unavailable observation: every nonempty step contains a
`classifyLayer ... = some ...` proof.  The equivalence theorem below is proved against the
defining equations of `selectChoice?`, not assumed.
-/

/-- Positive certificate of a successful `selectChoice?` run.  The fuel index is the fuel consumed
by the actual recursion, so this supports arbitrary finite depth. -/
inductive Selects (spec : FrontierSpec Cursor Descriptor) :
    Nat → List (RankedCursor Cursor) → Option (FrontierChoice Descriptor) → Prop
  /-- The empty frontier is exhausted without evidence. -/
  | exhausted (fuel : Nat) :
      Selects spec fuel [] (some ⟨[], []⟩)
  /-- The first non-silent sphere is fully classified and its least evidence-bearing path is
  selected with all uppercase evidence there. -/
  | selected {fuel : Nat} {rc : RankedCursor Cursor} {rest : List (RankedCursor Cursor)}
      {classified : List (RankedCursor Cursor × Option Descriptor)}
      {choice : FrontierChoice Descriptor}
      (hclass : classifyLayer spec (rc :: rest) = some classified)
      (hevidence : layerCandidates classified ≠ [])
      (hselect : selectLayerChoice? classified = some choice) :
      Selects spec (Nat.succ fuel) (rc :: rest) (some choice)
  /-- A fully classified silent sphere is descended; the remainder is again a successful run. -/
  | descended {fuel : Nat} {rc : RankedCursor Cursor} {rest : List (RankedCursor Cursor)}
      {classified : List (RankedCursor Cursor × Option Descriptor)}
      {next : List (RankedCursor Cursor)}
      {result : Option (FrontierChoice Descriptor)}
      (hclass : classifyLayer spec (rc :: rest) = some classified)
      (hsilent : layerCandidates classified = [])
      (hregroup : regroup spec (rc :: rest) = some next)
      (htail : Selects spec fuel next result) :
      Selects spec (Nat.succ fuel) (rc :: rest) result

/-- Every successful certificate returns a `some` choice.  In particular there is no successful
certificate for `none`. -/
theorem Selects.isSome {fuel : Nat} {frontier : List (RankedCursor Cursor)}
    {result : Option (FrontierChoice Descriptor)}
    (h : Selects spec fuel frontier result) :
    ∃ choice : FrontierChoice Descriptor, result = some choice := by
  induction h with
  | exhausted fuel => exact ⟨⟨[], []⟩, rfl⟩
  | selected hclass hevidence hselect => exact ⟨_, rfl⟩
  | descended hclass hsilent hregroup htail ih => exact ih

/-- No successful certificate produces `none`. -/
theorem selects_none_false {fuel : Nat} {frontier : List (RankedCursor Cursor)} :
    ¬ Selects spec fuel frontier none := by
  intro h
  obtain ⟨choice, hchoice⟩ := h.isSome
  cases hchoice

/-- Soundness of the certificate against the actual recursion: every certificate is exactly the
result computed by `selectChoice?`. -/
theorem selects_sound {fuel : Nat} {frontier : List (RankedCursor Cursor)}
    {result : Option (FrontierChoice Descriptor)}
    (h : Selects spec fuel frontier result) :
    selectChoice? spec fuel frontier = result := by
  induction h with
  | exhausted fuel =>
      cases fuel <;> rfl
  | selected hclass hevidence hselect =>
      obtain ⟨c, cs, hcand⟩ := List.exists_cons_of_ne_nil hevidence
      simpa [selectChoice?, hclass, hcand] using hselect
  | descended hclass hsilent hregroup htail ih =>
      simpa [selectChoice?, hclass, hsilent, hregroup] using ih

/-- Completeness of the certificate against the actual recursion: if the executable selector
succeeds, the recursion's own path is a certificate.  This is proved by recursion on the fuel of
`selectChoice?`; no minimality or firstness is assumed. -/
theorem selectChoice?_complete (spec : FrontierSpec Cursor Descriptor) :
    ∀ (fuel : Nat) (frontier : List (RankedCursor Cursor))
      (choice : FrontierChoice Descriptor),
      selectChoice? spec fuel frontier = some choice →
        Selects spec fuel frontier (some choice)
  | 0, [], choice => by
      intro h
      have hchoice : choice = ⟨[], []⟩ := by
        simpa [selectChoice?] using h.symm
      rw [hchoice]
      exact Selects.exhausted 0
  | 0, _ :: _, choice => by
      intro h
      simp [selectChoice?] at h
  | Nat.succ fuel, [], choice => by
      intro h
      have hchoice : choice = ⟨[], []⟩ := by
        simpa [selectChoice?] using h.symm
      rw [hchoice]
      exact Selects.exhausted (Nat.succ fuel)
  | Nat.succ fuel, rc :: rest, choice => by
      intro h
      cases hc : classifyLayer spec (rc :: rest) with
      | none =>
          simp [selectChoice?, hc] at h
      | some classified =>
          cases hcand : layerCandidates classified with
          | nil =>
              cases hr : regroup spec (rc :: rest) with
              | none => simp [selectChoice?, hc, hcand, hr] at h
              | some next =>
                  have htail : selectChoice? spec fuel next = some choice := by
                    simpa [selectChoice?, hc, hcand, hr] using h
                  exact Selects.descended hc hcand hr
                    (selectChoice?_complete spec fuel next choice htail)
          | cons c cs =>
              have hsel : selectLayerChoice? classified = some choice := by
                simpa [selectChoice?, hc, hcand] using h
              exact Selects.selected hc
                (by rw [hcand]; exact List.cons_ne_nil c cs) hsel

/-- Success characterisation of the actual recursive selector at arbitrary finite fuel.  A
`some choice` result is equivalent to the existence of a recursion-faithful certificate whose
first evidence-bearing sphere is the selected one.  Every earlier sphere is fully classified and
silent; an unavailable observation anywhere on that path has no certificate. -/
theorem selectChoice?_eq_some_iff_selects
    {fuel : Nat} {frontier : List (RankedCursor Cursor)}
    {choice : FrontierChoice Descriptor} :
    selectChoice? spec fuel frontier = some choice ↔
      Selects spec fuel frontier (some choice) :=
  ⟨selectChoice?_complete spec fuel frontier choice, fun h => selects_sound h⟩

/-- First-step inversion read directly off the defining equations of `selectChoice?`: a successful
run on a nonempty sphere either selects that sphere (it has evidence) or fully classifies it as
silent and continues.  There is no third possibility. -/
theorem selectChoice?_succ_cons_cases
    {fuel : Nat} {rc : RankedCursor Cursor} {rest : List (RankedCursor Cursor)}
    {choice : FrontierChoice Descriptor}
    (h : selectChoice? spec (Nat.succ fuel) (rc :: rest) = some choice) :
    (∃ classified : List (RankedCursor Cursor × Option Descriptor),
        classifyLayer spec (rc :: rest) = some classified ∧
          layerCandidates classified ≠ [] ∧
            selectLayerChoice? classified = some choice) ∨
      (∃ (classified : List (RankedCursor Cursor × Option Descriptor))
          (next : List (RankedCursor Cursor)),
          classifyLayer spec (rc :: rest) = some classified ∧
            layerCandidates classified = [] ∧
              regroup spec (rc :: rest) = some next ∧
                selectChoice? spec fuel next = some choice) := by
  cases hc : classifyLayer spec (rc :: rest) with
  | none => simp [selectChoice?, hc] at h
  | some classified =>
      cases hcand : layerCandidates classified with
      | nil =>
          cases hr : regroup spec (rc :: rest) with
          | none => simp [selectChoice?, hc, hcand, hr] at h
          | some next =>
              exact Or.inr
                ⟨classified, next, rfl, hcand, rfl,
                  (by simpa [selectChoice?, hc, hcand, hr] using h)⟩
      | cons c cs =>
          refine Or.inl ⟨classified, rfl, ?_, ?_⟩
          · rw [hcand]
            exact List.cons_ne_nil c cs
          · simpa [selectChoice?, hc, hcand] using h

/-! ### Refusal of unavailable observations at arbitrary depth

`SilentReach` traces the deterministic prefix of the search on which every sphere is fully
classified and silent.  It is used to state that an unavailable observation on any such sphere
refuses the selection: the recursion never skips it and continues to a deeper sphere.
-/

/-- Deterministic silent prefix of the search.  `SilentReach spec k frontier target` means that
*at most* `k` consecutive spheres starting at `frontier` are fully classified, carry no uppercase
evidence, and regroup successfully, ending at `target`.  The bound is not exact: `refl` accepts an
arbitrary fuel with no descent, so the constructor `step` may be used fewer than `k` times.  This
is the intended reading, since only the descent prefix matters for refusal. -/
inductive SilentReach (spec : FrontierSpec Cursor Descriptor) :
    Nat → List (RankedCursor Cursor) → List (RankedCursor Cursor) → Prop
  /-- No descent: the target is the starting frontier. -/
  | refl (fuel : Nat) (frontier : List (RankedCursor Cursor)) :
      SilentReach spec fuel frontier frontier
  /-- One fully classified silent sphere followed by a silent prefix. -/
  | step {fuel : Nat} {rc : RankedCursor Cursor} {rest : List (RankedCursor Cursor)}
      {classified : List (RankedCursor Cursor × Option Descriptor)}
      {next target : List (RankedCursor Cursor)}
      (hclass : classifyLayer spec (rc :: rest) = some classified)
      (hsilent : layerCandidates classified = [])
      (hregroup : regroup spec (rc :: rest) = some next)
      (htail : SilentReach spec fuel next target) :
      SilentReach spec (Nat.succ fuel) (rc :: rest) target

/-- An unavailable observation at the end of a silent prefix refuses the whole selection.  The
recursion has no branch that skips the offending sphere. -/
theorem selectChoice?_eq_none_of_silentReach_resolve_none
    {fuel : Nat} {frontier target : List (RankedCursor Cursor)}
    (hreach : SilentReach spec fuel frontier target) :
    ∀ (r : RankedCursor Cursor), r ∈ target → spec.resolve r.cursor = none →
      selectChoice? spec fuel frontier = none := by
  induction hreach with
  | refl fuel frontier =>
      intro r hmem hresolve
      exact selectChoice?_eq_none_of_mem_resolve_none spec fuel frontier r hmem hresolve
  | step hclass hsilent hregroup htail ih =>
      intro r hmem hresolve
      have hnext := ih r hmem hresolve
      simpa [selectChoice?, hclass, hsilent, hregroup] using hnext

/-- Contrapositive form: a successful selection cannot silently reach a sphere carrying an
unavailable observation.  This is the "refusing rather than skipping" guarantee at arbitrary
finite depth. -/
theorem selectChoice?_some_no_reachable_resolve_none
    {fuel : Nat} {frontier : List (RankedCursor Cursor)}
    {choice : FrontierChoice Descriptor}
    (hsel : selectChoice? spec fuel frontier = some choice)
    {target : List (RankedCursor Cursor)}
    (hreach : SilentReach spec fuel frontier target)
    {rc : RankedCursor Cursor} (hmem : rc ∈ target) :
    spec.resolve rc.cursor ≠ none := by
  intro hresolve
  have hnone := selectChoice?_eq_none_of_silentReach_resolve_none hreach rc hmem hresolve
  rw [hnone] at hsel
  cases hsel

end TetraStereo.Rule4bFirstChiralSelectionOptimality

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.foldl_minPath_le
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.minPath?_le
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.minPath?_isLeast
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.minPath?_eq_none_iff
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.mem_layerCandidates_iff
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.mem_evidenceAtPath_iff
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.selectLayerChoice?_eq_none_iff
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.selectLayerChoice?_path_mem
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.selectLayerChoice?_path_le
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.selectLayerChoice?_path_le_of_candidate
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.selectLayerChoice?_evidence
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.mem_selectLayerChoice?_evidence_iff
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.mem_selectLayerChoice?_evidence_of_entry
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.Selects.isSome
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.selects_none_false
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.selects_sound
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.selectChoice?_complete
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.selectChoice?_eq_some_iff_selects
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.selectChoice?_succ_cons_cases
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.selectChoice?_eq_none_of_silentReach_resolve_none
assert_kernel_only TetraStereo.Rule4bFirstChiralSelectionOptimality.selectChoice?_some_no_reachable_resolve_none
