import TetraStereo.OneCenter.LocalizedChemicalRingReferencePolicy
import TetraStereo.OneCenter.LocalizedChemicalRingJointPreparedSourceModelExistence
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime

open CertifiedLocalizedCIPInput
open LocalizedChemicalRingReferencePolicy (ReferenceLifetime AuxiliaryChronology policyFallback)
open LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingJointPreparedSourceStep
open LocalizedChemicalRingJointPreparedSourceQueries
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedGenericMarkedRecalculation (Geometry consensus caseFromMirror? mirror structuralDepth WellFormedBonds)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant Descends)
open LocalizedChemicalRingJointPreparedStructuralProfile (structuralDepth_lt)
open scoped Classical
noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (agreement : mol.AuthoritativeStructureAgreement input.certified.input)
  (admissible : mol.StereochemicalAdmissible)
  (supported : ∀ bond ∈ mol.bonds, bond.kind.IsLocalizedCovalent)
  (single : input.moleculeGraph.SimpleBonded)

local notation "Q" => SourceQuery input mol
local notation "P" => Profile input mol

/-- A molecular occurrence frame for each eligible query, derived once for both policies. -/
def frames (q : Q) : Σ c, OccurrenceData input mol c q.1 :=
  let h := sourceQuery_data_exists input mol agreement admissible supported single q
  ⟨h.choose, Classical.choice h.choose_spec.2⟩

variable (frame : (q : SourceQuery input mol) →
  (Σ c : input.detectedMultiCenterMolecule.Center, OccurrenceData input mol c q.1))

def rawWith (life : ReferenceLifetime) (chronology : AuxiliaryChronology) (p : P) (q : Q) (g : Geometry) (refs : List input.Atom) : Option RS :=
  let data := (frame q).2
  let family := profileFamily input mol p q
  let k := sourceKeysAt input single family data.target data.frame g refs
  if Function.Injective k then sourceReading input g data.frame k
  else consensus ((sourceSelectedSlots k).map
    (policyFallback input single life chronology family data.target data.frame g refs))

abbrev raw (life : ReferenceLifetime) := rawWith input mol single frame life .regenerated

def update (life : ReferenceLifetime) (p : P) (q : Q) (g : Geometry) (refs : List input.Atom) :=
  caseFromMirror? (raw input mol single frame life p q g refs)
    (raw input mol single frame life p q (mirror g) refs)

theorem update_local (life : ReferenceLifetime) (p t : P) (q : Q)
    (agree : ∀ g refs (d : Q), StrictDescendant mol q.1 d.1 → p g refs d = t g refs d)
    (g : Geometry) (refs : List input.Atom) :
    update input mol single frame life p q g refs = update input mol single frame life t q g refs := by
  unfold update raw rawWith
  rw [profileFamily_local input mol q p t agree]

theorem first_mark_agrees (p : P) (q : Q) (g : Geometry) :
    update input mol single frame .accumulated p q g [] =
      update input mol single frame .current p q g [] := rfl

set_option quotPrecheck false
local notation "depth" => fun q : Q => structuralDepth mol q.1

/-- At round n a schedule must refresh every query of structural depth n. It may refresh
other queries speculatively or repeat earlier work. All context tables are regenerated. -/
def rounds (life : ReferenceLifetime) (refresh : Nat → Q → Bool) (seed : P) : Nat → P
  | 0 => seed
  | n+1 => fun g refs q =>
      let previous := rounds life refresh seed n
      if refresh n q then update input mol single frame life previous q g refs else previous g refs q

local notation "layers" => rounds input mol single frame
local notation "due" => fun (n : Nat) (q : Q) => decide (depth q = n)

def solution (life : ReferenceLifetime) : P := fun g refs q =>
  layers life due (fun _ _ _ => none) (depth q + 1) g refs q

private theorem after_due (life : ReferenceLifetime) (n : Nat) (q : Q) (ready : depth q < n)
    (g : Geometry) (refs : List input.Atom) :
    layers life due (fun _ _ _ => none) n g refs q = solution input mol single frame life g refs q := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases h : depth q = n
    · simp [solution,h]
    · have lt : depth q < n := by omega
      simpa [rounds, h] using ih lt

include admissible in
theorem solution_equation (life : ReferenceLifetime) (q : Q) (g : Geometry) (refs : List input.Atom) :
    solution input mol single frame life g refs q =
      update input mol single frame life (solution input mol single frame life) q g refs := by
  change layers life due _ (depth q + 1) g refs q = _
  simp only [rounds, decide_true, if_true]
  apply update_local
  intro geo context d child
  have wf : WellFormedBonds mol := fun b hb =>
    ⟨(admissible.1.1 b hb).1, (admissible.1.1 b hb).2.1⟩
  exact after_due input mol single frame life _ d (structuralDepth_lt mol wf q.2.1 child) geo context

include admissible in
/-- Once a query's depth has passed, every covered schedule and arbitrary initial table give
the same result, including completed refusals, for either reference lifetime. -/
theorem schedule_independent (life : ReferenceLifetime) (refresh : Nat → Q → Bool)
    (covers : ∀ q, refresh (depth q) q = true) (seed : P) (n : Nat) :
    ∀ q : Q, depth q < n → ∀ g refs, layers life refresh seed n g refs q =
      solution input mol single frame life g refs q := by
  induction n with
  | zero => intro q h; omega
  | succ n ih =>
    intro q ready g refs
    simp only [rounds]
    split <;> rename_i test
    · rw [solution_equation input mol admissible single frame life q g refs]
      apply update_local
      intro geo ctx d child
      have wf : WellFormedBonds mol := fun b hb =>
        ⟨(admissible.1.1 b hb).1, (admissible.1.1 b hb).2.1⟩
      have lt := structuralDepth_lt mol wf q.2.1 child
      exact ih d (Nat.lt_of_lt_of_le lt (Nat.le_of_lt_succ ready)) geo ctx
    · apply ih q _ g refs
      by_contra! h
      have same : depth q = n := Nat.le_antisymm (Nat.le_of_lt_succ ready) h
      exact test (same ▸ covers q)

include admissible in
theorem solution_unique (life : ReferenceLifetime) (p : P)
    (solves : ∀ g refs q, p g refs q = update input mol single frame life p q g refs) :
    p = solution input mol single frame life := by
  have wf : WellFormedBonds mol := fun b hb =>
    ⟨(admissible.1.1 b hb).1, (admissible.1.1 b hb).2.1⟩
  suffices ∀ q : Q, ∀ g refs, p g refs q = solution input mol single frame life g refs q by
    funext g refs q
    exact this q g refs
  intro q
  induction q using (measure depth).wf.induction with
  | h q ih =>
    intro g refs
    rw [solves, solution_equation input mol admissible single frame life q g refs]
    exact update_local input mol single frame life _ _ q
      (fun geo ctx d child => ih d (structuralDepth_lt mol wf q.2.1 child) geo ctx) g refs

include admissible in
theorem accumulated_eq_sourceModel (p : P) (model : SourceModel input mol single p) :
    solution input mol single frame .accumulated = p := by
  apply Eq.symm
  apply solution_unique input mol admissible single frame .accumulated
  intro g refs q
  exact (model g refs q (frame q).1 (frame q).2).symm

include admissible in
/-- Equality of the two independently generated profiles reduces to the effect of older
references at a single nonempty context on the derived replacement-policy table. -/
theorem lifetime_eq_iff_nested :
    solution input mol single frame .accumulated = solution input mol single frame .current ↔
    ∀ (q : Q) (g : Geometry) (refs : List input.Atom), refs ≠ [] →
      let p := solution input mol single frame .current
      update input mol single frame .accumulated p q g refs =
        update input mol single frame .current p q g refs := by
  constructor
  · intro same q g refs _
    dsimp only
    conv_lhs => rw [← same]
    rw [← solution_equation input mol admissible single frame .accumulated,
      ← solution_equation input mol admissible single frame .current, same]
  · intro nested
    symm
    apply solution_unique input mol admissible single frame .accumulated
    intro g refs q
    rw [solution_equation input mol admissible single frame .current q g refs]
    by_cases empty : refs = []
    · subst refs
      exact (first_mark_agrees input mol single frame _ q g).symm
    · exact (nested q g refs empty).symm

/-- A concrete diagnostic on the independently regenerated replacement table: the same
subquery and the same contextual child table respond differently to retaining an older mark. -/
def NestedDifference (q : Q) : Prop :=
  ∃ g refs, refs ≠ [] ∧
    let p := solution input mol single frame .current
    update input mol single frame .accumulated p q g refs ≠
      update input mol single frame .current p q g refs

private theorem below_trans {a b c : RawMolecule.CanonicalBranchNode}
    (ab : StrictDescendant mol a b) (bc : StrictDescendant mol b c) : StrictDescendant mol a c := by
  obtain ⟨x,hx,xb⟩ := ab
  obtain ⟨y,hy,yc⟩ := bc
  exact ⟨x,hx,(xb.tail hy).trans yc⟩

include admissible in
/-- A final-query difference between the two lifetime choices requires a strict molecular
descendant with a local difference at a nonempty context. No comparison result, generated
child map, or terminal descriptor is an input to the witness. -/
theorem empty_context_disagreement_descends (q : Q) (geom : Geometry)
    (different : solution input mol single frame .accumulated geom [] q ≠
      solution input mol single frame .current geom [] q) :
    ∃ d : Q, StrictDescendant mol q.1 d.1 ∧ NestedDifference input mol single frame d := by
  classical
  by_contra! absent
  have wf : WellFormedBonds mol := fun b hb =>
    ⟨(admissible.1.1 b hb).1, (admissible.1.1 b hb).2.1⟩
  have agree (d : Q) : StrictDescendant mol q.1 d.1 → ∀ g refs,
      solution input mol single frame .accumulated g refs d =
        solution input mol single frame .current g refs d := by
    induction d using (measure depth).wf.induction with
    | h d ih =>
      intro below g refs
      rw [solution_equation input mol admissible single frame .accumulated d,
        solution_equation input mol admissible single frame .current d]
      trans update input mol single frame .accumulated (solution input mol single frame .current) d g refs
      · apply update_local
        intro geo ctx child path
        exact ih child (structuralDepth_lt mol wf d.2.1 path) (below_trans mol below path) geo ctx
      · by_cases empty : refs = []
        · subst refs
          exact first_mark_agrees input mol single frame _ d g
        · by_contra diff
          exact absent d below ⟨g,refs,empty,diff⟩
  apply different
  rw [solution_equation input mol admissible single frame .accumulated q,
    solution_equation input mol admissible single frame .current q]
  trans update input mol single frame .accumulated (solution input mol single frame .current) q geom []
  · exact update_local input mol single frame .accumulated _ _ q
      (fun g ctx d path => agree d path g ctx) geom []
  · exact first_mark_agrees input mol single frame _ q geom



/-- A difference at one shared child table needs an eligible promotion whose raw reading
changes on a concrete geometry side. -/
private theorem raw_disagreement (p : P) (q : Q) (g : Geometry) (refs : List input.Atom)
    (diff : raw input mol single frame .accumulated p q g refs ≠
      raw input mol single frame .current p q g refs) :
    let data := (frame q).2
    let family := profileFamily input mol p q
    let k := sourceKeysAt input single family data.target data.frame g refs
    ¬ Function.Injective k ∧ ∃ i ∈ sourceSelectedSlots k,
      policyFallback input single .accumulated .regenerated family data.target data.frame g refs i ≠
        policyFallback input single .current .regenerated family data.target data.frame g refs i := by
  dsimp only
  unfold raw rawWith at diff
  dsimp only at diff
  split at diff <;> rename_i h
  · exact False.elim (diff rfl)
  · refine ⟨h, ?_⟩
    by_contra! all
    apply diff
    exact congrArg consensus (List.map_congr_left all)

include admissible in
/-- Report disagreement localizes to one eligible nested promotion with a nonempty inherited
context. Its inputs come entirely from the independently regenerated replacement solution. -/
theorem empty_context_disagreement_has_promotion (q : Q) (geom : Geometry)
    (different : solution input mol single frame .accumulated geom [] q ≠
      solution input mol single frame .current geom [] q) :
    ∃ (d : Q) (g : Geometry) (refs : List input.Atom), StrictDescendant mol q.1 d.1 ∧ refs ≠ [] ∧
      let data := (frame d).2
      let family := profileFamily input mol (solution input mol single frame .current) d
      let k := sourceKeysAt input single family data.target data.frame g refs
      ¬ Function.Injective k ∧ ∃ i ∈ sourceSelectedSlots k,
        policyFallback input single .accumulated .regenerated family data.target data.frame g refs i ≠
          policyFallback input single .current .regenerated family data.target data.frame g refs i := by
  obtain ⟨d, below, g, refs, nonempty, diff⟩ := empty_context_disagreement_descends
    input mol admissible single frame q geom different
  let p := solution input mol single frame .current
  by_cases first : raw input mol single frame .accumulated p d g refs =
      raw input mol single frame .current p d g refs
  · have second : raw input mol single frame .accumulated p d (mirror g) refs ≠
        raw input mol single frame .current p d (mirror g) refs := by
      intro same
      apply diff
      exact congrArg₂ caseFromMirror? first same
    exact ⟨d, mirror g, refs, below, nonempty, raw_disagreement input mol single frame p d _ refs second⟩
  · exact ⟨d, g, refs, below, nonempty, raw_disagreement input mol single frame p d _ refs first⟩

set_option maxHeartbeats 40000 in
/-- A replacement step can consult only its incoming table or a singleton table on this
geometry. The unmarked root and all its replacement descendants have at most one mark. -/
private theorem scalar_raw_local (p t : P) (q : Q) (g : Geometry) (refs : List input.Atom)
    (small : refs.length ≤ 1)
    (agree : ∀ ctx : List input.Atom, ctx.length ≤ 1 → ∀ d : Q, StrictDescendant mol q.1 d.1 →
      p g ctx d = t g ctx d) :
    raw input mol single frame .current p q g refs = raw input mol single frame .current t q g refs := by
  have maps (ctx : List input.Atom) (one : ctx.length ≤ 1) :
      profileFamily input mol p q g ctx = profileFamily input mol t q g ctx :=
    LocalizedChemicalRingJointPreparedSourceQueryMap.sourceQueryMap_local input mol q _ _ (agree ctx one)
  let data := (frame q).2
  let k := fun (profile : P) (ctx : List input.Atom) =>
    sourceKeysAt input single (profileFamily input mol profile q) data.target data.frame g ctx
  have keys (ctx : List input.Atom) (one : ctx.length ≤ 1) : k p ctx = k t ctx := by
    unfold k sourceKeysAt
    rw [maps ctx one]
  let fallback := fun (profile : P) i =>
    policyFallback input single .current .regenerated (profileFamily input mol profile q)
      data.target data.frame g refs i
  let select := fun (profile : P) (a : input.Atom) =>
    if Function.Injective (k profile [a]) then sourceReading input g data.frame (k profile [a]) else none
  have selectEq : select p = select t := by
    funext a
    dsimp only [select]
    rw [keys [a] (by simp)]
  have fall (i : Fin 4) : fallback p i = fallback t i :=
    congrArg (fun action => (frameAtom? input data.frame i).bind action) selectEq
  change (if Function.Injective (k p refs) then sourceReading input g data.frame (k p refs) else
    consensus ((sourceSelectedSlots (k p refs)).map (fallback p))) =
    (if Function.Injective (k t refs) then sourceReading input g data.frame (k t refs) else
    consensus ((sourceSelectedSlots (k t refs)).map (fallback t)))
  rw [keys refs small, funext fall]

include admissible in
/-- For a discrepancy in the empty-context report, one *singleton* inherited reference
already distinguishes the two local updates on CURRENT's own derived table. The geometry
at that strict descendant is the actual original geometry or its reflection. -/
theorem disagreement_singleton_on_input (q : Q) (geom : Geometry)
    (different : solution input mol single frame .accumulated geom [] q ≠
      solution input mol single frame .current geom [] q) :
    ∃ (d : Q) (g : Geometry) (a : input.Atom), StrictDescendant mol q.1 d.1 ∧
      (g = geom ∨ g = mirror geom) ∧
      let actual := solution input mol single frame .accumulated
      update input mol single frame .accumulated actual d g [a] ≠
        update input mol single frame .current actual d g [a] := by
  classical
  let actual := solution input mol single frame .accumulated
  let scalar := solution input mol single frame .current
  let sides := fun g : Geometry => g = geom ∨ g = mirror geom
  have flip {g : Geometry} (h : sides g) : sides (mirror g) := by
    rcases h with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (LocalizedChemicalRingOrientationInduction.mirror_mirror geom)
  have wf : WellFormedBonds mol := fun b hb =>
    ⟨(admissible.1.1 b hb).1, (admissible.1.1 b hb).2.1⟩
  by_contra! absent
  have agree (d : Q) : StrictDescendant mol q.1 d.1 →
      ∀ g, sides g → ∀ ctx : List input.Atom, ctx.length ≤ 1 → actual g ctx d = scalar g ctx d := by
    induction d using (measure depth).wf.induction with
    | h d ih =>
      intro below g side ctx small
      rw [show actual g ctx d = _ from solution_equation input mol admissible single frame .accumulated d g ctx,
        show scalar g ctx d = _ from solution_equation input mol admissible single frame .current d g ctx]
      trans update input mol single frame .current actual d g ctx
      · cases ctx with
        | nil => rfl
        | cons a tail =>
          have empty : tail = [] := List.length_eq_zero_iff.mp (by simpa using small)
          subst tail
          exact Classical.byContradiction (absent d g a below side)
      · apply congrArg₂ caseFromMirror?
        all_goals
          apply scalar_raw_local input mol single frame _ _ d _ ctx small
          intro refs one child path
          apply ih child (structuralDepth_lt mol wf d.2.1 path) (below_trans mol below path)
          first | exact side | exact flip side
          exact one
  apply different
  rw [solution_equation input mol admissible single frame .accumulated q geom [],
    solution_equation input mol admissible single frame .current q geom [], first_mark_agrees]
  apply congrArg₂ caseFromMirror?
  all_goals
    apply scalar_raw_local input mol single frame _ _ q _ [] (by simp)
    intro refs one child below
    apply agree child below
    first | exact Or.inl rfl | exact Or.inr rfl
    exact one

include admissible in
/-- On the input or its mirror, disagreement needs one tied slot whose promoted reading
changes when one older atom is kept. Both reads use the accumulated solution. -/
theorem disagreement_singleton_promotion (q : Q) (geom : Geometry)
    (different : solution input mol single frame .accumulated geom [] q ≠
      solution input mol single frame .current geom [] q) :
    ∃ (d : Q) (g : Geometry) (a : input.Atom), StrictDescendant mol q.1 d.1 ∧
      (g = geom ∨ g = mirror geom) ∧
      let data := (frame d).2
      let family := profileFamily input mol (solution input mol single frame .accumulated) d
      let k := sourceKeysAt input single family data.target data.frame g [a]
      ∃ i ∈ sourceSelectedSlots k,
        policyFallback input single .accumulated .regenerated family data.target data.frame g [a] i ≠
          policyFallback input single .current .regenerated family data.target data.frame g [a] i := by
  obtain ⟨d,g,a,path,side,diff⟩ := disagreement_singleton_on_input input mol admissible single frame q geom different
  let actual := solution input mol single frame .accumulated
  by_cases first : raw input mol single frame .accumulated actual d g [a] =
      raw input mol single frame .current actual d g [a]
  · have second : raw input mol single frame .accumulated actual d (mirror g) [a] ≠
        raw input mol single frame .current actual d (mirror g) [a] := by
      intro same
      exact diff (congrArg₂ caseFromMirror? first same)
    have reflected : mirror g = geom ∨ mirror g = mirror geom := by
      rcases side with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl (LocalizedChemicalRingOrientationInduction.mirror_mirror geom)
    exact ⟨d, mirror g, a, path, reflected, (raw_disagreement input mol single frame actual d _ [a] second).2⟩
  · exact ⟨d,g,a,path,side,(raw_disagreement input mol single frame actual d g [a] first).2⟩

/-- Where no other detected occurrence lies below the query, the comparison is independent
of both reference lifetime and auxiliary chronology. Even unrelated starting profiles agree. -/
theorem raw_without_descendants (q : Q)
    (terminal : ∀ d : Q, ¬ StrictDescendant mol q.1 d.1) (life : ReferenceLifetime)
    (chronology : AuxiliaryChronology) (first second : P) (g : Geometry) :
    rawWith input mol single frame life chronology first q g [] =
      raw input mol single frame .accumulated second q g [] := by
  have flat (p : P) : profileFamily input mol p q =
      fun _ _ => LocalizedChemicalRingJointPreparedSourceQueryMap.sourceQueryMap input mol q (fun _ => none) := by
    funext geo refs
    exact LocalizedChemicalRingJointPreparedSourceQueryMap.sourceQueryMap_local input mol q _ _
      (fun d below => False.elim (terminal d below))
  unfold raw rawWith
  rw [flat first, flat second]
  cases life <;> cases chronology <;> rfl

include agreement in
/-- A single detected center is sufficient, even on a cyclic molecular graph: a later
occurrence of the same atom is a duplicate and cannot be a real source query. -/
theorem single_center_no_descendants (c : input.detectedMultiCenterMolecule.Center)
    (onlyCenter : ∀ other : input.detectedMultiCenterMolecule.Center, other = c) :
    ∀ d : Q, ¬ StrictDescendant mol (canonicalCenterRoot c.1.val) d.1 := by
  intro d below
  obtain ⟨other, atom⟩ := d.2.2.2
  have forced : d.1.forcedLeaf = false := by
    simp [RawMolecule.CanonicalBranchNode.forcedLeaf, d.2.2.1]
  exact LocalizedMarkedTerminalReferenceScope.strictDescendant_atom_ne
    (final_query_eligible input mol agreement c).1 below forced
    (by simpa [onlyCenter other] using atom)

/-- Newest event first. Repeated visits are allowed. Every detected descendant must already
have been visited when its parent is processed. -/
inductive DependencyOrder : List Q → Prop
  | empty : DependencyOrder []
  | visit {q : Q} {earlier : List Q} : DependencyOrder earlier →
      (∀ d : Q, StrictDescendant mol q.1 d.1 → d ∈ earlier) → DependencyOrder (q :: earlier)

def replay (life : ReferenceLifetime) (seed : P) : List Q → P
  | [] => seed
  | q :: earlier => fun g refs d =>
      let previous := replay life seed earlier
      if d = q then update input mol single frame life previous q g refs else previous g refs d

include admissible in
/-- Every descendant-first visitation order computes the independently generated solution
at every visited query, from any initial table, for either lifetime and both geometry sides. -/
theorem replay_correct (life : ReferenceLifetime) (seed : P) {events : List Q}
    (ordered : DependencyOrder input mol events) :
    ∀ q ∈ events, ∀ g refs, replay input mol single frame life seed events g refs q =
      solution input mol single frame life g refs q := by
  induction ordered with
  | empty => simp
  | @visit q earlier _ ready ih =>
    intro d member g refs
    by_cases same : d = q
    · subst d
      simp only [replay]
      rw [solution_equation input mol admissible single frame life q g refs]
      exact update_local input mol single frame life _ _ q
        (fun geo ctx child path => ih child (ready child path) geo ctx) g refs
    · simp only [replay, if_neg same]
      exact ih d ((List.mem_cons.mp member).resolve_left same) g refs

end
end TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime.solution_equation
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime.schedule_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime.accumulated_eq_sourceModel
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime.lifetime_eq_iff_nested
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime.empty_context_disagreement_descends
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime.empty_context_disagreement_has_promotion
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime.raw_without_descendants
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime.single_center_no_descendants
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime.replay_correct
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime.disagreement_singleton_on_input
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime.disagreement_singleton_promotion
