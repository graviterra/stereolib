import TetraStereo.OneCenter.LocalizedChemicalRingRegeneratedLifetime

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace TetraStereo.OneCenter.LocalizedChemicalRingFrozenChronology

open CertifiedLocalizedCIPInput LocalizedChemicalRingJointPreparedSourceModel
open LocalizedChemicalRingRegeneratedLifetime (rawWith)
open LocalizedChemicalRingReferencePolicy (ReferenceLifetime)
open LocalizedChemicalRingJointPreparedSourceQueries (SourceQuery)
open LocalizedChemicalRingInheritedRefusalCases (OccurrenceData)
open LocalizedGenericMarkedRecalculation (Geometry consensus mirror caseFromMirror? structuralDepth WellFormedBonds)
open LocalizedMarkedTerminalReferenceScope (StrictDescendant)
open LocalizedChemicalRingJointPreparedStructuralProfile (structuralDepth_lt)
open scoped Classical
noncomputable section

variable (input : CertifiedLocalizedCIPInput) (mol : RawMolecule)
  (admissible : mol.StereochemicalAdmissible) (single : input.moleculeGraph.SimpleBonded)
local notation "Q" => SourceQuery input mol
local notation "P" => Profile input mol
variable (frame : (q : SourceQuery input mol) →
  (Σ c : input.detectedMultiCenterMolecule.Center, OccurrenceData input mol c q.1))

abbrev UnmarkedProfile := Geometry → SourceQuery input mol → Option LocalizedAuxiliaryLabel

def lift (t : UnmarkedProfile input mol) : P := fun g _ q => t g q

/-- The frozen root equation stores one label per occurrence and geometry. A ranker
still has access to the promoted atom when comparing ligands. -/
def update (t : UnmarkedProfile input mol) (q : Q) (g : Geometry) : Option LocalizedAuxiliaryLabel :=
  LocalizedChemicalRingRegeneratedLifetime.update input mol single frame .accumulated
    (fun geo _ inner => t geo inner) q g []

/-- Both frozen reference-lifetime rules factor through the very same unmarked update,
even on arbitrary contextual tables and before any fixed-point hypothesis. -/
theorem erase (life : ReferenceLifetime) (p : P) (q : Q) (g : Geometry) :
    caseFromMirror? (rawWith input mol single frame life .frozen p q g [])
      (rawWith input mol single frame life .frozen p q (mirror g) []) =
      update input mol single frame (fun geo d => p geo [] d) q g := by
  cases life <;> rfl

theorem update_local (t u : UnmarkedProfile input mol) (q : Q)
    (agree : ∀ g (d : Q), StrictDescendant mol q.1 d.1 → t g d = u g d) (g : Geometry) :
    update input mol single frame t q g = update input mol single frame u q g :=
  LocalizedChemicalRingRegeneratedLifetime.update_local input mol single frame .accumulated
    _ _ q (fun geo _ d below => agree geo d below) g []

private abbrev depth (q : SourceQuery input mol) := structuralDepth mol q.1

/-- A depth-ordered bottom-up pass with arbitrary initial data and optional extra updates. -/
def rounds (refresh : Nat → Q → Bool) (seed : UnmarkedProfile input mol) : Nat → UnmarkedProfile input mol
  | 0 => seed
  | n+1 => fun g q =>
    let prev := rounds refresh seed n
    if refresh n q then update input mol single frame prev q g else prev g q

private abbrev wfBonds : WellFormedBonds mol := fun b hb =>
  ⟨(admissible.1.1 b hb).1, (admissible.1.1 b hb).2.1⟩

def solution (g : Geometry) (q : Q) :=
  rounds input mol single frame (fun _ _ => true) (fun _ _ => none) (depth input mol q + 1) g q

include admissible in
private theorem stable (q : Q) : ∀ n m, depth input mol q < n → depth input mol q < m → ∀ g,
    rounds input mol single frame (fun _ _ => true) (fun _ _ => none) n g q =
    rounds input mol single frame (fun _ _ => true) (fun _ _ => none) m g q := by
  induction q using (measure (depth input mol)).wf.induction with
  | h q ih =>
    intro n m hn hm g
    cases n with
    | zero => omega
    | succ n =>
      cases m with
      | zero => omega
      | succ m =>
        simp only [rounds, if_true]
        apply update_local
        intro geo d below
        have lt := structuralDepth_lt mol (wfBonds mol admissible) q.2.1 below
        exact ih d lt n m (Nat.lt_of_lt_of_le lt (Nat.le_of_lt_succ hn))
          (Nat.lt_of_lt_of_le lt (Nat.le_of_lt_succ hm)) geo

include admissible in
theorem solution_equation (q : Q) (g : Geometry) :
    solution input mol single frame g q = update input mol single frame
      (solution input mol single frame) q g := by
  unfold solution
  simp only [rounds, if_true]
  apply update_local
  intro geo d below
  exact stable input mol admissible single frame d _ _
    (structuralDepth_lt mol (wfBonds mol admissible) q.2.1 below) (Nat.lt_succ_self _) geo

include admissible in
theorem schedule_independent (refresh : Nat → Q → Bool)
    (covers : ∀ q, refresh (depth input mol q) q = true) (seed : UnmarkedProfile input mol) (n : Nat) :
    ∀ q, depth input mol q < n → ∀ g, rounds input mol single frame refresh seed n g q =
      solution input mol single frame g q := by
  induction n with
  | zero => intro q h; omega
  | succ n ih =>
    intro q ready geo
    simp only [rounds]
    split <;> rename_i test
    · rw [solution_equation input mol admissible single frame q geo]
      apply update_local
      intro g d below
      exact ih d (Nat.lt_of_lt_of_le (structuralDepth_lt mol (wfBonds mol admissible) q.2.1 below)
        (Nat.le_of_lt_succ ready)) g
    · apply ih q _ geo
      by_contra! h
      exact test ((Nat.le_antisymm (Nat.le_of_lt_succ ready) h) ▸ covers q)

include admissible in
/-- The same unique frozen result at every detected occurrence, for arbitrary choices
of lifetime per occurrence and geometry, with no restrictions on nonempty profile entries. -/
theorem frozen_profile_eq (life : Geometry → Q → ReferenceLifetime) (p : P)
    (solves : ∀ g q, p g [] q =
      caseFromMirror? (rawWith input mol single frame (life g q) .frozen p q g [])
        (rawWith input mol single frame (life g q) .frozen p q (mirror g) [])) :
    ∀ q g, p g [] q = solution input mol single frame g q := by
  intro q
  induction q using (measure (depth input mol)).wf.induction with
  | h q ih =>
    intro g
    rw [solves, erase, solution_equation input mol admissible single frame]
    apply update_local
    intro geo d below
    exact ih d (structuralDepth_lt mol (wfBonds mol admissible) q.2.1 below) geo

include admissible in
/-- An exact chronology test on the named source profile. All unmarked occurrence
labels coincide with the frozen policy iff their values satisfy the erased equations. -/
theorem agrees_iff (p : P) :
    (∀ q g, p g [] q = solution input mol single frame g q) ↔
    ∀ q g, p g [] q = update input mol single frame (fun geo d => p geo [] d) q g := by
  constructor
  · intro agree q g
    rw [agree,solution_equation input mol admissible single frame]
    exact update_local input mol single frame _ _ q (fun geo d _ => (agree d geo).symm) g
  · intro eqn
    apply frozen_profile_eq input mol admissible single frame (fun _ _ => .current)
    intro g q
    rw [erase]
    exact eqn q g

open LocalizedChemicalRingJointPreparedSourceStep
open LocalizedChemicalRingReferencePolicy (policyFallback)

/-- A local causal witness. The two trials select the same eligible ligand at the
same tied ranking. Its atom changes a strictly deeper auxiliary descriptor. -/
def Impact (p : P) (q : Q) (g : Geometry) : Prop :=
  let data := (frame q).2
  let fam := profileFamily input mol p q
  let key := sourceKeysAt input single fam data.target data.frame g []
  ¬ Function.Injective key ∧
    ∃ i ∈ sourceSelectedSlots key, ∃ a : input.Atom, frameAtom? input data.frame i = some a ∧
      policyFallback input single .accumulated .regenerated fam data.target data.frame g [] i ≠
        policyFallback input single .accumulated .frozen fam data.target data.frame g [] i ∧
      ∃ d : Q, StrictDescendant mol q.1 d.1 ∧ p g [a] d ≠ p g [] d

private theorem raw_impact (p : P) (q : Q) (g : Geometry)
    (diff : rawWith input mol single frame .accumulated .regenerated p q g [] ≠
      rawWith input mol single frame .accumulated .frozen p q g []) :
    Impact input mol single frame p q g := by
  let data := (frame q).2
  let fam := profileFamily input mol p q
  let key := sourceKeysAt input single fam data.target data.frame g []
  let read := fun chronology => policyFallback input single .accumulated chronology
    fam data.target data.frame g []
  change (if Function.Injective key then sourceReading input g data.frame key else
    consensus ((sourceSelectedSlots key).map (read .regenerated))) ≠
    (if Function.Injective key then sourceReading input g data.frame key else
    consensus ((sourceSelectedSlots key).map (read .frozen))) at diff
  by_cases sep : Function.Injective key
  · simp [sep] at diff
  simp only [if_neg sep] at diff
  obtain ⟨i,hi,changeAt⟩ : ∃ i ∈ sourceSelectedSlots key, read .regenerated i ≠ read .frozen i := by
    by_contra! all
    exact diff (congrArg consensus (List.map_congr_left all))
  refine ⟨sep,i,hi,?_⟩
  cases mark : frameAtom? input data.frame i with
  | none => simp [read,policyFallback,mark] at changeAt
  | some a =>
    refine ⟨a,rfl,changeAt,?_⟩
    by_contra! all
    have maps : fam g [a] = fam g [] :=
      LocalizedChemicalRingJointPreparedSourceQueryMap.sourceQueryMap_local input mol q _ _ all
    apply changeAt
    simp only [read,policyFallback,mark,Option.bind_some,LocalizedChemicalRingReferencePolicy.extend,
      List.nil_append]
    unfold sourceKeysAt
    dsimp only
    rw [maps]

private theorem lower_trans {x y z : Q} (xy : StrictDescendant mol x.1 y.1)
    (yz : StrictDescendant mol y.1 z.1) : StrictDescendant mol x.1 z.1 := by
  obtain ⟨a,ha,ab⟩ := xy
  obtain ⟨b,hb,bc⟩ := yz
  exact ⟨a,ha,(ab.tail hb).trans bc⟩

private theorem unmarkedRaw_local (p t : UnmarkedProfile input mol) (q : Q) (g : Geometry)
    (agree : ∀ d : Q, StrictDescendant mol q.1 d.1 → p g d = t g d) :
    rawWith input mol single frame .accumulated .regenerated (lift input mol p) q g [] =
    rawWith input mol single frame .accumulated .regenerated (lift input mol t) q g [] := by
  let constant := fun (u : UnmarkedProfile input mol) => lift input mol (fun _ => u g)
  change rawWith input mol single frame .accumulated .regenerated (constant p) q g [] =
    rawWith input mol single frame .accumulated .regenerated (constant t) q g []
  unfold rawWith
  rw [profileFamily_local input mol q (constant p) (constant t) (fun _ _ => agree)]

include admissible in
/-- A final discrepancy implies a specific changed promoted reading and a distinct,
strictly downstream changed descriptor on that very geometry and selected atom. -/
theorem report_impact (p : P) (model : SourceModel input mol single p) (q : Q) :
    ∀ g, p g [] q ≠ solution input mol single frame g q →
      ∃ (parent : Q) (side : Geometry), (parent = q ∨ StrictDescendant mol q.1 parent.1) ∧
        (side = g ∨ side = mirror g) ∧ Impact input mol single frame p parent side := by
  induction q using (measure (depth input mol)).wf.induction with
  | h q ih =>
    intro g different
    let base := fun geo (d : Q) => p geo [] d
    have equation : p g [] q = LocalizedChemicalRingRegeneratedLifetime.update
        input mol single frame .accumulated p q g [] :=
      (model g [] q (frame q).1 (frame q).2).symm
    by_cases here : p g [] q ≠ update input mol single frame base q g
    · have rawDiff : ∃ side, (side = g ∨ side = mirror g) ∧
          rawWith input mol single frame .accumulated .regenerated p q side [] ≠
          rawWith input mol single frame .accumulated .frozen p q side [] := by
        by_contra! same
        apply here
        rw [equation, ← erase input mol single frame .accumulated p q g]
        exact congrArg₂ caseFromMirror? (same g (Or.inl rfl)) (same (mirror g) (Or.inr rfl))
      obtain ⟨side,hs,hraw⟩ := rawDiff
      exact ⟨q,side,Or.inl rfl,hs,raw_impact input mol single frame p q side hraw⟩
    · have childDiff : ∃ (d : Q) (side : Geometry), StrictDescendant mol q.1 d.1 ∧
          (side = g ∨ side = mirror g) ∧ p side [] d ≠ solution input mol single frame side d := by
        by_contra! same
        apply different
        rw [Classical.not_not.mp here, solution_equation input mol admissible single frame]
        apply congrArg₂ caseFromMirror?
        · exact unmarkedRaw_local input mol single frame base _ q g
            (fun d below => same d g below (Or.inl rfl))
        · exact unmarkedRaw_local input mol single frame base _ q (mirror g)
            (fun d below => same d (mirror g) below (Or.inr rfl))
      obtain ⟨d,geo,below,hs,hbad⟩ := childDiff
      obtain ⟨parent,side,whereAt,hs',effect⟩ := ih d
        (structuralDepth_lt mol (wfBonds mol admissible) q.2.1 below) geo hbad
      refine ⟨parent,side,Or.inr ?_,?_,effect⟩
      · rcases whereAt with rfl | path
        · exact below
        · exact lower_trans input mol below path
      · rcases hs with rfl | rfl <;> rcases hs' with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
        · exact Or.inr rfl
        · exact Or.inl (LocalizedChemicalRingOrientationInduction.mirror_mirror g)


end
end TetraStereo.OneCenter.LocalizedChemicalRingFrozenChronology

assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFrozenChronology.erase
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFrozenChronology.solution_equation
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFrozenChronology.schedule_independent
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFrozenChronology.frozen_profile_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFrozenChronology.agrees_iff
assert_kernel_only TetraStereo.OneCenter.LocalizedChemicalRingFrozenChronology.report_impact
