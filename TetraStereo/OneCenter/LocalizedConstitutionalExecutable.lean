import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Executable
import TetraStereo.OneCenter.LocalizedRerootFuelCompleteness
import TetraStereo.OneCenter.LocalizedConstitutionalObservable

set_option autoImplicit false
namespace TetraStereo.OneCenter.CertifiedLocalizedCIPInput

/-- Executable complete Rules-1a--2 compiler. Only the certified child enumerator differs from
its existing proof-facing counterpart. -/
def buildLocalizedRerootRuleMajorKeyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    Nat → input.LocalizedRerootCursor carrierFuel → Option (OfficialRuleMajorKey input.Atom)
  | 0, cursor => do
      let children ← input.executableLocalizedRerootChildren? cursor
      if children = [] then
        some (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true)
      else none
  | fuel + 1, cursor => do
      let children ← input.executableLocalizedRerootChildren? cursor
      if children = [] then
        some (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true)
      else
        let childKeys ← children.mapM (input.buildLocalizedRerootRuleMajorKeyExec? fuel)
        let sorted ← OfficialRuleMajorKey.sort? childKeys
        some (OfficialRuleMajorKey.assemble
          (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false) sorted)

/-- Exact Option equality, including every refusal, at every cursor and budget. -/
theorem buildLocalizedRerootRuleMajorKeyExec?_eq_original
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ fuel (cursor : input.LocalizedRerootCursor carrierFuel),
      input.buildLocalizedRerootRuleMajorKeyExec? fuel cursor =
        input.buildLocalizedRerootRuleMajorKey? fuel cursor := by
  intro fuel
  induction fuel with
  | zero =>
      intro cursor
      simp only [buildLocalizedRerootRuleMajorKeyExec?, buildLocalizedRerootRuleMajorKey?,
        executableLocalizedRerootChildren?_eq_localizedRerootChildren]
  | succ fuel ih =>
      intro cursor
      have functions : input.buildLocalizedRerootRuleMajorKeyExec? fuel =
          input.buildLocalizedRerootRuleMajorKey? (carrierFuel := carrierFuel) fuel := funext ih
      simp only [buildLocalizedRerootRuleMajorKeyExec?, buildLocalizedRerootRuleMajorKey?,
        executableLocalizedRerootChildren?_eq_localizedRerootChildren, functions]

theorem buildLocalizedRerootRuleMajorKeyExec?_sound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : OfficialRuleMajorKey input.Atom)
    (computed : input.buildLocalizedRerootRuleMajorKeyExec? fuel cursor = some key) :
    input.DeclarativeLocalizedRerootRuleMajorKey fuel cursor key := by
  apply input.buildLocalizedRerootRuleMajorKey?_sound fuel cursor key
  rwa [input.buildLocalizedRerootRuleMajorKeyExec?_eq_original] at computed

theorem buildLocalizedRerootRuleMajorKeyExec?_complete
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : OfficialRuleMajorKey input.Atom)
    (computed : input.buildLocalizedRerootRuleMajorKeyExec? fuel cursor = some key) :
    key.complete = true := by
  apply input.buildLocalizedRerootRuleMajorKey?_complete fuel cursor key
  rwa [input.buildLocalizedRerootRuleMajorKeyExec?_eq_original] at computed

private theorem mapM_exists_complete {α V : Type*}
    (f : α → Option (OfficialRuleMajorKey V))
    (complete : ∀ value key, f value = some key → key.complete = true) :
    ∀ values : List α,
      (∀ value ∈ values, ∃ key, f value = some key) →
      ∃ keys, values.mapM f = some keys ∧ ∀ key ∈ keys, key.complete = true
  | [], _ => ⟨[], rfl, by simp⟩
  | value :: values, total => by
      obtain ⟨key, head⟩ := total value (by simp)
      obtain ⟨keys, tail, allComplete⟩ := mapM_exists_complete f complete values
        (fun value present => total value (by simp [present]))
      refine ⟨key :: keys, by simp [head, tail], ?_⟩
      intro child present
      rcases List.mem_cons.mp present with rfl | present
      · exact complete value _ head
      · exact allComplete child present

/-- Structural cursor depth suffices for the complete constitutional compiler. This requires no
stereo callback, auxiliary view, endpoint readiness or assumption that a desired key exists. -/
theorem exists_constitutionalKey_of_budget_lt
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} :
    ∀ fuel (cursor : input.LocalizedRerootCursor carrierFuel),
      input.LocalizedRerootCursorValid cursor →
      input.localizedRerootCursorBudget cursor < fuel →
      ∃ key, input.buildLocalizedRerootRuleMajorKeyExec? fuel cursor = some key
  | 0, _, _, covered => by omega
  | fuel + 1, cursor, valid, covered => by
      let children := input.executableLocalizedRerootChildren cursor
      have computed : input.executableLocalizedRerootChildren? cursor = some children := rfl
      have derived := input.executableLocalizedRerootChildren_declarative cursor
      by_cases empty : children = []
      · exact ⟨input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node true,
          by simp [buildLocalizedRerootRuleMajorKeyExec?, computed, empty]⟩
      · have total : ∀ child ∈ children, ∃ key,
            input.buildLocalizedRerootRuleMajorKeyExec? fuel child = some key := by
          intro child present
          have childValid := input.localizedRerootChild_valid cursor child children derived present
          have decreases := input.localizedRerootChild_budget_lt
            cursor child children valid derived present
          apply input.exists_constitutionalKey_of_budget_lt fuel child childValid
          omega
        obtain ⟨childKeys, childComputed, complete⟩ := mapM_exists_complete
          (input.buildLocalizedRerootRuleMajorKeyExec? fuel)
          (input.buildLocalizedRerootRuleMajorKeyExec?_complete fuel) children total
        have sortable := OfficialRuleMajorKey.sort?_isSome_of_complete childKeys complete
        cases sortedComputed : OfficialRuleMajorKey.sort? childKeys with
        | none => simp [sortedComputed] at sortable
        | some sorted =>
            exact ⟨OfficialRuleMajorKey.assemble
              (input.moleculeGraph.officialRuleMajorRootKey cursor.occurrence.1.node false) sorted,
              by simp [buildLocalizedRerootRuleMajorKeyExec?, computed, empty,
                childComputed, sortedComputed]⟩

/-- A single input-derived linear budget covers every path-valid cursor. -/
theorem exists_constitutionalKey_at_linear_bound
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (cursor : input.LocalizedRerootCursor carrierFuel)
    (valid : input.LocalizedRerootCursorValid cursor) :
    ∃ key, input.buildLocalizedRerootRuleMajorKeyExec?
      (2 * (carrierFuel + 1) + 1) cursor = some key := by
  apply input.exists_constitutionalKey_of_budget_lt _ cursor valid
  have bounded := input.localizedRerootCursorBudget_le_twice cursor
  omega

/-- All successful budgets give the same comparison-visible answer. -/
theorem constitutionalKeyExec_observable_stable
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (leftFuel rightFuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (left right : OfficialRuleMajorKey input.Atom)
    (hl : input.buildLocalizedRerootRuleMajorKeyExec? leftFuel cursor = some left)
    (hr : input.buildLocalizedRerootRuleMajorKeyExec? rightFuel cursor = some right) :
    constitutionalObservable left = constitutionalObservable right :=
  input.declarative_constitutional_observable_unique leftFuel rightFuel cursor left right
    (input.buildLocalizedRerootRuleMajorKeyExec?_sound leftFuel cursor left hl)
    (input.buildLocalizedRerootRuleMajorKeyExec?_sound rightFuel cursor right hr)

/-- Complete constitutional comparison at the common structural budget. A refusal remains explicit
for arbitrary cursors; both keys exist for path-valid cursors. -/
def compareLocalizedConstitutionalCursors?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel) : Option Ordering := do
  let firstKey ← input.buildLocalizedRerootRuleMajorKeyExec? (2 * (carrierFuel + 1) + 1) first
  let secondKey ← input.buildLocalizedRerootRuleMajorKeyExec? (2 * (carrierFuel + 1) + 1) second
  some (OfficialRuleMajorKey.compare firstKey secondKey)

theorem compareLocalizedConstitutionalCursors?_computations
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel) (outcome : Ordering)
    (computed : input.compareLocalizedConstitutionalCursors? first second = some outcome) :
    ∃ firstKey secondKey,
      input.buildLocalizedRerootRuleMajorKeyExec? (2 * (carrierFuel + 1) + 1) first = some firstKey ∧
      input.buildLocalizedRerootRuleMajorKeyExec? (2 * (carrierFuel + 1) + 1) second = some secondKey ∧
      OfficialRuleMajorKey.compare firstKey secondKey = outcome := by
  unfold compareLocalizedConstitutionalCursors? at computed
  cases left : input.buildLocalizedRerootRuleMajorKeyExec? (2 * (carrierFuel + 1) + 1) first with
  | none => simp [left] at computed
  | some firstKey =>
      cases right : input.buildLocalizedRerootRuleMajorKeyExec? (2 * (carrierFuel + 1) + 1) second with
      | none => simp [left, right] at computed
      | some secondKey =>
          exact ⟨firstKey, secondKey, rfl, rfl, by simpa [left, right] using computed⟩

theorem compareLocalizedConstitutionalCursors?_total
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (first second : input.LocalizedRerootCursor carrierFuel)
    (firstValid : input.LocalizedRerootCursorValid first)
    (secondValid : input.LocalizedRerootCursorValid second) :
    ∃ outcome, input.compareLocalizedConstitutionalCursors? first second = some outcome := by
  obtain ⟨firstKey, left⟩ := input.exists_constitutionalKey_at_linear_bound first firstValid
  obtain ⟨secondKey, right⟩ := input.exists_constitutionalKey_at_linear_bound second secondValid
  exact ⟨OfficialRuleMajorKey.compare firstKey secondKey,
    by simp [compareLocalizedConstitutionalCursors?, left, right]⟩

end TetraStereo.OneCenter.CertifiedLocalizedCIPInput
