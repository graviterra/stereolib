import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Key
import TetraStereo.OneCenter.LocalizedRerootCumulativeRule45Executable

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Executable compound Rules-4b--4c--5 wrappers over occurrence reroot cursors

`LocalizedRerootCompoundRule45Key` defines the normative no/one/`[R,S]` Rule-4b alternatives, the
cumulative Rule-4c reading behind each of them, and the two common-reference Rule-5 readings.  Its
six compilers

* `buildLocalizedRerootRule4bcReading?`,
* `buildLocalizedRerootRule4bcReadings?`,
* `buildLocalizedRerootCompoundRule4bcKey?`,
* `buildLocalizedRerootRule5Reading?`,
* `buildLocalizedRerootRule5Readings?`,
* `buildLocalizedRerootCompoundRule45Key?`

are `noncomputable` only because they call the noncomputable cumulative key compiler
`buildLocalizedRerootCumulativeRule45Key?`.  `LocalizedRerootCumulativeRule45Executable` supplies an
executable twin of that single dependency.

This module therefore re-expresses each of the six wrappers as a plain definition whose only
difference is the replacement of every call to `buildLocalizedRerootCumulativeRule45Key?` by
`buildLocalizedRerootCumulativeRule45KeyExec?`; each recursive call goes to the executable twin of
the wrapper itself.  Nothing else changes: the P-92 reference population
(`localizedRule4bReferencesFromRankedLabels`), the normative `[R,S]` alternative sequence
(`localizedRule4bcReferenceAlternatives`), the reference-count priority, and both common Rule-5
references (`.R` and `.S`) are preserved verbatim, including the fail-closed behaviour.

The six `..._eq_...Exec?` theorems prove every executable wrapper extensionally equal to its
original at arbitrary arguments, so the executable copies return exactly the same keys and exactly
the same `none` answers.  Their only noncomputable input is the cumulative key equality
`buildLocalizedRerootCumulativeRule45KeyExec?_eq_build` of
`LocalizedRerootCumulativeRule45Executable`, read right to left; no other noncomputable declaration
occurs in the six wrappers.
-/

namespace CertifiedLocalizedCIPInput

/-! ## Rule-4b/4c alternatives -/

/-- Executable twin of `buildLocalizedRerootRule4bcReading?`.  Both cumulative stages of one
reference alternative are compiled by the executable cumulative compiler; the `none` alternative
keeps its `rule4a`/`rule4cNoReference` stages and a selected reference keeps its
`.rule4b reference`/`.rule4c reference` stages. -/
def buildLocalizedRerootRule4bcReadingExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option RS → Option input.LocalizedRerootRule4bcReading
  | none => do
      let rule4bKey ← input.buildLocalizedRerootCumulativeRule45KeyExec?
        .rule4a target view fuel cursor
      let rule4cKey ← input.buildLocalizedRerootCumulativeRule45KeyExec?
        .rule4cNoReference target view fuel cursor
      some
        { reference? := none
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey }
  | some reference => do
      let rule4bKey ← input.buildLocalizedRerootCumulativeRule45KeyExec?
        (.rule4b reference) target view fuel cursor
      let rule4cKey ← input.buildLocalizedRerootCumulativeRule45KeyExec?
        (.rule4c reference) target view fuel cursor
      some
        { reference? := some reference
          rule4bKey := rule4bKey
          rule4cKey := rule4cKey }

/-- The executable Rule-4b/4c alternative compiler agrees with the original at every argument. -/
theorem buildLocalizedRerootRule4bcReading?_eq_buildLocalizedRerootRule4bcReadingExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS) :
    input.buildLocalizedRerootRule4bcReading? target view fuel cursor reference =
      input.buildLocalizedRerootRule4bcReadingExec? target view fuel cursor reference := by
  cases reference with
  | none =>
      simp only [buildLocalizedRerootRule4bcReading?,
        buildLocalizedRerootRule4bcReadingExec?,
        ← buildLocalizedRerootCumulativeRule45KeyExec?_eq_build]
  | some reference =>
      simp only [buildLocalizedRerootRule4bcReading?,
        buildLocalizedRerootRule4bcReadingExec?,
        ← buildLocalizedRerootCumulativeRule45KeyExec?_eq_build]

/-- Executable twin of `buildLocalizedRerootRule4bcReadings?`.  The alternative list, in the
normative sequence produced by `localizedRule4bcReferenceAlternatives`, is traversed exactly as
before; failure of any alternative fails the whole list. -/
def buildLocalizedRerootRule4bcReadingsExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List (Option RS) → Option (List input.LocalizedRerootRule4bcReading)
  | [] => some []
  | reference :: references => do
      let reading ← input.buildLocalizedRerootRule4bcReadingExec?
        target view fuel cursor reference
      let readings ← input.buildLocalizedRerootRule4bcReadingsExec?
        target view fuel cursor references
      some (reading :: readings)

/-- The executable alternative-list compiler agrees with the original at every reference list. -/
theorem buildLocalizedRerootRule4bcReadings?_eq_buildLocalizedRerootRule4bcReadingsExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ references,
      input.buildLocalizedRerootRule4bcReadings? target view fuel cursor references =
        input.buildLocalizedRerootRule4bcReadingsExec? target view fuel cursor references
  | [] => by
      simp only [buildLocalizedRerootRule4bcReadings?,
        buildLocalizedRerootRule4bcReadingsExec?]
  | reference :: references => by
      simp only [buildLocalizedRerootRule4bcReadings?,
        buildLocalizedRerootRule4bcReadingsExec?,
        input.buildLocalizedRerootRule4bcReading?_eq_buildLocalizedRerootRule4bcReadingExec?
          target view fuel cursor reference,
        input.buildLocalizedRerootRule4bcReadings?_eq_buildLocalizedRerootRule4bcReadingsExec?
          target view fuel cursor references]

/-- Executable twin of `buildLocalizedRerootCompoundRule4bcKey?`.  The Rule-4a key, the P-92
reference selection, the reference-count priority and the normative alternative list are computed
from the executable cumulative compiler in exactly the original order. -/
def buildLocalizedRerootCompoundRule4bcKeyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule4bcKey := do
  let rule4aKey ← input.buildLocalizedRerootCumulativeRule45KeyExec?
    .rule4a target view fuel cursor
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := localizedRule4bcReferenceAlternatives references
  let readings ← input.buildLocalizedRerootRule4bcReadingsExec?
    target view fuel cursor alternatives
  some
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := readings }

/-- The executable compound Rules-4b/4c compiler agrees with the original, so it selects the same
no/one/`[R,S]` alternatives and the same reference-count priority. -/
theorem buildLocalizedRerootCompoundRule4bcKey?_eq_buildLocalizedRerootCompoundRule4bcKeyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor =
      input.buildLocalizedRerootCompoundRule4bcKeyExec? target view fuel cursor := by
  simp only [buildLocalizedRerootCompoundRule4bcKey?,
    buildLocalizedRerootCompoundRule4bcKeyExec?,
    ← buildLocalizedRerootCumulativeRule45KeyExec?_eq_build,
    input.buildLocalizedRerootRule4bcReadings?_eq_buildLocalizedRerootRule4bcReadingsExec?]

/-! ## Rule-5 readings -/

/-- Executable twin of `buildLocalizedRerootRule5Reading?`.  Both common-reference readings are
compiled by the executable cumulative compiler; the Rule-4b reference of the preceding alternative
chooses the cumulative stage exactly as before, for `.R` and for `.S`. -/
def buildLocalizedRerootRule5ReadingExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading) :
    Option input.LocalizedRerootRule5Reading := do
  let commonR ← input.buildLocalizedRerootCumulativeRule45KeyExec?
    (localizedRule5StageFor prior.reference? .R) target view fuel cursor
  let commonS ← input.buildLocalizedRerootCumulativeRule45KeyExec?
    (localizedRule5StageFor prior.reference? .S) target view fuel cursor
  some { prior := prior, commonR := commonR, commonS := commonS }

/-- The executable pair of common-`R`/common-`S` readings agrees with the original. -/
theorem buildLocalizedRerootRule5Reading?_eq_buildLocalizedRerootRule5ReadingExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading) :
    input.buildLocalizedRerootRule5Reading? target view fuel cursor prior =
      input.buildLocalizedRerootRule5ReadingExec? target view fuel cursor prior := by
  simp only [buildLocalizedRerootRule5Reading?,
    buildLocalizedRerootRule5ReadingExec?,
    ← buildLocalizedRerootCumulativeRule45KeyExec?_eq_build]

/-- Executable twin of `buildLocalizedRerootRule5Readings?`.  The Rule-5 readings are produced in
the canonical prior-reading order, and any failure fails the whole list. -/
def buildLocalizedRerootRule5ReadingsExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    List input.LocalizedRerootRule4bcReading →
      Option (List input.LocalizedRerootRule5Reading)
  | [] => some []
  | prior :: priors => do
      let reading ← input.buildLocalizedRerootRule5ReadingExec?
        target view fuel cursor prior
      let readings ← input.buildLocalizedRerootRule5ReadingsExec?
        target view fuel cursor priors
      some (reading :: readings)

/-- The executable Rule-5 reading list agrees with the original at every prior-reading list. -/
theorem buildLocalizedRerootRule5Readings?_eq_buildLocalizedRerootRule5ReadingsExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ priors,
      input.buildLocalizedRerootRule5Readings? target view fuel cursor priors =
        input.buildLocalizedRerootRule5ReadingsExec? target view fuel cursor priors
  | [] => by
      simp only [buildLocalizedRerootRule5Readings?,
        buildLocalizedRerootRule5ReadingsExec?]
  | prior :: priors => by
      simp only [buildLocalizedRerootRule5Readings?,
        buildLocalizedRerootRule5ReadingsExec?,
        input.buildLocalizedRerootRule5Reading?_eq_buildLocalizedRerootRule5ReadingExec?
          target view fuel cursor prior,
        input.buildLocalizedRerootRule5Readings?_eq_buildLocalizedRerootRule5ReadingsExec?
          target view fuel cursor priors]

/-- Executable twin of `buildLocalizedRerootCompoundRule45Key?`. -/
def buildLocalizedRerootCompoundRule45KeyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    Option input.LocalizedRerootCompoundRule45Key := do
  let prior ← input.buildLocalizedRerootCompoundRule4bcKeyExec?
    target view fuel cursor
  let readings ← input.buildLocalizedRerootRule5ReadingsExec?
    target view fuel cursor prior.readings
  some { prior := prior, rule5Readings := readings }

/-- The executable through-Rule-5 compound compiler agrees with the original at every argument. -/
theorem buildLocalizedRerootCompoundRule45Key?_eq_buildLocalizedRerootCompoundRule45KeyExec?
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    input.buildLocalizedRerootCompoundRule45Key? target view fuel cursor =
      input.buildLocalizedRerootCompoundRule45KeyExec? target view fuel cursor := by
  simp only [buildLocalizedRerootCompoundRule45Key?,
    buildLocalizedRerootCompoundRule45KeyExec?,
    input.buildLocalizedRerootCompoundRule4bcKey?_eq_buildLocalizedRerootCompoundRule4bcKeyExec?,
    input.buildLocalizedRerootRule5Readings?_eq_buildLocalizedRerootRule5ReadingsExec?]

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
