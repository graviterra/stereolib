import TetraStereo.OneCenter.PublicExactConstitutionalObservable
import TetraStereo.OneCenter.PublicParametricCompoundRule45Key
import TetraStereo.OneCenter.PublicParametricRule45Availability
import TetraStereo.OneCenter.LocalizedConstitutionalRootSeparation
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter
namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-!
# Exact constitutional observables of the public compound Rules-4b/4c/5 builders

`PublicExactConstitutionalObservable` proves that the actual public cumulative Rules-4a--5
builder, driven by an arbitrary total label reader, has a reader-independent exact constitutional
observable: the whole `Option`-valued build, including the fail-closed `none` outcome, projects
through `cumulativeRule45ConstitutionalObservable` to the same value for any two readers at the
same stage, fuel and cursor.  `PublicParametricCompoundRule45Key` assembles the actual public
compound Rules-4b/4c/5 layers from that cumulative builder, but leaves the observable question
open at the compound level.

This module closes that gap on the actual executable definitions:

* It generalises the observable-independence theorem from one fixed stage to *two arbitrary
  stages*.  The constitutional component of a cumulative key never mentions the stage; only the
  later-rule descriptor (and therefore sibling order) does, and the proof passes through sorted
  permutation uniqueness of exact constitutional observables exactly as the one-stage theorem did.
* It shows that success (`Option.isSome`) of every one of the six actual compound builders is
  independent of the reader, the reference alternative and the stage.  The cumulative builder's
  terminal test is structural, so its fail-closed outcome cannot depend on label data; the
  reference-alternative list is always nonempty, so a readings list cannot succeed vacuously
  before its alternatives have been compiled.
* It defines the canonical exact constitutional observable of each compound layer -- the Rule-4b
  cumulative key of a Rule-4b/4c reading, the Rule-4a cumulative key of a compound Rules-4b/4c
  key, the common-R cumulative key of a Rule-5 reading, and the Rule-4a cumulative key under the
  prior of a complete through-Rule-5 key -- and proves the full `Option` projection theorem for
  the four key-producing builders at *arbitrary* fuel, cursor and reference alternative, with no
  success hypothesis.  The two readings-list builders are covered by an `Option`-level head
  projection and by pointwise membership equalities under the (discharged) nonempty-alternatives
  hypothesis of the actual compound layers.
* It exports the actual source-ordinal root-distance insulation.  A successful cumulative build
  begins its Rule-1b projection with `[([], d)]` at the original-root distance of the compiled
  cursor node, and a successful compound Rules-4b/4c or through-Rule-5 build begins the Rule-1b
  projection of its extracted Rule-4a key the same way.  Keys whose constitutional heads sit at
  different root distances therefore cannot compare equal constitutionally, whatever reader,
  stage, fuel or reference selection produced them.  Consequently the shipped cumulative
  comparator, whose first component is the exact constitutional comparison, is *reader-invariant
  whenever that constitutional comparison is strict*: its outcome is then exactly the strict
  constitutional outcome.  The reader-invariance endpoints are supplied both for actual Rule-4a
  cumulative builds and for the extracted Rule-4a keys of actual compound Rules-4b/4c and
  through-Rule-5 builds, including the source root-distance case.  On a constitutional tie the
  descriptor field is consulted, and this module makes no reader-invariance claim there; in
  particular it makes no claim about the compound descriptor comparators
  `compareAromaticCanonicalRerootCompoundRule4bcKeys` / `...Rule45Keys`, which never inspect the
  constitutional field.

## Scope and honesty

Everything is stated on the actual public structures and the actual parametric builders imported
from `PublicParametricCompoundRule45Key`; no key is rebuilt, collapsed or reordered.  Both
`commonR`/`commonS` readings and the no/one/two-reference alternatives are retained.  The
constitutional values are read through the semantic exact Rule-1a observation, i.e. through the
`Rat` value carried by `DeclarativeCIP.ExactAtomicNumber.value`, never through equality of
`ExactAtomicNumber` records.  No `noMancude` hypothesis and no desired-success hypothesis is
assumed: the projection theorems quantify over all fuel and cursor values and therefore cover the
`none` outcomes, and success at the structural bound `2 * (carrierFuel + 1)` is the already
verified availability theorem of `PublicParametricRule45Availability`.
-/

/-! ## Canonical exact constitutional observable of each compound layer -/

/-- Exact constitutional observable of one actual Rule-4b/4c reading, read from its Rule-4b
cumulative key.  The Rule-4c key of the same reading carries the same observable; that equality is
proved below from the stage-general independence theorem, so choosing the Rule-4b constituent does
not discard constitutional information. -/
def rule4bcReadingConstitutionalObservable
    (source : AuthoritativeChemicalInput)
    (reading : source.AromaticCanonicalRerootRule4bcReading) :
    ExactConstitutionalObservable :=
  cumulativeRule45ConstitutionalObservable source reading.rule4bKey

/-- Exact constitutional observable of an actual compound Rules-4b/4c key, read from the Rule-4a
cumulative key that the builder actually compiled.  This is the field the shipped cumulative
comparator inspects first and the field a parent-versus-outward comparison short-circuits on. -/
def compoundRule4bcConstitutionalObservable
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey) :
    ExactConstitutionalObservable :=
  cumulativeRule45ConstitutionalObservable source key.rule4aKey

/-- Exact constitutional observable of one actual Rule-5 reading, read from its common-R
cumulative key.  The common-S key of the same reading carries the same observable; that equality
is proved below. -/
def rule5ReadingConstitutionalObservable
    (source : AuthoritativeChemicalInput)
    (reading : source.AromaticCanonicalRerootRule5Reading) :
    ExactConstitutionalObservable :=
  cumulativeRule45ConstitutionalObservable source reading.commonR

/-- Exact constitutional observable of an actual complete through-Rule-5 compound key, read from
the Rule-4a cumulative key inside the prior Rules-4b/4c key.  Both the alternatives of the prior
layer and every common-R/common-S Rule-5 reading are retained by the key; this projection exposes
the single constitutional value they all share. -/
def compoundRule45ConstitutionalObservable
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalRerootCompoundRule45Key) :
    ExactConstitutionalObservable :=
  cumulativeRule45ConstitutionalObservable source key.prior.rule4aKey

/-! ## Structural `Option` lemmas -/

/-- The `Bind`-class syntactic form of `Option.bind_some`, matching `do`-notation. -/
private theorem bind_some_option_compound {α β : Type _} (value : α) (next : α → Option β) :
    Bind.bind (some value) next = next value := rfl

/-- The `Bind`-class syntactic form of `Option.bind_none`, matching `do`-notation. -/
private theorem bind_none_option_compound {α β : Type _} (next : α → Option β) :
    Bind.bind (none : Option α) next = none := rfl

/-- Pointwise agreement of the projected options lifts through `List.mapM`.  This is the local
copy of the helper used by the one-stage observable-independence proof; the original is private to
`PublicExactConstitutionalObservable`, so the argument is reproduced here on the same `Bind.bind`
syntactic form that `do`-notation elaborates. -/
private theorem list_mapM_map_projection_compound {α β γ : Type _}
    (first second : α → Option β) (project : β → γ)
    (agrees : ∀ value, (first value).map project = (second value).map project) :
    ∀ values : List α,
      (values.mapM first).map (List.map project) =
        (values.mapM second).map (List.map project)
  | [] => rfl
  | value :: values => by
      rw [List.mapM_cons, List.mapM_cons]
      have inner : ∀ chosen : β,
          Option.map (List.map project)
              ((values.mapM first).bind (fun rest => some (chosen :: rest))) =
            Option.map (List.map project)
              ((values.mapM second).bind (fun rest => some (chosen :: rest))) := by
        intro chosen
        rw [Option.map_bind, Option.map_bind]
        show (values.mapM first).bind
              (fun rest => some (project chosen :: List.map project rest)) =
            (values.mapM second).bind
              (fun rest => some (project chosen :: List.map project rest))
        have firstNormalized :
            (values.mapM first).bind
                (fun rest => some (project chosen :: List.map project rest)) =
              (values.mapM first).map
                (fun rest => project chosen :: List.map project rest) := by
          cases List.mapM first values <;> rfl
        have secondNormalized :
            (values.mapM second).bind
                (fun rest => some (project chosen :: List.map project rest)) =
              (values.mapM second).map
                (fun rest => project chosen :: List.map project rest) := by
          cases List.mapM second values <;> rfl
        rw [firstNormalized, secondNormalized]
        have combined := congrArg
          (Option.map (fun rest : List γ => project chosen :: rest))
          (list_mapM_map_projection_compound first second project agrees values)
        rw [Option.map_map, Option.map_map] at combined
        exact combined
      cases firstComputed : first value with
      | none =>
          have secondComputed : second value = none := by
            have pointwise := agrees value
            rw [firstComputed] at pointwise
            cases secondValue : second value with
            | none => rfl
            | some _ => simp [secondValue] at pointwise
          rw [secondComputed]
          rfl
      | some head =>
          have secondValue :
              ∃ other, second value = some other ∧ project head = project other := by
            have pointwise := agrees value
            rw [firstComputed] at pointwise
            cases secondComputed : second value with
            | none => simp [secondComputed] at pointwise
            | some other =>
                simp [secondComputed] at pointwise
                exact ⟨other, rfl, pointwise⟩
          obtain ⟨other, secondComputed, projectionEq⟩ := secondValue
          rw [secondComputed]
          show Option.map (List.map project)
                ((values.mapM first).bind (fun rest => some (head :: rest))) =
              Option.map (List.map project)
                ((values.mapM second).bind (fun rest => some (other :: rest)))
          rw [inner head]
          rw [Option.map_bind, Option.map_bind]
          show (values.mapM second).bind
                (fun rest => some (project head :: List.map project rest)) =
              (values.mapM second).bind
                (fun rest => some (project other :: List.map project rest))
          rw [projectionEq]

/-- `isSome` of a `do`-block whose final statement is `some` is the `isSome` of its last bind. -/
private theorem isSome_bind_some_compound {α β : Type _} (value : Option α) (next : α → β) :
    (Bind.bind value (fun chosen => some (next chosen))).isSome = value.isSome := by
  cases value <;> rfl

/-- `isSome` of a bind whose continuation maps a chosen value into a bare list cons. -/
private theorem isSome_bind_cons_compound {β : Type _} (value : β) (tail : Option (List β)) :
    (Bind.bind tail (fun rest => some (value :: rest))).isSome = tail.isSome := by
  cases tail <;> rfl

/-- The `isSome` of a two-step `do`-block is the conjunction of the `isSome` of its first step
and the `isSome` of its continuation at any successful first value. -/
private theorem isSome_bind_eq_and {α β : Type _} (value : Option α)
    (next : α → Option β) (headValue tailValue : Bool)
    (headShape : value.isSome = headValue)
    (tailShape : ∀ chosen, value = some chosen → (next chosen).isSome = tailValue) :
    (Bind.bind value next).isSome = (headValue && tailValue) := by
  cases value with
  | none =>
      rw [← headShape]
      simp
  | some chosen =>
      rw [bind_some_option_compound, tailShape chosen rfl, ← headShape]
      simp

/-- If two options have the same `isSome` and their continuations have the same `isSome` at every
pair of successful values, then the two binds have the same `isSome`. -/
private theorem isSome_bind_eq_of_isSome_eq {α β : Type _}
    {first second : Option α} {firstNext secondNext : α → Option β}
    (shape : first.isSome = second.isSome)
    (heads : ∀ left right, first = some left → second = some right →
      (firstNext left).isSome = (secondNext right).isSome) :
    (Bind.bind first firstNext).isSome = (Bind.bind second secondNext).isSome := by
  cases first with
  | none =>
      have secondNone : second = none := by
        have falseShape : second.isSome = false := by rw [← shape]; rfl
        cases second with
        | none => rfl
        | some _ => simp at falseShape
      rw [secondNone]
      rfl
  | some left =>
      have trueShape : second.isSome = true := by rw [← shape]; rfl
      obtain ⟨right, secondEq⟩ := Option.isSome_iff_exists.mp trueShape
      rw [secondEq]
      exact heads left right rfl secondEq

/-- Pointwise `isSome` agreement lifts through `List.mapM`. -/
private theorem list_mapM_isSome_eq {α β : Type _}
    (first second : α → Option β)
    (agrees : ∀ value, (first value).isSome = (second value).isSome) :
    ∀ values : List α,
      (values.mapM first).isSome = (values.mapM second).isSome
  | [] => rfl
  | value :: values => by
      rw [List.mapM_cons, List.mapM_cons]
      refine isSome_bind_eq_of_isSome_eq (agrees value) ?_
      intro left right _ _
      have recursive := list_mapM_isSome_eq first second agrees values
      cases firstTail : values.mapM first with
      | none =>
          have secondTail : values.mapM second = none := by
            have falseShape : (values.mapM second).isSome = false := by
              rw [← recursive, firstTail]
              rfl
            rw [Option.isSome_eq_false_iff] at falseShape
            have isNoneValue : (values.mapM second).isNone := by simpa using falseShape
            exact Option.isNone_iff_eq_none.mp isNoneValue
          simp [firstTail, secondTail, bind_none_option_compound,
            bind_some_option_compound]
      | some tailFirst =>
          have trueShape : (values.mapM second).isSome = true := by
            rw [← recursive, firstTail]
            rfl
          obtain ⟨tailSecond, secondTail⟩ := Option.isSome_iff_exists.mp trueShape
          simp [firstTail, secondTail, bind_none_option_compound,
            bind_some_option_compound]

/-- If two options have the same `isSome` and every pair of successful values projects equally,
then the projected options are equal.  This is the fail-closed lift used for every full `Option`
projection theorem below. -/
private theorem option_map_eq_of_isSome_eq {α β : Type _}
    {first second : Option α} {project : α → β}
    (shape : first.isSome = second.isSome)
    (agree : ∀ left right, first = some left → second = some right →
      project left = project right) :
    first.map project = second.map project := by
  cases first with
  | none =>
      have secondNone : second = none := by
        have falseShape : second.isSome = false := by rw [← shape]; rfl
        cases second with
        | none => rfl
        | some _ => simp at falseShape
      rw [secondNone]
  | some left =>
      have trueShape : second.isSome = true := by rw [← shape]; rfl
      obtain ⟨right, secondEq⟩ := Option.isSome_iff_exists.mp trueShape
      rw [secondEq]
      show some (project left) = some (project right)
      rw [agree left right rfl secondEq]

/-! ## Stage-general observable independence of the cumulative builder -/

/-- **Observable independence from reader *and* stage.**  Two actual public cumulative
Rules-4a--5 builds at the same fuel and cursor, driven by arbitrary label readers and compiled at
arbitrary cumulative stages, have the same exact constitutional observable.  Sibling order may
differ between the builds because both the stage and the reader enter the later-rule descriptor
tie-break; the proof passes through sorted permutation uniqueness of observables and the
addressed-merge factorization, and never assumes that the sorted orders agree.  The statement is a
full `Option` equality, so it covers the fail-closed `none` outcome. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutionalObservable_eq_of_stages
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (firstStage secondStage : LocalizedCumulativeRule45Stage)
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        firstStage first fuel cursor).map
          (cumulativeRule45ConstitutionalObservable source) =
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          secondStage second fuel cursor).map
          (cumulativeRule45ConstitutionalObservable source)
  | 0, cursor => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead?
      simp only [aromaticCanonicalRerootChildren?]
      let children := source.aromaticCanonicalRerootChildren cursor
      by_cases terminal : children = []
      · simp [children, terminal, cumulativeRule45ConstitutionalObservable]
      · simp [children, terminal]
  | fuel + 1, cursor => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead?
      simp only [aromaticCanonicalRerootChildren?]
      by_cases terminal : source.aromaticCanonicalRerootChildren cursor = []
      · simp only [bind_some_option_compound, if_pos terminal, Option.map_some,
          cumulativeRule45ConstitutionalObservable]
      · simp only [bind_some_option_compound, if_neg terminal]
        have mapProjectionEq :
            ((source.aromaticCanonicalRerootChildren cursor).mapM
                (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                  firstStage first fuel)).map
                (List.map (cumulativeRule45ConstitutionalObservable source)) =
              ((source.aromaticCanonicalRerootChildren cursor).mapM
                (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                  secondStage second fuel)).map
                (List.map (cumulativeRule45ConstitutionalObservable source)) :=
          list_mapM_map_projection_compound
            (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              firstStage first fuel)
            (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              secondStage second fuel)
            (cumulativeRule45ConstitutionalObservable source)
            (fun child =>
              buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutionalObservable_eq_of_stages
                source firstStage secondStage first second fuel child)
            (source.aromaticCanonicalRerootChildren cursor)
        cases firstComputed : (source.aromaticCanonicalRerootChildren cursor).mapM
            (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              firstStage first fuel) with
        | none =>
            have secondComputed : (source.aromaticCanonicalRerootChildren cursor).mapM
                (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                  secondStage second fuel) = none := by
              cases secondValue : (source.aromaticCanonicalRerootChildren cursor).mapM
                  (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                    secondStage second fuel) with
              | none => rfl
              | some _ => simp [firstComputed, secondValue] at mapProjectionEq
            simp only [secondComputed, bind_none_option_compound]
        | some firstKeys =>
            cases secondComputed : (source.aromaticCanonicalRerootChildren cursor).mapM
                (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                  secondStage second fuel) with
            | none => simp [firstComputed, secondComputed] at mapProjectionEq
            | some secondKeys =>
                have observablesEq :
                    firstKeys.map (cumulativeRule45ConstitutionalObservable source) =
                      secondKeys.map (cumulativeRule45ConstitutionalObservable source) := by
                  simp [firstComputed, secondComputed] at mapProjectionEq
                  exact mapProjectionEq
                have sortedMapEq :
                    (sortAromaticCanonicalCumulativeRule45Keys
                        source.compareAromaticCanonicalCumulativeRule45Keys firstKeys).map
                        (cumulativeRule45ConstitutionalObservable source) =
                      (sortAromaticCanonicalCumulativeRule45Keys
                        source.compareAromaticCanonicalCumulativeRule45Keys secondKeys).map
                        (cumulativeRule45ConstitutionalObservable source) := by
                  haveI : Std.TransCmp source.compareAromaticCanonicalCumulativeRule45Keys :=
                    source.compareAromaticCanonicalCumulativeRule45Keys_transCmp
                  have firstPerm :=
                    (sortAromaticCanonicalCumulativeRule45Keys_perm
                      source.compareAromaticCanonicalCumulativeRule45Keys firstKeys).map
                      (cumulativeRule45ConstitutionalObservable source)
                  have secondPerm :=
                    (sortAromaticCanonicalCumulativeRule45Keys_perm
                      source.compareAromaticCanonicalCumulativeRule45Keys secondKeys).map
                      (cumulativeRule45ConstitutionalObservable source)
                  refine exactConstitutionalObservable_eq_of_perm ?_ ?_ ?_
                  · exact (sortAromaticCanonicalCumulativeRule45Keys_descending
                        source.compareAromaticCanonicalCumulativeRule45Keys firstKeys).map
                      (cumulativeRule45ConstitutionalObservable source)
                      (fun left right notLt =>
                        cumulativeRule45ConstitutionalObservable_not_lt source notLt)
                  · exact (sortAromaticCanonicalCumulativeRule45Keys_descending
                        source.compareAromaticCanonicalCumulativeRule45Keys secondKeys).map
                      (cumulativeRule45ConstitutionalObservable source)
                      (fun left right notLt =>
                        cumulativeRule45ConstitutionalObservable_not_lt source notLt)
                  · refine firstPerm.trans ?_
                    rw [observablesEq]
                    exact secondPerm.symm
                simp only [bind_some_option_compound, Option.map_some, Option.some.injEq,
                  cumulativeRule45ConstitutionalObservable]
                rw [exactConstitutionalObservableObserved_assemble,
                  exactConstitutionalObservableObserved_assemble]
                have mapRewrite : ∀ (keys : List source.AromaticCanonicalCumulativeRule45Key),
                    (keys.map (fun child => child.constitutional)).map
                        (exactConstitutionalObservableObserved
                          source.molecule.toLocalizedMoleculeGraph
                          source.molecule.semanticExactOfficialRule1aObservation) =
                      keys.map (cumulativeRule45ConstitutionalObservable source) := by
                  intro keys
                  rw [List.map_map]
                  rfl
                rw [mapRewrite, mapRewrite, sortedMapEq]

/-- **Structural success is reader- and stage-independent.**  Two actual public cumulative
Rules-4a--5 builds at the same fuel and cursor succeed or fail together, whatever readers and
stages drive them.  The terminal test of the recursive builder is purely structural: neither the
label values nor the later-rule descriptor consulted for sibling sorting can change whether a
node has children. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (firstStage secondStage : LocalizedCumulativeRule45Stage)
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel) :
    ∀ (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel),
      (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        firstStage first fuel cursor).isSome =
      (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        secondStage second fuel cursor).isSome
  | 0, cursor => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead?
      simp only [aromaticCanonicalRerootChildren?]
      let children := source.aromaticCanonicalRerootChildren cursor
      by_cases terminal : children = []
      · simp [children, terminal]
      · simp [children, terminal]
  | fuel + 1, cursor => by
      unfold buildAromaticCanonicalCumulativeRule45KeyWithRead?
      simp only [aromaticCanonicalRerootChildren?]
      by_cases terminal : source.aromaticCanonicalRerootChildren cursor = []
      · simp only [bind_some_option_compound, if_pos terminal]
        simp
      · simp only [bind_some_option_compound, if_neg terminal]
        refine isSome_bind_eq_of_isSome_eq ?_ ?_
        · exact list_mapM_isSome_eq _ _
            (fun child =>
              buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
                source firstStage secondStage first second fuel child)
            (source.aromaticCanonicalRerootChildren cursor)
        · intro left right _ _
          simp

/-- Successful builds under arbitrary stages and readers have the same exact constitutional
observable.  This is the success form of the stage-general independence theorem. -/
theorem cumulativeRule45ConstitutionalObservable_eq_of_success
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {firstStage secondStage : LocalizedCumulativeRule45Stage}
    {first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {firstKey secondKey : source.AromaticCanonicalCumulativeRule45Key}
    (firstComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      firstStage first fuel cursor = some firstKey)
    (secondComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      secondStage second fuel cursor = some secondKey) :
    cumulativeRule45ConstitutionalObservable source firstKey =
      cumulativeRule45ConstitutionalObservable source secondKey := by
  have combined :=
    buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutionalObservable_eq_of_stages
      source firstStage secondStage first second fuel cursor
  rw [firstComputed, secondComputed] at combined
  simpa using combined

/-- Existential-stage form of `cumulativeRule45ConstitutionalObservable_eq_of_success`: it is
enough that both keys are produced by *some* stage of an actual cumulative build at the same fuel
and cursor, under arbitrary readers. -/
theorem cumulativeRule45ConstitutionalObservable_eq_of_exists_success
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    {firstRead secondRead : source.AromaticCanonicalRerootCursor carrierFuel →
      Option LocalizedAuxiliaryLabel}
    {fuel : Nat} {cursor : source.AromaticCanonicalRerootCursor carrierFuel}
    {firstKey secondKey : source.AromaticCanonicalCumulativeRule45Key}
    (firstComputed : ∃ stage : LocalizedCumulativeRule45Stage,
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage firstRead fuel cursor = some firstKey)
    (secondComputed : ∃ stage : LocalizedCumulativeRule45Stage,
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage secondRead fuel cursor = some secondKey) :
    cumulativeRule45ConstitutionalObservable source firstKey =
      cumulativeRule45ConstitutionalObservable source secondKey := by
  obtain ⟨firstStage, firstStageComputed⟩ := firstComputed
  obtain ⟨secondStage, secondStageComputed⟩ := secondComputed
  exact cumulativeRule45ConstitutionalObservable_eq_of_success
    source firstStageComputed secondStageComputed

/-! ## Rule-4b/4c reading layer -/

/-- The Rule-4b member of a successful actual Rule-4b/4c reading is exactly the cumulative build
at its reference-dependent Rule-4b stage. -/
theorem buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4bKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (reference : Option RS)
    (reading : source.AromaticCanonicalRerootRule4bcReading)
    (computed : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
      read fuel cursor reference = some reading) :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        (match reference with
          | none => .rule4a
          | some found => .rule4b found) read fuel cursor =
      some reading.rule4bKey := by
  cases reference with
  | none =>
      unfold buildAromaticCanonicalRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          simp [rule4bComputed] at computed
          cases rule4cComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              .rule4cNoReference read fuel cursor with
          | none => simp [rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4cComputed] at computed
              subst reading
              rfl
  | some reference =>
      unfold buildAromaticCanonicalRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (.rule4b reference) read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          simp [rule4bComputed] at computed
          cases rule4cComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              (.rule4c reference) read fuel cursor with
          | none => simp [rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4cComputed] at computed
              subst reading
              rfl

/-- The Rule-4c member of a successful actual Rule-4b/4c reading is exactly the cumulative build
at its reference-dependent Rule-4c stage. -/
theorem buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4cKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (reference : Option RS)
    (reading : source.AromaticCanonicalRerootRule4bcReading)
    (computed : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
      read fuel cursor reference = some reading) :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        (match reference with
          | none => .rule4cNoReference
          | some found => .rule4c found) read fuel cursor =
      some reading.rule4cKey := by
  cases reference with
  | none =>
      unfold buildAromaticCanonicalRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          simp [rule4bComputed] at computed
          cases rule4cComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              .rule4cNoReference read fuel cursor with
          | none => simp [rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4cComputed] at computed
              subst reading
              rfl
  | some reference =>
      unfold buildAromaticCanonicalRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (.rule4b reference) read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          simp [rule4bComputed] at computed
          cases rule4cComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              (.rule4c reference) read fuel cursor with
          | none => simp [rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4cComputed] at computed
              subst reading
              rfl

/-- A successful actual Rule-4b/4c reading has equal constitutional observables in its Rule-4b
and Rule-4c members: the reference selection changes the stage but never the constitutional
component. -/
theorem buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4b_rule4c_observable_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (reference : Option RS)
    (reading : source.AromaticCanonicalRerootRule4bcReading)
    (computed : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
      read fuel cursor reference = some reading) :
    cumulativeRule45ConstitutionalObservable source reading.rule4bKey =
      cumulativeRule45ConstitutionalObservable source reading.rule4cKey :=
  cumulativeRule45ConstitutionalObservable_eq_of_success
    source
    (buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4bKey
      source read fuel cursor reference reading computed)
    (buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4cKey
      source read fuel cursor reference reading computed)

/-- Structural success of one actual Rule-4b/4c reading is independent of the reader, the stage
and the reference alternative.  Every branch compiles the same two cumulative stages at the same
fuel and cursor, and cumulative success is stage- and reader-independent. -/
theorem buildAromaticCanonicalRerootRule4bcReadingWithRead?_isSome_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstReference secondReference : Option RS) :
    (source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
      first fuel cursor firstReference).isSome =
      (source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
        second fuel cursor secondReference).isSome := by
  cases firstReference with
  | none =>
      cases secondReference with
      | none =>
          unfold buildAromaticCanonicalRerootRule4bcReadingWithRead?
          refine isSome_bind_eq_of_isSome_eq
            (buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
              source .rule4a .rule4a first second fuel cursor) ?_
          intro left right _ _
          exact isSome_bind_eq_of_isSome_eq
            (buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
              source .rule4cNoReference .rule4cNoReference first second fuel cursor)
            (fun _ _ _ _ => by simp)
      | some secondFound =>
          unfold buildAromaticCanonicalRerootRule4bcReadingWithRead?
          refine isSome_bind_eq_of_isSome_eq
            (buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
              source .rule4a (.rule4b secondFound) first second fuel cursor) ?_
          intro left right _ _
          exact isSome_bind_eq_of_isSome_eq
            (buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
              source .rule4cNoReference (.rule4c secondFound) first second fuel cursor)
            (fun _ _ _ _ => by simp)
  | some firstFound =>
      cases secondReference with
      | none =>
          unfold buildAromaticCanonicalRerootRule4bcReadingWithRead?
          refine isSome_bind_eq_of_isSome_eq
            (buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
              source (.rule4b firstFound) .rule4a first second fuel cursor) ?_
          intro left right _ _
          exact isSome_bind_eq_of_isSome_eq
            (buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
              source (.rule4c firstFound) .rule4cNoReference first second fuel cursor)
            (fun _ _ _ _ => by simp)
      | some secondFound =>
          unfold buildAromaticCanonicalRerootRule4bcReadingWithRead?
          refine isSome_bind_eq_of_isSome_eq
            (buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
              source (.rule4b firstFound) (.rule4b secondFound) first second fuel cursor) ?_
          intro left right _ _
          exact isSome_bind_eq_of_isSome_eq
            (buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
              source (.rule4c firstFound) (.rule4c secondFound) first second fuel cursor)
            (fun _ _ _ _ => by simp)

/-- **Full `Option` projection of the actual Rule-4b/4c reading builder.**  At arbitrary fuel,
cursor and (possibly different) reference alternatives, two builds driven by arbitrary readers
project through the canonical exact constitutional observable to the same `Option` value,
including the fail-closed `none` outcome. -/
theorem buildAromaticCanonicalRerootRule4bcReadingWithRead?_constitutionalObservable_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstReference secondReference : Option RS) :
    (source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
        first fuel cursor firstReference).map
        (rule4bcReadingConstitutionalObservable source) =
      (source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
        second fuel cursor secondReference).map
        (rule4bcReadingConstitutionalObservable source) := by
  refine option_map_eq_of_isSome_eq
    (buildAromaticCanonicalRerootRule4bcReadingWithRead?_isSome_eq
      source first second fuel cursor firstReference secondReference) ?_
  intro left right leftComputed rightComputed
  exact cumulativeRule45ConstitutionalObservable_eq_of_success
    source
    (buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4bKey
      source first fuel cursor firstReference left leftComputed)
    (buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4bKey
      source second fuel cursor secondReference right rightComputed)

/-! ## Rule-4b/4c reading-list layer -/

/-- The normative Rule-4b/4c alternative list is never empty: no reference yields `[none]`, and
one or two references yield the `some`-images of the selected references. -/
theorem aromaticCanonicalRule4bcReferenceAlternatives_ne_nil (references : List RS) :
    aromaticCanonicalRule4bcReferenceAlternatives references ≠ [] := by
  cases references with
  | nil => simp [aromaticCanonicalRule4bcReferenceAlternatives]
  | cons reference references =>
      simp [aromaticCanonicalRule4bcReferenceAlternatives]

/-- Structural success of one actual reading is exactly the structural success of its Rule-4a
cumulative constituent, whichever reference alternative is selected. -/
private theorem buildAromaticCanonicalRerootRule4bcReadingWithRead?_isSome_eq_cumulative
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (reference : Option RS) :
    (source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
        read fuel cursor reference).isSome =
      (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        .rule4a read fuel cursor).isSome := by
  cases reference with
  | none =>
      unfold buildAromaticCanonicalRerootRule4bcReadingWithRead?
      have step := isSome_bind_eq_and
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor)
        (fun rule4bKey => Bind.bind
          (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
            .rule4cNoReference read fuel cursor)
          (fun rule4cKey => some
            ({ reference? := none
               rule4bKey := rule4bKey
               rule4cKey := rule4cKey } :
              source.AromaticCanonicalRerootRule4bcReading)))
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor).isSome
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          .rule4cNoReference read fuel cursor).isSome
        rfl
        (fun rule4bKey _ => by
          cases rule4cComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              .rule4cNoReference read fuel cursor with
          | none => simp [rule4cComputed]
          | some rule4cKey => simp [rule4cComputed])
      rw [step]
      rw [← buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
        source .rule4a .rule4cNoReference read read fuel cursor]
      simp
  | some reference =>
      unfold buildAromaticCanonicalRerootRule4bcReadingWithRead?
      have step := isSome_bind_eq_and
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (.rule4b reference) read fuel cursor)
        (fun rule4bKey => Bind.bind
          (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
            (.rule4c reference) read fuel cursor)
          (fun rule4cKey => some
            ({ reference? := some reference
               rule4bKey := rule4bKey
               rule4cKey := rule4cKey } :
              source.AromaticCanonicalRerootRule4bcReading)))
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (.rule4b reference) read fuel cursor).isSome
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (.rule4c reference) read fuel cursor).isSome
        rfl
        (fun rule4bKey _ => by
          cases rule4cComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
              (.rule4c reference) read fuel cursor with
          | none => simp [rule4cComputed]
          | some rule4cKey => simp [rule4cComputed])
      rw [step]
      rw [← buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
        source .rule4a (.rule4b reference) read read fuel cursor,
        ← buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
          source .rule4a (.rule4c reference) read read fuel cursor]
      simp

/-- Over a nonempty alternative list, the sequential reading-list compiler succeeds exactly when
its Rule-4a cumulative constituent succeeds, independently of the reader and of the list length. -/
private theorem buildAromaticCanonicalRerootRule4bcReadingsWithRead?_isSome_eq_scalar
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    ∀ (references : List (Option RS)), references ≠ [] →
      (source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        read fuel cursor references).isSome =
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor).isSome
  | [], empty => by exact absurd rfl empty
  | reference :: references, _ => by
      unfold buildAromaticCanonicalRerootRule4bcReadingsWithRead?
      have step := isSome_bind_eq_and
        (source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
          read fuel cursor reference)
        (fun reading => Bind.bind
          (source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
            read fuel cursor references)
          (fun readings => some (reading :: readings)))
        (source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
          read fuel cursor reference).isSome
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor).isSome
        rfl
        (fun reading headSome => by
          cases tailComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
              read fuel cursor references with
          | none =>
              have tailNe : references ≠ [] := by
                intro tailEmpty
                rw [tailEmpty] at tailComputed
                unfold buildAromaticCanonicalRerootRule4bcReadingsWithRead? at tailComputed
                simp at tailComputed
              have commonFalse : (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                  .rule4a read fuel cursor).isSome = false := by
                rw [← buildAromaticCanonicalRerootRule4bcReadingsWithRead?_isSome_eq_scalar
                  source read fuel cursor references tailNe]
                simp [tailComputed]
              simp [tailComputed, commonFalse]
          | some tail =>
              have commonTrue : (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                  .rule4a read fuel cursor).isSome = true := by
                rw [← buildAromaticCanonicalRerootRule4bcReadingWithRead?_isSome_eq_cumulative
                  source read fuel cursor reference]
                simp [headSome]
              simp [tailComputed, commonTrue])
      rw [step]
      rw [← buildAromaticCanonicalRerootRule4bcReadingWithRead?_isSome_eq_cumulative
        source read fuel cursor reference]
      simp

/-- **Structural success of the actual Rule-4b/4c reading list.**  At arbitrary readers and
nonempty alternative lists, the two list builds have the same `isSome`, i.e. the same fail-closed
success outcome, including the `none` case. -/
theorem buildAromaticCanonicalRerootRule4bcReadingsWithRead?_isSome_eq_of_ne_nil
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstReferences secondReferences : List (Option RS))
    (firstNe : firstReferences ≠ []) (secondNe : secondReferences ≠ []) :
    (source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        first fuel cursor firstReferences).isSome =
      (source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        second fuel cursor secondReferences).isSome := by
  rw [buildAromaticCanonicalRerootRule4bcReadingsWithRead?_isSome_eq_scalar
      source first fuel cursor firstReferences firstNe,
    buildAromaticCanonicalRerootRule4bcReadingsWithRead?_isSome_eq_scalar
      source second fuel cursor secondReferences secondNe,
    buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
      source .rule4a .rule4a first second fuel cursor]

/-- A successful reading list over a nonempty alternative list is nonempty. -/
theorem buildAromaticCanonicalRerootRule4bcReadingsWithRead?_ne_nil_of_success
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (references : List (Option RS))
    (readings : List source.AromaticCanonicalRerootRule4bcReading)
    (nonempty : references ≠ [])
    (computed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
      read fuel cursor references = some readings) :
    readings ≠ [] := by
  intro empty
  subst readings
  cases references with
  | nil => exact nonempty rfl
  | cons reference references =>
      unfold buildAromaticCanonicalRerootRule4bcReadingsWithRead? at computed
      cases headComputed : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
          read fuel cursor reference with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
              read fuel cursor references with
          | none => simp [headComputed, tailComputed] at computed
          | some tail => simp [headComputed, tailComputed] at computed

/-- Every member of a successful actual Rule-4b/4c reading list is compiled by the cumulative
builder at its reference-selected Rule-4b stage, at the same fuel and cursor. -/
theorem buildAromaticCanonicalRerootRule4bcReadingsWithRead?_mem_rule4bKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    ∀ (references : List (Option RS))
      (readings : List source.AromaticCanonicalRerootRule4bcReading),
      source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        read fuel cursor references = some readings →
      ∀ (reading : source.AromaticCanonicalRerootRule4bcReading),
        reading ∈ readings →
        ∃ stage : LocalizedCumulativeRule45Stage,
          source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
            stage read fuel cursor = some reading.rule4bKey
  | [], readings, computed, reading, present => by
      unfold buildAromaticCanonicalRerootRule4bcReadingsWithRead? at computed
      injection computed with reverseEq
      have readingsEq : readings = [] := reverseEq.symm
      subst readings
      simp at present
  | reference :: references, readings, computed, reading, present => by
      unfold buildAromaticCanonicalRerootRule4bcReadingsWithRead? at computed
      cases headComputed : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
          read fuel cursor reference with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
              read fuel cursor references with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst readings
              rcases List.mem_cons.mp present with same | later
              · rw [same]
                exact ⟨_,
                  buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4bKey
                    source read fuel cursor reference head headComputed⟩
              · exact buildAromaticCanonicalRerootRule4bcReadingsWithRead?_mem_rule4bKey
                  source read fuel cursor references tail tailComputed reading later

/-- Every member of a successful actual Rule-4b/4c reading list is compiled by the cumulative
builder at its reference-selected Rule-4c stage, at the same fuel and cursor. -/
theorem buildAromaticCanonicalRerootRule4bcReadingsWithRead?_mem_rule4cKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    ∀ (references : List (Option RS))
      (readings : List source.AromaticCanonicalRerootRule4bcReading),
      source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        read fuel cursor references = some readings →
      ∀ (reading : source.AromaticCanonicalRerootRule4bcReading),
        reading ∈ readings →
        ∃ stage : LocalizedCumulativeRule45Stage,
          source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
            stage read fuel cursor = some reading.rule4cKey
  | [], readings, computed, reading, present => by
      unfold buildAromaticCanonicalRerootRule4bcReadingsWithRead? at computed
      injection computed with reverseEq
      have readingsEq : readings = [] := reverseEq.symm
      subst readings
      simp at present
  | reference :: references, readings, computed, reading, present => by
      unfold buildAromaticCanonicalRerootRule4bcReadingsWithRead? at computed
      cases headComputed : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
          read fuel cursor reference with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
              read fuel cursor references with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst readings
              rcases List.mem_cons.mp present with same | later
              · rw [same]
                exact ⟨_,
                  buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4cKey
                    source read fuel cursor reference head headComputed⟩
              · exact buildAromaticCanonicalRerootRule4bcReadingsWithRead?_mem_rule4cKey
                  source read fuel cursor references tail tailComputed reading later

/-- Readings drawn from two successful actual reading lists have the same exact constitutional
observable, whatever the readers, alternatives, list positions and Rule-4b/4c stages. -/
theorem buildAromaticCanonicalRerootRule4bcReadingsWithRead?_observable_eq_of_mem
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstReferences secondReferences : List (Option RS))
    (firstReadings secondReadings : List source.AromaticCanonicalRerootRule4bcReading)
    (firstComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
      first fuel cursor firstReferences = some firstReadings)
    (secondComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
      second fuel cursor secondReferences = some secondReadings)
    (firstReading secondReading : source.AromaticCanonicalRerootRule4bcReading)
    (firstPresent : firstReading ∈ firstReadings)
    (secondPresent : secondReading ∈ secondReadings) :
    rule4bcReadingConstitutionalObservable source firstReading =
      rule4bcReadingConstitutionalObservable source secondReading :=
  cumulativeRule45ConstitutionalObservable_eq_of_exists_success source
    (buildAromaticCanonicalRerootRule4bcReadingsWithRead?_mem_rule4bKey
      source first fuel cursor firstReferences firstReadings firstComputed
      firstReading firstPresent)
    (buildAromaticCanonicalRerootRule4bcReadingsWithRead?_mem_rule4bKey
      source second fuel cursor secondReferences secondReadings secondComputed
      secondReading secondPresent)

/-- **Full `Option` projection of the head of an actual Rule-4b/4c reading list.**  Over
nonempty alternative lists, arbitrary readers produce lists whose first reading has the same
exact constitutional observable; failure of either list is retained as `none`. -/
theorem buildAromaticCanonicalRerootRule4bcReadingsWithRead?_constitutionalObservable_eq_of_ne_nil
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstReferences secondReferences : List (Option RS))
    (firstNe : firstReferences ≠ []) (secondNe : secondReferences ≠ []) :
    (source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        first fuel cursor firstReferences).map
        (fun readings => readings.head?.map
          (rule4bcReadingConstitutionalObservable source)) =
      (source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
        second fuel cursor secondReferences).map
        (fun readings => readings.head?.map
          (rule4bcReadingConstitutionalObservable source)) := by
  refine option_map_eq_of_isSome_eq
    (buildAromaticCanonicalRerootRule4bcReadingsWithRead?_isSome_eq_of_ne_nil
      source first second fuel cursor firstReferences secondReferences firstNe secondNe) ?_
  intro left right leftComputed rightComputed
  have leftNe := buildAromaticCanonicalRerootRule4bcReadingsWithRead?_ne_nil_of_success
    source first fuel cursor firstReferences left firstNe leftComputed
  have rightNe := buildAromaticCanonicalRerootRule4bcReadingsWithRead?_ne_nil_of_success
    source second fuel cursor secondReferences right secondNe rightComputed
  cases left with
  | nil => exact absurd rfl leftNe
  | cons leftHead leftTail =>
      cases right with
      | nil => exact absurd rfl rightNe
      | cons rightHead rightTail =>
          show some (rule4bcReadingConstitutionalObservable source leftHead) =
            some (rule4bcReadingConstitutionalObservable source rightHead)
          rw [buildAromaticCanonicalRerootRule4bcReadingsWithRead?_observable_eq_of_mem
            source first second fuel cursor firstReferences secondReferences
            (leftHead :: leftTail) (rightHead :: rightTail)
            leftComputed rightComputed leftHead rightHead (by simp) (by simp)]

/-! ## Compound Rules-4b/4c key -/

/-- **Structural success of the actual compound Rules-4b/4c builder.**  The fail-closed `none`
outcome is independent of the reader: the Rule-4a constituent and the alternative-selected
reading list succeed or fail together. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_isSome_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    (source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
        first fuel cursor).isSome =
      (source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
        second fuel cursor).isSome := by
  unfold buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
  refine isSome_bind_eq_of_isSome_eq
    (buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
      source .rule4a .rule4a first second fuel cursor) ?_
  intro leftKey rightKey _ _
  exact isSome_bind_eq_of_isSome_eq
    (buildAromaticCanonicalRerootRule4bcReadingsWithRead?_isSome_eq_of_ne_nil
      source first second fuel cursor
      (aromaticCanonicalRule4bcReferenceAlternatives
        (localizedRule4bReferencesFromRankedLabels leftKey.rankedLabels))
      (aromaticCanonicalRule4bcReferenceAlternatives
        (localizedRule4bReferencesFromRankedLabels rightKey.rankedLabels))
      (aromaticCanonicalRule4bcReferenceAlternatives_ne_nil _)
      (aromaticCanonicalRule4bcReferenceAlternatives_ne_nil _))
    (fun _ _ _ _ => by simp)

/-- The alternative-selected reading list of a successful actual compound Rules-4b/4c build is
nonempty. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_readings_ne_nil
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (computed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key) :
    key.readings ≠ [] := by
  unfold buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead? at computed
  cases rule4aComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a read fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      simp [rule4aComputed] at computed
      cases readingsComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
          read fuel cursor
          (aromaticCanonicalRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => simp [readingsComputed] at computed
      | some readings =>
          simp [readingsComputed] at computed
          subst key
          exact buildAromaticCanonicalRerootRule4bcReadingsWithRead?_ne_nil_of_success
            source read fuel cursor
            (aromaticCanonicalRule4bcReferenceAlternatives
              (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels))
            readings
            (aromaticCanonicalRule4bcReferenceAlternatives_ne_nil _)
            readingsComputed

/-- Every reading retained by a successful actual compound Rules-4b/4c build is compiled by the
cumulative builder at its reference-selected Rule-4b stage. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_mem_readings_rule4bKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (computed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key)
    (reading : source.AromaticCanonicalRerootRule4bcReading)
    (present : reading ∈ key.readings) :
    ∃ stage : LocalizedCumulativeRule45Stage,
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage read fuel cursor = some reading.rule4bKey := by
  unfold buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead? at computed
  cases rule4aComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a read fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      simp [rule4aComputed] at computed
      cases readingsComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
          read fuel cursor
          (aromaticCanonicalRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => simp [readingsComputed] at computed
      | some readings =>
          simp [readingsComputed] at computed
          subst key
          exact buildAromaticCanonicalRerootRule4bcReadingsWithRead?_mem_rule4bKey
            source read fuel cursor
            (aromaticCanonicalRule4bcReferenceAlternatives
              (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels))
            readings readingsComputed reading (by simpa using present)

/-- Every reading retained by a successful actual compound Rules-4b/4c build is compiled by the
cumulative builder at its reference-selected Rule-4c stage. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_mem_readings_rule4cKey
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (computed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key)
    (reading : source.AromaticCanonicalRerootRule4bcReading)
    (present : reading ∈ key.readings) :
    ∃ stage : LocalizedCumulativeRule45Stage,
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage read fuel cursor = some reading.rule4cKey := by
  unfold buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead? at computed
  cases rule4aComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a read fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      simp [rule4aComputed] at computed
      cases readingsComputed : source.buildAromaticCanonicalRerootRule4bcReadingsWithRead?
          read fuel cursor
          (aromaticCanonicalRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => simp [readingsComputed] at computed
      | some readings =>
          simp [readingsComputed] at computed
          subst key
          exact buildAromaticCanonicalRerootRule4bcReadingsWithRead?_mem_rule4cKey
            source read fuel cursor
            (aromaticCanonicalRule4bcReferenceAlternatives
              (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels))
            readings readingsComputed reading (by simpa using present)

/-- **Full `Option` projection of the actual compound Rules-4b/4c builder.**  At arbitrary fuel
and cursor, two builds driven by arbitrary readers project through the exact constitutional
observable to the same `Option` value, including the fail-closed `none` outcome.  The reference
selection, the no/one/two-reference alternatives and the entire reading list are retained. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_constitutionalObservable_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    (source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
        first fuel cursor).map (compoundRule4bcConstitutionalObservable source) =
      (source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
        second fuel cursor).map (compoundRule4bcConstitutionalObservable source) := by
  refine option_map_eq_of_isSome_eq
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_isSome_eq
      source first second fuel cursor) ?_
  intro left right leftComputed rightComputed
  exact cumulativeRule45ConstitutionalObservable_eq_of_success source
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source first fuel cursor left leftComputed)
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source second fuel cursor right rightComputed)

/-- A successful compound Rules-4b/4c key has the same exact constitutional observable as every
Rule-4b reading retained in its alternative-selected list.  This records that the alternatives and
the reference selection change stages only, never the constitutional projection. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_readings_observable_eq_of_mem
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (computed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key)
    (reading : source.AromaticCanonicalRerootRule4bcReading)
    (present : reading ∈ key.readings) :
    compoundRule4bcConstitutionalObservable source key =
      rule4bcReadingConstitutionalObservable source reading :=
  cumulativeRule45ConstitutionalObservable_eq_of_exists_success source
    ⟨.rule4a, buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source read fuel cursor key computed⟩
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_mem_readings_rule4bKey
      source read fuel cursor key computed reading present)

/-! ## Rule-5 reading layer -/

/-- The common-R member of a successful actual Rule-5 reading is exactly the cumulative build at
the reference-dependent common-R stage. -/
theorem buildAromaticCanonicalRerootRule5ReadingWithRead?_commonR
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading)
    (reading : source.AromaticCanonicalRerootRule5Reading)
    (computed : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
      read fuel cursor prior = some reading) :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        (aromaticCanonicalRule5StageFor prior.reference? .R) read fuel cursor =
      some reading.commonR := by
  unfold buildAromaticCanonicalRerootRule5ReadingWithRead? at computed
  cases commonRComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      (aromaticCanonicalRule5StageFor prior.reference? .R) read fuel cursor with
  | none => simp [commonRComputed] at computed
  | some commonR =>
      simp [commonRComputed] at computed
      cases commonSComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (aromaticCanonicalRule5StageFor prior.reference? .S) read fuel cursor with
      | none => simp [commonSComputed] at computed
      | some commonS =>
          simp [commonSComputed] at computed
          subst reading
          rfl

/-- The common-S member of a successful actual Rule-5 reading is exactly the cumulative build at
the reference-dependent common-S stage. -/
theorem buildAromaticCanonicalRerootRule5ReadingWithRead?_commonS
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading)
    (reading : source.AromaticCanonicalRerootRule5Reading)
    (computed : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
      read fuel cursor prior = some reading) :
    source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        (aromaticCanonicalRule5StageFor prior.reference? .S) read fuel cursor =
      some reading.commonS := by
  unfold buildAromaticCanonicalRerootRule5ReadingWithRead? at computed
  cases commonRComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      (aromaticCanonicalRule5StageFor prior.reference? .R) read fuel cursor with
  | none => simp [commonRComputed] at computed
  | some commonR =>
      simp [commonRComputed] at computed
      cases commonSComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (aromaticCanonicalRule5StageFor prior.reference? .S) read fuel cursor with
      | none => simp [commonSComputed] at computed
      | some commonS =>
          simp [commonSComputed] at computed
          subst reading
          rfl

/-- Both common-R and common-S members of a successful actual Rule-5 reading have the same exact
constitutional observable.  The reference-dependent stage and the R/S common reference change the
construction but never the constitutional projection. -/
theorem buildAromaticCanonicalRerootRule5ReadingWithRead?_commonR_commonS_observable_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading)
    (reading : source.AromaticCanonicalRerootRule5Reading)
    (computed : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
      read fuel cursor prior = some reading) :
    cumulativeRule45ConstitutionalObservable source reading.commonR =
      cumulativeRule45ConstitutionalObservable source reading.commonS :=
  cumulativeRule45ConstitutionalObservable_eq_of_success source
    (buildAromaticCanonicalRerootRule5ReadingWithRead?_commonR
      source read fuel cursor prior reading computed)
    (buildAromaticCanonicalRerootRule5ReadingWithRead?_commonS
      source read fuel cursor prior reading computed)

/-- Structural success of one actual Rule-5 reading is independent of the reader and of the prior
Rules-4b/4c reading: both common-reference cumulative builds succeed or fail together. -/
theorem buildAromaticCanonicalRerootRule5ReadingWithRead?_isSome_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstPrior secondPrior : source.AromaticCanonicalRerootRule4bcReading) :
    (source.buildAromaticCanonicalRerootRule5ReadingWithRead?
        first fuel cursor firstPrior).isSome =
      (source.buildAromaticCanonicalRerootRule5ReadingWithRead?
        second fuel cursor secondPrior).isSome := by
  unfold buildAromaticCanonicalRerootRule5ReadingWithRead?
  refine isSome_bind_eq_of_isSome_eq
    (buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq source
      (aromaticCanonicalRule5StageFor firstPrior.reference? .R)
      (aromaticCanonicalRule5StageFor secondPrior.reference? .R)
      first second fuel cursor) ?_
  intro left right _ _
  exact isSome_bind_eq_of_isSome_eq
    (buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq source
      (aromaticCanonicalRule5StageFor firstPrior.reference? .S)
      (aromaticCanonicalRule5StageFor secondPrior.reference? .S)
      first second fuel cursor)
    (fun _ _ _ _ => by simp)

/-- Structural success of one actual Rule-5 reading is exactly the structural success of any
cumulative stage at the same fuel and cursor. -/
private theorem buildAromaticCanonicalRerootRule5ReadingWithRead?_isSome_eq_cumulative
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading) :
    (source.buildAromaticCanonicalRerootRule5ReadingWithRead?
        read fuel cursor prior).isSome =
      (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        .rule4a read fuel cursor).isSome := by
  unfold buildAromaticCanonicalRerootRule5ReadingWithRead?
  have step := isSome_bind_eq_and
    (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      (aromaticCanonicalRule5StageFor prior.reference? .R) read fuel cursor)
    (fun commonR => Bind.bind
      (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        (aromaticCanonicalRule5StageFor prior.reference? .S) read fuel cursor)
      (fun commonS => some
        ({ prior := prior
           commonR := commonR
           commonS := commonS } :
          source.AromaticCanonicalRerootRule5Reading)))
    (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      (aromaticCanonicalRule5StageFor prior.reference? .R) read fuel cursor).isSome
    (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      (aromaticCanonicalRule5StageFor prior.reference? .S) read fuel cursor).isSome
    rfl
    (fun commonR _ => by
      cases commonSComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          (aromaticCanonicalRule5StageFor prior.reference? .S) read fuel cursor with
      | none => simp [commonSComputed]
      | some commonS => simp [commonSComputed])
  rw [step]
  rw [← buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
      source .rule4a (aromaticCanonicalRule5StageFor prior.reference? .R) read read fuel cursor,
    ← buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
      source .rule4a (aromaticCanonicalRule5StageFor prior.reference? .S) read read fuel cursor]
  simp

/-- **Full `Option` projection of the actual Rule-5 reading builder.**  Arbitrary readers and
prior readings project through the exact constitutional observable to the same `Option` value,
including the fail-closed `none` outcome. -/
theorem buildAromaticCanonicalRerootRule5ReadingWithRead?_constitutionalObservable_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstPrior secondPrior : source.AromaticCanonicalRerootRule4bcReading) :
    (source.buildAromaticCanonicalRerootRule5ReadingWithRead?
        first fuel cursor firstPrior).map
        (rule5ReadingConstitutionalObservable source) =
      (source.buildAromaticCanonicalRerootRule5ReadingWithRead?
        second fuel cursor secondPrior).map
        (rule5ReadingConstitutionalObservable source) := by
  refine option_map_eq_of_isSome_eq
    (buildAromaticCanonicalRerootRule5ReadingWithRead?_isSome_eq
      source first second fuel cursor firstPrior secondPrior) ?_
  intro left right leftComputed rightComputed
  exact cumulativeRule45ConstitutionalObservable_eq_of_success source
    (buildAromaticCanonicalRerootRule5ReadingWithRead?_commonR
      source first fuel cursor firstPrior left leftComputed)
    (buildAromaticCanonicalRerootRule5ReadingWithRead?_commonR
      source second fuel cursor secondPrior right rightComputed)

/-! ## Rule-5 reading-list layer -/

/-- Over a nonempty prior list, the sequential Rule-5 reading-list compiler succeeds exactly when
any cumulative stage succeeds, independently of the reader, the priors and the list length. -/
private theorem buildAromaticCanonicalRerootRule5ReadingsWithRead?_isSome_eq_scalar
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    ∀ (priors : List source.AromaticCanonicalRerootRule4bcReading), priors ≠ [] →
      (source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
        read fuel cursor priors).isSome =
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor).isSome
  | [], empty => by exact absurd rfl empty
  | prior :: priors, _ => by
      unfold buildAromaticCanonicalRerootRule5ReadingsWithRead?
      have step := isSome_bind_eq_and
        (source.buildAromaticCanonicalRerootRule5ReadingWithRead?
          read fuel cursor prior)
        (fun reading => Bind.bind
          (source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
            read fuel cursor priors)
          (fun readings => some (reading :: readings)))
        (source.buildAromaticCanonicalRerootRule5ReadingWithRead?
          read fuel cursor prior).isSome
        (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor).isSome
        rfl
        (fun reading headSome => by
          cases tailComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
              read fuel cursor priors with
          | none =>
              have tailNe : priors ≠ [] := by
                intro tailEmpty
                rw [tailEmpty] at tailComputed
                unfold buildAromaticCanonicalRerootRule5ReadingsWithRead? at tailComputed
                simp at tailComputed
              have commonFalse : (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                  .rule4a read fuel cursor).isSome = false := by
                rw [← buildAromaticCanonicalRerootRule5ReadingsWithRead?_isSome_eq_scalar
                  source read fuel cursor priors tailNe]
                simp [tailComputed]
              simp [tailComputed, commonFalse]
          | some tail =>
              have commonTrue : (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
                  .rule4a read fuel cursor).isSome = true := by
                rw [← buildAromaticCanonicalRerootRule5ReadingWithRead?_isSome_eq_cumulative
                  source read fuel cursor prior]
                simp [headSome]
              simp [tailComputed, commonTrue])
      rw [step]
      rw [← buildAromaticCanonicalRerootRule5ReadingWithRead?_isSome_eq_cumulative
        source read fuel cursor prior]
      simp

/-- **Structural success of the actual Rule-5 reading list.**  Over nonempty prior lists,
arbitrary readers have the same fail-closed success outcome. -/
theorem buildAromaticCanonicalRerootRule5ReadingsWithRead?_isSome_eq_of_ne_nil
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstPriors secondPriors : List source.AromaticCanonicalRerootRule4bcReading)
    (firstNe : firstPriors ≠ []) (secondNe : secondPriors ≠ []) :
    (source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
        first fuel cursor firstPriors).isSome =
      (source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
        second fuel cursor secondPriors).isSome := by
  rw [buildAromaticCanonicalRerootRule5ReadingsWithRead?_isSome_eq_scalar
      source first fuel cursor firstPriors firstNe,
    buildAromaticCanonicalRerootRule5ReadingsWithRead?_isSome_eq_scalar
      source second fuel cursor secondPriors secondNe,
    buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
      source .rule4a .rule4a first second fuel cursor]

/-- A successful Rule-5 reading list over a nonempty prior list is nonempty. -/
theorem buildAromaticCanonicalRerootRule5ReadingsWithRead?_ne_nil_of_success
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (priors : List source.AromaticCanonicalRerootRule4bcReading)
    (readings : List source.AromaticCanonicalRerootRule5Reading)
    (nonempty : priors ≠ [])
    (computed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
      read fuel cursor priors = some readings) :
    readings ≠ [] := by
  intro empty
  subst readings
  cases priors with
  | nil => exact nonempty rfl
  | cons prior priors =>
      unfold buildAromaticCanonicalRerootRule5ReadingsWithRead? at computed
      cases headComputed : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
          read fuel cursor prior with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
              read fuel cursor priors with
          | none => simp [headComputed, tailComputed] at computed
          | some tail => simp [headComputed, tailComputed] at computed

/-- Every member of a successful actual Rule-5 reading list is compiled by the cumulative builder
at its reference-dependent common-R stage. -/
theorem buildAromaticCanonicalRerootRule5ReadingsWithRead?_mem_commonR
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    ∀ (priors : List source.AromaticCanonicalRerootRule4bcReading)
      (readings : List source.AromaticCanonicalRerootRule5Reading),
      source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
        read fuel cursor priors = some readings →
      ∀ (reading : source.AromaticCanonicalRerootRule5Reading),
        reading ∈ readings →
        ∃ stage : LocalizedCumulativeRule45Stage,
          source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
            stage read fuel cursor = some reading.commonR
  | [], readings, computed, reading, present => by
      unfold buildAromaticCanonicalRerootRule5ReadingsWithRead? at computed
      simp at computed
      subst readings
      simp at present
  | prior :: priors, readings, computed, reading, present => by
      unfold buildAromaticCanonicalRerootRule5ReadingsWithRead? at computed
      cases headComputed : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
          read fuel cursor prior with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
              read fuel cursor priors with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst readings
              rcases List.mem_cons.mp present with same | later
              · rw [same]
                exact ⟨_,
                  buildAromaticCanonicalRerootRule5ReadingWithRead?_commonR
                    source read fuel cursor prior head headComputed⟩
              · exact buildAromaticCanonicalRerootRule5ReadingsWithRead?_mem_commonR
                  source read fuel cursor priors tail tailComputed reading later

/-- Every member of a successful actual Rule-5 reading list is compiled by the cumulative builder
at its reference-dependent common-S stage. -/
theorem buildAromaticCanonicalRerootRule5ReadingsWithRead?_mem_commonS
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    ∀ (priors : List source.AromaticCanonicalRerootRule4bcReading)
      (readings : List source.AromaticCanonicalRerootRule5Reading),
      source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
        read fuel cursor priors = some readings →
      ∀ (reading : source.AromaticCanonicalRerootRule5Reading),
        reading ∈ readings →
        ∃ stage : LocalizedCumulativeRule45Stage,
          source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
            stage read fuel cursor = some reading.commonS
  | [], readings, computed, reading, present => by
      unfold buildAromaticCanonicalRerootRule5ReadingsWithRead? at computed
      simp at computed
      subst readings
      simp at present
  | prior :: priors, readings, computed, reading, present => by
      unfold buildAromaticCanonicalRerootRule5ReadingsWithRead? at computed
      cases headComputed : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
          read fuel cursor prior with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
              read fuel cursor priors with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst readings
              rcases List.mem_cons.mp present with same | later
              · rw [same]
                exact ⟨_,
                  buildAromaticCanonicalRerootRule5ReadingWithRead?_commonS
                    source read fuel cursor prior head headComputed⟩
              · exact buildAromaticCanonicalRerootRule5ReadingsWithRead?_mem_commonS
                  source read fuel cursor priors tail tailComputed reading later

/-- Readings drawn from two successful actual Rule-5 reading lists have the same exact
constitutional observable, whatever the readers, priors and list positions. -/
theorem buildAromaticCanonicalRerootRule5ReadingsWithRead?_observable_eq_of_mem
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstPriors secondPriors : List source.AromaticCanonicalRerootRule4bcReading)
    (firstReadings secondReadings : List source.AromaticCanonicalRerootRule5Reading)
    (firstComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
      first fuel cursor firstPriors = some firstReadings)
    (secondComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
      second fuel cursor secondPriors = some secondReadings)
    (firstReading secondReading : source.AromaticCanonicalRerootRule5Reading)
    (firstPresent : firstReading ∈ firstReadings)
    (secondPresent : secondReading ∈ secondReadings) :
    rule5ReadingConstitutionalObservable source firstReading =
      rule5ReadingConstitutionalObservable source secondReading :=
  cumulativeRule45ConstitutionalObservable_eq_of_exists_success source
    (buildAromaticCanonicalRerootRule5ReadingsWithRead?_mem_commonR
      source first fuel cursor firstPriors firstReadings firstComputed
      firstReading firstPresent)
    (buildAromaticCanonicalRerootRule5ReadingsWithRead?_mem_commonR
      source second fuel cursor secondPriors secondReadings secondComputed
      secondReading secondPresent)

/-- **Full `Option` projection of the head of an actual Rule-5 reading list.**  Over nonempty
prior lists, arbitrary readers produce lists whose first reading has the same exact constitutional
observable; failure of either list is retained as `none`. -/
theorem buildAromaticCanonicalRerootRule5ReadingsWithRead?_constitutionalObservable_eq_of_ne_nil
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstPriors secondPriors : List source.AromaticCanonicalRerootRule4bcReading)
    (firstNe : firstPriors ≠ []) (secondNe : secondPriors ≠ []) :
    (source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
        first fuel cursor firstPriors).map
        (fun readings => readings.head?.map
          (rule5ReadingConstitutionalObservable source)) =
      (source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
        second fuel cursor secondPriors).map
        (fun readings => readings.head?.map
          (rule5ReadingConstitutionalObservable source)) := by
  refine option_map_eq_of_isSome_eq
    (buildAromaticCanonicalRerootRule5ReadingsWithRead?_isSome_eq_of_ne_nil
      source first second fuel cursor firstPriors secondPriors firstNe secondNe) ?_
  intro left right leftComputed rightComputed
  have leftNe := buildAromaticCanonicalRerootRule5ReadingsWithRead?_ne_nil_of_success
    source first fuel cursor firstPriors left firstNe leftComputed
  have rightNe := buildAromaticCanonicalRerootRule5ReadingsWithRead?_ne_nil_of_success
    source second fuel cursor secondPriors right secondNe rightComputed
  cases left with
  | nil => exact absurd rfl leftNe
  | cons leftHead leftTail =>
      cases right with
      | nil => exact absurd rfl rightNe
      | cons rightHead rightTail =>
          show some (rule5ReadingConstitutionalObservable source leftHead) =
            some (rule5ReadingConstitutionalObservable source rightHead)
          rw [buildAromaticCanonicalRerootRule5ReadingsWithRead?_observable_eq_of_mem
            source first second fuel cursor firstPriors secondPriors
            (leftHead :: leftTail) (rightHead :: rightTail)
            leftComputed rightComputed leftHead rightHead (by simp) (by simp)]

/-! ## Compound through-Rule-5 key -/

/-- A successful complete compound build carries the actual compound Rules-4b/4c key it compiled
as `key.prior`. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_computed
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key)
    (computed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key) :
    source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key.prior := by
  unfold buildAromaticCanonicalRerootCompoundRule45KeyWithRead? at computed
  cases priorComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel cursor with
  | none => simp [priorComputed] at computed
  | some prior =>
      simp [priorComputed] at computed
      cases readingsComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
          read fuel cursor prior.readings with
      | none => simp [readingsComputed] at computed
      | some readings =>
          simp [readingsComputed] at computed
          subst key
          rfl

/-- **Structural success of the actual complete through-Rule-5 compound builder.**  The
fail-closed `none` outcome is independent of the reader: the prior compound key and its retained
Rule-5 reading list succeed or fail together. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_isSome_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        first fuel cursor).isSome =
      (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        second fuel cursor).isSome := by
  unfold buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
  refine isSome_bind_eq_of_isSome_eq
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_isSome_eq
      source first second fuel cursor) ?_
  intro leftPrior rightPrior leftComputed rightComputed
  exact isSome_bind_eq_of_isSome_eq
    (buildAromaticCanonicalRerootRule5ReadingsWithRead?_isSome_eq_of_ne_nil
      source first second fuel cursor leftPrior.readings rightPrior.readings
      (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_readings_ne_nil
        source first fuel cursor leftPrior leftComputed)
      (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_readings_ne_nil
        source second fuel cursor rightPrior rightComputed))
    (fun _ _ _ _ => by simp)

/-- Every Rule-5 reading retained by a successful complete compound build is compiled by the
cumulative builder at its reference-dependent common-R stage. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_mem_rule5Readings_commonR
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key)
    (computed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key)
    (reading : source.AromaticCanonicalRerootRule5Reading)
    (present : reading ∈ key.rule5Readings) :
    ∃ stage : LocalizedCumulativeRule45Stage,
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage read fuel cursor = some reading.commonR := by
  unfold buildAromaticCanonicalRerootCompoundRule45KeyWithRead? at computed
  cases priorComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel cursor with
  | none => simp [priorComputed] at computed
  | some prior =>
      simp [priorComputed] at computed
      cases readingsComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
          read fuel cursor prior.readings with
      | none => simp [readingsComputed] at computed
      | some readings =>
          simp [readingsComputed] at computed
          subst key
          exact buildAromaticCanonicalRerootRule5ReadingsWithRead?_mem_commonR
            source read fuel cursor prior.readings readings readingsComputed
            reading (by simpa using present)

/-- Every Rule-5 reading retained by a successful complete compound build is compiled by the
cumulative builder at its reference-dependent common-S stage. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_mem_rule5Readings_commonS
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key)
    (computed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key)
    (reading : source.AromaticCanonicalRerootRule5Reading)
    (present : reading ∈ key.rule5Readings) :
    ∃ stage : LocalizedCumulativeRule45Stage,
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        stage read fuel cursor = some reading.commonS := by
  unfold buildAromaticCanonicalRerootCompoundRule45KeyWithRead? at computed
  cases priorComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel cursor with
  | none => simp [priorComputed] at computed
  | some prior =>
      simp [priorComputed] at computed
      cases readingsComputed : source.buildAromaticCanonicalRerootRule5ReadingsWithRead?
          read fuel cursor prior.readings with
      | none => simp [readingsComputed] at computed
      | some readings =>
          simp [readingsComputed] at computed
          subst key
          exact buildAromaticCanonicalRerootRule5ReadingsWithRead?_mem_commonS
            source read fuel cursor prior.readings readings readingsComputed
            reading (by simpa using present)

/-- **Full `Option` projection of the actual complete through-Rule-5 compound builder.**  At
arbitrary fuel and cursor, two builds driven by arbitrary readers project through the exact
constitutional observable to the same `Option` value, including the fail-closed `none` outcome.
The prior compound key, the full Rule-5 reading list and both common-R/common-S readings are
retained. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_constitutionalObservable_eq
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel) :
    (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        first fuel cursor).map (compoundRule45ConstitutionalObservable source) =
      (source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        second fuel cursor).map (compoundRule45ConstitutionalObservable source) := by
  refine option_map_eq_of_isSome_eq
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_isSome_eq
      source first second fuel cursor) ?_
  intro left right leftComputed rightComputed
  exact cumulativeRule45ConstitutionalObservable_eq_of_success source
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source first fuel cursor left leftComputed)
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source second fuel cursor right rightComputed)

/-- A successful complete compound key has the same exact constitutional observable as its prior
Rules-4b/4c key. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_observable_eq_prior
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key)
    (computed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key) :
    compoundRule45ConstitutionalObservable source key =
      compoundRule4bcConstitutionalObservable source key.prior :=
  cumulativeRule45ConstitutionalObservable_eq_of_success source
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source read fuel cursor key computed)
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source read fuel cursor key.prior
      (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_computed
        source read fuel cursor key computed))

/-- A successful complete compound key has the same exact constitutional observable as every
Rule-5 reading retained in its list. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_rule5Readings_observable_eq_of_mem
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key)
    (computed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key)
    (reading : source.AromaticCanonicalRerootRule5Reading)
    (present : reading ∈ key.rule5Readings) :
    compoundRule45ConstitutionalObservable source key =
      rule5ReadingConstitutionalObservable source reading :=
  cumulativeRule45ConstitutionalObservable_eq_of_exists_success source
    ⟨.rule4a, buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source read fuel cursor key computed⟩
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_mem_rule5Readings_commonR
      source read fuel cursor key computed reading present)

/-- The same retained Rule-5 reading also agrees with the complete compound observable through
its common-S member.  This records that both `commonR` and `commonS` are retained and
constitutionally aligned, not only the `commonR` projection used by the reading wrapper. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_rule5Readings_observable_eq_of_mem_commonS
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key)
    (computed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key)
    (reading : source.AromaticCanonicalRerootRule5Reading)
    (present : reading ∈ key.rule5Readings) :
    compoundRule45ConstitutionalObservable source key =
      cumulativeRule45ConstitutionalObservable source reading.commonS :=
  cumulativeRule45ConstitutionalObservable_eq_of_exists_success source
    ⟨.rule4a, buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source read fuel cursor key computed⟩
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_mem_rule5Readings_commonS
      source read fuel cursor key computed reading present)

/-! ## Adequate-fuel corollaries

The existing availability theorem of `PublicParametricRule45Availability` supplies success at the
structural bound `2 * (carrierFuel + 1)` for every path-valid cursor.  These corollaries combine
that theorem with the full `Option` projection theorems above; they introduce no solver. -/

/-- At the adequate fuel, two arbitrary readers of the actual compound Rules-4b/4c builder succeed
and their exact constitutional observables agree. -/
theorem exists_buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_observable_eq_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ firstKey secondKey,
      source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
        first (2 * (carrierFuel + 1)) cursor = some firstKey ∧
      source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
        second (2 * (carrierFuel + 1)) cursor = some secondKey ∧
      compoundRule4bcConstitutionalObservable source firstKey =
        compoundRule4bcConstitutionalObservable source secondKey := by
  obtain ⟨firstKey, firstComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_at_twice
      first cursor valid
  obtain ⟨secondKey, secondComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_at_twice
      second cursor valid
  refine ⟨firstKey, secondKey, firstComputed, secondComputed, ?_⟩
  have projected :=
    buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_constitutionalObservable_eq
      source first second (2 * (carrierFuel + 1)) cursor
  rw [firstComputed, secondComputed] at projected
  simpa using projected

/-- At the adequate fuel, two arbitrary readers of the actual complete compound builder succeed
and their exact constitutional observables agree. -/
theorem exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_observable_eq_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (first second : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (valid : source.AromaticCanonicalRerootCursorValid cursor) :
    ∃ firstKey secondKey,
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        first (2 * (carrierFuel + 1)) cursor = some firstKey ∧
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        second (2 * (carrierFuel + 1)) cursor = some secondKey ∧
      compoundRule45ConstitutionalObservable source firstKey =
        compoundRule45ConstitutionalObservable source secondKey := by
  obtain ⟨firstKey, firstComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_at_twice
      first cursor valid
  obtain ⟨secondKey, secondComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_at_twice
      second cursor valid
  refine ⟨firstKey, secondKey, firstComputed, secondComputed, ?_⟩
  have projected :=
    buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_constitutionalObservable_eq
      source first second (2 * (carrierFuel + 1)) cursor
  rw [firstComputed, secondComputed] at projected
  simpa using projected

end AuthoritativeChemicalInput

/-! ## Exact-domain Rule-1b root-distance insulation

This section lifts the existing generic first-Rule-1b-layer separation from the localised
natural-number keys to the exact public key `ExactOfficialRuleMajorKey`, whose Rule-1b column is
the addressed `OfficialCIPNode.rule1bRootDistance` observation.  It is the exact-domain
replacement for the localised-only parent insulation. -/

namespace ExactOfficialRuleMajorKey

/-- The Rule-1b projection of a provenance tree whose head is the singleton root node begins with
that node's original-root distance. -/
theorem rule1bLayers_head_of_sourceNodes_head
    {V : Type*} {sources : OfficialRuleMajorKey.AddressedSourceLayers V}
    {node : OfficialCIPNode V}
    (head : sources.head? = some [([], node)]) :
    (rule1bLayers sources).head? = some [([], node.rule1bRootDistance)] := by
  cases sources with
  | nil => simp at head
  | cons first rest =>
      simp at head
      subst first
      rfl

/-- Distinct original-root distances at the two source-tree heads make the addressed exact
constitutional comparison strict.  The comparison still tests the full Rule-1a projection first:
when Rule 1a is itself strict it decides the comparison outright, and when Rule 1a ties the first
Rule-1b entries decide. -/
theorem compareAddressedSourcesObserved_ne_eq_of_rule1b_head_distances
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    {left right : OfficialRuleMajorKey.AddressedSourceLayers V}
    {leftNode rightNode : OfficialCIPNode V}
    (leftHead : left.head? = some [([], leftNode)])
    (rightHead : right.head? = some [([], rightNode)])
    (different : leftNode.rule1bRootDistance ≠ rightNode.rule1bRootDistance) :
    compareAddressedSourcesObserved m observe left right ≠ Ordering.eq := by
  have leftLayer := rule1bLayers_head_of_sourceNodes_head leftHead
  have rightLayer := rule1bLayers_head_of_sourceNodes_head rightHead
  have rule1bDecisive :
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
        (rule1bLayers left) (rule1bLayers right) ≠ Ordering.eq :=
    OfficialRuleMajorKey.compareSparseLayers_compareRule1b_ne_eq_of_head_distances
      leftLayer rightLayer different
  by_cases rule1aEq :
      OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
        (observedRule1aLayers observe left) (observedRule1aLayers observe right) =
          Ordering.eq
  · unfold compareAddressedSourcesObserved
    rw [ConstitutionalLexAlgebra.compareLex_eq_second_of_first_eq
      (Ordering.byKey (observedRule1aLayers observe)
        (OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber))
      (compareLex
        (Ordering.byKey rule1bLayers
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
        (Ordering.byKey (rule2Layers m)
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)))
      left right (by simpa [Ordering.byKey] using rule1aEq)]
    exact ConstitutionalLexAlgebra.compareLex_ne_eq_of_left_ne_eq _ _ left right
      (by simpa [Ordering.byKey] using rule1bDecisive)
  · unfold compareAddressedSourcesObserved
    exact ConstitutionalLexAlgebra.compareLex_ne_eq_of_left_ne_eq _ _ left right
      (by simpa [Ordering.byKey] using rule1aEq)

/-- Once Rule 1a ties, the first Rule-1b entries decide the exact addressed comparison outright;
Rule 2 and the deeper provenance fields are not consulted. -/
theorem compareAddressedSourcesObserved_eq_rule1b_of_rule1a_eq_of_head_distances
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    {left right : OfficialRuleMajorKey.AddressedSourceLayers V}
    {leftNode rightNode : OfficialCIPNode V}
    (rule1aEq :
      OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
        (observedRule1aLayers observe left) (observedRule1aLayers observe right) =
          Ordering.eq)
    (leftHead : left.head? = some [([], leftNode)])
    (rightHead : right.head? = some [([], rightNode)])
    (different : leftNode.rule1bRootDistance ≠ rightNode.rule1bRootDistance) :
    compareAddressedSourcesObserved m observe left right =
      OfficialRuleMajorKey.compareRule1b
        leftNode.rule1bRootDistance rightNode.rule1bRootDistance := by
  have leftLayer := rule1bLayers_head_of_sourceNodes_head leftHead
  have rightLayer := rule1bLayers_head_of_sourceNodes_head rightHead
  have rule1bDecisive :
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b
        (rule1bLayers left) (rule1bLayers right) ≠ Ordering.eq :=
    OfficialRuleMajorKey.compareSparseLayers_compareRule1b_ne_eq_of_head_distances
      leftLayer rightLayer different
  unfold compareAddressedSourcesObserved
  rw [ConstitutionalLexAlgebra.compareLex_eq_second_of_first_eq
    (Ordering.byKey (observedRule1aLayers observe)
      (OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber))
    (compareLex
      (Ordering.byKey rule1bLayers
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
      (Ordering.byKey (rule2Layers m)
        (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat)))
    left right (by simpa [Ordering.byKey] using rule1aEq)]
  rw [ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq
    (Ordering.byKey rule1bLayers
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareRule1b))
    (Ordering.byKey (rule2Layers m)
      (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
    left right (by simpa [Ordering.byKey] using rule1bDecisive)]
  exact OfficialRuleMajorKey.compareSparseLayers_compareRule1b_eq_of_head_distances
    leftLayer rightLayer different

/-- Distinct original-root distances at the two key heads make the full observed exact
constitutional comparison strict, whatever Rule 1a and the deeper fields are. -/
theorem compareObserved_ne_eq_of_rule1b_head_distances
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    {left right : ExactOfficialRuleMajorKey V}
    {leftNode rightNode : OfficialCIPNode V}
    (leftHead : left.sourceNodes.head? = some [([], leftNode)])
    (rightHead : right.sourceNodes.head? = some [([], rightNode)])
    (different : leftNode.rule1bRootDistance ≠ rightNode.rule1bRootDistance) :
    compareObserved m observe left right ≠ Ordering.eq := by
  simpa [compareObserved, Ordering.byKey] using
    compareAddressedSourcesObserved_ne_eq_of_rule1b_head_distances
      m observe leftHead rightHead different

/-- Once Rule 1a ties, the first Rule-1b entries decide the full observed comparison outright. -/
theorem compareObserved_eq_rule1b_of_rule1a_eq_of_head_distances
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    {left right : ExactOfficialRuleMajorKey V}
    {leftNode rightNode : OfficialCIPNode V}
    (rule1aEq :
      OfficialRuleMajorKey.compareSparseLayers compareExactAtomicNumber
        (observedRule1aLayers observe left.sourceNodes)
        (observedRule1aLayers observe right.sourceNodes) = Ordering.eq)
    (leftHead : left.sourceNodes.head? = some [([], leftNode)])
    (rightHead : right.sourceNodes.head? = some [([], rightNode)])
    (different : leftNode.rule1bRootDistance ≠ rightNode.rule1bRootDistance) :
    compareObserved m observe left right =
      OfficialRuleMajorKey.compareRule1b
        leftNode.rule1bRootDistance rightNode.rule1bRootDistance := by
  simpa [compareObserved, Ordering.byKey] using
    compareAddressedSourcesObserved_eq_rule1b_of_rule1a_eq_of_head_distances
      m observe rule1aEq leftHead rightHead different

/-- The observed exact comparator depends on its operands only through their exact constitutional
observables.  This is the four-key transport used to compare reader variants. -/
theorem compareObserved_eq_of_observable_eq
    {V : Type*} [Fintype V] [DecidableEq V]
    (m : MoleculeGraph V)
    (observe : OfficialCIPNode V → DeclarativeCIP.ExactAtomicNumber)
    {firstLeft firstRight secondLeft secondRight : ExactOfficialRuleMajorKey V}
    (leftEq :
      exactConstitutionalObservableObserved m observe firstLeft =
        exactConstitutionalObservableObserved m observe secondLeft)
    (rightEq :
      exactConstitutionalObservableObserved m observe firstRight =
        exactConstitutionalObservableObserved m observe secondRight) :
    compareObserved m observe firstLeft firstRight =
      compareObserved m observe secondLeft secondRight := by
  rw [compareObserved_eq_compareExactConstitutionalObservable m observe firstLeft firstRight,
    compareObserved_eq_compareExactConstitutionalObservable m observe secondLeft secondRight,
    leftEq, rightEq]

end ExactOfficialRuleMajorKey

namespace AuthoritativeChemicalInput

open CertifiedLocalizedCIPInput

/-! ### Strict-prefix reduction and reader invariance of the shipped cumulative comparator

The shipped cumulative comparator `compareAromaticCanonicalCumulativeRule45Keys` is lexicographic:
its first component is the exact constitutional comparison and its second component is the
later-rule descriptor.  The theorems below expose its exact behaviour on a strict constitutional
prefix -- it returns the constitutional outcome unchanged -- and use that to transport comparisons
across readers at equal fuel and cursor.  They are conditional on that strictness.  On a
constitutional tie the descriptor is consulted, and no reader-invariance claim is made for that
case. -/

/-- The exact constitutional observable of a cumulative key is, by definition, the observed exact
constitutional observable of its `constitutional` field. -/
theorem cumulativeRule45ConstitutionalObservable_eq_observed
    (source : AuthoritativeChemicalInput)
    (key : source.AromaticCanonicalCumulativeRule45Key) :
    cumulativeRule45ConstitutionalObservable source key =
      exactConstitutionalObservableObserved
        source.molecule.toLocalizedMoleculeGraph
        source.molecule.semanticExactOfficialRule1aObservation key.constitutional :=
  rfl

/-- The exact constitutional comparison of two cumulative keys under the ambient semantic Rule-1a
observation.  This is the first component of the shipped cumulative comparator. -/
abbrev cumulativeConstitutionalComparison (source : AuthoritativeChemicalInput)
    (left right : source.AromaticCanonicalCumulativeRule45Key) : Ordering :=
  ExactOfficialRuleMajorKey.compareObserved
    source.molecule.toLocalizedMoleculeGraph
    source.molecule.semanticExactOfficialRule1aObservation
    left.constitutional right.constitutional

/-- **Strict-prefix reduction.**  When the exact constitutional comparison of two cumulative keys
is strict, the shipped cumulative comparator returns exactly that comparison; the later-rule
descriptor is not consulted.  On a constitutional tie the descriptor is consulted and this theorem
says nothing. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_eq_constitutional_of_ne
    (source : AuthoritativeChemicalInput)
    {left right : source.AromaticCanonicalCumulativeRule45Key}
    (decisive : source.cumulativeConstitutionalComparison left right ≠ Ordering.eq) :
    source.compareAromaticCanonicalCumulativeRule45Keys left right =
      source.cumulativeConstitutionalComparison left right := by
  unfold compareAromaticCanonicalCumulativeRule45Keys cumulativeConstitutionalComparison
  exact ConstitutionalLexAlgebra.compareLex_eq_left_of_left_ne_eq _ _ left right
    (by simpa [Ordering.byKey] using decisive)

/-- A strict exact constitutional comparison makes the shipped cumulative comparator non-tied. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_ne_eq_of_constitutional_ne
    (source : AuthoritativeChemicalInput)
    {left right : source.AromaticCanonicalCumulativeRule45Key}
    (decisive : source.cumulativeConstitutionalComparison left right ≠ Ordering.eq) :
    source.compareAromaticCanonicalCumulativeRule45Keys left right ≠ Ordering.eq := by
  rw [compareAromaticCanonicalCumulativeRule45Keys_eq_constitutional_of_ne source decisive]
  exact decisive

/-- **Reader invariance on a strict constitutional prefix.**  Two cumulative-key pairs whose exact
constitutional observables agree pointwise compare identically, provided the first pair's exact
constitutional comparison is strict.  The hypothesis is not removable: on a constitutional tie the
later-rule descriptor decides and can depend on the reader. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_congr_of_observable_eq
    (source : AuthoritativeChemicalInput)
    {firstLeft firstRight secondLeft secondRight :
      source.AromaticCanonicalCumulativeRule45Key}
    (leftEq :
      cumulativeRule45ConstitutionalObservable source firstLeft =
        cumulativeRule45ConstitutionalObservable source secondLeft)
    (rightEq :
      cumulativeRule45ConstitutionalObservable source firstRight =
        cumulativeRule45ConstitutionalObservable source secondRight)
    (decisive : source.cumulativeConstitutionalComparison firstLeft firstRight ≠
      Ordering.eq) :
    source.compareAromaticCanonicalCumulativeRule45Keys firstLeft firstRight =
      source.compareAromaticCanonicalCumulativeRule45Keys secondLeft secondRight := by
  have leftEqObserved :
      exactConstitutionalObservableObserved
        source.molecule.toLocalizedMoleculeGraph
        source.molecule.semanticExactOfficialRule1aObservation firstLeft.constitutional =
      exactConstitutionalObservableObserved
        source.molecule.toLocalizedMoleculeGraph
        source.molecule.semanticExactOfficialRule1aObservation secondLeft.constitutional := by
    simpa [cumulativeRule45ConstitutionalObservable] using leftEq
  have rightEqObserved :
      exactConstitutionalObservableObserved
        source.molecule.toLocalizedMoleculeGraph
        source.molecule.semanticExactOfficialRule1aObservation firstRight.constitutional =
      exactConstitutionalObservableObserved
        source.molecule.toLocalizedMoleculeGraph
        source.molecule.semanticExactOfficialRule1aObservation secondRight.constitutional := by
    simpa [cumulativeRule45ConstitutionalObservable] using rightEq
  have transport : source.cumulativeConstitutionalComparison firstLeft firstRight =
      source.cumulativeConstitutionalComparison secondLeft secondRight :=
    ExactOfficialRuleMajorKey.compareObserved_eq_of_observable_eq
      source.molecule.toLocalizedMoleculeGraph
      source.molecule.semanticExactOfficialRule1aObservation
      leftEqObserved rightEqObserved
  have secondDecisive : source.cumulativeConstitutionalComparison secondLeft secondRight ≠
      Ordering.eq := by
    intro same
    exact decisive (transport.trans same)
  rw [compareAromaticCanonicalCumulativeRule45Keys_eq_constitutional_of_ne source decisive,
    compareAromaticCanonicalCumulativeRule45Keys_eq_constitutional_of_ne source secondDecisive]
  exact transport

/-- A successful cumulative build begins its exact constitutional provenance with the singleton
cursor node. -/
theorem buildAromaticCanonicalCumulativeRule45KeyWithRead?_sourceNodes_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalCumulativeRule45Key)
    (computed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      stage read fuel cursor = some key) :
    key.constitutional.sourceNodes.head? = some [([], cursor.occurrence.1.node)] :=
  (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_successful_shape
    stage read fuel cursor key computed).1

/-- **Source-ordinal Rule-1b strictness.**  Two successful cumulative builds at cursor nodes with
different total original-root distances, whose Rule-1a projections tie, are compared by the shipped
cumulative comparator exactly by those two root distances.  The distances are the actual compiled
cursor nodes, i.e. the heads of the exact constitutional provenance lists. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_eq_rule1b_of_builds
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {firstKey secondKey : source.AromaticCanonicalCumulativeRule45Key}
    (firstComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a read fuel firstCursor = some firstKey)
    (secondComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a read fuel secondCursor = some secondKey)
    (rule1aEq :
      OfficialRuleMajorKey.compareSparseLayers
        ExactOfficialRuleMajorKey.compareExactAtomicNumber
        (ExactOfficialRuleMajorKey.observedRule1aLayers
          source.molecule.semanticExactOfficialRule1aObservation
          firstKey.constitutional.sourceNodes)
        (ExactOfficialRuleMajorKey.observedRule1aLayers
          source.molecule.semanticExactOfficialRule1aObservation
          secondKey.constitutional.sourceNodes) = Ordering.eq)
    (different :
      firstCursor.occurrence.1.node.rule1bRootDistance ≠
        secondCursor.occurrence.1.node.rule1bRootDistance) :
    source.compareAromaticCanonicalCumulativeRule45Keys firstKey secondKey =
      OfficialRuleMajorKey.compareRule1b
        firstCursor.occurrence.1.node.rule1bRootDistance
        secondCursor.occurrence.1.node.rule1bRootDistance := by
  have firstHead :=
    buildAromaticCanonicalCumulativeRule45KeyWithRead?_sourceNodes_head
      source .rule4a read fuel firstCursor firstKey firstComputed
  have secondHead :=
    buildAromaticCanonicalCumulativeRule45KeyWithRead?_sourceNodes_head
      source .rule4a read fuel secondCursor secondKey secondComputed
  have decisive :=
    ExactOfficialRuleMajorKey.compareObserved_ne_eq_of_rule1b_head_distances
      source.molecule.toLocalizedMoleculeGraph
      source.molecule.semanticExactOfficialRule1aObservation
      firstHead secondHead different
  rw [compareAromaticCanonicalCumulativeRule45Keys_eq_constitutional_of_ne source decisive]
  exact ExactOfficialRuleMajorKey.compareObserved_eq_rule1b_of_rule1a_eq_of_head_distances
    source.molecule.toLocalizedMoleculeGraph
    source.molecule.semanticExactOfficialRule1aObservation
    rule1aEq firstHead secondHead different

/-- Different total original-root distances at the compiled cursor nodes make the shipped
cumulative comparison of two successful cumulative builds non-tied. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_ne_eq_of_builds_of_rule1b_head_distances
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {firstKey secondKey : source.AromaticCanonicalCumulativeRule45Key}
    (firstComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a read fuel firstCursor = some firstKey)
    (secondComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a read fuel secondCursor = some secondKey)
    (different :
      firstCursor.occurrence.1.node.rule1bRootDistance ≠
        secondCursor.occurrence.1.node.rule1bRootDistance) :
    source.compareAromaticCanonicalCumulativeRule45Keys firstKey secondKey ≠ Ordering.eq := by
  have firstHead :=
    buildAromaticCanonicalCumulativeRule45KeyWithRead?_sourceNodes_head
      source .rule4a read fuel firstCursor firstKey firstComputed
  have secondHead :=
    buildAromaticCanonicalCumulativeRule45KeyWithRead?_sourceNodes_head
      source .rule4a read fuel secondCursor secondKey secondComputed
  exact compareAromaticCanonicalCumulativeRule45Keys_ne_eq_of_constitutional_ne source
    (ExactOfficialRuleMajorKey.compareObserved_ne_eq_of_rule1b_head_distances
      source.molecule.toLocalizedMoleculeGraph
      source.molecule.semanticExactOfficialRule1aObservation
      firstHead secondHead different)

/-- **Reader invariance of the cumulative comparator on actual cumulative builds.**  Two readers
are compared at the same fuel and at two cursors, each reader compiling one key at each cursor.
Whenever the first reader's exact constitutional comparison of the two cursors is strict, both
readers produce the same cumulative comparison.  All four builds are actual
`buildAromaticCanonicalCumulativeRule45KeyWithRead?` runs; no success premise is assumed beyond the
four explicitly supplied computed keys. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_congr_of_cumulative_builds
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (firstRead secondRead : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {firstKey secondKey thirdKey fourthKey : source.AromaticCanonicalCumulativeRule45Key}
    (firstComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a firstRead fuel firstCursor = some firstKey)
    (secondComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a secondRead fuel firstCursor = some secondKey)
    (thirdComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a firstRead fuel secondCursor = some thirdKey)
    (fourthComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a secondRead fuel secondCursor = some fourthKey)
    (decisive : source.cumulativeConstitutionalComparison firstKey thirdKey ≠ Ordering.eq) :
    source.compareAromaticCanonicalCumulativeRule45Keys firstKey thirdKey =
      source.compareAromaticCanonicalCumulativeRule45Keys secondKey fourthKey := by
  refine compareAromaticCanonicalCumulativeRule45Keys_congr_of_observable_eq source ?_ ?_ decisive
  · exact cumulativeRule45ConstitutionalObservable_eq_of_success source
      firstComputed secondComputed
  · exact cumulativeRule45ConstitutionalObservable_eq_of_success source
      thirdComputed fourthComputed

/-- **Reader invariance under source root-distance separation.**  If the two compared cursors are
at different total original-root distances, the two first Rule-1b entries of the exact
constitutional provenance differ, so the exact constitutional comparison is strict, the shipped
cumulative comparator is non-tied, and it returns the same outcome for every pair of readers. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_congr_of_builds_of_rule1b_head_distances
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (firstRead secondRead : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {firstKey secondKey thirdKey fourthKey : source.AromaticCanonicalCumulativeRule45Key}
    (firstComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a firstRead fuel firstCursor = some firstKey)
    (secondComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a secondRead fuel firstCursor = some secondKey)
    (thirdComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a firstRead fuel secondCursor = some thirdKey)
    (fourthComputed : source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
      .rule4a secondRead fuel secondCursor = some fourthKey)
    (different :
      firstCursor.occurrence.1.node.rule1bRootDistance ≠
        secondCursor.occurrence.1.node.rule1bRootDistance) :
    source.compareAromaticCanonicalCumulativeRule45Keys firstKey thirdKey =
      source.compareAromaticCanonicalCumulativeRule45Keys secondKey fourthKey := by
  refine compareAromaticCanonicalCumulativeRule45Keys_congr_of_cumulative_builds source
    firstRead secondRead fuel firstCursor secondCursor
    firstComputed secondComputed thirdComputed fourthComputed ?_
  have firstHead :=
    buildAromaticCanonicalCumulativeRule45KeyWithRead?_sourceNodes_head
      source .rule4a firstRead fuel firstCursor firstKey firstComputed
  have thirdHead :=
    buildAromaticCanonicalCumulativeRule45KeyWithRead?_sourceNodes_head
      source .rule4a firstRead fuel secondCursor thirdKey thirdComputed
  exact ExactOfficialRuleMajorKey.compareObserved_ne_eq_of_rule1b_head_distances
    source.molecule.toLocalizedMoleculeGraph
    source.molecule.semanticExactOfficialRule1aObservation
    firstHead thirdHead different

/-! ### Actual compound Rule-4b/4c/5 builders -/

/-- A successful actual Rule-4b/4c reading begins the Rule-4b key's exact constitutional provenance
with the singleton cursor node. -/
theorem buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4b_sourceNodes_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (reference : Option RS)
    (reading : source.AromaticCanonicalRerootRule4bcReading)
    (computed : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
      read fuel cursor reference = some reading) :
    reading.rule4bKey.constitutional.sourceNodes.head? =
      some [([], cursor.occurrence.1.node)] :=
  (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_successful_shape
    (match reference with
      | none => .rule4a
      | some found => .rule4b found) read fuel cursor reading.rule4bKey
    (buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4bKey
      source read fuel cursor reference reading computed)).1

/-- A successful actual Rule-4b/4c reading begins the Rule-4c key's exact constitutional provenance
with the same singleton cursor node. -/
theorem buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4c_sourceNodes_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (reference : Option RS)
    (reading : source.AromaticCanonicalRerootRule4bcReading)
    (computed : source.buildAromaticCanonicalRerootRule4bcReadingWithRead?
      read fuel cursor reference = some reading) :
    reading.rule4cKey.constitutional.sourceNodes.head? =
      some [([], cursor.occurrence.1.node)] :=
  (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_successful_shape
    (match reference with
      | none => .rule4cNoReference
      | some found => .rule4c found) read fuel cursor reading.rule4cKey
    (buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4cKey
      source read fuel cursor reference reading computed)).1

/-- A successful actual Rule-5 reading begins the common-R key's exact constitutional provenance
with the singleton cursor node. -/
theorem buildAromaticCanonicalRerootRule5ReadingWithRead?_commonR_sourceNodes_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading)
    (reading : source.AromaticCanonicalRerootRule5Reading)
    (computed : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
      read fuel cursor prior = some reading) :
    reading.commonR.constitutional.sourceNodes.head? =
      some [([], cursor.occurrence.1.node)] :=
  (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_successful_shape
    (aromaticCanonicalRule5StageFor prior.reference? .R) read fuel cursor reading.commonR
    (buildAromaticCanonicalRerootRule5ReadingWithRead?_commonR
      source read fuel cursor prior reading computed)).1

/-- A successful actual Rule-5 reading begins the common-S key's exact constitutional provenance
with the singleton cursor node. -/
theorem buildAromaticCanonicalRerootRule5ReadingWithRead?_commonS_sourceNodes_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (prior : source.AromaticCanonicalRerootRule4bcReading)
    (reading : source.AromaticCanonicalRerootRule5Reading)
    (computed : source.buildAromaticCanonicalRerootRule5ReadingWithRead?
      read fuel cursor prior = some reading) :
    reading.commonS.constitutional.sourceNodes.head? =
      some [([], cursor.occurrence.1.node)] :=
  (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_successful_shape
    (aromaticCanonicalRule5StageFor prior.reference? .S) read fuel cursor reading.commonS
    (buildAromaticCanonicalRerootRule5ReadingWithRead?_commonS
      source read fuel cursor prior reading computed)).1

/-- A successful actual compound Rules-4b/4c build begins the Rule-4a key's exact constitutional
provenance with the singleton cursor node. -/
theorem buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_rule4a_sourceNodes_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule4bcKey)
    (computed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key) :
    key.rule4aKey.constitutional.sourceNodes.head? =
      some [([], cursor.occurrence.1.node)] :=
  (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_successful_shape
    .rule4a read fuel cursor key.rule4aKey
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source read fuel cursor key computed)).1

/-- A successful actual compound through-Rule-5 build begins the prior Rule-4a key's exact
constitutional provenance with the singleton cursor node. -/
theorem buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_rule4a_sourceNodes_head
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat) (cursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (key : source.AromaticCanonicalRerootCompoundRule45Key)
    (computed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read fuel cursor = some key) :
    key.prior.rule4aKey.constitutional.sourceNodes.head? =
      some [([], cursor.occurrence.1.node)] :=
  (source.buildAromaticCanonicalCumulativeRule45KeyWithRead?_successful_shape
    .rule4a read fuel cursor key.prior.rule4aKey
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source read fuel cursor key computed)).1

/-- **Reader invariance for actual compound Rules-4b/4c keys.**  The shipped cumulative comparator
applied to the extracted Rule-4a keys of four actual compound builds is reader-invariant whenever
the first reader's exact constitutional comparison is strict.  The compound descriptor comparator
`compareAromaticCanonicalRerootCompoundRule4bcKeys` is not claimed reader-invariant. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound4bc_builds
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (firstRead secondRead : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {firstKey secondKey thirdKey fourthKey :
      source.AromaticCanonicalRerootCompoundRule4bcKey}
    (firstComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      firstRead fuel firstCursor = some firstKey)
    (secondComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      secondRead fuel firstCursor = some secondKey)
    (thirdComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      firstRead fuel secondCursor = some thirdKey)
    (fourthComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      secondRead fuel secondCursor = some fourthKey)
    (decisive : source.cumulativeConstitutionalComparison
      firstKey.rule4aKey thirdKey.rule4aKey ≠ Ordering.eq) :
    source.compareAromaticCanonicalCumulativeRule45Keys
        firstKey.rule4aKey thirdKey.rule4aKey =
      source.compareAromaticCanonicalCumulativeRule45Keys
        secondKey.rule4aKey fourthKey.rule4aKey :=
  compareAromaticCanonicalCumulativeRule45Keys_congr_of_cumulative_builds source
    firstRead secondRead fuel firstCursor secondCursor
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source firstRead fuel firstCursor firstKey firstComputed)
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source secondRead fuel firstCursor secondKey secondComputed)
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source firstRead fuel secondCursor thirdKey thirdComputed)
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source secondRead fuel secondCursor fourthKey fourthComputed)
    decisive

/-- **Reader invariance for actual compound through-Rule-5 keys.**  The shipped cumulative
comparator applied to the extracted prior Rule-4a keys of four actual compound builds is
reader-invariant whenever the first reader's exact constitutional comparison is strict.  The
compound descriptor comparison is not claimed reader-invariant. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound45_builds
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (firstRead secondRead : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {firstKey secondKey thirdKey fourthKey :
      source.AromaticCanonicalRerootCompoundRule45Key}
    (firstComputed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      firstRead fuel firstCursor = some firstKey)
    (secondComputed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      secondRead fuel firstCursor = some secondKey)
    (thirdComputed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      firstRead fuel secondCursor = some thirdKey)
    (fourthComputed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      secondRead fuel secondCursor = some fourthKey)
    (decisive : source.cumulativeConstitutionalComparison
      firstKey.prior.rule4aKey thirdKey.prior.rule4aKey ≠ Ordering.eq) :
    source.compareAromaticCanonicalCumulativeRule45Keys
        firstKey.prior.rule4aKey thirdKey.prior.rule4aKey =
      source.compareAromaticCanonicalCumulativeRule45Keys
        secondKey.prior.rule4aKey fourthKey.prior.rule4aKey :=
  compareAromaticCanonicalCumulativeRule45Keys_congr_of_cumulative_builds source
    firstRead secondRead fuel firstCursor secondCursor
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source firstRead fuel firstCursor firstKey firstComputed)
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source secondRead fuel firstCursor secondKey secondComputed)
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source firstRead fuel secondCursor thirdKey thirdComputed)
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source secondRead fuel secondCursor fourthKey fourthComputed)
    decisive

/-- **Root-distance strictness for actual compound Rules-4b/4c keys.**  Two actual compound builds
by the same reader at cursor nodes with different total original-root distances, whose Rule-1a
projections tie, are compared on their extracted Rule-4a keys exactly by the two root distances. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_eq_rule1b_of_compound4bc_builds
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {firstKey thirdKey : source.AromaticCanonicalRerootCompoundRule4bcKey}
    (firstComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel firstCursor = some firstKey)
    (thirdComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel secondCursor = some thirdKey)
    (rule1aEq :
      OfficialRuleMajorKey.compareSparseLayers
        ExactOfficialRuleMajorKey.compareExactAtomicNumber
        (ExactOfficialRuleMajorKey.observedRule1aLayers
          source.molecule.semanticExactOfficialRule1aObservation
          firstKey.rule4aKey.constitutional.sourceNodes)
        (ExactOfficialRuleMajorKey.observedRule1aLayers
          source.molecule.semanticExactOfficialRule1aObservation
          thirdKey.rule4aKey.constitutional.sourceNodes) = Ordering.eq)
    (different :
      firstCursor.occurrence.1.node.rule1bRootDistance ≠
        secondCursor.occurrence.1.node.rule1bRootDistance) :
    source.compareAromaticCanonicalCumulativeRule45Keys
        firstKey.rule4aKey thirdKey.rule4aKey =
      OfficialRuleMajorKey.compareRule1b
        firstCursor.occurrence.1.node.rule1bRootDistance
        secondCursor.occurrence.1.node.rule1bRootDistance :=
  compareAromaticCanonicalCumulativeRule45Keys_eq_rule1b_of_builds source
    read fuel firstCursor secondCursor
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source read fuel firstCursor firstKey firstComputed)
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source read fuel secondCursor thirdKey thirdComputed)
    rule1aEq different

/-- **Root-distance strictness for actual compound through-Rule-5 keys.**  Two actual compound
builds by the same reader at cursor nodes with different total original-root distances, whose
Rule-1a projections tie, are compared on their extracted prior Rule-4a keys exactly by the two root
distances. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_eq_rule1b_of_compound45_builds
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {firstKey thirdKey : source.AromaticCanonicalRerootCompoundRule45Key}
    (firstComputed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read fuel firstCursor = some firstKey)
    (thirdComputed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read fuel secondCursor = some thirdKey)
    (rule1aEq :
      OfficialRuleMajorKey.compareSparseLayers
        ExactOfficialRuleMajorKey.compareExactAtomicNumber
        (ExactOfficialRuleMajorKey.observedRule1aLayers
          source.molecule.semanticExactOfficialRule1aObservation
          firstKey.prior.rule4aKey.constitutional.sourceNodes)
        (ExactOfficialRuleMajorKey.observedRule1aLayers
          source.molecule.semanticExactOfficialRule1aObservation
          thirdKey.prior.rule4aKey.constitutional.sourceNodes) = Ordering.eq)
    (different :
      firstCursor.occurrence.1.node.rule1bRootDistance ≠
        secondCursor.occurrence.1.node.rule1bRootDistance) :
    source.compareAromaticCanonicalCumulativeRule45Keys
        firstKey.prior.rule4aKey thirdKey.prior.rule4aKey =
      OfficialRuleMajorKey.compareRule1b
        firstCursor.occurrence.1.node.rule1bRootDistance
        secondCursor.occurrence.1.node.rule1bRootDistance :=
  compareAromaticCanonicalCumulativeRule45Keys_eq_rule1b_of_builds source
    read fuel firstCursor secondCursor
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source read fuel firstCursor firstKey firstComputed)
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source read fuel secondCursor thirdKey thirdComputed)
    rule1aEq different

/-- Different total original-root distances at the compiled cursor nodes make the shipped
cumulative comparison of two actual compound Rules-4b/4c builds non-tied on their extracted
Rule-4a keys. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_ne_eq_of_compound4bc_builds_of_rule1b_head_distances
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {firstKey thirdKey : source.AromaticCanonicalRerootCompoundRule4bcKey}
    (firstComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel firstCursor = some firstKey)
    (thirdComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      read fuel secondCursor = some thirdKey)
    (different :
      firstCursor.occurrence.1.node.rule1bRootDistance ≠
        secondCursor.occurrence.1.node.rule1bRootDistance) :
    source.compareAromaticCanonicalCumulativeRule45Keys
      firstKey.rule4aKey thirdKey.rule4aKey ≠ Ordering.eq :=
  compareAromaticCanonicalCumulativeRule45Keys_ne_eq_of_builds_of_rule1b_head_distances source
    read fuel firstCursor secondCursor
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source read fuel firstCursor firstKey firstComputed)
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source read fuel secondCursor thirdKey thirdComputed)
    different

/-- Different total original-root distances at the compiled cursor nodes make the shipped
cumulative comparison of two actual compound through-Rule-5 builds non-tied on their extracted
prior Rule-4a keys. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_ne_eq_of_compound45_builds_of_rule1b_head_distances
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (read : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {firstKey thirdKey : source.AromaticCanonicalRerootCompoundRule45Key}
    (firstComputed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read fuel firstCursor = some firstKey)
    (thirdComputed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      read fuel secondCursor = some thirdKey)
    (different :
      firstCursor.occurrence.1.node.rule1bRootDistance ≠
        secondCursor.occurrence.1.node.rule1bRootDistance) :
    source.compareAromaticCanonicalCumulativeRule45Keys
      firstKey.prior.rule4aKey thirdKey.prior.rule4aKey ≠ Ordering.eq :=
  compareAromaticCanonicalCumulativeRule45Keys_ne_eq_of_builds_of_rule1b_head_distances source
    read fuel firstCursor secondCursor
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source read fuel firstCursor firstKey firstComputed)
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source read fuel secondCursor thirdKey thirdComputed)
    different

/-- **Root-distance reader invariance for actual compound Rules-4b/4c keys.**  Four actual compound
builds, two readers at two cursor nodes whose total original-root distances differ, compare
identically on their extracted Rule-4a keys through the shipped cumulative comparator. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound4bc_builds_of_rule1b_head_distances
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (firstRead secondRead : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {firstKey secondKey thirdKey fourthKey :
      source.AromaticCanonicalRerootCompoundRule4bcKey}
    (firstComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      firstRead fuel firstCursor = some firstKey)
    (secondComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      secondRead fuel firstCursor = some secondKey)
    (thirdComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      firstRead fuel secondCursor = some thirdKey)
    (fourthComputed : source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
      secondRead fuel secondCursor = some fourthKey)
    (different :
      firstCursor.occurrence.1.node.rule1bRootDistance ≠
        secondCursor.occurrence.1.node.rule1bRootDistance) :
    source.compareAromaticCanonicalCumulativeRule45Keys
        firstKey.rule4aKey thirdKey.rule4aKey =
      source.compareAromaticCanonicalCumulativeRule45Keys
        secondKey.rule4aKey fourthKey.rule4aKey :=
  compareAromaticCanonicalCumulativeRule45Keys_congr_of_builds_of_rule1b_head_distances source
    firstRead secondRead fuel firstCursor secondCursor
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source firstRead fuel firstCursor firstKey firstComputed)
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source secondRead fuel firstCursor secondKey secondComputed)
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source firstRead fuel secondCursor thirdKey thirdComputed)
    (buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_prior_rule4aKey
      source secondRead fuel secondCursor fourthKey fourthComputed)
    different

/-- **Root-distance reader invariance for actual compound through-Rule-5 keys.**  Four actual
compound builds, two readers at two cursor nodes whose total original-root distances differ,
compare identically on their extracted prior Rule-4a keys through the shipped cumulative
comparator. -/
theorem compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound45_builds_of_rule1b_head_distances
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (firstRead secondRead : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (fuel : Nat)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    {firstKey secondKey thirdKey fourthKey :
      source.AromaticCanonicalRerootCompoundRule45Key}
    (firstComputed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      firstRead fuel firstCursor = some firstKey)
    (secondComputed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      secondRead fuel firstCursor = some secondKey)
    (thirdComputed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      firstRead fuel secondCursor = some thirdKey)
    (fourthComputed : source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
      secondRead fuel secondCursor = some fourthKey)
    (different :
      firstCursor.occurrence.1.node.rule1bRootDistance ≠
        secondCursor.occurrence.1.node.rule1bRootDistance) :
    source.compareAromaticCanonicalCumulativeRule45Keys
        firstKey.prior.rule4aKey thirdKey.prior.rule4aKey =
      source.compareAromaticCanonicalCumulativeRule45Keys
        secondKey.prior.rule4aKey fourthKey.prior.rule4aKey :=
  compareAromaticCanonicalCumulativeRule45Keys_congr_of_builds_of_rule1b_head_distances source
    firstRead secondRead fuel firstCursor secondCursor
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source firstRead fuel firstCursor firstKey firstComputed)
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source secondRead fuel firstCursor secondKey secondComputed)
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source firstRead fuel secondCursor thirdKey thirdComputed)
    (buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_rule4aKey
      source secondRead fuel secondCursor fourthKey fourthComputed)
    different

/-! ### Adequate-fuel endpoints

At the structural bound `2 * (carrierFuel + 1)` every valid cursor is successfully compiled, so the
reader-invariance endpoints above need no success premise beyond path validity and no new solver.
The root-distance separation is the only comparison premise. -/

/-- At the adequate fuel, four actual cumulative Rule-4a builds by two readers at two valid
cursors with different total original-root distances all succeed, and the shipped cumulative
comparison of the two cursors agrees between the two readers. -/
theorem exists_compareAromaticCanonicalCumulativeRule45Keys_congr_of_builds_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (firstRead secondRead : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstValid : source.AromaticCanonicalRerootCursorValid firstCursor)
    (secondValid : source.AromaticCanonicalRerootCursorValid secondCursor)
    (different :
      firstCursor.occurrence.1.node.rule1bRootDistance ≠
        secondCursor.occurrence.1.node.rule1bRootDistance) :
    ∃ firstKey secondKey thirdKey fourthKey,
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        .rule4a firstRead (2 * (carrierFuel + 1)) firstCursor = some firstKey ∧
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        .rule4a secondRead (2 * (carrierFuel + 1)) firstCursor = some secondKey ∧
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        .rule4a firstRead (2 * (carrierFuel + 1)) secondCursor = some thirdKey ∧
      source.buildAromaticCanonicalCumulativeRule45KeyWithRead?
        .rule4a secondRead (2 * (carrierFuel + 1)) secondCursor = some fourthKey ∧
      source.compareAromaticCanonicalCumulativeRule45Keys firstKey thirdKey =
        source.compareAromaticCanonicalCumulativeRule45Keys secondKey fourthKey := by
  obtain ⟨firstKey, firstComputed⟩ :=
    source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
      .rule4a firstRead firstCursor firstValid
  obtain ⟨secondKey, secondComputed⟩ :=
    source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
      .rule4a secondRead firstCursor firstValid
  obtain ⟨thirdKey, thirdComputed⟩ :=
    source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
      .rule4a firstRead secondCursor secondValid
  obtain ⟨fourthKey, fourthComputed⟩ :=
    source.exists_buildAromaticCanonicalCumulativeRule45KeyWithRead?_at_twice
      .rule4a secondRead secondCursor secondValid
  exact ⟨firstKey, secondKey, thirdKey, fourthKey,
    firstComputed, secondComputed, thirdComputed, fourthComputed,
    compareAromaticCanonicalCumulativeRule45Keys_congr_of_builds_of_rule1b_head_distances
      source firstRead secondRead (2 * (carrierFuel + 1)) firstCursor secondCursor
      firstComputed secondComputed thirdComputed fourthComputed different⟩

/-- At the adequate fuel, four actual compound Rules-4b/4c builds by two readers at two valid
cursors with different total original-root distances all succeed, and the shipped cumulative
comparison of their extracted Rule-4a keys agrees between the two readers. -/
theorem exists_compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound4bc_builds_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (firstRead secondRead : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstValid : source.AromaticCanonicalRerootCursorValid firstCursor)
    (secondValid : source.AromaticCanonicalRerootCursorValid secondCursor)
    (different :
      firstCursor.occurrence.1.node.rule1bRootDistance ≠
        secondCursor.occurrence.1.node.rule1bRootDistance) :
    ∃ firstKey secondKey thirdKey fourthKey :
        source.AromaticCanonicalRerootCompoundRule4bcKey,
      source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
        firstRead (2 * (carrierFuel + 1)) firstCursor = some firstKey ∧
      source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
        secondRead (2 * (carrierFuel + 1)) firstCursor = some secondKey ∧
      source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
        firstRead (2 * (carrierFuel + 1)) secondCursor = some thirdKey ∧
      source.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?
        secondRead (2 * (carrierFuel + 1)) secondCursor = some fourthKey ∧
      source.compareAromaticCanonicalCumulativeRule45Keys
          firstKey.rule4aKey thirdKey.rule4aKey =
        source.compareAromaticCanonicalCumulativeRule45Keys
          secondKey.rule4aKey fourthKey.rule4aKey := by
  obtain ⟨firstKey, firstComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_at_twice
      firstRead firstCursor firstValid
  obtain ⟨secondKey, secondComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_at_twice
      secondRead firstCursor firstValid
  obtain ⟨thirdKey, thirdComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_at_twice
      firstRead secondCursor secondValid
  obtain ⟨fourthKey, fourthComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_at_twice
      secondRead secondCursor secondValid
  exact ⟨firstKey, secondKey, thirdKey, fourthKey,
    firstComputed, secondComputed, thirdComputed, fourthComputed,
    compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound4bc_builds_of_rule1b_head_distances
      source firstRead secondRead (2 * (carrierFuel + 1)) firstCursor secondCursor
      firstComputed secondComputed thirdComputed fourthComputed different⟩

/-- At the adequate fuel, four actual compound through-Rule-5 builds by two readers at two valid
cursors with different total original-root distances all succeed, and the shipped cumulative
comparison of their extracted prior Rule-4a keys agrees between the two readers. -/
theorem exists_compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound45_builds_at_twice
    (source : AuthoritativeChemicalInput) {carrierFuel : Nat}
    (firstRead secondRead : source.AromaticCanonicalRerootCursor carrierFuel →
      Option AromaticCanonicalAuxiliaryLabel)
    (firstCursor secondCursor : source.AromaticCanonicalRerootCursor carrierFuel)
    (firstValid : source.AromaticCanonicalRerootCursorValid firstCursor)
    (secondValid : source.AromaticCanonicalRerootCursorValid secondCursor)
    (different :
      firstCursor.occurrence.1.node.rule1bRootDistance ≠
        secondCursor.occurrence.1.node.rule1bRootDistance) :
    ∃ firstKey secondKey thirdKey fourthKey :
        source.AromaticCanonicalRerootCompoundRule45Key,
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        firstRead (2 * (carrierFuel + 1)) firstCursor = some firstKey ∧
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        secondRead (2 * (carrierFuel + 1)) firstCursor = some secondKey ∧
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        firstRead (2 * (carrierFuel + 1)) secondCursor = some thirdKey ∧
      source.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?
        secondRead (2 * (carrierFuel + 1)) secondCursor = some fourthKey ∧
      source.compareAromaticCanonicalCumulativeRule45Keys
          firstKey.prior.rule4aKey thirdKey.prior.rule4aKey =
        source.compareAromaticCanonicalCumulativeRule45Keys
          secondKey.prior.rule4aKey fourthKey.prior.rule4aKey := by
  obtain ⟨firstKey, firstComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_at_twice
      firstRead firstCursor firstValid
  obtain ⟨secondKey, secondComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_at_twice
      secondRead firstCursor firstValid
  obtain ⟨thirdKey, thirdComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_at_twice
      firstRead secondCursor secondValid
  obtain ⟨fourthKey, fourthComputed⟩ :=
    source.exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_at_twice
      secondRead secondCursor secondValid
  exact ⟨firstKey, secondKey, thirdKey, fourthKey,
    firstComputed, secondComputed, thirdComputed, fourthComputed,
    compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound45_builds_of_rule1b_head_distances
      source firstRead secondRead (2 * (carrierFuel + 1)) firstCursor secondCursor
      firstComputed secondComputed thirdComputed fourthComputed different⟩

end AuthoritativeChemicalInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.rule4bcReadingConstitutionalObservable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compoundRule4bcConstitutionalObservable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.rule5ReadingConstitutionalObservable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compoundRule45ConstitutionalObservable
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_constitutionalObservable_eq_of_stages
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_isSome_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.cumulativeRule45ConstitutionalObservable_eq_of_success
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.cumulativeRule45ConstitutionalObservable_eq_of_exists_success
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4bKey
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4cKey
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4b_rule4c_observable_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingWithRead?_isSome_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingWithRead?_constitutionalObservable_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.aromaticCanonicalRule4bcReferenceAlternatives_ne_nil
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_isSome_eq_of_ne_nil
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_ne_nil_of_success
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_mem_rule4bKey
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_mem_rule4cKey
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_observable_eq_of_mem
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingsWithRead?_constitutionalObservable_eq_of_ne_nil
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_isSome_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_readings_ne_nil
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_mem_readings_rule4bKey
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_mem_readings_rule4cKey
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_constitutionalObservable_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_readings_observable_eq_of_mem
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingWithRead?_commonR
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingWithRead?_commonS
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingWithRead?_commonR_commonS_observable_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingWithRead?_isSome_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingWithRead?_constitutionalObservable_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingsWithRead?_isSome_eq_of_ne_nil
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingsWithRead?_ne_nil_of_success
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingsWithRead?_mem_commonR
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingsWithRead?_mem_commonS
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingsWithRead?_observable_eq_of_mem
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingsWithRead?_constitutionalObservable_eq_of_ne_nil
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_prior_computed
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_isSome_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_mem_rule5Readings_commonR
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_mem_rule5Readings_commonS
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_constitutionalObservable_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_observable_eq_prior
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_rule5Readings_observable_eq_of_mem
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_rule5Readings_observable_eq_of_mem_commonS
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_observable_eq_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_observable_eq_at_twice
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.rule1bLayers_head_of_sourceNodes_head
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.compareAddressedSourcesObserved_ne_eq_of_rule1b_head_distances
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.compareAddressedSourcesObserved_eq_rule1b_of_rule1a_eq_of_head_distances
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.compareObserved_ne_eq_of_rule1b_head_distances
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.compareObserved_eq_rule1b_of_rule1a_eq_of_head_distances
assert_kernel_only TetraStereo.OneCenter.ExactOfficialRuleMajorKey.compareObserved_eq_of_observable_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.cumulativeRule45ConstitutionalObservable_eq_observed
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.cumulativeConstitutionalComparison
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_eq_constitutional_of_ne
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_ne_eq_of_constitutional_ne
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_congr_of_observable_eq
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalCumulativeRule45KeyWithRead?_sourceNodes_head
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_eq_rule1b_of_builds
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_ne_eq_of_builds_of_rule1b_head_distances
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_congr_of_cumulative_builds
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_congr_of_builds_of_rule1b_head_distances
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4b_sourceNodes_head
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule4bcReadingWithRead?_rule4c_sourceNodes_head
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingWithRead?_commonR_sourceNodes_head
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootRule5ReadingWithRead?_commonS_sourceNodes_head
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule4bcKeyWithRead?_rule4a_sourceNodes_head
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.buildAromaticCanonicalRerootCompoundRule45KeyWithRead?_rule4a_sourceNodes_head
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound4bc_builds
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound45_builds
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_eq_rule1b_of_compound4bc_builds
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_eq_rule1b_of_compound45_builds
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_ne_eq_of_compound4bc_builds_of_rule1b_head_distances
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_ne_eq_of_compound45_builds_of_rule1b_head_distances
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound4bc_builds_of_rule1b_head_distances
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound45_builds_of_rule1b_head_distances
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_compareAromaticCanonicalCumulativeRule45Keys_congr_of_builds_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound4bc_builds_at_twice
assert_kernel_only TetraStereo.OneCenter.AuthoritativeChemicalInput.exists_compareAromaticCanonicalCumulativeRule45Keys_congr_of_compound45_builds_at_twice
