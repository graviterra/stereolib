import TetraStereo.OneCenter.CIPBlueBookConformance
import TetraStereo.OneCenter.LocalizedRerootCompoundRule45Key
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace Rule4c5SourceDecision

/-!
# Sparse Rules-4c/5 source-decision fidelity

This module compares the *actual* occurrence-local sparse comparators for Rule 4c and Rule 5
with an independent transcription of the Blue Book P-92 primitive decisions that
`TetraStereo.OneCenter.CIPBlueBookConformance` provides.

The independent side never calls the production comparator.  It is a first-applicable source
judgment over addressed symbolic observations:

* an address (a `List Nat` path of sibling slots) with an explicit path policy: a proper prefix
  (shorter address, i.e. the nearer position) is senior, otherwise the first differing
  component decides, smaller sibling slot first;
* only when the two addresses are *equal* is the symbolic P-92 decision consulted;
* when the addresses are equal and either observation is missing (`none`), the pair is
  `unavailable`.  `unavailable` is a separate constructor of `SourceDecision`, not the ordering
  `eq` and not a chemical "nonstereogenic" verdict.  This unavailability clause applies **only
  at tied addresses**: at distinct addresses the path policy still returns a verdict even when
  one or both observations are absent or out of family.

## Address policy is explicit implementation matching, not a P-92 derivation

`sourcePathDecision` is an explicit policy chosen to match the production sparse path
component.  We prove `sourcePathDecision_eq_flip_compareLex` that it is exactly
`flip (List.compareLex compareNat)` on the production encoding.  We do **not** claim that P-92
independently ranks sibling-slot paths this way; that identification is the stated policy of
this module, not an independently source-justified path ranking.

## Reading-level endpoints and residual assumptions

The reading-level theorems (`actualRule4cReading_conforms_source`,
`actualRule5Reading_conforms_source`) take the observed labels as hypotheses and identify the
actual reading fields/projections with compiled terminal keys through explicit hypotheses
(`leftRule4c`/`rightRule4c` or `leftProjection`/`rightProjection`).  They do not derive the
full compound reading builder, a `some`-ness theorem for the cumulative key, or the
reading-field-to-builder correspondence.  Supplying those derivations is residual work; this
module deliberately introduces no further assumption wrapper beyond the explicit wiring
hypotheses needed to state the actual reading comparison.


The actual side is the sparse lifting used by
`CertifiedLocalizedCIPInput.localizedCumulativeRule45Priority`, compared by
`OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority`.

## Exact domain and explicit guards

The actual label type is `LocalizedAuxiliaryLabel`
(`.chiral R/S` and `.pseudoasymmetric r/s`).  It does not contain `m`/`p`, axial/planar
families, or any other Rule-4c/Rule-5 family.  Consequently:

* Rule 4c is proved only for two `.pseudoasymmetric` labels (`r`/`s`), at equal addresses, in a
  cumulative stage that actually contains the Rule-4c component.  A `.chiral` observation is
  outside this source family and yields `unavailable`; the actual comparator then decides by
  Rule 4a kind first, which is preserved as a separate theorem.
* Rule 5 is proved only for two `.chiral` labels (`R`/`S`), in a cumulative stage whose probe is
  the tetrahedral-center, non-auxiliary probe of the actual comparator, and only after the
  earlier cumulative components tie.  This tie premise is genuine: if a selected Rule-4b
  reference separates the two ligands, the actual comparator stops before the Rule-5 bit.
* The common-**R** reading probes absolute P-92 sense (`R` senior, `S` junior).
  The common-**S** reading is a *sense-swapped probe*: it assigns `S` the senior bit.  It
  therefore agrees with the source decision only after swapping both input senses; it is not the
  absolute P-92 sense ordering.  This negative fact is stated explicitly below.

Full physical chemistry equivalence (molecule-to-digraph construction, stereogenic-unit
perception, absolute handedness) remains outside this module; this is exact source-decision
conformance on the explicitly typed, actual comparison domain.
-/

open BlueBookP92
open CertifiedLocalizedCIPInput

/-! ## Explicit address precedence policy -/

/-- Explicit address precedence policy for sibling-slot paths.

This is an implementation-matching policy, not an independently derived P-92 path ranking.
Orientation matches the production sparse comparator, whose first component is
`flip (List.compareLex compareNat)`: `gt` means the left address is senior/higher priority.
A smaller leading component is senior; when the leading components are equal the tails decide;
a proper prefix (shorter address) is senior.  The identification with the production path
component is *proved* in `sourcePathDecision_eq_flip_compareLex`. -/
def sourcePathDecision : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .gt
  | _ :: _, [] => .lt
  | a :: as, b :: bs => (compare b a).then (sourcePathDecision as bs)

/-- The independent address precedence is exactly the production sparse-entry path component.
This is the only place where the two address encodings are identified; it is proved, not assumed
by construction of the source judgment. -/
theorem sourcePathDecision_eq_flip_compareLex (left right : List Nat) :
    sourcePathDecision left right =
      flip (List.compareLex OfficialRuleMajorKey.compareNat) left right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons b bs => rfl
  | cons a as inductionHypothesis =>
      cases right with
      | nil => rfl
      | cons b bs =>
          change (compare b a).then (sourcePathDecision as bs) =
            flip (List.compareLex OfficialRuleMajorKey.compareNat) (a :: as) (b :: bs)
          rw [inductionHypothesis bs]
          simp only [flip, List.compareLex_cons_cons, OfficialRuleMajorKey.compareNat]

/-- Distinct addresses always receive a strict source decision; the source path order is total
and antisymmetric on its diagonal. -/
theorem sourcePathDecision_ne_eq_of_ne {left right : List Nat} (ne : left ≠ right) :
    sourcePathDecision left right ≠ Ordering.eq := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => exact (ne rfl).elim
      | cons b bs => simp [sourcePathDecision]
  | cons a as inductionHypothesis =>
      cases right with
      | nil => simp [sourcePathDecision]
      | cons b bs =>
          cases compared : compare b a with
          | lt => simp [sourcePathDecision, compared]
          | gt => simp [sourcePathDecision, compared]
          | eq =>
              have eqHeads : b = a := compare_eq_iff_eq.mp compared
              have tailNe : as ≠ bs := by
                intro same
                exact ne (by rw [← eqHeads, same])
              change (compare b a).then (sourcePathDecision as bs) ≠ Ordering.eq
              rw [compared, Ordering.eq_then]
              exact inductionHypothesis tailNe

/-- Equal addresses tie under the independent source precedence. -/
@[simp] theorem sourcePathDecision_self (address : List Nat) :
    sourcePathDecision address address = Ordering.eq := by
  induction address with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [sourcePathDecision, inductionHypothesis]

/-- Explicit path/length precedence: a proper prefix (a shorter address) is senior. -/
theorem sourcePathDecision_prefix_senior (stem extra : List Nat) (nonempty : extra ≠ []) :
    sourcePathDecision stem (stem ++ extra) = Ordering.gt := by
  induction stem generalizing extra with
  | nil =>
      cases extra with
      | nil => exact absurd rfl nonempty
      | cons head tail => rfl
  | cons a as inductionHypothesis =>
      cases extra with
      | nil => exact absurd rfl nonempty
      | cons b bs =>
          simp [sourcePathDecision, inductionHypothesis (b :: bs) (by simp)]

/-! ## First-applicable source judgment over addressed symbolic observations -/

/-- One symbolic source observation at an explicit address.  `value = none` is the explicit
availability probe result "no auxiliary label at this address"; it is not a stereochemical
classification. -/
structure AddressedObservation (α : Type*) where
  address : List Nat
  value : Option α
  deriving DecidableEq, Repr

/-- Independent source-jump result. `unavailable` records an absent/out-of-family observation;
it is deliberately not an `Ordering` and therefore cannot be mistaken for the chemical
"nonstereogenic" class or for an equality verdict. -/
inductive SourceDecision where
  | decided (ordering : Ordering)
  | unavailable
  deriving DecidableEq, Repr

def SourceDecision.ofOption : Option Ordering → SourceDecision
  | some ordering => .decided ordering
  | none => .unavailable

/-- First-applicable addressed judgment.

1. Address precedence is applied first.  It is a strict decision for distinct addresses.
2. Only at tied addresses are the two symbolic observations consulted.
3. If either observation is absent, the result is `unavailable`.

The observation decision is supplied independently; this function never inspects a production
key, label payload, or comparator. -/
def firstApplicableAddressed {α : Type*}
    (decideObservation : α → α → Option Ordering)
    (left right : AddressedObservation α) : SourceDecision :=
  match sourcePathDecision left.address right.address with
  | .eq =>
      match left.value, right.value with
      | some leftValue, some rightValue =>
          SourceDecision.ofOption (decideObservation leftValue rightValue)
      | _, _ => .unavailable
  | outcome => .decided outcome

/-! ## Independent Rule-4c source judgment -/

/-- The actual label type has only lowercase `r`/`s` in the Rule-4c family.  Uppercase
`.chiral R/S` belongs to the Rule-5 family and is out of family here. -/
def sourceRule4cSymbolOfPseudo : PseudoRS → Rule4cSymbol
  | .r => .r
  | .s => .s

/-- Family/availability guard for the Rule-4c source alphabet.  `none` (absent) and `.chiral`
(out of family) are unavailable; no `m`/`p` or axial family is fabricated. -/
def sourceRule4cSymbol? : Option LocalizedAuxiliaryLabel → Option Rule4cSymbol
  | some (.pseudoasymmetric pseudo) => some (sourceRule4cSymbolOfPseudo pseudo)
  | none | some (.chiral _) => none

/-- Independent Rule-4c pair decision: exactly P-92.1.3.4(c) on two available symbols. -/
def sourceRule4cPairDecision (left right : LocalizedAuxiliaryLabel) : Option Ordering :=
  match sourceRule4cSymbol? (some left), sourceRule4cSymbol? (some right) with
  | some leftSymbol, some rightSymbol => BlueBookP92.rule4cDecision? leftSymbol rightSymbol
  | _, _ => none

/-- Independent first-applicable Rule-4c source judgment over addressed symbolic observations. -/
def sourceRule4cJudgment
    (left right : AddressedObservation LocalizedAuxiliaryLabel) : SourceDecision :=
  firstApplicableAddressed sourceRule4cPairDecision left right

/-- At tied addresses the Rule-4c judgment is exactly the independent pair decision. -/
@[simp] theorem sourceRule4cJudgment_at_tiedAddress
    (address : List Nat) (left right : LocalizedAuxiliaryLabel) :
    sourceRule4cJudgment ⟨address, some left⟩ ⟨address, some right⟩ =
      SourceDecision.ofOption (sourceRule4cPairDecision left right) := by
  simp [sourceRule4cJudgment, firstApplicableAddressed]

/-- An absent observation at a tied address is `unavailable`, not a decision. -/
@[simp] theorem sourceRule4cJudgment_none_at_tiedAddress
    (address : List Nat) (right : Option LocalizedAuxiliaryLabel) :
    sourceRule4cJudgment ⟨address, none⟩ ⟨address, right⟩ = .unavailable := by
  simp [sourceRule4cJudgment, firstApplicableAddressed]

/-- `unavailable` is not the ordering tie; absence carries no chemical classification. -/
theorem unavailable_ne_decided (ordering : Ordering) :
    SourceDecision.unavailable ≠ SourceDecision.decided ordering := by
  intro equality
  cases equality

/-! ## Independent Rule-5 source judgment -/

/-- Independent probe sense.  The actual common-reference reading assigns the senior bit to the
ligand whose descriptor equals the probe reference. -/
def probeSense (probe descriptor : RS) : Rule5Sense :=
  if descriptor = probe then .senior else .junior

/-- The tetrahedral-center, non-auxiliary Rule-5 probe descriptor used by the actual cumulative
Rule-5 bit.  The family and auxiliary level are explicit guards: no axial or planar family is
claimed. -/
def probeRule5Descriptor (probe descriptor : RS) : Rule5Descriptor :=
  { family := .tetrahedralCenter, auxiliary := false, sense := probeSense probe descriptor }

/-- Absolute P-92 source sense of an uppercase tetrahedral descriptor. -/
def sourceRule5SenseOfRS : RS → Rule5Sense
  | .R => .senior
  | .S => .junior

/-- The absolute (unprobed) tetrahedral source descriptor. -/
def absoluteRule5Descriptor (descriptor : RS) : Rule5Descriptor :=
  { family := .tetrahedralCenter, auxiliary := false, sense := sourceRule5SenseOfRS descriptor }

/-- Swap senior/junior. -/
def senseSwap : Rule5Sense → Rule5Sense
  | .senior => .junior
  | .junior => .senior

/-- The common-R probe is the absolute P-92 sense order: `R` senior, `S` junior. -/
@[simp] theorem probeRule5Descriptor_R_eq_absolute (descriptor : RS) :
    probeRule5Descriptor .R descriptor = absoluteRule5Descriptor descriptor := by
  cases descriptor <;> rfl

/-- The common-S probe is the absolute sense order with both senses swapped: `S` is made senior,
`R` junior.  This is the formal content of "sense-swapped probe". -/
theorem probeRule5Descriptor_S_eq_senseSwapped_absolute (descriptor : RS) :
    probeRule5Descriptor .S descriptor =
      { absoluteRule5Descriptor descriptor with
          sense := senseSwap (absoluteRule5Descriptor descriptor).sense } := by
  cases descriptor <;> rfl

/-- Family/availability guard for the Rule-5 source probe: only uppercase `.chiral` observations
are in the tetrahedral family; lowercase pseudoasymmetric observations are reflection-invariant
at this layer and are unavailable. -/
def sourceRule5ProbeDescriptor? (probe : RS) (label : Option LocalizedAuxiliaryLabel) :
    Option Rule5Descriptor :=
  match label with
  | some (.chiral descriptor) => some (probeRule5Descriptor probe descriptor)
  | none | some (.pseudoasymmetric _) => none

/-- Independent Rule-5 pair decision at one probe reference. -/
def sourceRule5PairDecision (probe : RS)
    (left right : LocalizedAuxiliaryLabel) : Option Ordering :=
  match sourceRule5ProbeDescriptor? probe (some left),
      sourceRule5ProbeDescriptor? probe (some right) with
  | some leftDescriptor, some rightDescriptor => BlueBookP92.rule5Decision? leftDescriptor rightDescriptor
  | _, _ => none

/-- Independent first-applicable Rule-5 source judgment at one probe reference. -/
def sourceRule5Judgment (probe : RS)
    (left right : AddressedObservation LocalizedAuxiliaryLabel) : SourceDecision :=
  firstApplicableAddressed (sourceRule5PairDecision probe) left right

/-- At tied addresses the Rule-5 judgment is exactly the independent pair decision. -/
@[simp] theorem sourceRule5Judgment_at_tiedAddress
    (probe : RS) (address : List Nat) (left right : LocalizedAuxiliaryLabel) :
    sourceRule5Judgment probe ⟨address, some left⟩ ⟨address, some right⟩ =
      SourceDecision.ofOption (sourceRule5PairDecision probe left right) := by
  simp [sourceRule5Judgment, firstApplicableAddressed]

/-- Lowercase observations are out of the Rule-5 family and yield `unavailable`. -/
@[simp] theorem sourceRule5Judgment_pseudo_unavailable
    (probe : RS) (address : List Nat) (left right : PseudoRS) :
    sourceRule5Judgment probe
        ⟨address, some (.pseudoasymmetric left)⟩
        ⟨address, some (.pseudoasymmetric right)⟩ = .unavailable := by
  simp [sourceRule5Judgment, firstApplicableAddressed, sourceRule5PairDecision,
    sourceRule5ProbeDescriptor?, SourceDecision.ofOption]

/-! ## Sparse lifting of one actual stage observation -/

/-- Lift one addressed observation to the sparse descriptor shape consumed by the actual
comparators. -/
def liftSparseObservation {α : Type*} (address : List Nat) (vector : α) :
    List (List (OfficialSparseEntry α)) :=
  [[(address, vector)]]

/-- The actual cumulative priority vector of one stage observation, lifted to that sparse shape.
The label is erased into the numeric vector exactly as the occurrence builder does. -/
def actualStageObservation (stage : LocalizedCumulativeRule45Stage)
    (address : List Nat) (label : Option LocalizedAuxiliaryLabel) :
    List (List (OfficialSparseEntry (List Nat))) :=
  liftSparseObservation address (localizedCumulativeRule45Priority stage label)

/-- Singleton sparse comparison reduces to the path comparator followed by the observation
comparator.  This is the concrete one-entry computation of the production sparse stack. -/
private theorem compareSparseLayers_liftSparseObservation_then
    {α : Type*} (compareObservation : α → α → Ordering)
    (leftAddress rightAddress : List Nat) (leftVector rightVector : α) :
    OfficialRuleMajorKey.compareSparseLayers compareObservation
        (liftSparseObservation leftAddress leftVector)
        (liftSparseObservation rightAddress rightVector) =
      (flip (List.compareLex OfficialRuleMajorKey.compareNat) leftAddress rightAddress).then
        (compareObservation leftVector rightVector) := by
  dsimp only [liftSparseObservation, OfficialRuleMajorKey.compareSparseLayers,
    OfficialRuleMajorKey.compareSparseLayer, OfficialRuleMajorKey.compareSparseEntry,
    Ordering.byKey, compareLex]
  rw [List.compareLex_cons_cons, List.compareLex_cons_cons,
    List.compareLex_nil_nil, List.compareLex_nil_nil,
    Ordering.then_eq, Ordering.then_eq]
  rfl

/-- The actual sparse comparator on two singleton observations: path precedence first, then the
observation comparator at tied addresses.  No production key or comparator outcome is assumed. -/
theorem compareSparseLayers_liftSparseObservation
    {α : Type*} (compareObservation : α → α → Ordering)
    (leftAddress rightAddress : List Nat) (leftVector rightVector : α) :
    OfficialRuleMajorKey.compareSparseLayers compareObservation
        (liftSparseObservation leftAddress leftVector)
        (liftSparseObservation rightAddress rightVector) =
      match sourcePathDecision leftAddress rightAddress with
      | .eq => compareObservation leftVector rightVector
      | outcome => outcome := by
  rw [compareSparseLayers_liftSparseObservation_then,
    sourcePathDecision_eq_flip_compareLex leftAddress rightAddress]
  cases path : flip (List.compareLex OfficialRuleMajorKey.compareNat) leftAddress rightAddress <;>
    rfl

/-! ## Stage guards for the actual cumulative vectors -/

/-- The cumulative stage really contains a Rule-4c component.  In the other stages the actual
vector stops before `r/s`, so a claimed Rule-4c conformance would be false. -/
def stageHasRule4c : LocalizedCumulativeRule45Stage → Bool
  | .rule4a => false
  | .rule4b _ => false
  | .rule4cNoReference => true
  | .rule4c _ => true
  | .rule5NoRule4bReference _ => true
  | .rule5 _ _ => true

/-- The probe reference of a cumulative stage that contains a Rule-5 component. -/
def stageRule5Probe? : LocalizedCumulativeRule45Stage → Option RS
  | .rule5NoRule4bReference probe => some probe
  | .rule5 _ probe => some probe
  | _ => none

/-- The cumulative vector with its final Rule-5 component removed.  This is the actual earlier
priority material that Rule 5 is allowed to refine only after a tie. -/
def stagePriorityPrefix :
    LocalizedCumulativeRule45Stage → Option LocalizedAuxiliaryLabel → List Nat
  | .rule4a, label => [localizedRule4aPriority label]
  | .rule4b reference, label =>
      [localizedRule4aPriority label, localizedRule4bPriority reference label]
  | .rule4cNoReference, label =>
      [localizedRule4aPriority label, localizedRule4cPriority label]
  | .rule4c reference, label =>
      [localizedRule4aPriority label, localizedRule4bPriority reference label,
        localizedRule4cPriority label]
  | .rule5NoRule4bReference _, label =>
      [localizedRule4aPriority label, localizedRule4cPriority label]
  | .rule5 rule4bReference _, label =>
      [localizedRule4aPriority label, localizedRule4bPriority rule4bReference label,
        localizedRule4cPriority label]

/-- A cumulative vector is its earlier prefix followed by the Rule-5 bit, for every stage with a
Rule-5 probe. -/
theorem cumulativePriority_eq_prefix_append_rule5
    (stage : LocalizedCumulativeRule45Stage) (probe : RS)
    (probeEq : stageRule5Probe? stage = some probe)
    (label : Option LocalizedAuxiliaryLabel) :
    localizedCumulativeRule45Priority stage label =
      stagePriorityPrefix stage label ++ [localizedRule5Priority probe label] := by
  cases stage with
  | rule4a => simp [stageRule5Probe?] at probeEq
  | rule4b reference => simp [stageRule5Probe?] at probeEq
  | rule4cNoReference => simp [stageRule5Probe?] at probeEq
  | rule4c reference => simp [stageRule5Probe?] at probeEq
  | rule5NoRule4bReference probe' =>
      simp only [stageRule5Probe?, Option.some.injEq] at probeEq
      rw [probeEq]
      rfl
  | rule5 rule4bReference probe' =>
      simp only [stageRule5Probe?, Option.some.injEq] at probeEq
      rw [probeEq]
      rfl

/-- Comparing equal natural prefixes leaves exactly the singleton tails to compare. -/
theorem compareLex_compareNat_append_singleton (stem : List Nat) (left right : Nat) :
    List.compareLex OfficialRuleMajorKey.compareNat (stem ++ [left]) (stem ++ [right]) =
      OfficialRuleMajorKey.compareNat left right := by
  induction stem with
  | nil =>
      simp [List.compareLex_cons_cons, List.compareLex_nil_nil,
        OfficialRuleMajorKey.compareNat]
  | cons head tail inductionHypothesis =>
      simp only [List.cons_append, List.compareLex_cons_cons, inductionHypothesis,
        OfficialRuleMajorKey.compareNat]
      simp

/-- After an actual earlier-priority tie, the cumulative comparison is exactly the Rule-5 bit
comparison.  This is the numeric form of "a later rule refines only a tie". -/
theorem comparePriority_of_prefix_tie
    (stage : LocalizedCumulativeRule45Stage) (probe : RS)
    (probeEq : stageRule5Probe? stage = some probe)
    (left right : Option LocalizedAuxiliaryLabel)
    (tied : stagePriorityPrefix stage left = stagePriorityPrefix stage right) :
    compareLocalizedCumulativeRule45Priority
        (localizedCumulativeRule45Priority stage left)
        (localizedCumulativeRule45Priority stage right) =
      OfficialRuleMajorKey.compareNat
        (localizedRule5Priority probe left) (localizedRule5Priority probe right) := by
  simp only [compareLocalizedCumulativeRule45Priority]
  rw [cumulativePriority_eq_prefix_append_rule5 stage probe probeEq left,
    cumulativePriority_eq_prefix_append_rule5 stage probe probeEq right,
    tied, compareLex_compareNat_append_singleton]

/-! ## Actual Rule-4c conformance -/

/-- **Actual sparse Rule-4c comparison conforms to the independent source judgment.**

Guards: the stage contains Rule 4c, both observations are lowercase pseudoasymmetric `r/s`
(so Rule 4a kind ties, and the selected Rule-4b like/unlike components both read zero), and the
probe addresses are tied.  The source judgment is exactly the *decided* actual ordering; in
particular it never reports `unavailable` here. -/
theorem actualRule4cSingleton_conforms_source
    (stage : LocalizedCumulativeRule45Stage)
    (hasRule4c : stageHasRule4c stage = true)
    (address : List Nat) (leftPseudo rightPseudo : PseudoRS) :
    sourceRule4cJudgment
        ⟨address, some (.pseudoasymmetric leftPseudo)⟩
        ⟨address, some (.pseudoasymmetric rightPseudo)⟩ =
      SourceDecision.decided
        (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          (actualStageObservation stage address (some (.pseudoasymmetric leftPseudo)))
          (actualStageObservation stage address (some (.pseudoasymmetric rightPseudo)))) := by
  rw [sourceRule4cJudgment_at_tiedAddress]
  simp only [actualStageObservation, compareSparseLayers_liftSparseObservation,
    sourcePathDecision_self]
  cases stage <;> simp [stageHasRule4c] at hasRule4c <;>
    cases leftPseudo <;> cases rightPseudo <;> rfl

/-- Actual Rule-4c tie conditions: on two lowercase observations at the same address in an
Rule-4c-bearing stage, the comparator ties exactly when the two `r/s` symbols are equal. -/
theorem actualRule4cSingleton_eq_iff
    (stage : LocalizedCumulativeRule45Stage)
    (hasRule4c : stageHasRule4c stage = true)
    (address : List Nat) (leftPseudo rightPseudo : PseudoRS) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (actualStageObservation stage address (some (.pseudoasymmetric leftPseudo)))
        (actualStageObservation stage address (some (.pseudoasymmetric rightPseudo))) =
      Ordering.eq ↔ leftPseudo = rightPseudo := by
  simp only [actualStageObservation, compareSparseLayers_liftSparseObservation,
    sourcePathDecision_self]
  cases stage <;> simp [stageHasRule4c] at hasRule4c <;>
    cases leftPseudo <;> cases rightPseudo <;>
    simp only [compareLocalizedCumulativeRule45Priority,
      localizedCumulativeRule45Priority, localizedRule4aPriority,
      localizedRule4bPriority, localizedRule4cPriority, localizedRule5Priority] <;>
    decide

/-- **Rule-4a kind precedence is preserved and Rule-4c is unavailable out of family.**

An uppercase `.chiral` observation is senior to a lowercase `.pseudoasymmetric` one by Rule 4a,
independently of the later `r/s` value; the Rule-4c source pair decision is `none`.  Thus the
Rule-4c conformance theorem above cannot be silently extended across the kind boundary. -/
theorem actualChiral_precedes_pseudo_rule4c
    (stage : LocalizedCumulativeRule45Stage)
    (hasRule4c : stageHasRule4c stage = true)
    (address : List Nat) (chiral : RS) (pseudo : PseudoRS) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (actualStageObservation stage address (some (.chiral chiral)))
        (actualStageObservation stage address (some (.pseudoasymmetric pseudo))) =
        Ordering.gt ∧
      sourceRule4cPairDecision (.chiral chiral) (.pseudoasymmetric pseudo) = none := by
  constructor
  · simp only [actualStageObservation, compareSparseLayers_liftSparseObservation,
      sourcePathDecision_self]
    cases stage <;> simp [stageHasRule4c] at hasRule4c <;>
      cases chiral <;> cases pseudo <;> rfl
  · rfl

/-! ## Actual Rule-5 conformance -/

/-- **Actual sparse Rule-5 comparison conforms to the independent source judgment**, at a probe
reference and after the actual earlier-priority components tie.

Guards: the stage carries the same probe reference, both observations are uppercase tetrahedral
`.chiral R/S` in the tetrahedral-center non-auxiliary family, and the cumulative vector prefix
(Rule 4a, any selected Rule 4b reading, and Rule 4c) ties.  Without the tie premise an earlier
rule can decide first, which is exactly why the premise is explicit rather than derived from a
desired comparator outcome. -/
theorem actualRule5Singleton_conforms_source
    (stage : LocalizedCumulativeRule45Stage) (probe : RS)
    (probeEq : stageRule5Probe? stage = some probe)
    (address : List Nat) (leftDescriptor rightDescriptor : RS)
    (earlierTie : stagePriorityPrefix stage (some (.chiral leftDescriptor)) =
      stagePriorityPrefix stage (some (.chiral rightDescriptor))) :
    sourceRule5Judgment probe
        ⟨address, some (.chiral leftDescriptor)⟩
        ⟨address, some (.chiral rightDescriptor)⟩ =
      SourceDecision.decided
        (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          (actualStageObservation stage address (some (.chiral leftDescriptor)))
          (actualStageObservation stage address (some (.chiral rightDescriptor)))) := by
  rw [sourceRule5Judgment_at_tiedAddress]
  simp only [actualStageObservation, compareSparseLayers_liftSparseObservation,
    sourcePathDecision_self]
  rw [comparePriority_of_prefix_tie stage probe probeEq
    (some (.chiral leftDescriptor)) (some (.chiral rightDescriptor)) earlierTie]
  cases probe <;> cases leftDescriptor <;> cases rightDescriptor <;> rfl

/-- The common-R reading, which is the actual through-Rule-5 ordering component, conforms to the
absolute P-92 tetrahedral decision: `R` senior over `S` junior. -/
theorem actualCommonR_conforms_absolute_source
    (stage : LocalizedCumulativeRule45Stage)
    (probeEq : stageRule5Probe? stage = some .R)
    (address : List Nat) (leftDescriptor rightDescriptor : RS)
    (earlierTie : stagePriorityPrefix stage (some (.chiral leftDescriptor)) =
      stagePriorityPrefix stage (some (.chiral rightDescriptor))) :
    SourceDecision.ofOption
        (BlueBookP92.rule5Decision?
          (absoluteRule5Descriptor leftDescriptor)
          (absoluteRule5Descriptor rightDescriptor)) =
      SourceDecision.decided
        (OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          (actualStageObservation stage address (some (.chiral leftDescriptor)))
          (actualStageObservation stage address (some (.chiral rightDescriptor)))) := by
  have conforms := actualRule5Singleton_conforms_source stage .R probeEq address
    leftDescriptor rightDescriptor earlierTie
  rw [sourceRule5Judgment_at_tiedAddress] at conforms
  simpa [sourceRule5PairDecision, sourceRule5ProbeDescriptor?,
    probeRule5Descriptor_R_eq_absolute] using conforms

/-- The common-S reading is a sense-swapped probe: it is senior for `S` and junior for `R`.
Therefore it does **not** have the absolute P-92 sense ordering.  This is stated as an explicit
negative result, not hidden behind a conformance claim.  The earlier-priority tie premise is the
same genuine precondition as in Rule-5 conformance. -/
theorem actualCommonS_is_sense_swapped_not_absolute
    (stage : LocalizedCumulativeRule45Stage)
    (probeEq : stageRule5Probe? stage = some .S)
    (address : List Nat)
    (earlierTie : stagePriorityPrefix stage (some (.chiral .S)) =
      stagePriorityPrefix stage (some (.chiral .R))) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (actualStageObservation stage address (some (.chiral .S)))
        (actualStageObservation stage address (some (.chiral .R))) =
        Ordering.gt ∧
      BlueBookP92.rule5Decision?
        (absoluteRule5Descriptor .S) (absoluteRule5Descriptor .R) = some Ordering.lt := by
  have sourceValue : sourceRule5Judgment .S
      ⟨address, some (.chiral .S)⟩ ⟨address, some (.chiral .R)⟩ =
      SourceDecision.decided Ordering.gt := by
    rw [sourceRule5Judgment_at_tiedAddress]
    simp only [sourceRule5PairDecision, sourceRule5ProbeDescriptor?, probeRule5Descriptor,
      probeSense, SourceDecision.ofOption]
    rfl
  have conforms := actualRule5Singleton_conforms_source stage .S probeEq address
    .S .R earlierTie
  rw [sourceValue] at conforms
  exact ⟨SourceDecision.decided.inj conforms |>.symm, by rfl⟩

/-- Unconditional witness that the common-S swap is reachable in the actual Rule-5 stage with no
selected Rule-4b reference; the explicit tie premise above is therefore satisfiable, not
vacuous. -/
theorem actualCommonS_sense_swapped_witness (address : List Nat) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (actualStageObservation (.rule5NoRule4bReference .S) address (some (.chiral .S)))
        (actualStageObservation (.rule5NoRule4bReference .S) address (some (.chiral .R))) =
        Ordering.gt ∧
      BlueBookP92.rule5Decision?
        (absoluteRule5Descriptor .S) (absoluteRule5Descriptor .R) = some Ordering.lt := by
  exact actualCommonS_is_sense_swapped_not_absolute
    (.rule5NoRule4bReference .S) rfl address rfl

/-- Concrete actual Rule-4c orientation `r > s`, together with the independent source judgment's
identical decided verdict.  This is the numeric ordering requested by the source theorem, in
every actual cumulative stage that contains Rule 4c. -/
theorem actualRule4c_r_over_s_source
    (stage : LocalizedCumulativeRule45Stage)
    (hasRule4c : stageHasRule4c stage = true)
    (address : List Nat) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (actualStageObservation stage address (some (.pseudoasymmetric .r)))
        (actualStageObservation stage address (some (.pseudoasymmetric .s))) = Ordering.gt ∧
      sourceRule4cJudgment
        ⟨address, some (.pseudoasymmetric .r)⟩
        ⟨address, some (.pseudoasymmetric .s)⟩ = SourceDecision.decided Ordering.gt := by
  have sourceValue : sourceRule4cJudgment
      ⟨address, some (.pseudoasymmetric .r)⟩
      ⟨address, some (.pseudoasymmetric .s)⟩ = SourceDecision.decided Ordering.gt := by
    rw [sourceRule4cJudgment_at_tiedAddress]
    simp only [sourceRule4cPairDecision, sourceRule4cSymbol?, sourceRule4cSymbolOfPseudo,
      SourceDecision.ofOption]
    rfl
  have conforms := actualRule4cSingleton_conforms_source stage hasRule4c address .r .s
  rw [sourceValue] at conforms
  exact ⟨SourceDecision.decided.inj conforms |>.symm, sourceValue⟩

/-- Concrete actual common-R Rule-5 orientation `R > S`, together with the absolute P-92
tetrahedral decision.  The chosen actual stage has no selected Rule-4b reference, so the genuine
earlier-priority tie is definitional rather than assumed. -/
theorem actualCommonR_R_over_S_source (address : List Nat) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (actualStageObservation (.rule5NoRule4bReference .R) address (some (.chiral .R)))
        (actualStageObservation (.rule5NoRule4bReference .R) address (some (.chiral .S))) =
        Ordering.gt ∧
      BlueBookP92.rule5Decision?
        (absoluteRule5Descriptor .R) (absoluteRule5Descriptor .S) = some Ordering.gt := by
  have sourceValue : SourceDecision.ofOption
      (BlueBookP92.rule5Decision?
        (absoluteRule5Descriptor .R) (absoluteRule5Descriptor .S)) =
      SourceDecision.decided Ordering.gt := by
    rfl
  have conforms := actualCommonR_conforms_absolute_source
    (.rule5NoRule4bReference .R) rfl address .R .S rfl
  rw [sourceValue] at conforms
  exact ⟨SourceDecision.decided.inj conforms |>.symm, by rfl⟩

/-! ## Builder output: erasure and position correspondence -/

/-- **Actual builder output at a terminal cursor.**

The compiled descriptor is exactly the singleton sparse observation at address `[]` whose
observation is the stage priority vector of the label read from the dependency view.  This is
derived by unfolding the actual builder; it does not assume any raw `sourceNodes` alignment, any
symbolic-source alignment, or any comparator outcome. -/
theorem buildLocalizedRerootCumulativeRule45Key?_terminal_descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (children : input.localizedRerootChildren? cursor = some [])
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key) :
    key.descriptor =
      actualStageObservation stage [] (input.localizedDependencyLabel target view cursor) := by
  cases fuel with
  | zero =>
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      rw [children] at computed
      simp at computed
      subst key
      rfl
  | succ fuel =>
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      rw [children] at computed
      simp at computed
      subst key
      rfl

/-! ## Actual reading comparators -/

/-- The actual Rule-4c reading comparator on singleton reading lists reads exactly the two
Rule-4c cumulative descriptor projections. -/
theorem compareLocalizedRerootCompoundRule4cReadings_singleton
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRule4bcReading) :
    input.compareLocalizedRerootCompoundRule4cReadings [left] [right] =
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        left.rule4cKey.descriptor right.rule4cKey.descriptor := by
  simp [compareLocalizedRerootCompoundRule4cReadings, List.compareLex_cons_cons,
    List.compareLex_nil_nil, Ordering.byKey]

/-- The actual Rule-5 reading comparator on singleton reading lists reads exactly the two
common-reference cumulative descriptor projections. -/
theorem compareLocalizedRerootCompoundRule5Readings_singleton
    (input : CertifiedLocalizedCIPInput) (probe : RS)
    (left right : input.LocalizedRerootRule5Reading) :
    input.compareLocalizedRerootCompoundRule5Readings probe [left] [right] =
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (input.localizedRerootRule5Descriptor probe left)
        (input.localizedRerootRule5Descriptor probe right) := by
  simp [compareLocalizedRerootCompoundRule5Readings, List.compareLex_cons_cons,
    List.compareLex_nil_nil, Ordering.byKey]

/-- The common-R descriptor projection is the actual `commonR` field. -/
@[simp] theorem localizedRerootRule5Descriptor_R_eq_commonR
    (input : CertifiedLocalizedCIPInput)
    (reading : input.LocalizedRerootRule5Reading) :
    input.localizedRerootRule5Descriptor .R reading = reading.commonR.descriptor := rfl

/-- The common-S descriptor projection is the actual `commonS` field. -/
@[simp] theorem localizedRerootRule5Descriptor_S_eq_commonS
    (input : CertifiedLocalizedCIPInput)
    (reading : input.LocalizedRerootRule5Reading) :
    input.localizedRerootRule5Descriptor .S reading = reading.commonS.descriptor := rfl

/-! ## Actual reading-level conformance from builder output -/

/-- **Actual Rule-4c reading comparison conforms to the independent source judgment.**

The two reading keys are the actual compiled terminal keys; `leftRule4c`/`rightRule4c` identify
the actual `rule4cKey` fields with those compiled keys (as produced by the Rule-4bc reading
builder).  The observed labels are explicit hypotheses, and both addresses are the builder's
actual `[]` root address. -/
theorem actualRule4cReading_conforms_source
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (reference : RS)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftKey rightKey : input.LocalizedRerootCumulativeRule45Key)
    (leftChildren : input.localizedRerootChildren? leftCursor = some [])
    (rightChildren : input.localizedRerootChildren? rightCursor = some [])
    (leftComputed : input.buildLocalizedRerootCumulativeRule45Key?
      (.rule4c reference) target view fuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCumulativeRule45Key?
      (.rule4c reference) target view fuel rightCursor = some rightKey)
    (leftPseudo rightPseudo : PseudoRS)
    (leftObserved : input.localizedDependencyLabel target view leftCursor =
      some (.pseudoasymmetric leftPseudo))
    (rightObserved : input.localizedDependencyLabel target view rightCursor =
      some (.pseudoasymmetric rightPseudo))
    (leftReading rightReading : input.LocalizedRerootRule4bcReading)
    (leftRule4c : leftReading.rule4cKey = leftKey)
    (rightRule4c : rightReading.rule4cKey = rightKey) :
    sourceRule4cJudgment
        ⟨[], some (.pseudoasymmetric leftPseudo)⟩
        ⟨[], some (.pseudoasymmetric rightPseudo)⟩ =
      SourceDecision.decided
        (input.compareLocalizedRerootCompoundRule4cReadings [leftReading] [rightReading]) := by
  rw [compareLocalizedRerootCompoundRule4cReadings_singleton]
  rw [leftRule4c, rightRule4c]
  rw [buildLocalizedRerootCumulativeRule45Key?_terminal_descriptor input
    (.rule4c reference) target view fuel leftCursor leftChildren leftKey leftComputed]
  rw [buildLocalizedRerootCumulativeRule45Key?_terminal_descriptor input
    (.rule4c reference) target view fuel rightCursor rightChildren rightKey rightComputed]
  rw [leftObserved, rightObserved]
  exact actualRule4cSingleton_conforms_source (.rule4c reference) rfl [] leftPseudo rightPseudo

/-- **Actual Rule-5 reading comparison conforms to the independent source judgment.**

The common-reference descriptor projections are identified with the actual compiled terminal
keys.  The earlier-priority tie premise is explicit and is the precise precondition under which
the source Rule-5 decision is reached. -/
theorem actualRule5Reading_conforms_source
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (stage : LocalizedCumulativeRule45Stage) (probe : RS)
    (probeEq : stageRule5Probe? stage = some probe)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftKey rightKey : input.LocalizedRerootCumulativeRule45Key)
    (leftChildren : input.localizedRerootChildren? leftCursor = some [])
    (rightChildren : input.localizedRerootChildren? rightCursor = some [])
    (leftComputed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel rightCursor = some rightKey)
    (leftDescriptor rightDescriptor : RS)
    (leftObserved : input.localizedDependencyLabel target view leftCursor =
      some (.chiral leftDescriptor))
    (rightObserved : input.localizedDependencyLabel target view rightCursor =
      some (.chiral rightDescriptor))
    (leftReading rightReading : input.LocalizedRerootRule5Reading)
    (leftProjection : input.localizedRerootRule5Descriptor probe leftReading =
      leftKey.descriptor)
    (rightProjection : input.localizedRerootRule5Descriptor probe rightReading =
      rightKey.descriptor)
    (earlierTie : stagePriorityPrefix stage (some (.chiral leftDescriptor)) =
      stagePriorityPrefix stage (some (.chiral rightDescriptor))) :
    sourceRule5Judgment probe
        ⟨[], some (.chiral leftDescriptor)⟩
        ⟨[], some (.chiral rightDescriptor)⟩ =
      SourceDecision.decided
        (input.compareLocalizedRerootCompoundRule5Readings probe [leftReading] [rightReading]) := by
  rw [compareLocalizedRerootCompoundRule5Readings_singleton]
  rw [leftProjection, rightProjection]
  rw [buildLocalizedRerootCumulativeRule45Key?_terminal_descriptor input
    stage target view fuel leftCursor leftChildren leftKey leftComputed]
  rw [buildLocalizedRerootCumulativeRule45Key?_terminal_descriptor input
    stage target view fuel rightCursor rightChildren rightKey rightComputed]
  rw [leftObserved, rightObserved]
  exact actualRule5Singleton_conforms_source stage probe probeEq []
    leftDescriptor rightDescriptor earlierTie

/-! ## Kernel-only export checks -/

/- Public definitions, structures and inductives (22 declared objects). -/
assert_kernel_only AddressedObservation
assert_kernel_only SourceDecision
assert_kernel_only sourcePathDecision
assert_kernel_only SourceDecision.ofOption
assert_kernel_only firstApplicableAddressed
assert_kernel_only sourceRule4cSymbolOfPseudo
assert_kernel_only sourceRule4cSymbol?
assert_kernel_only sourceRule4cPairDecision
assert_kernel_only sourceRule4cJudgment
assert_kernel_only probeSense
assert_kernel_only probeRule5Descriptor
assert_kernel_only sourceRule5SenseOfRS
assert_kernel_only absoluteRule5Descriptor
assert_kernel_only senseSwap
assert_kernel_only sourceRule5ProbeDescriptor?
assert_kernel_only sourceRule5PairDecision
assert_kernel_only sourceRule5Judgment
assert_kernel_only liftSparseObservation
assert_kernel_only actualStageObservation
assert_kernel_only stageHasRule4c
assert_kernel_only stageRule5Probe?
assert_kernel_only stagePriorityPrefix

/- Public theorem exports. -/
assert_kernel_only sourcePathDecision_eq_flip_compareLex
assert_kernel_only sourcePathDecision_ne_eq_of_ne
assert_kernel_only sourcePathDecision_self
assert_kernel_only sourcePathDecision_prefix_senior
assert_kernel_only sourceRule4cJudgment_at_tiedAddress
assert_kernel_only sourceRule4cJudgment_none_at_tiedAddress
assert_kernel_only unavailable_ne_decided
assert_kernel_only probeRule5Descriptor_R_eq_absolute
assert_kernel_only probeRule5Descriptor_S_eq_senseSwapped_absolute
assert_kernel_only sourceRule5Judgment_at_tiedAddress
assert_kernel_only sourceRule5Judgment_pseudo_unavailable
assert_kernel_only compareSparseLayers_liftSparseObservation
assert_kernel_only cumulativePriority_eq_prefix_append_rule5
assert_kernel_only compareLex_compareNat_append_singleton
assert_kernel_only comparePriority_of_prefix_tie
assert_kernel_only actualRule4cSingleton_conforms_source
assert_kernel_only actualRule4cSingleton_eq_iff
assert_kernel_only actualChiral_precedes_pseudo_rule4c
assert_kernel_only actualRule5Singleton_conforms_source
assert_kernel_only actualCommonR_conforms_absolute_source
assert_kernel_only actualCommonS_is_sense_swapped_not_absolute
assert_kernel_only actualCommonS_sense_swapped_witness
assert_kernel_only actualRule4c_r_over_s_source
assert_kernel_only actualCommonR_R_over_S_source
assert_kernel_only buildLocalizedRerootCumulativeRule45Key?_terminal_descriptor
assert_kernel_only compareLocalizedRerootCompoundRule4cReadings_singleton
assert_kernel_only compareLocalizedRerootCompoundRule5Readings_singleton
assert_kernel_only localizedRerootRule5Descriptor_R_eq_commonR
assert_kernel_only localizedRerootRule5Descriptor_S_eq_commonS
assert_kernel_only actualRule4cReading_conforms_source
assert_kernel_only actualRule5Reading_conforms_source

end Rule4c5SourceDecision

end TetraStereo.OneCenter
