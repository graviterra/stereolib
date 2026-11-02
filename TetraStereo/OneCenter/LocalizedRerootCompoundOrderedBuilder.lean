import TetraStereo.OneCenter.LocalizedRerootCompoundRule45OutcomeOrder
import TetraStereo.OneCenter.LocalizedOccurrenceRule45Descriptor
import TetraStereo.OneCenter.LocalizedCompoundParentNoninterference
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 800000

/-!
# The ordered compound builder and the ordered bare Rule-4/5 evaluator

The repair proposed in `LocalizedRerootCompoundRule4bcOutcomeOrder` post-processes a built
compound key (`outcomeOrdered`, `outcomeOrdered45`).  This module states the repair as a
**builder**: `buildLocalizedRerootCompoundRule4bcKeyOrdered?` is the production compound
Rules-4b/4c builder with the alternatives placed in outcome order, and
`buildLocalizedRerootCompoundRule45KeyOrdered?` builds the Rule-5 readings per alternative from the
ordered prior.  Both are identified with the post-processing of the production builds
(`…Ordered?_eq_map`): the Rule-5 readings commute with the two-alternative order
(`buildLocalizedRerootRule5Readings?_rankReadings`).  Their declarative meanings are the production
derivations followed by the order.

On top of the builder the **ordered bare Rule-4/5 evaluator** is assembled along the production
pipeline of `localizedOccurrenceRule45Descriptor?` (the executable rule of the bare Rule-4/5
auxiliary semantics, which the generated reference state satisfies on inputs without double-bond
records): `compareLocalizedOccurrenceThroughRule5OrderedAt?`,
`safeLocalizedOccurrenceRule45TrackedOrderOrdered?`, `localizedOccurrenceRule45DescriptorOrdered?`.
The tracked-order, coherence and safe-order steps are stated once over an arbitrary pairwise
comparison function (`safeTrackedOrderOf`), of which both the production and the ordered pipeline
are instances.

Agreement and refusal lemmas for the preservation proof (P1):

* `localizedOccurrenceRule45DescriptorOrdered?_eq_of_compareAt_eq` — the descriptor depends on
  the compound keys only through the pairwise comparison records;
* `compareThroughRule5_outcomeOrdered45_of_rule4a_ne` — a Rule-4a-decided pair compares
  identically after ordering;
* `outcomeOrdered45_eq_self_of_length_le_one` (imported) — keys with at most one alternative are
  unchanged;
* `safeTrackedOrderOf_eq_none_of_tie`, `localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_safe_eq_none`
  — two tied distinct slots make the tracked order incoherent and the descriptor refuse.
-/

namespace TetraStereo.OneCenter
namespace CertifiedLocalizedCIPInput

noncomputable section

variable (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}

/-! ## The ordered compound builders -/

section Builders

variable (target : input.LocalizedCIPOccurrence carrierFuel)
  (view : input.LocalizedDependencyView target)
  (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)

/-- The production compound Rules-4b/4c builder with the alternatives in outcome order. -/
def buildLocalizedRerootCompoundRule4bcKeyOrdered? :
    Option input.LocalizedRerootCompoundRule4bcKey := do
  let rule4aKey ← input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor
  let references := localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
  let alternatives := localizedRule4bcReferenceAlternatives references
  let readings ← input.buildLocalizedRerootRule4bcReadings? target view fuel cursor alternatives
  some
    { rule4aKey := rule4aKey
      references := references
      referenceCountPriority := constitutionalRule4bReferenceCountPriority references
      readings := input.rankReadings readings }

/-- The ordered builder is the production build with its alternatives ordered afterwards. -/
theorem buildLocalizedRerootCompoundRule4bcKeyOrdered?_eq_map :
    input.buildLocalizedRerootCompoundRule4bcKeyOrdered? target view fuel cursor =
      Option.map input.outcomeOrdered
        (input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor) := by
  unfold buildLocalizedRerootCompoundRule4bcKeyOrdered? buildLocalizedRerootCompoundRule4bcKey?
  cases h4a : input.buildLocalizedRerootCumulativeRule45Key? .rule4a target view fuel cursor with
  | none => rfl
  | some rule4aKey =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases hr : input.buildLocalizedRerootRule4bcReadings? target view fuel cursor
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => rfl
      | some readings => rfl

/-- A built Rule-5 reading records its alternative. -/
theorem buildLocalizedRerootRule5Reading?_prior {prior : input.LocalizedRerootRule4bcReading}
    {reading : input.LocalizedRerootRule5Reading}
    (h : input.buildLocalizedRerootRule5Reading? target view fuel cursor prior = some reading) :
    reading.prior = prior := by
  unfold buildLocalizedRerootRule5Reading? at h
  cases hR : input.buildLocalizedRerootCumulativeRule45Key?
      (localizedRule5StageFor prior.reference? .R) target view fuel cursor with
  | none => simp [hR] at h
  | some commonR =>
      cases hS : input.buildLocalizedRerootCumulativeRule45Key?
          (localizedRule5StageFor prior.reference? .S) target view fuel cursor with
      | none => simp [hR, hS] at h
      | some commonS =>
          simp [hR, hS] at h
          subst h
          rfl

theorem rankRule5Readings_of_length_ne_two (readings : List input.LocalizedRerootRule5Reading)
    (h : readings.length ≠ 2) : input.rankRule5Readings readings = readings := by
  match readings, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], h => exact absurd rfl h
  | _ :: _ :: _ :: _, _ => rfl

theorem rankReadings_of_length_ne_two (readings : List input.LocalizedRerootRule4bcReading)
    (h : readings.length ≠ 2) : input.rankReadings readings = readings := by
  match readings, h with
  | [], _ => rfl
  | [_], _ => rfl
  | [_, _], h => exact absurd rfl h
  | _ :: _ :: _ :: _, _ => rfl

theorem buildLocalizedRerootRule5Readings?_length
    (priors : List input.LocalizedRerootRule4bcReading)
    {readings : List input.LocalizedRerootRule5Reading}
    (h : input.buildLocalizedRerootRule5Readings? target view fuel cursor priors = some readings) :
    readings.length = priors.length := by
  induction priors generalizing readings with
  | nil => simp [buildLocalizedRerootRule5Readings?] at h; subst h; rfl
  | cons prior priors ih =>
      unfold buildLocalizedRerootRule5Readings? at h
      cases hr : input.buildLocalizedRerootRule5Reading? target view fuel cursor prior with
      | none => simp [hr] at h
      | some reading =>
          cases hrest : input.buildLocalizedRerootRule5Readings? target view fuel cursor priors with
          | none => simp [hr, hrest] at h
          | some rest =>
              simp [hr, hrest] at h
              subst h
              simp [ih hrest]

/-- **The Rule-5 readings commute with the two-alternative order.** -/
theorem buildLocalizedRerootRule5Readings?_rankReadings
    (readings : List input.LocalizedRerootRule4bcReading) :
    input.buildLocalizedRerootRule5Readings? target view fuel cursor (input.rankReadings readings) =
      Option.map input.rankRule5Readings
        (input.buildLocalizedRerootRule5Readings? target view fuel cursor readings) := by
  by_cases hlen : readings.length = 2
  · obtain ⟨a, b, rfl⟩ := List.length_eq_two.1 hlen
    have expand : ∀ (x y : input.LocalizedRerootRule4bcReading),
        input.buildLocalizedRerootRule5Readings? target view fuel cursor [x, y] =
          match input.buildLocalizedRerootRule5Reading? target view fuel cursor x,
              input.buildLocalizedRerootRule5Reading? target view fuel cursor y with
          | some rx, some ry => some [rx, ry]
          | _, _ => none := by
      intro x y
      simp only [buildLocalizedRerootRule5Readings?]
      cases input.buildLocalizedRerootRule5Reading? target view fuel cursor x <;>
        cases input.buildLocalizedRerootRule5Reading? target view fuel cursor y <;> rfl
    simp only [rankReadings]
    cases ha : input.buildLocalizedRerootRule5Reading? target view fuel cursor a with
    | none =>
        split_ifs <;> simp [expand, ha]
    | some ra =>
        cases hb : input.buildLocalizedRerootRule5Reading? target view fuel cursor b with
        | none => split_ifs <;> simp [expand, ha, hb]
        | some rb =>
            have pa := input.buildLocalizedRerootRule5Reading?_prior target view fuel cursor ha
            have pb := input.buildLocalizedRerootRule5Reading?_prior target view fuel cursor hb
            split_ifs with hord
            · simp only [expand, ha, hb, Option.map_some, rankRule5Readings, pa, pb, hord]
              rfl
            · simp only [expand, ha, hb, Option.map_some, rankRule5Readings, pa, pb, hord]
              rfl
  · rw [input.rankReadings_of_length_ne_two readings hlen]
    cases h : input.buildLocalizedRerootRule5Readings? target view fuel cursor readings with
    | none => rfl
    | some rs =>
        have := input.buildLocalizedRerootRule5Readings?_length target view fuel cursor readings h
        rw [Option.map_some, input.rankRule5Readings_of_length_ne_two rs (by rw [this]; exact hlen)]

/-- The production through-Rule-5 builder on the ordered prior. -/
def buildLocalizedRerootCompoundRule45KeyOrdered? :
    Option input.LocalizedRerootCompoundRule45Key := do
  let prior ← input.buildLocalizedRerootCompoundRule4bcKeyOrdered? target view fuel cursor
  let readings ← input.buildLocalizedRerootRule5Readings? target view fuel cursor prior.readings
  some { prior := prior, rule5Readings := readings }

/-- **The ordered through-Rule-5 builder is the ordered production build.** -/
theorem buildLocalizedRerootCompoundRule45KeyOrdered?_eq_map :
    input.buildLocalizedRerootCompoundRule45KeyOrdered? target view fuel cursor =
      Option.map input.outcomeOrdered45
        (input.buildLocalizedRerootCompoundRule45Key? target view fuel cursor) := by
  unfold buildLocalizedRerootCompoundRule45KeyOrdered? buildLocalizedRerootCompoundRule45Key?
  rw [input.buildLocalizedRerootCompoundRule4bcKeyOrdered?_eq_map]
  cases hp : input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor with
  | none => rfl
  | some prior =>
      simp only [Option.bind_eq_bind, Option.bind_some, Option.map_some]
      rw [show (input.outcomeOrdered prior).readings = input.rankReadings prior.readings from rfl,
        input.buildLocalizedRerootRule5Readings?_rankReadings]
      cases hr : input.buildLocalizedRerootRule5Readings? target view fuel cursor prior.readings with
      | none => rfl
      | some readings => rfl

/-- Independent meaning of the ordered compound Rules-4b/4c key: a production derivation followed
by the outcome order of its alternatives. -/
def DeclarativeLocalizedRerootCompoundRule4bcKeyOrdered
    (key : input.LocalizedRerootCompoundRule4bcKey) : Prop :=
  ∃ built, input.DeclarativeLocalizedRerootCompoundRule4bcKey target view fuel cursor built ∧
    key = input.outcomeOrdered built

def DeclarativeLocalizedRerootCompoundRule45KeyOrdered
    (key : input.LocalizedRerootCompoundRule45Key) : Prop :=
  ∃ built, input.DeclarativeLocalizedRerootCompoundRule45Key target view fuel cursor built ∧
    key = input.outcomeOrdered45 built

theorem buildLocalizedRerootCompoundRule4bcKeyOrdered?_sound
    {key : input.LocalizedRerootCompoundRule4bcKey}
    (computed : input.buildLocalizedRerootCompoundRule4bcKeyOrdered? target view fuel cursor =
      some key) :
    input.DeclarativeLocalizedRerootCompoundRule4bcKeyOrdered target view fuel cursor key := by
  rw [buildLocalizedRerootCompoundRule4bcKeyOrdered?_eq_map] at computed
  cases h : input.buildLocalizedRerootCompoundRule4bcKey? target view fuel cursor with
  | none => rw [h] at computed; simp at computed
  | some built =>
      rw [h] at computed
      refine ⟨built, input.buildLocalizedRerootCompoundRule4bcKey?_sound target view fuel cursor
        built h, ?_⟩
      simpa using computed.symm

theorem buildLocalizedRerootCompoundRule45KeyOrdered?_sound
    {key : input.LocalizedRerootCompoundRule45Key}
    (computed : input.buildLocalizedRerootCompoundRule45KeyOrdered? target view fuel cursor =
      some key) :
    input.DeclarativeLocalizedRerootCompoundRule45KeyOrdered target view fuel cursor key := by
  rw [buildLocalizedRerootCompoundRule45KeyOrdered?_eq_map] at computed
  cases h : input.buildLocalizedRerootCompoundRule45Key? target view fuel cursor with
  | none => rw [h] at computed; simp at computed
  | some built =>
      rw [h] at computed
      refine ⟨built, input.buildLocalizedRerootCompoundRule45Key?_sound target view fuel cursor
        built h, ?_⟩
      simpa using computed.symm

end Builders

/-! ## The tracked order over an arbitrary pairwise comparison -/

section Generic

variable (compareAt : Fin 4 → Fin 4 → Option ConstitutionalDescriptorHierarchyComparison)

/-- Strict earlier/later check for one pair. -/
def pairStrictOf (left right : Fin 4) : Bool :=
  match compareAt left right with
  | none => false
  | some result => result.ordering == Ordering.gt

/-- All-pairs coherence of a candidate order. -/
def orderCoherentOf : List (Fin 4) → Bool
  | [] => true
  | left :: rest => rest.all (pairStrictOf compareAt left) && orderCoherentOf rest

/-- The safe tracked order: the stable four-ligand sort, accepted only when all pairs are strict. -/
def safeTrackedOrderOf : Option TrackedLocalizedLigandOrder := do
  let tracked ← sortFourLocalizedLigandsTracked compareAt
  if orderCoherentOf compareAt tracked.highestFirst then some tracked else none

theorem pairStrictOf_eq_true_iff (left right : Fin 4) :
    pairStrictOf compareAt left right = true ↔
      ∃ result, compareAt left right = some result ∧ result.ordering = Ordering.gt := by
  unfold pairStrictOf
  cases h : compareAt left right with
  | none => simp
  | some result => simp [beq_iff_eq]

theorem orderCoherentOf_eq_true_iff :
    ∀ order : List (Fin 4), orderCoherentOf compareAt order = true ↔
      order.Pairwise fun left right =>
        ∃ result, compareAt left right = some result ∧ result.ordering = Ordering.gt
  | [] => by simp [orderCoherentOf]
  | left :: rest => by
      simp only [orderCoherentOf, Bool.and_eq_true, List.all_eq_true, List.pairwise_cons,
        pairStrictOf_eq_true_iff, orderCoherentOf_eq_true_iff rest]

/-- **Two tied distinct slots refuse the safe order.** -/
theorem safeTrackedOrderOf_eq_none_of_tie {i j : Fin 4} (hij : i ≠ j)
    (tieIJ : ∃ result, compareAt i j = some result ∧ result.ordering = Ordering.eq)
    (tieJI : ∃ result, compareAt j i = some result ∧ result.ordering = Ordering.eq) :
    safeTrackedOrderOf compareAt = none := by
  unfold safeTrackedOrderOf
  cases hsort : sortFourLocalizedLigandsTracked compareAt with
  | none => rfl
  | some tracked =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [if_neg]
      intro coherent
      have pairwise := (orderCoherentOf_eq_true_iff compareAt tracked.highestFirst).1 coherent
      have perm := sortFourLocalizedLigandsTracked_perm compareAt tracked hsort
      have sym : tracked.highestFirst.Pairwise fun a b : Fin 4 =>
          (∃ result, compareAt a b = some result ∧ result.ordering = Ordering.gt) ∨
            (∃ result, compareAt b a = some result ∧ result.ordering = Ordering.gt) :=
        pairwise.imp fun h => Or.inl h
      rcases List.Pairwise.forall (fun _ _ h => h.symm) sym
          (perm.mem_iff.2 (List.mem_finRange i)) (perm.mem_iff.2 (List.mem_finRange j)) hij with
        ⟨r, hr, hgt⟩ | ⟨r, hr, hgt⟩
      · obtain ⟨r', hr', heq⟩ := tieIJ
        rw [hr] at hr'
        cases Option.some.inj hr'
        exact absurd (heq.symm.trans hgt) (by decide)
      · obtain ⟨r', hr', heq⟩ := tieJI
        rw [hr] at hr'
        cases Option.some.inj hr'
        exact absurd (heq.symm.trans hgt) (by decide)

end Generic

section Production

variable (target : input.LocalizedCIPOccurrence carrierFuel)
  (view : input.LocalizedDependencyView target)
  (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)

theorem localizedOccurrenceRule45OrderPairStrict?_eq_of (left : Fin 4) :
    input.localizedOccurrenceRule45OrderPairStrict? target view frame left =
      pairStrictOf (input.compareLocalizedOccurrenceThroughRule5At? target view frame) left :=
  rfl

theorem localizedOccurrenceRule45OrderCoherent?_eq_of :
    ∀ order, input.localizedOccurrenceRule45OrderCoherent? target view frame order =
      orderCoherentOf (input.compareLocalizedOccurrenceThroughRule5At? target view frame) order
  | [] => rfl
  | left :: rest => by
      simp only [localizedOccurrenceRule45OrderCoherent?, orderCoherentOf,
        localizedOccurrenceRule45OrderPairStrict?_eq_of,
        localizedOccurrenceRule45OrderCoherent?_eq_of rest]

/-- The production safe order is the generic one at the production pairwise comparison. -/
theorem safeLocalizedOccurrenceRule45TrackedOrder?_eq_of :
    input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame =
      safeTrackedOrderOf (input.compareLocalizedOccurrenceThroughRule5At? target view frame) := by
  unfold safeLocalizedOccurrenceRule45TrackedOrder? localizedOccurrenceRule45TrackedOrder?
    safeTrackedOrderOf
  cases sortFourLocalizedLigandsTracked
      (input.compareLocalizedOccurrenceThroughRule5At? target view frame) with
  | none => rfl
  | some tracked =>
      simp only [Option.bind_eq_bind, Option.bind_some,
        input.localizedOccurrenceRule45OrderCoherent?_eq_of target view frame]

/-- The production pairwise comparison of two built slot keys. -/
theorem compareLocalizedOccurrenceThroughRule5At?_of_built {left right : Fin 4}
    {leftKey rightKey : input.LocalizedRerootCompoundRule45Key}
    (hl : input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt left) = some leftKey)
    (hr : input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt right) = some rightKey) :
    input.compareLocalizedOccurrenceThroughRule5At? target view frame left right =
      some (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey)) := by
  unfold compareLocalizedOccurrenceThroughRule5At?
  simp only [hl, hr, Option.bind_eq_bind, Option.bind_some]

end Production

/-! ## The ordered bare Rule-4/5 evaluator -/

section Ordered

variable (target : input.LocalizedCIPOccurrence carrierFuel)
  (view : input.LocalizedDependencyView target)

/-- The ordered pairwise comparison of two frame slots: both compound keys built by the ordered
builder at the production budget. -/
def compareLocalizedOccurrenceThroughRule5OrderedAt?
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) (left right : Fin 4) :
    Option ConstitutionalDescriptorHierarchyComparison := do
  let fuel := localizedOccurrenceRerootEvaluationFuel carrierFuel
  let leftKey ← input.buildLocalizedRerootCompoundRule45KeyOrdered? target view fuel
    (frame.cursorAt left)
  let rightKey ← input.buildLocalizedRerootCompoundRule45KeyOrdered? target view fuel
    (frame.cursorAt right)
  some (localizedOccurrenceRule45ComparisonRecord
    (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey))

theorem compareLocalizedOccurrenceThroughRule5OrderedAt?_of_built
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) {left right : Fin 4}
    {leftKey rightKey : input.LocalizedRerootCompoundRule45Key}
    (hl : input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt left) = some leftKey)
    (hr : input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt right) = some rightKey) :
    input.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame left right =
      some (localizedOccurrenceRule45ComparisonRecord
        (input.compareLocalizedRerootCompoundThroughRule5 (input.outcomeOrdered45 leftKey)
          (input.outcomeOrdered45 rightKey))) := by
  unfold compareLocalizedOccurrenceThroughRule5OrderedAt?
  simp only [buildLocalizedRerootCompoundRule45KeyOrdered?_eq_map, hl, hr, Option.map_some,
    Option.bind_eq_bind, Option.bind_some]

/-- The ordered comparison fails exactly when the production comparison fails. -/
theorem compareLocalizedOccurrenceThroughRule5OrderedAt?_eq_none_iff
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) (left right : Fin 4) :
    input.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame left right = none ↔
      input.compareLocalizedOccurrenceThroughRule5At? target view frame left right = none := by
  unfold compareLocalizedOccurrenceThroughRule5OrderedAt? compareLocalizedOccurrenceThroughRule5At?
  simp only [buildLocalizedRerootCompoundRule45KeyOrdered?_eq_map]
  cases input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt left) <;>
    cases input.buildLocalizedRerootCompoundRule45Key? target view
      (localizedOccurrenceRerootEvaluationFuel carrierFuel) (frame.cursorAt right) <;>
    simp

/-- The ordered safe tracked order. -/
def safeLocalizedOccurrenceRule45TrackedOrderOrdered?
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel) :
    Option TrackedLocalizedLigandOrder :=
  safeTrackedOrderOf (input.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame)

/-- The ordered spatial evidence: production centre, frame and coordinates, ordered order. -/
def localizedOccurrenceRule45SpatialEvidenceOrdered? :
    Option (input.LocalizedOccurrenceRule45SpatialEvidence carrierFuel) := do
  let center ← input.localizedOccurrenceDescriptorCenter? target
  let frame ← input.localizedOccurrenceFourLigandFrame? target
  let tracked ← input.safeLocalizedOccurrenceRule45TrackedOrderOrdered? target view frame
  let points ← tracked.highestFirst.mapM fun index =>
    input.localizedRerootCursorSpatialPoint? (frame.cursorAt index)
  some { center := center, frame := frame, tracked := tracked, points := points }

/-- The ordered bare Rule-4/5 descriptor. -/
def localizedOccurrenceRule45DescriptorOrdered? : Option LocalizedAuxiliaryLabel := do
  let evidence ← input.localizedOccurrenceRule45SpatialEvidenceOrdered? target view
  let raw ← descriptorOfPriorityOrderedPoints? evidence.points
  some (classifyTetrahedralRSPseudo raw evidence.tracked.pseudoComparisons)

/-- **Agreement.**  Whenever every pair of frame slots compares identically under the ordered and
the production keys, the two descriptors agree. -/
theorem localizedOccurrenceRule45DescriptorOrdered?_eq_of_compareAt_eq
    (h : ∀ frame, input.localizedOccurrenceFourLigandFrame? target = some frame →
      input.compareLocalizedOccurrenceThroughRule5OrderedAt? target view frame =
        input.compareLocalizedOccurrenceThroughRule5At? target view frame) :
    input.localizedOccurrenceRule45DescriptorOrdered? target view =
      input.localizedOccurrenceRule45Descriptor? target view := by
  unfold localizedOccurrenceRule45DescriptorOrdered? localizedOccurrenceRule45Descriptor?
    localizedOccurrenceRule45SpatialEvidenceOrdered? localizedOccurrenceRule45SpatialEvidence?
  cases input.localizedOccurrenceDescriptorCenter? target with
  | none => rfl
  | some center =>
      cases hframe : input.localizedOccurrenceFourLigandFrame? target with
      | none => rfl
      | some frame =>
          have safeEq : input.safeLocalizedOccurrenceRule45TrackedOrderOrdered? target view frame =
              input.safeLocalizedOccurrenceRule45TrackedOrder? target view frame := by
            unfold safeLocalizedOccurrenceRule45TrackedOrderOrdered?
            rw [h frame hframe, input.safeLocalizedOccurrenceRule45TrackedOrder?_eq_of]
          simp only [Option.bind_eq_bind, Option.bind_some, safeEq]

/-- **Refusal.**  If the ordered safe order refuses at the frame the descriptor computes, the
ordered descriptor refuses. -/
theorem localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_safe_eq_none
    (frame : input.LocalizedOccurrenceFourLigandFrame carrierFuel)
    (frameComputed : input.localizedOccurrenceFourLigandFrame? target = some frame)
    (safeNone : input.safeLocalizedOccurrenceRule45TrackedOrderOrdered? target view frame = none) :
    input.localizedOccurrenceRule45DescriptorOrdered? target view = none := by
  unfold localizedOccurrenceRule45DescriptorOrdered? localizedOccurrenceRule45SpatialEvidenceOrdered?
  cases input.localizedOccurrenceDescriptorCenter? target with
  | none => rfl
  | some center => simp [frameComputed, safeNone]

/-- Without a descriptor centre both descriptors refuse. -/
theorem localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_center_none
    (hcenter : input.localizedOccurrenceDescriptorCenter? target = none) :
    input.localizedOccurrenceRule45DescriptorOrdered? target view = none := by
  unfold localizedOccurrenceRule45DescriptorOrdered? localizedOccurrenceRule45SpatialEvidenceOrdered?
  simp [hcenter]

theorem localizedOccurrenceRule45Descriptor?_eq_none_of_center_none
    (hcenter : input.localizedOccurrenceDescriptorCenter? target = none) :
    input.localizedOccurrenceRule45Descriptor? target view = none := by
  unfold localizedOccurrenceRule45Descriptor? localizedOccurrenceRule45SpatialEvidence?
  simp [hcenter]

end Ordered

/-! ## Pairs decided at Rule 4a -/

/-- A pair decided at Rule 4a compares identically after ordering the alternatives. -/
theorem compareThroughRule5_outcomeOrdered45_of_rule4a_ne
    (left right : input.LocalizedRerootCompoundRule45Key)
    (decisive : input.compareLocalizedRerootCumulativeRule45Keys
      left.prior.rule4aKey right.prior.rule4aKey ≠ Ordering.eq) :
    input.compareLocalizedRerootCompoundThroughRule5 (input.outcomeOrdered45 left)
        (input.outcomeOrdered45 right) =
      input.compareLocalizedRerootCompoundThroughRule5 left right := by
  have hleft := input.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
    (input.outcomeOrdered45 left).prior (input.outcomeOrdered45 right).prior decisive
  have hright := input.compareLocalizedRerootCompoundRule4bcKeys_eq_rule4a_of_ne
    left.prior right.prior decisive
  unfold compareLocalizedRerootCompoundThroughRule5
  simp only [hleft, hright]
  split_ifs with h1 h2 h2
  · rfl
  · exact absurd (bne_iff_ne.2 decisive) h2
  · exact absurd (bne_iff_ne.2 decisive) h1
  · exact absurd (bne_iff_ne.2 decisive) h1

/-- A constitutional decision is a Rule-4a decision of the cumulative keys. -/
theorem compareLocalizedRerootCumulativeRule45Keys_ne_of_constitutional_ne
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (notTie : OfficialRuleMajorKey.compare left.constitutional right.constitutional ≠ Ordering.eq) :
    input.compareLocalizedRerootCumulativeRule45Keys left right ≠ Ordering.eq := by
  unfold compareLocalizedRerootCumulativeRule45Keys compareLex Ordering.byKey
  cases h : OfficialRuleMajorKey.compare left.constitutional right.constitutional with
  | lt => simp [Ordering.then]
  | gt => simp [Ordering.then]
  | eq => exact absurd h notTie

end
end CertifiedLocalizedCIPInput
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyOrdered?_eq_map
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5Readings?_rankReadings
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyOrdered?_eq_map
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule45KeyOrdered?_sound
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.safeTrackedOrderOf_eq_none_of_tie
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.safeLocalizedOccurrenceRule45TrackedOrder?_eq_of
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedOccurrenceThroughRule5OrderedAt?_of_built
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45DescriptorOrdered?_eq_of_compareAt_eq
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedOccurrenceRule45DescriptorOrdered?_eq_none_of_safe_eq_none
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareThroughRule5_outcomeOrdered45_of_rule4a_ne
