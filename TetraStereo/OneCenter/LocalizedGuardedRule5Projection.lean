import TetraStereo.OneCenter.LocalizedChiralStageExtension
import TetraStereo.OneCenter.LocalizedFullCompoundTieLabelDecoding
import TetraStereo.OneCenter.Rule4c5SparseSourceDecisionFidelity
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

/-!
# Guarded Rule-5 last-component projection

The Rule-5 stage refines only ties accumulated through Rules 4a--4c, and its own contribution to a
cumulative node vector is the final component.  For a *two-component* Rule-4b observation the
Rule-5 extension is completely determined by the leading two components, so the whole extended
descriptor comparison collapses to the comparison of the final components.  This module proves
that collapse in three layers:

1. a generic algebra lemma over an arbitrary common base table `D` and arbitrary own Rule-4b
   references, assuming only that every base entry is an actual two-component Rule-4b image;
2. a reusable `WithRead` actual-builder theorem: two actual Rule-4b builds (independent readers,
   fuels and references), each reader none/chiral on its reachable closure, and an exact Rule-4b
   descriptor tie, produce the last-component identity for the two actual stage-5 builds;
3. the compound call-site endpoint over the *same* actual successfully built compound keys: after
   an exact compound Rules-4b/4c tie, and assuming each side's actual P-92 reference population is
   empty or a singleton, the actual Rule-5 reading-list comparison is exactly the lexicographic
   comparison of the last-component projections.

The projection reads `vector.reverse.headD 0`, so it covers the width-3 no-reference vector (last
index 2) and the width-4 referenced vector (last index 3) with one total definition; no index is
hard-coded.  The two-sided reference populations are classified by the actual reference-count
priority recorded by the builder and the exact tie of the compound Rules-4b/4c comparator, so the
mixed empty/singleton pair is excluded by derivation rather than by hypothesis.

Everything here is a statement about the executable builders; nothing assumes a reference value, a
singleton reading witness, matching reading lists, prefix tables, a mirror relation, or the desired
output.  The Rule-5 senior/junior decision is a comparison result, not a claim that the substrate
is pseudoasymmetric.
-/

namespace CertifiedLocalizedCIPInput

/-! ## The last-component projection -/

/-- The final component of an actual cumulative priority vector.  All cumulative vectors of the
stages handled here are nonempty; the total `headD 0` reading keeps the projection total without
fixing any vector width. -/
def localizedLastPriorityComponent (vector : List Nat) : Nat :=
  vector.reverse.headD 0

/-- Project one addressed cumulative descriptor entry to its final component.  The position
address is untouched. -/
def lastProjectionEntry (entry : OfficialSparseEntry (List Nat)) : OfficialSparseEntry Nat :=
  (entry.1, localizedLastPriorityComponent entry.2)

/-- Project one cumulative descriptor sphere to final components. -/
def lastProjectionLayer (layer : List (OfficialSparseEntry (List Nat))) :
    List (OfficialSparseEntry Nat) :=
  layer.map lastProjectionEntry

/-- Project a whole cumulative descriptor to its last-component table.  Every sphere and every
address is preserved; only the observation value is replaced by the final component of its node
vector. -/
def lastProjection (layers : List (List (OfficialSparseEntry (List Nat)))) :
    List (List (OfficialSparseEntry Nat)) :=
  layers.map lastProjectionLayer

@[simp] theorem lastProjectionEntry_fst (entry : OfficialSparseEntry (List Nat)) :
    (lastProjectionEntry entry).1 = entry.1 := rfl

@[simp] theorem lastProjectionEntry_snd (entry : OfficialSparseEntry (List Nat)) :
    (lastProjectionEntry entry).2 = localizedLastPriorityComponent entry.2 := rfl

@[simp] theorem lastProjectionLayer_nil : lastProjectionLayer [] = [] := rfl

@[simp] theorem lastProjectionLayer_cons (entry : OfficialSparseEntry (List Nat))
    (layer : List (OfficialSparseEntry (List Nat))) :
    lastProjectionLayer (entry :: layer) =
      lastProjectionEntry entry :: lastProjectionLayer layer := rfl

@[simp] theorem lastProjection_nil : lastProjection [] = [] := rfl

@[simp] theorem lastProjection_cons (layer : List (OfficialSparseEntry (List Nat)))
    (layers : List (List (OfficialSparseEntry (List Nat)))) :
    lastProjection (layer :: layers) =
      lastProjectionLayer layer :: lastProjection layers := rfl

/-- The last component of a vector ending in an explicit singleton. -/
@[simp] theorem localizedLastPriorityComponent_append_singleton (stem : List Nat) (value : Nat) :
    localizedLastPriorityComponent (stem ++ [value]) = value := by
  simp [localizedLastPriorityComponent]

/-- The projection of an extended descriptor in explicit `map` form.  This is the normal form used
by the generic algebra lemmas below. -/
theorem lastProjection_extendLocalizedPriorityLayers (extend : List Nat → List Nat)
    (base : List (List (OfficialSparseEntry (List Nat)))) :
    lastProjection (extendLocalizedPriorityLayers extend base) =
      base.map (fun layer =>
        (layer.map (extendLocalizedPriorityEntry extend)).map lastProjectionEntry) := by
  simp [lastProjection, lastProjectionLayer, extendLocalizedPriorityLayers,
    extendLocalizedPriorityLayer, List.map_map]

/-- An extended descriptor in explicit `map` form. -/
theorem extendLocalizedPriorityLayers_eq_map (extend : List Nat → List Nat)
    (base : List (List (OfficialSparseEntry (List Nat)))) :
    extendLocalizedPriorityLayers extend base =
      base.map (fun layer => layer.map (extendLocalizedPriorityEntry extend)) := by
  simp [extendLocalizedPriorityLayers, extendLocalizedPriorityLayer]

/-! ## Generic two-component Rule-5 extension algebra -/

/-- A cumulative node vector produced by the Rule-4b stage: exactly two components. -/
abbrev LocalizedTwoComponentPriorityVector (vector : List Nat) : Prop :=
  ∃ kind like : Nat, vector = [kind, like]

/-- The Rule-5 senior/junior bit of a two-component Rule-4b vector under one common reference.
This is the literal seniority subterm of `extendLocalizedRule4bPriorityToRule5`. -/
def localizedRule5SeniorityBit (rule4bReference rule5Reference : RS)
    (kind like : Nat) : Nat :=
  if kind == 2 then
    if (if like == 1 then rule4bReference else RS.swap rule4bReference) == rule5Reference
      then 1 else 0
  else 0

/-- On the actual Rule-4b two-component vectors the Rule-5 extension appends the Rule-4c zero and
exactly the Rule-5 seniority bit. -/
theorem extendLocalizedRule4bPriorityToRule5_twoComponent
    (rule4bReference rule5Reference : RS) (kind like : Nat) :
    extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference [kind, like] =
      [kind, like, 0] ++
        [localizedRule5SeniorityBit rule4bReference rule5Reference kind like] := rfl

/-- A reflexive comparator makes every list comparison with itself a tie. -/
theorem compareLex_self_eq_of_refl {α : Type*} (cmp : α → α → Ordering)
    (refl : ∀ value, cmp value value = Ordering.eq) :
    ∀ values : List α, List.compareLex cmp values values = Ordering.eq
  | [] => rfl
  | value :: values => by
      simp [List.compareLex_cons_cons, refl value,
        compareLex_self_eq_of_refl cmp refl values]

/-- Two addressed entries at the same address compare exactly by their observations. -/
theorem compareSparseEntry_sameAddress {α : Type*} (cmp : α → α → Ordering)
    (address : List Nat) (left right : α) :
    OfficialRuleMajorKey.compareSparseEntry cmp (address, left) (address, right) =
      cmp left right := by
  have addressTie :
      List.compareLex OfficialRuleMajorKey.compareNat address address = Ordering.eq :=
    compareLex_self_eq_of_refl OfficialRuleMajorKey.compareNat
      (fun number => (localizedCompareNat_eq_iff number number).mpr rfl) address
  have step := localizedCompareLex_eq_right_of_eq
    (cmp₁ := Ordering.byKey Prod.fst (flip (List.compareLex OfficialRuleMajorKey.compareNat)))
    (cmp₂ := Ordering.byKey Prod.snd cmp)
    (a := (address, left)) (b := (address, right)) addressTie
  simpa [OfficialRuleMajorKey.compareSparseEntry, Ordering.byKey] using step

/-- Entry-level identity: two entries carrying actual two-component Rule-4b vectors, extended to
Rule 5 under independent own Rule-4b references and a common probe, compare exactly as their final
components compare. -/
theorem compareSparseEntry_extendLocalizedRule5_lastProjection
    (leftReference rightReference probe : RS) (address : List Nat) (kind like : Nat) :
    OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority
        (extendLocalizedPriorityEntry
          (extendLocalizedRule4bPriorityToRule5 leftReference probe) (address, [kind, like]))
        (extendLocalizedPriorityEntry
          (extendLocalizedRule4bPriorityToRule5 rightReference probe) (address, [kind, like])) =
      OfficialRuleMajorKey.compareSparseEntry OfficialRuleMajorKey.compareNat
        (lastProjectionEntry (extendLocalizedPriorityEntry
          (extendLocalizedRule4bPriorityToRule5 leftReference probe) (address, [kind, like])))
        (lastProjectionEntry (extendLocalizedPriorityEntry
          (extendLocalizedRule4bPriorityToRule5 rightReference probe) (address, [kind, like]))) := by
  have leftLast :
      localizedLastPriorityComponent
          (extendLocalizedRule4bPriorityToRule5 leftReference probe [kind, like]) =
        localizedRule5SeniorityBit leftReference probe kind like := by
    rw [extendLocalizedRule4bPriorityToRule5_twoComponent]
    exact localizedLastPriorityComponent_append_singleton [kind, like, 0] _
  have rightLast :
      localizedLastPriorityComponent
          (extendLocalizedRule4bPriorityToRule5 rightReference probe [kind, like]) =
        localizedRule5SeniorityBit rightReference probe kind like := by
    rw [extendLocalizedRule4bPriorityToRule5_twoComponent]
    exact localizedLastPriorityComponent_append_singleton [kind, like, 0] _
  simp only [extendLocalizedPriorityEntry, lastProjectionEntry, leftLast, rightLast,
    compareSparseEntry_sameAddress, compareLocalizedCumulativeRule45Priority,
    extendLocalizedRule4bPriorityToRule5_twoComponent,
    localizedLastPriorityComponent_append_singleton,
    Rule4c5SourceDecision.compareLex_compareNat_append_singleton]

/-- Sphere-level identity: over a sphere of actual two-component Rule-4b observations, the
Rule-5-extended cumulative comparison is exactly the last-component comparison. -/
theorem compareSparseLayer_extendLocalizedRule5_lastProjection
    (leftReference rightReference probe : RS) :
    ∀ (base : List (OfficialSparseEntry (List Nat))),
      (∀ entry ∈ base, LocalizedTwoComponentPriorityVector entry.2) →
      OfficialRuleMajorKey.compareSparseLayer compareLocalizedCumulativeRule45Priority
          (base.map (extendLocalizedPriorityEntry
            (extendLocalizedRule4bPriorityToRule5 leftReference probe)))
          (base.map (extendLocalizedPriorityEntry
            (extendLocalizedRule4bPriorityToRule5 rightReference probe))) =
        OfficialRuleMajorKey.compareSparseLayer OfficialRuleMajorKey.compareNat
          ((base.map (extendLocalizedPriorityEntry
            (extendLocalizedRule4bPriorityToRule5 leftReference probe))).map lastProjectionEntry)
          ((base.map (extendLocalizedPriorityEntry
            (extendLocalizedRule4bPriorityToRule5 rightReference probe))).map lastProjectionEntry)
  | [], _ => rfl
  | head :: tail, image => by
      rcases head with ⟨address, vector⟩
      obtain ⟨kind, like, shape⟩ := image (address, vector) (by simp)
      subst shape
      unfold OfficialRuleMajorKey.compareSparseLayer
      simp only [List.map_cons, List.compareLex_cons_cons]
      rw [compareSparseEntry_extendLocalizedRule5_lastProjection leftReference rightReference probe
        address kind like]
      have tailStep := compareSparseLayer_extendLocalizedRule5_lastProjection leftReference
        rightReference probe tail (fun entry present => image entry (by simp [present]))
      unfold OfficialRuleMajorKey.compareSparseLayer at tailStep
      rw [tailStep]

/-- Descriptor-level identity: over a common base descriptor whose every entry is an actual
two-component Rule-4b observation, the Rule-5-extended cumulative comparison is exactly the
last-component comparison. -/
theorem compareSparseLayers_extendLocalizedRule5_lastProjection
    (leftReference rightReference probe : RS) :
    ∀ (base : List (List (OfficialSparseEntry (List Nat)))),
      (∀ layer ∈ base, ∀ entry ∈ layer, LocalizedTwoComponentPriorityVector entry.2) →
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          (base.map (fun layer => layer.map (extendLocalizedPriorityEntry
            (extendLocalizedRule4bPriorityToRule5 leftReference probe))))
          (base.map (fun layer => layer.map (extendLocalizedPriorityEntry
            (extendLocalizedRule4bPriorityToRule5 rightReference probe)))) =
        OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
          (base.map (fun layer => (layer.map (extendLocalizedPriorityEntry
            (extendLocalizedRule4bPriorityToRule5 leftReference probe))).map lastProjectionEntry))
          (base.map (fun layer => (layer.map (extendLocalizedPriorityEntry
            (extendLocalizedRule4bPriorityToRule5 rightReference probe))).map lastProjectionEntry))
  | [], _ => rfl
  | head :: tail, image => by
      unfold OfficialRuleMajorKey.compareSparseLayers
      simp only [List.map_cons, List.compareLex_cons_cons]
      rw [compareSparseLayer_extendLocalizedRule5_lastProjection leftReference rightReference probe
        head (fun entry present => image head (by simp) entry present)]
      have tailStep := compareSparseLayers_extendLocalizedRule5_lastProjection leftReference
        rightReference probe tail
        (fun layer present entry entryPresent => image layer (by simp [present]) entry entryPresent)
      unfold OfficialRuleMajorKey.compareSparseLayers at tailStep
      rw [tailStep]

/-- The cumulative priority comparator ties a table with itself. -/
theorem compareSparseLayers_cmpPriority_self
    (layers : List (List (OfficialSparseEntry (List Nat)))) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        layers layers = Ordering.eq :=
  (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff layers layers).mpr rfl

/-- The last-component comparator ties a table with itself. -/
theorem compareSparseLayers_compareNat_self
    (layers : List (List (OfficialSparseEntry Nat))) :
    OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        layers layers = Ordering.eq :=
  (compareSparseLayers_compareNat_eq_iff layers layers).mpr rfl

/-- No-reference identity: when both sides use the same no-reference Rule-5 extension on one
common base, both the extended cumulative comparison and the last-component comparison are ties. -/
theorem compareSparseLayers_extendRule5NoRule4bReference_lastProjection
    (probe : RS) (base : List (List (OfficialSparseEntry (List Nat)))) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        (extendLocalizedPriorityLayers
          (extendLocalizedRule4aPriorityToRule5NoRule4bReference probe) base)
        (extendLocalizedPriorityLayers
          (extendLocalizedRule4aPriorityToRule5NoRule4bReference probe) base) =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (lastProjection (extendLocalizedPriorityLayers
          (extendLocalizedRule4aPriorityToRule5NoRule4bReference probe) base))
        (lastProjection (extendLocalizedPriorityLayers
          (extendLocalizedRule4aPriorityToRule5NoRule4bReference probe) base)) := by
  rw [compareSparseLayers_cmpPriority_self, compareSparseLayers_compareNat_self]

/-! ## Actual `WithRead` builder endpoints -/

/-- An admitted Rule-4b observation has exactly a two-component cumulative vector. -/
theorem localizedTwoComponentPriorityVector_of_rule4b_image
    (reference : RS) {vector : List Nat}
    (image : LocalizedStagePriorityImage (.rule4b reference) LocalizedNoPseudoLabel vector) :
    LocalizedTwoComponentPriorityVector vector := by
  obtain ⟨label, admitted, rfl⟩ := image
  cases label with
  | none => exact ⟨0, 0, rfl⟩
  | some label =>
      cases label with
      | pseudoasymmetric descriptor => exact admitted.elim
      | chiral descriptor =>
          exact ⟨2, if descriptor == reference then 1 else 0, rfl⟩

/-- The descriptor of a successful actual Rule-4b build consists of two-component vectors. -/
theorem localizedStageDescriptorImage_rule4b_twoComponent
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (reference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (admittedReads : ∀ cursor,
      Relation.ReflTransGen (E input) start cursor → LocalizedNoPseudoLabel (read cursor))
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b reference) read fuel cursor = some key) :
    ∀ layer ∈ key.descriptor, ∀ entry ∈ layer,
      LocalizedTwoComponentPriorityVector entry.2 :=
  fun layer layerPresent entry entryPresent =>
    localizedTwoComponentPriorityVector_of_rule4b_image reference
      (buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptorImage input
        (.rule4b reference) LocalizedNoPseudoLabel read start admittedReads fuel cursor reachable
        key computed layer layerPresent entry entryPresent)

/-- A successful actual stage-5 build extends the actual Rule-4b descriptor by the explicit
two-component Rule-5 transformation.  The stage-5 output is identified by `Option.some`
injectivity from the actual builder-success theorem. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (rule4bReference rule5Reference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (admittedReads : ∀ cursor,
      Relation.ReflTransGen (E input) start cursor → LocalizedNoPseudoLabel (read cursor))
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b rule4bReference) read fuel cursor = some key)
    (rule5Key : input.LocalizedRerootCumulativeRule45Key)
    (rule5Computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule5 rule4bReference rule5Reference) read fuel cursor = some rule5Key) :
    rule5Key.descriptor =
      extendLocalizedPriorityLayers
        (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference) key.descriptor := by
  have extension := buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_success input
    rule4bReference rule5Reference read start admittedReads fuel cursor reachable key computed
  rw [extension] at rule5Computed
  injection rule5Computed with same
  rw [← same]
  rfl

/-- A successful actual no-reference stage-5 build extends the actual Rule-4a descriptor by the
explicit no-reference Rule-5 transformation. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5NoRule4bReference_descriptor
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (rule5Reference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (noReads : ∀ cursor, Relation.ReflTransGen (E input) start cursor → read cursor = none)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read fuel cursor = some key)
    (rule5Key : input.LocalizedRerootCumulativeRule45Key)
    (rule5Computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule5NoRule4bReference rule5Reference) read fuel cursor = some rule5Key) :
    rule5Key.descriptor =
      extendLocalizedPriorityLayers
        (extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference) key.descriptor := by
  have extension :=
    buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5NoRule4bReference_success input
      rule5Reference read start noReads fuel cursor reachable key computed
  rw [extension] at rule5Computed
  injection rule5Computed with same
  rw [← same]
  rfl

/-- **Reusable actual-builder last-component identity (own reference).**  Two actual Rule-4b builds
at independent cursors, readers, fuels and own Rule-4b references, each reader none/chiral on its
reachable closure, together with an exact Rule-4b descriptor tie, make the two actual stage-5
descriptor comparisons coincide with the last-component comparison under any common probe. -/
theorem compareSparseLayers_actualRule5_lastProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (leftReference rightReference probe : RS)
    (leftRead rightRead :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (leftStart rightStart : input.LocalizedRerootCursor carrierFuel)
    {leftFuel rightFuel : Nat}
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftReachable : Relation.ReflTransGen (E input) leftStart leftCursor)
    (rightReachable : Relation.ReflTransGen (E input) rightStart rightCursor)
    (leftAdmitted : ∀ cursor,
      Relation.ReflTransGen (E input) leftStart cursor → LocalizedNoPseudoLabel (leftRead cursor))
    (rightAdmitted : ∀ cursor,
      Relation.ReflTransGen (E input) rightStart cursor → LocalizedNoPseudoLabel (rightRead cursor))
    (leftKey rightKey : input.LocalizedRerootCumulativeRule45Key)
    (leftComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b leftReference) leftRead leftFuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b rightReference) rightRead rightFuel rightCursor = some rightKey)
    (baseTie : OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority leftKey.descriptor rightKey.descriptor =
        Ordering.eq)
    (leftRule5 rightRule5 : input.LocalizedRerootCumulativeRule45Key)
    (leftRule5Computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule5 leftReference probe) leftRead leftFuel leftCursor = some leftRule5)
    (rightRule5Computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule5 rightReference probe) rightRead rightFuel rightCursor = some rightRule5) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        leftRule5.descriptor rightRule5.descriptor =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (lastProjection leftRule5.descriptor) (lastProjection rightRule5.descriptor) := by
  have leftDescriptor := buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_descriptor input
    leftReference probe leftRead leftStart leftAdmitted leftFuel leftCursor leftReachable
    leftKey leftComputed leftRule5 leftRule5Computed
  have rightDescriptor := buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_descriptor input
    rightReference probe rightRead rightStart rightAdmitted rightFuel rightCursor rightReachable
    rightKey rightComputed rightRule5 rightRule5Computed
  rw [leftDescriptor, rightDescriptor]
  have baseEq : leftKey.descriptor = rightKey.descriptor :=
    (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff
      leftKey.descriptor rightKey.descriptor).mp baseTie
  rw [baseEq]
  have rightImage := localizedStageDescriptorImage_rule4b_twoComponent input rightReference
    rightRead rightStart rightAdmitted rightFuel rightCursor rightReachable rightKey rightComputed
  have step := compareSparseLayers_extendLocalizedRule5_lastProjection leftReference
    rightReference probe rightKey.descriptor rightImage
  rw [lastProjection_extendLocalizedPriorityLayers, lastProjection_extendLocalizedPriorityLayers]
  simpa only [extendLocalizedPriorityLayers, extendLocalizedPriorityLayer, List.map_map] using step

/-- **Reusable actual-builder last-component identity (no reference).**  Two actual Rule-4a builds
whose readers are everywhere `none` on their reachable closures, together with an exact Rule-4a
descriptor tie, make the two actual no-reference stage-5 descriptor comparisons coincide with the
last-component comparison under any common probe. -/
theorem compareSparseLayers_actualRule5NoRule4bReference_lastProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (probe : RS)
    (leftRead rightRead :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (leftStart rightStart : input.LocalizedRerootCursor carrierFuel)
    {leftFuel rightFuel : Nat}
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftReachable : Relation.ReflTransGen (E input) leftStart leftCursor)
    (rightReachable : Relation.ReflTransGen (E input) rightStart rightCursor)
    (leftNoReads : ∀ cursor,
      Relation.ReflTransGen (E input) leftStart cursor → leftRead cursor = none)
    (rightNoReads : ∀ cursor,
      Relation.ReflTransGen (E input) rightStart cursor → rightRead cursor = none)
    (leftKey rightKey : input.LocalizedRerootCumulativeRule45Key)
    (leftComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a leftRead leftFuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a rightRead rightFuel rightCursor = some rightKey)
    (baseTie : OfficialRuleMajorKey.compareSparseLayers
      compareLocalizedCumulativeRule45Priority leftKey.descriptor rightKey.descriptor =
        Ordering.eq)
    (leftRule5 rightRule5 : input.LocalizedRerootCumulativeRule45Key)
    (leftRule5Computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule5NoRule4bReference probe) leftRead leftFuel leftCursor = some leftRule5)
    (rightRule5Computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule5NoRule4bReference probe) rightRead rightFuel rightCursor = some rightRule5) :
    OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
        leftRule5.descriptor rightRule5.descriptor =
      OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat
        (lastProjection leftRule5.descriptor) (lastProjection rightRule5.descriptor) := by
  have leftDescriptor :=
    buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5NoRule4bReference_descriptor input
      probe leftRead leftStart leftNoReads leftFuel leftCursor leftReachable
      leftKey leftComputed leftRule5 leftRule5Computed
  have rightDescriptor :=
    buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5NoRule4bReference_descriptor input
      probe rightRead rightStart rightNoReads rightFuel rightCursor rightReachable
      rightKey rightComputed rightRule5 rightRule5Computed
  rw [leftDescriptor, rightDescriptor]
  have baseEq : leftKey.descriptor = rightKey.descriptor :=
    (compareSparseLayers_compareLocalizedCumulativeRule45Priority_eq_iff
      leftKey.descriptor rightKey.descriptor).mp baseTie
  rw [baseEq]
  exact compareSparseLayers_extendRule5NoRule4bReference_lastProjection probe rightKey.descriptor

/-! ## Component extraction for the actual compound builders -/

/-- A successful actual Rule-4b/4c reading records exactly the alternative it was built for. -/
theorem buildLocalizedRerootRule4bcReadingWithRead?_reference
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS)
    (reading : input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReadingWithRead?
      read fuel cursor reference = some reading) :
    reading.reference? = reference := by
  cases reference with
  | none =>
      unfold buildLocalizedRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              .rule4cNoReference read fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              have readingEq : reading =
                  { reference? := none, rule4bKey := rule4bKey, rule4cKey := rule4cKey } := by
                simpa [rule4bComputed, rule4cComputed] using computed.symm
              rw [readingEq]
  | some reference =>
      unfold buildLocalizedRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (.rule4b reference) read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule4c reference) read fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              have readingEq : reading =
                  { reference? := some reference, rule4bKey := rule4bKey,
                    rule4cKey := rule4cKey } := by
                simpa [rule4bComputed, rule4cComputed] using computed.symm
              rw [readingEq]

/-- The Rule-4b member of a successful actual Rule-4b/4c reading is exactly the actual cumulative
build at the reference-dependent Rule-4b stage. -/
theorem buildLocalizedRerootRule4bcReadingWithRead?_rule4bKey
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS)
    (reading : input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReadingWithRead?
      read fuel cursor reference = some reading) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        (match reference with
          | none => .rule4a
          | some found => .rule4b found) read fuel cursor =
      some reading.rule4bKey := by
  cases reference with
  | none =>
      unfold buildLocalizedRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          .rule4a read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              .rule4cNoReference read fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              have readingEq : reading =
                  { reference? := none, rule4bKey := rule4bKey, rule4cKey := rule4cKey } := by
                simpa [rule4bComputed, rule4cComputed] using computed.symm
              rw [readingEq]
  | some reference =>
      unfold buildLocalizedRerootRule4bcReadingWithRead? at computed
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (.rule4b reference) read fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule4c reference) read fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              have readingEq : reading =
                  { reference? := some reference, rule4bKey := rule4bKey,
                    rule4cKey := rule4cKey } := by
                simpa [rule4bComputed, rule4cComputed] using computed.symm
              rw [readingEq]

/-- A successful actual Rule-4b/4c reading-list build over one alternative is exactly a singleton
list whose unique reading was actually built from that alternative. -/
theorem buildLocalizedRerootRule4bcReadingsWithRead?_singleton
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (alternative : Option RS)
    (readings : List input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReadingsWithRead?
      read fuel cursor [alternative] = some readings) :
    ∃ reading : input.LocalizedRerootRule4bcReading,
      readings = [reading] ∧
        input.buildLocalizedRerootRule4bcReadingWithRead?
          read fuel cursor alternative = some reading := by
  unfold buildLocalizedRerootRule4bcReadingsWithRead? at computed
  cases headComputed : input.buildLocalizedRerootRule4bcReadingWithRead?
      read fuel cursor alternative with
  | none => simp [headComputed] at computed
  | some head =>
      simp only [headComputed, buildLocalizedRerootRule4bcReadingsWithRead?] at computed
      have readingsEq : readings = [head] := by
        simpa using computed.symm
      exact ⟨head, readingsEq, rfl⟩

/-- A successful actual Rule-5 reading-list build over one prior alternative is exactly a
singleton list whose unique reading was actually built from that prior. -/
theorem buildLocalizedRerootRule5ReadingsWithRead?_singleton
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (prior : input.LocalizedRerootRule4bcReading)
    (readings : List input.LocalizedRerootRule5Reading)
    (computed : input.buildLocalizedRerootRule5ReadingsWithRead?
      read fuel cursor [prior] = some readings) :
    ∃ reading : input.LocalizedRerootRule5Reading,
      readings = [reading] ∧
        input.buildLocalizedRerootRule5ReadingWithRead?
          read fuel cursor prior = some reading := by
  unfold buildLocalizedRerootRule5ReadingsWithRead? at computed
  cases headComputed : input.buildLocalizedRerootRule5ReadingWithRead?
      read fuel cursor prior with
  | none => simp [headComputed] at computed
  | some head =>
      simp only [headComputed, buildLocalizedRerootRule5ReadingsWithRead?] at computed
      have readingsEq : readings = [head] := by
        simpa using computed.symm
      exact ⟨head, readingsEq, rfl⟩

/-- The reference-count priority recorded by a successful actual compound Rules-4b/4c build is
exactly the constitutional priority of that key's actual reference population. -/
theorem buildLocalizedRerootCompoundRule4bcKeyWithRead?_referenceCountPriority
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKeyWithRead?
      read fuel cursor = some key) :
    key.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority key.references := by
  unfold buildLocalizedRerootCompoundRule4bcKeyWithRead? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      .rule4a read fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadingsWithRead?
          read fuel cursor
          (localizedRule4bcReferenceAlternatives
            (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)) with
      | none => simp [rule4aComputed, readingsComputed] at computed
      | some readings =>
          have keyEq : key =
              { rule4aKey := rule4aKey
                references :=
                  localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels
                referenceCountPriority :=
                  constitutionalRule4bReferenceCountPriority
                    (localizedRule4bReferencesFromRankedLabels rule4aKey.rankedLabels)
                readings := readings } := by
            simpa [rule4aComputed, readingsComputed] using computed.symm
          rw [keyEq]

/-- Under the per-side cardinality bound `≤ 1`, the actual P-92 reference population is either
empty (count priority `0`) or a singleton (count priority `2`). -/
theorem constitutionalRule4bReferenceCountPriority_cases_of_length_le_one
    (references : List RS) (bound : references.length ≤ 1) :
    (references = [] ∧ constitutionalRule4bReferenceCountPriority references = 0) ∨
      (∃ reference : RS, references = [reference] ∧
        constitutionalRule4bReferenceCountPriority references = 2) := by
  cases references with
  | nil => exact Or.inl ⟨rfl, rfl⟩
  | cons reference rest =>
      cases rest with
      | nil => exact Or.inr ⟨reference, rfl, rfl⟩
      | cons second tail =>
          simp only [List.length_cons] at bound
          omega

/-! ## The compound call-site endpoint -/

/-- **Guarded compound Rule-5 last-component projection.**  Over the same actual successfully built
compound through-Rule-5 keys on both sides:

* each side's actual P-92 reference population has cardinality at most one;
* each reader is none/chiral on its own reachable closure;
* on a side whose actual reference population is empty, that reader is everywhere `none` on its
  reachable closure;
* the actual compound Rules-4b/4c keys tie exactly;

then the actual Rule-5 reading-list comparison under any common probe is exactly the lexicographic
comparison of the last-component projections of the two reading lists.

The mixed empty/singleton pair is excluded by derivation: the exact compound tie forces the
recorded reference-count priorities to be equal, and the cardinality bound makes those priorities
exactly `0` on an empty population and exactly `2` on a singleton one.  The two remaining diagonal
cases are the empty/empty (no-reference stages) and singleton/singleton (own-reference stages, with
independent and possibly different own Rule-4b references). -/
theorem compareLocalizedRerootCompoundRule5Readings_eq_lastProjection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (leftRead rightRead :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (leftStart rightStart : input.LocalizedRerootCursor carrierFuel)
    {leftFuel rightFuel : Nat}
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftKey rightKey : input.LocalizedRerootCompoundRule45Key)
    (leftComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      leftRead leftFuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      rightRead rightFuel rightCursor = some rightKey)
    (leftReachable : Relation.ReflTransGen (E input) leftStart leftCursor)
    (rightReachable : Relation.ReflTransGen (E input) rightStart rightCursor)
    (leftAdmitted : ∀ cursor,
      Relation.ReflTransGen (E input) leftStart cursor → LocalizedNoPseudoLabel (leftRead cursor))
    (rightAdmitted : ∀ cursor,
      Relation.ReflTransGen (E input) rightStart cursor → LocalizedNoPseudoLabel (rightRead cursor))
    (leftNoReads : leftKey.prior.references = [] → ∀ cursor,
      Relation.ReflTransGen (E input) leftStart cursor → leftRead cursor = none)
    (rightNoReads : rightKey.prior.references = [] → ∀ cursor,
      Relation.ReflTransGen (E input) rightStart cursor → rightRead cursor = none)
    (leftCardinality : leftKey.prior.references.length ≤ 1)
    (rightCardinality : rightKey.prior.references.length ≤ 1)
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      leftKey.prior rightKey.prior = Ordering.eq)
    (probe : RS) :
    input.compareLocalizedRerootCompoundRule5Readings probe
        leftKey.rule5Readings rightKey.rule5Readings =
      List.compareLex
        (Ordering.byKey
          (lastProjection ∘ input.localizedRerootRule5Descriptor probe)
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
        leftKey.rule5Readings rightKey.rule5Readings := by
  -- Expose every actual sub-build of the two compound keys.
  obtain ⟨leftPriorComputed, leftReadingsComputed⟩ :=
    fullTie_compoundRule45Key_components input leftRead leftFuel leftCursor leftKey leftComputed
  obtain ⟨rightPriorComputed, rightReadingsComputed⟩ :=
    fullTie_compoundRule45Key_components input rightRead rightFuel rightCursor rightKey rightComputed
  obtain ⟨_leftRule4aComputed, leftPriorReadingsComputed⟩ :=
    fullTie_compoundRule4bcKey_components input leftRead leftFuel leftCursor
      leftKey.prior leftPriorComputed
  obtain ⟨_rightRule4aComputed, rightPriorReadingsComputed⟩ :=
    fullTie_compoundRule4bcKey_components input rightRead rightFuel rightCursor
      rightKey.prior rightPriorComputed
  -- Decompose the exact compound Rules-4b/4c tie.
  obtain ⟨_rule4aTie, countTie, rule4bTie, _rule4cTie⟩ :=
    (input.compareLocalizedRerootCompoundRule4bcKeys_eq_eq_iff
      leftKey.prior rightKey.prior).mp priorTie
  have countEq :
      leftKey.prior.referenceCountPriority = rightKey.prior.referenceCountPriority :=
    compare_eq_iff_eq.mp countTie
  have leftCountReadback :=
    buildLocalizedRerootCompoundRule4bcKeyWithRead?_referenceCountPriority input
      leftRead leftFuel leftCursor leftKey.prior leftPriorComputed
  have rightCountReadback :=
    buildLocalizedRerootCompoundRule4bcKeyWithRead?_referenceCountPriority input
      rightRead rightFuel rightCursor rightKey.prior rightPriorComputed
  rw [leftCountReadback, rightCountReadback] at countEq
  -- Classify the two actual reference populations.
  rcases constitutionalRule4bReferenceCountPriority_cases_of_length_le_one
      leftKey.prior.references leftCardinality with
    ⟨leftEmpty, leftCountValue⟩ | ⟨leftReference, leftSingleton, leftCountValue⟩
  · rcases constitutionalRule4bReferenceCountPriority_cases_of_length_le_one
        rightKey.prior.references rightCardinality with
      ⟨rightEmpty, rightCountValue⟩ | ⟨rightReference, rightSingleton, rightCountValue⟩
    · -- Case A: both actual reference populations are empty.
      have leftAlternatives :
          localizedRule4bcReferenceAlternatives leftKey.prior.references = [none] := by
        rw [leftEmpty]
        rfl
      have rightAlternatives :
          localizedRule4bcReferenceAlternatives rightKey.prior.references = [none] := by
        rw [rightEmpty]
        rfl
      rw [leftAlternatives] at leftPriorReadingsComputed
      rw [rightAlternatives] at rightPriorReadingsComputed
      obtain ⟨leftPrior, leftPriorReadingsEq, leftPriorComputed⟩ :=
        buildLocalizedRerootRule4bcReadingsWithRead?_singleton input leftRead leftFuel leftCursor
          none leftKey.prior.readings leftPriorReadingsComputed
      obtain ⟨rightPrior, rightPriorReadingsEq, rightPriorComputed⟩ :=
        buildLocalizedRerootRule4bcReadingsWithRead?_singleton input rightRead rightFuel rightCursor
          none rightKey.prior.readings rightPriorReadingsComputed
      rw [leftPriorReadingsEq] at leftReadingsComputed
      rw [rightPriorReadingsEq] at rightReadingsComputed
      obtain ⟨leftReading, leftReadingsEq, leftReadingComputed⟩ :=
        buildLocalizedRerootRule5ReadingsWithRead?_singleton input leftRead leftFuel leftCursor
          leftPrior leftKey.rule5Readings leftReadingsComputed
      obtain ⟨rightReading, rightReadingsEq, rightReadingComputed⟩ :=
        buildLocalizedRerootRule5ReadingsWithRead?_singleton input rightRead rightFuel rightCursor
          rightPrior rightKey.rule5Readings rightReadingsComputed
      have leftReferenceEq :=
        buildLocalizedRerootRule4bcReadingWithRead?_reference input leftRead leftFuel leftCursor
          none leftPrior leftPriorComputed
      have rightReferenceEq :=
        buildLocalizedRerootRule4bcReadingWithRead?_reference input rightRead rightFuel rightCursor
          none rightPrior rightPriorComputed
      obtain ⟨_leftPriorEq, leftCommonRComputed, leftCommonSComputed⟩ :=
        fullTie_rule5Reading_components input leftRead leftFuel leftCursor
          leftPrior leftReading leftReadingComputed
      obtain ⟨_rightPriorEq, rightCommonRComputed, rightCommonSComputed⟩ :=
        fullTie_rule5Reading_components input rightRead rightFuel rightCursor
          rightPrior rightReading rightReadingComputed
      have leftCommonRNone :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule5NoRule4bReference .R) leftRead leftFuel leftCursor =
            some leftReading.commonR := by
        simpa [leftReferenceEq] using leftCommonRComputed
      have leftCommonSNone :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule5NoRule4bReference .S) leftRead leftFuel leftCursor =
            some leftReading.commonS := by
        simpa [leftReferenceEq] using leftCommonSComputed
      have rightCommonRNone :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule5NoRule4bReference .R) rightRead rightFuel rightCursor =
            some rightReading.commonR := by
        simpa [rightReferenceEq] using rightCommonRComputed
      have rightCommonSNone :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule5NoRule4bReference .S) rightRead rightFuel rightCursor =
            some rightReading.commonS := by
        simpa [rightReferenceEq] using rightCommonSComputed
      have leftBaseComputed :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              .rule4a leftRead leftFuel leftCursor = some leftPrior.rule4bKey :=
        buildLocalizedRerootRule4bcReadingWithRead?_rule4bKey input leftRead leftFuel leftCursor
          none leftPrior leftPriorComputed
      have rightBaseComputed :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              .rule4a rightRead rightFuel rightCursor = some rightPrior.rule4bKey :=
        buildLocalizedRerootRule4bcReadingWithRead?_rule4bKey input rightRead rightFuel rightCursor
          none rightPrior rightPriorComputed
      have baseTie :
          OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
              leftPrior.rule4bKey.descriptor rightPrior.rule4bKey.descriptor =
            Ordering.eq := by
        have tie := rule4bTie
        rw [leftPriorReadingsEq, rightPriorReadingsEq] at tie
        simpa [compareLocalizedRerootCompoundRule4bReadings,
          compareLocalizedRerootRule4bcReadingsByRule4b, Ordering.byKey,
          List.compareLex_cons_cons, List.compareLex_nil_nil] using tie
      have leftAllNone := leftNoReads leftEmpty
      have rightAllNone := rightNoReads rightEmpty
      rw [leftReadingsEq, rightReadingsEq]
      cases probe with
      | R =>
          simp only [compareLocalizedRerootCompoundRule5Readings,
            localizedRerootRule5Descriptor, List.compareLex_cons_cons, List.compareLex_nil_nil,
            Ordering.byKey, Ordering.then_eq]
          exact compareSparseLayers_actualRule5NoRule4bReference_lastProjection input .R
            leftRead rightRead leftStart rightStart
            (leftFuel := leftFuel) (rightFuel := rightFuel) leftCursor rightCursor
            leftReachable rightReachable leftAllNone rightAllNone
            leftPrior.rule4bKey rightPrior.rule4bKey leftBaseComputed rightBaseComputed
            baseTie leftReading.commonR rightReading.commonR
            leftCommonRNone rightCommonRNone
      | S =>
          simp only [compareLocalizedRerootCompoundRule5Readings,
            localizedRerootRule5Descriptor, List.compareLex_cons_cons, List.compareLex_nil_nil,
            Ordering.byKey, Ordering.then_eq]
          exact compareSparseLayers_actualRule5NoRule4bReference_lastProjection input .S
            leftRead rightRead leftStart rightStart
            (leftFuel := leftFuel) (rightFuel := rightFuel) leftCursor rightCursor
            leftReachable rightReachable leftAllNone rightAllNone
            leftPrior.rule4bKey rightPrior.rule4bKey leftBaseComputed rightBaseComputed
            baseTie leftReading.commonS rightReading.commonS
            leftCommonSNone rightCommonSNone
    · -- The left population is empty and the right one is a singleton: the recorded count
      -- priorities `0` and `2` contradict the exact compound tie.
      rw [leftCountValue, rightCountValue] at countEq
      omega
  · rcases constitutionalRule4bReferenceCountPriority_cases_of_length_le_one
        rightKey.prior.references rightCardinality with
      ⟨rightEmpty, rightCountValue⟩ | ⟨rightReference, rightSingleton, rightCountValue⟩
    · -- The left population is a singleton and the right one is empty: contradiction.
      rw [leftCountValue, rightCountValue] at countEq
      omega
    · -- Case B: both actual reference populations are singletons.
      have leftAlternatives :
          localizedRule4bcReferenceAlternatives leftKey.prior.references =
            [some leftReference] := by
        rw [leftSingleton]
        rfl
      have rightAlternatives :
          localizedRule4bcReferenceAlternatives rightKey.prior.references =
            [some rightReference] := by
        rw [rightSingleton]
        rfl
      rw [leftAlternatives] at leftPriorReadingsComputed
      rw [rightAlternatives] at rightPriorReadingsComputed
      obtain ⟨leftPrior, leftPriorReadingsEq, leftPriorComputed⟩ :=
        buildLocalizedRerootRule4bcReadingsWithRead?_singleton input leftRead leftFuel leftCursor
          (some leftReference) leftKey.prior.readings leftPriorReadingsComputed
      obtain ⟨rightPrior, rightPriorReadingsEq, rightPriorComputed⟩ :=
        buildLocalizedRerootRule4bcReadingsWithRead?_singleton input rightRead rightFuel rightCursor
          (some rightReference) rightKey.prior.readings rightPriorReadingsComputed
      rw [leftPriorReadingsEq] at leftReadingsComputed
      rw [rightPriorReadingsEq] at rightReadingsComputed
      obtain ⟨leftReading, leftReadingsEq, leftReadingComputed⟩ :=
        buildLocalizedRerootRule5ReadingsWithRead?_singleton input leftRead leftFuel leftCursor
          leftPrior leftKey.rule5Readings leftReadingsComputed
      obtain ⟨rightReading, rightReadingsEq, rightReadingComputed⟩ :=
        buildLocalizedRerootRule5ReadingsWithRead?_singleton input rightRead rightFuel rightCursor
          rightPrior rightKey.rule5Readings rightReadingsComputed
      have leftReferenceEq :=
        buildLocalizedRerootRule4bcReadingWithRead?_reference input leftRead leftFuel leftCursor
          (some leftReference) leftPrior leftPriorComputed
      have rightReferenceEq :=
        buildLocalizedRerootRule4bcReadingWithRead?_reference input rightRead rightFuel rightCursor
          (some rightReference) rightPrior rightPriorComputed
      obtain ⟨_leftPriorEq, leftCommonRComputed, leftCommonSComputed⟩ :=
        fullTie_rule5Reading_components input leftRead leftFuel leftCursor
          leftPrior leftReading leftReadingComputed
      obtain ⟨_rightPriorEq, rightCommonRComputed, rightCommonSComputed⟩ :=
        fullTie_rule5Reading_components input rightRead rightFuel rightCursor
          rightPrior rightReading rightReadingComputed
      have leftCommonRSome :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule5 leftReference .R) leftRead leftFuel leftCursor =
            some leftReading.commonR := by
        simpa [leftReferenceEq] using leftCommonRComputed
      have leftCommonSSome :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule5 leftReference .S) leftRead leftFuel leftCursor =
            some leftReading.commonS := by
        simpa [leftReferenceEq] using leftCommonSComputed
      have rightCommonRSome :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule5 rightReference .R) rightRead rightFuel rightCursor =
            some rightReading.commonR := by
        simpa [rightReferenceEq] using rightCommonRComputed
      have rightCommonSSome :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule5 rightReference .S) rightRead rightFuel rightCursor =
            some rightReading.commonS := by
        simpa [rightReferenceEq] using rightCommonSComputed
      have leftBaseComputed :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule4b leftReference) leftRead leftFuel leftCursor = some leftPrior.rule4bKey :=
        buildLocalizedRerootRule4bcReadingWithRead?_rule4bKey input leftRead leftFuel leftCursor
          (some leftReference) leftPrior leftPriorComputed
      have rightBaseComputed :
          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
              (.rule4b rightReference) rightRead rightFuel rightCursor = some rightPrior.rule4bKey :=
        buildLocalizedRerootRule4bcReadingWithRead?_rule4bKey input rightRead rightFuel rightCursor
          (some rightReference) rightPrior rightPriorComputed
      have baseTie :
          OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
              leftPrior.rule4bKey.descriptor rightPrior.rule4bKey.descriptor =
            Ordering.eq := by
        have tie := rule4bTie
        rw [leftPriorReadingsEq, rightPriorReadingsEq] at tie
        simpa [compareLocalizedRerootCompoundRule4bReadings,
          compareLocalizedRerootRule4bcReadingsByRule4b, Ordering.byKey,
          List.compareLex_cons_cons, List.compareLex_nil_nil] using tie
      rw [leftReadingsEq, rightReadingsEq]
      cases probe with
      | R =>
          simp only [compareLocalizedRerootCompoundRule5Readings,
            localizedRerootRule5Descriptor, List.compareLex_cons_cons, List.compareLex_nil_nil,
            Ordering.byKey, Ordering.then_eq]
          exact compareSparseLayers_actualRule5_lastProjection input
            leftReference rightReference .R
            leftRead rightRead leftStart rightStart
            (leftFuel := leftFuel) (rightFuel := rightFuel) leftCursor rightCursor
            leftReachable rightReachable leftAdmitted rightAdmitted
            leftPrior.rule4bKey rightPrior.rule4bKey leftBaseComputed rightBaseComputed
            baseTie leftReading.commonR rightReading.commonR
            leftCommonRSome rightCommonRSome
      | S =>
          simp only [compareLocalizedRerootCompoundRule5Readings,
            localizedRerootRule5Descriptor, List.compareLex_cons_cons, List.compareLex_nil_nil,
            Ordering.byKey, Ordering.then_eq]
          exact compareSparseLayers_actualRule5_lastProjection input
            leftReference rightReference .S
            leftRead rightRead leftStart rightStart
            (leftFuel := leftFuel) (rightFuel := rightFuel) leftCursor rightCursor
            leftReachable rightReachable leftAdmitted rightAdmitted
            leftPrior.rule4bKey rightPrior.rule4bKey leftBaseComputed rightBaseComputed
            baseTie leftReading.commonS rightReading.commonS
            leftCommonSSome rightCommonSSome

/-! ## Execution corollaries -/

/-- After an exact compound Rules-4b/4c tie the executable through-Rule-5 ordering is exactly the
common-`R` Rule-5 reading-list comparison. -/
theorem compareLocalizedRerootCompoundThroughRule5_ordering_eq_commonR
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      left.prior right.prior = Ordering.eq) :
    (input.compareLocalizedRerootCompoundThroughRule5 left right).ordering =
      input.compareLocalizedRerootCompoundRule5Readings
        .R left.rule5Readings right.rule5Readings := by
  rw [compareLocalizedRerootCompoundThroughRule5_ordering]
  unfold compareLocalizedRerootCompoundRule45Keys
  simp [compareLex, Ordering.byKey, priorTie]

/-- The runtime pseudo flag of the through-Rule-5 comparison reads exactly the common-`S`
Rule-5 decision.  This is a comparison flag, not a claim that the substrate is
pseudoasymmetric. -/
theorem compareLocalizedRerootCompoundThroughRule5_pseudo_eq_commonS
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule45Key)
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      left.prior right.prior = Ordering.eq) :
    (input.compareLocalizedRerootCompoundThroughRule5 left right).pseudo =
      (match input.compareLocalizedRerootCompoundRule5Readings
          .R left.rule5Readings right.rule5Readings with
        | .lt => (input.compareLocalizedRerootCompoundRule5Readings
            .S left.rule5Readings right.rule5Readings) != .lt
        | .gt => (input.compareLocalizedRerootCompoundRule5Readings
            .S left.rule5Readings right.rule5Readings) != .gt
        | .eq => false) := by
  unfold compareLocalizedRerootCompoundThroughRule5
  rw [priorTie]
  generalize cmpREq : input.compareLocalizedRerootCompoundRule5Readings
    .R left.rule5Readings right.rule5Readings = cmpR
  generalize cmpSEq : input.compareLocalizedRerootCompoundRule5Readings
    .S left.rule5Readings right.rule5Readings = cmpS
  cases cmpR <;> cases cmpS <;> simp [cmpREq, cmpSEq]

/-- **Guarded execution corollary.**  Under the guarded compound endpoint hypotheses, the
executable through-Rule-5 ordering after an exact compound Rules-4b/4c tie is exactly the
lexicographic comparison of the last-component projections of the two actual Rule-5 reading
lists. -/
theorem compareLocalizedRerootCompoundThroughRule5_ordering_eq_lastProjection_commonR
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (leftRead rightRead :
      input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (leftStart rightStart : input.LocalizedRerootCursor carrierFuel)
    {leftFuel rightFuel : Nat}
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (leftKey rightKey : input.LocalizedRerootCompoundRule45Key)
    (leftComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      leftRead leftFuel leftCursor = some leftKey)
    (rightComputed : input.buildLocalizedRerootCompoundRule45KeyWithRead?
      rightRead rightFuel rightCursor = some rightKey)
    (leftReachable : Relation.ReflTransGen (E input) leftStart leftCursor)
    (rightReachable : Relation.ReflTransGen (E input) rightStart rightCursor)
    (leftAdmitted : ∀ cursor,
      Relation.ReflTransGen (E input) leftStart cursor → LocalizedNoPseudoLabel (leftRead cursor))
    (rightAdmitted : ∀ cursor,
      Relation.ReflTransGen (E input) rightStart cursor → LocalizedNoPseudoLabel (rightRead cursor))
    (leftNoReads : leftKey.prior.references = [] → ∀ cursor,
      Relation.ReflTransGen (E input) leftStart cursor → leftRead cursor = none)
    (rightNoReads : rightKey.prior.references = [] → ∀ cursor,
      Relation.ReflTransGen (E input) rightStart cursor → rightRead cursor = none)
    (leftCardinality : leftKey.prior.references.length ≤ 1)
    (rightCardinality : rightKey.prior.references.length ≤ 1)
    (priorTie : input.compareLocalizedRerootCompoundRule4bcKeys
      leftKey.prior rightKey.prior = Ordering.eq) :
    (input.compareLocalizedRerootCompoundThroughRule5 leftKey rightKey).ordering =
      List.compareLex
        (Ordering.byKey
          (lastProjection ∘ input.localizedRerootRule5Descriptor .R)
          (OfficialRuleMajorKey.compareSparseLayers OfficialRuleMajorKey.compareNat))
        leftKey.rule5Readings rightKey.rule5Readings := by
  rw [compareLocalizedRerootCompoundThroughRule5_ordering_eq_commonR
    input leftKey rightKey priorTie]
  exact compareLocalizedRerootCompoundRule5Readings_eq_lastProjection input
    leftRead rightRead leftStart rightStart leftCursor rightCursor
    leftKey rightKey leftComputed rightComputed leftReachable rightReachable
    leftAdmitted rightAdmitted leftNoReads rightNoReads
    leftCardinality rightCardinality priorTie .R

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLastPriorityComponent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.lastProjectionEntry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.lastProjectionLayer
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.lastProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.lastProjectionEntry_fst
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.lastProjectionEntry_snd
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.lastProjectionLayer_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.lastProjectionLayer_cons
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.lastProjection_nil
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.lastProjection_cons
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedLastPriorityComponent_append_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.lastProjection_extendLocalizedPriorityLayers
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedPriorityLayers_eq_map
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedTwoComponentPriorityVector
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRule5SeniorityBit
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRule4bPriorityToRule5_twoComponent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLex_self_eq_of_refl
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareSparseEntry_sameAddress
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareSparseEntry_extendLocalizedRule5_lastProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareSparseLayer_extendLocalizedRule5_lastProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareSparseLayers_extendLocalizedRule5_lastProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareSparseLayers_cmpPriority_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareSparseLayers_compareNat_self
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareSparseLayers_extendRule5NoRule4bReference_lastProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedTwoComponentPriorityVector_of_rule4b_image
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedStageDescriptorImage_rule4b_twoComponent
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_descriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5NoRule4bReference_descriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareSparseLayers_actualRule5_lastProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareSparseLayers_actualRule5NoRule4bReference_lastProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingWithRead?_reference
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingWithRead?_rule4bKey
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule4bcReadingsWithRead?_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootRule5ReadingsWithRead?_singleton
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCompoundRule4bcKeyWithRead?_referenceCountPriority
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.constitutionalRule4bReferenceCountPriority_cases_of_length_le_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundRule5Readings_eq_lastProjection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_ordering_eq_commonR
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_pseudo_eq_commonS
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCompoundThroughRule5_ordering_eq_lastProjection_commonR

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
