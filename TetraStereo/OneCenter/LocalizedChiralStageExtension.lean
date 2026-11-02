import TetraStereo.OneCenter.LocalizedCumulativeKeyObservableOrder
import TetraStereo.OneCenter.LocalizedOutwardWholeStateKeyAgreement
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace TetraStereo.OneCenter

/-!
# Cross-stage exact extension of localized cumulative Rules-4a--5 keys

`LocalizedCumulativeRule45Stage` offers several cumulative readings of one and the same physical
observation.  `rule4b reference` carries only the Rule-4a unit kind and the Rule-4b like/unlike bit,
`rule4c reference` carries those two components and the Rule-4c lowercase bit, and
`rule5 rule4bReference rule5Reference` carries all of them and the Rule-5 senior/junior bit.

This module proves that the production builder
`buildLocalizedRerootCumulativeRule45KeyWithRead?` transports a *successful* `rule4b` compilation to
the *exact* `rule4c` and `rule5` compilations at the same cursor, under one explicit restriction:
every cursor reachable from the start reads `none` or an uppercase `.chiral` observation, never a
lowercase `.pseudoasymmetric` one.  The transported key has

* the same constitutional projection,
* the same `labels` and `rankedLabels` projections (not merely a permutation), and
* a descriptor whose every addressed entry keeps its address and its exact first two vector
  components, with the correct Rule-4c zero and Rule-5 seniority bit appended.

The transport is a *value* transformation at a fixed cursor.  Nothing is assumed about the
existence of a successful compilation, about tree or table alignment, about comparator
correspondence or about sorting success: those are all derived from the production definitions by
induction on the actual builder fuel.

## Main results

* `LocalizedNoPseudoLabel` — the admitted-observation restriction.
* `LocalizedStagePriorityImage` / `LocalizedStageDescriptorImage` — the image predicates that
  replace any hypothesis that the builder only ever produces well-formed vectors.
* `extendLocalizedRule4bPriorityToRule4c` / `extendLocalizedRule4bPriorityToRule5` — the explicit
  vector transformations, together with the entrywise identities
  `localizedCumulativeRule45Priority_rule4b_extend_rule4c` and
  `localizedCumulativeRule45Priority_rule4b_extend_rule5`.
* `compareLocalizedCumulativeRule45Priority_extend_rule4c` and
  `compareLocalizedCumulativeRule45Priority_extend_rule5` — the finite node comparison is unchanged
  by the extension (no reference identity, no matching-kind hypothesis).
* `compareSparseEntry/Layer/Layers_extendLocalizedPriority*`,
  `compareLocalizedRerootCumulativeRule45Keys_extend`,
  `insertLocalizedRerootCumulativeRule45Key_extend`,
  `sortLocalizedRerootCumulativeRule45Keys_extend` — the actual sparse comparator and the actual
  deterministic sibling sort commute with the extension.
* `mergeLocalizedRerootDescriptorChildren_extendLocalized`,
  `mergeLocalizedRerootLabelChildren_extendLocalized`,
  `localizedRerootRankedChildren_extendLocalized`,
  `mergeLocalizedRerootRankedLabelChildren_extendLocalized` — the actual child merges commute with
  the extension; the exact-label merges are literally unchanged.
* `buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptorImage` and
  `buildLocalizedRerootCumulativeRule45KeyWithRead?_stageExtension` — the actual builder produces
  descriptor image vectors and commutes with the extension.

## Scope

The restriction to admitted observations is *not* removable for the Rule-5 stage: the Rule-4c and
Rule-5 components of a lowercase observation are not recoverable from its two-component Rule-4b
vector, and Rule 4c deliberately reorders the lowercase `r`/`s` pair.  The result is therefore
stated relative to a reader, not to a global physical hypothesis, and the physical obligation
(discharging `LocalizedNoPseudoLabel` for the actual outward reader) remains a separate claim.
This module proves structural mathematics only.  It adds no solver, evaluator or production path.
-/

namespace CertifiedLocalizedCIPInput

/-! ## Admitted observations and stage images -/

/-- An observation that is never a lowercase pseudoasymmetric descriptor.  Rule 4c and Rule 5 both
need this restriction: the two-component Rule-4b vector of a pseudoasymmetric observation carries no
information from which the Rule-4c or Rule-5 component could be recovered. -/
def LocalizedNoPseudoLabel : Option LocalizedAuxiliaryLabel → Prop
  | none => True
  | some (.chiral _) => True
  | some (.pseudoasymmetric _) => False

/-- A cumulative node vector lying in the stage image of an admitted observation. -/
def LocalizedStagePriorityImage (stage : LocalizedCumulativeRule45Stage)
    (admitted : Option LocalizedAuxiliaryLabel → Prop) (vector : List Nat) : Prop :=
  ∃ label, admitted label ∧ vector = localizedCumulativeRule45Priority stage label

/-- Every descriptor entry of a key reads an admitted observation through the source stage. -/
def LocalizedStageDescriptorImage (stage : LocalizedCumulativeRule45Stage)
    (admitted : Option LocalizedAuxiliaryLabel → Prop)
    (descriptor : List (List (OfficialSparseEntry (List Nat)))) : Prop :=
  ∀ layer ∈ descriptor, ∀ entry ∈ layer, LocalizedStagePriorityImage stage admitted entry.2

/-! ## The explicit vector transformations -/

/-- Extend a two-component Rule-4b cumulative vector by the Rule-4c bit.  Rule 4c contributes `0`
on every admitted observation, so the appended component is the constant `0`. -/
def extendLocalizedRule4bPriorityToRule4c (vector : List Nat) : List Nat :=
  match vector with
  | kind :: like :: _ => [kind, like, 0]
  | _ => vector

/-- Extend a two-component Rule-4b cumulative vector by the Rule-4c bit and the Rule-5
senior/junior bit.  Both appended components are recovered from the two leading components: the
Rule-4a kind tells whether an uppercase descriptor is present at all, and the Rule-4b like/unlike
bit names that descriptor (`reference` when like, `RS.swap reference` when unlike). -/
def extendLocalizedRule4bPriorityToRule5 (rule4bReference rule5Reference : RS)
    (vector : List Nat) : List Nat :=
  match vector with
  | kind :: like :: _ =>
      let seniority :=
        if kind == 2 then
          if (if like == 1 then rule4bReference else RS.swap rule4bReference) == rule5Reference
            then 1 else 0
        else 0
      [kind, like, 0, seniority]
  | _ => vector

/-- Extend one addressed descriptor entry.  The address is untouched. -/
def extendLocalizedPriorityEntry (extend : List Nat → List Nat)
    (entry : OfficialSparseEntry (List Nat)) : OfficialSparseEntry (List Nat) :=
  (entry.1, extend entry.2)

/-- Extend one descriptor sphere.  Addresses inside the sphere are untouched. -/
def extendLocalizedPriorityLayer (extend : List Nat → List Nat)
    (layer : List (OfficialSparseEntry (List Nat))) :
    List (OfficialSparseEntry (List Nat)) :=
  layer.map (extendLocalizedPriorityEntry extend)

/-- Extend every descriptor sphere of a key. -/
def extendLocalizedPriorityLayers (extend : List Nat → List Nat)
    (layers : List (List (OfficialSparseEntry (List Nat)))) :
    List (List (OfficialSparseEntry (List Nat))) :=
  layers.map (extendLocalizedPriorityLayer extend)

/-- Cross-stage extension of one cumulative key: the constitutional and both label projections are
untouched, and the descriptor projection is extended entrywise. -/
def extendLocalizedRerootCumulativeRule45Key (input : CertifiedLocalizedCIPInput)
    (extend : List Nat → List Nat)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    input.LocalizedRerootCumulativeRule45Key where
  constitutional := key.constitutional
  descriptor := extendLocalizedPriorityLayers extend key.descriptor
  labels := key.labels
  rankedLabels := key.rankedLabels

@[simp] theorem extendLocalizedPriorityEntry_fst (extend : List Nat → List Nat)
    (entry : OfficialSparseEntry (List Nat)) :
    (extendLocalizedPriorityEntry extend entry).1 = entry.1 := rfl

@[simp] theorem extendLocalizedPriorityEntry_snd (extend : List Nat → List Nat)
    (entry : OfficialSparseEntry (List Nat)) :
    (extendLocalizedPriorityEntry extend entry).2 = extend entry.2 := rfl

@[simp] theorem extendLocalizedRerootCumulativeRule45Key_constitutional
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (input.extendLocalizedRerootCumulativeRule45Key extend key).constitutional =
      key.constitutional := rfl

@[simp] theorem extendLocalizedRerootCumulativeRule45Key_descriptor
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (input.extendLocalizedRerootCumulativeRule45Key extend key).descriptor =
      extendLocalizedPriorityLayers extend key.descriptor := rfl

@[simp] theorem extendLocalizedRerootCumulativeRule45Key_labels
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (input.extendLocalizedRerootCumulativeRule45Key extend key).labels = key.labels := rfl

@[simp] theorem extendLocalizedRerootCumulativeRule45Key_rankedLabels
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (input.extendLocalizedRerootCumulativeRule45Key extend key).rankedLabels =
      key.rankedLabels := rfl

/-- The constitutional projection, as a function, is fixed by the key extension. -/
theorem constitutional_comp_extendLocalizedRerootCumulativeRule45Key
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat) :
    (fun key : input.LocalizedRerootCumulativeRule45Key => key.constitutional) ∘
        input.extendLocalizedRerootCumulativeRule45Key extend =
      fun key => key.constitutional := by
  funext key
  rfl

/-! ## Entrywise identities: the extension is the target stage vector -/

/-- Under an admitted observation the Rule-4b vector extends exactly to the Rule-4c vector. -/
theorem localizedCumulativeRule45Priority_rule4b_extend_rule4c
    (reference : RS) (label : Option LocalizedAuxiliaryLabel)
    (admitted : LocalizedNoPseudoLabel label) :
    extendLocalizedRule4bPriorityToRule4c
        (localizedCumulativeRule45Priority (.rule4b reference) label) =
      localizedCumulativeRule45Priority (.rule4c reference) label := by
  cases reference <;>
    cases label with
    | none => rfl
    | some label =>
        cases label with
        | pseudoasymmetric descriptor => exact admitted.elim
        | chiral descriptor => cases descriptor <;> rfl

/-- Under an admitted observation the Rule-4b vector extends exactly to the Rule-5 vector. -/
theorem localizedCumulativeRule45Priority_rule4b_extend_rule5
    (rule4bReference rule5Reference : RS) (label : Option LocalizedAuxiliaryLabel)
    (admitted : LocalizedNoPseudoLabel label) :
    extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference
        (localizedCumulativeRule45Priority (.rule4b rule4bReference) label) =
      localizedCumulativeRule45Priority (.rule5 rule4bReference rule5Reference) label := by
  cases rule4bReference <;> cases rule5Reference <;>
    cases label with
    | none => rfl
    | some label =>
        cases label with
        | pseudoasymmetric descriptor => exact admitted.elim
        | chiral descriptor => cases descriptor <;> rfl

/-! ## Node comparison is unchanged by the extension

The two-component Rule-4b vector of an admitted observation determines that observation, and the
extension appends components only to the right of a strictly longer vector.  Both facts together
make the node comparison identical at the source and target stages, with no relation between the
Rule-4b and Rule-5 references. -/

/-- At a fixed Rule-4b reference, admitted observations are determined by their Rule-4b
cumulative vector. -/
theorem localizedCumulativeRule45Priority_rule4b_injective (reference : RS)
    {first second : Option LocalizedAuxiliaryLabel}
    (firstAdmitted : LocalizedNoPseudoLabel first)
    (secondAdmitted : LocalizedNoPseudoLabel second)
    (equal : localizedCumulativeRule45Priority (.rule4b reference) first =
      localizedCumulativeRule45Priority (.rule4b reference) second) :
    first = second := by
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some second =>
          cases second with
          | pseudoasymmetric descriptor => exact secondAdmitted.elim
          | chiral descriptor =>
              cases descriptor <;> cases reference <;>
                simp_all [localizedCumulativeRule45Priority, localizedRule4aPriority,
                  localizedRule4bPriority]
  | some first =>
      cases first with
      | pseudoasymmetric descriptor => exact firstAdmitted.elim
      | chiral descriptor =>
          cases descriptor <;>
            cases second with
            | none =>
                cases reference <;>
                  simp_all [localizedCumulativeRule45Priority, localizedRule4aPriority,
                    localizedRule4bPriority]
            | some second =>
                cases second with
                | pseudoasymmetric descriptor => exact secondAdmitted.elim
                | chiral secondDescriptor =>
                    cases secondDescriptor <;> cases reference <;>
                      simp_all [localizedCumulativeRule45Priority, localizedRule4aPriority,
                        localizedRule4bPriority]

/-- The Rule-4c extension never changes a Rule-4b node comparison, for any observations. -/
theorem compareLocalizedCumulativeRule45Priority_extend_rule4c (reference : RS)
    (first second : Option LocalizedAuxiliaryLabel) :
    compareLocalizedCumulativeRule45Priority
        (extendLocalizedRule4bPriorityToRule4c
          (localizedCumulativeRule45Priority (.rule4b reference) first))
        (extendLocalizedRule4bPriorityToRule4c
          (localizedCumulativeRule45Priority (.rule4b reference) second)) =
      compareLocalizedCumulativeRule45Priority
        (localizedCumulativeRule45Priority (.rule4b reference) first)
        (localizedCumulativeRule45Priority (.rule4b reference) second) := by
  cases reference <;>
    cases first with
    | none =>
        cases second with
        | none => rfl
        | some second =>
            cases second with
            | pseudoasymmetric descriptor => rfl
            | chiral descriptor => cases descriptor <;> rfl
    | some first =>
        cases first with
        | pseudoasymmetric descriptor =>
            cases descriptor <;>
              cases second with
              | none => rfl
              | some second =>
                  cases second with
                  | pseudoasymmetric descriptor => cases descriptor <;> rfl
                  | chiral descriptor => cases descriptor <;> rfl
        | chiral descriptor =>
            cases descriptor <;>
              cases second with
              | none => rfl
              | some second =>
                  cases second with
                  | pseudoasymmetric descriptor => cases descriptor <;> rfl
                  | chiral descriptor => cases descriptor <;> rfl

/-- The Rule-5 extension never changes a Rule-4b node comparison on admitted observations, for any
pair of references. -/
theorem compareLocalizedCumulativeRule45Priority_extend_rule5
    (rule4bReference rule5Reference : RS) (first second : Option LocalizedAuxiliaryLabel)
    (firstAdmitted : LocalizedNoPseudoLabel first)
    (secondAdmitted : LocalizedNoPseudoLabel second) :
    compareLocalizedCumulativeRule45Priority
        (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference
          (localizedCumulativeRule45Priority (.rule4b rule4bReference) first))
        (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference
          (localizedCumulativeRule45Priority (.rule4b rule4bReference) second)) =
      compareLocalizedCumulativeRule45Priority
        (localizedCumulativeRule45Priority (.rule4b rule4bReference) first)
        (localizedCumulativeRule45Priority (.rule4b rule4bReference) second) := by
  cases rule4bReference <;> cases rule5Reference <;>
    cases first with
    | none =>
        cases second with
        | none => rfl
        | some second =>
            cases second with
            | pseudoasymmetric descriptor => exact secondAdmitted.elim
            | chiral descriptor => cases descriptor <;> rfl
    | some first =>
        cases first with
        | pseudoasymmetric descriptor => exact firstAdmitted.elim
        | chiral descriptor =>
            cases descriptor <;>
              cases second with
              | none => rfl
              | some second =>
                  cases second with
                  | pseudoasymmetric descriptor => exact secondAdmitted.elim
                  | chiral secondDescriptor => cases secondDescriptor <;> rfl

/-- Image form of the Rule-4c node comparison transport.  Every descriptor entry that the builder
can produce is of this shape, so this is the form consumed by the sparse comparators. -/
theorem compareLocalizedCumulativeRule45Priority_extend_rule4c_image (reference : RS)
    (first second : List Nat)
    (firstImage : LocalizedStagePriorityImage (.rule4b reference) LocalizedNoPseudoLabel first)
    (secondImage : LocalizedStagePriorityImage (.rule4b reference) LocalizedNoPseudoLabel second) :
    compareLocalizedCumulativeRule45Priority (extendLocalizedRule4bPriorityToRule4c first)
        (extendLocalizedRule4bPriorityToRule4c second) =
      compareLocalizedCumulativeRule45Priority first second := by
  obtain ⟨firstLabel, _firstAdmitted, rfl⟩ := firstImage
  obtain ⟨secondLabel, _secondAdmitted, rfl⟩ := secondImage
  exact compareLocalizedCumulativeRule45Priority_extend_rule4c reference firstLabel secondLabel

/-- Image form of the Rule-5 node comparison transport. -/
theorem compareLocalizedCumulativeRule45Priority_extend_rule5_image
    (rule4bReference rule5Reference : RS) (first second : List Nat)
    (firstImage : LocalizedStagePriorityImage (.rule4b rule4bReference) LocalizedNoPseudoLabel
      first)
    (secondImage : LocalizedStagePriorityImage (.rule4b rule4bReference) LocalizedNoPseudoLabel
      second) :
    compareLocalizedCumulativeRule45Priority
        (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference first)
        (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference second) =
      compareLocalizedCumulativeRule45Priority first second := by
  obtain ⟨firstLabel, firstAdmitted, rfl⟩ := firstImage
  obtain ⟨secondLabel, secondAdmitted, rfl⟩ := secondImage
  exact compareLocalizedCumulativeRule45Priority_extend_rule5 rule4bReference rule5Reference
    firstLabel secondLabel firstAdmitted secondAdmitted

/-! ## Sparse comparison of extended descriptors -/

/-- Extending an addressed descriptor entry does not change its sparse comparison. -/
theorem compareSparseEntry_extendLocalizedPriorityEntry
    {stage : LocalizedCumulativeRule45Stage}
    {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {extend : List Nat → List Nat}
    (nodewise : ∀ (first second : List Nat),
      LocalizedStagePriorityImage stage admitted first →
      LocalizedStagePriorityImage stage admitted second →
      compareLocalizedCumulativeRule45Priority (extend first) (extend second) =
        compareLocalizedCumulativeRule45Priority first second) :
    ∀ (left right : OfficialSparseEntry (List Nat)),
      LocalizedStagePriorityImage stage admitted left.2 →
      LocalizedStagePriorityImage stage admitted right.2 →
      OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority
          (extendLocalizedPriorityEntry extend left)
          (extendLocalizedPriorityEntry extend right) =
        OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority
          left right := by
  intro left right leftImage rightImage
  unfold OfficialRuleMajorKey.compareSparseEntry
  simp only [compareLex, Ordering.byKey, extendLocalizedPriorityEntry_fst,
    extendLocalizedPriorityEntry_snd]
  rw [nodewise left.2 right.2 leftImage rightImage]

/-- Extending a descriptor sphere does not change its sparse comparison. -/
theorem compareSparseLayer_extendLocalizedPriorityLayer
    {stage : LocalizedCumulativeRule45Stage}
    {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {extend : List Nat → List Nat}
    (nodewise : ∀ (first second : List Nat),
      LocalizedStagePriorityImage stage admitted first →
      LocalizedStagePriorityImage stage admitted second →
      compareLocalizedCumulativeRule45Priority (extend first) (extend second) =
        compareLocalizedCumulativeRule45Priority first second) :
    ∀ (left right : List (OfficialSparseEntry (List Nat))),
      (∀ entry ∈ left, LocalizedStagePriorityImage stage admitted entry.2) →
      (∀ entry ∈ right, LocalizedStagePriorityImage stage admitted entry.2) →
      OfficialRuleMajorKey.compareSparseLayer compareLocalizedCumulativeRule45Priority
          (left.map (extendLocalizedPriorityEntry extend))
          (right.map (extendLocalizedPriorityEntry extend)) =
        OfficialRuleMajorKey.compareSparseLayer compareLocalizedCumulativeRule45Priority
          left right
  | [], [] => by intro _ _; rfl
  | [], _ :: _ => by intro _ _; rfl
  | _ :: _, [] => by intro _ _; rfl
  | head :: tail, otherHead :: otherTail => by
      intro leftImage rightImage
      unfold OfficialRuleMajorKey.compareSparseLayer
      simp only [List.map_cons, List.compareLex_cons_cons]
      rw [compareSparseEntry_extendLocalizedPriorityEntry nodewise head otherHead
        (leftImage head (by simp)) (rightImage otherHead (by simp))]
      have tailStep := compareSparseLayer_extendLocalizedPriorityLayer nodewise tail otherTail
        (fun entry present => leftImage entry (by simp [present]))
        (fun entry present => rightImage entry (by simp [present]))
      unfold OfficialRuleMajorKey.compareSparseLayer at tailStep
      rw [tailStep]

/-- Extending a descriptor does not change its sparse comparison. -/
theorem compareSparseLayers_extendLocalizedPriorityLayers
    {stage : LocalizedCumulativeRule45Stage}
    {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {extend : List Nat → List Nat}
    (nodewise : ∀ (first second : List Nat),
      LocalizedStagePriorityImage stage admitted first →
      LocalizedStagePriorityImage stage admitted second →
      compareLocalizedCumulativeRule45Priority (extend first) (extend second) =
        compareLocalizedCumulativeRule45Priority first second) :
    ∀ (left right : List (List (OfficialSparseEntry (List Nat)))),
      LocalizedStageDescriptorImage stage admitted left →
      LocalizedStageDescriptorImage stage admitted right →
      OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          (left.map (extendLocalizedPriorityLayer extend))
          (right.map (extendLocalizedPriorityLayer extend)) =
        OfficialRuleMajorKey.compareSparseLayers compareLocalizedCumulativeRule45Priority
          left right
  | [], [] => by intro _ _; rfl
  | [], _ :: _ => by intro _ _; rfl
  | _ :: _, [] => by intro _ _; rfl
  | head :: tail, otherHead :: otherTail => by
      intro leftImage rightImage
      unfold OfficialRuleMajorKey.compareSparseLayers
      simp only [List.map_cons, List.compareLex_cons_cons, extendLocalizedPriorityLayer]
      have headStep := compareSparseLayer_extendLocalizedPriorityLayer nodewise head otherHead
        (fun entry present => leftImage head (by simp) entry present)
        (fun entry present => rightImage otherHead (by simp) entry present)
      rw [headStep]
      have tailStep := compareSparseLayers_extendLocalizedPriorityLayers nodewise tail otherTail
        (fun layer present entry entryPresent =>
          leftImage layer (by simp [present]) entry entryPresent)
        (fun layer present entry entryPresent =>
          rightImage layer (by simp [present]) entry entryPresent)
      unfold OfficialRuleMajorKey.compareSparseLayers at tailStep
      rw [tailStep]

/-- The actual cumulative key comparator is unchanged by the extension. -/
theorem compareLocalizedRerootCumulativeRule45Keys_extend
    (input : CertifiedLocalizedCIPInput)
    {stage : LocalizedCumulativeRule45Stage}
    {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {extend : List Nat → List Nat}
    (nodewise : ∀ (first second : List Nat),
      LocalizedStagePriorityImage stage admitted first →
      LocalizedStagePriorityImage stage admitted second →
      compareLocalizedCumulativeRule45Priority (extend first) (extend second) =
        compareLocalizedCumulativeRule45Priority first second)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (leftImage : LocalizedStageDescriptorImage stage admitted left.descriptor)
    (rightImage : LocalizedStageDescriptorImage stage admitted right.descriptor) :
    input.compareLocalizedRerootCumulativeRule45Keys
        (input.extendLocalizedRerootCumulativeRule45Key extend left)
        (input.extendLocalizedRerootCumulativeRule45Key extend right) =
      input.compareLocalizedRerootCumulativeRule45Keys left right := by
  unfold compareLocalizedRerootCumulativeRule45Keys
  simp only [compareLex, Ordering.byKey,
    extendLocalizedRerootCumulativeRule45Key_constitutional,
    extendLocalizedRerootCumulativeRule45Key_descriptor, extendLocalizedPriorityLayers]
  rw [compareSparseLayers_extendLocalizedPriorityLayers nodewise left.descriptor
    right.descriptor leftImage rightImage]

/-! ## The actual deterministic sibling sort commutes with the extension -/

/-- The actual cumulative insertion commutes with the key extension. -/
theorem insertLocalizedRerootCumulativeRule45Key_extend
    (input : CertifiedLocalizedCIPInput)
    {stage : LocalizedCumulativeRule45Stage}
    {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {extend : List Nat → List Nat}
    (nodewise : ∀ (first second : List Nat),
      LocalizedStagePriorityImage stage admitted first →
      LocalizedStagePriorityImage stage admitted second →
      compareLocalizedCumulativeRule45Priority (extend first) (extend second) =
        compareLocalizedCumulativeRule45Priority first second)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    ∀ keys : List input.LocalizedRerootCumulativeRule45Key,
      LocalizedStageDescriptorImage stage admitted key.descriptor →
      (∀ other ∈ keys, LocalizedStageDescriptorImage stage admitted other.descriptor) →
      input.insertLocalizedRerootCumulativeRule45Key
          (input.extendLocalizedRerootCumulativeRule45Key extend key)
          (keys.map (input.extendLocalizedRerootCumulativeRule45Key extend)) =
        (input.insertLocalizedRerootCumulativeRule45Key key keys).map
          (input.extendLocalizedRerootCumulativeRule45Key extend)
  | [] => by
      intro _ _
      rfl
  | head :: tail => by
      intro keyImage tailImage
      simp only [List.map_cons, insertLocalizedRerootCumulativeRule45Key]
      rw [compareLocalizedRerootCumulativeRule45Keys_extend input nodewise key head keyImage
        (tailImage head (by simp))]
      cases comparison : input.compareLocalizedRerootCumulativeRule45Keys key head with
      | lt =>
          rw [insertLocalizedRerootCumulativeRule45Key_extend input nodewise key tail keyImage
            (fun other present => tailImage other (by simp [present]))]
          rfl
      | eq => rfl
      | gt => rfl

/-- The actual cumulative sibling sort commutes with the key extension. -/
theorem sortLocalizedRerootCumulativeRule45Keys_extend
    (input : CertifiedLocalizedCIPInput)
    {stage : LocalizedCumulativeRule45Stage}
    {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {extend : List Nat → List Nat}
    (nodewise : ∀ (first second : List Nat),
      LocalizedStagePriorityImage stage admitted first →
      LocalizedStagePriorityImage stage admitted second →
      compareLocalizedCumulativeRule45Priority (extend first) (extend second) =
        compareLocalizedCumulativeRule45Priority first second)
    (keys : List input.LocalizedRerootCumulativeRule45Key) :
    (∀ key ∈ keys, LocalizedStageDescriptorImage stage admitted key.descriptor) →
      input.sortLocalizedRerootCumulativeRule45Keys
          (keys.map (input.extendLocalizedRerootCumulativeRule45Key extend)) =
        (input.sortLocalizedRerootCumulativeRule45Keys keys).map
          (input.extendLocalizedRerootCumulativeRule45Key extend) := by
  intro images
  induction keys with
  | nil => rfl
  | cons key keys inductionHypothesis =>
      simp only [List.map_cons, sortLocalizedRerootCumulativeRule45Keys]
      rw [inductionHypothesis (fun other present => images other (by simp [present]))]
      exact insertLocalizedRerootCumulativeRule45Key_extend input nodewise key
        (input.sortLocalizedRerootCumulativeRule45Keys keys)
        (images key (by simp))
        (fun other present =>
          images other (by
            simp [(List.Perm.mem_iff
              (input.sortLocalizedRerootCumulativeRule45Keys_perm keys)).mp present]))

/-! ## Child layer counts and the actual child merges -/

private theorem foldl_descriptor_length_extendLocalized
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat) :
    ∀ (children : List input.LocalizedRerootCumulativeRule45Key) (accumulator : Nat),
      (children.map (input.extendLocalizedRerootCumulativeRule45Key extend)).foldl
          (fun longest child => max longest child.descriptor.length) accumulator =
        children.foldl
          (fun longest child => max longest child.descriptor.length) accumulator
  | [], accumulator => rfl
  | child :: children, accumulator => by
      simp only [List.map_cons, List.foldl_cons,
        extendLocalizedRerootCumulativeRule45Key_descriptor, extendLocalizedPriorityLayers,
        List.length_map]
      exact foldl_descriptor_length_extendLocalized input extend children _

private theorem foldl_label_length_extendLocalized
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat) :
    ∀ (children : List input.LocalizedRerootCumulativeRule45Key) (accumulator : Nat),
      (children.map (input.extendLocalizedRerootCumulativeRule45Key extend)).foldl
          (fun longest child => max longest child.labels.length) accumulator =
        children.foldl
          (fun longest child => max longest child.labels.length) accumulator
  | [], accumulator => rfl
  | child :: children, accumulator => by
      simp only [List.map_cons, List.foldl_cons,
        extendLocalizedRerootCumulativeRule45Key_labels]
      exact foldl_label_length_extendLocalized input extend children _

private theorem foldl_rankedLabel_length_extendLocalized
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat) :
    ∀ (children : List input.LocalizedRerootCumulativeRule45Key) (accumulator : Nat),
      (children.map (input.extendLocalizedRerootCumulativeRule45Key extend)).foldl
          (fun longest child => max longest child.rankedLabels.length) accumulator =
        children.foldl
          (fun longest child => max longest child.rankedLabels.length) accumulator
  | [], accumulator => rfl
  | child :: children, accumulator => by
      simp only [List.map_cons, List.foldl_cons,
        extendLocalizedRerootCumulativeRule45Key_rankedLabels]
      exact foldl_rankedLabel_length_extendLocalized input extend children _

theorem localizedRerootDescriptorChildLayerCount_extendLocalized
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.localizedRerootDescriptorChildLayerCount
        (children.map (input.extendLocalizedRerootCumulativeRule45Key extend)) =
      input.localizedRerootDescriptorChildLayerCount children :=
  foldl_descriptor_length_extendLocalized input extend children 0

theorem localizedRerootLabelChildLayerCount_extendLocalized
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.localizedRerootLabelChildLayerCount
        (children.map (input.extendLocalizedRerootCumulativeRule45Key extend)) =
      input.localizedRerootLabelChildLayerCount children :=
  foldl_label_length_extendLocalized input extend children 0

theorem localizedRerootRankedLabelChildLayerCount_extendLocalized
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.localizedRerootRankedLabelChildLayerCount
        (children.map (input.extendLocalizedRerootCumulativeRule45Key extend)) =
      input.localizedRerootRankedLabelChildLayerCount children :=
  foldl_rankedLabel_length_extendLocalized input extend children 0

/-- The indexed `getD` projection of an extended descriptor is the entrywise extension of the
source sphere. -/
theorem extendLocalizedPriorityLayers_getD (extend : List Nat → List Nat)
    (layers : List (List (OfficialSparseEntry (List Nat)))) (depth : Nat) :
    (extendLocalizedPriorityLayers extend layers).getD depth [] =
      (layers.getD depth []).map (extendLocalizedPriorityEntry extend) := by
  induction layers generalizing depth with
  | nil => cases depth <;> rfl
  | cons layer layers inductionHypothesis =>
      cases depth with
      | zero => rfl
      | succ depth => exact inductionHypothesis depth

/-- `prefixLayer` commutes with the entrywise descriptor extension. -/
theorem prefixLayer_extendLocalizedPriorityEntry (extend : List Nat → List Nat) (slot : Nat)
    (layer : List (OfficialSparseEntry (List Nat))) :
    OfficialRuleMajorKey.prefixLayer slot (layer.map (extendLocalizedPriorityEntry extend)) =
      (OfficialRuleMajorKey.prefixLayer slot layer).map
        (extendLocalizedPriorityEntry extend) := by
  unfold OfficialRuleMajorKey.prefixLayer
  rw [List.map_map, List.map_map]
  rfl

private theorem flatMap_congr_extendLocalized {α β : Type*} (values : List α)
    {first second : α → List β} (agrees : ∀ value, first value = second value) :
    values.flatMap first = values.flatMap second := by
  induction values with
  | nil => rfl
  | cons value values inductionHypothesis =>
      simp [agrees value, inductionHypothesis]

/-- Merging cumulative descriptor spheres commutes with the entrywise extension. -/
theorem mergeLocalizedRerootDescriptorChildren_extendLocalized
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.mergeLocalizedRerootDescriptorChildren
        (children.map (input.extendLocalizedRerootCumulativeRule45Key extend)) =
      extendLocalizedPriorityLayers extend
        (input.mergeLocalizedRerootDescriptorChildren children) := by
  unfold mergeLocalizedRerootDescriptorChildren
  rw [localizedRerootDescriptorChildLayerCount_extendLocalized]
  simp only [extendLocalizedPriorityLayers, extendLocalizedPriorityLayer, List.map_map,
    Function.comp_apply]
  apply List.map_congr_left
  intro depth _
  simp only [Function.comp_apply, extendLocalizedPriorityLayer]
  rw [List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  apply flatMap_congr_extendLocalized
  rintro ⟨child, slot⟩
  simp only [Prod.map_fst, Prod.map_snd, id,
    extendLocalizedRerootCumulativeRule45Key_descriptor, extendLocalizedPriorityLayers_getD,
    prefixLayer_extendLocalizedPriorityEntry]

/-- Merging exact-label spheres is literally unchanged by the key extension. -/
theorem mergeLocalizedRerootLabelChildren_extendLocalized
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    input.mergeLocalizedRerootLabelChildren
        (children.map (input.extendLocalizedRerootCumulativeRule45Key extend)) =
      input.mergeLocalizedRerootLabelChildren children := by
  unfold mergeLocalizedRerootLabelChildren
  rw [localizedRerootLabelChildLayerCount_extendLocalized]
  apply List.map_congr_left
  intro depth _
  rw [List.zipIdx_map, List.flatMap_map]
  apply flatMap_congr_extendLocalized
  rintro ⟨child, slot⟩
  simp only [Prod.map_fst, Prod.map_snd, id,
    extendLocalizedRerootCumulativeRule45Key_labels]

/-- Equal-rank continuation commutes with the key extension: the extension preserves the actual
cumulative comparator, hence the rank decision. -/
theorem localizedRerootRankedChildTail_extendLocalized
    (input : CertifiedLocalizedCIPInput)
    {stage : LocalizedCumulativeRule45Stage}
    {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {extend : List Nat → List Nat}
    (nodewise : ∀ (first second : List Nat),
      LocalizedStagePriorityImage stage admitted first →
      LocalizedStagePriorityImage stage admitted second →
      compareLocalizedCumulativeRule45Priority (extend first) (extend second) =
        compareLocalizedCumulativeRule45Priority first second)
    (previous : input.LocalizedRerootCumulativeRule45Key) (rank : Nat) :
    ∀ children : List input.LocalizedRerootCumulativeRule45Key,
      (∀ other ∈ previous :: children,
        LocalizedStageDescriptorImage stage admitted other.descriptor) →
      input.localizedRerootRankedChildTail
          (input.extendLocalizedRerootCumulativeRule45Key extend previous) rank
          (children.map (input.extendLocalizedRerootCumulativeRule45Key extend)) =
        (input.localizedRerootRankedChildTail previous rank children).map
          (Prod.map (input.extendLocalizedRerootCumulativeRule45Key extend) id)
  | [], _ => rfl
  | child :: children, images => by
      simp only [List.map_cons, localizedRerootRankedChildTail]
      rw [compareLocalizedRerootCumulativeRule45Keys_extend input nodewise child previous
        (images child (by simp)) (images previous (by simp))]
      by_cases same : input.compareLocalizedRerootCumulativeRule45Keys child previous =
        Ordering.eq
      · rw [if_pos same]
        rw [localizedRerootRankedChildTail_extendLocalized input nodewise child rank children
          (fun other present => images other (by simp [present]))]
        rfl
      · rw [if_neg same]
        rw [localizedRerootRankedChildTail_extendLocalized input nodewise child (rank + 1)
          children (fun other present => images other (by simp [present]))]
        rfl

/-- The rank assignment over a child list commutes with the key extension. -/
theorem localizedRerootRankedChildren_extendLocalized
    (input : CertifiedLocalizedCIPInput)
    {stage : LocalizedCumulativeRule45Stage}
    {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {extend : List Nat → List Nat}
    (nodewise : ∀ (first second : List Nat),
      LocalizedStagePriorityImage stage admitted first →
      LocalizedStagePriorityImage stage admitted second →
      compareLocalizedCumulativeRule45Priority (extend first) (extend second) =
        compareLocalizedCumulativeRule45Priority first second)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    (∀ key ∈ children, LocalizedStageDescriptorImage stage admitted key.descriptor) →
      input.localizedRerootRankedChildren
          (children.map (input.extendLocalizedRerootCumulativeRule45Key extend)) =
        (input.localizedRerootRankedChildren children).map
          (Prod.map (input.extendLocalizedRerootCumulativeRule45Key extend) id) := by
  cases children with
  | nil => intro _; rfl
  | cons child children =>
      intro images
      simp only [List.map_cons, localizedRerootRankedChildren]
      rw [localizedRerootRankedChildTail_extendLocalized input nodewise child 0 children
        (fun other present => images other (by simp [present]))]
      rfl

/-- Merging hierarchy-rank-addressed label spheres is literally unchanged by the key
extension. -/
theorem mergeLocalizedRerootRankedLabelChildren_extendLocalized
    (input : CertifiedLocalizedCIPInput)
    {stage : LocalizedCumulativeRule45Stage}
    {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {extend : List Nat → List Nat}
    (nodewise : ∀ (first second : List Nat),
      LocalizedStagePriorityImage stage admitted first →
      LocalizedStagePriorityImage stage admitted second →
      compareLocalizedCumulativeRule45Priority (extend first) (extend second) =
        compareLocalizedCumulativeRule45Priority first second)
    (children : List input.LocalizedRerootCumulativeRule45Key) :
    (∀ key ∈ children, LocalizedStageDescriptorImage stage admitted key.descriptor) →
      input.mergeLocalizedRerootRankedLabelChildren
          (children.map (input.extendLocalizedRerootCumulativeRule45Key extend)) =
        input.mergeLocalizedRerootRankedLabelChildren children := by
  intro images
  unfold mergeLocalizedRerootRankedLabelChildren
  rw [localizedRerootRankedLabelChildLayerCount_extendLocalized,
    localizedRerootRankedChildren_extendLocalized input nodewise children images]
  apply List.map_congr_left
  intro depth _
  rw [List.flatMap_map]
  apply flatMap_congr_extendLocalized
  rintro ⟨child, rank⟩
  simp only [Prod.map_fst, Prod.map_snd, id,
    extendLocalizedRerootCumulativeRule45Key_rankedLabels]

/-! ## Descriptor image of the actual merges -/

private theorem mem_of_mem_getD_nil {α : Type*} :
    ∀ (layers : List (List α)) (depth : Nat) (entry : α),
      entry ∈ layers.getD depth [] → ∃ layer, layer ∈ layers ∧ entry ∈ layer
  | [], _, _, present => by
      simp at present
  | layer :: layers, depth, entry, present => by
      cases depth with
      | zero => exact ⟨layer, by simp, present⟩
      | succ depth =>
          obtain ⟨inner, innerMem, entryMem⟩ :=
            mem_of_mem_getD_nil layers depth entry present
          exact ⟨inner, by simp [innerMem], entryMem⟩

/-- Membership in a prefixed sphere, read back through the address prefix. -/
theorem mem_prefixLayer {α : Type*} (slot : Nat) (layer : List (OfficialSparseEntry α))
    (entry : OfficialSparseEntry α) (present : entry ∈ OfficialRuleMajorKey.prefixLayer slot layer) :
    ∃ source, source ∈ layer ∧ (slot :: source.1, source.2) = entry := by
  unfold OfficialRuleMajorKey.prefixLayer at present
  exact List.mem_map.mp present

/-- The indexed sphere of an imaged descriptor is imaged. -/
theorem LocalizedStageDescriptorImage.getD
    {stage : LocalizedCumulativeRule45Stage}
    {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {descriptor : List (List (OfficialSparseEntry (List Nat)))}
    (image : LocalizedStageDescriptorImage stage admitted descriptor) (depth : Nat)
    (entry : OfficialSparseEntry (List Nat)) (present : entry ∈ descriptor.getD depth []) :
    LocalizedStagePriorityImage stage admitted entry.2 := by
  obtain ⟨layer, layerMem, entryMem⟩ := mem_of_mem_getD_nil descriptor depth entry present
  exact image layer layerMem entry entryMem

/-- Merging cumulative descriptor spheres preserves the descriptor image. -/
theorem mergeLocalizedRerootDescriptorChildren_image
    (input : CertifiedLocalizedCIPInput) (stage : LocalizedCumulativeRule45Stage)
    (admitted : Option LocalizedAuxiliaryLabel → Prop)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    (images : ∀ key ∈ children, LocalizedStageDescriptorImage stage admitted key.descriptor) :
    LocalizedStageDescriptorImage stage admitted
      (input.mergeLocalizedRerootDescriptorChildren children) := by
  intro layer layerMem entry entryMem
  unfold mergeLocalizedRerootDescriptorChildren at layerMem
  obtain ⟨depth, _depthMem, rfl⟩ := List.mem_map.mp layerMem
  obtain ⟨⟨key, slot⟩, childMem, entryMem⟩ := List.mem_flatMap.mp entryMem
  obtain ⟨source, sourceMem, rfl⟩ :=
    mem_prefixLayer slot (key.descriptor.getD depth []) entry entryMem
  exact LocalizedStageDescriptorImage.getD
    (images key (List.fst_mem_of_mem_zipIdx childMem)) depth source sourceMem

/-! ## Descriptor image of the actual builder -/

/-- The executable children are exactly the list the frame reader returns. -/
theorem children_eq_executable_of_localizedRerootChildren?
    (input : CertifiedLocalizedCIPInput) {fuel : Nat}
    (cursor : input.LocalizedRerootCursor fuel)
    (children : List (input.LocalizedRerootCursor fuel))
    (computed : input.localizedRerootChildren? cursor = some children) :
    children = input.executableLocalizedRerootChildren cursor := by
  have executable := input.localizedRerootChildren?_eq_some_executable cursor
  rw [executable] at computed
  exact (Option.some.inj computed).symm

/-- Every successful `List.mapM` result element comes from some source element. -/
private theorem list_mapM_member {α β : Type*} (reader : α → Option β) :
    ∀ (values : List α) (results : List β),
      values.mapM reader = some results →
      ∀ result, result ∈ results →
        ∃ value, value ∈ values ∧ reader value = some result
  | [], results, computed, result, present => by
      simp at computed
      subst results
      simp at present
  | value :: values, results, computed, result, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : reader value with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : values.mapM reader with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst results
              rcases List.mem_cons.mp present with same | tailPresent
              · subst result
                exact ⟨value, by simp, headComputed⟩
              · rcases list_mapM_member reader values tail tailComputed result tailPresent with
                  ⟨source, sourcePresent, sourceComputed⟩
                exact ⟨source, List.mem_cons_of_mem value sourcePresent, sourceComputed⟩

/-- A single-sphere terminal descriptor is imaged as soon as its observation is admitted. -/
private theorem terminalDescriptorImage
    (stage : LocalizedCumulativeRule45Stage)
    (admitted : Option LocalizedAuxiliaryLabel → Prop)
    (label : Option LocalizedAuxiliaryLabel) (admittedLabel : admitted label) :
    LocalizedStageDescriptorImage stage admitted
      [[([], localizedCumulativeRule45Priority stage label)]] := by
  intro layer layerMem entry entryMem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at layerMem
  subst layer
  simp only [List.mem_cons, List.not_mem_nil, or_false] at entryMem
  subst entry
  exact ⟨label, admittedLabel, rfl⟩

/-- Prepending an imaged root sphere preserves the descriptor image. -/
private theorem appendRootDescriptorImage
    {stage : LocalizedCumulativeRule45Stage}
    {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {label : Option LocalizedAuxiliaryLabel} (admittedLabel : admitted label)
    {merged : List (List (OfficialSparseEntry (List Nat)))}
    (mergedImage : LocalizedStageDescriptorImage stage admitted merged) :
    LocalizedStageDescriptorImage stage admitted
      ([[([], localizedCumulativeRule45Priority stage label)]] ++ merged) := by
  intro layer layerMem entry entryMem
  rcases List.mem_append.mp layerMem with rootMem | mergedMem
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at rootMem
    subst layer
    simp only [List.mem_cons, List.not_mem_nil, or_false] at entryMem
    subst entry
    exact ⟨label, admittedLabel, rfl⟩
  · exact mergedImage layer mergedMem entry entryMem

/-- Every successful actual build has an imaged descriptor: every descriptor entry reads an
admitted observation through the source stage, at every depth. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptorImage
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (admitted : Option LocalizedAuxiliaryLabel → Prop)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (admittedReads : ∀ cursor,
      Relation.ReflTransGen (E input) start cursor → admitted (read cursor)) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      ∀ key,
        input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel cursor = some key →
        LocalizedStageDescriptorImage stage admitted key.descriptor
  | 0, cursor => by
      intro reachable key computed
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            rw [← computed]
            exact terminalDescriptorImage stage admitted (read cursor)
              (admittedReads cursor reachable)
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor => by
      intro reachable key computed
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            rw [← computed]
            exact terminalDescriptorImage stage admitted (read cursor)
              (admittedReads cursor reachable)
          · have edgeOf : ∀ child ∈ children, E input cursor child := by
              intro child childMem
              have childrenEq := children_eq_executable_of_localizedRerootChildren?
                input cursor children childrenComputed
              have present : child ∈ input.executableLocalizedRerootChildren cursor := by
                rw [← childrenEq]
                exact childMem
              simpa [E] using present
            cases childKeysComputed : children.mapM (fun child =>
                input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel child) with
            | none => simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                rw [← computed]
                apply appendRootDescriptorImage (label := read cursor)
                  (admittedReads cursor reachable)
                apply mergeLocalizedRerootDescriptorChildren_image input stage admitted
                intro childKey childKeyMem
                have present : childKey ∈ childKeys :=
                  (List.Perm.mem_iff
                    (input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys)).mp childKeyMem
                obtain ⟨child, childMem, childComputed⟩ :=
                  list_mapM_member (fun child =>
                    input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel child)
                    children childKeys childKeysComputed childKey present
                exact buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptorImage input stage
                  admitted read start admittedReads fuel child
                  (reachable.tail (edgeOf child childMem)) childKey childComputed

/-! ## The actual builder commutes with the cross-stage extension -/

/-- **Cross-stage builder extension.**  At every actual fuel and every actual cursor reachable from
`start`, if every observation read along the way is admitted, the production builder driven by the
target stage equals the extended key of the production builder driven by the source stage.  The
equality is a full `Option` equality, so a fail-closed `none` is preserved and a successful
compilation is transported at the same cursor and the same fuel. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_extend
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    {stage target : LocalizedCumulativeRule45Stage}
    {admitted : Option LocalizedAuxiliaryLabel → Prop}
    {extend : List Nat → List Nat}
    (nodewise : ∀ (first second : List Nat),
      LocalizedStagePriorityImage stage admitted first →
      LocalizedStagePriorityImage stage admitted second →
      compareLocalizedCumulativeRule45Priority (extend first) (extend second) =
        compareLocalizedCumulativeRule45Priority first second)
    (priorityExtend : ∀ label, admitted label →
      extend (localizedCumulativeRule45Priority stage label) =
        localizedCumulativeRule45Priority target label)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (admittedReads : ∀ cursor,
      Relation.ReflTransGen (E input) start cursor → admitted (read cursor)) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? target read fuel cursor =
        Option.map (input.extendLocalizedRerootCumulativeRule45Key extend)
          (input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel cursor)
  | 0, cursor => by
      intro reachable
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed]
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal, extendLocalizedRerootCumulativeRule45Key,
              extendLocalizedPriorityLayers, extendLocalizedPriorityLayer,
              extendLocalizedPriorityEntry,
              priorityExtend (read cursor) (admittedReads cursor reachable)]
          · simp [childrenComputed, terminal]
  | fuel + 1, cursor => by
      intro reachable
      unfold buildLocalizedRerootCumulativeRule45KeyWithRead?
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed]
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal, extendLocalizedRerootCumulativeRule45Key,
              extendLocalizedPriorityLayers, extendLocalizedPriorityLayer,
              extendLocalizedPriorityEntry,
              priorityExtend (read cursor) (admittedReads cursor reachable)]
          · have edgeOf : ∀ child ∈ children, E input cursor child := by
              intro child childMem
              have childrenEq := children_eq_executable_of_localizedRerootChildren?
                input cursor children childrenComputed
              have present : child ∈ input.executableLocalizedRerootChildren cursor := by
                rw [← childrenEq]
                exact childMem
              simpa [E] using present
            have mapMExtension : ∀ cursors : List (input.LocalizedRerootCursor carrierFuel),
                (∀ child ∈ cursors, Relation.ReflTransGen (E input) start child) →
                (cursors.mapM (fun child =>
                    input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                      target read fuel child)) =
                  Option.map (List.map (input.extendLocalizedRerootCumulativeRule45Key extend))
                    (cursors.mapM (fun child =>
                      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                        stage read fuel child)) := by
              intro cursors
              induction cursors with
              | nil => intro _; rfl
              | cons child children inductionHypothesis =>
                  intro reach
                  rw [List.mapM_cons, List.mapM_cons,
                    buildLocalizedRerootCumulativeRule45KeyWithRead?_extend input nodewise
                      priorityExtend read start admittedReads fuel child (reach child (by simp))]
                  cases computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read
                      fuel child with
                  | none => simp [computed]
                  | some childKey =>
                      cases remaining : List.mapM (fun child =>
                          input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                            stage read fuel child) children with
                      | none => simp [computed, remaining,
                          inductionHypothesis (fun other mem => reach other (by simp [mem]))]
                      | some tails => simp [computed, remaining,
                          inductionHypothesis (fun other mem => reach other (by simp [mem]))]
            cases childKeysComputed : children.mapM (fun child =>
                input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel child) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed,
                  mapMExtension children (fun child mem => reachable.tail (edgeOf child mem))]
            | some childKeys =>
                have targetSome : children.mapM (fun child =>
                    input.buildLocalizedRerootCumulativeRule45KeyWithRead?
                      target read fuel child) =
                    some (childKeys.map (input.extendLocalizedRerootCumulativeRule45Key extend)) := by
                  rw [mapMExtension children (fun child mem => reachable.tail (edgeOf child mem)),
                    childKeysComputed]
                  rfl
                have images : ∀ key ∈ childKeys,
                    LocalizedStageDescriptorImage stage admitted key.descriptor := by
                  intro key keyMem
                  obtain ⟨child, childMem, childComputed⟩ :=
                    list_mapM_member (fun child =>
                      input.buildLocalizedRerootCumulativeRule45KeyWithRead? stage read fuel child)
                      children childKeys childKeysComputed key keyMem
                  exact buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptorImage input stage
                    admitted read start admittedReads fuel child
                    (reachable.tail (edgeOf child childMem)) key childComputed
                simp [childrenComputed, terminal, childKeysComputed, targetSome,
                  extendLocalizedRerootCumulativeRule45Key,
                  extendLocalizedPriorityLayers, extendLocalizedPriorityLayer,
                  extendLocalizedPriorityEntry,
                  priorityExtend (read cursor) (admittedReads cursor reachable),
                  sortLocalizedRerootCumulativeRule45Keys_extend input nodewise childKeys images,
                  mergeLocalizedRerootDescriptorChildren_extendLocalized input extend
                    (input.sortLocalizedRerootCumulativeRule45Keys childKeys),
                  mergeLocalizedRerootLabelChildren_extendLocalized input extend
                    (input.sortLocalizedRerootCumulativeRule45Keys childKeys),
                  mergeLocalizedRerootRankedLabelChildren_extendLocalized input nodewise
                    (input.sortLocalizedRerootCumulativeRule45Keys childKeys)
                    (fun key keyMem =>
                      images key ((List.Perm.mem_iff
                        (input.sortLocalizedRerootCumulativeRule45Keys_perm childKeys)).mp keyMem)),
                  constitutional_comp_extendLocalizedRerootCumulativeRule45Key input extend,
                  List.map_append, List.map_cons, List.map_nil, List.map_map]

/-- Rule-4c stage extension of the actual cumulative builder, under an outward reader that never
returns a lowercase pseudoasymmetric observation. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4c_extension
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (reference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (admittedReads : ∀ cursor,
      Relation.ReflTransGen (E input) start cursor → LocalizedNoPseudoLabel (read cursor)) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4c reference) read fuel cursor =
        Option.map
          (input.extendLocalizedRerootCumulativeRule45Key extendLocalizedRule4bPriorityToRule4c)
          (input.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4b reference) read fuel
            cursor) := by
  intro fuel cursor reachable
  exact buildLocalizedRerootCumulativeRule45KeyWithRead?_extend
    (admitted := LocalizedNoPseudoLabel) input
    (nodewise := fun first second firstImage secondImage =>
      compareLocalizedCumulativeRule45Priority_extend_rule4c_image reference first second
        firstImage secondImage)
    (priorityExtend := fun label admitted =>
      localizedCumulativeRule45Priority_rule4b_extend_rule4c reference label admitted)
    read start admittedReads fuel cursor reachable

/-- Rule-5 stage extension of the actual cumulative builder, under the same outward-admitted
reader.  The Rule-4b and Rule-5 references are independent. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_extension
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (rule4bReference rule5Reference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (admittedReads : ∀ cursor,
      Relation.ReflTransGen (E input) start cursor → LocalizedNoPseudoLabel (read cursor)) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (.rule5 rule4bReference rule5Reference) read fuel cursor =
        Option.map
          (input.extendLocalizedRerootCumulativeRule45Key
            (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference))
          (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
            (.rule4b rule4bReference) read fuel cursor) := by
  intro fuel cursor reachable
  exact buildLocalizedRerootCumulativeRule45KeyWithRead?_extend
    (admitted := LocalizedNoPseudoLabel) input
    (nodewise := fun first second firstImage secondImage =>
      compareLocalizedCumulativeRule45Priority_extend_rule5_image rule4bReference rule5Reference
        first second firstImage secondImage)
    (priorityExtend := fun label admitted =>
      localizedCumulativeRule45Priority_rule4b_extend_rule5 rule4bReference rule5Reference label
        admitted)
    read start admittedReads fuel cursor reachable

/-- A successful actual Rule-4b build yields the actual Rule-4c build of the exact extended key,
at the same cursor and the same fuel. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4c_success
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (reference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (admittedReads : ∀ cursor,
      Relation.ReflTransGen (E input) start cursor → LocalizedNoPseudoLabel (read cursor))
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b reference) read fuel cursor = some key) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? (.rule4c reference) read fuel cursor =
      some
        (input.extendLocalizedRerootCumulativeRule45Key extendLocalizedRule4bPriorityToRule4c
          key) := by
  rw [buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4c_extension input reference read start
    admittedReads fuel cursor reachable, computed]
  rfl

/-- A successful actual Rule-4b build yields the actual Rule-5 build of the exact extended key, at
the same cursor and the same fuel. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_success
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
      (.rule4b rule4bReference) read fuel cursor = some key) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        (.rule5 rule4bReference rule5Reference) read fuel cursor =
      some
        (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference) key) := by
  rw [buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_extension input rule4bReference
    rule5Reference read start admittedReads fuel cursor reachable, computed]
  rfl

/-! ## Projection back to the Rule-4b descriptor -/

/-- On admitted observations the Rule-4c extension keeps the two leading components. -/
theorem extendLocalizedRule4bPriorityToRule4c_take_two (reference : RS) {vector : List Nat}
    (image : LocalizedStagePriorityImage (.rule4b reference) LocalizedNoPseudoLabel vector) :
    (extendLocalizedRule4bPriorityToRule4c vector).take 2 = vector := by
  obtain ⟨label, admitted, rfl⟩ := image
  cases label with
  | none => rfl
  | some label =>
      cases label with
      | pseudoasymmetric descriptor => exact admitted.elim
      | chiral descriptor => rfl

/-- On admitted observations the Rule-5 extension keeps the two leading components, for any pair
of Rule-4b and Rule-5 references. -/
theorem extendLocalizedRule4bPriorityToRule5_take_two (rule4bReference rule5Reference : RS)
    {vector : List Nat}
    (image : LocalizedStagePriorityImage (.rule4b rule4bReference) LocalizedNoPseudoLabel vector) :
    (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference vector).take 2 = vector := by
  obtain ⟨label, admitted, rfl⟩ := image
  cases label with
  | none => rfl
  | some label =>
      cases label with
      | pseudoasymmetric descriptor => exact admitted.elim
      | chiral descriptor => rfl

/-- Taking the first two components of an extended sphere recovers the source sphere exactly. -/
theorem extendLocalizedPriorityLayer_take_two (extend : List Nat → List Nat)
    (layer : List (OfficialSparseEntry (List Nat)))
    (takeTwo : ∀ entry ∈ layer, (extend entry.2).take 2 = entry.2) :
    (layer.map (extendLocalizedPriorityEntry extend)).map
        (fun entry : OfficialSparseEntry (List Nat) => (entry.1, entry.2.take 2)) =
      layer := by
  rw [List.map_map]
  have step : layer.map ((fun entry : OfficialSparseEntry (List Nat) =>
      (entry.1, entry.2.take 2)) ∘ extendLocalizedPriorityEntry extend) = layer.map id := by
    apply List.map_congr_left
    intro entry entryMem
    simp only [Function.comp_apply, extendLocalizedPriorityEntry_fst,
      extendLocalizedPriorityEntry_snd, takeTwo entry entryMem, Prod.mk.eta, id_eq]
  rw [step, List.map_id]

/-- Taking the first two components of an extended descriptor recovers the source descriptor
exactly, sphere by sphere. -/
theorem extendLocalizedPriorityLayers_take_two (extend : List Nat → List Nat)
    (layers : List (List (OfficialSparseEntry (List Nat))))
    (takeTwo : ∀ layer ∈ layers, ∀ entry ∈ layer, (extend entry.2).take 2 = entry.2) :
    (extendLocalizedPriorityLayers extend layers).map
        (List.map fun entry : OfficialSparseEntry (List Nat) => (entry.1, entry.2.take 2)) =
      layers := by
  unfold extendLocalizedPriorityLayers
  rw [List.map_map]
  have step : layers.map ((List.map fun entry : OfficialSparseEntry (List Nat) =>
      (entry.1, entry.2.take 2)) ∘ extendLocalizedPriorityLayer extend) = layers.map id := by
    apply List.map_congr_left
    intro layer layerMem
    simp only [Function.comp_apply]
    exact extendLocalizedPriorityLayer_take_two extend layer
      (fun entry entryMem => takeTwo layer layerMem entry entryMem)
  rw [step, List.map_id]

/-- The projected descriptor of an extended key recovers the source descriptor exactly. -/
theorem extendLocalizedRerootCumulativeRule45Key_descriptor_take_two
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (takeTwo : ∀ layer ∈ key.descriptor, ∀ entry ∈ layer, (extend entry.2).take 2 = entry.2) :
    (input.extendLocalizedRerootCumulativeRule45Key extend key).descriptor.map
        (List.map fun entry : OfficialSparseEntry (List Nat) => (entry.1, entry.2.take 2)) =
      key.descriptor := by
  simpa only [extendLocalizedRerootCumulativeRule45Key_descriptor] using
    extendLocalizedPriorityLayers_take_two extend key.descriptor takeTwo

/-- The projected Rule-5 descriptor recovers the Rule-4b descriptor exactly at the same cursor and
fuel, whether or not the build succeeds. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_descriptor_projection
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (rule4bReference rule5Reference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (admittedReads : ∀ cursor,
      Relation.ReflTransGen (E input) start cursor → LocalizedNoPseudoLabel (read cursor))
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor) :
    Option.map
        (fun built : input.LocalizedRerootCumulativeRule45Key =>
          built.descriptor.map
            (List.map fun entry : OfficialSparseEntry (List Nat) => (entry.1, entry.2.take 2)))
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (.rule5 rule4bReference rule5Reference) read fuel cursor) =
      Option.map (fun built : input.LocalizedRerootCumulativeRule45Key => built.descriptor)
        (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (.rule4b rule4bReference) read fuel cursor) := by
  rw [buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_extension input rule4bReference
    rule5Reference read start admittedReads fuel cursor reachable]
  cases computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b rule4bReference) read fuel cursor with
  | none => rfl
  | some key =>
      simp only [Option.map_some, Option.some.injEq]
      exact extendLocalizedRerootCumulativeRule45Key_descriptor_take_two input
        (extendLocalizedRule4bPriorityToRule5 rule4bReference rule5Reference) key
        (fun layer layerMem entry entryMem =>
          extendLocalizedRule4bPriorityToRule5_take_two rule4bReference rule5Reference
            (buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptorImage input
              (.rule4b rule4bReference) LocalizedNoPseudoLabel read start admittedReads fuel cursor
              reachable key computed layer layerMem entry entryMem))

/-! ## The no-reference branch

When every reachable observation is absent, the Rule-4a stage extends exactly to the no-reference
Rule-4c and Rule-5 stages.  The all-`none` restriction is essential here: the no-reference stages
carry no Rule-4b bit, and `adding5` can reorder an `R`/`S` tie, so an all-`none` hypothesis is not
interchangeable with the none-or-chiral hypothesis of the referenced branch. -/

/-- Extend a one-component Rule-4a cumulative vector to the no-reference Rule-4c stage. -/
def extendLocalizedRule4aPriorityToRule4cNoReference (vector : List Nat) : List Nat :=
  match vector with
  | kind :: _ => [kind, 0]
  | _ => vector

/-- Extend a one-component Rule-4a cumulative vector to the no-reference Rule-5 stage. -/
def extendLocalizedRule4aPriorityToRule5NoRule4bReference
    (_rule5Reference : RS) (vector : List Nat) : List Nat :=
  match vector with
  | kind :: _ => [kind, 0, 0]
  | _ => vector

/-- The Rule-4a vector of an absent observation extends to the no-reference Rule-4c vector. -/
theorem localizedCumulativeRule45Priority_rule4a_extend_rule4cNoReference
    (label : Option LocalizedAuxiliaryLabel) (admitted : label = none) :
    extendLocalizedRule4aPriorityToRule4cNoReference
        (localizedCumulativeRule45Priority .rule4a label) =
      localizedCumulativeRule45Priority .rule4cNoReference label := by
  subst label
  rfl

/-- The Rule-4a vector of an absent observation extends to the no-reference Rule-5 vector. -/
theorem localizedCumulativeRule45Priority_rule4a_extend_rule5NoRule4bReference
    (rule5Reference : RS) (label : Option LocalizedAuxiliaryLabel) (admitted : label = none) :
    extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference
        (localizedCumulativeRule45Priority .rule4a label) =
      localizedCumulativeRule45Priority (.rule5NoRule4bReference rule5Reference) label := by
  subst label
  rfl

/-- Image form of the no-reference Rule-4c node comparison transport. -/
theorem compareLocalizedCumulativeRule45Priority_extend_rule4cNoReference_image
    (first second : List Nat)
    (firstImage : LocalizedStagePriorityImage .rule4a (fun label => label = none) first)
    (secondImage : LocalizedStagePriorityImage .rule4a (fun label => label = none) second) :
    compareLocalizedCumulativeRule45Priority (extendLocalizedRule4aPriorityToRule4cNoReference first)
        (extendLocalizedRule4aPriorityToRule4cNoReference second) =
      compareLocalizedCumulativeRule45Priority first second := by
  obtain ⟨firstLabel, firstNone, rfl⟩ := firstImage
  obtain ⟨secondLabel, secondNone, rfl⟩ := secondImage
  subst firstLabel
  subst secondLabel
  rfl

/-- Image form of the no-reference Rule-5 node comparison transport. -/
theorem compareLocalizedCumulativeRule45Priority_extend_rule5NoRule4bReference_image
    (rule5Reference : RS) (first second : List Nat)
    (firstImage : LocalizedStagePriorityImage .rule4a (fun label => label = none) first)
    (secondImage : LocalizedStagePriorityImage .rule4a (fun label => label = none) second) :
    compareLocalizedCumulativeRule45Priority
        (extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference first)
        (extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference second) =
      compareLocalizedCumulativeRule45Priority first second := by
  obtain ⟨firstLabel, firstNone, rfl⟩ := firstImage
  obtain ⟨secondLabel, secondNone, rfl⟩ := secondImage
  subst firstLabel
  subst secondLabel
  rfl

/-- The no-reference Rule-4c extension keeps the Rule-4a component. -/
theorem extendLocalizedRule4aPriorityToRule4cNoReference_take_one {vector : List Nat}
    (image : LocalizedStagePriorityImage .rule4a (fun label => label = none) vector) :
    (extendLocalizedRule4aPriorityToRule4cNoReference vector).take 1 = vector := by
  obtain ⟨label, labelNone, rfl⟩ := image
  subst label
  rfl

/-- The no-reference Rule-5 extension keeps the Rule-4a component. -/
theorem extendLocalizedRule4aPriorityToRule5NoRule4bReference_take_one
    (rule5Reference : RS) {vector : List Nat}
    (image : LocalizedStagePriorityImage .rule4a (fun label => label = none) vector) :
    (extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference vector).take 1 = vector := by
  obtain ⟨label, labelNone, rfl⟩ := image
  subst label
  rfl

/-- No-reference Rule-4c stage extension of the actual cumulative builder, under a reader that is
absent at every reachable cursor. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4cNoReference_extension
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (noReads : ∀ cursor, Relation.ReflTransGen (E input) start cursor → read cursor = none) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4cNoReference read fuel cursor =
        Option.map
          (input.extendLocalizedRerootCumulativeRule45Key
            extendLocalizedRule4aPriorityToRule4cNoReference)
          (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel cursor) := by
  intro fuel cursor reachable
  exact buildLocalizedRerootCumulativeRule45KeyWithRead?_extend
    (admitted := fun label => label = none) input
    (nodewise := fun first second firstImage secondImage =>
      compareLocalizedCumulativeRule45Priority_extend_rule4cNoReference_image first second
        firstImage secondImage)
    (priorityExtend := fun label admitted =>
      localizedCumulativeRule45Priority_rule4a_extend_rule4cNoReference label admitted)
    read start noReads fuel cursor reachable

/-- No-reference Rule-5 stage extension of the actual cumulative builder, under a reader that is
absent at every reachable cursor. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5NoRule4bReference_extension
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (rule5Reference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (noReads : ∀ cursor, Relation.ReflTransGen (E input) start cursor → read cursor = none) :
    ∀ (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel),
      Relation.ReflTransGen (E input) start cursor →
      input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (.rule5NoRule4bReference rule5Reference) read fuel cursor =
        Option.map
          (input.extendLocalizedRerootCumulativeRule45Key
            (extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference))
          (input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel cursor) := by
  intro fuel cursor reachable
  exact buildLocalizedRerootCumulativeRule45KeyWithRead?_extend
    (admitted := fun label => label = none) input
    (nodewise := fun first second firstImage secondImage =>
      compareLocalizedCumulativeRule45Priority_extend_rule5NoRule4bReference_image rule5Reference
        first second firstImage secondImage)
    (priorityExtend := fun label admitted =>
      localizedCumulativeRule45Priority_rule4a_extend_rule5NoRule4bReference rule5Reference label
        admitted)
    read start noReads fuel cursor reachable

/-- A successful actual Rule-4a build yields the actual no-reference Rule-4c build of the exact
extended key, at the same cursor and the same fuel. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4cNoReference_success
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (noReads : ∀ cursor, Relation.ReflTransGen (E input) start cursor → read cursor = none)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel cursor =
      some key) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4cNoReference read fuel cursor =
      some
        (input.extendLocalizedRerootCumulativeRule45Key
          extendLocalizedRule4aPriorityToRule4cNoReference key) := by
  rw [buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4cNoReference_extension input read start
    noReads fuel cursor reachable, computed]
  rfl

/-- A successful actual Rule-4a build yields the actual no-reference Rule-5 build of the exact
extended key, at the same cursor and the same fuel. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5NoRule4bReference_success
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (rule5Reference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (noReads : ∀ cursor, Relation.ReflTransGen (E input) start cursor → read cursor = none)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead? .rule4a read fuel cursor =
      some key) :
    input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        (.rule5NoRule4bReference rule5Reference) read fuel cursor =
      some
        (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4aPriorityToRule5NoRule4bReference rule5Reference) key) := by
  rw [buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5NoRule4bReference_extension input
    rule5Reference read start noReads fuel cursor reachable, computed]
  rfl

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedNoPseudoLabel
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedStagePriorityImage
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedStageDescriptorImage
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRule4bPriorityToRule4c
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRule4bPriorityToRule5
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedPriorityEntry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedPriorityLayer
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedPriorityLayers
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRerootCumulativeRule45Key
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedPriorityEntry_fst
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedPriorityEntry_snd
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRerootCumulativeRule45Key_constitutional
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRerootCumulativeRule45Key_descriptor
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRerootCumulativeRule45Key_labels
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRerootCumulativeRule45Key_rankedLabels
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.constitutional_comp_extendLocalizedRerootCumulativeRule45Key
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCumulativeRule45Priority_rule4b_extend_rule4c
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCumulativeRule45Priority_rule4b_extend_rule5
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCumulativeRule45Priority_rule4b_injective
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedCumulativeRule45Priority_extend_rule4c
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedCumulativeRule45Priority_extend_rule5
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedCumulativeRule45Priority_extend_rule4c_image
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedCumulativeRule45Priority_extend_rule5_image
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareSparseEntry_extendLocalizedPriorityEntry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareSparseLayer_extendLocalizedPriorityLayer
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareSparseLayers_extendLocalizedPriorityLayers
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedRerootCumulativeRule45Keys_extend
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.insertLocalizedRerootCumulativeRule45Key_extend
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.sortLocalizedRerootCumulativeRule45Keys_extend
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootDescriptorChildLayerCount_extendLocalized
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootLabelChildLayerCount_extendLocalized
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRankedLabelChildLayerCount_extendLocalized
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedPriorityLayers_getD
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.prefixLayer_extendLocalizedPriorityEntry
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mergeLocalizedRerootDescriptorChildren_extendLocalized
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mergeLocalizedRerootLabelChildren_extendLocalized
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRankedChildTail_extendLocalized
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedRerootRankedChildren_extendLocalized
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mergeLocalizedRerootRankedLabelChildren_extendLocalized
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mem_prefixLayer
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.LocalizedStageDescriptorImage.getD
/-- The extension keeps the constitutional, exact-label and ranked-label projections literally. -/
theorem extendLocalizedRerootCumulativeRule45Key_projections
    (input : CertifiedLocalizedCIPInput) (extend : List Nat → List Nat)
    (key : input.LocalizedRerootCumulativeRule45Key) :
    (input.extendLocalizedRerootCumulativeRule45Key extend key).constitutional =
        key.constitutional ∧
      (input.extendLocalizedRerootCumulativeRule45Key extend key).labels = key.labels ∧
        (input.extendLocalizedRerootCumulativeRule45Key extend key).rankedLabels =
          key.rankedLabels :=
  ⟨rfl, rfl, rfl⟩

/-- Both common-reference Rule-5 keys (`R` and `S`) are exact extensions of one successful
Rule-4b key, at the same cursor and the same fuel. -/
theorem buildLocalizedRerootCumulativeRule45KeyWithRead?_common_reference_extensions
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat} (rule4bReference : RS)
    (read : input.LocalizedRerootCursor carrierFuel → Option LocalizedAuxiliaryLabel)
    (start : input.LocalizedRerootCursor carrierFuel)
    (admittedReads : ∀ cursor,
      Relation.ReflTransGen (E input) start cursor → LocalizedNoPseudoLabel (read cursor))
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reachable : Relation.ReflTransGen (E input) start cursor)
    (key : input.LocalizedRerootCumulativeRule45Key)
    (computed : input.buildLocalizedRerootCumulativeRule45KeyWithRead?
      (.rule4b rule4bReference) read fuel cursor = some key) :
    (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
        (.rule5 rule4bReference RS.R) read fuel cursor =
      some
        (input.extendLocalizedRerootCumulativeRule45Key
          (extendLocalizedRule4bPriorityToRule5 rule4bReference RS.R) key)) ∧
      (input.buildLocalizedRerootCumulativeRule45KeyWithRead?
          (.rule5 rule4bReference RS.S) read fuel cursor =
        some
          (input.extendLocalizedRerootCumulativeRule45Key
            (extendLocalizedRule4bPriorityToRule5 rule4bReference RS.S) key)) :=
  ⟨buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_success input rule4bReference RS.R read
      start admittedReads fuel cursor reachable key computed,
    buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_success input rule4bReference RS.S read
      start admittedReads fuel cursor reachable key computed⟩

assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.mergeLocalizedRerootDescriptorChildren_image
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRerootCumulativeRule45Key_projections
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_common_reference_extensions
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.children_eq_executable_of_localizedRerootChildren?
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_descriptorImage
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_extend
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4c_extension
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_extension
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4c_success
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_success
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRule4bPriorityToRule4c_take_two
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRule4bPriorityToRule5_take_two
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedPriorityLayer_take_two
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedPriorityLayers_take_two
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRerootCumulativeRule45Key_descriptor_take_two
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5_descriptor_projection
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRule4aPriorityToRule4cNoReference
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRule4aPriorityToRule5NoRule4bReference
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCumulativeRule45Priority_rule4a_extend_rule4cNoReference
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.localizedCumulativeRule45Priority_rule4a_extend_rule5NoRule4bReference
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedCumulativeRule45Priority_extend_rule4cNoReference_image
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.compareLocalizedCumulativeRule45Priority_extend_rule5NoRule4bReference_image
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRule4aPriorityToRule4cNoReference_take_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.extendLocalizedRule4aPriorityToRule5NoRule4bReference_take_one
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4cNoReference_extension
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5NoRule4bReference_extension
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule4cNoReference_success
assert_kernel_only TetraStereo.OneCenter.CertifiedLocalizedCIPInput.buildLocalizedRerootCumulativeRule45KeyWithRead?_rule5NoRule4bReference_success

end CertifiedLocalizedCIPInput

end TetraStereo.OneCenter
