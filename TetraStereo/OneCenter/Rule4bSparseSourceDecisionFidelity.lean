import TetraStereo.KernelOnly
import TetraStereo.OneCenter.CIPBlueBookConformance
import TetraStereo.OneCenter.LocalizedRerootCompoundRule4bcKey

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace Rule4bSparseSource

open CertifiedLocalizedCIPInput

/-!
# Independent Rule-4b source decisions for the actual sparse encodings

## Scope and gap

`CIPBlueBookConformance` proves that the *primitive* descriptor comparators agree with an
independent transcription of IUPAC P-92, including the Rule-4b reference-count judgment
`rule4bReferenceCountDecision` (one reference precedes two) and the like/unlike pair judgment
`rule4bPairDecision` (like precedes unlike).  The actual localized engine, however, does not
compare those primitive values directly:

* `localizedCumulativeRule45Priority (.rule4b reference) label` encodes one node as the numeric
  vector `[rule4aPriority, rule4bPriority]`;
* `compareLocalizedCumulativeRule45Priority` is lexicographic comparison of such vectors;
* `OfficialRuleMajorKey.compareSparseEntry/Layer/Layers` compares addressed sparse observations,
  first by the reversed lexicographic position address and then by the observation comparator;
* `compareLocalizedRerootCompoundRule4bcAfterRule4a` compares
  `referenceCountPriority`, then the Rule-4b reading lists, then the Rule-4c reading lists.

This module closes the source-conformance gap *at that actual layer* by defining an independent
symbolic source semantics and proving that the actual encodings and sparse comparators realize it.
The connection is a comparison-order fidelity result: it says that the actual comparator returns
the independent P-92 judgment.  It does **not** assert that the populated actual reader's labels
are physically faithful stereochemistry; that is a separate, unproved physical-reader obligation.

## Proved endpoints

* The actual Rule-4a/Rule-4b cumulative priority vectors decode to source observations, and
  `compareLocalizedCumulativeRule45Priority` realizes the first-applicable source judgment.
* One/two reference counts are compared by *order*: production `2/1` and P-92 `1/0` yield the
  same decision; the numeric values are never identified.  An empty population is explicitly
  outside the one/two domain, and the actual population selector is proved to return empty, one,
  or two references only.
* The actual sparse entry/layer/layer-list comparators realize the source address-first and
  observation-second decisions, with an independently defined path precedence.
* The actual cumulative builder's `descriptor` entries all have the expected stage-vector shape;
  the root position is identified; and the whole descriptor erases to source observations.  These
  facts are derived from the builder, not assumed from raw `sourceNodes`.
* The actual compound comparison at an exact Rule-4a tie realizes the source count-then-Rule-4b
  reading judgment.  On a full source tie the unchanged actual Rule-4c reading comparison is
  exposed; it is not renamed as a Rule-4b result.  The actual compound builder's readings erase to
  source readings, and its stored count priority is derived from the builder's declarative
  soundness theorem.
* End-to-end corollaries discharge the erasure and priority-field hypotheses directly from
  successful actual builder runs: `sourceBuildCumulative_comparison_realizes_source`,
  `sourceBuildCompound_afterRule4a_realizes_source`, and
  `sourceBuildCompoundKeys_realizes_source_at_rule4aTie`.

## Independent source judgments used

Only the P-92 judgments already transcribed in `CIPBlueBookConformance.BlueBookP92` are used for
the Rule-4b decisions: `rule4bReferenceCountDecision` on the one/two-reference domain and
`rule4bPairDecision` on `like`/`unlike`.  Rule 4a is preserved as a *preceding-rule tie gate*: the
Rule-4b pair is consulted only after the Rule-4a class comparison ties.

## Honest representation boundaries

* A missing label (`none`) is represented as `unavailable`/absent.  It is **not** identified with
  chemical nonstereogenicity.  Its comparison position is an explicit encoding fact (it orders
  below an observed chiral or pseudoasymmetric class), not a chemical claim.
* Uppercase `CIP` descriptors are decoded relative to the selected reference: equal to the
  reference means `like`, otherwise `unlike`.  Other labels (absent and lowercase
  pseudoasymmetric) are retained as `absent`/`deferred`; no Rule-4b pair is invented for them.
* A Rule-4a-only key (no selected reference) has no pair layer.  It is represented by
  `rule4aOnly`, which is distinct from a two-component vector whose pair is merely unavailable.
* The empty reference population has no P-92 one/two reference count.  It is kept explicitly
  outside the source count domain (`sourceRule4bReferenceCount? = none`); the conformance theorem
  is stated only for lists that actually decode to one or two references.
* Production stores one reference as priority `2` and two as priority `1`; P-92 stores `1` and
  `0`.  Only the comparison *order* is identified, never the numeric values.
* Rule 4c decoding is deliberately out of scope (the sibling Rule-4c/5 module owns it).  The
  compound characterization falls through to the unchanged actual Rule-4c comparator on a full
  Rule-4b tie.

## Source observations are erasures of the actual sparse key

The source observations are obtained by decoding the *actual* `descriptor` vectors produced by
`buildLocalizedRerootCumulativeRule45Key?`.  They are not read from `constitutional.sourceNodes`,
and no alignment of raw source nodes with sparse positions is assumed.  The decodability and
root-position correspondence are derived from the actual builder (Part 4), and the per-reading
descriptor erasure used by the compound endpoint is derived from the actual reading and compound
builders (Part 5).

## Residual assumptions / scope

* No physical stereochemistry is asserted.  In particular, the source decode of an uppercase
  chiral descriptor is relative to the selected reference and is only a like/unlike decision.
* `unavailable` is absence of an observed label, not chemical nonstereogenicity.
* Rule 4c decoding and Rule-4c source semantics are out of scope; the compound endpoint returns
  the unchanged actual Rule-4c comparator on a full Rule-4b tie.
* The compound source theorem is stated on reference lists that decode to one or two counts.
  Empty lists are explicitly outside the domain; the actual selector is separately proved to be
  empty, one, or two, so no other case is hidden.
* The `referenceCountPriority` field-reflection hypotheses in the compound theorem are the
  declarative meaning of a compiled key and are derived for builder output by
  `sourceBuildCompound_referenceCountPriority`; they are not extra source choices.
-/

/-! ## Part 1: independent source classes decoded from the Rule-4a/Rule-4b vector -/

/-- Source Rule-4a classes.  `unavailable` records that no label was observed; it is deliberately
kept distinct from P-92's `nonstereogenic` class. -/
inductive SourceRule4aClass where
  | unavailable
  | pseudoasymmetricDeferred
  | chiral
  deriving DecidableEq, Repr

/-- Explicit comparison position of the source classes.  This is an encoding of the
preceding-rule gate only; in particular `unavailable` is not claimed to be chemically
nonstereogenic. -/
def sourceRule4aClassPriority : SourceRule4aClass → Nat
  | .unavailable => 0
  | .pseudoasymmetricDeferred => 1
  | .chiral => 2

/-- The preceding-Rule-4a tie gate on source classes. -/
def sourceRule4aGateDecision (left right : SourceRule4aClass) : Ordering :=
  BlueBookP92.higherNatDecision
    (sourceRule4aClassPriority left) (sourceRule4aClassPriority right)

/-- Total syntactic translation into the independent P-92 Rule-4a vocabulary.  The image of
`unavailable` is used only as a totalization; every theorem that invokes the P-92 decision carries
explicit availability hypotheses, so absence is never *asserted* to be nonstereogenic. -/
def sourceRule4aClassToP92 : SourceRule4aClass → BlueBookP92.Rule4aClass
  | .unavailable => .nonstereogenic
  | .pseudoasymmetricDeferred => .pseudoasymmetric
  | .chiral => .chiral

/-- On available classes the source gate is exactly the independent P-92 Rule-4a decision. -/
theorem sourceRule4aGateDecision_eq_rule4aDecision_of_available
    (left right : SourceRule4aClass)
    (leftAvailable : left ≠ .unavailable) (rightAvailable : right ≠ .unavailable) :
    sourceRule4aGateDecision left right =
      BlueBookP92.rule4aDecision
        (sourceRule4aClassToP92 left) (sourceRule4aClassToP92 right) := by
  rcases left with _ | _ | _ <;> rcases right with _ | _ | _ <;>
    simp_all [sourceRule4aGateDecision, sourceRule4aClassPriority,
      sourceRule4aClassToP92, BlueBookP92.rule4aDecision,
      BlueBookP92.rule4aPriority, BlueBookP92.higherNatDecision]

/-- One independent source observation of an encoded cumulative vector.

`rule4aOnly` corresponds to the one-component vector of a Rule-4a-only key (no reference was
selected).  `withRule4b` corresponds to the two-component vector of a Rule-4b reading.  The pair
component is `none` precisely for absent/deferred labels, for which no like/unlike pair exists. -/
inductive SourceRule45Observation where
  | rule4aOnly (rule4a : SourceRule4aClass)
  | withRule4b (rule4a : SourceRule4aClass)
      (pair? : Option BlueBookP92.Rule4bPairClass)
  deriving DecidableEq, Repr

/-- The preceding Rule-4a class of a source observation. -/
def SourceRule45Observation.rule4aClass :
    SourceRule45Observation → SourceRule4aClass
  | .rule4aOnly rule4a => rule4a
  | .withRule4b rule4a _ => rule4a

/-- The Rule-4b pair observed at a source observation, when there is one. -/
def SourceRule45Observation.pair? :
    SourceRule45Observation → Option BlueBookP92.Rule4bPairClass
  | .rule4aOnly _ => none
  | .withRule4b _ pair? => pair?

/-- First-applicable source judgment for one encoded node.

The preceding Rule-4a gate is applied first.  Only on an exact Rule-4a tie is the Rule-4b
like/unlike judgment used, and only between two observed chiral pairs.  When one vector has no
pair layer and the other does, the sparse length decides (the shorter vector is the first
difference), which is the explicit structural ordering of the encoding, not a chemical
like/unlike claim. -/
def sourceRule45ObservationDecision
    (left right : SourceRule45Observation) : Ordering :=
  match sourceRule4aGateDecision left.rule4aClass right.rule4aClass with
  | .eq =>
      match left, right with
      | .rule4aOnly _, .rule4aOnly _ => .eq
      | .rule4aOnly _, .withRule4b _ _ => .lt
      | .withRule4b _ _, .rule4aOnly _ => .gt
      | .withRule4b _ none, .withRule4b _ none => .eq
      | .withRule4b _ none, .withRule4b _ (some _) => .lt
      | .withRule4b _ (some _), .withRule4b _ none => .gt
      | .withRule4b _ (some leftPair), .withRule4b _ (some rightPair) =>
          BlueBookP92.rule4bPairDecision leftPair rightPair
  | decision => decision

/-- Decode a one-component Rule-4a vector. -/
def sourceObserveRule4aLabel :
    Option LocalizedAuxiliaryLabel → SourceRule45Observation
  | none => .rule4aOnly .unavailable
  | some (.pseudoasymmetric _) => .rule4aOnly .pseudoasymmetricDeferred
  | some (.chiral _) => .rule4aOnly .chiral

/-- Decode a two-component Rule-4b vector relative to the selected reference.  Only uppercase
chiral descriptors produce a pair: equality with the reference is `like`, everything else is
`unlike`.  Absent and lowercase labels stay absent/deferred. -/
def sourceObserveRule4bLabel :
    RS → Option LocalizedAuxiliaryLabel → SourceRule45Observation
  | _, none => .withRule4b .unavailable none
  | _, some (.pseudoasymmetric _) => .withRule4b .pseudoasymmetricDeferred none
  | reference, some (.chiral descriptor) =>
      .withRule4b .chiral
        (some (if descriptor == reference then .like else .unlike))

/-- Decode an actual sparse priority vector into a source observation.  The accepted vectors are
exactly the ones produced by the Rule-4a and Rule-4b cumulative stages. -/
def sourceDecodeRule45Vector? : List Nat → Option SourceRule45Observation
  | [0] => some (.rule4aOnly .unavailable)
  | [1] => some (.rule4aOnly .pseudoasymmetricDeferred)
  | [2] => some (.rule4aOnly .chiral)
  | [0, 0] => some (.withRule4b .unavailable none)
  | [1, 0] => some (.withRule4b .pseudoasymmetricDeferred none)
  | [2, 0] => some (.withRule4b .chiral (some .unlike))
  | [2, 1] => some (.withRule4b .chiral (some .like))
  | _ => none

/-- The actual Rule-4a cumulative vector decodes to the absent/pseudo/chiral source observation. -/
theorem sourceDecodeRule45Vector?_rule4a
    (label : Option LocalizedAuxiliaryLabel) :
    sourceDecodeRule45Vector?
        (localizedCumulativeRule45Priority .rule4a label) =
      some (sourceObserveRule4aLabel label) := by
  cases label with
  | none => rfl
  | some label => cases label <;> rfl

/-- The actual Rule-4b cumulative vector decodes to the reference-relative source observation. -/
theorem sourceDecodeRule45Vector?_rule4b
    (reference : RS) (label : Option LocalizedAuxiliaryLabel) :
    sourceDecodeRule45Vector?
        (localizedCumulativeRule45Priority (.rule4b reference) label) =
      some (sourceObserveRule4bLabel reference label) := by
  cases reference <;> cases label with
  | none => rfl
  | some label =>
      cases label with
      | pseudoasymmetric descriptor => rfl
      | chiral descriptor => cases descriptor <;> rfl

/-- Every Rule-4a or Rule-4b cumulative vector decodes to a source observation. -/
theorem sourceDecodeRule45Vector?_cumulativePriority
    (stage : LocalizedCumulativeRule45Stage)
    (label : Option LocalizedAuxiliaryLabel)
    (compatible : stage = .rule4a ∨ ∃ reference, stage = .rule4b reference) :
    ∃ observation, sourceDecodeRule45Vector?
        (localizedCumulativeRule45Priority stage label) = some observation := by
  rcases compatible with rfl | ⟨reference, rfl⟩
  · exact ⟨sourceObserveRule4aLabel label, sourceDecodeRule45Vector?_rule4a label⟩
  · exact ⟨sourceObserveRule4bLabel reference label,
      sourceDecodeRule45Vector?_rule4b reference label⟩

/-- Complete enumeration of the decodable vectors. -/
theorem sourceDecodeRule45Vector?_eq_some_iff
    (vector : List Nat) (observation : SourceRule45Observation) :
    sourceDecodeRule45Vector? vector = some observation ↔
      (vector = [0] ∧ observation = .rule4aOnly .unavailable) ∨
      (vector = [1] ∧ observation = .rule4aOnly .pseudoasymmetricDeferred) ∨
      (vector = [2] ∧ observation = .rule4aOnly .chiral) ∨
      (vector = [0, 0] ∧ observation = .withRule4b .unavailable none) ∨
      (vector = [1, 0] ∧
        observation = .withRule4b .pseudoasymmetricDeferred none) ∨
      (vector = [2, 0] ∧ observation = .withRule4b .chiral (some .unlike)) ∨
      (vector = [2, 1] ∧ observation = .withRule4b .chiral (some .like)) := by
  constructor
  · intro decoded
    unfold sourceDecodeRule45Vector? at decoded
    repeat' split at decoded
    all_goals simp_all
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> rfl

/-! ## Part 2: the encoded comparison realizes the source judgment -/

/-- **Actual encoded priority vectors realize the source judgment.**  For any two sparse priority
vectors that decode to source observations, lexicographic comparison of the vectors is exactly the
source Rule-4a-then-Rule-4b judgment.  No desired comparator output is supplied. -/
theorem compareLocalizedCumulativeRule45Priority_realizes_source
    (leftVector rightVector : List Nat)
    (leftObservation rightObservation : SourceRule45Observation)
    (leftDecoded : sourceDecodeRule45Vector? leftVector = some leftObservation)
    (rightDecoded : sourceDecodeRule45Vector? rightVector = some rightObservation) :
    compareLocalizedCumulativeRule45Priority leftVector rightVector =
      sourceRule45ObservationDecision leftObservation rightObservation := by
  rcases (sourceDecodeRule45Vector?_eq_some_iff leftVector leftObservation).mp
    leftDecoded with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rcases (sourceDecodeRule45Vector?_eq_some_iff rightVector rightObservation).mp
    rightDecoded with
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
  rfl

/-! ## Part 3: reference-count conformance on the one/two-reference domain -/

/-- Independent source decoding of a selected reference population.

P-92.5.2.1(c)(i) distinguishes one reference from two.  An empty population (no uppercase
reference was selected) has no such count, and neither has any longer list; both are explicitly
outside the domain and return `none`. -/
def sourceRule4bReferenceCount? : List RS → Option BlueBookP92.Rule4bReferenceCount
  | [_] => some .one
  | [_, _] => some .two
  | _ => none

/-- Complete enumeration of the source count domain.  In particular the empty list is not
decodable: absence of a reference is outside the one/two domain, not a third source count. -/
theorem sourceRule4bReferenceCount?_eq_some_iff (references : List RS)
    (count : BlueBookP92.Rule4bReferenceCount) :
    sourceRule4bReferenceCount? references = some count ↔
      (∃ reference, references = [reference] ∧ count = .one) ∨
      (∃ first second, references = [first, second] ∧ count = .two) := by
  constructor
  · intro decoded
    cases references with
    | nil => simp [sourceRule4bReferenceCount?] at decoded
    | cons first rest =>
        cases rest with
        | nil =>
            exact Or.inl ⟨first, rfl, by
              simpa [sourceRule4bReferenceCount?] using decoded.symm⟩
        | cons second rest =>
            cases rest with
            | nil =>
                exact Or.inr ⟨first, second, rfl, by
                  simpa [sourceRule4bReferenceCount?] using decoded.symm⟩
            | cons third rest =>
                simp [sourceRule4bReferenceCount?] at decoded
  · rintro (⟨reference, rfl, rfl⟩ | ⟨first, second, rfl, rfl⟩) <;> rfl

/-- The empty population is explicitly outside the source count domain. -/
@[simp] theorem sourceRule4bReferenceCount?_empty :
    sourceRule4bReferenceCount? [] = none :=
  rfl

/-- The actual reference-choice selector can only return the empty population, one reference, or
two references.  Thus every nonempty actual selection lies in the source one/two domain, and the
only undecodable actual selection is the explicit empty population. -/
theorem localizedRule4bReferencesFromPopulation_eq_nil_or_singleton_or_pair
    (descriptors : List RS) :
    localizedRule4bReferencesFromPopulation descriptors = [] ∨
      (∃ reference, localizedRule4bReferencesFromPopulation descriptors =
        [reference]) ∨
      (∃ first second, localizedRule4bReferencesFromPopulation descriptors =
        [first, second]) := by
  by_cases empty : descriptors.isEmpty
  · exact Or.inl (by
      simp [localizedRule4bReferencesFromPopulation, empty])
  · right
    by_cases sLessR :
        (descriptors.filter fun descriptor => descriptor == RS.S).length <
          (descriptors.filter fun descriptor => descriptor == RS.R).length
    · exact Or.inl ⟨RS.R, by
        simp [localizedRule4bReferencesFromPopulation, empty, sLessR]⟩
    · by_cases rLessS :
          (descriptors.filter fun descriptor => descriptor == RS.R).length <
            (descriptors.filter fun descriptor => descriptor == RS.S).length
      · exact Or.inl ⟨RS.S, by
          simp [localizedRule4bReferencesFromPopulation, empty, sLessR, rLessS]⟩
      · exact Or.inr ⟨RS.R, RS.S, by
          simp [localizedRule4bReferencesFromPopulation, empty, sLessR, rLessS]⟩

/-- Consequently the actual population selector is decodable whenever it is nonempty; an empty
population is reported as outside the domain rather than as a third source count. -/
theorem sourceRule4bReferenceCount?_fromPopulation_or_empty
    (descriptors : List RS) :
    (∃ count, sourceRule4bReferenceCount?
      (localizedRule4bReferencesFromPopulation descriptors) = some count) ∨
      localizedRule4bReferencesFromPopulation descriptors = [] := by
  rcases localizedRule4bReferencesFromPopulation_eq_nil_or_singleton_or_pair
    descriptors with empty | ⟨reference, singleton⟩ | ⟨first, second, pair⟩
  · exact Or.inr empty
  · exact Or.inl ⟨.one, by rw [singleton]; rfl⟩
  · exact Or.inl ⟨.two, by rw [pair]; rfl⟩

/-- Production priority of one reference is `2`. -/
theorem constitutionalRule4bReferenceCountPriority_one (reference : RS) :
    constitutionalRule4bReferenceCountPriority [reference] = 2 :=
  rfl

/-- Production priority of two references is `1`. -/
theorem constitutionalRule4bReferenceCountPriority_two (first second : RS) :
    constitutionalRule4bReferenceCountPriority [first, second] = 1 :=
  rfl

/-- The empty production population has priority `0`; it is *not* claimed to be a P-92 count. -/
theorem constitutionalRule4bReferenceCountPriority_empty :
    constitutionalRule4bReferenceCountPriority [] = 0 :=
  rfl

/-- P-92's priority of one reference is `1`. -/
theorem rule4bReferenceCountPriority_one :
    BlueBookP92.rule4bReferenceCountPriority .one = 1 :=
  rfl

/-- P-92's priority of two references is `0`. -/
theorem rule4bReferenceCountPriority_two :
    BlueBookP92.rule4bReferenceCountPriority .two = 0 :=
  rfl

/-- Only the comparison order is identified: the actual and source numeric values for one
reference are different (`2` versus `1`), so this is not a numeric equality claim. -/
theorem constitutionalRule4bReferenceCountPriority_not_source_one :
    constitutionalRule4bReferenceCountPriority [RS.R] ≠
      BlueBookP92.rule4bReferenceCountPriority .one := by
  decide

/-- **Actual reference-count priority realizes the independent P-92 count judgment.**  On the
one/two-reference domain, `compare` of the production count priorities is exactly
`rule4bReferenceCountDecision`.  Only the order is asserted: the numeric values are `2/1` in
production and `1/0` in P-92. -/
theorem compare_constitutionalRule4bReferenceCountPriorities_eq_decision
    (leftReferences rightReferences : List RS)
    (leftCount rightCount : BlueBookP92.Rule4bReferenceCount)
    (leftDecoded : sourceRule4bReferenceCount? leftReferences = some leftCount)
    (rightDecoded : sourceRule4bReferenceCount? rightReferences = some rightCount) :
    compare (constitutionalRule4bReferenceCountPriority leftReferences)
        (constitutionalRule4bReferenceCountPriority rightReferences) =
      BlueBookP92.rule4bReferenceCountDecision leftCount rightCount := by
  rcases (sourceRule4bReferenceCount?_eq_some_iff leftReferences leftCount).mp
    leftDecoded with
    ⟨leftReference, rfl, rfl⟩ | ⟨leftFirst, leftSecond, rfl, rfl⟩ <;>
  rcases (sourceRule4bReferenceCount?_eq_some_iff rightReferences rightCount).mp
    rightDecoded with
    ⟨rightReference, rfl, rfl⟩ | ⟨rightFirst, rightSecond, rfl, rfl⟩ <;>
  rfl

/-! ## Part 4: addressed source observations, erasure, and builder correspondence -/

/-- An entry at an addressed position occurs in one of the sparse layers. -/
def sourceSparseEntryMem {α : Type*}
    (layers : List (List (OfficialSparseEntry α)))
    (position : List Nat) (value : α) : Prop :=
  ∃ layer, layer ∈ layers ∧ (position, value) ∈ layer

/-- Entry membership distributes through `++`. -/
theorem sourceSparseEntryMem_append {α : Type*}
    {left right : List (List (OfficialSparseEntry α))}
    {position : List Nat} {value : α} :
    sourceSparseEntryMem (left ++ right) position value ↔
      sourceSparseEntryMem left position value ∨
        sourceSparseEntryMem right position value := by
  unfold sourceSparseEntryMem
  constructor
  · rintro ⟨layer, layerMem, entryMem⟩
    rcases List.mem_append.mp layerMem with leftMem | rightMem
    · exact Or.inl ⟨layer, leftMem, entryMem⟩
    · exact Or.inr ⟨layer, rightMem, entryMem⟩
  · rintro (⟨layer, layerMem, entryMem⟩ | ⟨layer, layerMem, entryMem⟩)
    · exact ⟨layer, List.mem_append_left right layerMem, entryMem⟩
    · exact ⟨layer, List.mem_append_right left layerMem, entryMem⟩

/-- The singleton root layer contains exactly the root entry. -/
theorem sourceSparseEntryMem_singleton_iff {α : Type*}
    {position : List Nat} {value root : α} :
    sourceSparseEntryMem [[([], root)]] position value ↔
      position = [] ∧ value = root := by
  constructor
  · rintro ⟨layer, layerMem, entryMem⟩
    simp only [List.mem_singleton] at layerMem
    subst layer
    simpa using entryMem
  · intro same
    obtain ⟨positionEq, valueEq⟩ := same
    subst position
    subst value
    exact ⟨[([], root)], by simp, by simp⟩

/-- A child whose padded layer contains an entry contributes that entry. -/
theorem sourceMem_of_mem_getD {α : Type*} {layers : List (List α)} {depth : ℕ} {entry : α}
    (member : entry ∈ layers.getD depth []) :
    ∃ layer, layer ∈ layers ∧ entry ∈ layer := by
  unfold List.getD at member
  cases fetched : layers[depth]? with
  | none => simp [fetched] at member
  | some layer =>
      exact ⟨layer, List.mem_of_getElem? fetched, by simpa [fetched] using member⟩

/-- Every entry of the merged descriptor children comes from one child's own descriptor, with the
child's final sibling slot prefixed to the address. -/
theorem sourceSparseEntryMem_mergeDescriptorChildren
    (input : CertifiedLocalizedCIPInput)
    (children : List input.LocalizedRerootCumulativeRule45Key)
    {position : List Nat} {vector : List Nat}
    (mem : sourceSparseEntryMem
      (input.mergeLocalizedRerootDescriptorChildren children) position vector) :
    ∃ child ∈ children.zipIdx, ∃ rest : List Nat,
      position = child.2 :: rest ∧
        sourceSparseEntryMem child.1.descriptor rest vector := by
  obtain ⟨layer, layerMem, entryMem⟩ := mem
  unfold mergeLocalizedRerootDescriptorChildren at layerMem
  obtain ⟨depth, _depthMem, layerEq⟩ := List.mem_map.mp layerMem
  subst layer
  obtain ⟨child, childMem, prefixedMem⟩ := List.mem_flatMap.mp entryMem
  unfold OfficialRuleMajorKey.prefixLayer at prefixedMem
  obtain ⟨entry, entryMem', entryEq⟩ := List.mem_map.mp prefixedMem
  have positionEq : position = child.2 :: entry.1 :=
    (congrArg Prod.fst entryEq).symm
  have vectorEq : vector = entry.2 := (congrArg Prod.snd entryEq).symm
  obtain ⟨sourceLayer, sourceLayerMem, entryInSource⟩ :=
    sourceMem_of_mem_getD (layers := child.1.descriptor) (depth := depth)
      (entry := entry) entryMem'
  exact ⟨child, childMem, entry.1, positionEq,
    ⟨sourceLayer, sourceLayerMem, by simpa [vectorEq] using entryInSource⟩⟩

/-- Independent address precedence for sibling-slot paths.

This is the explicit source ordering, not a call into the production comparator.  Orientation
matches the production sparse entry: a proper prefix (shorter address) is senior (`gt`), and
otherwise the first differing component decides, with the smaller sibling slot senior. -/
def sourceRule4bPathDecision : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .gt
  | _ :: _, [] => .lt
  | first :: firstRest, second :: secondRest =>
      (compare second first).then
        (sourceRule4bPathDecision firstRest secondRest)

/-- The independent path precedence is exactly the production sparse-entry path component.  This
is proved, so the source ordering is not defined by the production comparator. -/
theorem sourceRule4bPathDecision_eq_flip_compareLex (left right : List Nat) :
    sourceRule4bPathDecision left right =
      flip (List.compareLex OfficialRuleMajorKey.compareNat) left right := by
  induction left generalizing right with
  | nil =>
      cases right with
      | nil => rfl
      | cons second secondRest => rfl
  | cons first firstRest inductionHypothesis =>
      cases right with
      | nil => rfl
      | cons second secondRest =>
          change (compare second first).then
              (sourceRule4bPathDecision firstRest secondRest) =
            flip (List.compareLex OfficialRuleMajorKey.compareNat)
              (first :: firstRest) (second :: secondRest)
          rw [inductionHypothesis secondRest]
          simp only [flip, List.compareLex_cons_cons,
            OfficialRuleMajorKey.compareNat]

/-- Source decision for one addressed observation: the leading-rule observation is consulted only
when the addresses are equal.  Address precedence is the explicit source path/length ordering
above; the observation judgment is `sourceRule45ObservationDecision`. -/
def sourceSparseEntryDecision
    (left right : OfficialSparseEntry SourceRule45Observation) : Ordering :=
  compareLex
    (Ordering.byKey Prod.fst sourceRule4bPathDecision)
    (Ordering.byKey Prod.snd sourceRule45ObservationDecision)
    left right

/-- First-difference source decision for one layer: lexicographic comparison of the addressed
entries.  When one layer is a proper prefix of the other, the shorter layer is the first
difference. -/
def sourceSparseLayerDecision
    (left right : List (OfficialSparseEntry SourceRule45Observation)) : Ordering :=
  List.compareLex sourceSparseEntryDecision left right

/-- First-difference source decision for all layers, from the root sphere outward. -/
def sourceSparseLayersDecision
    (left right : List (List (OfficialSparseEntry SourceRule45Observation))) : Ordering :=
  List.compareLex sourceSparseLayerDecision left right

/-- Erase one actual sparse entry to its source observation, if its priority vector decodes. -/
def sourceEraseEntry? (entry : OfficialSparseEntry (List Nat)) :
    Option (OfficialSparseEntry SourceRule45Observation) :=
  (sourceDecodeRule45Vector? entry.2).map fun observation =>
    (entry.1, observation)

/-- Erase one actual sparse layer. -/
def sourceEraseLayer? (layer : List (OfficialSparseEntry (List Nat))) :
    Option (List (OfficialSparseEntry SourceRule45Observation)) :=
  layer.mapM sourceEraseEntry?

/-- Erase all actual sparse layers. -/
def sourceEraseLayers?
    (layers : List (List (OfficialSparseEntry (List Nat)))) :
    Option (List (List (OfficialSparseEntry SourceRule45Observation))) :=
  layers.mapM sourceEraseLayer?

/-- If every element decodes, `mapM` succeeds. -/
private theorem sourceMapM_eq_some_of_forall {α β : Type*} (f : α → Option β) :
    ∀ (values : List α),
      (∀ value, value ∈ values → ∃ decoded, f value = some decoded) →
      ∃ decoded, values.mapM f = some decoded
  | [], _ => ⟨[], rfl⟩
  | value :: values, allDecode => by
      obtain ⟨decoded, decodedEq⟩ := allDecode value (by simp)
      obtain ⟨decodedTail, tailEq⟩ := sourceMapM_eq_some_of_forall f values
        (fun tail tailMem => allDecode tail (by simp [tailMem]))
      exact ⟨decoded :: decodedTail, by
        simp [List.mapM_cons, decodedEq, tailEq]⟩

/-- Pair comparison: equal leading positions leave the observation comparator, and a realized
observation comparison transfers through the lexicographic composition. -/
private theorem sourceCompareLex_pair_realizes {β : Type*}
    (positionComparator : List Nat → List Nat → Ordering)
    (actualObservation : List Nat → List Nat → Ordering)
    (sourceObservation : β → β → Ordering)
    (leftPosition rightPosition : List Nat)
    (leftVector rightVector : List Nat)
    (leftObservation rightObservation : β)
    (observationRealizes : actualObservation leftVector rightVector =
      sourceObservation leftObservation rightObservation) :
    compareLex
        (Ordering.byKey Prod.fst positionComparator)
        (Ordering.byKey Prod.snd actualObservation)
        (leftPosition, leftVector) (rightPosition, rightVector) =
      compareLex
        (Ordering.byKey Prod.fst positionComparator)
        (Ordering.byKey Prod.snd sourceObservation)
        (leftPosition, leftObservation) (rightPosition, rightObservation) := by
  change (positionComparator leftPosition rightPosition).then
      (actualObservation leftVector rightVector) =
    (positionComparator leftPosition rightPosition).then
      (sourceObservation leftObservation rightObservation)
  rw [observationRealizes]

/-- **The actual sparse entry comparator realizes the addressed source judgment.**  The erasure
hypotheses say that each actual entry decodes to the symbolic source entry; no desired result is
supplied. -/
theorem sourceCompareSparseEntry_realizes
    (left right : OfficialSparseEntry (List Nat))
    (leftSource rightSource : OfficialSparseEntry SourceRule45Observation)
    (leftErased : sourceEraseEntry? left = some leftSource)
    (rightErased : sourceEraseEntry? right = some rightSource) :
    OfficialRuleMajorKey.compareSparseEntry
        compareLocalizedCumulativeRule45Priority left right =
      sourceSparseEntryDecision leftSource rightSource := by
  rcases left with ⟨leftPosition, leftVector⟩
  rcases right with ⟨rightPosition, rightVector⟩
  rcases leftSource with ⟨leftSourcePosition, leftSourceObservation⟩
  rcases rightSource with ⟨rightSourcePosition, rightSourceObservation⟩
  unfold sourceEraseEntry? at leftErased rightErased
  cases leftDecoded : sourceDecodeRule45Vector? leftVector with
  | none => simp [leftDecoded] at leftErased
  | some leftObservation =>
      cases rightDecoded : sourceDecodeRule45Vector? rightVector with
      | none => simp [rightDecoded] at rightErased
      | some rightObservation =>
          simp only [leftDecoded, rightDecoded, Option.map_some,
            Option.some.injEq, Prod.mk.injEq] at leftErased rightErased
          obtain ⟨rfl, rfl⟩ := leftErased
          obtain ⟨rfl, rfl⟩ := rightErased
          unfold OfficialRuleMajorKey.compareSparseEntry sourceSparseEntryDecision
          rw [show sourceRule4bPathDecision =
              flip (List.compareLex OfficialRuleMajorKey.compareNat) from
            funext fun left => funext fun right =>
              sourceRule4bPathDecision_eq_flip_compareLex left right]
          exact sourceCompareLex_pair_realizes
            (flip (List.compareLex OfficialRuleMajorKey.compareNat))
            compareLocalizedCumulativeRule45Priority
            sourceRule45ObservationDecision
            leftPosition rightPosition leftVector rightVector
            leftObservation rightObservation
            (compareLocalizedCumulativeRule45Priority_realizes_source
              leftVector rightVector leftObservation rightObservation
              leftDecoded rightDecoded)

/-- Generic first difference over decoded lists. -/
private theorem sourceCompareLex_mapM_realizes {α β : Type*}
    (decode : α → Option β)
    (actualComparator : α → α → Ordering)
    (sourceComparator : β → β → Ordering)
    (elementRealizes : ∀ (left right : α) (leftSource rightSource : β),
      decode left = some leftSource → decode right = some rightSource →
      actualComparator left right = sourceComparator leftSource rightSource) :
    ∀ (left right : List α) (leftSource rightSource : List β),
      left.mapM decode = some leftSource →
      right.mapM decode = some rightSource →
      List.compareLex actualComparator left right =
        List.compareLex sourceComparator leftSource rightSource
  | [], [], leftSource, rightSource, leftComputed, rightComputed => by
      simp [List.mapM_nil] at leftComputed rightComputed
      subst leftSource
      subst rightSource
      rfl
  | [], rightHead :: rightRest, leftSource, rightSource, leftComputed, rightComputed => by
      simp [List.mapM_nil] at leftComputed
      subst leftSource
      rw [List.mapM_cons] at rightComputed
      cases rightHeadDecoded : decode rightHead with
      | none => simp [rightHeadDecoded] at rightComputed
      | some rightHeadSource =>
          cases rightTailDecoded : rightRest.mapM decode with
          | none => simp [rightHeadDecoded, rightTailDecoded] at rightComputed
          | some rightTailSource =>
              simp [rightHeadDecoded, rightTailDecoded] at rightComputed
              subst rightSource
              rfl
  | leftHead :: leftRest, [], leftSource, rightSource, leftComputed, rightComputed => by
      simp [List.mapM_nil] at rightComputed
      subst rightSource
      rw [List.mapM_cons] at leftComputed
      cases leftHeadDecoded : decode leftHead with
      | none => simp [leftHeadDecoded] at leftComputed
      | some leftHeadSource =>
          cases leftTailDecoded : leftRest.mapM decode with
          | none => simp [leftHeadDecoded, leftTailDecoded] at leftComputed
          | some leftTailSource =>
              simp [leftHeadDecoded, leftTailDecoded] at leftComputed
              subst leftSource
              rfl
  | leftHead :: leftRest, rightHead :: rightRest, leftSource, rightSource,
      leftComputed, rightComputed => by
      rw [List.mapM_cons] at leftComputed
      cases leftHeadDecoded : decode leftHead with
      | none => simp [leftHeadDecoded] at leftComputed
      | some leftHeadSource =>
          cases leftTailDecoded : leftRest.mapM decode with
          | none => simp [leftHeadDecoded, leftTailDecoded] at leftComputed
          | some leftTailSource =>
              simp [leftHeadDecoded, leftTailDecoded] at leftComputed
              subst leftSource
              rw [List.mapM_cons] at rightComputed
              cases rightHeadDecoded : decode rightHead with
              | none => simp [rightHeadDecoded] at rightComputed
              | some rightHeadSource =>
                  cases rightTailDecoded : rightRest.mapM decode with
                  | none =>
                      simp [rightHeadDecoded, rightTailDecoded] at rightComputed
                  | some rightTailSource =>
                      simp [rightHeadDecoded, rightTailDecoded] at rightComputed
                      subst rightSource
                      rw [List.compareLex_cons_cons, List.compareLex_cons_cons]
                      have headEq : actualComparator leftHead rightHead =
                          sourceComparator leftHeadSource rightHeadSource :=
                        elementRealizes leftHead rightHead leftHeadSource
                          rightHeadSource leftHeadDecoded rightHeadDecoded
                      rw [headEq]
                      cases headComparison :
                          sourceComparator leftHeadSource rightHeadSource with
                      | lt => rfl
                      | eq =>
                          exact sourceCompareLex_mapM_realizes decode
                            actualComparator sourceComparator elementRealizes
                            leftRest rightRest leftTailSource rightTailSource
                            leftTailDecoded rightTailDecoded
                      | gt => rfl

/-- **The actual sparse layer comparator realizes the source first difference.** -/
theorem sourceCompareSparseLayer_realizes
    (left right : List (OfficialSparseEntry (List Nat)))
    (leftSource rightSource : List (OfficialSparseEntry SourceRule45Observation))
    (leftErased : sourceEraseLayer? left = some leftSource)
    (rightErased : sourceEraseLayer? right = some rightSource) :
    OfficialRuleMajorKey.compareSparseLayer
        compareLocalizedCumulativeRule45Priority left right =
      sourceSparseLayerDecision leftSource rightSource := by
  unfold OfficialRuleMajorKey.compareSparseLayer sourceSparseLayerDecision
  exact sourceCompareLex_mapM_realizes sourceEraseEntry?
    (OfficialRuleMajorKey.compareSparseEntry compareLocalizedCumulativeRule45Priority)
    sourceSparseEntryDecision
    (fun leftEntry rightEntry leftSourceEntry rightSourceEntry
        leftEntryErased rightEntryErased =>
      sourceCompareSparseEntry_realizes leftEntry rightEntry
        leftSourceEntry rightSourceEntry leftEntryErased rightEntryErased)
    left right leftSource rightSource leftErased rightErased

/-- **The actual sparse layer-list comparator realizes the root-outward source judgment.** -/
theorem sourceCompareSparseLayers_realizes
    (left right : List (List (OfficialSparseEntry (List Nat))))
    (leftSource rightSource :
      List (List (OfficialSparseEntry SourceRule45Observation)))
    (leftErased : sourceEraseLayers? left = some leftSource)
    (rightErased : sourceEraseLayers? right = some rightSource) :
    OfficialRuleMajorKey.compareSparseLayers
        compareLocalizedCumulativeRule45Priority left right =
      sourceSparseLayersDecision leftSource rightSource := by
  unfold OfficialRuleMajorKey.compareSparseLayers sourceSparseLayersDecision
  exact sourceCompareLex_mapM_realizes sourceEraseLayer?
    (OfficialRuleMajorKey.compareSparseLayer compareLocalizedCumulativeRule45Priority)
    sourceSparseLayerDecision
    (fun leftLayer rightLayer leftSourceLayer rightSourceLayer
        leftLayerErased rightLayerErased =>
      sourceCompareSparseLayer_realizes leftLayer rightLayer
        leftSourceLayer rightSourceLayer leftLayerErased rightLayerErased)
    left right leftSource rightSource leftErased rightErased

/-- After an exact constitutional tie, the actual cumulative Rule-4a key comparator is exactly
the source sparse layer decision of the erased keys.  The constitutional gate itself is the
unchanged production comparison; only the descriptor layers are decoded. -/
theorem sourceCompareCumulativeRule45Keys_eq_sparseSource_of_constitutionalTie
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (leftSource rightSource :
      List (List (OfficialSparseEntry SourceRule45Observation)))
    (constitutionalTie :
      OfficialRuleMajorKey.compare left.constitutional right.constitutional =
        Ordering.eq)
    (leftErased : sourceEraseLayers? left.descriptor = some leftSource)
    (rightErased : sourceEraseLayers? right.descriptor = some rightSource) :
    input.compareLocalizedRerootCumulativeRule45Keys left right =
      sourceSparseLayersDecision leftSource rightSource := by
  unfold compareLocalizedRerootCumulativeRule45Keys
  have tied :
      (Ordering.byKey (fun key => key.constitutional)
          OfficialRuleMajorKey.compare) left right = Ordering.eq := by
    simpa only [Ordering.byKey] using constitutionalTie
  rw [localizedCompareLex_eq_right_of_eq tied]
  simpa only [Ordering.byKey] using
    sourceCompareSparseLayers_realizes left.descriptor right.descriptor
      leftSource rightSource leftErased rightErased

/-! ### Builder membership: every child key comes from its own successful build -/

/-- `mapM` membership for the cumulative builder. -/
private theorem sourceBuildCumulativeMapM_member
    (input : CertifiedLocalizedCIPInput) {carrierFuel fuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ (cursors : List (input.LocalizedRerootCursor carrierFuel))
      (keys : List input.LocalizedRerootCumulativeRule45Key),
      cursors.mapM (input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel) = some keys →
      ∀ key, key ∈ keys →
        ∃ cursor, cursor ∈ cursors ∧
          input.buildLocalizedRerootCumulativeRule45Key?
            stage target view fuel cursor = some key
  | [], keys, computed, key, present => by
      simp at computed
      subst keys
      simp at present
  | cursor :: cursors, keys, computed, key, present => by
      rw [List.mapM_cons] at computed
      cases headComputed : input.buildLocalizedRerootCumulativeRule45Key?
          stage target view fuel cursor with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : cursors.mapM
              (input.buildLocalizedRerootCumulativeRule45Key?
                stage target view fuel) with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst keys
              rcases List.mem_cons.mp present with rfl | tailPresent
              · exact ⟨cursor, by simp, headComputed⟩
              · rcases sourceBuildCumulativeMapM_member input stage target view
                    cursors tail tailComputed key tailPresent with
                  ⟨source, sourcePresent, sourceComputed⟩
                exact ⟨source, List.mem_cons_of_mem cursor sourcePresent,
                  sourceComputed⟩

/-- **Builder source correspondence for addressed observations.**  Every entry of every sparse
layer of a successfully built Rule-4a/Rule-4b cumulative key is the actual priority vector of
*this* stage at *some* source cursor.  No raw `sourceNodes` alignment is assumed: the statement is
derived by induction over the actual builder and its merge. -/
theorem sourceBuildCumulative_descriptor_entry_label
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursor key,
      input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel cursor = some key →
      ∀ {position : List Nat} {vector : List Nat},
        sourceSparseEntryMem key.descriptor position vector →
          ∃ label, vector = localizedCumulativeRule45Priority stage label
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            intro mem
            obtain ⟨_positionEq, vectorEq⟩ :=
              (sourceSparseEntryMem_singleton_iff
                (root := localizedCumulativeRule45Priority stage
                  (input.localizedDependencyLabel target view cursor))).mp mem
            exact ⟨input.localizedDependencyLabel target view cursor, vectorEq⟩
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            intro mem
            obtain ⟨_positionEq, vectorEq⟩ :=
              (sourceSparseEntryMem_singleton_iff
                (root := localizedCumulativeRule45Priority stage
                  (input.localizedDependencyLabel target view cursor))).mp mem
            exact ⟨input.localizedDependencyLabel target view cursor, vectorEq⟩
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootCumulativeRule45Key?
                  stage target view fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                intro mem
                have appendMem : sourceSparseEntryMem
                    ([[([], localizedCumulativeRule45Priority stage
                        (input.localizedDependencyLabel target view cursor))]] ++
                      input.mergeLocalizedRerootDescriptorChildren
                        (input.sortLocalizedRerootCumulativeRule45Keys
                          childKeys)) _ _ := mem
                rcases (sourceSparseEntryMem_append.mp appendMem) with
                  rootMem | mergedMem
                · obtain ⟨_positionEq, vectorEq⟩ :=
                    (sourceSparseEntryMem_singleton_iff
                      (root := localizedCumulativeRule45Priority stage
                        (input.localizedDependencyLabel target view cursor))).mp
                      rootMem
                  exact ⟨input.localizedDependencyLabel target view cursor,
                    vectorEq⟩
                · obtain ⟨child, childMem, rest, _positionEq, childEntryMem⟩ :=
                    sourceSparseEntryMem_mergeDescriptorChildren input
                      (input.sortLocalizedRerootCumulativeRule45Keys childKeys)
                      mergedMem
                  have childSorted : child.1 ∈
                      input.sortLocalizedRerootCumulativeRule45Keys childKeys :=
                    List.fst_mem_of_mem_zipIdx childMem
                  have childInKeys : child.1 ∈ childKeys :=
                    (input.sortLocalizedRerootCumulativeRule45Keys_perm
                      childKeys).mem_iff.mp childSorted
                  obtain ⟨childCursor, _childCursorMem, childComputed⟩ :=
                    sourceBuildCumulativeMapM_member input stage target view
                      children childKeys childKeysComputed child.1 childInKeys
                  exact sourceBuildCumulative_descriptor_entry_label input stage
                    target view fuel childCursor child.1 childComputed
                    childEntryMem

/-- **Root position correspondence.**  A successful actual build stores this stage's root
priority vector at the empty address in the first sphere. -/
theorem sourceBuildCumulative_descriptor_head
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target) :
    ∀ fuel cursor key,
      input.buildLocalizedRerootCumulativeRule45Key?
        stage target view fuel cursor = some key →
      key.descriptor.head? =
        some [([], localizedCumulativeRule45Priority stage
          (input.localizedDependencyLabel target view cursor))]
  | 0, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            rfl
          · simp [childrenComputed, terminal] at computed
  | fuel + 1, cursor, key, computed => by
      unfold buildLocalizedRerootCumulativeRule45Key? at computed
      cases childrenComputed : input.localizedRerootChildren? cursor with
      | none => simp [childrenComputed] at computed
      | some children =>
          by_cases terminal : children = []
          · simp [childrenComputed, terminal] at computed
            subst key
            rfl
          · cases childKeysComputed : children.mapM
                (input.buildLocalizedRerootCumulativeRule45Key?
                  stage target view fuel) with
            | none =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
            | some childKeys =>
                simp [childrenComputed, terminal, childKeysComputed] at computed
                subst key
                rfl

/-- **Every actual built Rule-4a/Rule-4b key erases to addressed source observations.**  The
erasure is of the actual descriptor; its existence is derived from the builder, not assumed. -/
theorem sourceBuildCumulative_descriptor_erases
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (compatible : stage = .rule4a ∨
      ∃ reference, stage = .rule4b reference)
    {fuel : Nat} {cursor : input.LocalizedRerootCursor carrierFuel}
    {key : input.LocalizedRerootCumulativeRule45Key}
    (computed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel cursor = some key) :
    ∃ sourceDescriptor,
      sourceEraseLayers? key.descriptor = some sourceDescriptor := by
  have entryDecodes : ∀ layer, layer ∈ key.descriptor → ∀ entry, entry ∈ layer →
      ∃ sourceEntry, sourceEraseEntry? entry = some sourceEntry := by
    intro layer layerMem entry entryMem
    obtain ⟨label, vectorEq⟩ :=
      sourceBuildCumulative_descriptor_entry_label input stage target view
        fuel cursor key computed ⟨layer, layerMem, entryMem⟩
    obtain ⟨observation, decoded⟩ :=
      sourceDecodeRule45Vector?_cumulativePriority stage label compatible
    exact ⟨(entry.1, observation), by
      simp [sourceEraseEntry?, vectorEq, decoded]⟩
  have layerDecodes : ∀ layer, layer ∈ key.descriptor →
      ∃ sourceLayer, sourceEraseLayer? layer = some sourceLayer := by
    intro layer layerMem
    exact sourceMapM_eq_some_of_forall sourceEraseEntry? layer
      (fun entry entryMem => entryDecodes layer layerMem entry entryMem)
  exact sourceMapM_eq_some_of_forall sourceEraseLayer? key.descriptor layerDecodes

/-! ## Part 5: the actual compound comparison realizes count-then-Rule-4b -/

/-- Source view of one Rule-4b reading: its addressed decoded descriptor.  The selected reference
itself is not needed for the Rule-4b comparison; the decoded vector already contains the
reference-relative like/unlike pair. -/
structure SourceRule4bReading where
  descriptor : List (List (OfficialSparseEntry SourceRule45Observation))

/-- Erase one actual Rule-4b reading to its intended source view. -/
def sourceEraseRule4bReading? {input : CertifiedLocalizedCIPInput}
    (reading : input.LocalizedRerootRule4bcReading) : Option SourceRule4bReading :=
  (sourceEraseLayers? reading.rule4bKey.descriptor).map fun descriptor =>
    { descriptor := descriptor }

/-- First-difference source comparison of complete Rule-4b reading lists. -/
def sourceRule4bReadingsDecision
    (left right : List SourceRule4bReading) : Ordering :=
  List.compareLex
    (fun leftReading rightReading =>
      sourceSparseLayersDecision leftReading.descriptor rightReading.descriptor)
    left right

/-- **One actual Rule-4b reading comparator realizes the source reading comparison.** -/
theorem sourceCompareReadingsByRule4b_realizes
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootRule4bcReading)
    (leftSource rightSource : SourceRule4bReading)
    (leftErased : sourceEraseRule4bReading? left = some leftSource)
    (rightErased : sourceEraseRule4bReading? right = some rightSource) :
    input.compareLocalizedRerootRule4bcReadingsByRule4b left right =
      sourceSparseLayersDecision leftSource.descriptor
        rightSource.descriptor := by
  unfold sourceEraseRule4bReading? at leftErased rightErased
  cases leftDecoded : sourceEraseLayers? left.rule4bKey.descriptor with
  | none => simp [leftDecoded] at leftErased
  | some leftDescriptor =>
      cases rightDecoded : sourceEraseLayers? right.rule4bKey.descriptor with
      | none => simp [rightDecoded] at rightErased
      | some rightDescriptor =>
          simp only [leftDecoded, rightDecoded, Option.map_some,
            Option.some.injEq] at leftErased rightErased
          subst leftSource
          subst rightSource
          unfold compareLocalizedRerootRule4bcReadingsByRule4b
          simpa only [Ordering.byKey] using
            sourceCompareSparseLayers_realizes
              left.rule4bKey.descriptor right.rule4bKey.descriptor
              leftDescriptor rightDescriptor leftDecoded rightDecoded

/-- **List-level actual Rule-4b reading comparison realizes the source first difference.** -/
theorem sourceCompareRule4bReadings_realizes
    (input : CertifiedLocalizedCIPInput)
    (left right : List input.LocalizedRerootRule4bcReading)
    (leftSource rightSource : List SourceRule4bReading)
    (leftErased : left.mapM sourceEraseRule4bReading? = some leftSource)
    (rightErased : right.mapM sourceEraseRule4bReading? = some rightSource) :
    input.compareLocalizedRerootCompoundRule4bReadings left right =
      sourceRule4bReadingsDecision leftSource rightSource := by
  unfold compareLocalizedRerootCompoundRule4bReadings
    sourceRule4bReadingsDecision
  exact sourceCompareLex_mapM_realizes sourceEraseRule4bReading?
    input.compareLocalizedRerootRule4bcReadingsByRule4b
    (fun leftReading rightReading =>
      sourceSparseLayersDecision leftReading.descriptor
        rightReading.descriptor)
    (fun leftReading rightReading leftSourceReading rightSourceReading
        leftReadingErased rightReadingErased =>
      sourceCompareReadingsByRule4b_realizes input leftReading rightReading
        leftSourceReading rightSourceReading leftReadingErased
        rightReadingErased)
    left right leftSource rightSource leftErased rightErased

/-- First-applicable source Rule-4b judgment after a Rule-4a tie: the one/two reference count
first, then the complete Rule-4b reading first difference.  An exact tie returns `eq` and is *not*
allowed to stand in for the later Rule-4c comparison. -/
def sourceRule4bAfterRule4aDecision
    (leftCount rightCount : BlueBookP92.Rule4bReferenceCount)
    (leftReadings rightReadings : List SourceRule4bReading) : Ordering :=
  match BlueBookP92.rule4bReferenceCountDecision leftCount rightCount with
  | .eq => sourceRule4bReadingsDecision leftReadings rightReadings
  | decision => decision

/-- **The actual compound comparison after a Rule-4a tie realizes the source count-then-Reading
judgment.**  If the source decision is strict, the actual comparator returns exactly it.  If the
source count and every Rule-4b reading tie, the actual comparator falls through to the unchanged
actual Rule-4c reading comparison; that fall-through is displayed in the result, never renamed as
a source Rule-4b judgment.

The two `referenceCountPriority` hypotheses are not additional source premises: they are the
declarative meaning of a compiled compound key and are supplied by
`buildLocalizedRerootCompoundRule4bcKey?_sound` for actual builder output. -/
theorem sourceCompareAfterRule4a_realizes_source
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (leftCount rightCount : BlueBookP92.Rule4bReferenceCount)
    (leftSourceReadings rightSourceReadings : List SourceRule4bReading)
    (leftCountDecoded :
      sourceRule4bReferenceCount? left.references = some leftCount)
    (rightCountDecoded :
      sourceRule4bReferenceCount? right.references = some rightCount)
    (leftPriority :
      left.referenceCountPriority =
        constitutionalRule4bReferenceCountPriority left.references)
    (rightPriority :
      right.referenceCountPriority =
        constitutionalRule4bReferenceCountPriority right.references)
    (leftReadingsErased :
      left.readings.mapM sourceEraseRule4bReading? = some leftSourceReadings)
    (rightReadingsErased :
      right.readings.mapM sourceEraseRule4bReading? = some rightSourceReadings) :
    input.compareLocalizedRerootCompoundRule4bcAfterRule4a left right =
      match sourceRule4bAfterRule4aDecision leftCount rightCount
          leftSourceReadings rightSourceReadings with
      | .eq =>
          input.compareLocalizedRerootCompoundRule4cReadings
            left.readings right.readings
      | decision => decision := by
  have countRealized :
      compare (constitutionalRule4bReferenceCountPriority left.references)
          (constitutionalRule4bReferenceCountPriority right.references) =
        BlueBookP92.rule4bReferenceCountDecision leftCount rightCount :=
    compare_constitutionalRule4bReferenceCountPriorities_eq_decision
      left.references right.references leftCount rightCount
      leftCountDecoded rightCountDecoded
  have readingsRealized :
      input.compareLocalizedRerootCompoundRule4bReadings
          left.readings right.readings =
        sourceRule4bReadingsDecision leftSourceReadings rightSourceReadings :=
    sourceCompareRule4bReadings_realizes input left.readings right.readings
      leftSourceReadings rightSourceReadings leftReadingsErased
      rightReadingsErased
  unfold sourceRule4bAfterRule4aDecision
  cases countDecision :
      BlueBookP92.rule4bReferenceCountDecision leftCount rightCount with
  | eq =>
      have countTie :
          compare left.referenceCountPriority right.referenceCountPriority =
            Ordering.eq := by
        rw [leftPriority, rightPriority, countRealized, countDecision]
      by_cases readingsTie :
          sourceRule4bReadingsDecision leftSourceReadings
            rightSourceReadings = Ordering.eq
      · have productionRule4bTie :
            input.compareLocalizedRerootCompoundRule4bReadings
              left.readings right.readings = Ordering.eq := by
          rw [readingsRealized, readingsTie]
        rw [input.compareLocalizedRerootCompoundRule4bcAfterRule4a_eq_rule4c_of_priorTies
          left right countTie productionRule4bTie]
        simp [readingsTie]
      · have productionRule4bNe :
            input.compareLocalizedRerootCompoundRule4bReadings
              left.readings right.readings ≠ Ordering.eq := by
          rw [readingsRealized]
          exact readingsTie
        rw [input.compareLocalizedRerootCompoundRule4bcAfterRule4a_eq_rule4b_of_priorTie
          left right countTie productionRule4bNe]
        rw [readingsRealized]
        simp
  | lt =>
      have countNe :
          compare left.referenceCountPriority right.referenceCountPriority ≠
            Ordering.eq := by
        rw [leftPriority, rightPriority, countRealized, countDecision]
        decide
      rw [input.compareLocalizedRerootCompoundRule4bcAfterRule4a_eq_referenceCount_of_ne
        left right countNe]
      rw [leftPriority, rightPriority, countRealized, countDecision]
  | gt =>
      have countNe :
          compare left.referenceCountPriority right.referenceCountPriority ≠
            Ordering.eq := by
        rw [leftPriority, rightPriority, countRealized, countDecision]
        decide
      rw [input.compareLocalizedRerootCompoundRule4bcAfterRule4a_eq_referenceCount_of_ne
        left right countNe]
      rw [leftPriority, rightPriority, countRealized, countDecision]

/-- **Bridge from the normative compound key comparator at an exact actual Rule-4a tie.**  The
strict Rule-4a gate is the unchanged actual comparison; only after that explicit tie does the
source count-then-reading judgment apply, and an exact source tie exposes the unchanged actual
Rule-4c comparison. -/
theorem sourceCompareCompoundRule4bcKeys_realizes_source_at_rule4aTie
    (input : CertifiedLocalizedCIPInput)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (rule4aTie :
      input.compareLocalizedRerootCumulativeRule45Keys
        left.rule4aKey right.rule4aKey = Ordering.eq)
    (leftCount rightCount : BlueBookP92.Rule4bReferenceCount)
    (leftSourceReadings rightSourceReadings : List SourceRule4bReading)
    (leftCountDecoded :
      sourceRule4bReferenceCount? left.references = some leftCount)
    (rightCountDecoded :
      sourceRule4bReferenceCount? right.references = some rightCount)
    (leftPriority :
      left.referenceCountPriority =
        constitutionalRule4bReferenceCountPriority left.references)
    (rightPriority :
      right.referenceCountPriority =
        constitutionalRule4bReferenceCountPriority right.references)
    (leftReadingsErased :
      left.readings.mapM sourceEraseRule4bReading? = some leftSourceReadings)
    (rightReadingsErased :
      right.readings.mapM sourceEraseRule4bReading? = some rightSourceReadings) :
    input.compareLocalizedRerootCompoundRule4bcKeys left right =
      match sourceRule4bAfterRule4aDecision leftCount rightCount
          leftSourceReadings rightSourceReadings with
      | .eq =>
          input.compareLocalizedRerootCompoundRule4cReadings
            left.readings right.readings
      | decision => decision := by
  rw [input.compareLocalizedRerootCompoundRule4bcKeys_eq_afterRule4a_of_tie
    left right rule4aTie]
  exact sourceCompareAfterRule4a_realizes_source input left right
    leftCount rightCount leftSourceReadings rightSourceReadings
    leftCountDecoded rightCountDecoded leftPriority rightPriority
    leftReadingsErased rightReadingsErased

/-! ### Builder correspondence for readings and the compound key -/

/-- Every reading of a successful reading-list build comes from one successful per-reference
reading build. -/
theorem sourceBuildReadings_member
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel) :
    ∀ (alternatives : List (Option RS))
      (readings : List input.LocalizedRerootRule4bcReading),
      input.buildLocalizedRerootRule4bcReadings?
        target view fuel cursor alternatives = some readings →
      ∀ reading, reading ∈ readings →
        ∃ reference, reference ∈ alternatives ∧
          input.buildLocalizedRerootRule4bcReading?
            target view fuel cursor reference = some reading
  | [], readings, computed => by
      simp [buildLocalizedRerootRule4bcReadings?] at computed
      subst readings
      intro reading mem
      simp at mem
  | reference :: alternatives, readings, computed => by
      unfold buildLocalizedRerootRule4bcReadings? at computed
      cases headComputed : input.buildLocalizedRerootRule4bcReading?
          target view fuel cursor reference with
      | none => simp [headComputed] at computed
      | some head =>
          cases tailComputed : input.buildLocalizedRerootRule4bcReadings?
              target view fuel cursor alternatives with
          | none => simp [headComputed, tailComputed] at computed
          | some tail =>
              simp [headComputed, tailComputed] at computed
              subst readings
              intro reading mem
              rcases List.mem_cons.mp mem with rfl | tailMem
              · exact ⟨reference, by simp, headComputed⟩
              · obtain ⟨sourceReference, sourceMem, sourceComputed⟩ :=
                  sourceBuildReadings_member input target view fuel cursor
                    alternatives tail tailComputed reading tailMem
                exact ⟨sourceReference,
                  List.mem_cons_of_mem reference sourceMem, sourceComputed⟩

/-- The cumulative stage of an optional selected reference: Rule 4a when no reference was
selected, and Rule 4b at that reference otherwise. -/
def sourceStageOfReference :
    Option RS → LocalizedCumulativeRule45Stage
  | none => .rule4a
  | some reference => .rule4b reference

/-- A successful per-reference reading build exposes its Rule-4b key as a successful cumulative
build at the reference's stage. -/
theorem sourceBuildReading_rule4bKey_built
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS)
    (reading : input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReading?
      target view fuel cursor reference = some reading) :
    input.buildLocalizedRerootCumulativeRule45Key?
      (sourceStageOfReference reference)
      target view fuel cursor = some reading.rule4bKey := by
  cases reference with
  | none =>
      change input.buildLocalizedRerootCumulativeRule45Key?
        .rule4a target view fuel cursor = some reading.rule4bKey
      unfold buildLocalizedRerootRule4bcReading? at computed
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45Key?
          .rule4a target view fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45Key?
              .rule4cNoReference target view fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4bComputed, rule4cComputed] at computed
              subst reading
              rfl
  | some reference =>
      change input.buildLocalizedRerootCumulativeRule45Key?
        (.rule4b reference) target view fuel cursor =
        some reading.rule4bKey
      unfold buildLocalizedRerootRule4bcReading? at computed
      cases rule4bComputed : input.buildLocalizedRerootCumulativeRule45Key?
          (.rule4b reference) target view fuel cursor with
      | none => simp [rule4bComputed] at computed
      | some rule4bKey =>
          cases rule4cComputed : input.buildLocalizedRerootCumulativeRule45Key?
              (.rule4c reference) target view fuel cursor with
          | none => simp [rule4bComputed, rule4cComputed] at computed
          | some rule4cKey =>
              simp [rule4bComputed, rule4cComputed] at computed
              subst reading
              rfl

/-- The stage of an optional reference is always a Rule-4a or Rule-4b cumulative stage. -/
theorem sourceStageOfReference_compatible (reference : Option RS) :
    sourceStageOfReference reference = .rule4a ∨
      ∃ selected : RS,
        sourceStageOfReference reference = .rule4b selected := by
  cases reference with
  | none => exact Or.inl rfl
  | some reference => exact Or.inr ⟨reference, rfl⟩

/-- Every successful per-reference reading erases to a source reading.  The erasure is derived
from the actual reading builder and the cumulative descriptor erasure, not supplied. -/
theorem sourceEraseRule4bReading?_of_built
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (reference : Option RS)
    (reading : input.LocalizedRerootRule4bcReading)
    (computed : input.buildLocalizedRerootRule4bcReading?
      target view fuel cursor reference = some reading) :
    ∃ sourceReading, sourceEraseRule4bReading? reading = some sourceReading := by
  have keyBuilt := sourceBuildReading_rule4bKey_built input target view
    fuel cursor reference reading computed
  have compatible := sourceStageOfReference_compatible reference
  obtain ⟨descriptor, erased⟩ := sourceBuildCumulative_descriptor_erases
    input (sourceStageOfReference reference) target view compatible keyBuilt
  refine ⟨{ descriptor := descriptor }, ?_⟩
  simp [sourceEraseRule4bReading?, erased]

/-- Every successful actual compound build's readings erase to source readings. -/
theorem sourceBuildCompound_readings_erase
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key) :
    ∃ sourceReadings,
      key.readings.mapM sourceEraseRule4bReading? = some sourceReadings := by
  unfold buildLocalizedRerootCompoundRule4bcKey? at computed
  cases rule4aComputed : input.buildLocalizedRerootCumulativeRule45Key?
      .rule4a target view fuel cursor with
  | none => simp [rule4aComputed] at computed
  | some rule4aKey =>
      let references := localizedRule4bReferencesFromRankedLabels
        rule4aKey.rankedLabels
      let alternatives := localizedRule4bcReferenceAlternatives references
      cases readingsComputed : input.buildLocalizedRerootRule4bcReadings?
          target view fuel cursor alternatives with
      | none =>
          simp [rule4aComputed, references, alternatives,
            readingsComputed] at computed
      | some readings =>
          simp [rule4aComputed, references, alternatives,
            readingsComputed] at computed
          subst key
          have allErase : ∀ reading, reading ∈ readings →
              ∃ sourceReading,
                sourceEraseRule4bReading? reading = some sourceReading := by
            intro reading readingMem
            obtain ⟨reference, _referenceMem, readingComputed⟩ :=
              sourceBuildReadings_member input target view fuel cursor
                alternatives readings readingsComputed reading readingMem
            exact sourceEraseRule4bReading?_of_built input target view
              fuel cursor reference reading readingComputed
          exact sourceMapM_eq_some_of_forall sourceEraseRule4bReading?
            readings allErase

/-- The actual compound builder stores exactly the production count priority, as derived from its
declarative soundness theorem (not assumed). -/
theorem sourceBuildCompound_referenceCountPriority
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat) (cursor : input.LocalizedRerootCursor carrierFuel)
    (key : input.LocalizedRerootCompoundRule4bcKey)
    (computed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel cursor = some key) :
    key.referenceCountPriority =
      constitutionalRule4bReferenceCountPriority key.references :=
  (input.buildLocalizedRerootCompoundRule4bcKey?_sound
    target view fuel cursor key computed).2.2.1

/-! ### End-to-end actual-builder corollaries

The preceding comparator theorems take erasure equations as hypotheses.  The following corollaries
discharge them, plus the compound priority-field hypotheses, directly from successful actual
builder runs.  Each side has its own cursor, so the comparison is a genuine comparison of two
localized branches rather than a forced self-tie; target, view, stage, and fuel are shared.  No
raw `sourceNodes` alignment or supplied source observation is used. -/

/-- **Actual cumulative builder output decides the independent sparse source judgment.**  Given
two successful builds at a compatible stage and an exact actual constitutional tie, there exist
source erasures of both built descriptors such that the actual cumulative-key comparator returns
the source sparse decision. -/
theorem sourceBuildCumulative_comparison_realizes_source
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (stage : LocalizedCumulativeRule45Stage)
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (compatible : stage = .rule4a ∨ ∃ reference, stage = .rule4b reference)
    {fuel : Nat}
    {leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel}
    (left right : input.LocalizedRerootCumulativeRule45Key)
    (leftComputed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel leftCursor = some left)
    (rightComputed : input.buildLocalizedRerootCumulativeRule45Key?
      stage target view fuel rightCursor = some right)
    (constitutionalTie :
      OfficialRuleMajorKey.compare left.constitutional right.constitutional =
        Ordering.eq) :
    ∃ leftSource rightSource,
      sourceEraseLayers? left.descriptor = some leftSource ∧
      sourceEraseLayers? right.descriptor = some rightSource ∧
      input.compareLocalizedRerootCumulativeRule45Keys left right =
        sourceSparseLayersDecision leftSource rightSource := by
  obtain ⟨leftSource, leftErased⟩ :=
    sourceBuildCumulative_descriptor_erases input stage target view
      compatible leftComputed
  obtain ⟨rightSource, rightErased⟩ :=
    sourceBuildCumulative_descriptor_erases input stage target view
      compatible rightComputed
  exact ⟨leftSource, rightSource, leftErased, rightErased,
    sourceCompareCumulativeRule45Keys_eq_sparseSource_of_constitutionalTie
      input left right leftSource rightSource constitutionalTie
      leftErased rightErased⟩

/-- **Actual compound builder output decides the independent count-then-Rule-4b judgment.**  Both
readings lists erase to source readings and both count priorities are derived from the actual
builder's soundness theorem; only the explicit one/two count decoding remains a hypothesis.  A
full source tie exposes the unchanged actual Rule-4c comparison. -/
theorem sourceBuildCompound_afterRule4a_realizes_source
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (leftComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel leftCursor = some left)
    (rightComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel rightCursor = some right)
    (leftCount rightCount : BlueBookP92.Rule4bReferenceCount)
    (leftCountDecoded :
      sourceRule4bReferenceCount? left.references = some leftCount)
    (rightCountDecoded :
      sourceRule4bReferenceCount? right.references = some rightCount) :
    ∃ leftSourceReadings rightSourceReadings,
      left.readings.mapM sourceEraseRule4bReading? = some leftSourceReadings ∧
      right.readings.mapM sourceEraseRule4bReading? = some rightSourceReadings ∧
      input.compareLocalizedRerootCompoundRule4bcAfterRule4a left right =
        match sourceRule4bAfterRule4aDecision leftCount rightCount
            leftSourceReadings rightSourceReadings with
        | .eq =>
            input.compareLocalizedRerootCompoundRule4cReadings
              left.readings right.readings
        | decision => decision := by
  obtain ⟨leftSourceReadings, leftErased⟩ :=
    sourceBuildCompound_readings_erase input target view fuel leftCursor
      left leftComputed
  obtain ⟨rightSourceReadings, rightErased⟩ :=
    sourceBuildCompound_readings_erase input target view fuel rightCursor
      right rightComputed
  have leftPriority := sourceBuildCompound_referenceCountPriority
    input target view fuel leftCursor left leftComputed
  have rightPriority := sourceBuildCompound_referenceCountPriority
    input target view fuel rightCursor right rightComputed
  exact ⟨leftSourceReadings, rightSourceReadings, leftErased, rightErased,
    sourceCompareAfterRule4a_realizes_source input left right
      leftCount rightCount leftSourceReadings rightSourceReadings
      leftCountDecoded rightCountDecoded leftPriority rightPriority
      leftErased rightErased⟩

/-- **End-to-end compound key comparator at an exact actual Rule-4a tie.**  Same builder-derived
data as the previous corollary, but routed through the normative compound-key comparator. -/
theorem sourceBuildCompoundKeys_realizes_source_at_rule4aTie
    (input : CertifiedLocalizedCIPInput) {carrierFuel : Nat}
    (target : input.LocalizedCIPOccurrence carrierFuel)
    (view : input.LocalizedDependencyView target)
    (fuel : Nat)
    (leftCursor rightCursor : input.LocalizedRerootCursor carrierFuel)
    (left right : input.LocalizedRerootCompoundRule4bcKey)
    (leftComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel leftCursor = some left)
    (rightComputed : input.buildLocalizedRerootCompoundRule4bcKey?
      target view fuel rightCursor = some right)
    (rule4aTie :
      input.compareLocalizedRerootCumulativeRule45Keys
        left.rule4aKey right.rule4aKey = Ordering.eq)
    (leftCount rightCount : BlueBookP92.Rule4bReferenceCount)
    (leftCountDecoded :
      sourceRule4bReferenceCount? left.references = some leftCount)
    (rightCountDecoded :
      sourceRule4bReferenceCount? right.references = some rightCount) :
    ∃ leftSourceReadings rightSourceReadings,
      left.readings.mapM sourceEraseRule4bReading? = some leftSourceReadings ∧
      right.readings.mapM sourceEraseRule4bReading? = some rightSourceReadings ∧
      input.compareLocalizedRerootCompoundRule4bcKeys left right =
        match sourceRule4bAfterRule4aDecision leftCount rightCount
            leftSourceReadings rightSourceReadings with
        | .eq =>
            input.compareLocalizedRerootCompoundRule4cReadings
              left.readings right.readings
        | decision => decision := by
  obtain ⟨leftSourceReadings, leftErased⟩ :=
    sourceBuildCompound_readings_erase input target view fuel leftCursor
      left leftComputed
  obtain ⟨rightSourceReadings, rightErased⟩ :=
    sourceBuildCompound_readings_erase input target view fuel rightCursor
      right rightComputed
  have leftPriority := sourceBuildCompound_referenceCountPriority
    input target view fuel leftCursor left leftComputed
  have rightPriority := sourceBuildCompound_referenceCountPriority
    input target view fuel rightCursor right rightComputed
  exact ⟨leftSourceReadings, rightSourceReadings, leftErased, rightErased,
    sourceCompareCompoundRule4bcKeys_realizes_source_at_rule4aTie
      input left right rule4aTie leftCount rightCount
      leftSourceReadings rightSourceReadings leftCountDecoded rightCountDecoded
      leftPriority rightPriority leftErased rightErased⟩

/-! ## Kernel-authority guards for every public export -/

assert_kernel_only SourceRule4aClass
assert_kernel_only sourceRule4aClassPriority
assert_kernel_only sourceRule4aGateDecision
assert_kernel_only sourceRule4aClassToP92
assert_kernel_only sourceRule4aGateDecision_eq_rule4aDecision_of_available
assert_kernel_only SourceRule45Observation
assert_kernel_only SourceRule45Observation.rule4aClass
assert_kernel_only SourceRule45Observation.pair?
assert_kernel_only sourceRule45ObservationDecision
assert_kernel_only sourceObserveRule4aLabel
assert_kernel_only sourceObserveRule4bLabel
assert_kernel_only sourceDecodeRule45Vector?
assert_kernel_only sourceDecodeRule45Vector?_rule4a
assert_kernel_only sourceDecodeRule45Vector?_rule4b
assert_kernel_only sourceDecodeRule45Vector?_cumulativePriority
assert_kernel_only sourceDecodeRule45Vector?_eq_some_iff
assert_kernel_only compareLocalizedCumulativeRule45Priority_realizes_source
assert_kernel_only sourceRule4bReferenceCount?
assert_kernel_only sourceRule4bReferenceCount?_eq_some_iff
assert_kernel_only sourceRule4bReferenceCount?_empty
assert_kernel_only localizedRule4bReferencesFromPopulation_eq_nil_or_singleton_or_pair
assert_kernel_only sourceRule4bReferenceCount?_fromPopulation_or_empty
assert_kernel_only constitutionalRule4bReferenceCountPriority_one
assert_kernel_only constitutionalRule4bReferenceCountPriority_two
assert_kernel_only constitutionalRule4bReferenceCountPriority_empty
assert_kernel_only rule4bReferenceCountPriority_one
assert_kernel_only rule4bReferenceCountPriority_two
assert_kernel_only constitutionalRule4bReferenceCountPriority_not_source_one
assert_kernel_only compare_constitutionalRule4bReferenceCountPriorities_eq_decision
assert_kernel_only sourceSparseEntryMem
assert_kernel_only sourceSparseEntryMem_append
assert_kernel_only sourceSparseEntryMem_singleton_iff
assert_kernel_only sourceMem_of_mem_getD
assert_kernel_only sourceSparseEntryMem_mergeDescriptorChildren
assert_kernel_only sourceRule4bPathDecision
assert_kernel_only sourceRule4bPathDecision_eq_flip_compareLex
assert_kernel_only sourceSparseEntryDecision
assert_kernel_only sourceSparseLayerDecision
assert_kernel_only sourceSparseLayersDecision
assert_kernel_only sourceEraseEntry?
assert_kernel_only sourceEraseLayer?
assert_kernel_only sourceEraseLayers?
assert_kernel_only sourceCompareSparseEntry_realizes
assert_kernel_only sourceCompareSparseLayer_realizes
assert_kernel_only sourceCompareSparseLayers_realizes
assert_kernel_only sourceCompareCumulativeRule45Keys_eq_sparseSource_of_constitutionalTie
assert_kernel_only sourceBuildCumulative_descriptor_entry_label
assert_kernel_only sourceBuildCumulative_descriptor_head
assert_kernel_only sourceBuildCumulative_descriptor_erases
assert_kernel_only SourceRule4bReading
assert_kernel_only sourceEraseRule4bReading?
assert_kernel_only sourceRule4bReadingsDecision
assert_kernel_only sourceCompareReadingsByRule4b_realizes
assert_kernel_only sourceCompareRule4bReadings_realizes
assert_kernel_only sourceRule4bAfterRule4aDecision
assert_kernel_only sourceCompareAfterRule4a_realizes_source
assert_kernel_only sourceCompareCompoundRule4bcKeys_realizes_source_at_rule4aTie
assert_kernel_only sourceBuildReadings_member
assert_kernel_only sourceStageOfReference
assert_kernel_only sourceBuildReading_rule4bKey_built
assert_kernel_only sourceStageOfReference_compatible
assert_kernel_only sourceEraseRule4bReading?_of_built
assert_kernel_only sourceBuildCompound_readings_erase
assert_kernel_only sourceBuildCompound_referenceCountPriority
assert_kernel_only sourceBuildCumulative_comparison_realizes_source
assert_kernel_only sourceBuildCompound_afterRule4a_realizes_source
assert_kernel_only sourceBuildCompoundKeys_realizes_source_at_rule4aTie

end Rule4bSparseSource
end TetraStereo.OneCenter
