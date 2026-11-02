/-
Copyright (c) 2026 TetraStereo contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescription
import TetraStereo.OneCenter.OrganicStereoMolarComposition

set_option autoImplicit false

/-!
# Heterogeneous finite molecular samples with whole-record uncertainty

This module assembles a finite family of molecular constituents, each described by the actual
`WholeState` record of `OrganicStereoFiniteClassicalDescription`, together with unrestricted real
mole amounts and a supplied joint possibility set.

## Heterogeneity

A sample is indexed by an arbitrary finite component type `I`.  Each component `i : I` has its
own finite atom, edge and band types `shape.Atom i`, `shape.Edge i`, `shape.Band i`, each with its
own `Fintype` instance (and atoms with their own `DecidableEq` instance).  The component state is
the actual whole description

`FiniteClassicalStereoDescription (shape.Atom i) (shape.Edge i) (shape.Band i)`,

i.e. the repository's `WholeState` carrying the interaction hypergraph, electronic/CIP counts, the
shared real conformation, the role ledger, site evidence, path annotations, the band family, the
optional drawing data and the sparse incidence ledger.  There is no global atom type: cardinalities
`shape.atomCard i`, `shape.edgeCard i` and `shape.bandCard i` are independent functions of `i`.

Validity (`SampleData.Valid`) records exactly: the supplied whole state belongs to its supplied
full possible-state set, every amount is nonnegative, and the total amount is strictly positive.
No probability, energy, weight, CIP rule or chemical truth claim is introduced.

## Encoding

For a fixed shape, externally supplied equivalences

* `atomIndex i : shape.Atom i ≃ Fin (shape.atomCard i)`,
* `edgeIndex i : shape.Edge i ≃ Fin (shape.edgeCard i)`,
* `bandIndex i : shape.Band i ≃ Fin (shape.bandCard i)`

transport each whole state using the domain module's `encodeDescription`, and each whole
possible-state set using `encodeDescriptionSet`.  The canonical sample type mentions only the
natural-number cardinalities and the types `Fin (shape.atomCard i)`, `Fin (shape.edgeCard i)`,
`Fin (shape.bandCard i)`; the original label types do not occur.  `decodeDescription` is a
concrete inverse, and the component round trips are proved from the domain module's
`decodeDescription_encodeDescription` and `encodeDescription_decodeDescription`; no opaque
encode/decode assumption is made.

Scope boundary: every statement is for a fixed shape together with explicitly supplied
equivalences.  No encoding or injectivity claim is made across different label types or different
shapes; such a claim would require an explicit external bijection or an explicit up-to-relabel
relation, which this module does not assume.

## Amounts

Amounts are unrestricted real mole amounts, preserved exactly by encoding and decoding.  The
normalization laws are not re-derived: both sample types expose the existing
`MolarComposition.Composition` carrier (`amountComposition`) and use its `total`, `fraction`,
`total_pos'`, `fraction_nonneg`, `fraction_le_one` and `sum_fraction_eq_one`.

## Uncertainty

An uncertain sample is a `Set` of **whole** samples (`UncertainSample`).  Encoding and decoding act
on the whole set, and `decodeSet_encodeSet` recovers it exactly.  The marginal separation example
at the end uses the domain module's concrete two-atom description and shows that the component
state marginal and the amount marginal do not determine the whole sample: two distinct records
have the same marginals, so no function of those marginals reconstructs every sample.

## Residual scope

* The statements are componentwise-parametric in `I`; an unknown number of constituents is not
  packaged here as a sigma type of shapes.  That packaging is left as explicit residual work.
* No cross-label-type or cross-shape encoding claim is made.
* No chemical realizability, CIP outcome, energy, probability or dynamics is asserted.
-/

namespace TetraStereo
namespace OneCenter
namespace OrganicStereoHeterogeneousSamples

noncomputable section

open scoped BigOperators

/-! ## Independent finite types per constituent -/

/-- The finite type shape of a heterogeneous sample.  Each component has its own atom, edge and
band type and its own finiteness data; the cardinalities may differ arbitrarily between
components. -/
structure Shape (I : Type*) where
  /-- Atom type of each component. -/
  Atom : I → Type*
  /-- Edge type of each component. -/
  Edge : I → Type*
  /-- Band type of each component. -/
  Band : I → Type*
  /-- Decidable equality of each component's atoms. -/
  atomDecidableEq : ∀ i, DecidableEq (Atom i)
  /-- Finiteness of each component's atom type. -/
  atomFintype : ∀ i, Fintype (Atom i)
  /-- Finiteness of each component's edge type. -/
  edgeFintype : ∀ i, Fintype (Edge i)
  /-- Finiteness of each component's band type. -/
  bandFintype : ∀ i, Fintype (Band i)

attribute [instance] Shape.atomDecidableEq Shape.atomFintype Shape.edgeFintype
  Shape.bandFintype

namespace Shape

variable {I : Type*}

/-- Atom cardinality of one component. -/
def atomCard (shape : Shape I) (i : I) : ℕ :=
  @Fintype.card (shape.Atom i) (shape.atomFintype i)

/-- Edge cardinality of one component. -/
def edgeCard (shape : Shape I) (i : I) : ℕ :=
  @Fintype.card (shape.Edge i) (shape.edgeFintype i)

/-- Band cardinality of one component. -/
def bandCard (shape : Shape I) (i : I) : ℕ :=
  @Fintype.card (shape.Band i) (shape.bandFintype i)

end Shape

variable {I : Type*}

/-- The actual whole description of component `i`, with the shape's instances supplied
explicitly.  This is the domain module's `FiniteClassicalStereoDescription` at the component's
own atom, edge and band types. -/
abbrev ComponentState (shape : Shape I) (i : I) :=
  @FiniteClassicalStereoDescription (shape.Atom i) (shape.Edge i) (shape.Band i)
    (shape.atomDecidableEq i) (shape.atomFintype i) (shape.edgeFintype i)
    (shape.bandFintype i)

/-- The encoded whole description of component `i` at the shape's cardinalities. -/
abbrev CanonicalState (shape : Shape I) (i : I) :=
  EncodedDescription (shape.atomCard i) (shape.edgeCard i) (shape.bandCard i)

/-- Externally supplied explicit index equivalences for every component. -/
structure Indexing {I : Type*} (shape : Shape I) where
  /-- The explicit atom bijection of each component. -/
  atomIndex : ∀ i, shape.Atom i ≃ Fin (shape.atomCard i)
  /-- The explicit edge bijection of each component. -/
  edgeIndex : ∀ i, shape.Edge i ≃ Fin (shape.edgeCard i)
  /-- The explicit band bijection of each component. -/
  bandIndex : ∀ i, shape.Band i ≃ Fin (shape.bandCard i)

/-! ## Sample data, validity and the canonical schema -/

/-- The data of a heterogeneous sample: for every component an actual whole description, a full
possible-state set of whole descriptions, and an unrestricted real mole amount.

The evidence that the supplied whole description lies in its possible set and that the amounts
are valid is kept in `Valid`, so the data record has no dependent proof fields. -/
structure SampleData (I : Type*) [Fintype I] (shape : Shape I) where
  /-- The supplied whole state of each component. -/
  state : ∀ i, ComponentState shape i
  /-- The supplied full possible-state set of each component, a set of whole states. -/
  possible : ∀ i, Set (ComponentState shape i)
  /-- The unrestricted real mole amount of each component. -/
  amount : I → ℝ

namespace SampleData

variable {I : Type*} [Fintype I] {shape : Shape I}

/-- Extensionality for sample data. -/
@[ext] theorem ext {s s' : SampleData I shape}
    (state : s.state = s'.state)
    (possible : s.possible = s'.possible)
    (amount : s.amount = s'.amount) : s = s' := by
  cases s with
  | mk state' possible' amount' =>
  cases s' with
  | mk state'' possible'' amount'' =>
  simp only [SampleData.mk.injEq]
  exact ⟨state, possible, amount⟩

/-- The validity obligations: the supplied whole state belongs to its own full possible set, all
amounts are nonnegative, and the total amount is strictly positive. -/
def Valid (s : SampleData I shape) : Prop :=
  (∀ i, s.state i ∈ s.possible i) ∧
    (∀ i, 0 ≤ s.amount i) ∧
    0 < ∑ i, s.amount i

end SampleData

/-- A valid heterogeneous sample. -/
abbrev HeterogeneousSample (I : Type*) [Fintype I] (shape : Shape I) :=
  {s : SampleData I shape // s.Valid}

/-- Canonical sample data.  The state and possible-set channels use only `Fin` cardinality
indices; the original atom, edge and band types do not occur. -/
structure CanonicalData (I : Type*) [Fintype I] (shape : Shape I) where
  /-- The encoded whole state of each component. -/
  state : ∀ i, CanonicalState shape i
  /-- The encoded full possible-state set of each component. -/
  possible : ∀ i, Set (CanonicalState shape i)
  /-- The amount, carried unchanged. -/
  amount : I → ℝ

namespace CanonicalData

variable {I : Type*} [Fintype I] {shape : Shape I}

/-- Extensionality for canonical data. -/
@[ext] theorem ext {c c' : CanonicalData I shape}
    (state : c.state = c'.state)
    (possible : c.possible = c'.possible)
    (amount : c.amount = c'.amount) : c = c' := by
  cases c with
  | mk state' possible' amount' =>
  cases c' with
  | mk state'' possible'' amount'' =>
  simp only [CanonicalData.mk.injEq]
  exact ⟨state, possible, amount⟩

/-- The validity obligations for canonical data. -/
def Valid (c : CanonicalData I shape) : Prop :=
  (∀ i, c.state i ∈ c.possible i) ∧
    (∀ i, 0 ≤ c.amount i) ∧
    0 < ∑ i, c.amount i

end CanonicalData

/-- A valid canonical sample. -/
abbrev CanonicalSample (I : Type*) [Fintype I] (shape : Shape I) :=
  {c : CanonicalData I shape // c.Valid}

/-! ## Whole-description set encoding at one component -/

/-- The image of a set of whole descriptions under `decodeDescription`. -/
noncomputable def decodeDescriptionSet {V E B : Type*} [DecidableEq V] [Fintype V] [Fintype E]
    [Fintype B] (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (states : Set (EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B))) :
    Set (FiniteClassicalStereoDescription V E B) :=
  decodeDescription eV eE eB '' states

/-- Decoding the encoded image of a whole possible-state set recovers the set exactly. -/
theorem decodeDescriptionSet_encodeDescriptionSet {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (states : Set (FiniteClassicalStereoDescription V E B)) :
    decodeDescriptionSet eV eE eB (encodeDescriptionSet eV eE eB states) = states := by
  unfold decodeDescriptionSet encodeDescriptionSet
  rw [Set.image_image]
  have composed :
      (fun state => decodeDescription eV eE eB (encodeDescription eV eE eB state)) = id := by
    funext state
    exact decodeDescription_encodeDescription eV eE eB state
  rw [composed, Set.image_id]

/-- Encoding the decoded image of a set of encoded whole states recovers the set exactly. -/
theorem encodeDescriptionSet_decodeDescriptionSet {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B))
    (states : Set (EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B))) :
    encodeDescriptionSet eV eE eB (decodeDescriptionSet eV eE eB states) = states := by
  unfold decodeDescriptionSet encodeDescriptionSet
  rw [Set.image_image]
  have composed :
      (fun state => encodeDescription eV eE eB (decodeDescription eV eE eB state)) = id := by
    funext state
    exact encodeDescription_decodeDescription eV eE eB state
  rw [composed, Set.image_id]

/-- Decoding is injective; this is derived from the domain module's two inverse laws and is used
to transport membership through a decoded possible-state set. -/
theorem decodeDescription_injective {V E B : Type*} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (eV : V ≃ Fin (Fintype.card V))
    (eE : E ≃ Fin (Fintype.card E)) (eB : B ≃ Fin (Fintype.card B)) :
    Function.Injective (decodeDescription eV eE eB) := by
  intro first second equal
  have encoded := congrArg (encodeDescription eV eE eB) equal
  rwa [encodeDescription_decodeDescription, encodeDescription_decodeDescription] at encoded

/-! ## Encoding and decoding whole samples -/

variable [Fintype I] {shape : Shape I}

/-- Encode every component's whole state and whole possible-state set through the explicit
equivalences.  Amounts are copied unchanged. -/
noncomputable def encodeData (shape : Shape I) (idx : Indexing shape)
    (s : SampleData I shape) : CanonicalData I shape where
  state i := encodeDescription (idx.atomIndex i) (idx.edgeIndex i) (idx.bandIndex i)
    (s.state i)
  possible i := encodeDescriptionSet (idx.atomIndex i) (idx.edgeIndex i) (idx.bandIndex i)
    (s.possible i)
  amount := s.amount

/-- Decode canonical data to the original label types using the inverse equivalences.  The result
mentions exactly the shape's label types; no hidden raw source is retained. -/
noncomputable def decodeData (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalData I shape) : SampleData I shape where
  state i := decodeDescription (idx.atomIndex i) (idx.edgeIndex i) (idx.bandIndex i)
    (c.state i)
  possible i := decodeDescriptionSet (idx.atomIndex i) (idx.edgeIndex i) (idx.bandIndex i)
    (c.possible i)
  amount := c.amount

@[simp] theorem encodeData_state (shape : Shape I) (idx : Indexing shape)
    (s : SampleData I shape) (i : I) :
    (encodeData shape idx s).state i =
      encodeDescription (idx.atomIndex i) (idx.edgeIndex i) (idx.bandIndex i) (s.state i) :=
  rfl

@[simp] theorem encodeData_possible (shape : Shape I) (idx : Indexing shape)
    (s : SampleData I shape) (i : I) :
    (encodeData shape idx s).possible i =
      encodeDescriptionSet (idx.atomIndex i) (idx.edgeIndex i) (idx.bandIndex i)
        (s.possible i) :=
  rfl

@[simp] theorem encodeData_amount (shape : Shape I) (idx : Indexing shape)
    (s : SampleData I shape) : (encodeData shape idx s).amount = s.amount :=
  rfl

@[simp] theorem decodeData_state (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalData I shape) (i : I) :
    (decodeData shape idx c).state i =
      decodeDescription (idx.atomIndex i) (idx.edgeIndex i) (idx.bandIndex i) (c.state i) :=
  rfl

@[simp] theorem decodeData_possible (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalData I shape) (i : I) :
    (decodeData shape idx c).possible i =
      decodeDescriptionSet (idx.atomIndex i) (idx.edgeIndex i) (idx.bandIndex i)
        (c.possible i) :=
  rfl

@[simp] theorem decodeData_amount (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalData I shape) : (decodeData shape idx c).amount = c.amount :=
  rfl

/-- Encoding preserves validity. -/
theorem encodeData_valid (shape : Shape I) (idx : Indexing shape)
    (s : SampleData I shape) (valid : s.Valid) : (encodeData shape idx s).Valid := by
  refine ⟨?_, valid.2.1, valid.2.2⟩
  intro i
  exact ⟨s.state i, valid.1 i, rfl⟩

/-- Decoding preserves validity. -/
theorem decodeData_valid (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalData I shape) (valid : c.Valid) : (decodeData shape idx c).Valid := by
  refine ⟨?_, valid.2.1, valid.2.2⟩
  intro i
  exact ⟨c.state i, valid.1 i, rfl⟩

/-- Encode a valid heterogeneous sample. -/
noncomputable def encode (shape : Shape I) (idx : Indexing shape)
    (s : HeterogeneousSample I shape) : CanonicalSample I shape :=
  ⟨encodeData shape idx s.val, encodeData_valid shape idx s.val s.property⟩

/-- Decode a canonical sample to the original label types. -/
noncomputable def decode (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalSample I shape) : HeterogeneousSample I shape :=
  ⟨decodeData shape idx c.val, decodeData_valid shape idx c.val c.property⟩

@[simp] theorem encode_val (shape : Shape I) (idx : Indexing shape)
    (s : HeterogeneousSample I shape) :
    (encode shape idx s).val = encodeData shape idx s.val :=
  rfl

@[simp] theorem decode_val (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalSample I shape) :
    (decode shape idx c).val = decodeData shape idx c.val :=
  rfl

/-! ## Round trips and componentwise recovery -/

/-- Decoding encoded data recovers the original sample data exactly. -/
theorem decodeData_encodeData (shape : Shape I) (idx : Indexing shape)
    (s : SampleData I shape) : decodeData shape idx (encodeData shape idx s) = s := by
  refine SampleData.ext ?_ ?_ ?_
  · funext i
    exact decodeDescription_encodeDescription (idx.atomIndex i) (idx.edgeIndex i)
      (idx.bandIndex i) (s.state i)
  · funext i
    exact decodeDescriptionSet_encodeDescriptionSet (idx.atomIndex i) (idx.edgeIndex i)
      (idx.bandIndex i) (s.possible i)
  · rfl

/-- Encoding decoded data recovers the original canonical data exactly. -/
theorem encodeData_decodeData (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalData I shape) : encodeData shape idx (decodeData shape idx c) = c := by
  refine CanonicalData.ext ?_ ?_ ?_
  · funext i
    exact encodeDescription_decodeDescription (idx.atomIndex i) (idx.edgeIndex i)
      (idx.bandIndex i) (c.state i)
  · funext i
    exact encodeDescriptionSet_decodeDescriptionSet (idx.atomIndex i) (idx.edgeIndex i)
      (idx.bandIndex i) (c.possible i)
  · rfl

/-- Decoding an encoded whole sample recovers it exactly. -/
theorem decode_encode (shape : Shape I) (idx : Indexing shape)
    (s : HeterogeneousSample I shape) : decode shape idx (encode shape idx s) = s := by
  apply Subtype.ext
  exact decodeData_encodeData shape idx s.val

/-- Encoding a decoded canonical sample recovers it exactly. -/
theorem encode_decode (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalSample I shape) : encode shape idx (decode shape idx c) = c := by
  apply Subtype.ext
  exact encodeData_decodeData shape idx c.val

/-- For a fixed shape and fixed explicit equivalences, encoding is injective. -/
theorem encode_injective (shape : Shape I) (idx : Indexing shape) :
    Function.Injective (encode shape idx) := by
  intro s t equal
  rw [← decode_encode shape idx s, ← decode_encode shape idx t, equal]

/-- For a fixed shape and fixed explicit equivalences, decoding is injective. -/
theorem decode_injective (shape : Shape I) (idx : Indexing shape) :
    Function.Injective (decode shape idx) := by
  intro c d equal
  rw [← encode_decode shape idx c, ← encode_decode shape idx d, equal]

/-- Encoding is a bijection between samples over the fixed shape and canonical samples. -/
theorem encode_bijective (shape : Shape I) (idx : Indexing shape) :
    Function.Bijective (encode shape idx) :=
  ⟨encode_injective shape idx,
    fun c => ⟨decode shape idx c, encode_decode shape idx c⟩⟩

/-- Every component's whole state, full possible set, amount and state membership are recovered
exactly by the round trip. -/
theorem decode_encode_component (shape : Shape I) (idx : Indexing shape)
    (s : HeterogeneousSample I shape) (i : I) :
    (decode shape idx (encode shape idx s)).val.state i = s.val.state i ∧
    (decode shape idx (encode shape idx s)).val.possible i = s.val.possible i ∧
    (decode shape idx (encode shape idx s)).val.amount i = s.val.amount i ∧
    ((decode shape idx (encode shape idx s)).val.state i ∈
        (decode shape idx (encode shape idx s)).val.possible i ↔
      s.val.state i ∈ s.val.possible i) := by
  rw [decode_encode]
  exact ⟨rfl, rfl, rfl, Iff.rfl⟩

/-- Every canonical component's whole state, full possible set, amount and state membership are
recovered exactly by the reverse round trip. -/
theorem encode_decode_component (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalSample I shape) (i : I) :
    (encode shape idx (decode shape idx c)).val.state i = c.val.state i ∧
    (encode shape idx (decode shape idx c)).val.possible i = c.val.possible i ∧
    (encode shape idx (decode shape idx c)).val.amount i = c.val.amount i ∧
    ((encode shape idx (decode shape idx c)).val.state i ∈
        (encode shape idx (decode shape idx c)).val.possible i ↔
      c.val.state i ∈ c.val.possible i) := by
  rw [encode_decode]
  exact ⟨rfl, rfl, rfl, Iff.rfl⟩

/-- Encoding preserves membership of each component's supplied whole state in its full possible
set, in both directions. -/
@[simp] theorem encode_state_mem_iff (shape : Shape I) (idx : Indexing shape)
    (s : HeterogeneousSample I shape) (i : I) :
    (encode shape idx s).val.state i ∈ (encode shape idx s).val.possible i ↔
      s.val.state i ∈ s.val.possible i := by
  constructor
  · rintro ⟨source, hsource, hsourceEq⟩
    have hsourceEq' :
        encodeDescription (idx.atomIndex i) (idx.edgeIndex i) (idx.bandIndex i) source =
          encodeDescription (idx.atomIndex i) (idx.edgeIndex i) (idx.bandIndex i)
            (s.val.state i) :=
      hsourceEq
    have source_eq : source = s.val.state i :=
      encodeDescription_injective _ _ _ hsourceEq'
    rwa [source_eq] at hsource
  · intro h
    exact ⟨s.val.state i, h, rfl⟩

/-- Decoding preserves membership of each canonical component's state in its possible set, in
both directions. -/
@[simp] theorem decode_state_mem_iff (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalSample I shape) (i : I) :
    (decode shape idx c).val.state i ∈ (decode shape idx c).val.possible i ↔
      c.val.state i ∈ c.val.possible i := by
  constructor
  · rintro ⟨source, hsource, hsourceEq⟩
    have hsourceEq' :
        decodeDescription (idx.atomIndex i) (idx.edgeIndex i) (idx.bandIndex i) source =
          decodeDescription (idx.atomIndex i) (idx.edgeIndex i) (idx.bandIndex i)
            (c.val.state i) :=
      hsourceEq
    have source_eq : source = c.val.state i :=
      decodeDescription_injective _ _ _ hsourceEq'
    rwa [source_eq] at hsource
  · intro h
    exact ⟨c.val.state i, h, rfl⟩

/-! ## Amounts: exact preservation and existing molar-composition laws -/

namespace HeterogeneousSample

/-- The amount view of a heterogeneous sample using the existing `MolarComposition.Composition`
carrier with exactly the sample's amounts. -/
def amountComposition (s : HeterogeneousSample I shape) :
    MolarComposition.Composition I Unit where
  species := fun _ => ()
  amount := s.val.amount
  amount_nonneg := s.property.2.1
  total_pos := s.property.2.2

/-- The composition's amount is literally the sample's amount. -/
@[simp] theorem amountComposition_amount (s : HeterogeneousSample I shape) (i : I) :
    (amountComposition s).amount i = s.val.amount i := rfl

/-- The total amount, inherited from the existing molar composition. -/
def total (s : HeterogeneousSample I shape) : ℝ := (amountComposition s).total

/-- The total is the sum of the sample's amounts. -/
@[simp] theorem total_eq_sum (s : HeterogeneousSample I shape) :
    s.total = ∑ i, s.val.amount i := rfl

/-- Strict positivity of the total amount, from the existing composition law. -/
theorem total_pos (s : HeterogeneousSample I shape) : 0 < s.total :=
  (amountComposition s).total_pos'

/-- The normalized mole fraction, inherited from the existing molar composition. -/
def fraction (s : HeterogeneousSample I shape) (i : I) : ℝ :=
  (amountComposition s).fraction i

/-- The fraction is the amount divided by the total. -/
@[simp] theorem fraction_eq (s : HeterogeneousSample I shape) (i : I) :
    s.fraction i = s.val.amount i / s.total := rfl

/-- Fraction nonnegativity, from the existing composition law. -/
theorem fraction_nonneg (s : HeterogeneousSample I shape) (i : I) : 0 ≤ s.fraction i :=
  (amountComposition s).fraction_nonneg i

/-- Fraction upper bound, from the existing composition law. -/
theorem fraction_le_one (s : HeterogeneousSample I shape) (i : I) : s.fraction i ≤ 1 :=
  (amountComposition s).fraction_le_one i

/-- Strong normalization, from the existing composition law. -/
theorem sum_fraction_eq_one (s : HeterogeneousSample I shape) :
    ∑ i, s.fraction i = 1 :=
  (amountComposition s).sum_fraction_eq_one

end HeterogeneousSample

namespace CanonicalSample

/-- The amount view of a canonical sample using the existing `MolarComposition.Composition`
carrier. -/
def amountComposition (c : CanonicalSample I shape) :
    MolarComposition.Composition I Unit where
  species := fun _ => ()
  amount := c.val.amount
  amount_nonneg := c.property.2.1
  total_pos := c.property.2.2

/-- The composition's amount is literally the canonical sample's amount. -/
@[simp] theorem amountComposition_amount (c : CanonicalSample I shape) (i : I) :
    (amountComposition c).amount i = c.val.amount i := rfl

/-- The total amount, inherited from the existing molar composition. -/
def total (c : CanonicalSample I shape) : ℝ := (amountComposition c).total

/-- The total is the sum of the canonical sample's amounts. -/
@[simp] theorem total_eq_sum (c : CanonicalSample I shape) :
    c.total = ∑ i, c.val.amount i := rfl

/-- Strict positivity of the total amount, from the existing composition law. -/
theorem total_pos (c : CanonicalSample I shape) : 0 < c.total :=
  (amountComposition c).total_pos'

/-- The normalized mole fraction, inherited from the existing molar composition. -/
def fraction (c : CanonicalSample I shape) (i : I) : ℝ :=
  (amountComposition c).fraction i

/-- The fraction is the amount divided by the total. -/
@[simp] theorem fraction_eq (c : CanonicalSample I shape) (i : I) :
    c.fraction i = c.val.amount i / c.total := rfl

/-- Fraction nonnegativity, from the existing composition law. -/
theorem fraction_nonneg (c : CanonicalSample I shape) (i : I) : 0 ≤ c.fraction i :=
  (amountComposition c).fraction_nonneg i

/-- Fraction upper bound, from the existing composition law. -/
theorem fraction_le_one (c : CanonicalSample I shape) (i : I) : c.fraction i ≤ 1 :=
  (amountComposition c).fraction_le_one i

/-- Strong normalization, from the existing composition law. -/
theorem sum_fraction_eq_one (c : CanonicalSample I shape) :
    ∑ i, c.fraction i = 1 :=
  (amountComposition c).sum_fraction_eq_one

end CanonicalSample

/-- Encoding preserves every component amount exactly. -/
@[simp] theorem encode_amount (shape : Shape I) (idx : Indexing shape)
    (s : HeterogeneousSample I shape) (i : I) :
    (encode shape idx s).val.amount i = s.val.amount i := rfl

/-- Encoding preserves the total amount exactly. -/
@[simp] theorem encode_total (shape : Shape I) (idx : Indexing shape)
    (s : HeterogeneousSample I shape) :
    (encode shape idx s).total = s.total := rfl

/-- Encoding preserves every normalized mole fraction exactly. -/
theorem encode_fraction (shape : Shape I) (idx : Indexing shape)
    (s : HeterogeneousSample I shape) (i : I) :
    (encode shape idx s).fraction i = s.fraction i := rfl

/-- Decoding preserves every component amount exactly. -/
@[simp] theorem decode_amount (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalSample I shape) (i : I) :
    (decode shape idx c).val.amount i = c.val.amount i := rfl

/-- Decoding preserves the total amount exactly. -/
@[simp] theorem decode_total (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalSample I shape) :
    (decode shape idx c).total = c.total := rfl

/-- Decoding preserves every normalized mole fraction exactly. -/
theorem decode_fraction (shape : Shape I) (idx : Indexing shape)
    (c : CanonicalSample I shape) (i : I) :
    (decode shape idx c).fraction i = c.fraction i := rfl

/-! ## Uncertainty over whole samples -/

/-- An uncertain sample over a fixed shape: a set of whole samples.  Membership records joint
possibility of the entire record; it is not a product of component marginals and carries no
probability, energy or weight. -/
abbrev UncertainSample (I : Type*) [Fintype I] (shape : Shape I) :=
  Set (HeterogeneousSample I shape)

namespace UncertainSample

/-- Consistency of an uncertain sample: at least one whole record. -/
def Consistent (U : UncertainSample I shape) : Prop :=
  U.Nonempty

@[simp] theorem consistent_iff (U : UncertainSample I shape) :
    Consistent U ↔ U.Nonempty := Iff.rfl

theorem consistent_of_mem {U : UncertainSample I shape} {s : HeterogeneousSample I shape}
    (member : s ∈ U) : Consistent U :=
  ⟨s, member⟩

@[simp] theorem not_consistent_empty :
    ¬ Consistent (∅ : UncertainSample I shape) := by
  simp [Consistent]

/-- The image of a whole uncertain sample under encoding. -/
def encodeSet (shape : Shape I) (idx : Indexing shape) (U : UncertainSample I shape) :
    Set (CanonicalSample I shape) :=
  encode shape idx '' U

/-- The image of a set of canonical samples under decoding. -/
def decodeSet (shape : Shape I) (idx : Indexing shape)
    (V : Set (CanonicalSample I shape)) : UncertainSample I shape :=
  decode shape idx '' V

@[simp] theorem mem_encodeSet_iff (shape : Shape I) (idx : Indexing shape)
    (U : UncertainSample I shape) (c : CanonicalSample I shape) :
    c ∈ encodeSet shape idx U ↔ ∃ s ∈ U, encode shape idx s = c := Iff.rfl

@[simp] theorem mem_decodeSet_iff (shape : Shape I) (idx : Indexing shape)
    (V : Set (CanonicalSample I shape)) (s : HeterogeneousSample I shape) :
    s ∈ decodeSet shape idx V ↔ ∃ c ∈ V, decode shape idx c = s := Iff.rfl

/-- Encoding and then decoding a whole uncertain sample recovers it exactly, including the joint
state/amount pairing of every record. -/
theorem decodeSet_encodeSet (shape : Shape I) (idx : Indexing shape)
    (U : UncertainSample I shape) :
    decodeSet shape idx (encodeSet shape idx U) = U := by
  ext s
  constructor
  · rintro ⟨c, ⟨s0, hs0, rfl⟩, hdec⟩
    rw [decode_encode] at hdec
    rwa [← hdec]
  · intro hs
    exact ⟨encode shape idx s, ⟨s, hs, rfl⟩, decode_encode shape idx s⟩

/-- Decoding and then re-encoding a set of canonical samples recovers it exactly. -/
theorem encodeSet_decodeSet (shape : Shape I) (idx : Indexing shape)
    (V : Set (CanonicalSample I shape)) :
    encodeSet shape idx (decodeSet shape idx V) = V := by
  ext c
  constructor
  · rintro ⟨s, ⟨c0, hc0, rfl⟩, hdec⟩
    rw [encode_decode] at hdec
    rwa [← hdec]
  · intro hc
    exact ⟨decode shape idx c, ⟨c, hc, rfl⟩, encode_decode shape idx c⟩

/-- Consistency is preserved and reflected by encoding. -/
@[simp] theorem nonempty_encodeSet_iff (shape : Shape I) (idx : Indexing shape)
    (U : UncertainSample I shape) :
    (encodeSet shape idx U).Nonempty ↔ Consistent U := by
  constructor
  · rintro ⟨c, hc⟩
    obtain ⟨s, hs, _⟩ := hc
    exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨encode shape idx s, s, hs, rfl⟩

/-- Consistency is preserved and reflected by decoding. -/
@[simp] theorem nonempty_decodeSet_iff (shape : Shape I) (idx : Indexing shape)
    (V : Set (CanonicalSample I shape)) :
    (decodeSet shape idx V).Nonempty ↔ V.Nonempty := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨c, hc, _⟩ := hs
    exact ⟨c, hc⟩
  · rintro ⟨c, hc⟩
    exact ⟨decode shape idx c, c, hc, rfl⟩

end UncertainSample

/-! ## Marginal separation on the concrete whole description

The domain module supplies a concrete two-atom description with one interaction, one role and one
path.  Two whole samples below use that description at both components and swap the amounts `2`
and `1`.  Their component-state marginals are equal and their amount marginals are equal, yet the
whole samples differ at component `0`, so no function of those marginals reconstructs every
sample. -/

namespace MarginalSeparation

/-- Both components have two atoms, one edge (a bond path) and no bands, matching the concrete
description from the domain module. -/
def exampleShape : Shape (Fin 2) where
  Atom := fun _ => Fin 2
  Edge := fun _ => Fin 1
  Band := fun _ => Fin 0
  atomDecidableEq := fun _ => inferInstance
  atomFintype := fun _ => inferInstance
  edgeFintype := fun _ => inferInstance
  bandFintype := fun _ => inferInstance

/-- The actual concrete whole description from the domain module. -/
def componentState : FiniteClassicalStereoDescription (Fin 2) (Fin 1) (Fin 0) :=
  FiniteClassicalStereoDescriptionExample.description

/-- Amount vector `(2, 1)`, reusing the existing binary amount constructor. -/
def amountA : Fin 2 → ℝ := MolarComposition.Composition.binaryAmount 2 1

/-- Amount vector `(1, 2)`. -/
def amountB : Fin 2 → ℝ := MolarComposition.Composition.binaryAmount 1 2

/-- A valid composition with amounts `(2, 1)`, used only to inherit the existing amount laws. -/
def compositionA : MolarComposition.Composition (Fin 2) Unit :=
  MolarComposition.Composition.binary () () 2 1 (by norm_num) (by norm_num) (by norm_num)

/-- A valid composition with amounts `(1, 2)`. -/
def compositionB : MolarComposition.Composition (Fin 2) Unit :=
  MolarComposition.Composition.binary () () 1 2 (by norm_num) (by norm_num) (by norm_num)

/-- The first entry of the binary amount vector. -/
@[simp] theorem binaryAmount_zero (first second : ℝ) :
    MolarComposition.Composition.binaryAmount first second 0 = first := by
  simp only [MolarComposition.Composition.binaryAmount, Fin.cases_zero]

/-- The second entry of the binary amount vector. -/
@[simp] theorem binaryAmount_one (first second : ℝ) :
    MolarComposition.Composition.binaryAmount first second 1 = second := by
  rw [← Fin.succ_zero_eq_one]
  simp only [MolarComposition.Composition.binaryAmount, Fin.cases_succ]

/-- Nonnegativity of the amount vector `(2,1)`, inherited from the binary composition. -/
theorem amountA_nonneg : ∀ i, 0 ≤ amountA i :=
  compositionA.amount_nonneg

/-- Strict positivity of the total of `(2,1)`, inherited from the binary composition. -/
theorem amountA_total_pos : 0 < ∑ i, amountA i :=
  compositionA.total_pos

/-- Nonnegativity of the amount vector `(1,2)`, inherited from the binary composition. -/
theorem amountB_nonneg : ∀ i, 0 ≤ amountB i :=
  compositionB.amount_nonneg

/-- Strict positivity of the total of `(1,2)`, inherited from the binary composition. -/
theorem amountB_total_pos : 0 < ∑ i, amountB i :=
  compositionB.total_pos

/-- Sample data with amounts `(2,1)` and both components in the full possible set. -/
def dataA : SampleData (Fin 2) exampleShape where
  state := fun _ => componentState
  possible := fun _ => Set.univ
  amount := amountA

/-- Sample data with amounts `(1,2)` and both components in the full possible set. -/
def dataB : SampleData (Fin 2) exampleShape where
  state := fun _ => componentState
  possible := fun _ => Set.univ
  amount := amountB

/-- The data with amounts `(2,1)` is valid. -/
theorem dataA_valid : dataA.Valid :=
  ⟨fun _ => Set.mem_univ _, amountA_nonneg, amountA_total_pos⟩

/-- The data with amounts `(1,2)` is valid. -/
theorem dataB_valid : dataB.Valid :=
  ⟨fun _ => Set.mem_univ _, amountB_nonneg, amountB_total_pos⟩

/-- The first whole sample: both components carry the concrete description; amounts are `(2, 1)`. -/
def sampleA : HeterogeneousSample (Fin 2) exampleShape := ⟨dataA, dataA_valid⟩

/-- The second whole sample: the same component states; amounts are `(1, 2)`. -/
def sampleB : HeterogeneousSample (Fin 2) exampleShape := ⟨dataB, dataB_valid⟩

/-- The component-state marginal of a whole sample. -/
def stateMarginal (s : HeterogeneousSample (Fin 2) exampleShape) :
    Set (FiniteClassicalStereoDescription (Fin 2) (Fin 1) (Fin 0)) :=
  {state | state = s.val.state 0 ∨ state = s.val.state 1}

/-- The component-amount marginal of a whole sample. -/
def amountMarginal (s : HeterogeneousSample (Fin 2) exampleShape) : Set ℝ :=
  {amount | amount = s.val.amount 0 ∨ amount = s.val.amount 1}

/-- The pair of marginals of a whole sample. -/
def marginal (s : HeterogeneousSample (Fin 2) exampleShape) :
    Set (FiniteClassicalStereoDescription (Fin 2) (Fin 1) (Fin 0)) × Set ℝ :=
  (stateMarginal s, amountMarginal s)

/-- The two whole samples have the same component-state marginal. -/
theorem stateMarginal_A_eq_B : stateMarginal sampleA = stateMarginal sampleB := by
  rfl

/-- The two whole samples have the same component-amount marginal. -/
theorem amountMarginal_A_eq_B : amountMarginal sampleA = amountMarginal sampleB := by
  ext amount
  simp only [amountMarginal, Set.mem_setOf_eq]
  have hA : sampleA.val.amount = amountA := rfl
  have hB : sampleB.val.amount = amountB := rfl
  rw [hA, hB]
  simp only [amountA, amountB, binaryAmount_zero, binaryAmount_one]
  exact or_comm

/-- Both whole samples have identical marginals. -/
theorem marginals_eq : marginal sampleA = marginal sampleB := by
  simp only [marginal]
  rw [stateMarginal_A_eq_B, amountMarginal_A_eq_B]

/-- The whole samples are nevertheless distinct: component `0` carries amount `2` in the first
and amount `1` in the second. -/
theorem sampleA_ne_sampleB : sampleA ≠ sampleB := by
  intro equal
  have atZero :
      sampleA.val.amount 0 = sampleB.val.amount 0 :=
    congrArg (fun s : HeterogeneousSample (Fin 2) exampleShape => s.val.amount 0) equal
  have left : sampleA.val.amount 0 = 2 := by
    show MolarComposition.Composition.binaryAmount 2 1 (0 : Fin 2) = 2
    simp only [MolarComposition.Composition.binaryAmount, Fin.cases_zero]
  have right : sampleB.val.amount 0 = 1 := by
    show MolarComposition.Composition.binaryAmount 1 2 (0 : Fin 2) = 1
    simp only [MolarComposition.Composition.binaryAmount, Fin.cases_zero]
  rw [left, right] at atZero
  norm_num at atZero

/-- No function of the state marginal and the amount marginal reconstructs every whole sample. -/
theorem no_reconstruction_from_marginals :
    ¬ ∃ reconstruct : Set (FiniteClassicalStereoDescription (Fin 2) (Fin 1) (Fin 0)) →
        Set ℝ → HeterogeneousSample (Fin 2) exampleShape,
      ∀ s, reconstruct (stateMarginal s) (amountMarginal s) = s := by
  rintro ⟨reconstruct, recovers⟩
  have same :
      reconstruct (stateMarginal sampleA) (amountMarginal sampleA) =
        reconstruct (stateMarginal sampleB) (amountMarginal sampleB) := by
    rw [stateMarginal_A_eq_B, amountMarginal_A_eq_B]
  rw [recovers sampleA, recovers sampleB] at same
  exact sampleA_ne_sampleB same

/-- The uncertainty set containing both correlated records.  It is a set of whole samples, so each
record's state/amount pairing is retained. -/
def correlatedUncertainty : UncertainSample (Fin 2) exampleShape :=
  {sampleA, sampleB}

/-- The correlated uncertainty set is consistent. -/
theorem correlatedUncertainty_consistent :
    UncertainSample.Consistent correlatedUncertainty :=
  UncertainSample.consistent_of_mem (s := sampleA) (by simp [correlatedUncertainty])

end MarginalSeparation

end

end OrganicStereoHeterogeneousSamples
end OneCenter
end TetraStereo
