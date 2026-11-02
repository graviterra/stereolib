/-
Copyright (c) 2026 TetraStereo contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TetraStereo.OneCenter.OrganicStereoHeterogeneousSamples

set_option autoImplicit false

/-!
# Variable-shape exact uncertainty domain for heterogeneous molecular samples

`OrganicStereoHeterogeneousSamples` fixes a finite constituent index type `I` and a `Shape I`
together with an `Indexing`.  This module packages the *variable* case as a genuine dependent sum:
the constituent index type, its `Fintype` witness, the per-constituent atom/edge/band label types
and the explicit enumerations are all part of the record.

Two packages are defined:

* `UniversalSample` is the dependent sum over a `UniversalShape` of an actual
  `HeterogeneousSample`, i.e. actual `WholeState`s with unrestricted real mole amounts and the
  supplied joint possibility set.
* `UniversalCanonical` is the dependent sum over the same `UniversalShape` of an actual
  `CanonicalSample`, whose state channel is exactly the existing `EncodedDescription` produced by
  `OrganicStereoHeterogeneousSamples.encode`.

The second component of a `UniversalCanonical` therefore contains **no** original `WholeState`
and no original source record: it is the existing canonical sample.  The retained shape and
indexing data are legitimate *indexing witnesses* (label types and their enumerations), not a copy
of the sample's state, amounts or possibility set.

## Identity versus quotienting

`decodeUniversal_encodeUniversal` and `encodeUniversal_decodeUniversal` are exact identities of the
whole dependent record, including the witness.  `encodeUniversal` is injective.  Nothing here forms
a quotient by graph isomorphism or by any relabelling relation: two distinct whole records remain
distinct under encoding.  See `encodeUniversal_eq_iff`.

## Scope

The general set-image theorems are parametric in the `UniversalShape`, so they apply to samples
whose constituent counts and whose per-constituent atom, edge and band counts all differ.  The
concrete section instantiates this with actual physical whole states: no `Unit` surrogate is used
for the state channel and no artificial padding is employed.  The existing
`HeterogeneousSample.amountComposition` has species type `Unit`; that is deliberately the pure
amount projection of the source module and is not treated here as a data-loss bug of the state
codec.  A faithful species-weighted observable over the actual constituent carrier is supplied
separately (`speciesWeighted`), together with exact recovery of each constituent's amount and a
pushforward theorem along the existing encode/decode pair.

No probability, energy, CIP outcome, chemical realizability or graph-isomorphism semantics is
asserted.  `MixedSourceSamples` composition is not part of this module.
-/

namespace TetraStereo
namespace OneCenter
namespace OrganicStereoUniversalMixtureSamples

noncomputable section

open scoped BigOperators
open scoped Classical

open OrganicStereoHeterogeneousSamples

/-! ## The dependent shape/indexing witness -/

/-- A variable shape: a finite constituent index type, its finiteness witness, the per-constituent
atom, edge and band label types, and the explicit enumerations of those label types.  The label
types and enumerations are indexing witnesses.  No molecular state, amount or possibility set is
stored here. -/
structure UniversalShape where
  /-- The finite type of constituents. -/
  I : Type
  /-- Finiteness of the constituent index type. -/
  fintypeI : Fintype I
  /-- The atom, edge and band label types of every constituent. -/
  shape : Shape I
  /-- Explicit enumeration witnesses for every constituent. -/
  indexing : Indexing shape

attribute [instance] UniversalShape.fintypeI

/-- A variable-shape heterogeneous sample: the shape/indexing witness together with the actual
heterogeneous sample over that shape.  The second component is the source module's
`HeterogeneousSample`, carrying actual `WholeState`s, unrestricted real amounts and the supplied
joint possibility set. -/
abbrev UniversalSample := Σ U : UniversalShape, HeterogeneousSample U.I U.shape

/-- A variable-shape canonical sample: the same shape/indexing witness together with the source
module's `CanonicalSample`.  The state channel of the second component is exactly the existing
canonical encoding; no original `WholeState`, amount or possibility set is retained as an escape
field. -/
abbrev UniversalCanonical := Σ U : UniversalShape, CanonicalSample U.I U.shape

/-- The number of constituents. -/
def constituentCount (U : UniversalShape) : ℕ :=
  @Fintype.card U.I U.fintypeI

/-- The total number of atom labels across all constituents. -/
def totalAtomCount (U : UniversalShape) : ℕ :=
  ∑ i : U.I, U.shape.atomCard i

/-- The total number of edge labels across all constituents. -/
def totalEdgeCount (U : UniversalShape) : ℕ :=
  ∑ i : U.I, U.shape.edgeCard i

/-- The total number of band labels across all constituents. -/
def totalBandCount (U : UniversalShape) : ℕ :=
  ∑ i : U.I, U.shape.bandCard i

/-! ## Encoding and decoding the whole dependent record -/

/-- Encode a universal sample: the witness is retained verbatim and the sample is sent to the
existing canonical sample by the source module's `encode`. -/
def encodeUniversal (x : UniversalSample) : UniversalCanonical :=
  ⟨x.1, OrganicStereoHeterogeneousSamples.encode x.1.shape x.1.indexing x.2⟩

/-- Decode a universal canonical sample using the source module's concrete `decode`. -/
def decodeUniversal (c : UniversalCanonical) : UniversalSample :=
  ⟨c.1, OrganicStereoHeterogeneousSamples.decode c.1.shape c.1.indexing c.2⟩

@[simp] theorem encodeUniversal_shape (x : UniversalSample) :
    (encodeUniversal x).1 = x.1 := rfl

/-- The canonical component is literally the existing `encode`; it is not an additional field. -/
@[simp] theorem encodeUniversal_sample (x : UniversalSample) :
    (encodeUniversal x).2 =
      OrganicStereoHeterogeneousSamples.encode x.1.shape x.1.indexing x.2 := rfl

@[simp] theorem decodeUniversal_shape (c : UniversalCanonical) :
    (decodeUniversal c).1 = c.1 := rfl

/-- The decoded component is literally the existing `decode`; no hidden source is consulted. -/
@[simp] theorem decodeUniversal_sample (c : UniversalCanonical) :
    (decodeUniversal c).2 =
      OrganicStereoHeterogeneousSamples.decode c.1.shape c.1.indexing c.2 := rfl

/-- Decoding an encoded universal sample recovers the whole dependent record, witness included. -/
theorem decodeUniversal_encodeUniversal (x : UniversalSample) :
    decodeUniversal (encodeUniversal x) = x := by
  obtain ⟨U, s⟩ := x
  simp only [encodeUniversal, decodeUniversal]
  rw [OrganicStereoHeterogeneousSamples.decode_encode]

/-- Encoding a decoded universal canonical sample recovers the whole dependent record. -/
theorem encodeUniversal_decodeUniversal (c : UniversalCanonical) :
    encodeUniversal (decodeUniversal c) = c := by
  obtain ⟨U, c⟩ := c
  simp only [encodeUniversal, decodeUniversal]
  rw [OrganicStereoHeterogeneousSamples.encode_decode]

/-- For the fixed dependent package, encoding is injective. -/
theorem encodeUniversal_injective : Function.Injective encodeUniversal := by
  intro x y equal
  rw [← decodeUniversal_encodeUniversal x, ← decodeUniversal_encodeUniversal y, equal]

/-- For the fixed dependent package, decoding is injective. -/
theorem decodeUniversal_injective : Function.Injective decodeUniversal := by
  intro c d equal
  rw [← encodeUniversal_decodeUniversal c, ← encodeUniversal_decodeUniversal d, equal]

/-- Encoding is a bijection between universal samples and universal canonical samples. -/
theorem encodeUniversal_bijective : Function.Bijective encodeUniversal :=
  ⟨encodeUniversal_injective,
    fun c => ⟨decodeUniversal c, encodeUniversal_decodeUniversal c⟩⟩

/-- Exact identity, not a quotient: two universal samples have equal canonical images exactly when
they are equal.  In particular no graph-isomorphism or relabelling quotient is formed. -/
theorem encodeUniversal_eq_iff (x y : UniversalSample) :
    encodeUniversal x = encodeUniversal y ↔ x = y :=
  ⟨fun h => encodeUniversal_injective h, fun h => congrArg encodeUniversal h⟩

/-! ## Whole-set image recovery -/

/-- The image of a variable-shape uncertain sample (a set of whole records) under encoding. -/
def encodeSet (U : Set UniversalSample) : Set UniversalCanonical :=
  encodeUniversal '' U

/-- The image of a set of universal canonical samples under decoding. -/
def decodeSet (V : Set UniversalCanonical) : Set UniversalSample :=
  decodeUniversal '' V

@[simp] theorem mem_encodeSet_iff {U : Set UniversalSample} {c : UniversalCanonical} :
    c ∈ encodeSet U ↔ ∃ x ∈ U, encodeUniversal x = c := Iff.rfl

@[simp] theorem mem_decodeSet_iff {V : Set UniversalCanonical} {x : UniversalSample} :
    x ∈ decodeSet V ↔ ∃ c ∈ V, decodeUniversal c = x := Iff.rfl

/-- Encoding and then decoding recovers an arbitrary correlated whole-sample set exactly.  The
statement is parametric in the dependent shape package, so it covers samples with different
constituent counts and different per-constituent atom, edge and band counts. -/
theorem decodeSet_encodeSet (U : Set UniversalSample) :
    decodeSet (encodeSet U) = U := by
  ext x
  constructor
  · rintro ⟨c, ⟨s, hs, rfl⟩, hx⟩
    rw [decodeUniversal_encodeUniversal] at hx
    exact hx ▸ hs
  · intro hx
    exact ⟨encodeUniversal x, ⟨x, hx, rfl⟩, decodeUniversal_encodeUniversal x⟩

/-- Decoding and then re-encoding recovers an arbitrary set of canonical samples exactly. -/
theorem encodeSet_decodeSet (V : Set UniversalCanonical) :
    encodeSet (decodeSet V) = V := by
  ext c
  constructor
  · rintro ⟨x, ⟨c0, hc0, rfl⟩, hc⟩
    rw [encodeUniversal_decodeUniversal] at hc
    exact hc ▸ hc0
  · intro hc
    exact ⟨decodeUniversal c, ⟨c, hc, rfl⟩, encodeUniversal_decodeUniversal c⟩

/-- Consistency (nonemptiness) is preserved and reflected by encoding. -/
@[simp] theorem nonempty_encodeSet_iff (U : Set UniversalSample) :
    (encodeSet U).Nonempty ↔ U.Nonempty :=
  ⟨fun ⟨_, x, hx, _⟩ => ⟨x, hx⟩, fun ⟨x, hx⟩ => ⟨encodeUniversal x, x, hx, rfl⟩⟩

/-- Consistency (nonemptiness) is preserved and reflected by decoding. -/
@[simp] theorem nonempty_decodeSet_iff (V : Set UniversalCanonical) :
    (decodeSet V).Nonempty ↔ V.Nonempty :=
  ⟨fun ⟨_, c, hc, _⟩ => ⟨c, hc⟩, fun ⟨c, hc⟩ => ⟨decodeUniversal c, c, hc, rfl⟩⟩

/-! ## The actual constituent carrier and a faithful species-weighted observable

The carrier of a variable-shape sample is the dependent sum of the constituent index with the
actual whole state at that index.  It therefore preserves repeated occurrences: two constituents
with identical states are still distinct carrier points because their indices differ.
-/

/-- The actual constituent carrier: every index together with its actual whole state. -/
abbrev ConstituentCarrier (U : UniversalShape) : Type _ :=
  Σ i : U.I, ComponentState U.shape i

/-- The canonical constituent carrier: every index together with its existing canonical state. -/
abbrev CanonicalCarrier (U : UniversalShape) : Type _ :=
  Σ i : U.I, CanonicalState U.shape i

/-- The existing concrete encoding, lifted fibrewise to the constituent carrier. -/
def carrierEncode (U : UniversalShape) : ConstituentCarrier U → CanonicalCarrier U :=
  fun p => ⟨p.1, encodeDescription (U.indexing.atomIndex p.1) (U.indexing.edgeIndex p.1)
    (U.indexing.bandIndex p.1) p.2⟩

/-- The existing concrete decoding, lifted fibrewise to the constituent carrier. -/
def carrierDecode (U : UniversalShape) : CanonicalCarrier U → ConstituentCarrier U :=
  fun p => ⟨p.1, decodeDescription (U.indexing.atomIndex p.1) (U.indexing.edgeIndex p.1)
    (U.indexing.bandIndex p.1) p.2⟩

/-- Decoding an encoded carrier point recovers it exactly; the index is retained. -/
theorem carrierDecode_carrierEncode (U : UniversalShape) (p : ConstituentCarrier U) :
    carrierDecode U (carrierEncode U p) = p := by
  obtain ⟨i, state⟩ := p
  show (⟨i, decodeDescription (U.indexing.atomIndex i) (U.indexing.edgeIndex i)
      (U.indexing.bandIndex i)
      (encodeDescription (U.indexing.atomIndex i) (U.indexing.edgeIndex i)
        (U.indexing.bandIndex i) state)⟩ : ConstituentCarrier U) = ⟨i, state⟩
  rw [decodeDescription_encodeDescription]

/-- Encoding a decoded carrier point recovers it exactly; the index is retained. -/
theorem carrierEncode_carrierDecode (U : UniversalShape) (p : CanonicalCarrier U) :
    carrierEncode U (carrierDecode U p) = p := by
  obtain ⟨i, state⟩ := p
  show (⟨i, encodeDescription (U.indexing.atomIndex i) (U.indexing.edgeIndex i)
      (U.indexing.bandIndex i)
      (decodeDescription (U.indexing.atomIndex i) (U.indexing.edgeIndex i)
        (U.indexing.bandIndex i) state)⟩ : CanonicalCarrier U) = ⟨i, state⟩
  rw [encodeDescription_decodeDescription]

/-- The composition that retains the actual species/identity of every constituent: the species
datum is the actual whole state together with its index, and the amounts are the sample's actual
real amounts.  This is the faithful refinement of the `Unit`-species amount projection of the
source module. -/
def speciesComposition (U : UniversalShape) (s : HeterogeneousSample U.I U.shape) :
    MolarComposition.Composition U.I (ConstituentCarrier U) where
  species := fun i => ⟨i, s.val.state i⟩
  amount := s.val.amount
  amount_nonneg := s.property.2.1
  total_pos := s.property.2.2

@[simp] theorem speciesComposition_amount (U : UniversalShape)
    (s : HeterogeneousSample U.I U.shape) (i : U.I) :
    (speciesComposition U s).amount i = s.val.amount i := rfl

/-- The species composition's amount is exactly the source amount projection.  The `Unit` species
of `amountComposition` is a projection, not a loss of the state codec. -/
theorem speciesComposition_amount_eq_amountComposition (U : UniversalShape)
    (s : HeterogeneousSample U.I U.shape) (i : U.I) :
    (speciesComposition U s).amount i = (HeterogeneousSample.amountComposition s).amount i := rfl

/-- The species composition has the same total as the sample. -/
theorem speciesComposition_total (U : UniversalShape)
    (s : HeterogeneousSample U.I U.shape) :
    (speciesComposition U s).total = s.total := by
  rw [MolarComposition.Composition.total_eq_sum, HeterogeneousSample.total_eq_sum]
  rfl

/-- The species-weighted observable over the actual constituent carrier: every constituent
contributes its actual real amount times the observable evaluated at the pair (index, actual whole
state).  Because the carrier retains the index, identical states at different occurrences are
neither merged nor deduplicated. -/
def speciesWeighted (U : UniversalShape) (s : HeterogeneousSample U.I U.shape)
    (φ : ConstituentCarrier U → ℝ) : ℝ :=
  ∑ i : U.I, s.val.amount i * φ ⟨i, s.val.state i⟩

/-- The observable is exactly the existing amount-weighted observable of the species composition. -/
theorem speciesWeighted_eq_amountWeighted (U : UniversalShape)
    (s : HeterogeneousSample U.I U.shape) (φ : ConstituentCarrier U → ℝ) :
    speciesWeighted U s φ =
      MolarComposition.Composition.amountWeighted (speciesComposition U s) φ := rfl

/-- The canonical analogue of the species-weighted observable. -/
def canonicalSpeciesWeighted (U : UniversalShape) (c : CanonicalSample U.I U.shape)
    (φ : CanonicalCarrier U → ℝ) : ℝ :=
  ∑ i : U.I, c.val.amount i * φ ⟨i, c.val.state i⟩

/-- Index indicator over the actual constituent carrier.  It separates the occurrence labelled by
`i0` from every other occurrence, even when the states coincide. -/
def indexIndicator (U : UniversalShape) (i0 : U.I) : ConstituentCarrier U → ℝ :=
  fun p => if p.1 = i0 then 1 else 0

/-- Exact recovery of every constituent amount from the species-weighted observable: the indicator
of an occurrence reads off exactly that occurrence's actual real amount.  Repeated occurrences with
identical states are counted separately. -/
theorem speciesWeighted_indexIndicator (U : UniversalShape)
    (s : HeterogeneousSample U.I U.shape) (i0 : U.I) :
    speciesWeighted U s (indexIndicator U i0) = s.val.amount i0 := by
  simp only [speciesWeighted, indexIndicator]
  rw [Finset.sum_eq_single i0]
  · simp
  · intro i _ hne
    simp [hne]
  · intro hmem
    exact absurd (Finset.mem_univ i0) hmem

/-- The constant observable returns the unrestricted total real amount. -/
theorem speciesWeighted_one (U : UniversalShape) (s : HeterogeneousSample U.I U.shape) :
    speciesWeighted U s (fun _ => 1) = ∑ i : U.I, s.val.amount i := by
  simp only [speciesWeighted, mul_one]

/-- Pushforward of the faithful observable along the existing encoding.  The encoded record
evaluates the transported observable at exactly the same actual constituent values. -/
theorem canonicalSpeciesWeighted_encode (U : UniversalShape)
    (s : HeterogeneousSample U.I U.shape) (φ : ConstituentCarrier U → ℝ) :
    canonicalSpeciesWeighted U (OrganicStereoHeterogeneousSamples.encode U.shape U.indexing s)
        (fun p => φ (carrierDecode U p)) = speciesWeighted U s φ := by
  simp only [canonicalSpeciesWeighted, speciesWeighted]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hstate :
      φ (carrierDecode U ⟨i,
        (OrganicStereoHeterogeneousSamples.encode U.shape U.indexing s).val.state i⟩) =
        φ ⟨i, s.val.state i⟩ := by
    rw [show carrierDecode U ⟨i,
          (OrganicStereoHeterogeneousSamples.encode U.shape U.indexing s).val.state i⟩ =
        ⟨i, s.val.state i⟩ from
      carrierDecode_carrierEncode U ⟨i, s.val.state i⟩]
  rw [hstate]
  simp

/-- Pushforward of the faithful observable along the existing decoding. -/
theorem speciesWeighted_decode (U : UniversalShape)
    (c : CanonicalSample U.I U.shape) (φ : CanonicalCarrier U → ℝ) :
    speciesWeighted U (OrganicStereoHeterogeneousSamples.decode U.shape U.indexing c)
        (fun p => φ (carrierEncode U p)) = canonicalSpeciesWeighted U c φ := by
  simp only [canonicalSpeciesWeighted, speciesWeighted]
  refine Finset.sum_congr rfl ?_
  intro i _
  have hstate :
      φ (carrierEncode U ⟨i,
        (OrganicStereoHeterogeneousSamples.decode U.shape U.indexing c).val.state i⟩) =
        φ ⟨i, c.val.state i⟩ := by
    rw [show carrierEncode U ⟨i,
          (OrganicStereoHeterogeneousSamples.decode U.shape U.indexing c).val.state i⟩ =
        ⟨i, c.val.state i⟩ from
      carrierEncode_carrierDecode U ⟨i, c.val.state i⟩]
  rw [hstate]
  simp

/-- Exact recovery of the amount, and hence of the state/amount pairing, for the canonical record:
decoding returns the original sample and the observable reads the same amount. -/
theorem canonicalSpeciesWeighted_encoded_indexIndicator (U : UniversalShape)
    (s : HeterogeneousSample U.I U.shape) (i0 : U.I) :
    canonicalSpeciesWeighted U (OrganicStereoHeterogeneousSamples.encode U.shape U.indexing s)
        (fun p => indexIndicator U i0 (carrierDecode U p)) = s.val.amount i0 := by
  rw [canonicalSpeciesWeighted_encode, speciesWeighted_indexIndicator]

/-! ## Concrete physical whole states

The examples below use the repository's concrete two-atom hydrogen description
`FiniteClassicalStereoDescriptionExample.description` and an empty-shell whole state (no roles,
paths, bands, drawing data, frames or electronic inventory) on a concrete atom type.  No `Unit`
surrogate is used for a state.
-/

/-- An empty interaction hypergraph on any finite atom type; the atom data are the concrete hydrogen
element. -/
def emptyHypergraph (V : Type) [DecidableEq V] [Fintype V] :
    FiniteAtomInteractionHypergraph V where
  atomData := fun _ => { element := FiniteClassicalStereoDescriptionExample.hydrogen }
  interactions := []
  arity_ge_two := by
    intro edge member
    simp at member
  participants_nodup := by
    intro edge member
    simp at member

/-- The zero conformation on any finite atom type. -/
def zeroConformation (V : Type) [Fintype V] : MolecularConformation V :=
  fun _ => (0 : EuclideanSpace ℝ (Fin 3))

/-- A genuine whole state with no roles, paths, bands, drawing data, frames or electronic
inventory.  Its graph and conformation are supplied; every optional channel is genuinely absent. -/
def emptyShellState {V : Type} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (conformation : MolecularConformation V) :
    WholeState V (Fin 0) (Fin 0) where
  graph := graph
  electronic? := none
  electronic_unpaired := by
    intro channel present
    simp at present
  conformation := conformation
  rationalPositions? := none
  rationalPositions_valid := by
    intro positions present
    simp at present
  roles := []
  role_valid := by
    intro annotation member
    simp at member
  paths := fun edge => Fin.elim0 edge
  path_valid := fun edge => Fin.elim0 edge
  path_source_endpoint := fun edge => Fin.elim0 edge
  path_target_endpoint := fun edge => Fin.elim0 edge
  bandFamily := fun band => Fin.elim0 band
  band_agreement := by
    intro band
    exact Fin.elim0 band
  diagram? := none
  diagramPartial? := none
  diagramIncidence := []
  diagram_valid := by
    intro row member
    simp at member

/-! ## Concrete shapes and enumerations -/

/-- Two constituents, each with two atom labels, one edge label and no band labels. -/
def twoAtomShape : Shape (Fin 2) where
  Atom := fun _ => Fin 2
  Edge := fun _ => Fin 1
  Band := fun _ => Fin 0
  atomDecidableEq := fun _ => inferInstance
  atomFintype := fun _ => inferInstance
  edgeFintype := fun _ => inferInstance
  bandFintype := fun _ => inferInstance

/-- Explicit enumerations for `twoAtomShape`. -/
def twoAtomIndexing : Indexing twoAtomShape where
  atomIndex := fun _ => Equiv.refl (Fin 2)
  edgeIndex := fun _ => Equiv.refl (Fin 1)
  bandIndex := fun _ => Equiv.refl (Fin 0)

/-- Three constituents, each with three atom labels, no edge labels and no band labels. -/
def threeAtomShape : Shape (Fin 3) where
  Atom := fun _ => Fin 3
  Edge := fun _ => Fin 0
  Band := fun _ => Fin 0
  atomDecidableEq := fun _ => inferInstance
  atomFintype := fun _ => inferInstance
  edgeFintype := fun _ => inferInstance
  bandFintype := fun _ => inferInstance

/-- Explicit enumerations for `threeAtomShape`. -/
def threeAtomIndexing : Indexing threeAtomShape where
  atomIndex := fun _ => Equiv.refl (Fin 3)
  edgeIndex := fun _ => Equiv.refl (Fin 0)
  bandIndex := fun _ => Equiv.refl (Fin 0)

/-- A single constituent with two atom labels, one edge label and no band labels. -/
def singleRichShape : Shape (Fin 1) where
  Atom := fun _ => Fin 2
  Edge := fun _ => Fin 1
  Band := fun _ => Fin 0
  atomDecidableEq := fun _ => inferInstance
  atomFintype := fun _ => inferInstance
  edgeFintype := fun _ => inferInstance
  bandFintype := fun _ => inferInstance

/-- Explicit enumerations for `singleRichShape`. -/
def singleRichIndexing : Indexing singleRichShape where
  atomIndex := fun _ => Equiv.refl (Fin 2)
  edgeIndex := fun _ => Equiv.refl (Fin 1)
  bandIndex := fun _ => Equiv.refl (Fin 0)

/-- A single constituent with three atom labels, no edge labels and no band labels. -/
def singlePoorShape : Shape (Fin 1) where
  Atom := fun _ => Fin 3
  Edge := fun _ => Fin 0
  Band := fun _ => Fin 0
  atomDecidableEq := fun _ => inferInstance
  atomFintype := fun _ => inferInstance
  edgeFintype := fun _ => inferInstance
  bandFintype := fun _ => inferInstance

/-- Explicit enumerations for `singlePoorShape`. -/
def singlePoorIndexing : Indexing singlePoorShape where
  atomIndex := fun _ => Equiv.refl (Fin 3)
  edgeIndex := fun _ => Equiv.refl (Fin 0)
  bandIndex := fun _ => Equiv.refl (Fin 0)

/-- Explicit enumerations for the source module's concrete example shape, used for the correlation
witness. -/
def marginalExampleIndexing : Indexing MarginalSeparation.exampleShape where
  atomIndex := fun _ => Equiv.refl (Fin 2)
  edgeIndex := fun _ => Equiv.refl (Fin 1)
  bandIndex := fun _ => Equiv.refl (Fin 0)

/-! ## Concrete samples with actual whole states and real amounts -/

/-- The empty-shell state of every constituent of `threeAtomShape`. -/
def threeComponentState (i : Fin 3) : ComponentState threeAtomShape i :=
  emptyShellState (emptyHypergraph (V := Fin 3)) (zeroConformation (Fin 3))

/-- Unit real amount on three constituents. -/
def threeAmount : Fin 3 → ℝ := fun _ => 1

theorem threeAmount_nonneg : ∀ i : Fin 3, 0 ≤ threeAmount i :=
  fun _ => by norm_num [threeAmount]

theorem threeAmount_total_pos : 0 < ∑ i : Fin 3, threeAmount i := by
  rw [Fin.sum_univ_three]
  norm_num [threeAmount]

/-- Sample data over `threeAtomShape`: three distinct constituents, each with an actual whole
state in the full possibility set and unit real amount. -/
def threeData : SampleData (Fin 3) threeAtomShape where
  state := threeComponentState
  possible := fun _ => Set.univ
  amount := threeAmount

theorem threeData_valid : threeData.Valid :=
  ⟨fun _ => Set.mem_univ _, threeAmount_nonneg, threeAmount_total_pos⟩

/-- The valid three-constituent heterogeneous sample. -/
def threeSample : HeterogeneousSample (Fin 3) threeAtomShape :=
  ⟨threeData, threeData_valid⟩

/-- The concrete two-atom hydrogen description carried by the single rich constituent. -/
def singleRichState (i : Fin 1) : ComponentState singleRichShape i :=
  FiniteClassicalStereoDescriptionExample.description

/-- The empty-shell state carried by the single poor constituent. -/
def singlePoorState (i : Fin 1) : ComponentState singlePoorShape i :=
  emptyShellState (emptyHypergraph (V := Fin 3)) (zeroConformation (Fin 3))

/-- Unit real amount on one constituent. -/
def oneAmount : Fin 1 → ℝ := fun _ => 1

theorem oneAmount_nonneg : ∀ i : Fin 1, 0 ≤ oneAmount i :=
  fun _ => by norm_num [oneAmount]

theorem oneAmount_total_pos : 0 < ∑ i : Fin 1, oneAmount i := by
  rw [Fin.sum_univ_one]
  norm_num [oneAmount]

/-- Sample data for the single rich constituent (two atoms, one edge, no bands). -/
def singleRichData : SampleData (Fin 1) singleRichShape where
  state := singleRichState
  possible := fun _ => Set.univ
  amount := oneAmount

theorem singleRichData_valid : singleRichData.Valid :=
  ⟨fun _ => Set.mem_univ _, oneAmount_nonneg, oneAmount_total_pos⟩

/-- The valid single rich heterogeneous sample. -/
def singleRichSampleData : HeterogeneousSample (Fin 1) singleRichShape :=
  ⟨singleRichData, singleRichData_valid⟩

/-- Sample data for the single poor constituent (three atoms, no edges, no bands). -/
def singlePoorData : SampleData (Fin 1) singlePoorShape where
  state := singlePoorState
  possible := fun _ => Set.univ
  amount := oneAmount

theorem singlePoorData_valid : singlePoorData.Valid :=
  ⟨fun _ => Set.mem_univ _, oneAmount_nonneg, oneAmount_total_pos⟩

/-- The valid single poor heterogeneous sample. -/
def singlePoorSampleData : HeterogeneousSample (Fin 1) singlePoorShape :=
  ⟨singlePoorData, singlePoorData_valid⟩

/-! ## Universal shape witnesses and samples -/

/-- The witness for the two-constituent sample, reusing the source module's concrete example shape
and its two-atom hydrogen whole description. -/
def mixedTwoShape : UniversalShape where
  I := Fin 2
  fintypeI := inferInstance
  shape := MarginalSeparation.exampleShape
  indexing := marginalExampleIndexing

/-- The witness for the three-constituent sample. -/
def mixedThreeShape : UniversalShape where
  I := Fin 3
  fintypeI := inferInstance
  shape := threeAtomShape
  indexing := threeAtomIndexing

/-- The witness for the single rich constituent. -/
def singleRichWitness : UniversalShape where
  I := Fin 1
  fintypeI := inferInstance
  shape := singleRichShape
  indexing := singleRichIndexing

/-- The witness for the single poor constituent. -/
def singlePoorWitness : UniversalShape where
  I := Fin 1
  fintypeI := inferInstance
  shape := singlePoorShape
  indexing := singlePoorIndexing

/-- The two-constituent universal sample with amounts `(2, 1)`, reused from the source module's
concrete correlation witness. -/
def mixedTwo : UniversalSample :=
  ⟨mixedTwoShape, MarginalSeparation.sampleA⟩

/-- The same two-constituent states with the amounts swapped to `(1, 2)`. -/
def swappedTwo : UniversalSample :=
  ⟨mixedTwoShape, MarginalSeparation.sampleB⟩

/-- The three-constituent universal sample with actual empty-shell whole states and unit amounts. -/
def mixedThree : UniversalSample :=
  ⟨mixedThreeShape, threeSample⟩

/-- The single rich-constituent universal sample. -/
def singleRichSample : UniversalSample :=
  ⟨singleRichWitness, singleRichSampleData⟩

/-- The single poor-constituent universal sample. -/
def singlePoorSample : UniversalSample :=
  ⟨singlePoorWitness, singlePoorSampleData⟩

/-! ## Count computations -/

@[simp] theorem constituentCount_mixedTwo : constituentCount mixedTwo.1 = 2 := by
  simp [constituentCount, mixedTwo, mixedTwoShape]

@[simp] theorem constituentCount_mixedThree : constituentCount mixedThree.1 = 3 := by
  simp [constituentCount, mixedThree, mixedThreeShape]

@[simp] theorem totalAtomCount_singleRich : totalAtomCount singleRichSample.1 = 2 := by
  simp [totalAtomCount, singleRichSample, singleRichWitness, singleRichShape, Shape.atomCard]

@[simp] theorem totalAtomCount_singlePoor : totalAtomCount singlePoorSample.1 = 3 := by
  simp [totalAtomCount, singlePoorSample, singlePoorWitness, singlePoorShape, Shape.atomCard]

@[simp] theorem totalEdgeCount_singleRich : totalEdgeCount singleRichSample.1 = 1 := by
  simp [totalEdgeCount, singleRichSample, singleRichWitness, singleRichShape, Shape.edgeCard]

@[simp] theorem totalEdgeCount_singlePoor : totalEdgeCount singlePoorSample.1 = 0 := by
  simp [totalEdgeCount, singlePoorSample, singlePoorWitness, singlePoorShape, Shape.edgeCard]

/-! ## Decisive inhabited tests

The first test places samples with different constituent counts in **one** uncertainty set.  The
second test is a separate pair with the same constituent count but different per-constituent atom
and edge counts. -/

/-- One uncertainty set containing a two-constituent and a three-constituent whole sample. -/
def mixedUncertainty : Set UniversalSample :=
  {mixedTwo, mixedThree}

theorem mixedTwo_mem : mixedTwo ∈ mixedUncertainty := by
  simp [mixedUncertainty]

theorem mixedThree_mem : mixedThree ∈ mixedUncertainty := by
  simp [mixedUncertainty]

theorem mixedUncertainty_nonempty : mixedUncertainty.Nonempty :=
  ⟨mixedTwo, mixedTwo_mem⟩

/-- The two samples in `mixedUncertainty` really have different constituent counts. -/
theorem mixedTwo_ne_mixedThree : mixedTwo ≠ mixedThree := by
  intro equal
  have hcount : constituentCount mixedTwo.1 = constituentCount mixedThree.1 :=
    congrArg (fun x : UniversalSample => constituentCount x.1) equal
  have : (2 : ℕ) = 3 := by
    calc (2 : ℕ) = constituentCount mixedTwo.1 := constituentCount_mixedTwo.symm
      _ = constituentCount mixedThree.1 := hcount
      _ = 3 := constituentCount_mixedThree
  omega

/-- `mixedUncertainty` contains samples of different constituent counts. -/
theorem mixedUncertainty_differs_in_constituentCount :
    (∃ x ∈ mixedUncertainty, constituentCount x.1 = 2) ∧
      (∃ y ∈ mixedUncertainty, constituentCount y.1 = 3) :=
  ⟨⟨mixedTwo, mixedTwo_mem, constituentCount_mixedTwo⟩,
    ⟨mixedThree, mixedThree_mem, constituentCount_mixedThree⟩⟩

/-- The mixed uncertainty set is recovered exactly by the whole-set round trip. -/
theorem mixedUncertainty_recovery :
    decodeSet (encodeSet mixedUncertainty) = mixedUncertainty :=
  decodeSet_encodeSet mixedUncertainty

/-- The encoded images of the two differently-sized samples remain distinct. -/
theorem encode_mixedTwo_ne_mixedThree :
    encodeUniversal mixedTwo ≠ encodeUniversal mixedThree :=
  fun equal => mixedTwo_ne_mixedThree (encodeUniversal_injective equal)

/-- A separate set containing two samples with the same constituent count but different
per-constituent atom and edge counts. -/
def atomEdgeUncertainty : Set UniversalSample :=
  {singleRichSample, singlePoorSample}

theorem singleRich_mem : singleRichSample ∈ atomEdgeUncertainty := by
  simp [atomEdgeUncertainty]

theorem singlePoor_mem : singlePoorSample ∈ atomEdgeUncertainty := by
  simp [atomEdgeUncertainty]

/-- The separate pair differs in atom count and in edge count, while both have one constituent. -/
theorem atomEdgeUncertainty_counts :
    constituentCount singleRichSample.1 = 1 ∧
      constituentCount singlePoorSample.1 = 1 ∧
      totalAtomCount singleRichSample.1 = 2 ∧
      totalAtomCount singlePoorSample.1 = 3 ∧
      totalEdgeCount singleRichSample.1 = 1 ∧
      totalEdgeCount singlePoorSample.1 = 0 := by
  refine ⟨?_, ?_, totalAtomCount_singleRich, totalAtomCount_singlePoor,
    totalEdgeCount_singleRich, totalEdgeCount_singlePoor⟩
  · simp [constituentCount, singleRichSample, singleRichWitness]
  · simp [constituentCount, singlePoorSample, singlePoorWitness]

/-- The atom/edge pair consists of two genuinely different whole records. -/
theorem singleRich_ne_singlePoor : singleRichSample ≠ singlePoorSample := by
  intro equal
  have hatoms : totalAtomCount singleRichSample.1 = totalAtomCount singlePoorSample.1 :=
    congrArg (fun x : UniversalSample => totalAtomCount x.1) equal
  have : (2 : ℕ) = 3 := by
    calc (2 : ℕ) = totalAtomCount singleRichSample.1 := totalAtomCount_singleRich.symm
      _ = totalAtomCount singlePoorSample.1 := hatoms
      _ = 3 := totalAtomCount_singlePoor
  omega

/-- The atom/edge uncertainty set is recovered exactly by the whole-set round trip. -/
theorem atomEdgeUncertainty_recovery :
    decodeSet (encodeSet atomEdgeUncertainty) = atomEdgeUncertainty :=
  decodeSet_encodeSet atomEdgeUncertainty

/-- The encoded atom/edge pair also remains distinct. -/
theorem encode_singleRich_ne_singlePoor :
    encodeUniversal singleRichSample ≠ encodeUniversal singlePoorSample :=
  fun equal => singleRich_ne_singlePoor (encodeUniversal_injective equal)

/-! ## Strictness against a specified count-preserving fixed-index embedding

The following candidate embedding keeps the constituent index type fixed.  It is
count-preserving, and we show only that this particular candidate is not surjective.  This makes
no claim that a different encoding (for example one using padding) is impossible: the strictness
statement is deliberately restricted to the specified map. -/

/-- A count-preserving fixed-index embedding candidate: it fixes the constituent index type and the
shape and therefore cannot represent samples with a different constituent count. -/
def fixedIndexEmbed (I : Type) [Fintype I] (shape : Shape I) (idx : Indexing shape) :
    HeterogeneousSample I shape → UniversalSample :=
  fun s => ⟨⟨I, inferInstance, shape, idx⟩, s⟩

/-- The candidate embedding preserves the constituent count. -/
theorem fixedIndexEmbed_constituentCount (I : Type) [Fintype I] (shape : Shape I)
    (idx : Indexing shape) (s : HeterogeneousSample I shape) :
    constituentCount (fixedIndexEmbed I shape idx s).1 = Fintype.card I := rfl

/-- The specified count-preserving fixed-index embedding is not surjective: it cannot reach a
three-constituent sample when its index type has two elements.  No claim is made about
count-changing encodings such as padding. -/
theorem fixedIndexEmbed_not_surjective :
    ¬ Function.Surjective (fixedIndexEmbed (Fin 2) twoAtomShape twoAtomIndexing) := by
  intro surjective
  obtain ⟨s, hs⟩ := surjective mixedThree
  have hcount : constituentCount (fixedIndexEmbed (Fin 2) twoAtomShape twoAtomIndexing s).1 =
      constituentCount mixedThree.1 :=
    congrArg (fun x : UniversalSample => constituentCount x.1) hs
  have hleft :
      constituentCount (fixedIndexEmbed (Fin 2) twoAtomShape twoAtomIndexing s).1 = 2 := by
    rw [fixedIndexEmbed_constituentCount]
    simp
  have : (2 : ℕ) = 3 := by
    calc (2 : ℕ) = constituentCount
          (fixedIndexEmbed (Fin 2) twoAtomShape twoAtomIndexing s).1 := hleft.symm
      _ = constituentCount mixedThree.1 := hcount
      _ = 3 := constituentCount_mixedThree
  omega

/-! ## State/amount correlation witness preserved jointly

The two samples `mixedTwo` and `swappedTwo` carry the same two actual whole states and the same
marginal amount set `{1, 2}`, but they pair the amounts with the occurrences differently.  The
faithful species-weighted observable detects the joint pairing (`2` at occurrence `0` versus `1`),
the encoding preserves that value, and the whole uncertainty set is recovered exactly. -/

/-- The set containing both correlated records. -/
def correlatedUncertainty : Set UniversalSample :=
  {mixedTwo, swappedTwo}

theorem mixedTwo_mem_correlated : mixedTwo ∈ correlatedUncertainty := by
  simp [correlatedUncertainty]

theorem swappedTwo_mem_correlated : swappedTwo ∈ correlatedUncertainty := by
  simp [correlatedUncertainty]

/-- The two records have the same component-state marginal. -/
theorem correlated_state_marginal_eq :
    MarginalSeparation.stateMarginal MarginalSeparation.sampleA =
      MarginalSeparation.stateMarginal MarginalSeparation.sampleB :=
  MarginalSeparation.stateMarginal_A_eq_B

/-- The two records have the same component-amount marginal. -/
theorem correlated_amount_marginal_eq :
    MarginalSeparation.amountMarginal MarginalSeparation.sampleA =
      MarginalSeparation.amountMarginal MarginalSeparation.sampleB :=
  MarginalSeparation.amountMarginal_A_eq_B

/-- The joint state/amount pairing is nevertheless different: occurrence `0` carries amount `2` in
the first record and `1` in the second. -/
theorem correlated_joint_pairing :
    speciesWeighted mixedTwoShape MarginalSeparation.sampleA
        (indexIndicator mixedTwoShape (0 : Fin 2)) = 2 ∧
      speciesWeighted mixedTwoShape MarginalSeparation.sampleB
        (indexIndicator mixedTwoShape (0 : Fin 2)) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [speciesWeighted_indexIndicator]
    simp [MarginalSeparation.sampleA, MarginalSeparation.dataA, MarginalSeparation.amountA,
      MolarComposition.Composition.binaryAmount]
  · rw [speciesWeighted_indexIndicator]
    simp [MarginalSeparation.sampleB, MarginalSeparation.dataB, MarginalSeparation.amountB,
      MolarComposition.Composition.binaryAmount]

/-- The joint observable distinguishes the two records even though both marginals agree. -/
theorem correlated_joint_pairing_distinguished :
    speciesWeighted mixedTwoShape MarginalSeparation.sampleA
        (indexIndicator mixedTwoShape (0 : Fin 2)) ≠
      speciesWeighted mixedTwoShape MarginalSeparation.sampleB
        (indexIndicator mixedTwoShape (0 : Fin 2)) := by
  rw [correlated_joint_pairing.1, correlated_joint_pairing.2]
  norm_num

/-- The two universal records are genuinely distinct. -/
theorem mixedTwo_ne_swappedTwo : mixedTwo ≠ swappedTwo := by
  intro equal
  have hpairs := Sigma.mk.inj_iff.mp equal
  exact MarginalSeparation.sampleA_ne_sampleB (eq_of_heq hpairs.2)

/-- The joint pairing is preserved by encoding: the canonical image of the first record reads `2`
at the encoded occurrence `0`. -/
theorem encoded_correlated_joint_pairing_zero :
    canonicalSpeciesWeighted mixedTwoShape
        (OrganicStereoHeterogeneousSamples.encode mixedTwoShape.shape mixedTwoShape.indexing
          MarginalSeparation.sampleA)
        (fun p => indexIndicator mixedTwoShape (0 : Fin 2) (carrierDecode mixedTwoShape p)) = 2 := by
  rw [canonicalSpeciesWeighted_encoded_indexIndicator]
  simp [MarginalSeparation.sampleA, MarginalSeparation.dataA, MarginalSeparation.amountA,
    MolarComposition.Composition.binaryAmount]

/-- The joint pairing is preserved by encoding: the canonical image of the second record reads `1`
at the same occurrence. -/
theorem encoded_correlated_joint_pairing_zero_swapped :
    canonicalSpeciesWeighted mixedTwoShape
        (OrganicStereoHeterogeneousSamples.encode mixedTwoShape.shape mixedTwoShape.indexing
          MarginalSeparation.sampleB)
        (fun p => indexIndicator mixedTwoShape (0 : Fin 2) (carrierDecode mixedTwoShape p)) = 1 := by
  rw [canonicalSpeciesWeighted_encoded_indexIndicator]
  simp [MarginalSeparation.sampleB, MarginalSeparation.dataB, MarginalSeparation.amountB,
    MolarComposition.Composition.binaryAmount]

/-- The encoded correlated records remain distinct. -/
theorem encoded_mixedTwo_ne_swappedTwo :
    encodeUniversal mixedTwo ≠ encodeUniversal swappedTwo :=
  fun equal => mixedTwo_ne_swappedTwo (encodeUniversal_injective equal)

/-- The correlated uncertainty set is recovered exactly; the joint pairing is not replaced by a
product of marginals. -/
theorem correlatedUncertainty_recovery :
    decodeSet (encodeSet correlatedUncertainty) = correlatedUncertainty :=
  decodeSet_encodeSet correlatedUncertainty

/-- Repeated occurrences with identical states are retained as distinct carrier points. -/
theorem repeated_states_distinct_occurrences :
    (⟨(0 : Fin 2), MarginalSeparation.sampleA.val.state (0 : Fin 2)⟩ :
        ConstituentCarrier mixedTwoShape) ≠
      ⟨(1 : Fin 2), MarginalSeparation.sampleA.val.state (1 : Fin 2)⟩ := by
  intro equal
  have hfst : (0 : Fin 2) = 1 := congrArg Sigma.fst equal
  exact absurd hfst (by decide)

/-- Both repeated occurrences are weighted separately: occurrence `0` carries amount `2` and
occurrence `1` carries amount `1`, so neither is deduplicated. -/
theorem repeated_states_occurrence_amounts :
    speciesWeighted mixedTwoShape MarginalSeparation.sampleA
        (indexIndicator mixedTwoShape (0 : Fin 2)) = 2 ∧
      speciesWeighted mixedTwoShape MarginalSeparation.sampleA
        (indexIndicator mixedTwoShape (1 : Fin 2)) = 1 := by
  refine ⟨correlated_joint_pairing.1, ?_⟩
  rw [speciesWeighted_indexIndicator, ← Fin.succ_zero_eq_one]
  simp only [MarginalSeparation.sampleA, MarginalSeparation.dataA, MarginalSeparation.amountA,
    MolarComposition.Composition.binaryAmount, Fin.cases_succ]

/-- The constant observable counts both occurrences: the total amount is `3`, the sum of the two
retained occurrence amounts. -/
theorem repeated_states_total :
    speciesWeighted mixedTwoShape MarginalSeparation.sampleA (fun _ => 1) = 3 := by
  rw [speciesWeighted_one]
  change (∑ i : Fin 2, MolarComposition.Composition.binaryAmount 2 1 i) = 3
  rw [Fin.sum_univ_two, ← Fin.succ_zero_eq_one]
  simp only [MolarComposition.Composition.binaryAmount, Fin.cases_zero, Fin.cases_succ]
  norm_num

end

end OrganicStereoUniversalMixtureSamples
end OneCenter
end TetraStereo
