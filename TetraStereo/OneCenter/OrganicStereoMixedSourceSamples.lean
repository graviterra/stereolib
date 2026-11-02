/-
Copyright (c) 2026 TetraStereo contributors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TetraStereo.OneCenter.OrganicStereoMixedSourceAssembly
import TetraStereo.OneCenter.OrganicStereoMolarComposition

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-!
# Mixed-source molecular samples with real amounts

This module lifts the actual mixed-source molecular assembly of
`OrganicStereoMixedSourceAssembly` into heterogeneous, amount-bearing samples.

## Constituents

A sample is indexed by an arbitrary finite type `I`.  A `Context I` fixes the external,
constituent-independent typed metadata (`LigandId`, `LigandKind`, `FragmentId`, `FragmentKind`,
`State`, `Framework`, `BaseName`, `Numbering`, `Locant`, `Prefix`) and, for every index `i : I`,
its own finite atom type `Atom i` with its own `DecidableEq` and `Fintype` instances.  The atom
type, and hence its cardinality, may vary arbitrarily with `i`.  No global atom type is assumed.
The four label types carry `DecidableEq` instances because the actual upstream mixed assembly
requires them; no other metadata type is constrained.

For each `i`, `ComponentRequest ctx i` is the actual upstream
`OrganicStereoMixedSourceAssembly.MixedSourceRequest` at `ctx.Atom i` and the fixed external
types.  A component therefore carries a genuine mixed request: an independently supplied
`OrganicMolecularEvidence` core, one explicit enumeration of the component's atoms, and one
ordered heterogeneous list of native source entries (observations, donors, citations, P-93
physical frames and shared physical cases), with every payload field retained literally.

## Encoding and decoding

`SampleData` stores, for each constituent, one actual mixed request, one possible-request set
(a set of *whole* mixed requests, not a marginal), and one unrestricted real mole amount.
`AssembledData` stores the same amount channel and possible-set channel after applying the
*actual* upstream `assembleMixed`; decoding applies the *actual* upstream `decodeMixed`.
No generic "encoder-inverse" class is introduced and no encoder is assumed: the round trips are
instances of the concrete upstream theorem `decodeMixed_assembleMixed` and its arbitrary-set
form `decodeMixed_image_assembleMixed_image`.

The main results are:

* `decodeData_encodeData`: decoding the assembled data recovers the whole `SampleData`, including
  every constituent request, every possible-request set and every amount;
* `decode_encode`: the same statement for valid heterogeneous samples;
* `decodeDataSet_encodeDataSet`: arbitrary sets of entire sample requests are recovered exactly;
* `UncertainSample.decodeSet_encodeSet`: arbitrary correlated sets of *whole* samples are
  recovered exactly, so no state/amount or cross-constituent correlation is marginalized;
* exact amount, total and normalized-fraction preservation, using the existing
  `MolarComposition.Composition` carrier rather than a second numeric composition library;
* `encodeData_representation` and `encodeData_representation_eq_of_request_eq`: each index keeps
  its own separate assembly, so duplicate occurrences are never identified or merged across
  constituents; `encodeData_request_duplicate_retained` records the single-index case.

## Scope and non-claims

Amounts are unrestricted real mole amounts; as in `MolarComposition`, a sample records
nonnegative amounts with positive total, and nothing here asserts a probability, energy,
kinetic, thermodynamic or chemical-realizability claim.  The possible sets are sets of complete
requests/samples; they are not reduced to products of component marginals.

The upstream assembly has the exact inverse `decodeMixed (assembleMixed r) = r` on requests.  It
does not provide a right inverse on arbitrary representations, so this module claims the
request-level and image-level round trips (`decode ∘ encode = id`, injectivity of encoding), not
`encode ∘ decode = id` on arbitrary `MixedSourceRepresentation` data.  Likewise, no whole-core
`Fin` relabelling codec is assumed; the atom types of the constituents are kept as supplied.
-/

namespace TetraStereo.OneCenter
namespace OrganicStereoMixedSourceSamples

open OrganicStereoMixedSourceAssembly
open MolarComposition

noncomputable section

open scoped BigOperators

/-! ## Constituent contexts -/

variable {I : Type*}

/-- The external typed metadata and the per-constituent finite atom shape of a mixed-source
sample.

The external label/state/framework/name types are fixed for the whole sample (they describe the
metadata vocabulary, not atom identities).  The atom type `Atom i`, by contrast, is chosen
independently at every constituent `i`; its cardinality may differ between constituents.
Decidable equality is recorded for the four label types because the actual upstream assembly
requires it, and for every constituent's atom type. -/
structure Context (I : Type*) where
  /-- Ligand identifier metadata type. -/
  LigandId : Type
  /-- Ligand kind metadata type. -/
  LigandKind : Type
  /-- Fragment identifier metadata type. -/
  FragmentId : Type
  /-- Fragment kind metadata type. -/
  FragmentKind : Type
  /-- Decidable equality of ligand identifiers. -/
  ligandIdDecidableEq : DecidableEq LigandId
  /-- Decidable equality of ligand kinds. -/
  ligandKindDecidableEq : DecidableEq LigandKind
  /-- Decidable equality of fragment identifiers. -/
  fragmentIdDecidableEq : DecidableEq FragmentId
  /-- Decidable equality of fragment kinds. -/
  fragmentKindDecidableEq : DecidableEq FragmentKind
  /-- Observation state metadata type. -/
  State : Type
  /-- Observation framework metadata type. -/
  Framework : Type
  /-- Base-name metadata type. -/
  BaseName : Type
  /-- Numbering metadata type. -/
  Numbering : Type
  /-- Locant metadata type. -/
  Locant : Type
  /-- Prefix metadata type. -/
  Prefix : Type
  /-- Atom type of each constituent. -/
  Atom : I → Type
  /-- Decidable equality of each constituent's atoms. -/
  atomDecidableEq : ∀ i, DecidableEq (Atom i)
  /-- Finiteness of each constituent's atom type. -/
  atomFintype : ∀ i, Fintype (Atom i)

section Instances

variable {ctx : Context I}

/-- The ligand identifier equality of the context, as a typeclass instance. -/
instance instLigandIdDecidableEq : DecidableEq ctx.LigandId :=
  ctx.ligandIdDecidableEq

/-- The ligand kind equality of the context, as a typeclass instance. -/
instance instLigandKindDecidableEq : DecidableEq ctx.LigandKind :=
  ctx.ligandKindDecidableEq

/-- The fragment identifier equality of the context, as a typeclass instance. -/
instance instFragmentIdDecidableEq : DecidableEq ctx.FragmentId :=
  ctx.fragmentIdDecidableEq

/-- The fragment kind equality of the context, as a typeclass instance. -/
instance instFragmentKindDecidableEq : DecidableEq ctx.FragmentKind :=
  ctx.fragmentKindDecidableEq

/-- The atom equality of each constituent, as a typeclass instance. -/
instance instAtomDecidableEq {i : I} : DecidableEq (ctx.Atom i) :=
  ctx.atomDecidableEq i

/-- The atom finiteness of each constituent, as a typeclass instance. -/
instance instAtomFintype {i : I} : Fintype (ctx.Atom i) :=
  ctx.atomFintype i

end Instances

/-- The actual upstream mixed-source request of one constituent.  Every constituent uses its
own atom type and its own enumeration, while the external metadata types are shared.

The universe of this abbrev is inferred: the upstream mixed structures contain type-valued
representation fields, so they do not live at `Type 0`. -/
abbrev ComponentRequest (ctx : Context I) (i : I) :=
  @MixedSourceRequest (ctx.Atom i) (ctx.atomDecidableEq i) (ctx.atomFintype i)
    ctx.LigandId ctx.LigandKind ctx.FragmentId ctx.FragmentKind
    ctx.State ctx.Framework ctx.BaseName ctx.Numbering ctx.Locant ctx.Prefix

/-- The actual upstream assembled mixed-source representation of one constituent. -/
abbrev ComponentRepresentation (ctx : Context I) (i : I) :=
  @MixedSourceRepresentation (ctx.Atom i) (ctx.atomDecidableEq i) (ctx.atomFintype i)
    ctx.LigandId ctx.LigandKind ctx.FragmentId ctx.FragmentKind
    ctx.State ctx.Framework ctx.BaseName ctx.Numbering ctx.Locant ctx.Prefix

/-! ## Sample data, assembled data and validity -/

/-- The unvalidated data of a heterogeneous mixed-source sample.

Each constituent retains its own actual mixed request, its own possible-request set (a set of
*whole* requests), and its own unrestricted real mole amount.  The sample is indexed by `I`;
equal requests at distinct indices remain distinct constituent occurrences. -/
structure SampleData (ctx : Context I) where
  /-- The actual mixed-source request of each constituent. -/
  request : ∀ i, ComponentRequest ctx i
  /-- The admissible possible-request set of each constituent.  It is a set of whole mixed
  requests, not a product of species or field marginals. -/
  possible : ∀ i, Set (ComponentRequest ctx i)
  /-- The unrestricted real mole amount of each constituent. -/
  amount : I → ℝ

/-- The assembled data of a heterogeneous mixed-source sample.  The request channel has been
passed through the actual upstream `assembleMixed`; the possible-set channel is the exact image
of the supplied possible-request sets; amounts are carried unchanged. -/
structure AssembledData (ctx : Context I) where
  /-- The actual assembly of each constituent's mixed request. -/
  representation : ∀ i, ComponentRepresentation ctx i
  /-- The exact image of each constituent's possible-request set under `assembleMixed`. -/
  possible : ∀ i, Set (ComponentRepresentation ctx i)
  /-- The amount, carried unchanged. -/
  amount : I → ℝ

namespace SampleData

variable [Fintype I] {ctx : Context I}

/-- Extensionality for sample data. -/
@[ext] theorem ext {s s' : SampleData ctx}
    (request : s.request = s'.request)
    (possible : s.possible = s'.possible)
    (amount : s.amount = s'.amount) : s = s' := by
  cases s with
  | mk request' possible' amount' =>
  cases s' with
  | mk request'' possible'' amount'' =>
  simp only [SampleData.mk.injEq]
  exact ⟨request, possible, amount⟩

/-- The validity obligations: the actual request of every constituent belongs to that
constituent's possible-request set, all amounts are nonnegative, and the total amount is strictly
positive.  This is the mixed-source analogue of `OrganicStereoHeterogeneousSamples.SampleData.Valid`
at the actual mixed request type. -/
def Valid (s : SampleData ctx) : Prop :=
  (∀ i, s.request i ∈ s.possible i) ∧
    (∀ i, 0 ≤ s.amount i) ∧
    0 < ∑ i, s.amount i

end SampleData

/-- A valid heterogeneous mixed-source sample. -/
abbrev HeterogeneousSample (ctx : Context I) [Fintype I] :=
  {s : SampleData ctx // s.Valid}

namespace AssembledData

variable [Fintype I] {ctx : Context I}

/-- Extensionality for assembled data. -/
@[ext] theorem ext {a a' : AssembledData ctx}
    (representation : a.representation = a'.representation)
    (possible : a.possible = a'.possible)
    (amount : a.amount = a'.amount) : a = a' := by
  cases a with
  | mk representation' possible' amount' =>
  cases a' with
  | mk representation'' possible'' amount'' =>
  simp only [AssembledData.mk.injEq]
  exact ⟨representation, possible, amount⟩

/-- The validity obligations for assembled data. -/
def Valid (a : AssembledData ctx) : Prop :=
  (∀ i, a.representation i ∈ a.possible i) ∧
    (∀ i, 0 ≤ a.amount i) ∧
    0 < ∑ i, a.amount i

end AssembledData

/-- A valid assembled heterogeneous sample. -/
abbrev AssembledSample (ctx : Context I) [Fintype I] :=
  {a : AssembledData ctx // a.Valid}

/-! ## Optional and admissible possible-request sets

The possible-request channel is optional in the following concrete sense: if no restriction is
supplied, the full set of all whole requests is used.  Every supplied set is admissible exactly
when the actual request lies in it, which is the membership clause of `Valid`. -/

/-- The unrestricted possible-request set: every whole mixed request is admitted at every
constituent.  This is the concrete "no restriction supplied" value. -/
def fullPossible (ctx : Context I) : ∀ i, Set (ComponentRequest ctx i) :=
  fun _ => Set.univ

/-- The full possible-request set is always admissible. -/
theorem fullPossible_admissible (ctx : Context I) (request : ∀ i, ComponentRequest ctx i) :
    ∀ i, request i ∈ fullPossible ctx i :=
  fun _ => Set.mem_univ _

/-- Sample data with no supplied possible-request restriction. -/
def ofRequests (ctx : Context I) (request : ∀ i, ComponentRequest ctx i) (amount : I → ℝ) :
    SampleData ctx where
  request := request
  possible := fullPossible ctx
  amount := amount

/-- Data with the full possible-request set is valid exactly when its amount channel is valid. -/
theorem ofRequests_valid_iff (ctx : Context I) [Fintype I]
    (request : ∀ i, ComponentRequest ctx i) (amount : I → ℝ) :
    (ofRequests ctx request amount).Valid ↔
      (∀ i, 0 ≤ amount i) ∧ 0 < ∑ i, amount i := by
  constructor
  · intro valid
    exact ⟨valid.2.1, valid.2.2⟩
  · intro valid
    exact ⟨fun i => Set.mem_univ (request i), valid.1, valid.2⟩

/-! ## Encoding and decoding with the actual mixed assembly -/

variable [Fintype I]
variable {ctx : Context I}

/-- Encode every constituent through the actual upstream `assembleMixed`.
The possible-request set of a constituent is sent to its exact image under `assembleMixed`;
amounts are copied unchanged. -/
def encodeData (s : SampleData ctx) : AssembledData ctx where
  representation i := assembleMixed (s.request i)
  possible i := assembleMixed '' s.possible i
  amount := s.amount

/-- Decode every constituent through the actual upstream `decodeMixed`.
The possible-set channel is sent to its exact image under `decodeMixed`; amounts are copied
unchanged. -/
def decodeData (a : AssembledData ctx) : SampleData ctx where
  request i := decodeMixed (a.representation i)
  possible i := decodeMixed '' a.possible i
  amount := a.amount

@[simp] theorem encodeData_representation (s : SampleData ctx) (i : I) :
    (encodeData s).representation i = assembleMixed (s.request i) := rfl

@[simp] theorem encodeData_possible (s : SampleData ctx) (i : I) :
    (encodeData s).possible i = assembleMixed '' s.possible i := rfl

@[simp] theorem encodeData_amount (s : SampleData ctx) :
    (encodeData s).amount = s.amount := rfl

@[simp] theorem decodeData_request (a : AssembledData ctx) (i : I) :
    (decodeData a).request i = decodeMixed (a.representation i) := rfl

@[simp] theorem decodeData_possible (a : AssembledData ctx) (i : I) :
    (decodeData a).possible i = decodeMixed '' a.possible i := rfl

@[simp] theorem decodeData_amount (a : AssembledData ctx) :
    (decodeData a).amount = a.amount := rfl

/-- The per-constituent possible-request set is recovered exactly from its assembled image.
This is the actual upstream arbitrary-set inverse; it is stated per constituent because the atom
types may differ between constituents. -/
theorem decode_encodedPossibleSet (i : I) (requests : Set (ComponentRequest ctx i)) :
    decodeMixed '' (assembleMixed '' requests) = requests :=
  decodeMixed_image_assembleMixed_image requests

/-- Encoding of actual mixed requests is injective at each constituent.  This is derived from the
actual upstream inverse, not assumed. -/
theorem assembleMixed_injective (i : I) :
    Function.Injective (fun request : ComponentRequest ctx i => assembleMixed request) := by
  intro first second equal
  have decoded := congrArg decodeMixed equal
  rwa [decodeMixed_assembleMixed, decodeMixed_assembleMixed] at decoded

/-- The assembly recorded at a constituent depends only on that constituent's own actual mixed
request.  This is the componentwise locality that prevents occurrences from being identified
with one another. -/
theorem encodeData_representation_eq_of_request_eq {s t : SampleData ctx} {i : I}
    (same : s.request i = t.request i) :
    (encodeData s).representation i = (encodeData t).representation i :=
  congrArg assembleMixed same

/-- Equal indices carry the same occurrence through encoding.  Because a sample is a dependent
function with one separate assembly entry at every index, duplicate requests at different
constituents are both retained; a homogeneous equality across two distinct indices is not
well-typed when their atom types differ, so this is stated heterogeneously under an explicit
index equality. -/
theorem encodeData_request_duplicate_retained (s : SampleData ctx) {i j : I}
    (index : i = j) :
    HEq ((encodeData s).representation i) ((encodeData s).representation j) := by
  subst index
  exact HEq.refl _

/-- Distinct mixed requests at one constituent index remain distinct after encoding. -/
@[simp] theorem encodeData_representation_inj_iff (s t : SampleData ctx) (i : I) :
    (encodeData s).representation i = (encodeData t).representation i ↔
      s.request i = t.request i := by
  constructor
  · intro equal
    change assembleMixed (s.request i) = assembleMixed (t.request i) at equal
    exact assembleMixed_injective i equal
  · intro equal
    change assembleMixed (s.request i) = assembleMixed (t.request i)
    rw [equal]

/-! ## Exact whole-data inverse -/

/-- Decoding assembled data returns the supplied sample data literally: every constituent's
actual mixed request, every possible-request set, and every amount. -/
theorem decodeData_encodeData (s : SampleData ctx) :
    decodeData (encodeData s) = s := by
  refine SampleData.ext ?_ ?_ ?_
  · funext i
    exact decodeMixed_assembleMixed (s.request i)
  · funext i
    exact decode_encodedPossibleSet i (s.possible i)
  · rfl

/-- Re-encoding the decoded encoding is the same assembled data.  This records the two-sided
inverse on the image of the encoding; no surjectivity onto arbitrary assembled representations
is claimed. -/
@[simp] theorem encodeData_decodeData_encodeData (s : SampleData ctx) :
    encodeData (decodeData (encodeData s)) = encodeData s := by
  rw [decodeData_encodeData]

/-! ## Validity preservation -/

/-- Encoding preserves validity. -/
theorem encodeData_valid (s : SampleData ctx) (valid : s.Valid) :
    (encodeData s).Valid := by
  refine ⟨?_, valid.2.1, valid.2.2⟩
  intro i
  change assembleMixed (s.request i) ∈ assembleMixed '' s.possible i
  exact ⟨s.request i, valid.1 i, rfl⟩

/-- Decoding preserves validity. -/
theorem decodeData_valid (a : AssembledData ctx) (valid : a.Valid) :
    (decodeData a).Valid := by
  refine ⟨?_, valid.2.1, valid.2.2⟩
  intro i
  change decodeMixed (a.representation i) ∈ decodeMixed '' a.possible i
  exact ⟨a.representation i, valid.1 i, rfl⟩

/-- Encode a valid heterogeneous mixed-source sample. -/
def encode (s : HeterogeneousSample ctx) : AssembledSample ctx :=
  ⟨encodeData s.val, encodeData_valid s.val s.property⟩

/-- Decode a valid assembled sample to the original label/atom types. -/
def decode (a : AssembledSample ctx) : HeterogeneousSample ctx :=
  ⟨decodeData a.val, decodeData_valid a.val a.property⟩

@[simp] theorem encode_val (s : HeterogeneousSample ctx) :
    (encode s).val = encodeData s.val := rfl

@[simp] theorem decode_val (a : AssembledSample ctx) :
    (decode a).val = decodeData a.val := rfl

/-- The exact whole-sample inverse on valid samples. -/
theorem decode_encode (s : HeterogeneousSample ctx) :
    decode (encode s) = s := by
  apply Subtype.ext
  simpa only [decode_val, encode_val] using decodeData_encodeData s.val

/-- The two-sided inverse on the image of the valid-sample encoding. -/
theorem encode_decode_encode (s : HeterogeneousSample ctx) :
    encode (decode (encode s)) = encode s := by
  rw [decode_encode]

/-- For a fixed context, encoding valid samples is injective. -/
theorem encode_injective : Function.Injective (encode (ctx := ctx)) := by
  intro first second equal
  have decoded := congrArg decode equal
  rwa [decode_encode, decode_encode] at decoded

/-- Decoding is a left inverse of encoding. -/
theorem decode_leftInverse : Function.LeftInverse (decode (ctx := ctx)) (encode (ctx := ctx)) :=
  decode_encode

/-- Every constituent's request, possible set, amount and membership are recovered exactly. -/
theorem decode_encode_component (s : HeterogeneousSample ctx) (i : I) :
    (decode (encode s)).val.request i = s.val.request i ∧
    (decode (encode s)).val.possible i = s.val.possible i ∧
    (decode (encode s)).val.amount i = s.val.amount i ∧
    ((decode (encode s)).val.request i ∈ (decode (encode s)).val.possible i ↔
      s.val.request i ∈ s.val.possible i) := by
  rw [decode_encode]
  exact ⟨rfl, rfl, rfl, Iff.rfl⟩

/-! ## Arbitrary sets of whole sample data -/

/-- The image of a set of whole sample data under encoding. -/
def encodeDataSet (U : Set (SampleData ctx)) : Set (AssembledData ctx) :=
  encodeData '' U

/-- The image of a set of whole assembled data under decoding. -/
def decodeDataSet (V : Set (AssembledData ctx)) : Set (SampleData ctx) :=
  decodeData '' V

@[simp] theorem mem_encodeDataSet_iff (U : Set (SampleData ctx)) (a : AssembledData ctx) :
    a ∈ encodeDataSet U ↔ ∃ s ∈ U, encodeData s = a := Iff.rfl

@[simp] theorem mem_decodeDataSet_iff (V : Set (AssembledData ctx)) (s : SampleData ctx) :
    s ∈ decodeDataSet V ↔ ∃ a ∈ V, decodeData a = s := Iff.rfl

/-- **Arbitrary-set data recovery.**  For every set of whole sample requests, the assembled data
whose decoding lands in that set are exactly the encoding of the original set.  No correlation
between constituents, requests, possible sets or amounts is discarded. -/
theorem decodeDataSet_encodeDataSet (U : Set (SampleData ctx)) :
    decodeDataSet (encodeDataSet U) = U := by
  ext s
  constructor
  · rintro ⟨a, ⟨s0, hs0, rfl⟩, decoded⟩
    rw [decodeData_encodeData] at decoded
    rwa [← decoded]
  · intro hs
    exact ⟨encodeData s, ⟨s, hs, rfl⟩, decodeData_encodeData s⟩

/-- Consistency is preserved and reflected by set-level encoding. -/
@[simp] theorem nonempty_encodeDataSet_iff (U : Set (SampleData ctx)) :
    (encodeDataSet U).Nonempty ↔ U.Nonempty := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨s, hs, _⟩ := ha
    exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨encodeData s, s, hs, rfl⟩

/-! ## Amounts: exact preservation and existing molar-composition laws -/

namespace HeterogeneousSample

/-- The amount view of a heterogeneous mixed-source sample, using the existing
`MolarComposition.Composition` carrier with exactly the sample's amounts.  The species datum is
the unique element of `Unit`; the mixed request itself is not used to build a second amount
theory. -/
def amountComposition (s : HeterogeneousSample ctx) :
    MolarComposition.Composition I Unit where
  species := fun _ => ()
  amount := s.val.amount
  amount_nonneg := s.property.2.1
  total_pos := s.property.2.2

/-- The composition's amount is literally the sample's amount. -/
@[simp] theorem amountComposition_amount (s : HeterogeneousSample ctx) (i : I) :
    (amountComposition s).amount i = s.val.amount i := rfl

/-- The total amount, inherited from the existing molar composition. -/
def total (s : HeterogeneousSample ctx) : ℝ := (amountComposition s).total

/-- The total is the sum of the sample's amounts. -/
@[simp] theorem total_eq_sum (s : HeterogeneousSample ctx) :
    s.total = ∑ i, s.val.amount i := rfl

/-- Strict positivity of the total amount, from the existing composition law. -/
theorem total_pos (s : HeterogeneousSample ctx) : 0 < s.total :=
  (amountComposition s).total_pos'

/-- The normalized mole fraction, inherited from the existing molar composition. -/
def fraction (s : HeterogeneousSample ctx) (i : I) : ℝ :=
  (amountComposition s).fraction i

/-- The fraction is the amount divided by the total. -/
@[simp] theorem fraction_eq (s : HeterogeneousSample ctx) (i : I) :
    s.fraction i = s.val.amount i / s.total := rfl

/-- Fraction nonnegativity, from the existing composition law. -/
theorem fraction_nonneg (s : HeterogeneousSample ctx) (i : I) : 0 ≤ s.fraction i :=
  (amountComposition s).fraction_nonneg i

/-- Fraction upper bound, from the existing composition law. -/
theorem fraction_le_one (s : HeterogeneousSample ctx) (i : I) : s.fraction i ≤ 1 :=
  (amountComposition s).fraction_le_one i

/-- Strong normalization, from the existing composition law. -/
theorem sum_fraction_eq_one (s : HeterogeneousSample ctx) :
    ∑ i, s.fraction i = 1 :=
  (amountComposition s).sum_fraction_eq_one

end HeterogeneousSample

namespace AssembledSample

/-- The amount view of an assembled sample, using the same existing
`MolarComposition.Composition` carrier. -/
def amountComposition (a : AssembledSample ctx) :
    MolarComposition.Composition I Unit where
  species := fun _ => ()
  amount := a.val.amount
  amount_nonneg := a.property.2.1
  total_pos := a.property.2.2

@[simp] theorem amountComposition_amount (a : AssembledSample ctx) (i : I) :
    (amountComposition a).amount i = a.val.amount i := rfl

/-- The total amount, inherited from the existing molar composition. -/
def total (a : AssembledSample ctx) : ℝ := (amountComposition a).total

@[simp] theorem total_eq_sum (a : AssembledSample ctx) :
    a.total = ∑ i, a.val.amount i := rfl

/-- Strict positivity of the total amount, from the existing composition law. -/
theorem total_pos (a : AssembledSample ctx) : 0 < a.total :=
  (amountComposition a).total_pos'

/-- The normalized mole fraction, inherited from the existing molar composition. -/
def fraction (a : AssembledSample ctx) (i : I) : ℝ :=
  (amountComposition a).fraction i

@[simp] theorem fraction_eq (a : AssembledSample ctx) (i : I) :
    a.fraction i = a.val.amount i / a.total := rfl

/-- Fraction nonnegativity, from the existing composition law. -/
theorem fraction_nonneg (a : AssembledSample ctx) (i : I) : 0 ≤ a.fraction i :=
  (amountComposition a).fraction_nonneg i

/-- Fraction upper bound, from the existing composition law. -/
theorem fraction_le_one (a : AssembledSample ctx) (i : I) : a.fraction i ≤ 1 :=
  (amountComposition a).fraction_le_one i

/-- Strong normalization, from the existing composition law. -/
theorem sum_fraction_eq_one (a : AssembledSample ctx) :
    ∑ i, a.fraction i = 1 :=
  (amountComposition a).sum_fraction_eq_one

end AssembledSample

/-- Encoding preserves every constituent amount exactly. -/
@[simp] theorem encode_amount (s : HeterogeneousSample ctx) (i : I) :
    (encode s).val.amount i = s.val.amount i := rfl

/-- Encoding preserves the total amount exactly. -/
@[simp] theorem encode_total (s : HeterogeneousSample ctx) :
    (encode s).total = s.total := rfl

/-- Encoding preserves every normalized mole fraction exactly. -/
theorem encode_fraction (s : HeterogeneousSample ctx) (i : I) :
    (encode s).fraction i = s.fraction i := rfl

/-- Decoding preserves every constituent amount exactly. -/
@[simp] theorem decode_amount (a : AssembledSample ctx) (i : I) :
    (decode a).val.amount i = a.val.amount i := rfl

/-- Decoding preserves the total amount exactly. -/
@[simp] theorem decode_total (a : AssembledSample ctx) :
    (decode a).total = a.total := rfl

/-- Decoding preserves every normalized mole fraction exactly. -/
theorem decode_fraction (a : AssembledSample ctx) (i : I) :
    (decode a).fraction i = a.fraction i := rfl

/-- The exact round trip preserves every constituent amount. -/
@[simp] theorem decode_encode_amount (s : HeterogeneousSample ctx) (i : I) :
    (decode (encode s)).val.amount i = s.val.amount i := by
  rw [decode_encode]

/-- The exact round trip preserves the total amount. -/
@[simp] theorem decode_encode_total (s : HeterogeneousSample ctx) :
    (decode (encode s)).total = s.total := by
  rw [decode_encode]

/-- The exact round trip preserves every normalized mole fraction. -/
theorem decode_encode_fraction (s : HeterogeneousSample ctx) (i : I) :
    (decode (encode s)).fraction i = s.fraction i := by
  rw [decode_encode]

/-! ## Arbitrary correlated sets of whole samples

An uncertain sample is a set of *whole* valid samples.  Membership records joint possibility of
the complete record (all constituent requests, their possible sets, and all amounts).  It is not
a product of component marginals and carries no probability, energy or weight. -/

/-- An uncertain mixed-source sample: a set of whole valid samples. -/
abbrev UncertainSample (ctx : Context I) [Fintype I] :=
  Set (HeterogeneousSample ctx)

namespace UncertainSample

/-- Consistency of an uncertain sample: at least one whole record. -/
def Consistent (U : UncertainSample ctx) : Prop :=
  U.Nonempty

@[simp] theorem consistent_iff (U : UncertainSample ctx) :
    Consistent U ↔ U.Nonempty := Iff.rfl

theorem consistent_of_mem {U : UncertainSample ctx} {s : HeterogeneousSample ctx}
    (member : s ∈ U) : Consistent U :=
  ⟨s, member⟩

@[simp] theorem not_consistent_empty :
    ¬ Consistent (∅ : UncertainSample ctx) := by
  simp [Consistent]

/-- The image of a whole uncertain sample under encoding. -/
def encodeSet (U : UncertainSample ctx) : Set (AssembledSample ctx) :=
  encode '' U

/-- The image of a set of assembled samples under decoding. -/
def decodeSet (V : Set (AssembledSample ctx)) : UncertainSample ctx :=
  decode '' V

@[simp] theorem mem_encodeSet_iff (U : UncertainSample ctx) (a : AssembledSample ctx) :
    a ∈ encodeSet U ↔ ∃ s ∈ U, encode s = a := Iff.rfl

@[simp] theorem mem_decodeSet_iff (V : Set (AssembledSample ctx)) (s : HeterogeneousSample ctx) :
    s ∈ decodeSet V ↔ ∃ a ∈ V, decode a = s := Iff.rfl

/-- **Arbitrary correlated-set recovery.**  Encoding and then decoding a set of whole samples
recovers it exactly, including every joint request/possible-set/amount pairing of every record.
No marginal product is substituted for the joint set. -/
theorem decodeSet_encodeSet (U : UncertainSample ctx) :
    decodeSet (encodeSet U) = U := by
  ext s
  constructor
  · rintro ⟨a, ⟨s0, hs0, rfl⟩, decoded⟩
    rw [decode_encode] at decoded
    rwa [← decoded]
  · intro hs
    exact ⟨encode s, ⟨s, hs, rfl⟩, decode_encode s⟩

/-- Consistency is preserved and reflected by encoding. -/
@[simp] theorem nonempty_encodeSet_iff (U : UncertainSample ctx) :
    (encodeSet U).Nonempty ↔ Consistent U := by
  constructor
  · rintro ⟨a, ha⟩
    obtain ⟨s, hs, _⟩ := ha
    exact ⟨s, hs⟩
  · rintro ⟨s, hs⟩
    exact ⟨encode s, s, hs, rfl⟩

/-- Consistency is preserved and reflected by decoding an arbitrary set of assembled samples. -/
@[simp] theorem nonempty_decodeSet_iff (V : Set (AssembledSample ctx)) :
    (decodeSet V).Nonempty ↔ V.Nonempty := by
  constructor
  · rintro ⟨s, hs⟩
    obtain ⟨a, ha, _⟩ := hs
    exact ⟨a, ha⟩
  · rintro ⟨a, ha⟩
    exact ⟨decode a, a, ha, rfl⟩

end UncertainSample

end

end OrganicStereoMixedSourceSamples
end TetraStereo.OneCenter
