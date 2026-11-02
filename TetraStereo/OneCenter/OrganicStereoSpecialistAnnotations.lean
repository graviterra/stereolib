import Mathlib.Data.Finset.Image
import TetraStereo.OneCenter.OrganicStereoFragmentSourceData
import TetraStereo.OneCenter.OrganicStereoResidueIncidence

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo.OneCenter

/-!
# Finite fragment source-reference annotations

This module is the fragment-scope metadata-retention layer.  It is *not* a chemical classifier and
it derives no stereochemical answer.  Its purpose is to carry the residue-scoped locant data of an
existing `ResidueFragment` across a change of the independent finite atom type, and to recover
exactly the fields that were stored.

The annotation language is an explicit finite structure indexed by an arbitrary atom-reference
type `V`:

* `V` is used *only* for atom references;
* `ScopeId` is a separate type for atom-independent locants and residue/fragment scopes.

Nothing in the annotation is an opaque payload, and no `String` tag is interpreted as chemistry.
The representation deliberately keeps ordered data ordered: the fragment support is a finite set,
and the scoped locant bindings are a list whose order, duplicate entries and explicit `none`
resolution flags are all retained.  Empty supports and empty binding lists are permitted; several
annotations for the same source object are permitted; there is no family totality requirement.

An atom relabelling `V ≃ W` moves every atom reference and nothing else.  The inverse and
injectivity results show that no original `V` source is hidden in the encoded annotation.  A
decoder is always given the external atom equivalence `V ≃ Fin atomCount`; the annotation itself
never stores an enumeration or a cast from an arbitrary natural number to an atom.  Encoding also
takes an explicit finite locant cover, supplied by the caller, and recovery assumes that cover is
duplicate-free and reaches every locant that the source fragment resolves.  The module does not
claim that an arbitrary locant function is finitely supported.

## Exact source data

Since the specialist authority semantics were added, a fragment annotation also carries an ordered
`sourceData : List (FragmentSourceDatum V)` channel (`[]` by default) together with the invariant
that every atom anchor of every datum belongs to the fragment support.  Source data are extra
metadata attached *alongside* the physical support and locant bindings; they never replace them.
`relabel` maps this channel with the same atom equivalence, and decoding/source-fragment recovery
ignores it.  The empty list is the compatibility default, and `ext_of_sourceData_eq_nil` is the
old support-and-bindings extensionality for annotations that carry no source data.

The residue-incidence ledger links, naming hierarchy and numbered cage/face adapters are out of
scope for this fragment module and are implemented in their separately owned modules.
-/

/-! ## Atom-independent tokens -/

/-- An atom-independent scope/locant label.  It is a distinct type so that a scope label can never
be confused with an atom reference. -/
structure ScopeId where
  /-- The numeric label itself.  No chemistry is attached to this number. -/
  index : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Encode/decode data for an atom-independent locant alphabet.  The codec is supplied externally;
it is not stored in any annotation, so the annotation remains independent of the locant type. -/
structure LocantCodec (Locant : Type*) where
  /-- Map a locant to its atom-independent finite label. -/
  code : Locant → ScopeId
  /-- Read a label back as a locant, failing outside the encoded image. -/
  decode : ScopeId → Option Locant
  /-- Encoding is left-inverse to decoding. -/
  decode_code : ∀ locant, decode (code locant) = some locant

namespace LocantCodec

/-- A locant codec has injective code map. -/
theorem code_injective {Locant : Type*} (codec : LocantCodec Locant) :
    Function.Injective codec.code := by
  intro first second equal
  have := codec.decode_code first
  rw [equal, codec.decode_code second] at this
  exact (Option.some.inj this).symm

/-- The identity codec for natural-number locants. -/
def nat : LocantCodec ℕ where
  code locant := ⟨locant⟩
  decode scope := some scope.index
  decode_code := fun _ => rfl

end LocantCodec

/-! ## Residue-scoped atom bindings -/

/-- One scoped locant binding: an atom-independent scope label paired with an optional source atom
reference.  `none` records that the scope label is present but resolves to no atom, preserving the
distinction between an unused locant and an absent one. -/
abbrev ScopedBinding (V : Type*) := ScopeId × Option V

/-- The retained data of one residue or fragment occurrence.

`support` is the finite set of referenced atoms.  `bindings` is the ordered residue-scoped locant
list; it may contain duplicates, and its order is retained.  The invariant says that every
resolved binding denotes an atom of the support. -/
structure FragmentAnnotation (V : Type*) where
  /-- Finite atom support, still referenced by `V`. -/
  support : Finset V
  /-- Ordered scoped locant bindings. -/
  bindings : List (ScopeId × Option V)
  /-- Every resolved binding denotes a support atom. -/
  resolved_mem_support : ∀ binding ∈ bindings, ∀ atom, binding.2 = some atom → atom ∈ support
  /-- Ordered exact source-level stereochemical data attached to this fragment.  It is extra
  metadata: it never replaces the physical support or the locant bindings.  The default is the
  empty list, so every pre-existing fragment is unchanged by the extension. -/
  sourceData : List (FragmentSourceDatum V) := []
  /-- Every atom anchor of every attached source datum belongs to the fragment support.  This is
  declared with auto-param syntax, so it is checked at each use site against the actual
  `sourceData`/`support` values; an omitted proof is discharged only when `sourceData = []`. -/
  sourceData_supported : ∀ datum ∈ sourceData, ∀ atom ∈ datum.atomReferences, atom ∈ support := by
    intro datum member
    exact absurd member (by simp)

namespace FragmentAnnotation

variable {V W U : Type*}

/-- The empty-source-data constructor.  It is exactly the pre-extension two-data-field fragment
annotation, with `sourceData = []`, and keeps old construction sites and their reading of the
annotation unchanged. -/
def ofEmptySourceData (support : Finset V) (bindings : List (ScopeId × Option V))
    (resolved_mem_support : ∀ binding ∈ bindings, ∀ atom, binding.2 = some atom →
      atom ∈ support) : FragmentAnnotation V where
  support := support
  bindings := bindings
  resolved_mem_support := resolved_mem_support
  sourceData := []

@[simp] theorem ofEmptySourceData_support (support : Finset V)
    (bindings : List (ScopeId × Option V))
    (resolved_mem_support : ∀ binding ∈ bindings, ∀ atom, binding.2 = some atom →
      atom ∈ support) :
    (ofEmptySourceData support bindings resolved_mem_support).support = support := rfl

@[simp] theorem ofEmptySourceData_bindings (support : Finset V)
    (bindings : List (ScopeId × Option V))
    (resolved_mem_support : ∀ binding ∈ bindings, ∀ atom, binding.2 = some atom →
      atom ∈ support) :
    (ofEmptySourceData support bindings resolved_mem_support).bindings = bindings := rfl

@[simp] theorem ofEmptySourceData_sourceData (support : Finset V)
    (bindings : List (ScopeId × Option V))
    (resolved_mem_support : ∀ binding ∈ bindings, ∀ atom, binding.2 = some atom →
      atom ∈ support) :
    (ofEmptySourceData support bindings resolved_mem_support).sourceData = [] := rfl

/-- Structure extensionality: a fragment annotation is determined by its support, its ordered
bindings **and** its ordered source data.  The two proof fields are propositional and add no data.
The old two-field statement is not valid once `sourceData` is a data field; use
`ext_of_sourceData_eq_nil` for the empty-data specialisation. -/
@[ext] theorem ext {first second : FragmentAnnotation V}
    (support : first.support = second.support) (bindings : first.bindings = second.bindings)
    (sourceData : first.sourceData = second.sourceData) :
    first = second := by
  cases first
  cases second
  simp_all

/-- Empty-source-data compatibility specialisation of extensionality: if both annotations carry
`sourceData = []`, then support and ordered bindings determine the annotation, exactly as before
the source-data extension. -/
theorem ext_of_sourceData_eq_nil {first second : FragmentAnnotation V}
    (firstEmpty : first.sourceData = []) (secondEmpty : second.sourceData = [])
    (support : first.support = second.support) (bindings : first.bindings = second.bindings) :
    first = second :=
  ext support bindings (by rw [firstEmpty, secondEmpty])

/-- Atom relabelling of a fragment annotation.  Only `V` references move; scope labels, resolution
flags, list order and every attached source datum's non-atom payload are copied verbatim.  Source
data are relabelled with the same atom equivalence and their support invariant is proved
transportable. -/
def relabel (f : V ≃ W) (annotation : FragmentAnnotation V) : FragmentAnnotation W where
  support := annotation.support.map f.toEmbedding
  bindings := annotation.bindings.map fun binding => (binding.1, binding.2.map f)
  resolved_mem_support := by
    intro binding member atom found
    obtain ⟨original, originalMember, equality⟩ := List.mem_map.mp member
    cases binding with
    | mk scope atom? =>
        cases original with
        | mk originalScope originalAtom =>
            simp only [Prod.mk.injEq] at equality
            obtain ⟨_, valueEq⟩ := equality
            cases h : originalAtom with
            | none =>
                simp [h] at valueEq
                rw [← valueEq] at found
                simp at found
            | some value =>
                simp only [h, Option.map_some] at valueEq
                have atomEq : atom = f value :=
                  (Option.some.inj (valueEq.trans found)).symm
                have valueMember : (originalScope, some value) ∈ annotation.bindings := by
                  simpa [h] using originalMember
                have valueMem := annotation.resolved_mem_support _ valueMember value rfl
                rw [atomEq]
                exact Finset.mem_map.mpr ⟨value, valueMem, rfl⟩
  sourceData := annotation.sourceData.map (FragmentSourceDatum.relabel f)
  sourceData_supported := by
    intro datum member atom atomMem
    obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
    rw [FragmentSourceDatum.atomReferences_relabel] at atomMem
    obtain ⟨originalAtom, originalAtomMem, rfl⟩ := List.mem_map.mp atomMem
    exact Finset.mem_map.mpr
      ⟨originalAtom,
        annotation.sourceData_supported original originalMember originalAtom originalAtomMem,
        rfl⟩

@[simp] theorem relabel_support (f : V ≃ W) (annotation : FragmentAnnotation V) :
    (annotation.relabel f).support = annotation.support.map f.toEmbedding := rfl

@[simp] theorem relabel_bindings (f : V ≃ W) (annotation : FragmentAnnotation V) :
    (annotation.relabel f).bindings =
      annotation.bindings.map fun binding => (binding.1, binding.2.map f) := rfl

/-- Relabelling maps the ordered source-data list with the same atom equivalence, preserving order
and every non-atom payload. -/
@[simp] theorem relabel_sourceData (f : V ≃ W) (annotation : FragmentAnnotation V) :
    (annotation.relabel f).sourceData =
      annotation.sourceData.map (FragmentSourceDatum.relabel f) := rfl

/-- Pointwise composition of two binding relabellings. -/
private theorem map_binding_comp (f : V ≃ W) (g : W ≃ U)
    (binding : ScopeId × Option V) :
    (fun current : ScopeId × Option W => (current.1, current.2.map g))
        ((fun current : ScopeId × Option V => (current.1, current.2.map f)) binding) =
      (binding.1, binding.2.map (f.trans g)) := by
  cases binding with
  | mk scope atom? => cases atom? <;> rfl

/-- Composition of the binding relabelling over a list. -/
private theorem map_binding_trans (f : V ≃ W) (g : W ≃ U)
    (bindings : List (ScopeId × Option V)) :
    (bindings.map fun binding => (binding.1, binding.2.map f)).map
        (fun binding => (binding.1, binding.2.map g)) =
      bindings.map fun binding => (binding.1, binding.2.map (f.trans g)) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro binding _
  exact map_binding_comp f g binding

/-- The identity relabelling leaves a binding list unchanged. -/
private theorem map_binding_refl (bindings : List (ScopeId × Option V)) :
    bindings.map (fun binding => (binding.1, binding.2.map (Equiv.refl V))) = bindings := by
  rw [show (fun binding : ScopeId × Option V =>
      (binding.1, binding.2.map (Equiv.refl V))) = id from by
    funext binding
    cases binding with
    | mk scope atom? => cases atom? <;> rfl]
  exact List.map_id bindings

/-- Relabelling composes along equivalence composition. -/
theorem relabel_trans (f : V ≃ W) (g : W ≃ U) (annotation : FragmentAnnotation V) :
    (annotation.relabel f).relabel g = annotation.relabel (f.trans g) := by
  apply FragmentAnnotation.ext
  · simp [relabel, Finset.map_map, Equiv.trans_toEmbedding]
  · exact map_binding_trans f g annotation.bindings
  · rw [relabel_sourceData, relabel_sourceData, relabel_sourceData, List.map_map]
    apply List.map_congr_left
    intro datum _
    exact FragmentSourceDatum.relabel_trans f g datum

/-- Relabelling by the identity equivalence is the identity. -/
@[simp] theorem relabel_refl (annotation : FragmentAnnotation V) :
    annotation.relabel (Equiv.refl V) = annotation := by
  apply FragmentAnnotation.ext
  · simp [relabel]
  · exact map_binding_refl annotation.bindings
  · rw [relabel_sourceData]
    change annotation.sourceData.map (fun datum => datum.relabel (Equiv.refl V)) =
      annotation.sourceData
    rw [show (fun datum => datum.relabel (Equiv.refl V)) = id from
      funext fun datum => FragmentSourceDatum.relabel_refl datum]
    exact List.map_id annotation.sourceData

/-- Relabelling by an equivalence and then by its inverse is the identity. -/
theorem relabel_relabel_symm (f : V ≃ W) (annotation : FragmentAnnotation V) :
    (annotation.relabel f).relabel f.symm = annotation := by
  rw [relabel_trans f f.symm]
  rw [show f.trans f.symm = Equiv.refl V from by ext atom; simp]
  exact relabel_refl annotation

/-- Relabelling by an inverse and then by the equivalence is the identity. -/
theorem relabel_symm_relabel (f : V ≃ W) (annotation : FragmentAnnotation W) :
    (annotation.relabel f.symm).relabel f = annotation := by
  rw [relabel_trans f.symm f]
  rw [show f.symm.trans f = Equiv.refl W from by ext atom; simp]
  exact relabel_refl annotation

/-- Relabelling by an equivalence is injective: the atom references are the only varying data. -/
theorem relabel_injective (f : V ≃ W) :
    Function.Injective (fun annotation : FragmentAnnotation V => annotation.relabel f) := by
  intro first second equal
  have inject := congrArg (fun annotation : FragmentAnnotation W => annotation.relabel f.symm) equal
  simpa [relabel_relabel_symm] using inject

end FragmentAnnotation

/-! ## Decoding residue fragments with an externally supplied atom equivalence -/

/-- Look up a scope label in an ordered binding list.  The first binding wins; duplicates are
therefore permitted and are preserved in the list. -/
def lookupBinding? {V : Type*} (bindings : List (ScopedBinding V)) (scope : ScopeId) :
    Option V :=
  (bindings.lookup scope).join

/-- The encoding of one fragment relative to an externally supplied atom equivalence `e`.

`cover` is a finite, duplicate-free list of locants reaching every locant that the source fragment
resolves.  It is supplied by the caller; this module never enumerates a locant family on its own.
All other data are copied exactly: scope codes, resolution flags and list order. -/
def encodeFragment {V Locant : Type*} (codec : LocantCodec Locant) {n : ℕ} (e : V ≃ Fin n)
    (fragment : ResidueFragment Locant n) (cover : List Locant) :
    FragmentAnnotation V where
  support := fragment.support.map e.symm.toEmbedding
  bindings := cover.map fun locant => (codec.code locant, (fragment.incidence locant).map e.symm)
  resolved_mem_support := by
    intro binding member atom found
    obtain ⟨locant, _, equality⟩ := List.mem_map.mp member
    cases binding with
    | mk scope atom? =>
        simp only [Prod.mk.injEq] at equality
        obtain ⟨_, valueEq⟩ := equality
        cases h : fragment.incidence locant with
        | none =>
            simp [h] at valueEq
            rw [← valueEq] at found
            simp at found
        | some value =>
            simp only [h, Option.map_some] at valueEq
            have atomEq : atom = e.symm value :=
              (Option.some.inj (valueEq.trans found)).symm
            rw [atomEq]
            exact Finset.mem_map.mpr
              ⟨value, fragment.incidence_mem_support locant value h, rfl⟩

@[simp] theorem encodeFragment_support {V Locant : Type*} (codec : LocantCodec Locant) {n : ℕ}
    (e : V ≃ Fin n) (fragment : ResidueFragment Locant n) (cover : List Locant) :
    (encodeFragment codec e fragment cover).support =
      fragment.support.map e.symm.toEmbedding := rfl

@[simp] theorem encodeFragment_bindings {V Locant : Type*} (codec : LocantCodec Locant) {n : ℕ}
    (e : V ≃ Fin n) (fragment : ResidueFragment Locant n) (cover : List Locant) :
    (encodeFragment codec e fragment cover).bindings =
      cover.map fun locant => (codec.code locant, (fragment.incidence locant).map e.symm) := rfl

/-- The existing fragment constructor attaches no source data: its source-data channel is exactly
the empty list, so all prior encoding/recovery statements are unaffected by the extension. -/
@[simp] theorem encodeFragment_sourceData {V Locant : Type*} (codec : LocantCodec Locant) {n : ℕ}
    (e : V ≃ Fin n) (fragment : ResidueFragment Locant n) (cover : List Locant) :
    (encodeFragment codec e fragment cover).sourceData = [] := rfl

/-! ### Ordered source-data lookup and attachment -/

namespace FragmentAnnotation

variable {V W U : Type*}

/-- Positional lookup in the ordered source-data list.  `none` means the position is beyond the
end; a datum itself is always returned, so the order and multiplicity of the list are observable. -/
def sourceDataAt? (annotation : FragmentAnnotation V) (index : ℕ) :
    Option (FragmentSourceDatum V) :=
  annotation.sourceData[index]?

/-- Positional lookup commutes with atom relabelling. -/
@[simp] theorem sourceDataAt?_relabel (f : V ≃ W) (annotation : FragmentAnnotation V)
    (index : ℕ) :
    (annotation.relabel f).sourceDataAt? index =
      (annotation.sourceDataAt? index).map (FragmentSourceDatum.relabel f) := by
  unfold sourceDataAt?
  simp [relabel]

/-- Encoded fragments have no source-data position. -/
@[simp] theorem sourceDataAt?_encodeFragment {V Locant : Type*} (codec : LocantCodec Locant)
    {n : ℕ} (e : V ≃ Fin n) (fragment : ResidueFragment Locant n) (cover : List Locant)
    (index : ℕ) :
    (encodeFragment codec e fragment cover).sourceDataAt? index = none := by
  unfold sourceDataAt?
  simp

/-- Relabelling preserves the length of the ordered source-data list. -/
@[simp] theorem sourceData_length_relabel (f : V ≃ W) (annotation : FragmentAnnotation V) :
    (annotation.relabel f).sourceData.length = annotation.sourceData.length := by
  simp [relabel]

/-- Membership of a relabelled source datum is exactly membership of the original datum.  This is
where injectivity of datum relabelling is used: no extra `V`-reference can appear. -/
theorem sourceData_mem_relabel_iff (f : V ≃ W) (annotation : FragmentAnnotation V)
    (datum : FragmentSourceDatum V) :
    datum.relabel f ∈ (annotation.relabel f).sourceData ↔ datum ∈ annotation.sourceData := by
  rw [relabel_sourceData, List.mem_map]
  constructor
  · rintro ⟨original, originalMember, equal⟩
    have : original = datum := FragmentSourceDatum.relabel_injective f equal
    simpa [this] using originalMember
  · intro member
    exact ⟨datum, member, rfl⟩

/-- Attach ordered source data to an existing fragment annotation **alongside** its existing data.

The new data are appended after the existing list, so old order is retained and no existing
physical datum (support, bindings or prior source data) is overwritten.  The `supported` premise is
exactly the anchor-membership invariant, stated against the unchanged support. -/
def withSourceData (annotation : FragmentAnnotation V) (data : List (FragmentSourceDatum V))
    (supported : ∀ datum ∈ data, ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support) :
    FragmentAnnotation V where
  support := annotation.support
  bindings := annotation.bindings
  resolved_mem_support := annotation.resolved_mem_support
  sourceData := annotation.sourceData ++ data
  sourceData_supported := by
    intro datum member atom atomMem
    rw [List.mem_append] at member
    rcases member with old | fresh
    · exact annotation.sourceData_supported datum old atom atomMem
    · exact supported datum fresh atom atomMem

@[simp] theorem withSourceData_support (annotation : FragmentAnnotation V)
    (data : List (FragmentSourceDatum V))
    (supported : ∀ datum ∈ data, ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support) :
    (annotation.withSourceData data supported).support = annotation.support := rfl

@[simp] theorem withSourceData_bindings (annotation : FragmentAnnotation V)
    (data : List (FragmentSourceDatum V))
    (supported : ∀ datum ∈ data, ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support) :
    (annotation.withSourceData data supported).bindings = annotation.bindings := rfl

/-- Attachment appends: existing source data stay in front, new data follow in order. -/
@[simp] theorem withSourceData_sourceData (annotation : FragmentAnnotation V)
    (data : List (FragmentSourceDatum V))
    (supported : ∀ datum ∈ data, ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support) :
    (annotation.withSourceData data supported).sourceData = annotation.sourceData ++ data := rfl

/-- Positional lookup after attachment is positional lookup in the concatenation. -/
theorem sourceDataAt?_withSourceData (annotation : FragmentAnnotation V)
    (data : List (FragmentSourceDatum V))
    (supported : ∀ datum ∈ data, ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support)
    (index : ℕ) :
    (annotation.withSourceData data supported).sourceDataAt? index =
      (annotation.sourceData ++ data)[index]? := rfl

/-- Positions inside the pre-existing source data are unaffected by attachment. -/
theorem sourceDataAt?_withSourceData_of_lt (annotation : FragmentAnnotation V)
    (data : List (FragmentSourceDatum V))
    (supported : ∀ datum ∈ data, ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support)
    (index : ℕ) (inside : index < annotation.sourceData.length) :
    (annotation.withSourceData data supported).sourceDataAt? index =
      annotation.sourceDataAt? index := by
  unfold sourceDataAt?
  rw [withSourceData_sourceData]
  exact List.getElem?_append_left inside

/-- Attachment commutes with atom relabelling; the appended data are relabelled by the same
equivalence and the support proof transports. -/
theorem relabel_withSourceData (f : V ≃ W) (annotation : FragmentAnnotation V)
    (data : List (FragmentSourceDatum V))
    (supported : ∀ datum ∈ data, ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support) :
    (annotation.withSourceData data supported).relabel f =
      (annotation.relabel f).withSourceData
        (data.map (FragmentSourceDatum.relabel f))
        (by
          intro datum member atom atomMem
          obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
          rw [FragmentSourceDatum.atomReferences_relabel] at atomMem
          obtain ⟨originalAtom, originalAtomMem, rfl⟩ := List.mem_map.mp atomMem
          exact Finset.mem_map.mpr
            ⟨originalAtom, supported original originalMember originalAtom originalAtomMem, rfl⟩) := by
  apply FragmentAnnotation.ext
  · rfl
  · rfl
  · rw [relabel_sourceData, withSourceData_sourceData, withSourceData_sourceData, List.map_append]
    rfl

end FragmentAnnotation

/-- Decoding of one fragment annotation into the existing residue-fragment carrier.  The atom
equivalence `e` is external.  The result is total precisely because the annotation carries the
support-membership invariant; an out-of-range source cannot be manufactured. -/
def decodeFragment {V Locant : Type*} (codec : LocantCodec Locant) {n : ℕ} (e : V ≃ Fin n)
    (annotation : FragmentAnnotation V) : ResidueFragment Locant n where
  support := annotation.support.map e.toEmbedding
  incidence locant := (lookupBinding? annotation.bindings (codec.code locant)).map e
  incidence_mem_support := by
    intro locant atom found
    unfold lookupBinding? at found
    cases lookupEq : annotation.bindings.lookup (codec.code locant) with
    | none => simp [lookupEq] at found
    | some value =>
        cases value with
        | none => simp [lookupEq] at found
        | some value =>
            obtain ⟨before, after, definition, _⟩ :=
              (List.lookup_eq_some_iff (l := annotation.bindings)
                (k := codec.code locant) (b := some value)).mp lookupEq
            have member : (codec.code locant, some value) ∈ annotation.bindings := by
              rw [definition]
              simp
            have valueMem := annotation.resolved_mem_support _ member value rfl
            simp [lookupEq] at found
            rw [← found]
            exact Finset.mem_map.mpr ⟨value, valueMem, rfl⟩

/-- Source data are metadata: decoding ignores them.  Attaching data (in particular with
`withSourceData`) does not change the recovered residue fragment in any way. -/
@[simp] theorem decodeFragment_withSourceData {V Locant : Type*} (codec : LocantCodec Locant)
    {n : ℕ} (e : V ≃ Fin n) (annotation : FragmentAnnotation V)
    (data : List (FragmentSourceDatum V))
    (supported : ∀ datum ∈ data, ∀ atom ∈ datum.atomReferences, atom ∈ annotation.support) :
    decodeFragment codec e (annotation.withSourceData data supported) =
      decodeFragment codec e annotation := rfl

/-! ### Exact recovery of the encoded fragment -/

/-- A finite set mapped along an equivalence and back is unchanged. -/
theorem Finset.map_symm_toEmbedding_map {V W : Type*} (e : V ≃ W) (support : Finset W) :
    (support.map e.symm.toEmbedding).map e.toEmbedding = support := by
  rw [Finset.map_map]
  have embeddingEq : e.symm.toEmbedding.trans e.toEmbedding = Function.Embedding.refl W := by
    ext atom
    simp
  rw [embeddingEq, Finset.map_refl]

/-- Membership round trip for a finite set mapped along an equivalence and back. -/
theorem Finset.mem_map_symm_toEmbedding_map {V W : Type*} (e : V ≃ W)
    (support : Finset W) (atom : W) :
    atom ∈ (support.map e.symm.toEmbedding).map e.toEmbedding ↔ atom ∈ support := by
  rw [Finset.map_symm_toEmbedding_map]

/-- Ordered key/value list lookup, under an injective key map and a duplicate-free key list. -/
private theorem lookup_map_code_eq_some_iff {Key Value α : Type*} [DecidableEq Key]
    (keys : List α) (code : α → Key) (value : α → Value)
    (injective : Function.Injective code) (nodup : keys.Nodup) (key : α) (result : Value) :
    (keys.map fun entry => (code entry, value entry)).lookup (code key) = some result ↔
      key ∈ keys ∧ value key = result := by
  induction keys with
  | nil => simp
  | cons head tail hypothesis =>
      rw [List.map_cons, List.lookup_cons]
      have tailNodup : tail.Nodup := (List.nodup_cons.mp nodup).2
      by_cases same : code key = code head
      · have keyEq : key = head := injective same
        simp [keyEq]
      · have notBeq : (code key == code head) = false := beq_eq_false_iff_ne.mpr same
        rw [notBeq]
        simp only []
        rw [hypothesis tailNodup]
        constructor
        · intro hyp
          exact ⟨List.mem_cons_of_mem _ hyp.1, hyp.2⟩
        · intro hyp
          have hmem : key ∈ tail := by
            rcases List.mem_cons.mp hyp.1 with keyHead | keyTail
            · exact absurd (congrArg code keyHead) same
            · exact keyTail
          exact ⟨hmem, hyp.2⟩

/-- Ordered key/value list lookup is `none` exactly when the key does not occur. -/
private theorem lookup_map_code_eq_none_iff {Key Value α : Type*} [DecidableEq Key]
    (keys : List α) (code : α → Key) (value : α → Value)
    (injective : Function.Injective code) (nodup : keys.Nodup) (key : α) :
    (keys.map fun entry => (code entry, value entry)).lookup (code key) = none ↔
      key ∉ keys := by
  induction keys with
  | nil => simp
  | cons head tail hypothesis =>
      rw [List.map_cons, List.lookup_cons]
      have tailNodup : tail.Nodup := (List.nodup_cons.mp nodup).2
      by_cases same : code key = code head
      · have keyEq : key = head := injective same
        simp [keyEq]
      · have notBeq : (code key == code head) = false := beq_eq_false_iff_ne.mpr same
        rw [notBeq]
        simp only []
        rw [hypothesis tailNodup]
        constructor
        · intro notTail member
          rcases List.mem_cons.mp member with keyHead | keyTail
          · exact absurd (congrArg code keyHead) same
          · exact notTail keyTail
        · intro notCons tailMember
          exact notCons (List.mem_cons_of_mem _ tailMember)

/-- The decoded incidence of an encoded fragment is exactly the source incidence at every locant. -/
theorem decodeFragment_incidence {V Locant : Type*} (codec : LocantCodec Locant) {n : ℕ}
    (e : V ≃ Fin n) (fragment : ResidueFragment Locant n) (cover : List Locant)
    (coverNodup : cover.Nodup)
    (covers : ∀ (locant : Locant) (atom : Fin n),
      fragment.incidence locant = some atom → locant ∈ cover)
    (locant : Locant) :
    (decodeFragment codec e (encodeFragment codec e fragment cover)).incidence
        locant = fragment.incidence locant := by
  unfold decodeFragment lookupBinding?
  simp only [encodeFragment_bindings]
  cases h : fragment.incidence locant with
  | none =>
      by_cases member : locant ∈ cover
      · have lookupSome :
            (cover.map fun entry =>
                (codec.code entry, (fragment.incidence entry).map e.symm)).lookup
                (codec.code locant) = some (none : Option V) :=
          (lookup_map_code_eq_some_iff cover codec.code
            (fun entry => (fragment.incidence entry).map e.symm)
            codec.code_injective coverNodup locant (none : Option V)).mpr
            ⟨member, by simp [h]⟩
        rw [lookupSome]
        simp
      · have lookupNone :
            (cover.map fun entry =>
                (codec.code entry, (fragment.incidence entry).map e.symm)).lookup
                (codec.code locant) = none :=
          (lookup_map_code_eq_none_iff cover codec.code
            (fun entry => (fragment.incidence entry).map e.symm)
            codec.code_injective coverNodup locant).mpr member
        rw [lookupNone]
        simp
  | some atom =>
      have member : locant ∈ cover := covers locant atom h
      have lookupSome :
          (cover.map fun entry =>
              (codec.code entry, (fragment.incidence entry).map e.symm)).lookup
              (codec.code locant) = some (some (e.symm atom)) :=
        (lookup_map_code_eq_some_iff cover codec.code
          (fun entry => (fragment.incidence entry).map e.symm)
          codec.code_injective coverNodup locant (some (e.symm atom))).mpr
          ⟨member, by simp [h]⟩
      rw [lookupSome]
      simp

/-- Exact support recovery for the encoded fragment. -/
theorem decodeFragment_support {V Locant : Type*} (codec : LocantCodec Locant) {n : ℕ}
    (e : V ≃ Fin n) (fragment : ResidueFragment Locant n) (cover : List Locant)
    (_coverNodup : cover.Nodup)
    (_covers : ∀ (locant : Locant) (atom : Fin n),
      fragment.incidence locant = some atom → locant ∈ cover) :
    (decodeFragment codec e (encodeFragment codec e fragment cover)).support =
      fragment.support := by
  unfold decodeFragment
  simp only [encodeFragment_support]
  exact Finset.map_symm_toEmbedding_map e fragment.support

/-- Extensionality for the existing residue-fragment carrier.  The source module does not provide
an `ext` lemma, and the support-membership field is propositional data. -/
private theorem residueFragment_ext {Locant : Type*} {n : ℕ}
    {first second : ResidueFragment Locant n} (support : first.support = second.support)
    (incidence : first.incidence = second.incidence) : first = second := by
  cases first
  cases second
  simp_all

/-- Exact recovery of a residue fragment from its encoded annotation: support and the complete
scoped incidence function are both recovered. -/
theorem decodeFragment_encodeFragment {V Locant : Type*} (codec : LocantCodec Locant) {n : ℕ}
    (e : V ≃ Fin n) (fragment : ResidueFragment Locant n) (cover : List Locant)
    (coverNodup : cover.Nodup)
    (covers : ∀ (locant : Locant) (atom : Fin n),
      fragment.incidence locant = some atom → locant ∈ cover) :
    decodeFragment codec e (encodeFragment codec e fragment cover) = fragment := by
  apply residueFragment_ext
  · exact decodeFragment_support codec e fragment cover coverNodup covers
  · funext locant
    exact decodeFragment_incidence codec e fragment cover coverNodup covers locant

end TetraStereo.OneCenter
