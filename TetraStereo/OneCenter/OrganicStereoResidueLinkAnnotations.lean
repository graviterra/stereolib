import TetraStereo.OneCenter.OrganicStereoSpecialistAnnotations

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo.OneCenter

/-!
# Atom-independent annotations for the actual residue incidence ledger

This module is the missing link/naming-hierarchy retention layer for
`TetraStereo.OneCenter.OrganicStereoResidueIncidence.ResidueIncidenceLedger`.  It is *not* a
chemical classifier and derives no descriptor, class or stereochemical answer.

The finite fragment channel is reused from `OrganicStereoSpecialistAnnotations`: a residue scope is
carried by the existing `FragmentAnnotation V` (finite `V`-referenced support plus an ordered list
of atom-independent `ScopeId` locant bindings).  This module adds the two pieces that channel does
not have:

* an ordered list of directed residue links, retaining source/target residue references, the
  residue-scoped source/target locant tokens, and a **bounded occurrence index** into the actual
  source interaction list (`Fin interactionCount`, where `interactionCount` is definitionally the
  source `interactions.length` in `encode`);
* an optional naming parent hierarchy (`ResidueParentHierarchy`), kept in a field of its own so that
  nomenclature parentage is never identified with directed connectivity.

## Short API

* `AnnotatedResidueLink` — one atom-independent directed link (`source`, `sourceLocant`, `target`,
  `targetLocant`, `interaction`), with `interactionIndex`/`interactionIndex_bound` exposing the
  actual source occurrence position and its bound.
* `ResidueLedgerAnnotation V residueCount interactionCount` — the concrete finite annotation
  channel: residues, links, optional hierarchy.
* `LocantCover ledger` — the finite, duplicate-free locant cover (and its completeness proof)
  required for exact fragment recovery.
* `encode` / `encodeOfCover` — constructor from a real `ResidueIncidenceLedger`.
* `ResidueLedgerView` / `viewOfLedger` — the non-proof observable content of a ledger.
* `decodeView?` / `decodeView?_encodeOfCover` — recovery of that observable content from encoded
  data alone (the original ledger is only the specification on the right-hand side).
* `relabel` and its laws — atom relabelling along an external `V ≃ W`, preserving every non-atom
  reference verbatim.
* `viewToLedger` — reconstruction of the full dependent ledger from a view; the only extra inputs
  are the two source participant certificates, which are *not* stored in the atom-independent
  annotation (see the section "Reconstructing the dependent certificate").
* `resolveAnchor?` / `resolveBondAnchors?` — resolve source locants through the actual ledger
  incidence into atom anchors of the external atom language, with support-membership certificates.
* `encodeWithSourceData` / `encodeOfCoverWithSourceData` — `encode`/`encodeOfCover` plus
  caller-supplied ordered `FragmentSourceDatum` data attached alongside each encoded residue.
* `sourceData` / `relabel_sourceData` — access to, and atom-relabelling compatibility of, the
  per-residue source-data channel carried by the underlying `FragmentAnnotation`.

Nothing here is an opaque payload: every field is a `Finset`, `List`, `Option`, `Fin`, `ScopeId`
or a proposition.  Locant encoding/decoding is delegated to the externally supplied
`LocantCodec`, whose stated `decode_code` law is the only codec property used below.
-/

/-! ## Atom-independent directed links -/

/-- A directed residue link in atom-independent form.

`source` and `target` are independent finite residue references.  Locants are `ScopeId` tokens, so
they are scoped by residue and never confused with atoms.  `interaction` is a `Fin` index into the
actual source interaction list; in every encoding below its type is definitionally the source
`interactions.length`, so a link can never name a non-existent source interaction. -/
structure AnnotatedResidueLink (residueCount interactionCount : ℕ) where
  source : Fin residueCount
  sourceLocant : ScopeId
  target : Fin residueCount
  targetLocant : ScopeId
  interaction : Fin interactionCount
  deriving DecidableEq, Repr

namespace AnnotatedResidueLink

variable {residueCount interactionCount : ℕ}

/-- Structure extensionality. -/
@[ext] theorem ext {first second : AnnotatedResidueLink residueCount interactionCount}
    (source : first.source = second.source)
    (sourceLocant : first.sourceLocant = second.sourceLocant)
    (target : first.target = second.target)
    (targetLocant : first.targetLocant = second.targetLocant)
    (interaction : first.interaction = second.interaction) : first = second := by
  cases first
  cases second
  simp_all

/-- The actual source-interaction occurrence index carried by an annotated link, as an
atom-independent natural number. -/
def interactionIndex (link : AnnotatedResidueLink residueCount interactionCount) : ℕ :=
  link.interaction.val

@[simp] theorem interactionIndex_eq (link : AnnotatedResidueLink residueCount interactionCount) :
    link.interactionIndex = link.interaction.val := rfl

/-- The occurrence index is certified to lie inside the actual source interaction count.  This is
the bound that makes the reference an actual source occurrence rather than a free-form number. -/
theorem interactionIndex_bound (link : AnnotatedResidueLink residueCount interactionCount) :
    link.interactionIndex < interactionCount :=
  link.interaction.isLt

end AnnotatedResidueLink

/-- Encode one real directed residue link.  Source and target residue references, locant order and
the actual source interaction index are copied exactly; only the locant tokens are encoded. -/
def encodeLink {Locant : Type*} (codec : LocantCodec Locant) {residueCount interactionCount : ℕ}
    (link : DirectedResidueLink Locant (Fin residueCount) interactionCount) :
    AnnotatedResidueLink residueCount interactionCount where
  source := link.source
  sourceLocant := codec.code link.sourceLocant
  target := link.target
  targetLocant := codec.code link.targetLocant
  interaction := link.interaction

@[simp] theorem encodeLink_source {Locant : Type*} (codec : LocantCodec Locant)
    {residueCount interactionCount : ℕ}
    (link : DirectedResidueLink Locant (Fin residueCount) interactionCount) :
    (encodeLink codec link).source = link.source := rfl

@[simp] theorem encodeLink_sourceLocant {Locant : Type*} (codec : LocantCodec Locant)
    {residueCount interactionCount : ℕ}
    (link : DirectedResidueLink Locant (Fin residueCount) interactionCount) :
    (encodeLink codec link).sourceLocant = codec.code link.sourceLocant := rfl

@[simp] theorem encodeLink_target {Locant : Type*} (codec : LocantCodec Locant)
    {residueCount interactionCount : ℕ}
    (link : DirectedResidueLink Locant (Fin residueCount) interactionCount) :
    (encodeLink codec link).target = link.target := rfl

@[simp] theorem encodeLink_targetLocant {Locant : Type*} (codec : LocantCodec Locant)
    {residueCount interactionCount : ℕ}
    (link : DirectedResidueLink Locant (Fin residueCount) interactionCount) :
    (encodeLink codec link).targetLocant = codec.code link.targetLocant := rfl

@[simp] theorem encodeLink_interaction {Locant : Type*} (codec : LocantCodec Locant)
    {residueCount interactionCount : ℕ}
    (link : DirectedResidueLink Locant (Fin residueCount) interactionCount) :
    (encodeLink codec link).interaction = link.interaction := rfl

/-- Decode one annotated link, failing only when a stored scope label is outside the encoded
locant image.  The interaction index is unchanged. -/
def decodeLink? {Locant : Type*} (codec : LocantCodec Locant) {residueCount interactionCount : ℕ}
    (link : AnnotatedResidueLink residueCount interactionCount) :
    Option (DirectedResidueLink Locant (Fin residueCount) interactionCount) :=
  (codec.decode link.sourceLocant).bind fun sourceLocant =>
    (codec.decode link.targetLocant).bind fun targetLocant =>
      some
        { source := link.source
          sourceLocant := sourceLocant
          target := link.target
          targetLocant := targetLocant
          interaction := link.interaction }

/-- Exact link round trip: decoding an encoded link returns the original link.  This holds for
any externally supplied `LocantCodec`, using its stated `decode_code` law. -/
@[simp] theorem decodeLink?_encode {Locant : Type*} (codec : LocantCodec Locant)
    {residueCount interactionCount : ℕ}
    (link : DirectedResidueLink Locant (Fin residueCount) interactionCount) :
    decodeLink? codec (encodeLink codec link) = some link := by
  cases link
  simp [decodeLink?, encodeLink, LocantCodec.decode_code]

/-- Encoding real links is injective: the annotated link determines the source link exactly. -/
theorem encodeLink_injective {Locant : Type*} (codec : LocantCodec Locant)
    {residueCount interactionCount : ℕ} :
    Function.Injective
      (fun link : DirectedResidueLink Locant (Fin residueCount) interactionCount =>
        encodeLink codec link) := by
  intro first second equality
  have decoded := congrArg (decodeLink? codec) equality
  simpa using decoded

/-! ## Finite locant covers -/

/-- A finite, duplicate-free cover of every locant that a real ledger fragment resolves, together
with its completeness proof.  This is exactly the extra data needed for exact fragment recovery;
it is supplied by the caller and is never guessed by this module. -/
structure LocantCover {Locant : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Locant input) where
  /-- One finite locant list per residue. -/
  cover : Fin ledger.residueCount → List Locant
  /-- Each cover list is duplicate-free, so ordered lookup is unambiguous. -/
  nodup : ∀ index, (cover index).Nodup
  /-- Every locant that resolves in a residue belongs to that residue's cover. -/
  covers : ∀ (index : Fin ledger.residueCount) (locant : Locant)
    (atom : Fin input.input.molecule.atomCount),
      (ledger.residue index).incidence locant = some atom → locant ∈ cover index

/-! ## The annotation channel -/

/-- A finite, atom-independent residue-ledger annotation.

* `residue` reuses the existing typed fragment channel `FragmentAnnotation V` for every residue
  scope (supports and ordered scoped bindings).
* `links` is an ordered list; duplicates, cycles and arbitrary direction are permitted, and its
  order is retained.
* `hierarchy?` is the optional naming parent hierarchy.  It is a separate field: the annotation
  never derives parent edges from `links`, nor links from `hierarchy?`. -/
structure ResidueLedgerAnnotation (V : Type*) (residueCount interactionCount : ℕ) where
  residue : Fin residueCount → FragmentAnnotation V
  links : List (AnnotatedResidueLink residueCount interactionCount)
  hierarchy? : Option (ResidueParentHierarchy residueCount) := none

namespace ResidueLedgerAnnotation

variable {V W U : Type*} {residueCount interactionCount : ℕ}

/-- Structure extensionality. -/
@[ext] theorem ext {first second : ResidueLedgerAnnotation V residueCount interactionCount}
    (residue : first.residue = second.residue) (links : first.links = second.links)
    (hierarchy? : first.hierarchy? = second.hierarchy?) : first = second := by
  cases first
  cases second
  simp_all

/-- The number of residue scopes, exposed as data for consumers of the annotation. -/
def residueTotal (_annotation : ResidueLedgerAnnotation V residueCount interactionCount) : ℕ :=
  residueCount

/-- The number of source interaction occurrences available to the annotation. -/
def interactionTotal (_annotation : ResidueLedgerAnnotation V residueCount interactionCount) : ℕ :=
  interactionCount

@[simp] theorem residueTotal_eq (annotation : ResidueLedgerAnnotation V residueCount
    interactionCount) : annotation.residueTotal = residueCount := rfl

@[simp] theorem interactionTotal_eq (annotation : ResidueLedgerAnnotation V residueCount
    interactionCount) : annotation.interactionTotal = interactionCount := rfl

/-- The naming parent of a residue, if a hierarchy is present. -/
def hierarchyParent? (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) : Option (Fin residueCount) :=
  annotation.hierarchy?.bind fun hierarchy => hierarchy.parent index

/-- The naming rank of a residue, if a hierarchy is present.  Ranks are non-atom data and are
retained verbatim; a present hierarchy always has strictly decreasing parent edges. -/
def hierarchyRank? (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) : Option ℕ :=
  annotation.hierarchy?.map fun hierarchy => hierarchy.rank index

/-- Relabel the atom references of an annotation along an external equivalence `V ≃ W`.  Every
non-atom reference (scope labels, residue references, occurrence indices, link order and the whole
naming hierarchy) is copied verbatim. -/
def relabel (f : V ≃ W) (annotation : ResidueLedgerAnnotation V residueCount interactionCount) :
    ResidueLedgerAnnotation W residueCount interactionCount where
  residue index := (annotation.residue index).relabel f
  links := annotation.links
  hierarchy? := annotation.hierarchy?

@[simp] theorem relabel_residue (f : V ≃ W)
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) :
    (annotation.relabel f).residue index = (annotation.residue index).relabel f := rfl

/-- Relabelling leaves the ordered link list untouched. -/
@[simp] theorem relabel_links (f : V ≃ W)
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount) :
    (annotation.relabel f).links = annotation.links := rfl

/-- Relabelling leaves the naming hierarchy untouched. -/
@[simp] theorem relabel_hierarchy? (f : V ≃ W)
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount) :
    (annotation.relabel f).hierarchy? = annotation.hierarchy? := rfl

@[simp] theorem relabel_hierarchyParent? (f : V ≃ W)
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) :
    (annotation.relabel f).hierarchyParent? index = annotation.hierarchyParent? index := rfl

@[simp] theorem relabel_hierarchyRank? (f : V ≃ W)
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) :
    (annotation.relabel f).hierarchyRank? index = annotation.hierarchyRank? index := rfl

/-- Relabelling composes along equivalence composition. -/
theorem relabel_trans (f : V ≃ W) (g : W ≃ U)
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount) :
    (annotation.relabel f).relabel g = annotation.relabel (f.trans g) := by
  apply ResidueLedgerAnnotation.ext
  · funext index
    exact FragmentAnnotation.relabel_trans f g (annotation.residue index)
  · rfl
  · rfl

/-- Relabelling by the identity equivalence is the identity. -/
@[simp] theorem relabel_refl (annotation : ResidueLedgerAnnotation V residueCount interactionCount) :
    annotation.relabel (Equiv.refl V) = annotation := by
  apply ResidueLedgerAnnotation.ext
  · funext index
    exact FragmentAnnotation.relabel_refl (annotation.residue index)
  · rfl
  · rfl

/-- Relabelling by an equivalence and then by its inverse is the identity. -/
theorem relabel_relabel_symm (f : V ≃ W)
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount) :
    (annotation.relabel f).relabel f.symm = annotation := by
  rw [relabel_trans f f.symm]
  rw [show f.trans f.symm = Equiv.refl V from by ext atom; simp]
  exact relabel_refl annotation

/-- Relabelling by an inverse and then by the equivalence is the identity. -/
theorem relabel_symm_relabel (f : V ≃ W)
    (annotation : ResidueLedgerAnnotation W residueCount interactionCount) :
    (annotation.relabel f.symm).relabel f = annotation := by
  rw [relabel_trans f.symm f]
  rw [show f.symm.trans f = Equiv.refl W from by ext atom; simp]
  exact relabel_refl annotation

/-- Relabelling by an equivalence is injective: no original atom reference can be hidden in the
encoded annotation. -/
theorem relabel_injective (f : V ≃ W) :
    Function.Injective
      (fun annotation : ResidueLedgerAnnotation V residueCount interactionCount =>
        annotation.relabel f) := by
  intro first second equality
  have injective := congrArg
    (fun annotation : ResidueLedgerAnnotation W residueCount interactionCount =>
      annotation.relabel f.symm) equality
  simpa [relabel_relabel_symm] using injective

/-- The ordered source-data list attached to one residue scope.  Source data are carried by each
residue's existing `FragmentAnnotation`, alongside (never instead of) its support and bindings. -/
def sourceData (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) : List (FragmentSourceDatum V) :=
  (annotation.residue index).sourceData

@[simp] theorem sourceData_eq (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) :
    annotation.sourceData index = (annotation.residue index).sourceData := rfl

/-- Relabelling carries each residue's ordered source data with the same atom equivalence. -/
@[simp] theorem relabel_sourceData (f : V ≃ W)
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount)
    (index : Fin residueCount) :
    (annotation.relabel f).sourceData index =
      (annotation.sourceData index).map (FragmentSourceDatum.relabel f) := rfl

end ResidueLedgerAnnotation

/-! ## Construction from a real ledger

The atom equivalence `V ≃ Fin atomCount` and the finite locant cover are external inputs.  The
residue fragments are encoded with the existing typed fragment channel; links are encoded by
`encodeLink`; the naming hierarchy is copied verbatim. -/

/-- Encode a real ledger into the atom-independent annotation channel, relative to an external
atom equivalence and a finite locant cover. -/
def encode {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) :
    ResidueLedgerAnnotation V ledger.residueCount
      input.input.molecule.interactions.length where
  residue index := encodeFragment codec e (ledger.residue index) (cover index)
  links := ledger.links.map (encodeLink codec)
  hierarchy? := ledger.hierarchy?

@[simp] theorem encode_residue {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) (index : Fin ledger.residueCount) :
    (encode codec e ledger cover).residue index =
      encodeFragment codec e (ledger.residue index) (cover index) := rfl

@[simp] theorem encode_links {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) :
    (encode codec e ledger cover).links = ledger.links.map (encodeLink codec) := rfl

/-- The naming hierarchy is retained verbatim, independently of the link list. -/
@[simp] theorem encode_hierarchy? {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) :
    (encode codec e ledger cover).hierarchy? = ledger.hierarchy? := rfl

@[simp] theorem encode_residueTotal {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) :
    (encode codec e ledger cover).residueTotal = ledger.residueCount := rfl

/-- The annotation's interaction budget is exactly the actual source interaction-list length. -/
@[simp] theorem encode_interactionTotal {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) :
    (encode codec e ledger cover).interactionTotal =
      input.input.molecule.interactions.length := rfl

/-- The constructor guarded by a finite locant cover. -/
def encodeOfCover {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger) :
    ResidueLedgerAnnotation V ledger.residueCount
      input.input.molecule.interactions.length :=
  encode codec e ledger cover.cover

@[simp] theorem encodeOfCover_links {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger) :
    (encodeOfCover codec e ledger cover).links = ledger.links.map (encodeLink codec) := rfl

/-! ## Source-bound locant anchors and source-data attachment

A leaf that attaches specialist source data must resolve every printed source locant through the
actual ledger incidence, not through a free-form number.  `resolveAnchor?` performs that resolution
against the real `ResidueFragment.incidence` and the external atom equivalence
`V ≃ Fin atomCount`; its membership theorem is the certificate that discharges the fragment
source-data support invariant.  `resolveBondAnchors?` does the same for an ordered pair of locants,
which is the anchor form of a double-bond datum.

`encodeWithSourceData` is the resulting exact constructor: plain `encode` plus caller-supplied
ordered source data attached to the encoded residue annotations.  Supports, locant bindings, links
and the naming hierarchy are exactly those of `encode`. -/

/-- Resolve one residue-scoped source locant through the actual ledger incidence and the external
atom equivalence.  `none` means the locant does not resolve; no anchor is manufactured from a
number that is not an actual ledger entry. -/
def resolveAnchor? {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (index : Fin ledger.residueCount)
    (locant : Locant) : Option V :=
  ((ledger.residue index).locate? locant).map e.symm

/-- A resolved locant anchor belongs to the encoded residue support.  This is exactly the
certificate needed for `FragmentAnnotation.sourceData_supported`. -/
theorem resolveAnchor?_mem_support {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (index : Fin ledger.residueCount)
    (locant : Locant) {anchor : V}
    (found : resolveAnchor? e ledger index locant = some anchor) :
    anchor ∈ (ledger.residue index).support.map e.symm.toEmbedding := by
  unfold resolveAnchor? at found
  cases resolveEq : (ledger.residue index).locate? locant with
  | none =>
      rw [resolveEq] at found
      simp at found
  | some atom =>
      rw [resolveEq] at found
      simp only [Option.map_some, Option.some.injEq] at found
      rw [← found]
      exact Finset.mem_map.mpr
        ⟨atom, (ledger.residue index).locate?_mem_support resolveEq, rfl⟩

/-- Resolve an ordered pair of residue-scoped locants to ordered bond anchors through the actual
ledger incidence.  The result is `some` only when both locants resolve; the order
`(source, target)` is retained. -/
def resolveBondAnchors? {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (index : Fin ledger.residueCount)
    (sourceLocant targetLocant : Locant) : Option (V × V) :=
  match resolveAnchor? e ledger index sourceLocant,
      resolveAnchor? e ledger index targetLocant with
  | some source, some target => some (source, target)
  | _, _ => none

/-- Both anchors of a resolved ordered bond pair belong to the encoded residue support. -/
theorem resolveBondAnchors?_mem_support {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (index : Fin ledger.residueCount)
    (sourceLocant targetLocant : Locant) {source target : V}
    (found : resolveBondAnchors? e ledger index sourceLocant targetLocant = some (source, target)) :
    source ∈ (ledger.residue index).support.map e.symm.toEmbedding ∧
      target ∈ (ledger.residue index).support.map e.symm.toEmbedding := by
  unfold resolveBondAnchors? at found
  cases sourceEq : resolveAnchor? e ledger index sourceLocant with
  | none =>
      rw [sourceEq] at found
      simp at found
  | some sourceAnchor =>
      cases targetEq : resolveAnchor? e ledger index targetLocant with
      | none =>
          rw [sourceEq, targetEq] at found
          simp at found
      | some targetAnchor =>
          rw [sourceEq, targetEq] at found
          simp only [Option.some.injEq, Prod.mk.injEq] at found
          obtain ⟨rfl, rfl⟩ := found
          exact ⟨resolveAnchor?_mem_support e ledger index sourceLocant sourceEq,
            resolveAnchor?_mem_support e ledger index targetLocant targetEq⟩

/-- Encode a real ledger with caller-supplied ordered source data attached to every residue scope.

The source data are appended alongside each encoded residue annotation by
`FragmentAnnotation.withSourceData`; no physical field, link or hierarchy is changed.  The
`supported` premise is the anchor-membership invariant stated against the encoded support
`(ledger.residue index).support.map e.symm.toEmbedding`, which is exactly the support of the
encoded fragment. -/
def encodeWithSourceData {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : ∀ index, ∀ datum ∈ sourceData index, ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding) :
    ResidueLedgerAnnotation V ledger.residueCount
      input.input.molecule.interactions.length where
  residue index :=
    (encodeFragment codec e (ledger.residue index) (cover index)).withSourceData
      (sourceData index) (supported index)
  links := ledger.links.map (encodeLink codec)
  hierarchy? := ledger.hierarchy?

@[simp] theorem encodeWithSourceData_residue {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : ∀ index, ∀ datum ∈ sourceData index, ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding)
    (index : Fin ledger.residueCount) :
    (encodeWithSourceData codec e ledger cover sourceData supported).residue index =
      (encodeFragment codec e (ledger.residue index) (cover index)).withSourceData
        (sourceData index) (supported index) := rfl

/-- Exact recovery of the attached source data: the encoded residue's ordered source-data list is
exactly the caller-supplied list, in the same order. -/
@[simp] theorem encodeWithSourceData_residue_sourceData {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : ∀ index, ∀ datum ∈ sourceData index, ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding)
    (index : Fin ledger.residueCount) :
    ((encodeWithSourceData codec e ledger cover sourceData supported).residue index).sourceData =
      sourceData index := by
  rw [encodeWithSourceData_residue]
  simp [FragmentAnnotation.withSourceData]

@[simp] theorem encodeWithSourceData_links {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : ∀ index, ∀ datum ∈ sourceData index, ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding) :
    (encodeWithSourceData codec e ledger cover sourceData supported).links =
      ledger.links.map (encodeLink codec) := rfl

@[simp] theorem encodeWithSourceData_hierarchy? {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : ∀ index, ∀ datum ∈ sourceData index, ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding) :
    (encodeWithSourceData codec e ledger cover sourceData supported).hierarchy? =
      ledger.hierarchy? := rfl

/-- Backwards compatibility: with empty source data the new constructor is exactly the existing
`encode`. -/
theorem encodeWithSourceData_nil {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) :
    encodeWithSourceData codec e ledger cover (fun _ => [])
        (by
          intro index datum member
          exact absurd member (by simp)) =
      encode codec e ledger cover := by
  apply ResidueLedgerAnnotation.ext
  · funext index
    apply FragmentAnnotation.ext
    · rfl
    · rfl
    · simp [encodeWithSourceData, encode, FragmentAnnotation.withSourceData]
  · rfl
  · rfl

/-- Cover-guarded form of `encodeWithSourceData`. -/
def encodeOfCoverWithSourceData {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : ∀ index, ∀ datum ∈ sourceData index, ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding) :
    ResidueLedgerAnnotation V ledger.residueCount
      input.input.molecule.interactions.length :=
  encodeWithSourceData codec e ledger cover.cover sourceData supported

/-- The cover-guarded constructor retains the attached source data exactly. -/
@[simp] theorem encodeOfCoverWithSourceData_residue_sourceData {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : ∀ index, ∀ datum ∈ sourceData index, ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding)
    (index : Fin ledger.residueCount) :
    ((encodeOfCoverWithSourceData codec e ledger cover sourceData supported).residue
      index).sourceData = sourceData index :=
  encodeWithSourceData_residue_sourceData codec e ledger cover.cover sourceData supported index

/-! ### Retention of order, multiplicity and occurrence bounds -/

/-- Positional exactness: the encoded link list is the image of the source link list in the same
order, so order and every positional multiplicity are retained. -/
theorem encode_links_getElem? {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) (index : ℕ) :
    (encode codec e ledger cover).links[index]? =
      (ledger.links[index]?).map (encodeLink codec) := by
  simp [encode]

/-- A source link occurs in the encoded list exactly when its encoding does. -/
theorem encodeLink_mem_iff {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (link : DirectedResidueLink Locant (Fin ledger.residueCount)
      input.input.molecule.interactions.length) :
    encodeLink codec link ∈ (encode codec e ledger cover).links ↔ link ∈ ledger.links := by
  rw [encode_links]
  constructor
  · intro member
    obtain ⟨other, otherMember, equality⟩ := List.mem_map.mp member
    rw [encodeLink_injective codec equality] at otherMember
    exact otherMember
  · intro member
    exact List.mem_map.mpr ⟨link, member, rfl⟩

/-- Every occurrence index stored in an encoded annotation is bounded by the actual source
interaction count. -/
theorem encode_occurrence_bound {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    {link : AnnotatedResidueLink ledger.residueCount
      input.input.molecule.interactions.length}
    (_member : link ∈ (encode codec e ledger cover).links) :
    link.interaction.val < input.input.molecule.interactions.length :=
  link.interaction.isLt

/-- An encoded link's occurrence index is exactly the source link's interaction index. -/
@[simp] theorem encodeLink_interactionIndex {Locant : Type*} (codec : LocantCodec Locant)
    {residueCount interactionCount : ℕ}
    (link : DirectedResidueLink Locant (Fin residueCount) interactionCount) :
    (encodeLink codec link).interactionIndex = link.interaction.val := rfl

/-! ### Supports, overlap and cycles -/

/-- The encoded support of a residue is the source support moved along the external atom
equivalence. -/
@[simp] theorem encode_residue_support {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) (index : Fin ledger.residueCount) :
    ((encode codec e ledger cover).residue index).support =
      (ledger.residue index).support.map e.symm.toEmbedding := rfl

/-- Overlapping residue supports are retained and reflected exactly.  Overlap is neither required
nor forbidden by the ledger or by the annotation. -/
theorem encode_support_inter_nonempty_iff {Locant V : Type*} [DecidableEq V]
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (first second : Fin ledger.residueCount) :
    (((encode codec e ledger cover).residue first).support ∩
        ((encode codec e ledger cover).residue second).support).Nonempty ↔
      ((ledger.residue first).support ∩ (ledger.residue second).support).Nonempty := by
  constructor
  · rintro ⟨atom, member⟩
    rw [Finset.mem_inter] at member
    obtain ⟨firstAtom, firstMember, rfl⟩ := Finset.mem_map.mp member.1
    obtain ⟨secondAtom, secondMember, secondEq⟩ := Finset.mem_map.mp member.2
    have atomsEqual : secondAtom = firstAtom := e.symm.injective secondEq
    exact ⟨firstAtom, Finset.mem_inter.mpr ⟨firstMember, atomsEqual ▸ secondMember⟩⟩
  · rintro ⟨atom, member⟩
    rw [Finset.mem_inter] at member
    exact ⟨e.symm atom,
      Finset.mem_inter.mpr
        ⟨Finset.mem_map.mpr ⟨atom, member.1, rfl⟩,
          Finset.mem_map.mpr ⟨atom, member.2, rfl⟩⟩⟩

/-- A directed two-cycle in a list of real residue links. -/
def LinkTwoCycle {Locant : Type*} {residueCount interactionCount : ℕ}
    (links : List (DirectedResidueLink Locant (Fin residueCount) interactionCount)) : Prop :=
  ∃ first ∈ links, ∃ second ∈ links,
    first.source = second.target ∧ first.target = second.source

/-- A directed two-cycle in a list of annotated links. -/
def AnnotatedLinkTwoCycle {residueCount interactionCount : ℕ}
    (links : List (AnnotatedResidueLink residueCount interactionCount)) : Prop :=
  ∃ first ∈ links, ∃ second ∈ links,
    first.source = second.target ∧ first.target = second.source

/-- Link cycles are retained and reflected exactly.  The encoding never linearises, deduplicates
or acyclic-ises the linkage list. -/
theorem encodeLink_twoCycle_iff {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) :
    AnnotatedLinkTwoCycle (encode codec e ledger cover).links ↔ LinkTwoCycle ledger.links := by
  unfold AnnotatedLinkTwoCycle LinkTwoCycle
  rw [encode_links]
  constructor
  · rintro ⟨first, firstMember, second, secondMember, sourceEq, targetEq⟩
    obtain ⟨rawFirst, rawFirstMember, rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨rawSecond, rawSecondMember, rfl⟩ := List.mem_map.mp secondMember
    exact ⟨rawFirst, rawFirstMember, rawSecond, rawSecondMember, sourceEq, targetEq⟩
  · rintro ⟨first, firstMember, second, secondMember, sourceEq, targetEq⟩
    exact ⟨encodeLink codec first, List.mem_map.mpr ⟨first, firstMember, rfl⟩,
      encodeLink codec second, List.mem_map.mpr ⟨second, secondMember, rfl⟩,
      sourceEq, targetEq⟩

/-! ### Parent-versus-connectivity distinction -/

/-- Replace the optional naming hierarchy of a real ledger, leaving residues, supports, links and
all source-bound proofs untouched.  This makes the independence of nomenclature parentage from
directed connectivity explicit at the ledger level. -/
def withNamingHierarchy {Locant : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Locant input)
    (hierarchy : Option (ResidueParentHierarchy ledger.residueCount)) :
    ResidueIncidenceLedger Locant input :=
  { ledger with hierarchy? := hierarchy }

@[simp] theorem withNamingHierarchy_links {Locant : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Locant input)
    (hierarchy : Option (ResidueParentHierarchy ledger.residueCount)) :
    (withNamingHierarchy ledger hierarchy).links = ledger.links := rfl

@[simp] theorem withNamingHierarchy_hierarchy? {Locant : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Locant input)
    (hierarchy : Option (ResidueParentHierarchy ledger.residueCount)) :
    (withNamingHierarchy ledger hierarchy).hierarchy? = hierarchy := rfl

/-- Changing only the naming hierarchy does not change the encoded link list. -/
theorem encode_withNamingHierarchy_links {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (hierarchy : Option (ResidueParentHierarchy ledger.residueCount)) :
    (encode codec e (withNamingHierarchy ledger hierarchy) cover).links =
      (encode codec e ledger cover).links := rfl

/-- Changing only the naming hierarchy does not change the encoded residues. -/
theorem encode_withNamingHierarchy_residue {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (hierarchy : Option (ResidueParentHierarchy ledger.residueCount))
    (index : Fin ledger.residueCount) :
    (encode codec e (withNamingHierarchy ledger hierarchy) cover).residue index =
      (encode codec e ledger cover).residue index := rfl

/-- Changing only the naming hierarchy changes only the encoded hierarchy field. -/
@[simp] theorem encode_withNamingHierarchy_hierarchy? {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (hierarchy : Option (ResidueParentHierarchy ledger.residueCount)) :
    (encode codec e (withNamingHierarchy ledger hierarchy) cover).hierarchy? = hierarchy := rfl

/-! ### Compatibility of encoding with atom relabelling -/

/-- Encoding commutes with atom relabelling: relabelling the encoded annotation is the same as
encoding with the correspondingly adjusted external atom equivalence. -/
theorem encodeFragment_relabel {Locant V W : Type*} (codec : LocantCodec Locant) {n : ℕ}
    (e : V ≃ Fin n) (fragment : ResidueFragment Locant n) (cover : List Locant)
    (f : V ≃ W) :
    (encodeFragment codec e fragment cover).relabel f =
      encodeFragment codec (f.symm.trans e) fragment cover := by
  apply FragmentAnnotation.ext
  · simp only [FragmentAnnotation.relabel_support, encodeFragment_support, Finset.map_map]
    rw [show (f.symm.trans e).symm.toEmbedding =
        e.symm.toEmbedding.trans f.toEmbedding from by
      ext atom
      simp]
  · rw [FragmentAnnotation.relabel_bindings, encodeFragment_bindings, encodeFragment_bindings]
    rw [List.map_map]
    apply List.map_congr_left
    intro locant _
    apply Prod.ext
    · rfl
    · simp only [Function.comp_apply, Option.map_map]
      congr 1
  · simp

/-- Annotation-level compatibility of encoding and atom relabelling. -/
theorem relabel_encode {Locant V W : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) (f : V ≃ W) :
    (encode codec e ledger cover).relabel f =
      encode codec (f.symm.trans e) ledger cover := by
  apply ResidueLedgerAnnotation.ext
  · funext index
    simp only [ResidueLedgerAnnotation.relabel_residue, encode_residue]
    exact encodeFragment_relabel codec e (ledger.residue index) (cover index) f
  · rfl
  · rfl

/-! ## Observable content and decoding

`ResidueLedgerView` is the non-proof content of a `ResidueIncidenceLedger`.  A view is *not* a
ledger: it contains no source-bound participant certificates.  Decoding below reconstructs a view
from an annotation alone; the original ledger occurs only in the specification theorem. -/

/-- The observable (non-proof) content of a residue incidence ledger. -/
structure ResidueLedgerView (Locant : Type*) (atomCount interactionCount residueCount : ℕ) where
  residue : Fin residueCount → ResidueFragment Locant atomCount
  links : List (DirectedResidueLink Locant (Fin residueCount) interactionCount)
  hierarchy? : Option (ResidueParentHierarchy residueCount) := none

namespace ResidueLedgerView

variable {Locant : Type*} {atomCount interactionCount residueCount : ℕ}

/-- Structure extensionality. -/
@[ext] theorem ext {first second : ResidueLedgerView Locant atomCount interactionCount residueCount}
    (residue : first.residue = second.residue) (links : first.links = second.links)
    (hierarchy? : first.hierarchy? = second.hierarchy?) : first = second := by
  cases first
  cases second
  simp_all

end ResidueLedgerView

/-- The observable content of a real ledger: residue fragments, ordered links and the optional
naming hierarchy.  The source-bound certificate fields are deliberately not included. -/
def viewOfLedger {Locant : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Locant input) :
    ResidueLedgerView Locant input.input.molecule.atomCount
      input.input.molecule.interactions.length ledger.residueCount where
  residue := ledger.residue
  links := ledger.links
  hierarchy? := ledger.hierarchy?

@[simp] theorem viewOfLedger_residue {Locant : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Locant input) (index : Fin ledger.residueCount) :
    (viewOfLedger ledger).residue index = ledger.residue index := rfl

@[simp] theorem viewOfLedger_links {Locant : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Locant input) :
    (viewOfLedger ledger).links = ledger.links := rfl

@[simp] theorem viewOfLedger_hierarchy? {Locant : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Locant input) :
    (viewOfLedger ledger).hierarchy? = ledger.hierarchy? := rfl

/-- Decode an ordered annotated link list.  The result is `none` if decoding either locant of any
link returns `none`; no link is silently dropped. -/
def decodeLinks? {Locant : Type*} (codec : LocantCodec Locant)
    {residueCount interactionCount : ℕ} :
    List (AnnotatedResidueLink residueCount interactionCount) →
      Option (List (DirectedResidueLink Locant (Fin residueCount) interactionCount))
  | [] => some []
  | link :: rest =>
      (decodeLink? codec link).bind fun decoded =>
        (decodeLinks? codec rest).bind fun decodedRest =>
          some (decoded :: decodedRest)

/-- Exact ordered-list round trip for links. -/
@[simp] theorem decodeLinks?_map_encode {Locant : Type*} (codec : LocantCodec Locant)
    {residueCount interactionCount : ℕ}
    (links : List (DirectedResidueLink Locant (Fin residueCount) interactionCount)) :
    decodeLinks? codec (links.map (encodeLink codec)) = some links := by
  induction links with
  | nil => rfl
  | cons head tail hypothesis =>
      rw [List.map_cons]
      simp [decodeLinks?, decodeLink?_encode, hypothesis]

/-- Decode an annotation into its observable ledger view, given the external atom equivalence and
locant codec.  Residues are decoded with the existing typed fragment channel; links are decoded
with `decodeLinks?`; the naming hierarchy is copied verbatim. -/
def decodeView? {Locant V : Type*} {atomCount interactionCount residueCount : ℕ}
    (codec : LocantCodec Locant) (e : V ≃ Fin atomCount)
    (annotation : ResidueLedgerAnnotation V residueCount interactionCount) :
    Option (ResidueLedgerView Locant atomCount interactionCount residueCount) :=
  (decodeLinks? codec annotation.links).bind fun links =>
    some
      { residue := fun index => decodeFragment codec e (annotation.residue index)
        links := links
        hierarchy? := annotation.hierarchy? }

/-- Observable recovery: decoding the encoding of a real ledger returns exactly the ledger's
observable content.  The hypotheses are only the finite-cover facts for the existing fragment
codec; the original ledger is not a payload of the annotation or of the decoder. -/
theorem decodeView?_encode {Locant V : Type*} {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (coverNodup : ∀ index, (cover index).Nodup)
    (covers : ∀ (index : Fin ledger.residueCount) (locant : Locant)
      (atom : Fin input.input.molecule.atomCount),
        (ledger.residue index).incidence locant = some atom → locant ∈ cover index) :
    decodeView? codec e (encode codec e ledger cover) = some (viewOfLedger ledger) := by
  unfold decodeView? encode
  rw [decodeLinks?_map_encode]
  simp only [Option.bind_some]
  rw [Option.some.injEq]
  apply ResidueLedgerView.ext
  · funext index
    exact decodeFragment_encodeFragment codec e (ledger.residue index) (cover index)
      (coverNodup index) (covers index)
  · rfl
  · rfl

/-- Attached source data are metadata: decoding the source-data-augmented encoding returns exactly
the original ledger's observable content.  In particular, the canonical fragment/link recovery is
unaffected by source-data attachment. -/
theorem decodeView?_encodeWithSourceData {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : ∀ index, ∀ datum ∈ sourceData index, ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding)
    (coverNodup : ∀ index, (cover index).Nodup)
    (covers : ∀ (index : Fin ledger.residueCount) (locant : Locant)
      (atom : Fin input.input.molecule.atomCount),
        (ledger.residue index).incidence locant = some atom → locant ∈ cover index) :
    decodeView? codec e (encodeWithSourceData codec e ledger cover sourceData supported) =
      some (viewOfLedger ledger) := by
  unfold decodeView? encodeWithSourceData
  rw [decodeLinks?_map_encode]
  simp only [Option.bind_some]
  rw [Option.some.injEq]
  apply ResidueLedgerView.ext
  · funext index
    simp only [decodeFragment_withSourceData]
    exact decodeFragment_encodeFragment codec e (ledger.residue index) (cover index)
      (coverNodup index) (covers index)
  · rfl
  · rfl

/-- The cover-guarded form of `decodeView?_encode`. -/
theorem decodeView?_encodeOfCover {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger) :
    decodeView? codec e (encodeOfCover codec e ledger cover) = some (viewOfLedger ledger) :=
  decodeView?_encode codec e ledger cover.cover cover.nodup cover.covers

/-- The cover-guarded form of `decodeView?_encodeWithSourceData`. -/
theorem decodeView?_encodeOfCoverWithSourceData {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger)
    (sourceData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (supported : ∀ index, ∀ datum ∈ sourceData index, ∀ atom ∈ datum.atomReferences,
      atom ∈ (ledger.residue index).support.map e.symm.toEmbedding) :
    decodeView? codec e (encodeOfCoverWithSourceData codec e ledger cover sourceData supported) =
      some (viewOfLedger ledger) :=
  decodeView?_encodeWithSourceData codec e ledger cover.cover sourceData supported
    cover.nodup cover.covers

/-! ### Individual observable recoveries -/

/-- Recovered residue supports are exactly the source supports. -/
theorem decodeView?_encodeOfCover_support {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger)
    (index : Fin ledger.residueCount) :
    (decodeView? codec e (encodeOfCover codec e ledger cover)).map
        (fun view => (view.residue index).support) =
      some ((ledger.residue index).support) := by
  rw [decodeView?_encodeOfCover codec e ledger cover]
  rfl

/-- Recovered scoped locant incidence is exactly the source incidence at every locant. -/
theorem decodeView?_encodeOfCover_incidence {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger)
    (index : Fin ledger.residueCount) (locant : Locant) :
    (decodeView? codec e (encodeOfCover codec e ledger cover)).map
        (fun view => (view.residue index).incidence locant) =
      some ((ledger.residue index).incidence locant) := by
  rw [decodeView?_encodeOfCover codec e ledger cover]
  rfl

/-- Recovered links are exactly the source links, in the same order (hence with the same
multiplicities and cycles). -/
theorem decodeView?_encodeOfCover_links {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger) :
    (decodeView? codec e (encodeOfCover codec e ledger cover)).map
        (fun view => view.links) = some ledger.links := by
  rw [decodeView?_encodeOfCover codec e ledger cover]
  rfl

/-- The optional naming hierarchy (parents and ranks) is recovered exactly. -/
theorem decodeView?_encodeOfCover_hierarchy? {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input) (cover : LocantCover ledger) :
    (decodeView? codec e (encodeOfCover codec e ledger cover)).map
        (fun view => view.hierarchy?) = some ledger.hierarchy? := by
  rw [decodeView?_encodeOfCover codec e ledger cover]
  rfl

/-- Relabelling atoms before decoding is invisible: the same observable view is recovered. -/
theorem decodeView?_relabel_encode {Locant V W : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (coverNodup : ∀ index, (cover index).Nodup)
    (covers : ∀ (index : Fin ledger.residueCount) (locant : Locant)
      (atom : Fin input.input.molecule.atomCount),
        (ledger.residue index).incidence locant = some atom → locant ∈ cover index)
    (f : V ≃ W) :
    decodeView? codec (f.symm.trans e) ((encode codec e ledger cover).relabel f) =
      some (viewOfLedger ledger) := by
  rw [relabel_encode]
  exact decodeView?_encode codec (f.symm.trans e) ledger cover coverNodup covers

/-! ## Reconstructing the dependent certificate

A view knows the source atom count and interaction count but has no participant certificates.  The
following constructor is therefore the exact interface at which the two remaining source facts are
supplied.  They are the only data not carried by an atom-independent annotation: `Decidable`
membership in `interactions.get link.interaction |>.participants` is a proposition about the
certified source input, and the annotation deliberately stores no source indices.
-/

/-- Reconstruct the full dependent `ResidueIncidenceLedger` from a view of the actual source
counts, given the two participant certificates for every link.  Nothing else is needed; the
naming hierarchy is carried by the view. -/
def viewToLedger {Locant : Type*} {input : CertifiedAuthoritativeChemicalInput}
    {residueCount : ℕ}
    (view : ResidueLedgerView Locant input.input.molecule.atomCount
      input.input.molecule.interactions.length residueCount)
    (link_source_mem : ∀ link ∈ view.links,
      ∃ atom : Fin input.input.molecule.atomCount,
        (view.residue link.source).incidence link.sourceLocant = some atom ∧
          atom.val ∈ (input.input.molecule.interactions.get link.interaction).participants)
    (link_target_mem : ∀ link ∈ view.links,
      ∃ atom : Fin input.input.molecule.atomCount,
        (view.residue link.target).incidence link.targetLocant = some atom ∧
          atom.val ∈ (input.input.molecule.interactions.get link.interaction).participants) :
    ResidueIncidenceLedger Locant input where
  residueCount := residueCount
  residue := view.residue
  links := view.links
  link_source_mem := link_source_mem
  link_target_mem := link_target_mem
  hierarchy? := view.hierarchy?

/-- The reconstruction interface is exact: feeding a ledger's own participant certificates with
its view returns that ledger.  No information is lost or invented by the view round trip. -/
@[simp] theorem viewToLedger_viewOfLedger {Locant : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Locant input) :
    viewToLedger (viewOfLedger ledger) ledger.link_source_mem ledger.link_target_mem = ledger := by
  cases ledger
  rfl

end TetraStereo.OneCenter
