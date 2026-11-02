import TetraStereo.OneCenter.OrganicStereoSharedPhysicalCaseIngress

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace TetraStereo.OneCenter
namespace OrganicStereoVaryingPhysicalRequestAssembly

open OrganicStereoSharedPhysicalCaseIngress

noncomputable section

universe u v

variable {V E B : Type u} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
variable {Locant : Type v}

/-!
# Varying-base physical request assembly

The fixed-base shared case ingress (`OrganicStereoSharedPhysicalCaseIngress`) packs a
`SharedCaseRequest Locant base` against one fixed ingress substrate `base`.  This module removes
that fixed base from the *type* of the request: a source request is a genuine dependent pair

```
structure VaryingRequest (Locant) where
  base : WholeState V E B
  request : SharedCaseRequest Locant base
```

so the graph, inventory, conformation, enumeration and the whole independently supplied case
collection may vary from request to request.

The packed output stores only the actual assembled state, the single enumeration, the ordered
interleaving tags, the proof-carrying certificate sidecar and the minimal residue metadata.  It
stores no original base, no raw request, no duplicated raw case list and no copied residue ledger.
The sidecar and the residue metadata are indexed by the *output* context

```
SharedPhysicalContext.ofState (SharedCaseRequest.clearIngressChannels state) enumeration
```

and by the state's own extracted case channels and residue-channel option.  In particular the
context index is derived from the output state, not from the supplied base; the base is recovered
only by clearing the ingress channels of the output.

The decoder reconstructs the source request against the recovered base
`SharedCaseRequest.clearIngressChannels state`.  Because clearing leaves no prior case metadata and
no residue ledger, the recovered base carries its empty-channel facts definitionally, so decoding
needs no hypotheses.  It decodes the sidecar against the recovered context, and rebuilds the
optional residue ingress from the state's own residue channel by `decodeView?` plus the packed
proof-only validity and cover metadata (the `PackedResidue.toIngress` API of the fixed module).

The main results are:

* `VaryingRequest.decode_pack : (pack r).decode = r` for every full request over an arbitrary base;
* `VaryingRequest.pack_injective`;
* `VaryingRequest.decode_image_pack_image : decode '' (pack '' S) = S` for every set of full
  requests, i.e. arbitrary correlated collections of request/base pairs, and
  `VaryingRequest.pack_set_image_inverse` for the preimage form.

All conditional physical and source-validity content stays inside the `PhysicalCase` records and
the `ResidueIngress` of the request; nothing here assumes an inverse or an untransported equality.
-/

/-- The context equality induced by an equality of whole states, at a fixed enumeration.  Only the
physical fields (graph, inventory, conformation) and the enumeration enter a
`SharedPhysicalContext`, and `clearIngressChannels` preserves all of them definitionally.  This is a
transparent `def` so that it reduces to `rfl` when the underlying state equality is `rfl`. -/
def contextEq {base base' : WholeState V E B} (h : base = base')
    (enumeration : V ≃ Fin (Fintype.card V)) :
    SharedPhysicalContext.ofState base enumeration =
      SharedPhysicalContext.ofState base' enumeration := by
  cases h
  rfl

/-- Transporting a channel sidecar along a context equality and then decoding commutes with
transporting the decoded ordered case list.  The certificate payloads are read from the channels;
transporting the context only re-indexes them. -/
theorem ChannelSidecar.decode_cast {ctx ctx' : SharedPhysicalContext V}
    {frames : List (FrameAnnotation V)} {cages : List (NumberedCageAnnotation V)}
    {fragments : List (FragmentAnnotation V)} {conventions : ConventionChannel V}
    {tags : List CaseShape} (h : ctx = ctx')
    (sidecar : ChannelSidecar ctx frames cages fragments conventions tags) :
    (h ▸ sidecar).decode = h ▸ sidecar.decode := by
  cases h
  rfl

/-! ## The recovered-base projections of a state

All of these are definitional: `clearIngressChannels` is exactly the record update that erases the
four case channels and the residue ledger, and it changes nothing else. -/

@[simp] theorem clearIngressChannels_graph (state : WholeState V E B) :
    (SharedCaseRequest.clearIngressChannels state).graph = state.graph := rfl

@[simp] theorem clearIngressChannels_electronic? (state : WholeState V E B) :
    (SharedCaseRequest.clearIngressChannels state).electronic? = state.electronic? := rfl

@[simp] theorem clearIngressChannels_conformation (state : WholeState V E B) :
    (SharedCaseRequest.clearIngressChannels state).conformation = state.conformation := rfl

@[simp] theorem clearIngressChannels_frames (state : WholeState V E B) :
    (SharedCaseRequest.clearIngressChannels state).frames = [] := rfl

@[simp] theorem clearIngressChannels_fragments (state : WholeState V E B) :
    (SharedCaseRequest.clearIngressChannels state).fragments = [] := rfl

@[simp] theorem clearIngressChannels_conventions (state : WholeState V E B) :
    (SharedCaseRequest.clearIngressChannels state).conventions = [] := rfl

@[simp] theorem clearIngressChannels_cages (state : WholeState V E B) :
    (SharedCaseRequest.clearIngressChannels state).cages = [] := rfl

@[simp] theorem clearIngressChannels_residueLedger? (state : WholeState V E B) :
    (SharedCaseRequest.clearIngressChannels state).residueLedger? = none := rfl

/-- The recovered base of an output state supplies no prior case metadata. -/
theorem clearIngressChannels_empty (state : WholeState V E B) :
    CaseChannelsEmpty (SharedCaseRequest.clearIngressChannels state) :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The recovered base of an output state supplies no prior residue ledger. -/
theorem clearIngressChannels_residue_empty (state : WholeState V E B) :
    (SharedCaseRequest.clearIngressChannels state).residueLedger? = none := rfl

/-! ### Residue reconstruction across the recovered-base equality

The decoded request lives at the recovered base `clearIngressChannels state`, whereas the source
request lives at the original base.  The two bases are propositionally equal but not definitionally
equal, so the residue ingredient is compared heterogeneously.  The packed metadata is indexed by
the graph, which *is* preserved definitionally, so only the base parameter of `ResidueIngress` has
to be transported; the graph transport is a proof of a reflexive equation after eliminating the
base equality and therefore contributes nothing. -/

/-- Rebuilding a genuine residue ingress from packed metadata transported to the recovered base
yields an ingress heterogeneously equal to the original.  Eliminating the base equality makes the
graph transport a proof of a reflexive equation, and the result is exactly
`PackedResidueMeta.toIngress?_ofIngress`. -/
theorem toIngress?_ofIngress_heq {base base' : WholeState V E B}
    (h : base = base') (hg : base.graph = base'.graph)
    {enumeration : V ≃ Fin (Fintype.card V)}
    (ingress : ResidueIngress Locant base enumeration) :
    HEq (PackedResidueMeta.toIngress? (base := base') (enumeration := enumeration)
      (hg ▸ (PackedResidueMeta.some (PackedResidue.ofIngress ingress)
        : PackedResidueMeta Locant base.graph enumeration (some ingress.channel))))
      (Option.some ingress) := by
  cases h
  have hgEq : hg = rfl := Subsingleton.elim hg rfl
  rw [hgEq]
  exact heq_of_eq (PackedResidueMeta.toIngress?_ofIngress ingress)

/-- Rebuilding the absent residue ingredient from a `none` node transported to the recovered base
yields `none`.  After eliminating the base equality, the packed metadata is a transport of the
`none` node along the empty-ledger proof, which `PackedResidueMeta.toIngress?_irrel` removes. -/
theorem toIngress?_none_heq {base base' : WholeState V E B}
    (h : base = base') (hg : base.graph = base'.graph)
    {enumeration : V ≃ Fin (Fintype.card V)}
    (hledger : base.residueLedger? = none) :
    HEq (PackedResidueMeta.toIngress? (base := base') (enumeration := enumeration)
      (hg ▸ (hledger.symm ▸ (PackedResidueMeta.none (Locant := Locant)
        (graph := base.graph) (enumeration := enumeration)))))
      (Option.none : Option (ResidueIngress Locant base enumeration)) := by
  cases h
  have hgEq : hg = rfl := Subsingleton.elim hg rfl
  rw [hgEq]
  rw [PackedResidueMeta.toIngress?_irrel (base := base)
    (channelOption₁ := (none : Option (ResidueLedgerChannel V)))
    (channelOption₂ := base.residueLedger?) hledger.symm
    (PackedResidueMeta.none (Locant := Locant) (graph := base.graph)
      (enumeration := enumeration))]
  exact HEq.refl _

/-! ## Full varying-base requests -/

/-- A full source request: a genuine ingress substrate together with an arbitrary shared case
request indexed by that substrate.  The base is an ordinary field, so its contents vary freely
between two full requests of the same type; all conditional physical and source-validity content
lives inside `request`. -/
structure VaryingRequest (V E B : Type u) [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
    (Locant : Type v) where
  /-- The genuine varying ingress substrate. -/
  base : WholeState V E B
  /-- The shared case request indexed by that substrate. -/
  request : SharedCaseRequest Locant base

/-- The packed output of a full varying-base request.  It stores exactly the actual assembled state,
the single enumeration, the ordered interleaving tags, the certificate sidecar and the minimal
residue metadata.  The sidecar is indexed by the state's own extracted case channels and by the
context recovered from the output state; the residue metadata is indexed by the state's own residue
channel and by the recovered context's graph.  No original base, raw request, raw case list or raw
ledger is retained. -/
structure PackedVaryingIngress (V E B : Type u) [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
    (Locant : Type v) where
  /-- The single common enumeration. -/
  enumeration : V ≃ Fin (Fintype.card V)
  /-- The actual assembled whole state. -/
  state : WholeState V E B
  /-- The ordered interleaving tags, one per independently supplied case. -/
  tags : List CaseShape
  /-- The certificate sidecar, indexed by the output state's own case channels and by the context
  recovered from that state. -/
  sidecar : BundleSidecar
    (SharedPhysicalContext.ofState (SharedCaseRequest.clearIngressChannels state) enumeration)
    (CaseBundle.extractCases state) tags
  /-- The residue metadata, indexed by the output state's own residue channel and by the graph of
  the recovered context. -/
  residueMeta : PackedResidueMeta Locant
    (SharedPhysicalContext.ofState (SharedCaseRequest.clearIngressChannels state) enumeration).graph
    enumeration state.residueLedger?

namespace VaryingRequest

variable {base : WholeState V E B}

/-- Pack a full request into its explicit output.  The state is the actual assembly of the request
(cases first, then the optional source-bound residue channel); the sidecar is the certificate tree
built from the collection, indexed by the output state's own channels and by the context recovered
from the output; the residue metadata is the fixed-module packed metadata for the attached channel.

The two branches are written explicitly so that the output indices are computed from the concrete
assembled state of the branch.  `pack_state` records that the resulting state is exactly
`request.assemble`. -/
def pack (r : VaryingRequest V E B Locant) : PackedVaryingIngress V E B Locant :=
  match r.request.residue? with
  | none =>
      { enumeration := r.request.enumeration
        state := assembleCases r.base r.request.cases
        tags := r.request.cases.map PhysicalCase.shape
        sidecar := ChannelSidecar.ofCases r.request.cases
        residueMeta := r.request.residue_empty.symm ▸ PackedResidueMeta.none }
  | some ingress =>
      { enumeration := r.request.enumeration
        state := attachSourceBoundResidueLedger (assembleCases r.base r.request.cases)
          ingress.channel
        tags := r.request.cases.map PhysicalCase.shape
        sidecar := ChannelSidecar.ofCases r.request.cases
        residueMeta := PackedResidueMeta.some (PackedResidue.ofIngress ingress) }

/-- The packed state is exactly the request's actual assembled state. -/
theorem pack_state (r : VaryingRequest V E B Locant) :
    r.pack.state = r.request.assemble := by
  cases r with
  | mk base request =>
    cases request with
    | mk enumeration cases residue? empty residueEmpty =>
      cases residue? <;> rfl

/-- The packed enumeration is the request enumeration. -/
@[simp] theorem pack_enumeration (r : VaryingRequest V E B Locant) :
    r.pack.enumeration = r.request.enumeration := by
  cases r with
  | mk base request =>
    cases request with
    | mk enumeration cases residue? empty residueEmpty =>
      cases residue? <;> rfl

/-- The packed tags are exactly the ordered shape tags of the collection. -/
@[simp] theorem pack_tags (r : VaryingRequest V E B Locant) :
    r.pack.tags = r.request.cases.map PhysicalCase.shape := by
  cases r with
  | mk base request =>
    cases request with
    | mk enumeration cases residue? empty residueEmpty =>
      cases residue? <;> rfl

/-- The packed sidecar is the certificate tree built from the collection.  Its indices are the
output state's channels and the recovered context; the payload (frames, cages, fragments,
conventions) is read back from the state, so no raw case list is stored. -/
theorem pack_sidecar (r : VaryingRequest V E B Locant) :
    HEq r.pack.sidecar (ChannelSidecar.ofCases r.request.cases) := by
  cases r with
  | mk base request =>
    cases request with
    | mk enumeration cases residue? empty residueEmpty =>
      cases residue? <;> exact HEq.refl _

/-- The packed residue metadata for an absent residue ingredient is the `none` node. -/
theorem pack_residueMeta_none (r : VaryingRequest V E B Locant)
    (h : r.request.residue? = none) :
    HEq r.pack.residueMeta
      (PackedResidueMeta.none (Locant := Locant)
        (graph := (SharedPhysicalContext.ofState
          (SharedCaseRequest.clearIngressChannels r.pack.state) r.request.enumeration).graph)
        (enumeration := r.request.enumeration)) := by
  cases r with
  | mk base request =>
    cases request with
    | mk enumeration caseList residue? empty residueEmpty =>
      cases residue? with
      | none =>
          exact eqRec_heq residueEmpty.symm
            (PackedResidueMeta.none (Locant := Locant)
              (graph := (SharedPhysicalContext.ofState
                (SharedCaseRequest.clearIngressChannels (assembleCases base caseList))
                enumeration).graph) (enumeration := enumeration))
      | some ingress => cases h

/-- The packed residue metadata for a present residue ingredient is exactly the `some` node holding
the packed metadata of the attached channel. -/
theorem pack_residueMeta_some (r : VaryingRequest V E B Locant)
    (ingress : ResidueIngress Locant r.base r.request.enumeration)
    (h : r.request.residue? = some ingress) :
    HEq r.pack.residueMeta (PackedResidueMeta.some (PackedResidue.ofIngress ingress)) := by
  cases r with
  | mk base request =>
    cases request with
    | mk enumeration cases residue? empty residueEmpty =>
      cases residue? with
      | none => cases h
      | some actual =>
          have actualEq : actual = ingress := Option.some.inj h
          subst actualEq
          exact HEq.refl _

/-- The packed state preserves the base graph. -/
@[simp] theorem pack_state_graph (r : VaryingRequest V E B Locant) :
    r.pack.state.graph = r.base.graph := by
  rw [pack_state]
  exact SharedCaseRequest.assemble_graph _

/-- The packed state preserves the base inventory. -/
@[simp] theorem pack_state_electronic? (r : VaryingRequest V E B Locant) :
    r.pack.state.electronic? = r.base.electronic? := by
  rw [pack_state]
  exact SharedCaseRequest.assemble_electronic? _

/-- The packed state preserves the base conformation. -/
@[simp] theorem pack_state_conformation (r : VaryingRequest V E B Locant) :
    r.pack.state.conformation = r.base.conformation := by
  rw [pack_state]
  exact SharedCaseRequest.assemble_conformation _

/-- The packed state's case channels are exactly the request's ordered bundle, including duplicate
occurrences and interleaving. -/
@[simp] theorem pack_state_extractCases (r : VaryingRequest V E B Locant) :
    CaseBundle.extractCases r.pack.state = r.request.caseBundle := by
  rw [pack_state]
  exact SharedCaseRequest.assemble_extractedCases _

end VaryingRequest

namespace PackedVaryingIngress

variable {base : WholeState V E B}

/-- View the packed output as a fixed-base packed ingress at the recovered base.  The recovered base
is `clearIngressChannels state`; the sidecar and residue metadata are already indexed by exactly
that base's context and graph, so this is the identity on the stored fields. -/
def toFixed (packed : PackedVaryingIngress V E B Locant) :
    PackedIngress Locant (SharedCaseRequest.clearIngressChannels packed.state) where
  enumeration := packed.enumeration
  state := packed.state
  tags := packed.tags
  sidecar := packed.sidecar
  residueMeta := packed.residueMeta

/-- Decode a packed output back into a full varying-base request.  The base is recovered from the
output state by clearing the ingress channels; the response is built against that recovered base by
the fixed-module decoder, whose empty-channel hypotheses hold definitionally for a cleared state.
The optional residue ingredient is rebuilt from the state's own residue channel via `decodeView?`
and the packed proof-only metadata. -/
noncomputable def decode (packed : PackedVaryingIngress V E B Locant) : VaryingRequest V E B Locant :=
  ⟨SharedCaseRequest.clearIngressChannels packed.state,
   PackedIngress.decode packed.toFixed (clearIngressChannels_empty packed.state)
     (clearIngressChannels_residue_empty packed.state)⟩

/-- Decoding recovers the enumeration from the packed output. -/
@[simp] theorem decode_enumeration (packed : PackedVaryingIngress V E B Locant) :
    packed.decode.request.enumeration = packed.enumeration := rfl

/-- Decoding recovers the base by clearing the output state's ingress channels. -/
@[simp] theorem decode_base (packed : PackedVaryingIngress V E B Locant) :
    packed.decode.base = SharedCaseRequest.clearIngressChannels packed.state := rfl

/-- Decoding reads the cases out of the state-indexed certificate sidecar. -/
@[simp] theorem decode_cases (packed : PackedVaryingIngress V E B Locant) :
    packed.decode.request.cases = packed.sidecar.decode := rfl

/-- Decoding reads the optional residue ingredient from the state channel and the packed metadata. -/
@[simp] theorem decode_residue? (packed : PackedVaryingIngress V E B Locant) :
    packed.decode.request.residue? = packed.toFixed.residueIngress? := rfl

end PackedVaryingIngress

/-! ## Request-level transport lemmas

These compare a decoded request at the recovered base with the source request at the original base.
The equality of bases is kept explicit so that the comparison is proved once, for arbitrary bases,
by eliminating that equality. -/

namespace SharedRequestTransport

variable {base base' : WholeState V E B}

/-- Two shared case requests at propositionally equal bases are heterogeneous-equal as soon as
their enumerations, ordered case lists and optional residue ingredients agree.  The two `Prop`
fields (empty-channel facts and empty-residue fact) are proof-irrelevant and are not compared. -/
theorem heq_of_data (h : base' = base) {first : SharedCaseRequest Locant base}
    {second : SharedCaseRequest Locant base'}
    (henum : second.enumeration = first.enumeration)
    (hcases : HEq second.cases first.cases)
    (hres : HEq second.residue? first.residue?) :
    HEq second first := by
  cases h
  cases first with
  | mk enumeration₁ cases₁ residue₁ empty₁ residueEmpty₁ =>
    cases second with
    | mk enumeration₂ cases₂ residue₂ empty₂ residueEmpty₂ =>
      simp only at henum
      cases henum
      have hcasesEq : cases₂ = cases₁ := eq_of_heq hcases
      have hresEq : residue₂ = residue₁ := eq_of_heq hres
      cases hcasesEq
      cases hresEq
      have hempty : empty₂ = empty₁ := Subsingleton.elim _ _
      have hresEmpty : residueEmpty₂ = residueEmpty₁ := Subsingleton.elim _ _
      cases hempty
      cases hresEmpty
      rfl

end SharedRequestTransport

namespace VaryingRequest

/-- Full-request extensionality along a recovered base equality: if the decoded request is
heterogeneous-equal to the source request and the recovered base is equal to the source base, then
the decoded full request is the source full request. -/
theorem eq_of_heq_request {base base' : WholeState V E B}
    (h : base' = base) {first : SharedCaseRequest Locant base}
    {second : SharedCaseRequest Locant base'} (hreq : HEq second first) :
    (⟨base', second⟩ : VaryingRequest V E B Locant) = ⟨base, first⟩ := by
  cases h
  have hEq : second = first := eq_of_heq hreq
  cases hEq
  rfl

/-! ## The round trip for arbitrary varying bases -/

/-- Decoding a packed full request returns that full request.  The proof splits on the optional
residue ingredient, so the packed state and its recovered context reduce to the concrete assembly
of that branch.  The recovered base is `clearIngressChannels` of the assembled state, which equals
the source base by `clearIngressChannels_assemble` composed with `clearIngressChannels_base`; the
sidecar decodes to the original ordered collection and the residue ingredient is reconstructed from
the state channel by `decodeView?` plus the packed proof-only metadata. -/
theorem decode_pack (r : VaryingRequest V E B Locant) : r.pack.decode = r := by
  cases r with
  | mk base request =>
    cases request with
    | mk enumeration caseList residue? empty residueEmpty =>
      cases residue? with
      | none =>
          have hclear : SharedCaseRequest.clearIngressChannels (assembleCases base caseList) = base := by
            have h₁ := SharedCaseRequest.clearIngressChannels_assemble
              ({ enumeration := enumeration, cases := caseList, residue? := none,
                 empty := empty, residue_empty := residueEmpty } : SharedCaseRequest Locant base)
            have h₂ := SharedCaseRequest.clearIngressChannels_base
              ({ enumeration := enumeration, cases := caseList, residue? := none,
                 empty := empty, residue_empty := residueEmpty } : SharedCaseRequest Locant base)
            simpa [SharedCaseRequest.assemble, SharedCaseRequest.assembleCaseChannels]
              using h₁.trans h₂
          refine VaryingRequest.eq_of_heq_request hclear ?_
          refine SharedRequestTransport.heq_of_data hclear ?_ ?_ ?_
          · rfl
          · dsimp only [PackedIngress.decode, PackedVaryingIngress.toFixed, VaryingRequest.pack]
            rw [ChannelSidecar.decode_ofCases]
          · dsimp only [PackedIngress.decode, PackedVaryingIngress.toFixed, VaryingRequest.pack,
              PackedIngress.residueIngress?]
            exact toIngress?_none_heq (base := base)
              (base' := SharedCaseRequest.clearIngressChannels (assembleCases base caseList))
              hclear.symm rfl (enumeration := enumeration) residueEmpty
      | some ingress =>
          have hclear : SharedCaseRequest.clearIngressChannels
              (attachSourceBoundResidueLedger (assembleCases base caseList) ingress.channel) = base := by
            have h₁ := SharedCaseRequest.clearIngressChannels_assemble
              ({ enumeration := enumeration, cases := caseList, residue? := some ingress,
                 empty := empty, residue_empty := residueEmpty } : SharedCaseRequest Locant base)
            have h₂ := SharedCaseRequest.clearIngressChannels_base
              ({ enumeration := enumeration, cases := caseList, residue? := some ingress,
                 empty := empty, residue_empty := residueEmpty } : SharedCaseRequest Locant base)
            simpa [SharedCaseRequest.assemble, SharedCaseRequest.assembleCaseChannels]
              using h₁.trans h₂
          refine VaryingRequest.eq_of_heq_request hclear ?_
          refine SharedRequestTransport.heq_of_data hclear ?_ ?_ ?_
          · rfl
          · dsimp only [PackedIngress.decode, PackedVaryingIngress.toFixed, VaryingRequest.pack]
            rw [ChannelSidecar.decode_ofCases]
          · dsimp only [PackedIngress.decode, PackedVaryingIngress.toFixed, VaryingRequest.pack,
              PackedIngress.residueIngress?]
            exact toIngress?_ofIngress_heq (base := base)
              (base' := SharedCaseRequest.clearIngressChannels
                (attachSourceBoundResidueLedger (assembleCases base caseList) ingress.channel))
              hclear.symm rfl (enumeration := enumeration) ingress

/-- `encode` is the packaged form of `pack`; decode is its left inverse. -/
abbrev encode (r : VaryingRequest V E B Locant) : PackedVaryingIngress V E B Locant := r.pack

/-- Encoding followed by decoding is the identity on every full request, for an arbitrary varying
base. -/
@[simp] theorem decode_encode (r : VaryingRequest V E B Locant) : r.encode.decode = r :=
  decode_pack r

/-- Decoding and re-assembling a packed full request returns exactly the packed state. -/
theorem decode_assemble (r : VaryingRequest V E B Locant) :
    r.pack.decode.request.assemble = r.pack.state := by
  rw [decode_pack]
  exact r.pack_state.symm

/-- Packing is injective on full varying-base requests: decoding is a left inverse. -/
theorem pack_injective :
    Function.Injective (fun r : VaryingRequest V E B Locant => r.pack) := by
  intro first second same
  have hsame : first.pack = second.pack := same
  have hfirst := decode_pack first
  have hsecond := decode_pack second
  rw [← hfirst, hsame]
  exact hsecond

/-- Arbitrary-set preimage form of the full-request inverse: the requests whose packed output lies
in the image of a set of requests are exactly that set.  This covers arbitrary correlated sets of
request/base pairs. -/
theorem pack_set_image_inverse (requests : Set (VaryingRequest V E B Locant)) :
    (fun r : VaryingRequest V E B Locant => r.pack) ⁻¹'
      ((fun r : VaryingRequest V E B Locant => r.pack) '' requests) = requests := by
  ext request
  constructor
  · rintro ⟨other, hother, same⟩
    have : other = request := pack_injective same
    simpa [this] using hother
  · intro member
    exact ⟨request, member, rfl⟩

/-- Image form: decoding the packed image of a set of full requests returns exactly that set. -/
theorem decode_image_pack_image (requests : Set (VaryingRequest V E B Locant)) :
    PackedVaryingIngress.decode ''
      ((fun r : VaryingRequest V E B Locant => r.pack) '' requests) = requests := by
  ext request
  constructor
  · rintro ⟨packed, ⟨original, member, rfl⟩, decoded⟩
    rw [decode_pack] at decoded
    exact decoded ▸ member
  · intro member
    exact ⟨request.pack, ⟨request, member, rfl⟩, decode_pack request⟩

/-- Complete packed recovery for a full varying-base request: the output carries the actual
assembled state, its sidecar is the certificate tree of the collection, and decoding returns the
whole source request including its base and optional residue ingredient. -/
theorem full_request_recovery (r : VaryingRequest V E B Locant) :
    r.pack.state = r.request.assemble ∧
    HEq r.pack.sidecar (ChannelSidecar.ofCases r.request.cases) ∧
    r.pack.decode = r :=
  ⟨r.pack_state, r.pack_sidecar, decode_pack r⟩

end VaryingRequest

end

end OrganicStereoVaryingPhysicalRequestAssembly
end TetraStereo.OneCenter
