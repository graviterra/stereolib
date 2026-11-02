import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoResidueIncidence
import TetraStereo.OneCenter.OrganicStereoSourceDataResidueAssembly

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

open OrganicStereoMolecularCanonicalTransport
open OrganicStereoMolecularEvidenceAssembly

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-!
# Glycosidic citation ingress: anomer-aware, output-only recovery

`Glycolipid1997.GlycosidicCitation` carries exactly three fields: `anomer`, `donorLocant` and
`acceptorLocant`.  The existing `GlycolipidCitationAdapter.Binding.toLink` turns a binding into a
directed residue link that retains the two locants, the two residue references and the actual source
interaction occurrence — but a link has no field for the anomer.  Consequently the adapter's
`metadata_retained` theorem only reads the three citation fields back from the *input* binding; it
does not establish that an actual canonical output still contains the anomer.

This module closes that one gap with the already approved channels, without a new carrier
constructor, a second ledger or a new graph:

* the actual directed link `binding.toLink` is placed constructively at the **end** of the actual
  ledger's ordered link list (`withCitationLink`), with the two participant certificates taken from
  the binding.  No link existence is assumed for an arbitrary ledger;
* the donor-residue-scoped datum `FragmentSourceDatum.carbohydrateAnomerKnowledge` is appended to the
  donor residue's ordered source-data list; the two constructors `alphaOnly` / `betaOnly` are the
  exact, two-sided image of `Glycolipid1997.Anomer.alpha` / `.beta` (`anomerKnowledgeOf`,
  `anomerOfKnowledge?`).  The datum has **no atom references**; it is scoped by residing in the
  donor residue's list, so it cannot be mistaken for an acceptor anchor and the existing
  `carbohydrateAnomer` constructor (whose second anchor is a reference atom) is deliberately not
  used;
* the source binding's actual input is `request.graph.certifiedEncoding eV`, so every residue,
  locant, interaction index and atom count is a bounded field of that certified source;
* the canonical output is the actual `sourceDataAppendedCanonicalOutput`, and the decoders below
  read **only** that output.  They receive no citation, no binding, no ledger and no source data:
  they take the canonical record, one explicit output link position and one explicit source-data
  offset.

## Results

* `citationCanonicalOutput_linkAt?` — the output-only link decoder at the explicit position
  `ledger.links.length` returns exactly `binding.toLink` (endpoints, locants, interaction);
* `citationCanonicalOutput_datumAt?` — the output-only datum decoder at the recovered link's
  donor residue and the explicit offset `(oldData donor).length` returns exactly the anomer-knowledge
  datum;
* `citationCanonicalOutput_reading?` — the single output-only reader recovers **all three** citation
  fields together with the link association:
  `(anomer, donorLocant, acceptorLocant)`;
* `citationCanonicalOutput_recovery` — the bundled decisive statement, including endpoint validity
  derived from the binding and the actual interaction bound;
* `citationRequest_policy` / `citationRequest_fresh` — the explicit attachment policy: exactly the
  `residueLedger?` field is replaced, a prior channel is superseded (not merged), every other
  request channel is retained;
* `citationCanonicalOutput_sameLedger_retention` — the only old-channel retention claim: under the
  explicit structural tie that the previous channel was built from the *same* extended ledger with
  `oldData`, links, hierarchy, supports and bindings are unchanged and `oldData` stays the exact
  prefix.

## Non-claims

No stereochemical correctness, chemical recognition, residue disjointness, acyclicity, global
locant uniqueness or source approval is claimed.  The recovered anomer is the supplied citation's
anomer transported through the canonical output; it is not an inferred configuration.  Only the
concrete extended ledger is used; arbitrary pre-existing ledgers are neither merged nor preserved.
-/

namespace GlycosidicCitationIngress

/-! ## The two-sided anomer / anomer-knowledge conversion -/

/-- The exact `alphaOnly`/`betaOnly` image of a supplied glycolipid anomer. -/
def anomerKnowledgeOf (anomer : Glycolipid1997.Anomer) :
    Carbohydrate1996Foundation.AnomerKnowledge :=
  match anomer with
  | .alpha => .alphaOnly
  | .beta => .betaOnly

/-- Read a single anomer back from an anomer-knowledge statement.  `equilibriumAlphaBeta` names no
single anomer, so it returns `none`; no configuration is invented. -/
def anomerOfKnowledge? (knowledge : Carbohydrate1996Foundation.AnomerKnowledge) :
    Option Glycolipid1997.Anomer :=
  match knowledge with
  | .alphaOnly => some .alpha
  | .betaOnly => some .beta
  | .equilibriumAlphaBeta => none

/-- One side of the exact inverse: the knowledge image of an anomer reads back as that anomer. -/
@[simp] theorem anomerOfKnowledge?_anomerKnowledgeOf (anomer : Glycolipid1997.Anomer) :
    anomerOfKnowledge? (anomerKnowledgeOf anomer) = some anomer := by
  cases anomer <;> rfl

/-- The other side of the exact inverse on the single-anomer constructors: any knowledge statement
that reads back as an anomer is the knowledge image of that anomer.  The equilibrium statement has
no preimage, which is why the hypothesis is a successful read. -/
theorem anomerKnowledgeOf_of_anomerOfKnowledge?
    {knowledge : Carbohydrate1996Foundation.AnomerKnowledge} {anomer : Glycolipid1997.Anomer}
    (found : anomerOfKnowledge? knowledge = some anomer) :
    anomerKnowledgeOf anomer = knowledge := by
  cases knowledge with
  | alphaOnly => cases anomer <;> simp_all [anomerOfKnowledge?, anomerKnowledgeOf]
  | betaOnly => cases anomer <;> simp_all [anomerOfKnowledge?, anomerKnowledgeOf]
  | equilibriumAlphaBeta => simp [anomerOfKnowledge?] at found

/-! ## The donor-scoped datum and the constructive link extension -/

/-- The anomeric datum for a bound citation: an anomer-knowledge statement, scoped by the residue
in whose ordered source-data list it is placed.  It carries no atom anchor, so no acceptor (or
other reference atom) can be abused as its anchor. -/
def citationDatum {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    (binding : GlycolipidCitationAdapter.Binding input ledger) : FragmentSourceDatum V :=
  FragmentSourceDatum.carbohydrateAnomerKnowledge
    (anomerKnowledgeOf binding.citation.anomer)

/-- The datum has no atom references: support of the datum is vacuous, and the only association
with the molecule is the residue scope in which it is stored. -/
@[simp] theorem citationDatum_atomReferences {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    (binding : GlycolipidCitationAdapter.Binding input ledger) :
    (citationDatum (V := V) binding).atomReferences = [] := rfl

/-- The appended per-residue data: exactly one anomer datum at the donor residue and nothing at
every other residue.  Order and duplicates of the old data are untouched because this list is
appended after them. -/
def citationSourceData {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    (binding : GlycolipidCitationAdapter.Binding input ledger) (index : Fin ledger.residueCount) :
    List (FragmentSourceDatum V) :=
  if index = binding.sourceResidue then [citationDatum (V := V) binding] else []

/-- The actual ledger extended by the binding's directed link at the end of its ordered link list.
Every existing link, residue, scoped incidence and the naming hierarchy are retained literally; the
two participant certificates of the new link are the binding's own proof fields.  This is a
constructive extension, so an arbitrary ledger needs no pre-existing link. -/
def withCitationLink {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Nat input)
    (binding : GlycolipidCitationAdapter.Binding input ledger) :
    ResidueIncidenceLedger Nat input where
  residueCount := ledger.residueCount
  residue := ledger.residue
  links := ledger.links ++ [binding.toLink]
  link_source_mem := by
    intro link member
    rcases List.mem_append.mp member with old | fresh
    · exact ledger.link_source_mem link old
    · rw [List.mem_singleton] at fresh
      subst fresh
      exact ⟨binding.sourceAtom, binding.toLink_source_resolves, binding.source_participant⟩
  link_target_mem := by
    intro link member
    rcases List.mem_append.mp member with old | fresh
    · exact ledger.link_target_mem link old
    · rw [List.mem_singleton] at fresh
      subst fresh
      exact ⟨binding.targetAtom, binding.toLink_target_resolves, binding.target_participant⟩
  hierarchy? := ledger.hierarchy?

@[simp] theorem withCitationLink_residueCount {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    (binding : GlycolipidCitationAdapter.Binding input ledger) :
    (withCitationLink ledger binding).residueCount = ledger.residueCount := rfl

@[simp] theorem withCitationLink_residue {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    (binding : GlycolipidCitationAdapter.Binding input ledger)
    (index : Fin ledger.residueCount) :
    (withCitationLink ledger binding).residue index = ledger.residue index := rfl

/-- The ordered link list of the extended ledger is the old list followed by the binding's link. -/
@[simp] theorem withCitationLink_links {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    (binding : GlycolipidCitationAdapter.Binding input ledger) :
    (withCitationLink ledger binding).links = ledger.links ++ [binding.toLink] := rfl

/-- The naming hierarchy is unchanged by the link extension. -/
@[simp] theorem withCitationLink_hierarchy? {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    (binding : GlycolipidCitationAdapter.Binding input ledger) :
    (withCitationLink ledger binding).hierarchy? = ledger.hierarchy? := rfl

/-- The explicit output link position of the citation link: the old link count. -/
theorem withCitationLink_links_getElem?_length {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input}
    (binding : GlycolipidCitationAdapter.Binding input ledger) :
    (withCitationLink ledger binding).links[ledger.links.length]? = some binding.toLink := by
  show (ledger.links ++ [binding.toLink])[ledger.links.length]? = some binding.toLink
  exact List.getElem?_concat_length

/-- The finite locant cover transports to the extended ledger: residues and their incidence are
unchanged, so the same finite duplicate-free cover is complete. -/
def coverWithCitationLink {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Nat input} (cover : LocantCover ledger)
    (binding : GlycolipidCitationAdapter.Binding input ledger) :
    LocantCover (withCitationLink ledger binding) where
  cover := cover.cover
  nodup := cover.nodup
  covers := by
    intro index locant atom found
    exact cover.covers index locant atom found

/-- The real-anchor guard for the appended citation data.  It holds because the datum has no atom
references, so no new anchor is introduced and no support is manufactured. -/
theorem citationSourceData_supported {graph : FiniteAtomInteractionHypergraph V}
    {eV : V ≃ Fin (Fintype.card V)}
    {ledger : ResidueIncidenceLedger Nat (graph.certifiedEncoding eV)}
    (binding : GlycolipidCitationAdapter.Binding (graph.certifiedEncoding eV) ledger) :
    SourceDataSupported (Locant := Nat) graph eV (withCitationLink ledger binding)
      (citationSourceData (V := V) (ledger := ledger) binding) := by
  intro index datum member atom atomMem
  by_cases donor : index = binding.sourceResidue
  · unfold citationSourceData at member
    rw [if_pos donor, List.mem_singleton] at member
    subst member
    exact absurd atomMem (by simp)
  · unfold citationSourceData at member
    rw [if_neg donor] at member
    exact absurd member (by simp)

/-! ## Output-only decoders

None of the decoders below receives the citation, the binding, the ledger, the cover or the source
data.  Each takes the actual canonical record and, at most, an explicit external position/offset. -/

/-- The output-decoded residue channel together with its observable ledger view, with the two
occurrence budgets existentially packed so that no ledger-side count is supplied to the decoder. -/
abbrev CitationView (graph : FiniteAtomInteractionHypergraph V)
    (eV : V ≃ Fin (Fintype.card V)) : Type :=
  Sigma fun residueCount : Nat =>
    Sigma fun interactionCount : Nat =>
      ResidueLedgerView Nat (graph.certifiedEncoding eV).input.molecule.atomCount
        interactionCount residueCount

/-- Decode the residue channel of the actual canonical record and then the observable ledger view
through the existing approved view decoder.  The record's stored enumeration is used by
`sourceDataChannelView?`; nothing from the original request is read. -/
def canonicalCitationView? (codec : LocantCodec Nat)
    (graph : FiniteAtomInteractionHypergraph V) (eV : V ≃ Fin (Fintype.card V))
    (canonical : CanonicalOrganicMolecularRepresentation V) : Option (CitationView graph eV) :=
  (sourceDataResidueChannel? canonical).bind fun channel =>
    (sourceDataChannelView? codec graph eV channel).map fun view =>
      ⟨channel.residueCount, ⟨channel.interactionCount, view⟩⟩

/-- One directed link of the output-decoded view, at an explicit external position.  The residue
and interaction budgets remain necessarily tied to the decoded link. -/
abbrev CitationLink : Type :=
  Sigma fun residueCount : Nat =>
    Sigma fun interactionCount : Nat =>
      DirectedResidueLink Nat (Fin residueCount) interactionCount

/-- Output-only link decoder.  It reads the decoded residue channel of the canonical record, takes
the *stored annotated link* at the explicit external position, and decodes it with the existing
`decodeLink?` locant codec.  It takes no graph, no enumeration and no ledger: the link's source and
target residues, both locants and the actual interaction occurrence come from the canonical output,
and the two occurrence budgets are the stored channel budgets packed beside the decoded link. -/
def canonicalCitationLinkAt? (codec : LocantCodec Nat)
    (canonical : CanonicalOrganicMolecularRepresentation V) (position : Nat) :
    Option CitationLink :=
  (sourceDataResidueChannel? canonical).bind fun channel =>
    (channel.annotation.links[position]?).bind fun annotated =>
      (decodeLink? codec annotated).map fun link =>
        ⟨channel.residueCount, ⟨channel.interactionCount, link⟩⟩

/-- Output-only positional datum decoder: the ordered source-data list at a residue position, then
the datum at an explicit offset.  Order and multiplicity of the output list are retained. -/
def canonicalCitationDatumAt? (canonical : CanonicalOrganicMolecularRepresentation V)
    (residueIndex offset : Nat) : Option (FragmentSourceDatum V) :=
  (decodedSourceDataAt? canonical residueIndex).bind fun data => data[offset]?

/-- The single output-only reading of a cited glycosidic link.  It locates the donor residue and the
two locants from the *decoded output link*, reads the anomeric datum at that residue selected by the
explicit offset, and returns the three citation fields together.  It cannot receive the original
citation or binding, and it does not treat the link's target locant as an anomer or the datum as an
acceptor anchor. -/
def canonicalCitationReading? (codec : LocantCodec Nat)
    (canonical : CanonicalOrganicMolecularRepresentation V)
    (linkPosition datumOffset : Nat) : Option (Glycolipid1997.Anomer × Nat × Nat) :=
  (sourceDataResidueChannel? canonical).bind fun channel =>
    (channel.annotation.links[linkPosition]?).bind fun annotated =>
      (decodeLink? codec annotated).bind fun link =>
        ((channel.annotation.residue link.source).sourceData[datumOffset]?).bind fun datum =>
          match datum with
          | .carbohydrateAnomerKnowledge knowledge =>
              (anomerOfKnowledge? knowledge).map fun anomer =>
                (anomer, link.sourceLocant, link.targetLocant)
          | _ => none

/-! ## The actual canonical output and its exact recovery -/

section Recovery

variable {request : OrganicMolecularEvidence V}
variable {eV : V ≃ Fin (Fintype.card V)}
variable {ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding eV)}
variable {binding : GlycolipidCitationAdapter.Binding (request.graph.certifiedEncoding eV) ledger}
variable {cover : LocantCover ledger}
variable {codec : LocantCodec Nat}
variable {oldData : Fin ledger.residueCount → List (FragmentSourceDatum V)}
variable {oldSupported : SourceDataSupported (Locant := Nat) request.graph eV ledger oldData}

/-- The actual canonical output of the source-data append on the constructively extended ledger.
The old ordered data are retained as the exact prefix at every residue and the citation datum is the
appended suffix only at the donor residue. -/
def citationCanonicalOutput (codec : LocantCodec Nat) (eV : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding eV))
    (binding : GlycolipidCitationAdapter.Binding (request.graph.certifiedEncoding eV) ledger)
    (cover : LocantCover ledger)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Nat) request.graph eV ledger oldData) :
    CanonicalOrganicMolecularRepresentation V :=
  sourceDataAppendedCanonicalOutput codec eV request (withCitationLink ledger binding)
    (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
    oldSupported (citationSourceData_supported binding)

/-- The recovered channel is exactly the coexisting channel on the same actual extended ledger. -/
theorem citationCanonicalOutput_channel? :
    sourceDataResidueChannel?
        (citationCanonicalOutput codec eV request ledger binding cover oldData oldSupported) =
      some (sourceDataCoexistingChannel codec eV request.graph (withCitationLink ledger binding)
        (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
        oldSupported (citationSourceData_supported binding)) := by
  unfold citationCanonicalOutput
  exact sourceDataAppendedCanonicalOutput_channel? codec eV request
    (withCitationLink ledger binding) (coverWithCitationLink cover binding) oldData
    (citationSourceData (V := V) (ledger := ledger) binding) oldSupported (citationSourceData_supported binding)

/-- The existing approved view decoder, applied to the recovered channel, returns exactly the
observable content of the extended ledger. -/
theorem citationChannelView? :
    sourceDataChannelView? codec request.graph eV
        (sourceDataCoexistingChannel codec eV request.graph (withCitationLink ledger binding)
          (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
          oldSupported (citationSourceData_supported binding)) =
      some (viewOfLedger (withCitationLink ledger binding)) := by
  unfold sourceDataCoexistingChannel
  exact sourceDataChannelView?_sourceDataBoundChannel codec eV request.graph
    (withCitationLink ledger binding) (coverWithCitationLink cover binding)
    (fun index => oldData index ++ citationSourceData (V := V) (ledger := ledger) binding index)
    (sourceDataSupported_append request.graph eV (withCitationLink ledger binding) oldData
      (citationSourceData (V := V) (ledger := ledger) binding) oldSupported (citationSourceData_supported binding))

/-- **Decisive link recovery.**  The output-only link decoder at the explicit position
`ledger.links.length` returns precisely the binding's directed link: the actual source and target
residues, the supplied donor and acceptor locants, and the actual source interaction occurrence. -/
theorem citationCanonicalOutput_linkAt? :
    canonicalCitationLinkAt? codec
        (citationCanonicalOutput codec eV request ledger binding cover oldData oldSupported)
        ledger.links.length =
      some ⟨ledger.residueCount,
        (request.graph.certifiedEncoding eV).input.molecule.interactions.length,
        binding.toLink⟩ := by
  unfold canonicalCitationLinkAt?
  rw [citationCanonicalOutput_channel?]
  simp only [Option.bind_some]
  rw [sourceDataCoexistingChannel_links]
  rw [sourceDataBoundChannel_links]
  simp only [List.getElem?_map, withCitationLink_links, List.getElem?_concat_length,
    Option.bind_some, Option.map_some, decodeLink?_encode]
  rfl

/-- **Decisive datum recovery.**  The output-only positional datum decoder at the *recovered link's
donor residue* and the explicit offset `(oldData donor).length` returns exactly the anomer-knowledge
datum.  This is the explicit source-residue association of the (anchor-free) anomeric datum. -/
theorem citationCanonicalOutput_datumAt? :
    canonicalCitationDatumAt?
        (citationCanonicalOutput codec eV request ledger binding cover oldData oldSupported)
        binding.sourceResidue.val (oldData binding.sourceResidue).length =
      some (citationDatum (V := V) binding) := by
  have hlist :
      decodedSourceDataAt?
          (citationCanonicalOutput codec eV request ledger binding cover oldData oldSupported)
          binding.sourceResidue.val =
        some (oldData binding.sourceResidue ++
          citationSourceData (V := V) (ledger := ledger) binding binding.sourceResidue) := by
    unfold decodedSourceDataAt? citationCanonicalOutput
    rw [sourceDataAppendedCanonicalOutput_lists, Option.bind_some, List.getElem?_ofFn,
      dif_pos (show binding.sourceResidue.val <
          (withCitationLink ledger binding).residueCount from binding.sourceResidue.isLt)]
    rfl
  unfold canonicalCitationDatumAt?
  rw [hlist, Option.bind_some]
  rw [show citationSourceData (V := V) (ledger := ledger) binding binding.sourceResidue =
      [citationDatum (V := V) binding] from by simp [citationSourceData]]
  exact List.getElem?_concat_length

/-- The recovered link's endpoints resolve, through the actual ledger incidence, to participants of
the actual source interaction at the recorded occurrence index.  Both facts are derived from the
binding; no endpoint or interaction is assumed. -/
theorem citationCanonicalOutput_endpoint_correct :
    (∃ atom : Fin (request.graph.certifiedEncoding eV).input.molecule.atomCount,
        (ledger.residue binding.toLink.source).incidence binding.toLink.sourceLocant = some atom ∧
          atom.val ∈ (ledger.interaction binding.toLink.interaction).participants) ∧
      (∃ atom : Fin (request.graph.certifiedEncoding eV).input.molecule.atomCount,
        (ledger.residue binding.toLink.target).incidence binding.toLink.targetLocant = some atom ∧
          atom.val ∈ (ledger.interaction binding.toLink.interaction).participants) :=
  binding.toLink_endpoint_correct

/-- The recovered interaction occurrence index is bounded by the actual certified interaction list
length.  The link can never name a non-existent source occurrence. -/
theorem citationCanonicalOutput_interaction_bound :
    binding.toLink.interaction.val <
      (request.graph.certifiedEncoding eV).input.molecule.interactions.length :=
  binding.toLink.interaction.isLt

/-- **Decisive output-only recovery of all three citation fields together with the link
association.**  At the explicit output link position and source-data offset, one reader that
receives only the actual canonical record returns exactly the supplied `(anomer, donorLocant,
acceptorLocant)`; the anomer comes from the datum at the recovered link's donor residue, and the two
locants come from the recovered link. -/
theorem citationCanonicalOutput_reading? :
    canonicalCitationReading? codec
        (citationCanonicalOutput codec eV request ledger binding cover oldData oldSupported)
        ledger.links.length (oldData binding.sourceResidue).length =
      some (binding.citation.anomer, binding.citation.donorLocant,
        binding.citation.acceptorLocant) := by
  unfold canonicalCitationReading?
  rw [citationCanonicalOutput_channel?]
  simp only [Option.bind_some]
  rw [sourceDataCoexistingChannel_links, sourceDataBoundChannel_links]
  simp only [List.getElem?_map, withCitationLink_links, List.getElem?_concat_length,
    Option.bind_some, Option.map_some, decodeLink?_encode]
  rw [sourceDataCoexistingChannel_residue_sourceData]
  rw [GlycolipidCitationAdapter.Binding.toLink_source]
  rw [show citationSourceData (V := V) (ledger := ledger) binding binding.sourceResidue =
      [citationDatum (V := V) binding] from by simp [citationSourceData]]
  rw [List.getElem?_concat_length]
  simp only [Option.bind_some, Option.map_some, citationDatum,
    anomerOfKnowledge?_anomerKnowledgeOf,
    GlycolipidCitationAdapter.Binding.toLink_sourceLocant,
    GlycolipidCitationAdapter.Binding.toLink_targetLocant]

/-- **Bundled decisive recovery.**  One actual canonical output simultaneously yields the full
channel, the observable ledger view, the exact citation link at the explicit output position, the
exact anomeric datum at the recovered donor residue, the output-only three-field citation reading,
the structural link equalities, the derived endpoint correctness and the actual interaction bound. -/
theorem citationCanonicalOutput_recovery :
    sourceDataResidueChannel?
        (citationCanonicalOutput codec eV request ledger binding cover oldData oldSupported) =
        some (sourceDataCoexistingChannel codec eV request.graph (withCitationLink ledger binding)
          (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
          oldSupported (citationSourceData_supported binding)) ∧
      sourceDataChannelView? codec request.graph eV
          (sourceDataCoexistingChannel codec eV request.graph (withCitationLink ledger binding)
            (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
            oldSupported (citationSourceData_supported binding)) =
        some (viewOfLedger (withCitationLink ledger binding)) ∧
      canonicalCitationLinkAt? codec
          (citationCanonicalOutput codec eV request ledger binding cover oldData oldSupported)
          ledger.links.length =
        some ⟨ledger.residueCount,
          (request.graph.certifiedEncoding eV).input.molecule.interactions.length,
          binding.toLink⟩ ∧
      canonicalCitationDatumAt?
          (citationCanonicalOutput codec eV request ledger binding cover oldData oldSupported)
          binding.sourceResidue.val (oldData binding.sourceResidue).length =
        some (citationDatum (V := V) binding) ∧
      canonicalCitationReading? codec
          (citationCanonicalOutput codec eV request ledger binding cover oldData oldSupported)
          ledger.links.length (oldData binding.sourceResidue).length =
        some (binding.citation.anomer, binding.citation.donorLocant,
          binding.citation.acceptorLocant) ∧
      (binding.toLink.source = binding.sourceResidue ∧
        binding.toLink.target = binding.targetResidue ∧
        binding.toLink.sourceLocant = binding.citation.donorLocant ∧
        binding.toLink.targetLocant = binding.citation.acceptorLocant ∧
        binding.toLink.interaction = binding.interaction) ∧
      ((∃ atom : Fin (request.graph.certifiedEncoding eV).input.molecule.atomCount,
          (ledger.residue binding.toLink.source).incidence binding.toLink.sourceLocant = some atom ∧
            atom.val ∈ (ledger.interaction binding.toLink.interaction).participants) ∧
        (∃ atom : Fin (request.graph.certifiedEncoding eV).input.molecule.atomCount,
          (ledger.residue binding.toLink.target).incidence binding.toLink.targetLocant = some atom ∧
            atom.val ∈ (ledger.interaction binding.toLink.interaction).participants)) ∧
      binding.toLink.interaction.val <
        (request.graph.certifiedEncoding eV).input.molecule.interactions.length :=
  ⟨citationCanonicalOutput_channel?, citationChannelView?, citationCanonicalOutput_linkAt?,
    citationCanonicalOutput_datumAt?, citationCanonicalOutput_reading?, ⟨rfl, rfl, rfl, rfl, rfl⟩,
    citationCanonicalOutput_endpoint_correct, citationCanonicalOutput_interaction_bound⟩

/-! ## Attachment policy and same-ledger retention

The shared policy API is explicit: attaching the source-data channel replaces exactly the
`residueLedger?` field.  A previous optional channel is superseded in that field, never merged, and
no preservation of an arbitrary old ledger is claimed.  The only retention statement is the
same-ledger structural one below. -/

/-- The actual request carrying the coexisting channel (old data first, citation datum last). -/
def citationRequest (codec : LocantCodec Nat) (eV : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V)
    (ledger : ResidueIncidenceLedger Nat (request.graph.certifiedEncoding eV))
    (binding : GlycolipidCitationAdapter.Binding (request.graph.certifiedEncoding eV) ledger)
    (cover : LocantCover ledger)
    (oldData : Fin ledger.residueCount → List (FragmentSourceDatum V))
    (oldSupported : SourceDataSupported (Locant := Nat) request.graph eV ledger oldData) :
    OrganicMolecularEvidence V :=
  sourceDataAppendedRequest codec eV request (withCitationLink ledger binding)
    (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
    oldSupported (citationSourceData_supported binding)

/-- The explicit attachment policy: only `residueLedger?` is replaced by the coexisting channel;
graph, conformation, rational positions, electronic, paths, bands, roles, drawing, fragments,
conventions, cages and frames are retained exactly. -/
theorem citationRequest_policy :
    SourceDataAttachmentPolicy request
      (citationRequest codec eV request ledger binding cover oldData oldSupported)
      (sourceDataCoexistingChannel codec eV request.graph (withCitationLink ledger binding)
        (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
        oldSupported (citationSourceData_supported binding)) := by
  unfold citationRequest sourceDataAppendedRequest
  exact attachSourceDataResidueLedgerRequest_policy request _

/-- Fresh-case exposure: when the request carries no residue channel, the attached request's only
residue channel is the coexisting channel and the policy still holds.  This makes the replacement
semantics observable rather than assumed. -/
theorem citationRequest_fresh (h : request.residueLedger? = none) :
    request.residueLedger? = none ∧
      (citationRequest codec eV request ledger binding cover oldData oldSupported).residueLedger? =
        some (sourceDataCoexistingChannel codec eV request.graph
          (withCitationLink ledger binding) (coverWithCitationLink cover binding) oldData
          (citationSourceData (V := V) (ledger := ledger) binding) oldSupported (citationSourceData_supported binding)) ∧
      SourceDataAttachmentPolicy request
        (citationRequest codec eV request ledger binding cover oldData oldSupported)
        (sourceDataCoexistingChannel codec eV request.graph (withCitationLink ledger binding)
          (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
          oldSupported (citationSourceData_supported binding)) :=
  ⟨h, rfl, citationRequest_policy⟩

/-- **Same-ledger structural retention.**  If the request's previous channel was built from the same
extended ledger with the same old data, then appending the citation datum leaves the ordered link
list, the naming hierarchy, every support and every ordered binding unchanged, and retains `oldData`
as the exact prefix of every recovered ordered source-data list.  No claim is made about a channel
built from any other ledger. -/
theorem citationCanonicalOutput_sameLedger_retention
    (existing : request.residueLedger? =
      some (sourceDataBoundChannel codec eV request.graph (withCitationLink ledger binding)
        (coverWithCitationLink cover binding) oldData oldSupported)) :
    request.residueLedger? =
        some (sourceDataBoundChannel codec eV request.graph (withCitationLink ledger binding)
          (coverWithCitationLink cover binding) oldData oldSupported) ∧
      (sourceDataCoexistingChannel codec eV request.graph (withCitationLink ledger binding)
          (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
          oldSupported (citationSourceData_supported binding)).annotation.links =
        (sourceDataBoundChannel codec eV request.graph (withCitationLink ledger binding)
          (coverWithCitationLink cover binding) oldData oldSupported).annotation.links ∧
      (sourceDataCoexistingChannel codec eV request.graph (withCitationLink ledger binding)
          (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
          oldSupported (citationSourceData_supported binding)).annotation.hierarchy? =
        (sourceDataBoundChannel codec eV request.graph (withCitationLink ledger binding)
          (coverWithCitationLink cover binding) oldData oldSupported).annotation.hierarchy? ∧
      (∀ index : Fin ledger.residueCount,
        ((sourceDataCoexistingChannel codec eV request.graph (withCitationLink ledger binding)
            (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
            oldSupported (citationSourceData_supported binding)).annotation.residue index).support =
          ((sourceDataBoundChannel codec eV request.graph (withCitationLink ledger binding)
            (coverWithCitationLink cover binding) oldData oldSupported).annotation.residue
            index).support ∧
        ((sourceDataCoexistingChannel codec eV request.graph (withCitationLink ledger binding)
            (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
            oldSupported (citationSourceData_supported binding)).annotation.residue index).bindings =
          ((sourceDataBoundChannel codec eV request.graph (withCitationLink ledger binding)
            (coverWithCitationLink cover binding) oldData oldSupported).annotation.residue
            index).bindings) ∧
      (∀ index : Fin ledger.residueCount,
        ((sourceDataCoexistingChannel codec eV request.graph (withCitationLink ledger binding)
            (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
            oldSupported (citationSourceData_supported binding)).annotation.residue index).sourceData.take
            (oldData index).length = oldData index) :=
  ⟨existing,
    sourceDataCoexistingChannel_links codec eV request.graph (withCitationLink ledger binding)
      (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
      oldSupported (citationSourceData_supported binding),
    sourceDataCoexistingChannel_hierarchy? codec eV request.graph (withCitationLink ledger binding)
      (coverWithCitationLink cover binding) oldData (citationSourceData (V := V) (ledger := ledger) binding)
      oldSupported (citationSourceData_supported binding),
    fun index =>
      ⟨sourceDataCoexistingChannel_residue_support codec eV request.graph
          (withCitationLink ledger binding) (coverWithCitationLink cover binding) oldData
          (citationSourceData (V := V) (ledger := ledger) binding) oldSupported
          (citationSourceData_supported binding) index,
        sourceDataCoexistingChannel_residue_bindings codec eV request.graph
          (withCitationLink ledger binding) (coverWithCitationLink cover binding) oldData
          (citationSourceData (V := V) (ledger := ledger) binding) oldSupported
          (citationSourceData_supported binding) index⟩,
    fun index =>
      sourceDataCoexistingChannel_old_prefix codec eV request.graph
        (withCitationLink ledger binding) (coverWithCitationLink cover binding) oldData
        (citationSourceData (V := V) (ledger := ledger) binding) oldSupported
        (citationSourceData_supported binding) index⟩

end Recovery

end GlycosidicCitationIngress

end

end TetraStereo.OneCenter

/-! Decisive glycosidic-citation recovery facts are kernel checked. -/
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.anomerOfKnowledge?_anomerKnowledgeOf
assert_kernel_only
  TetraStereo.OneCenter.GlycosidicCitationIngress.anomerKnowledgeOf_of_anomerOfKnowledge?
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.citationDatum_atomReferences
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.withCitationLink_links_getElem?_length
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.citationSourceData_supported
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.citationCanonicalOutput_channel?
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.citationChannelView?
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.citationCanonicalOutput_linkAt?
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.citationCanonicalOutput_datumAt?
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.citationCanonicalOutput_endpoint_correct
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.citationCanonicalOutput_interaction_bound
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.citationCanonicalOutput_reading?
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.citationCanonicalOutput_recovery
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.citationRequest_policy
assert_kernel_only TetraStereo.OneCenter.GlycosidicCitationIngress.citationRequest_fresh
assert_kernel_only
  TetraStereo.OneCenter.GlycosidicCitationIngress.citationCanonicalOutput_sameLedger_retention
