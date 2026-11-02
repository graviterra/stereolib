import TetraStereo.OneCenter.OrganicStereoSimultaneousCaseAssembly
import TetraStereo.OneCenter.OrganicStereoSourceBoundResidueAssembly

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace TetraStereo.OneCenter
namespace OrganicStereoSharedPhysicalCaseIngress

open OrganicStereoIndependentElectronicEncoding
open PhysicalPlaneEvidence
open PhysicalPlaneEvidence.ReferencePlane

noncomputable section

universe u v

variable {V E B : Type u} [DecidableEq V] [Fintype V] [Fintype E] [Fintype B]
variable {Locant : Type v}


































/-! ## External shape tags -/

/-- External tag distinguishing the heterogeneous case constructors.  The tag is not stored inside
the annotation payload; it is the ordered shape list supplied alongside the collection. -/
inductive CaseShape where
  | ringPlane
  | closedRing
  | torsion
  | cage
  | fragment
  | convention
  deriving DecidableEq, Repr

/-! ## The shared physical context -/

/-- The common physical source supplied independently of the cases: the actual interaction graph,
the optional present electronic inventory with its graph tie, the single real conformation, and the
chosen enumeration of the atom labels.  Every case is indexed by this context, so the same case list
type is meaningful for the ingress base and for the assembled state (both preserve these fields
definitionally). -/
structure SharedPhysicalContext (V : Type*) [DecidableEq V] [Fintype V] where
  /-- The actual finite atom-labelled interaction graph. -/
  graph : FiniteAtomInteractionHypergraph V
  /-- The optional present electronic inventory. -/
  electronic? : Option (ElectronicChannel V) := none
  /-- The declared tie of a present inventory to the graph. -/
  electronic_unpaired : ∀ channel, electronic? = some channel → ∀ owner,
    (channel.counts.counts owner).unpairedElectronPositions =
      (graph.atomData owner).unpairedElectrons
  /-- The single real conformation shared by every case. -/
  conformation : MolecularConformation V
  /-- The chosen enumeration of the atom labels used by the one encoding. -/
  enumeration : V ≃ Fin (Fintype.card V)

namespace SharedPhysicalContext

variable {state : WholeState V E B}

/-- The context of a genuine physical ingress state.  Its graph, inventory and conformation are
literally the state's fields, so definitions below reduce to the state's own data. -/
def ofState (state : WholeState V E B) (enumeration : V ≃ Fin (Fintype.card V)) :
    SharedPhysicalContext V where
  graph := state.graph
  electronic? := state.electronic?
  electronic_unpaired := state.electronic_unpaired
  conformation := state.conformation
  enumeration := enumeration

/-- The one encoded source molecule of the context. -/
def molecule (ctx : SharedPhysicalContext V) : SemanticMolecule :=
  ctx.graph.encode ctx.enumeration

/-- The atom equivalence induced by the context's single enumeration and the proved encoded atom
count.  It is the same `encodedAtomEquiv` used by the source-bound residue assembly: there is no
second enumeration. -/
def atomEquiv (ctx : SharedPhysicalContext V) : V ≃ Fin ctx.molecule.atomCount :=
  encodedAtomEquiv ctx.graph ctx.enumeration

/-- The context conformation transported to the encoded source indices. -/
def encodedConformation (ctx : SharedPhysicalContext V) :
    MolecularConformation (Fin ctx.molecule.atomCount) :=
  fun index => ctx.conformation (ctx.atomEquiv.symm index)

/-- An independent case observation agrees with the context exactly when its real conformation is
the context conformation read through the common encoding equivalence. -/
def ObservationAgrees (ctx : SharedPhysicalContext V)
    (observation : PhysicalRingPlaneObservation ctx.molecule) : Prop :=
  observation.conformation = ctx.encodedConformation

/-- Selected-support coplanarity stated directly over a frame: every frame ring atom, read at the
context conformation, lies in the frame's chosen plane.  This is a proposition; it is only ever
stored when actual `CoplanarRingEvidence` was supplied. -/
def CoplanarFrameSupport (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V) : Prop :=
  ∀ atom, atom ∈ frame.ringAtoms → frame.plane.InPlane (ctx.conformation atom)

end SharedPhysicalContext

variable {ctx : SharedPhysicalContext V}

/-! ## Certificates retained by the case records

The frame vocabulary retains the plane, ordered support, substituents and (for closed rings) the
selected attachment data.  It deliberately does not retain the propositional facts that made an
observation valid.  These certificates supply exactly those facts, over the frame's own retained
data; they contain no second copy of the plane, support or attachment indices. -/

/-- Propositional facts needed to read a generic ring-plane frame back as an observation.  The
optional coplanarity flag preserves the caller's actual choice: `none` means no coplanarity
evidence was supplied, and it is never replaced by a claim. -/
structure RingPlaneFrameCertificate (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V) where
  /-- The mapped support is duplicate-free. -/
  ringAtoms_nodup : (frame.ringAtoms.map ctx.atomEquiv).Nodup
  /-- The mapped support is nonempty. -/
  ringAtoms_nonempty : frame.ringAtoms.map ctx.atomEquiv ≠ []
  /-- The two substituents remain distinct after mapping. -/
  substituents_distinct :
    ctx.atomEquiv frame.firstSubstituent ≠ ctx.atomEquiv frame.secondSubstituent
  /-- The first substituent is not a support atom. -/
  firstSubstituent_not_ring :
    ctx.atomEquiv frame.firstSubstituent ∉ frame.ringAtoms.map ctx.atomEquiv
  /-- The second substituent is not a support atom. -/
  secondSubstituent_not_ring :
    ctx.atomEquiv frame.secondSubstituent ∉ frame.ringAtoms.map ctx.atomEquiv
  /-- The caller's actual optional coplanarity evidence, over the frame's own support.  `PLift`
  makes the propositional evidence storable in a `Type`-valued option; `none` means no evidence
  was supplied and is never replaced by a claim. -/
  coplanar? : Option (PLift (ctx.CoplanarFrameSupport frame)) := none

/-- The actual green closed-ring certificate over the frame's own retained support.  It stores the
source ring, both selected attachment values and their fitted validity witnesses; it is exactly the
certificate produced by the green `OrganicStereoFrameAnnotations` adapter, so no second ring,
observation or desired equality is invented here.  The selected ring positions and occurrence
indices are the frame's retained attachment values, and decoding goes through the green
`RealRingPlaneFrame.toPhysicalClosedRingObservation`. -/
abbrev ClosedRingFrameCertificate (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V) : Type u :=
  RealRingPlaneFrame.ClosedRingCertificate ctx.atomEquiv frame

/-- Propositional torsion facts: the frame is valid, and every selected site identity is bound to
the *present* electronic inventory of the same context.  Absent site selections are valid and are
not replaced by any invented slot. -/
structure TorsionFrameCertificate (ctx : SharedPhysicalContext V)
    (frame : TorsionReferenceFrame V) : Prop where
  /-- Every supplied site is compatible with its legacy participant. -/
  valid : frame.Valid
  /-- If any selected site is present, the context actually carries an inventory. -/
  sites_present : (frame.frontSite? ≠ none ∨ frame.rearSite? ≠ none) →
    ∃ channel : ElectronicChannel V, ctx.electronic? = some channel
  /-- Every selected site matches the present inventory's counts. -/
  site_matches : ∀ site : SelectedElectronicSite V,
    (frame.frontSite? = some site ∨ frame.rearSite? = some site) →
      ∀ channel : ElectronicChannel V, ctx.electronic? = some channel →
        site.MatchesInventory channel.counts

/-- Propositional graph backing for a numbered cage annotation.  Cage numbering metadata is not
geometry: this certificate only requires the actual carrier graph to contain the annotated edges
as participant co-memberships and the annotated addend interactions as actual interaction values.
It makes no claim that the carrier is, contains or determines a fullerene source graph. -/
structure CageGraphBound (ctx : SharedPhysicalContext V)
    (annotation : NumberedCageAnnotation V) : Prop where
  /-- The stored numbering universe is the actual atom-label universe. -/
  atomCount_eq : annotation.atomCount = Fintype.card V
  /-- Every cage edge is backed by an actual carrier interaction containing both endpoints. -/
  edge_backed : ∀ edge ∈ annotation.edges,
    ∃ interaction ∈ ctx.graph.interactions,
      edge.1 ∈ interaction.1 ∧ edge.2 ∈ interaction.1
  /-- Every addend interaction is an actual carrier interaction value. -/
  addend_backed : ∀ interaction ∈ annotation.addendInteractions,
    interaction ∈ ctx.graph.interactions

/-! ## The tagged case record -/

/-- One independently supplied shared-source case.  Every constructor stores an existing annotation
value and a proof-carrying certificate; no constructor stores an assembled `WholeState`, a request,
or an original observation. -/
inductive PhysicalCase (ctx : SharedPhysicalContext V) where
  | ringPlane (frame : RealRingPlaneFrame V) (certificate : RingPlaneFrameCertificate ctx frame)
  | closedRing (frame : RealRingPlaneFrame V) (certificate : ClosedRingFrameCertificate ctx frame)
  | torsion (frame : TorsionReferenceFrame V) (certificate : TorsionFrameCertificate ctx frame)
  | cage (annotation : NumberedCageAnnotation V) (certificate : CageGraphBound ctx annotation)
  | fragment (annotation : FragmentAnnotation V)
  | convention (source : OrganicConventionSource V)

namespace PhysicalCase

variable {ctx : SharedPhysicalContext V}

/-- The external shape tag of one case. -/
def shape : PhysicalCase ctx → CaseShape
  | .ringPlane _ _ => .ringPlane
  | .closedRing _ _ => .closedRing
  | .torsion _ _ => .torsion
  | .cage _ _ => .cage
  | .fragment _ => .fragment
  | .convention _ => .convention

/-- The frame-channel contribution of one case.  Ring, closed-ring and torsion cases contribute one
frame; cage, fragment and convention cases contribute none. -/
def frame? : PhysicalCase ctx → Option (FrameAnnotation V)
  | .ringPlane frame _ => some (.realRingPlane frame)
  | .closedRing frame _ => some (.realRingPlane frame)
  | .torsion frame _ => some (.torsionReference frame)
  | .cage _ _ => none
  | .fragment _ => none
  | .convention _ => none

/-- The cage-channel contribution of one case. -/
def cage? : PhysicalCase ctx → Option (NumberedCageAnnotation V)
  | .cage annotation _ => some annotation
  | _ => none

/-- The fragment-channel contribution of one case. -/
def fragment? : PhysicalCase ctx → Option (FragmentAnnotation V)
  | .fragment annotation => some annotation
  | _ => none

/-- The convention-channel contribution of one case. -/
def convention? : PhysicalCase ctx → Option (OrganicConventionSource V)
  | .convention source => some source
  | _ => none

end PhysicalCase

/-! ## Ordered channel contribution -/

/-- Append one case's frame contribution in front of the remaining frame channel. -/
def frameStep (c : PhysicalCase ctx) (rest : List (FrameAnnotation V)) :
    List (FrameAnnotation V) :=
  match c.frame? with
  | some frame => frame :: rest
  | none => rest

/-- Append one case's cage contribution in front of the remaining cage channel. -/
def cageStep (c : PhysicalCase ctx) (rest : List (NumberedCageAnnotation V)) :
    List (NumberedCageAnnotation V) :=
  match c.cage? with
  | some annotation => annotation :: rest
  | none => rest

/-- Append one case's fragment contribution in front of the remaining fragment channel. -/
def fragmentStep (c : PhysicalCase ctx) (rest : List (FragmentAnnotation V)) :
    List (FragmentAnnotation V) :=
  match c.fragment? with
  | some annotation => annotation :: rest
  | none => rest

/-- Append one case's convention contribution in front of the remaining convention channel. -/
def conventionStep (c : PhysicalCase ctx) (rest : ConventionChannel V) : ConventionChannel V :=
  match c.convention? with
  | some source => source :: rest
  | none => rest

/-- The ordered frame channel of a collection, at the exact occurrence positions of the cases that
contribute frames. -/
def caseFrames : List (PhysicalCase ctx) → List (FrameAnnotation V)
  | [] => []
  | c :: cs => frameStep c (caseFrames cs)

/-- The ordered cage channel of a collection. -/
def caseCages : List (PhysicalCase ctx) → List (NumberedCageAnnotation V)
  | [] => []
  | c :: cs => cageStep c (caseCages cs)

/-- The ordered fragment channel of a collection. -/
def caseFragments : List (PhysicalCase ctx) → List (FragmentAnnotation V)
  | [] => []
  | c :: cs => fragmentStep c (caseFragments cs)

/-- The ordered convention channel of a collection. -/
def caseConventions : List (PhysicalCase ctx) → ConventionChannel V
  | [] => []
  | c :: cs => conventionStep c (caseConventions cs)

@[simp] theorem caseFrames_nil : caseFrames ([] : List (PhysicalCase ctx)) = [] := rfl

@[simp] theorem caseFrames_cons (c : PhysicalCase ctx) (cs : List (PhysicalCase ctx)) :
    caseFrames (c :: cs) = frameStep c (caseFrames cs) := rfl

@[simp] theorem caseCages_cons (c : PhysicalCase ctx) (cs : List (PhysicalCase ctx)) :
    caseCages (c :: cs) = cageStep c (caseCages cs) := rfl

@[simp] theorem caseFragments_cons (c : PhysicalCase ctx) (cs : List (PhysicalCase ctx)) :
    caseFragments (c :: cs) = fragmentStep c (caseFragments cs) := rfl

@[simp] theorem caseConventions_cons (c : PhysicalCase ctx) (cs : List (PhysicalCase ctx)) :
    caseConventions (c :: cs) = conventionStep c (caseConventions cs) := rfl

/-- The whole `CaseBundle` derived from one arbitrary ordered collection.  Every list is exactly the
positional channel image; the request is never stored. -/
def bundleOfCases (cases : List (PhysicalCase ctx)) : CaseBundle V where
  frames := caseFrames cases
  fragments := caseFragments cases
  conventions := caseConventions cases
  cages := caseCages cases

@[simp] theorem bundleOfCases_frames (cases : List (PhysicalCase ctx)) :
    (bundleOfCases cases).frames = caseFrames cases := rfl

@[simp] theorem bundleOfCases_fragments (cases : List (PhysicalCase ctx)) :
    (bundleOfCases cases).fragments = caseFragments cases := rfl

@[simp] theorem bundleOfCases_conventions (cases : List (PhysicalCase ctx)) :
    (bundleOfCases cases).conventions = caseConventions cases := rfl

@[simp] theorem bundleOfCases_cages (cases : List (PhysicalCase ctx)) :
    (bundleOfCases cases).cages = caseCages cases := rfl

/-- Attach one independent case collection to a physical ingress substrate.  This is the actual
`CaseBundle`/`attachCases` attachment; no assembled state is taken as a premise. -/
def assembleCases (base : WholeState V E B) (cases : List (PhysicalCase ctx)) :
    WholeState V E B :=
  attachCases base (bundleOfCases cases)

@[simp] theorem assembleCases_graph (base : WholeState V E B) (cases : List (PhysicalCase ctx)) :
    (assembleCases base cases).graph = base.graph := rfl

@[simp] theorem assembleCases_conformation (base : WholeState V E B)
    (cases : List (PhysicalCase ctx)) :
    (assembleCases base cases).conformation = base.conformation := rfl

@[simp] theorem assembleCases_electronic? (base : WholeState V E B)
    (cases : List (PhysicalCase ctx)) :
    (assembleCases base cases).electronic? = base.electronic? := rfl

@[simp] theorem assembleCases_frames (base : WholeState V E B) (cases : List (PhysicalCase ctx)) :
    (assembleCases base cases).frames = caseFrames cases := rfl

@[simp] theorem assembleCases_cages (base : WholeState V E B) (cases : List (PhysicalCase ctx)) :
    (assembleCases base cases).cages = caseCages cases := rfl

@[simp] theorem assembleCases_fragments (base : WholeState V E B) (cases : List (PhysicalCase ctx)) :
    (assembleCases base cases).fragments = caseFragments cases := rfl

@[simp] theorem assembleCases_conventions (base : WholeState V E B)
    (cases : List (PhysicalCase ctx)) :
    (assembleCases base cases).conventions = caseConventions cases := rfl

/-! ## The proof-carrying certificate tree

The tree is indexed by the external shape list and by the *actual* channel lists.  Each constructor
consumes exactly the head of its own channel, so the interleaving of heterogeneous cases and the
occurrence position of every duplicate are both determined by the tag list plus the channel data.
Only the certificate is stored; the frame/annotation is an index and is read back from the state. -/

inductive CaseCertificates (ctx : SharedPhysicalContext V) :
    List CaseShape → List (FrameAnnotation V) → List (NumberedCageAnnotation V) →
      List (FragmentAnnotation V) → ConventionChannel V → Type u where
  | nil : CaseCertificates ctx [] [] [] [] []
  | ringPlane {tags : List CaseShape} {frames : List (FrameAnnotation V)}
      {cages : List (NumberedCageAnnotation V)} {fragments : List (FragmentAnnotation V)}
      {conventions : ConventionChannel V}
      (frame : RealRingPlaneFrame V) (certificate : RingPlaneFrameCertificate ctx frame)
      (tail : CaseCertificates ctx tags frames cages fragments conventions) :
      CaseCertificates ctx (.ringPlane :: tags) (.realRingPlane frame :: frames)
        cages fragments conventions
  | closedRing {tags : List CaseShape} {frames : List (FrameAnnotation V)}
      {cages : List (NumberedCageAnnotation V)} {fragments : List (FragmentAnnotation V)}
      {conventions : ConventionChannel V}
      (frame : RealRingPlaneFrame V) (certificate : ClosedRingFrameCertificate ctx frame)
      (tail : CaseCertificates ctx tags frames cages fragments conventions) :
      CaseCertificates ctx (.closedRing :: tags) (.realRingPlane frame :: frames)
        cages fragments conventions
  | torsion {tags : List CaseShape} {frames : List (FrameAnnotation V)}
      {cages : List (NumberedCageAnnotation V)} {fragments : List (FragmentAnnotation V)}
      {conventions : ConventionChannel V}
      (frame : TorsionReferenceFrame V) (certificate : TorsionFrameCertificate ctx frame)
      (tail : CaseCertificates ctx tags frames cages fragments conventions) :
      CaseCertificates ctx (.torsion :: tags) (.torsionReference frame :: frames)
        cages fragments conventions
  | cage {tags : List CaseShape} {frames : List (FrameAnnotation V)}
      {cages : List (NumberedCageAnnotation V)} {fragments : List (FragmentAnnotation V)}
      {conventions : ConventionChannel V}
      (annotation : NumberedCageAnnotation V) (certificate : CageGraphBound ctx annotation)
      (tail : CaseCertificates ctx tags frames cages fragments conventions) :
      CaseCertificates ctx (.cage :: tags) frames (annotation :: cages) fragments conventions
  | fragment {tags : List CaseShape} {frames : List (FrameAnnotation V)}
      {cages : List (NumberedCageAnnotation V)} {fragments : List (FragmentAnnotation V)}
      {conventions : ConventionChannel V}
      (annotation : FragmentAnnotation V)
      (tail : CaseCertificates ctx tags frames cages fragments conventions) :
      CaseCertificates ctx (.fragment :: tags) frames cages (annotation :: fragments) conventions
  | convention {tags : List CaseShape} {frames : List (FrameAnnotation V)}
      {cages : List (NumberedCageAnnotation V)} {fragments : List (FragmentAnnotation V)}
      {conventions : ConventionChannel V}
      (source : OrganicConventionSource V)
      (tail : CaseCertificates ctx tags frames cages fragments conventions) :
      CaseCertificates ctx (.convention :: tags) frames cages fragments (source :: conventions)

namespace CaseCertificates

/-- Decode the tagged collection from the actual channel data plus the proof-carrying certificates.
The data (frame, cage, fragment, convention) is read from the state's channel by the inductive
indices; only the certificate is taken from the tree. -/
def decode {tags : List CaseShape} {frames : List (FrameAnnotation V)}
    {cages : List (NumberedCageAnnotation V)} {fragments : List (FragmentAnnotation V)}
    {conventions : ConventionChannel V}
    (certificates : CaseCertificates ctx tags frames cages fragments conventions) :
    List (PhysicalCase ctx) :=
  match certificates with
  | .nil => []
  | .ringPlane frame certificate tail => .ringPlane frame certificate :: tail.decode
  | .closedRing frame certificate tail => .closedRing frame certificate :: tail.decode
  | .torsion frame certificate tail => .torsion frame certificate :: tail.decode
  | .cage annotation certificate tail => .cage annotation certificate :: tail.decode
  | .fragment annotation tail => .fragment annotation :: tail.decode
  | .convention source tail => .convention source :: tail.decode

/-- The certificate tree derived from one arbitrary ordered case collection.  Every certificate is
the case's own certificate; no observation, request or desired equality is used. -/
def ofCases :
    (cases : List (PhysicalCase ctx)) →
      CaseCertificates ctx (cases.map PhysicalCase.shape) (caseFrames cases)
        (caseCages cases) (caseFragments cases) (caseConventions cases)
  | [] => .nil
  | .ringPlane frame certificate :: tail => .ringPlane frame certificate (ofCases tail)
  | .closedRing frame certificate :: tail => .closedRing frame certificate (ofCases tail)
  | .torsion frame certificate :: tail => .torsion frame certificate (ofCases tail)
  | .cage annotation certificate :: tail => .cage annotation certificate (ofCases tail)
  | .fragment annotation :: tail => .fragment annotation (ofCases tail)
  | .convention source :: tail => .convention source (ofCases tail)

end CaseCertificates

/-! ## The certified encoding of one collection -/

/-- The complete certified encoding of an ordered collection: the external shape list, the four
actual channel lists, and the proof-carrying certificate tree.  This is the data the decoder
consumes; the assembled state supplies exactly the four channel lists. -/
structure EncodedCollection (ctx : SharedPhysicalContext V) where
  tags : List CaseShape
  frames : List (FrameAnnotation V)
  cages : List (NumberedCageAnnotation V)
  fragments : List (FragmentAnnotation V)
  conventions : ConventionChannel V
  certificates : CaseCertificates ctx tags frames cages fragments conventions

namespace EncodedCollection

/-- Encode one ordered case collection.  The four channel lists are exactly the assembled bundle's
lists, definitionally. -/
def encode (cases : List (PhysicalCase ctx)) : EncodedCollection ctx where
  tags := cases.map PhysicalCase.shape
  frames := caseFrames cases
  cages := caseCages cases
  fragments := caseFragments cases
  conventions := caseConventions cases
  certificates := CaseCertificates.ofCases cases

/-- Decode an encoded collection back to the ordered case list. -/
def decode (encoded : EncodedCollection ctx) : List (PhysicalCase ctx) :=
  encoded.certificates.decode

/-- The bundle carried by the encoding. -/
def bundle (encoded : EncodedCollection ctx) : CaseBundle V where
  frames := encoded.frames
  fragments := encoded.fragments
  conventions := encoded.conventions
  cages := encoded.cages

@[simp] theorem encode_tags (cases : List (PhysicalCase ctx)) :
    (encode cases).tags = cases.map PhysicalCase.shape := rfl

@[simp] theorem encode_frames (cases : List (PhysicalCase ctx)) :
    (encode cases).frames = caseFrames cases := rfl

@[simp] theorem encode_cages (cases : List (PhysicalCase ctx)) :
    (encode cases).cages = caseCages cases := rfl

@[simp] theorem encode_fragments (cases : List (PhysicalCase ctx)) :
    (encode cases).fragments = caseFragments cases := rfl

@[simp] theorem encode_conventions (cases : List (PhysicalCase ctx)) :
    (encode cases).conventions = caseConventions cases := rfl

@[simp] theorem encode_bundle (cases : List (PhysicalCase ctx)) :
    (encode cases).bundle = bundleOfCases cases := rfl

/-- The encoded collection is exactly the assembled state's channel data together with the
certificates. -/
@[simp] theorem encode_bundle_attachCases (base : WholeState V E B) (cases : List (PhysicalCase ctx)) :
    (encode cases).bundle = CaseBundle.extractCases (assembleCases base cases) := by
  rw [encode_bundle]
  exact (extractCases_attachCases base (bundleOfCases cases)).symm

end EncodedCollection

/-! ## Universal ordered recovery

The certificate tree consumes exactly one head of its own channel per constructor, so decoding the
tree built from a collection returns that collection literally.  No certificate is reconstructed
from an assumed equality, and no duplicate occurrence is collapsed. -/

namespace CaseCertificates

/-- Decoding the certificate tree derived from an arbitrary ordered collection returns the
collection itself, in the same order and with the same multiplicity. -/
@[simp] theorem decode_ofCases (cases : List (PhysicalCase ctx)) :
    (ofCases cases).decode = cases := by
  induction cases with
  | nil => rfl
  | cons c cs ih =>
      cases c <;> simp [ofCases, decode, ih]

end CaseCertificates

namespace EncodedCollection

/-- Encoding followed by decoding is the identity on every arbitrary ordered collection. -/
@[simp] theorem decode_encode (cases : List (PhysicalCase ctx)) :
    (encode cases).decode = cases :=
  CaseCertificates.decode_ofCases cases

/-- Encoding is injective: two collections with the same certified encoding are the same ordered
list, so no coexistence or correlation pattern is lost by the common-source ingress. -/
theorem encode_injective :
    Function.Injective (encode (ctx := ctx)) := by
  intro first second same
  have decoded := congrArg decode same
  simpa using decoded

/-- The whole set-level image inverse: for every set of ordered case collections, the collections
whose encoding lies in the image of that set are exactly the original set.  This is the set form of
the universal collection recovery and covers arbitrary coexistence and correlation patterns. -/
theorem set_image_inverse (collections : Set (List (PhysicalCase ctx))) :
    encode (ctx := ctx) ⁻¹' (encode (ctx := ctx) '' collections) = collections := by
  ext cases
  constructor
  · rintro ⟨other, hother, same⟩
    have : other = cases := encode_injective same
    simpa [this] using hother
  · intro member
    exact ⟨cases, member, rfl⟩

end EncodedCollection

/-! ## Channel-indexed certificate sidecar -/

/-- A certificate tree indexed by the *actual* channel lists of an assembled state rather than by
a private copy of them.  Each node consumes the head payload of the channel selected by its tag and
retains only the tag's proof-carrying certificate (with any optional coplanarity presence) plus the
rest of the tree; no frame, cage, fragment, convention or raw case payload is stored as a separate
list.  This is the minimal sidecar a state decoder needs. -/
inductive ChannelSidecar (ctx : SharedPhysicalContext V) :
    List (FrameAnnotation V) → List (NumberedCageAnnotation V) →
      List (FragmentAnnotation V) → ConventionChannel V → List CaseShape → Type u
  | nil : ChannelSidecar ctx [] [] [] [] []
  | ringPlane {frame : RealRingPlaneFrame V} {frames : List (FrameAnnotation V)}
      {cages : List (NumberedCageAnnotation V)} {fragments : List (FragmentAnnotation V)}
      {conventions : ConventionChannel V} {tags : List CaseShape}
      (certificate : RingPlaneFrameCertificate ctx frame)
      (rest : ChannelSidecar ctx frames cages fragments conventions tags) :
      ChannelSidecar ctx (.realRingPlane frame :: frames) cages fragments conventions
        (.ringPlane :: tags)
  | closedRing {frame : RealRingPlaneFrame V} {frames : List (FrameAnnotation V)}
      {cages : List (NumberedCageAnnotation V)} {fragments : List (FragmentAnnotation V)}
      {conventions : ConventionChannel V} {tags : List CaseShape}
      (certificate : ClosedRingFrameCertificate ctx frame)
      (rest : ChannelSidecar ctx frames cages fragments conventions tags) :
      ChannelSidecar ctx (.realRingPlane frame :: frames) cages fragments conventions
        (.closedRing :: tags)
  | torsion {frame : TorsionReferenceFrame V} {frames : List (FrameAnnotation V)}
      {cages : List (NumberedCageAnnotation V)} {fragments : List (FragmentAnnotation V)}
      {conventions : ConventionChannel V} {tags : List CaseShape}
      (certificate : TorsionFrameCertificate ctx frame)
      (rest : ChannelSidecar ctx frames cages fragments conventions tags) :
      ChannelSidecar ctx (.torsionReference frame :: frames) cages fragments conventions
        (.torsion :: tags)
  | cage {annotation : NumberedCageAnnotation V} {frames : List (FrameAnnotation V)}
      {cages : List (NumberedCageAnnotation V)} {fragments : List (FragmentAnnotation V)}
      {conventions : ConventionChannel V} {tags : List CaseShape}
      (certificate : CageGraphBound ctx annotation)
      (rest : ChannelSidecar ctx frames cages fragments conventions tags) :
      ChannelSidecar ctx frames (annotation :: cages) fragments conventions (.cage :: tags)
  | fragment {annotation : FragmentAnnotation V} {frames : List (FrameAnnotation V)}
      {cages : List (NumberedCageAnnotation V)} {fragments : List (FragmentAnnotation V)}
      {conventions : ConventionChannel V} {tags : List CaseShape}
      (rest : ChannelSidecar ctx frames cages fragments conventions tags) :
      ChannelSidecar ctx frames cages (annotation :: fragments) conventions (.fragment :: tags)
  | convention {source : OrganicConventionSource V} {frames : List (FrameAnnotation V)}
      {cages : List (NumberedCageAnnotation V)} {fragments : List (FragmentAnnotation V)}
      {conventions : ConventionChannel V} {tags : List CaseShape}
      (rest : ChannelSidecar ctx frames cages fragments conventions tags) :
      ChannelSidecar ctx frames cages fragments (source :: conventions) (.convention :: tags)

/-- The sidecar over a whole `CaseBundle`, so it can be indexed directly by
`CaseBundle.extractCases state`. -/
abbrev BundleSidecar (ctx : SharedPhysicalContext V) (bundle : CaseBundle V)
    (tags : List CaseShape) : Type u :=
  ChannelSidecar ctx bundle.frames bundle.cages bundle.fragments bundle.conventions tags

namespace ChannelSidecar

variable {ctx : SharedPhysicalContext V}

/-- Decode the actual case records from a channel-indexed sidecar: the payloads come from the
channels, the certificates come from the sidecar. -/
def decode : {frames : List (FrameAnnotation V)} → {cages : List (NumberedCageAnnotation V)} →
    {fragments : List (FragmentAnnotation V)} → {conventions : ConventionChannel V} →
    {tags : List CaseShape} →
    ChannelSidecar ctx frames cages fragments conventions tags → List (PhysicalCase ctx)
  | _, _, _, _, _, .ringPlane (frame := frame) certificate rest =>
      .ringPlane frame certificate :: decode rest
  | _, _, _, _, _, .closedRing (frame := frame) certificate rest =>
      .closedRing frame certificate :: decode rest
  | _, _, _, _, _, .torsion (frame := frame) certificate rest =>
      .torsion frame certificate :: decode rest
  | _, _, _, _, _, .cage (annotation := annotation) certificate rest =>
      .cage annotation certificate :: decode rest
  | _, _, _, _, _, .fragment (annotation := annotation) rest =>
      .fragment annotation :: decode rest
  | _, _, _, _, _, .convention (source := source) rest =>
      .convention source :: decode rest
  | _, _, _, _, _, .nil => []

/-- Encode an arbitrary ordered case collection into the sidecar indexed by its own channel
contributions.  The tags are exactly `cases.map PhysicalCase.shape`, in order. -/
def ofCases : (cases : List (PhysicalCase ctx)) →
    ChannelSidecar ctx (caseFrames cases) (caseCages cases) (caseFragments cases)
      (caseConventions cases) (cases.map PhysicalCase.shape)
  | [] => .nil
  | .ringPlane _frame certificate :: rest =>
      .ringPlane certificate (ofCases rest)
  | .closedRing _frame certificate :: rest =>
      .closedRing certificate (ofCases rest)
  | .torsion _frame certificate :: rest =>
      .torsion certificate (ofCases rest)
  | .cage _annotation certificate :: rest =>
      .cage certificate (ofCases rest)
  | .fragment _annotation :: rest =>
      .fragment (ofCases rest)
  | .convention _source :: rest =>
      .convention (ofCases rest)

/-- The channel-indexed sidecar decodes to exactly the collection that produced it. -/
@[simp] theorem decode_ofCases (cases : List (PhysicalCase ctx)) :
    (ofCases cases).decode = cases := by
  induction cases with
  | nil => rfl
  | cons c cs ih => cases c <;> simp [ofCases, decode, ih]

end ChannelSidecar

/-! ## Adapters from actual independent observations -/

/-- The real ring-plane frame retained for one actual generic ring-plane observation.  The real
plane, the ordered selected support and both substituents are mapped by the same encoding
equivalence; the legacy adapter leaves both attachments absent, so this frame is literally the
`realRingPlane` payload of `physicalRingPlaneObservationToFrame`. -/
noncomputable def ringPlaneFrameOfObservation (ctx : SharedPhysicalContext V)
    (observation : PhysicalRingPlaneObservation ctx.molecule) : RealRingPlaneFrame V where
  plane := observation.plane
  ringAtoms := observation.ringAtoms.map ctx.atomEquiv.symm
  firstSubstituent := ctx.atomEquiv.symm observation.firstSubstituent
  secondSubstituent := ctx.atomEquiv.symm observation.secondSubstituent
  firstAttachment? := none
  secondAttachment? := none

/-- The legacy generic adapter is exactly the `realRingPlane` payload of the frame above. -/
theorem physicalRingPlaneObservationToFrame_eq_frame (ctx : SharedPhysicalContext V)
    (observation : PhysicalRingPlaneObservation ctx.molecule) :
    physicalRingPlaneObservationToFrame ctx.atomEquiv observation =
      .realRingPlane (ringPlaneFrameOfObservation ctx observation) := rfl

/-- The proof-carrying certificate of one actual generic observation.  The certificate contains
only the propositional facts the frame omits.  Coplanarity is *not* invented: the optional field is
the caller's actual `CoplanarRingEvidence`, lifted into `Type`, and `none` remains `none`. -/
noncomputable def ringPlaneCertificateOfObservation (ctx : SharedPhysicalContext V)
    (observation : PhysicalRingPlaneObservation ctx.molecule)
    (agrees : ctx.ObservationAgrees observation)
    (coplanar? : Option (PLift (CoplanarRingEvidence observation)) := none) :
    RingPlaneFrameCertificate ctx (ringPlaneFrameOfObservation ctx observation) where
  ringAtoms_nodup := by
    show ((observation.ringAtoms.map ctx.atomEquiv.symm).map ctx.atomEquiv).Nodup
    rw [List.map_map]
    simpa [Function.comp_def] using observation.ringAtoms_nodup
  ringAtoms_nonempty := by
    show ((observation.ringAtoms.map ctx.atomEquiv.symm).map ctx.atomEquiv) ≠ []
    rw [List.map_map]
    simpa [Function.comp_def] using observation.ringAtoms_nonempty
  substituents_distinct := by
    show ctx.atomEquiv (ctx.atomEquiv.symm observation.firstSubstituent) ≠
      ctx.atomEquiv (ctx.atomEquiv.symm observation.secondSubstituent)
    simpa using observation.substituents_distinct
  firstSubstituent_not_ring := by
    show ctx.atomEquiv (ctx.atomEquiv.symm observation.firstSubstituent) ∉
      (observation.ringAtoms.map ctx.atomEquiv.symm).map ctx.atomEquiv
    rw [List.map_map]
    simpa [Function.comp_def] using observation.firstSubstituent_not_ring
  secondSubstituent_not_ring := by
    show ctx.atomEquiv (ctx.atomEquiv.symm observation.secondSubstituent) ∉
      (observation.ringAtoms.map ctx.atomEquiv.symm).map ctx.atomEquiv
    rw [List.map_map]
    simpa [Function.comp_def] using observation.secondSubstituent_not_ring
  coplanar? := coplanar?.map fun evidence => PLift.up (by
    intro atom member
    have mappedMember : ctx.atomEquiv atom ∈ observation.ringAtoms := by
      obtain ⟨source, sourceMember, sourceEq⟩ := List.mem_map.mp member
      have sourceIs : source = ctx.atomEquiv atom := by
        simpa using congrArg ctx.atomEquiv sourceEq
      simpa [sourceIs] using sourceMember
    have supported := evidence.down.ringSupportInPlane (ctx.atomEquiv atom) mappedMember
    have conformationEq : observation.atomPosition (ctx.atomEquiv atom) =
        ctx.conformation atom := by
      show observation.conformation (ctx.atomEquiv atom) = ctx.conformation atom
      have agreesEq : observation.conformation = ctx.encodedConformation := agrees
      rw [agreesEq]
      simp [SharedPhysicalContext.encodedConformation]
    simpa [ringPlaneFrameOfObservation, conformationEq] using supported)

/-- Build one generic ring-plane case from an actual observation agreeing with the common
conformation.  The returned case retains the observation's plane, ordered support, substituents
and (only if actually supplied) coplanarity evidence; it never claims a closed ring. -/
noncomputable def ringPlaneCaseOfObservation (ctx : SharedPhysicalContext V)
    (observation : PhysicalRingPlaneObservation ctx.molecule)
    (agrees : ctx.ObservationAgrees observation)
    (coplanar? : Option (PLift (CoplanarRingEvidence observation)) := none) : PhysicalCase ctx :=
  .ringPlane (ringPlaneFrameOfObservation ctx observation)
    (ringPlaneCertificateOfObservation ctx observation agrees coplanar?)

/-- Decode a generic ring-plane observation from a frame plus its proof-only certificate.  The
conformation is the common context conformation; ring membership and substituent data are read
back through the same encoding equivalence. -/
def ringPlaneObservationOfFrame (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : RingPlaneFrameCertificate ctx frame) :
    PhysicalRingPlaneObservation ctx.molecule where
  conformation := ctx.encodedConformation
  plane := frame.plane
  ringAtoms := frame.ringAtoms.map ctx.atomEquiv
  ringAtoms_nodup := certificate.ringAtoms_nodup
  ringAtoms_nonempty := certificate.ringAtoms_nonempty
  firstSubstituent := ctx.atomEquiv frame.firstSubstituent
  secondSubstituent := ctx.atomEquiv frame.secondSubstituent
  substituents_distinct := certificate.substituents_distinct
  firstSubstituent_not_ring := certificate.firstSubstituent_not_ring
  secondSubstituent_not_ring := certificate.secondSubstituent_not_ring

/-- The decoded generic observation uses the common context conformation, so it agrees with the
context by construction. -/
theorem ringPlaneObservationOfFrame_agrees (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : RingPlaneFrameCertificate ctx frame) :
    ctx.ObservationAgrees (ringPlaneObservationOfFrame ctx frame certificate) := rfl

/-- The decoded support is exactly the frame's retained support mapped to source indices. -/
@[simp] theorem ringPlaneObservationOfFrame_ringAtoms (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : RingPlaneFrameCertificate ctx frame) :
    (ringPlaneObservationOfFrame ctx frame certificate).ringAtoms =
      frame.ringAtoms.map ctx.atomEquiv := rfl

/-- The decoded plane is exactly the frame's retained plane. -/
@[simp] theorem ringPlaneObservationOfFrame_plane (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : RingPlaneFrameCertificate ctx frame) :
    (ringPlaneObservationOfFrame ctx frame certificate).plane = frame.plane := rfl

/-- The decoded first substituent is the frame's first substituent mapped to source indices. -/
@[simp] theorem ringPlaneObservationOfFrame_firstSubstituent (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : RingPlaneFrameCertificate ctx frame) :
    (ringPlaneObservationOfFrame ctx frame certificate).firstSubstituent =
      ctx.atomEquiv frame.firstSubstituent := rfl

/-- The decoded second substituent is the frame's second substituent mapped to source indices. -/
@[simp] theorem ringPlaneObservationOfFrame_secondSubstituent (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : RingPlaneFrameCertificate ctx frame) :
    (ringPlaneObservationOfFrame ctx frame certificate).secondSubstituent =
      ctx.atomEquiv frame.secondSubstituent := rfl

/-- Coplanarity is only available when the certificate carries the actual proof.  There is no
theorem deriving `CoplanarFrameSupport` from a certificate whose optional field is `none`. -/
theorem RingPlaneFrameCertificate.coplanarSupport {ctx : SharedPhysicalContext V}
    {frame : RealRingPlaneFrame V}
    (certificate : RingPlaneFrameCertificate ctx frame)
    {lifted : PLift (ctx.CoplanarFrameSupport frame)}
    (_present : certificate.coplanar? = some lifted) :
    ctx.CoplanarFrameSupport frame :=
  lifted.down

/-- Fieldwise recovery of the actual generic observation from its own case frame and certificate:
the ordered support is recovered literally, in order and with multiplicity. -/
@[simp] theorem ringPlaneCaseOfObservation_ringAtoms (ctx : SharedPhysicalContext V)
    (observation : PhysicalRingPlaneObservation ctx.molecule)
    (agrees : ctx.ObservationAgrees observation)
    (coplanar? : Option (PLift (CoplanarRingEvidence observation)) := none) :
    (ringPlaneObservationOfFrame ctx (ringPlaneFrameOfObservation ctx observation)
      (ringPlaneCertificateOfObservation ctx observation agrees coplanar?)).ringAtoms =
      observation.ringAtoms := by
  rw [ringPlaneObservationOfFrame_ringAtoms]
  show (observation.ringAtoms.map ctx.atomEquiv.symm).map ctx.atomEquiv =
    observation.ringAtoms
  rw [List.map_map]
  simp [Function.comp_def]

/-- Fieldwise recovery of the observation plane. -/
@[simp] theorem ringPlaneCaseOfObservation_plane (ctx : SharedPhysicalContext V)
    (observation : PhysicalRingPlaneObservation ctx.molecule)
    (agrees : ctx.ObservationAgrees observation)
    (coplanar? : Option (PLift (CoplanarRingEvidence observation)) := none) :
    (ringPlaneObservationOfFrame ctx (ringPlaneFrameOfObservation ctx observation)
      (ringPlaneCertificateOfObservation ctx observation agrees coplanar?)).plane =
      observation.plane := rfl

/-- Fieldwise recovery of the common conformation through the supplied agreement. -/
@[simp] theorem ringPlaneCaseOfObservation_conformation (ctx : SharedPhysicalContext V)
    (observation : PhysicalRingPlaneObservation ctx.molecule)
    (agrees : ctx.ObservationAgrees observation)
    (coplanar? : Option (PLift (CoplanarRingEvidence observation)) := none) :
    (ringPlaneObservationOfFrame ctx (ringPlaneFrameOfObservation ctx observation)
      (ringPlaneCertificateOfObservation ctx observation agrees coplanar?)).conformation =
      observation.conformation :=
  agrees.symm

/-- Extensionality for generic ring-plane observations.  The five data fields determine the
observation; the four remaining fields are proof-irrelevant facts about those data.  The existing
evidence structure does not register an `ext` theorem, so this one is proved explicitly. -/
theorem physicalRingPlaneObservation_ext {molecule : SemanticMolecule}
    {first second : PhysicalRingPlaneObservation molecule}
    (hconf : first.conformation = second.conformation)
    (hplane : first.plane = second.plane)
    (hring : first.ringAtoms = second.ringAtoms)
    (hfirst : first.firstSubstituent = second.firstSubstituent)
    (hsecond : first.secondSubstituent = second.secondSubstituent) :
    first = second := by
  cases first with
  | mk conf plane ringAtoms nodup nonempty firstSubstituent secondSubstituent
      distinct firstNotRing secondNotRing =>
    cases second with
    | mk conf' plane' ringAtoms' nodup' nonempty' firstSubstituent' secondSubstituent'
        distinct' firstNotRing' secondNotRing' =>
      simp only at hconf hplane hring hfirst hsecond
      subst hconf
      subst hplane
      subst hring
      subst hfirst
      subst hsecond
      rfl

/-- Complete inverse for an actual generic ring-plane observation: decoding the frame and
certificate built from the observation returns that very observation, with the ordered support
and both substituents recovered literally.  This is the observation-level inverse behind the
collection inverse; it holds for every supplied observation and every optional actual
coplanarity proof. -/
theorem ringPlaneCaseOfObservation_decode (ctx : SharedPhysicalContext V)
    (observation : PhysicalRingPlaneObservation ctx.molecule)
    (agrees : ctx.ObservationAgrees observation)
    (coplanar? : Option (PLift (CoplanarRingEvidence observation)) := none) :
    ringPlaneObservationOfFrame ctx (ringPlaneFrameOfObservation ctx observation)
      (ringPlaneCertificateOfObservation ctx observation agrees coplanar?) = observation := by
  have hconf := ringPlaneCaseOfObservation_conformation ctx observation agrees coplanar?
  have hplane := ringPlaneCaseOfObservation_plane ctx observation agrees coplanar?
  have hring := ringPlaneCaseOfObservation_ringAtoms ctx observation agrees coplanar?
  have hfirst :
      (ringPlaneObservationOfFrame ctx (ringPlaneFrameOfObservation ctx observation)
        (ringPlaneCertificateOfObservation ctx observation agrees coplanar?)).firstSubstituent =
        observation.firstSubstituent := by
    show ctx.atomEquiv (ctx.atomEquiv.symm observation.firstSubstituent) =
      observation.firstSubstituent
    exact ctx.atomEquiv.apply_symm_apply observation.firstSubstituent
  have hsecond :
      (ringPlaneObservationOfFrame ctx (ringPlaneFrameOfObservation ctx observation)
        (ringPlaneCertificateOfObservation ctx observation agrees coplanar?)).secondSubstituent =
        observation.secondSubstituent := by
    show ctx.atomEquiv (ctx.atomEquiv.symm observation.secondSubstituent) =
      observation.secondSubstituent
    exact ctx.atomEquiv.apply_symm_apply observation.secondSubstituent
  exact physicalRingPlaneObservation_ext hconf hplane hring hfirst hsecond

/-! ## Actual closed-ring cases -/

/-- Build one closed-ring case from an actual `PhysicalClosedRingObservation` agreeing with the
common conformation.  The frame retains the actual real plane, ordered ring support, both
substituents, both selected ring positions and both source-interaction occurrence indices via the
green adapter; the green certificate retains the source ring and the fitted attachment validity.
No assembled state and no desired equality is taken as a premise. -/
noncomputable def closedRingCaseOfObservation (ctx : SharedPhysicalContext V)
    (observation : PhysicalClosedRingObservation ctx.molecule)
    (_agrees : ctx.ObservationAgrees observation.observation) : PhysicalCase ctx :=
  .closedRing (physicalClosedRingObservationToRealRingPlaneFrame ctx.atomEquiv observation)
    (physicalClosedRingObservationToFrameCertificate ctx.atomEquiv observation)

/-- Decode a complete actual closed-ring observation from a frame plus the green certificate.  The
decoded conformation is the common context conformation and the green decoder reads both retained
attachment interactions at their recorded occurrence indices. -/
noncomputable def closedRingObservationOfFrame (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingFrameCertificate ctx frame) :
    PhysicalClosedRingObservation ctx.molecule :=
  RealRingPlaneFrame.toPhysicalClosedRingObservation ctx.atomEquiv
    ctx.encodedConformation frame certificate

/-- The decoded closed-ring observation agrees with the common context conformation. -/
@[simp] theorem closedRingObservationOfFrame_agrees (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingFrameCertificate ctx frame) :
    ctx.ObservationAgrees (closedRingObservationOfFrame ctx frame certificate).observation :=
  rfl

/-- Exact decoded conformation. -/
@[simp] theorem closedRingObservationOfFrame_conformation (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingFrameCertificate ctx frame) :
    (closedRingObservationOfFrame ctx frame certificate).observation.conformation =
      ctx.encodedConformation := rfl

/-- Exact decoded ordered ring support. -/
@[simp] theorem closedRingObservationOfFrame_ringAtoms (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingFrameCertificate ctx frame) :
    (closedRingObservationOfFrame ctx frame certificate).observation.ringAtoms =
      frame.ringAtoms.map ctx.atomEquiv := rfl

/-- Exact decoded real plane. -/
@[simp] theorem closedRingObservationOfFrame_plane (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingFrameCertificate ctx frame) :
    (closedRingObservationOfFrame ctx frame certificate).observation.plane = frame.plane := rfl

/-- Exact decoded first substituent. -/
@[simp] theorem closedRingObservationOfFrame_firstSubstituent (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingFrameCertificate ctx frame) :
    (closedRingObservationOfFrame ctx frame certificate).observation.firstSubstituent =
      ctx.atomEquiv frame.firstSubstituent := rfl

/-- Exact decoded second substituent. -/
@[simp] theorem closedRingObservationOfFrame_secondSubstituent (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingFrameCertificate ctx frame) :
    (closedRingObservationOfFrame ctx frame certificate).observation.secondSubstituent =
      ctx.atomEquiv frame.secondSubstituent := rfl

/-- The decoded source ring is exactly the certificate's actual source ring. -/
@[simp] theorem closedRingObservationOfFrame_ring (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingFrameCertificate ctx frame) :
    (closedRingObservationOfFrame ctx frame certificate).ring = certificate.ring := rfl

/-- The decoded first selected ring position is the frame's retained ring position mapped to the
source index. -/
@[simp] theorem closedRingObservationOfFrame_firstAttachment_ringPosition
    (ctx : SharedPhysicalContext V) (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingFrameCertificate ctx frame) :
    (closedRingObservationOfFrame ctx frame certificate).firstAttachment.ringPosition =
      ctx.atomEquiv certificate.firstAttachment.ringPosition := rfl

/-- The decoded first attachment interaction is the actual source interaction lookup at the
frame's retained occurrence index. -/
@[simp] theorem closedRingObservationOfFrame_firstAttachment_interaction
    (ctx : SharedPhysicalContext V) (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingFrameCertificate ctx frame) :
    (closedRingObservationOfFrame ctx frame certificate).firstAttachment.interaction =
      ctx.molecule.interactions[certificate.firstAttachment.interactionIndex]'
        certificate.firstAttachmentValid.interactionIndex_lt := rfl

/-- The decoded second selected ring position is the frame's retained ring position mapped to the
source index. -/
@[simp] theorem closedRingObservationOfFrame_secondAttachment_ringPosition
    (ctx : SharedPhysicalContext V) (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingFrameCertificate ctx frame) :
    (closedRingObservationOfFrame ctx frame certificate).secondAttachment.ringPosition =
      ctx.atomEquiv certificate.secondAttachment.ringPosition := rfl

/-- The decoded second attachment interaction is the actual source interaction lookup at the
frame's retained occurrence index. -/
@[simp] theorem closedRingObservationOfFrame_secondAttachment_interaction
    (ctx : SharedPhysicalContext V) (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingFrameCertificate ctx frame) :
    (closedRingObservationOfFrame ctx frame certificate).secondAttachment.interaction =
      ctx.molecule.interactions[certificate.secondAttachment.interactionIndex]'
        certificate.secondAttachmentValid.interactionIndex_lt := rfl

/-- The decoded source ring support is exactly the mapped frame support, in order. -/
@[simp] theorem closedRingObservationOfFrame_ringAtoms_ring (ctx : SharedPhysicalContext V)
    (frame : RealRingPlaneFrame V)
    (certificate : ClosedRingFrameCertificate ctx frame) :
    (closedRingObservationOfFrame ctx frame certificate).ring.ringAtoms =
      frame.ringAtoms.map ctx.atomEquiv :=
  certificate.ring_matches

/-- Recovery of the ordered ring support of an actual observation through its closed-ring case. -/
@[simp] theorem closedRingCaseOfObservation_ringAtoms (ctx : SharedPhysicalContext V)
    (observation : PhysicalClosedRingObservation ctx.molecule)
    (_agrees : ctx.ObservationAgrees observation.observation) :
    (closedRingObservationOfFrame ctx
      (physicalClosedRingObservationToRealRingPlaneFrame ctx.atomEquiv observation)
      (physicalClosedRingObservationToFrameCertificate ctx.atomEquiv observation)).observation.ringAtoms =
      observation.observation.ringAtoms := by
  rw [closedRingObservationOfFrame_ringAtoms]
  show (observation.observation.ringAtoms.map ctx.atomEquiv.symm).map ctx.atomEquiv =
    observation.observation.ringAtoms
  rw [List.map_map]
  simp [Function.comp_def]

/-- Recovery of the first substituent of an actual observation through its closed-ring case. -/
@[simp] theorem closedRingCaseOfObservation_firstSubstituent (ctx : SharedPhysicalContext V)
    (observation : PhysicalClosedRingObservation ctx.molecule)
    (_agrees : ctx.ObservationAgrees observation.observation) :
    (closedRingObservationOfFrame ctx
      (physicalClosedRingObservationToRealRingPlaneFrame ctx.atomEquiv observation)
      (physicalClosedRingObservationToFrameCertificate ctx.atomEquiv observation)).observation.firstSubstituent =
      observation.observation.firstSubstituent := by
  rw [closedRingObservationOfFrame_firstSubstituent]
  exact Equiv.apply_symm_apply ctx.atomEquiv _

/-- Recovery of the second substituent of an actual observation through its closed-ring case. -/
@[simp] theorem closedRingCaseOfObservation_secondSubstituent (ctx : SharedPhysicalContext V)
    (observation : PhysicalClosedRingObservation ctx.molecule)
    (_agrees : ctx.ObservationAgrees observation.observation) :
    (closedRingObservationOfFrame ctx
      (physicalClosedRingObservationToRealRingPlaneFrame ctx.atomEquiv observation)
      (physicalClosedRingObservationToFrameCertificate ctx.atomEquiv observation)).observation.secondSubstituent =
      observation.observation.secondSubstituent := by
  rw [closedRingObservationOfFrame_secondSubstituent]
  exact Equiv.apply_symm_apply ctx.atomEquiv _

/-- Recovery of the common conformation of an actual observation: the decoded conformation is the
context conformation, which equals the observation's own conformation by the supplied agreement. -/
@[simp] theorem closedRingCaseOfObservation_conformation (ctx : SharedPhysicalContext V)
    (observation : PhysicalClosedRingObservation ctx.molecule)
    (agrees : ctx.ObservationAgrees observation.observation) :
    (closedRingObservationOfFrame ctx
      (physicalClosedRingObservationToRealRingPlaneFrame ctx.atomEquiv observation)
      (physicalClosedRingObservationToFrameCertificate ctx.atomEquiv observation)).observation.conformation =
      observation.observation.conformation :=
  agrees.symm

/-- Recovery of the first selected ring position of an actual observation. -/
@[simp] theorem closedRingCaseOfObservation_firstAttachment_ringPosition
    (ctx : SharedPhysicalContext V)
    (observation : PhysicalClosedRingObservation ctx.molecule)
    (_agrees : ctx.ObservationAgrees observation.observation) :
    (closedRingObservationOfFrame ctx
      (physicalClosedRingObservationToRealRingPlaneFrame ctx.atomEquiv observation)
      (physicalClosedRingObservationToFrameCertificate ctx.atomEquiv observation)).firstAttachment.ringPosition =
      observation.firstAttachment.ringPosition := by
  rw [closedRingObservationOfFrame_firstAttachment_ringPosition]
  exact Equiv.apply_symm_apply ctx.atomEquiv _

/-- Recovery of the first actual attachment interaction value of an actual observation.  The
adapter's chosen occurrence index is used, not a preselected duplicate identity. -/
@[simp] theorem closedRingCaseOfObservation_firstAttachment_interaction
    (ctx : SharedPhysicalContext V)
    (observation : PhysicalClosedRingObservation ctx.molecule)
    (_agrees : ctx.ObservationAgrees observation.observation) :
    (closedRingObservationOfFrame ctx
      (physicalClosedRingObservationToRealRingPlaneFrame ctx.atomEquiv observation)
      (physicalClosedRingObservationToFrameCertificate ctx.atomEquiv observation)).firstAttachment.interaction =
      observation.firstAttachment.interaction := by
  rw [closedRingObservationOfFrame_firstAttachment_interaction]
  exact sourceInteractionIndex_get observation.firstAttachment.interaction
    observation.firstAttachment.interaction_mem

/-- Recovery of the second selected ring position of an actual observation. -/
@[simp] theorem closedRingCaseOfObservation_secondAttachment_ringPosition
    (ctx : SharedPhysicalContext V)
    (observation : PhysicalClosedRingObservation ctx.molecule)
    (_agrees : ctx.ObservationAgrees observation.observation) :
    (closedRingObservationOfFrame ctx
      (physicalClosedRingObservationToRealRingPlaneFrame ctx.atomEquiv observation)
      (physicalClosedRingObservationToFrameCertificate ctx.atomEquiv observation)).secondAttachment.ringPosition =
      observation.secondAttachment.ringPosition := by
  rw [closedRingObservationOfFrame_secondAttachment_ringPosition]
  exact Equiv.apply_symm_apply ctx.atomEquiv _

/-- Recovery of the second actual attachment interaction value of an actual observation. -/
@[simp] theorem closedRingCaseOfObservation_secondAttachment_interaction
    (ctx : SharedPhysicalContext V)
    (observation : PhysicalClosedRingObservation ctx.molecule)
    (_agrees : ctx.ObservationAgrees observation.observation) :
    (closedRingObservationOfFrame ctx
      (physicalClosedRingObservationToRealRingPlaneFrame ctx.atomEquiv observation)
      (physicalClosedRingObservationToFrameCertificate ctx.atomEquiv observation)).secondAttachment.interaction =
      observation.secondAttachment.interaction := by
  rw [closedRingObservationOfFrame_secondAttachment_interaction]
  exact sourceInteractionIndex_get observation.secondAttachment.interaction
    observation.secondAttachment.interaction_mem

/-- The source ring recovered from an actual observation's closed-ring case is exactly the
observation's own source ring, including its ordered atom list and bond witnesses. -/
@[simp] theorem closedRingCaseOfObservation_ring (ctx : SharedPhysicalContext V)
    (observation : PhysicalClosedRingObservation ctx.molecule)
    (_agrees : ctx.ObservationAgrees observation.observation) :
    (closedRingObservationOfFrame ctx
      (physicalClosedRingObservationToRealRingPlaneFrame ctx.atomEquiv observation)
      (physicalClosedRingObservationToFrameCertificate ctx.atomEquiv observation)).ring =
      observation.ring := rfl

/-- The complete fieldwise inverse content of an actual closed-ring observation: every piece of
data the observation carries is recovered from the case frame and the green certificate.  The
attachment fields are indexed by the recovered observation and ring, so this records their
recovered data without pretending the two structures are syntactically identical. -/
structure ClosedRingRecovery (ctx : SharedPhysicalContext V)
    (observation : PhysicalClosedRingObservation ctx.molecule)
    (decoded : PhysicalClosedRingObservation ctx.molecule) : Prop where
  observation_conformation :
    decoded.observation.conformation = observation.observation.conformation
  observation_plane : decoded.observation.plane = observation.observation.plane
  observation_ringAtoms : decoded.observation.ringAtoms = observation.observation.ringAtoms
  observation_firstSubstituent :
    decoded.observation.firstSubstituent = observation.observation.firstSubstituent
  observation_secondSubstituent :
    decoded.observation.secondSubstituent = observation.observation.secondSubstituent
  ring : decoded.ring = observation.ring
  firstAttachment_ringPosition :
    decoded.firstAttachment.ringPosition = observation.firstAttachment.ringPosition
  firstAttachment_interaction :
    decoded.firstAttachment.interaction = observation.firstAttachment.interaction
  secondAttachment_ringPosition :
    decoded.secondAttachment.ringPosition = observation.secondAttachment.ringPosition
  secondAttachment_interaction :
    decoded.secondAttachment.interaction = observation.secondAttachment.interaction

/-- Actual closed-ring observation inverse: decoding the case built from the observation recovers
all its structure carried by the common source graph, the selected ring positions and both
interaction values. -/
theorem closedRingCaseOfObservation_recovery (ctx : SharedPhysicalContext V)
    (observation : PhysicalClosedRingObservation ctx.molecule)
    (agrees : ctx.ObservationAgrees observation.observation) :
    ClosedRingRecovery ctx observation
      (closedRingObservationOfFrame ctx
        (physicalClosedRingObservationToRealRingPlaneFrame ctx.atomEquiv observation)
        (physicalClosedRingObservationToFrameCertificate ctx.atomEquiv observation)) where
  observation_conformation :=
    closedRingCaseOfObservation_conformation ctx observation agrees
  observation_plane :=
    closedRingObservationOfFrame_plane ctx _ _
  observation_ringAtoms :=
    closedRingCaseOfObservation_ringAtoms ctx observation agrees
  observation_firstSubstituent :=
    closedRingCaseOfObservation_firstSubstituent ctx observation agrees
  observation_secondSubstituent :=
    closedRingCaseOfObservation_secondSubstituent ctx observation agrees
  ring := closedRingCaseOfObservation_ring ctx observation agrees
  firstAttachment_ringPosition :=
    closedRingCaseOfObservation_firstAttachment_ringPosition ctx observation agrees
  firstAttachment_interaction :=
    closedRingCaseOfObservation_firstAttachment_interaction ctx observation agrees
  secondAttachment_ringPosition :=
    closedRingCaseOfObservation_secondAttachment_ringPosition ctx observation agrees
  secondAttachment_interaction :=
    closedRingCaseOfObservation_secondAttachment_interaction ctx observation agrees

/-! ## Remaining case constructors -/

/-- One torsion case from an actual frame and its inventory-binding certificate. -/
def torsionCaseOfFrame (ctx : SharedPhysicalContext V) (frame : TorsionReferenceFrame V)
    (certificate : TorsionFrameCertificate ctx frame) : PhysicalCase ctx :=
  .torsion frame certificate

/-- Every selected electronic site of a torsion case is bound to the same present inventory. -/
theorem torsionCaseOfFrame_site_matches (ctx : SharedPhysicalContext V)
    (frame : TorsionReferenceFrame V)
    (certificate : TorsionFrameCertificate ctx frame) :
    ∀ site : SelectedElectronicSite V,
      (frame.frontSite? = some site ∨ frame.rearSite? = some site) →
        ∀ channel : ElectronicChannel V, ctx.electronic? = some channel →
          site.MatchesInventory channel.counts :=
  certificate.site_matches

/-- Actual selected-site torsion construction from a present electronic inventory.  Both site slots
are the green `selectedSiteOfIndependent` sites of actual `IndependentSiteIdentity` witnesses of
the *present* channel; frame validity is the green `torsionFrameWithSelectedSites_valid` theorem,
and inventory compatibility is inherited from the same present channel.  No site is invented when
the inventory is absent, and no prebuilt certificate is required. -/
def torsionCaseOfPresentInventory (ctx : SharedPhysicalContext V)
    (channel : ElectronicChannel V) (present : ctx.electronic? = some channel)
    (axisPath : List V) (front rear : BlueBookP94.TorsionParticipant V)
    (frontIdentity rearIdentity : IndependentSiteIdentity channel.counts)
    (frontOwner : frontIdentity.owner = SelectedElectronicSite.participantOwner front)
    (frontKind : ∀ kind, SelectedElectronicSite.participantSiteKind? front = some kind →
      frontIdentity.kind = kind)
    (rearOwner : rearIdentity.owner = SelectedElectronicSite.participantOwner rear)
    (rearKind : ∀ kind, SelectedElectronicSite.participantSiteKind? rear = some kind →
      rearIdentity.kind = kind) :
    PhysicalCase ctx :=
  .torsion
    (torsionFrameWithSelectedSites channel.counts axisPath front rear
      frontIdentity rearIdentity)
    { valid := torsionFrameWithSelectedSites_valid channel.counts axisPath front rear
        frontIdentity rearIdentity frontOwner frontKind rearOwner rearKind
      sites_present := by
        intro _selected
        exact ⟨channel, present⟩
      site_matches := by
        intro site member channel' channelEq
        have sameChannel : channel' = channel := by
          have : some channel' = some channel := channelEq.symm.trans present
          exact Option.some.inj this
        rw [sameChannel]
        rcases member with frontMember | rearMember
        · have siteEq : site =
              selectedSiteOfIndependent channel.counts frontIdentity := by
            have assembled : some (selectedSiteOfIndependent channel.counts frontIdentity) =
                some site := by
              simpa [torsionFrameWithSelectedSites] using frontMember
            exact (Option.some.inj assembled).symm
          rw [siteEq]
          exact selectedSiteOfIndependent_matchesInventory channel.counts frontIdentity
        · have siteEq : site =
              selectedSiteOfIndependent channel.counts rearIdentity := by
            have assembled : some (selectedSiteOfIndependent channel.counts rearIdentity) =
                some site := by
              simpa [torsionFrameWithSelectedSites] using rearMember
            exact (Option.some.inj assembled).symm
          rw [siteEq]
          exact selectedSiteOfIndependent_matchesInventory channel.counts rearIdentity }

/-- One numbered-cage case.  The certificate only backs the annotation's edges and addend
interactions by actual carrier interactions; it makes no geometric claim. -/
def cageCaseOfAnnotation (ctx : SharedPhysicalContext V)
    (annotation : NumberedCageAnnotation V)
    (certificate : CageGraphBound ctx annotation) : PhysicalCase ctx :=
  .cage annotation certificate

/-- One fragment case: the annotation is retained literally. -/
def fragmentCaseOfAnnotation (ctx : SharedPhysicalContext V)
    (annotation : FragmentAnnotation V) : PhysicalCase ctx :=
  .fragment annotation

/-- One convention case: the convention source is retained literally and in order. -/
def conventionCaseOfSource (ctx : SharedPhysicalContext V)
    (source : OrganicConventionSource V) : PhysicalCase ctx :=
  .convention source

/-! ## Source-bound residue ingress on the same encoded graph -/

/-- A residue ingress bound to the base state's own certified encoding.  The ledger is indexed by
`base.graph.certifiedEncoding enumeration`, the same encoded graph used by the physical context and
by the assembled state, so every link endpoint is a participant of an actual base-graph
interaction. -/
structure ResidueIngress (Locant : Type v) (base : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V)) where
  /-- The locant codec used to encode and decode the ledger. -/
  codec : LocantCodec Locant
  /-- The actual source-bound residue ledger. -/
  ledger : ResidueIncidenceLedger Locant (base.graph.certifiedEncoding enumeration)
  /-- The locant cover of the ledger. -/
  cover : LocantCover ledger

namespace ResidueIngress

variable {base : WholeState V E B} {enumeration : V ≃ Fin (Fintype.card V)}

/-- Structure extensionality for a residue ingress: the cover is typed by the ledger, so its
comparison is heterogeneous and becomes an equality once the ledgers are identified. -/
theorem ext {first second : ResidueIngress Locant base enumeration}
    (codec : first.codec = second.codec) (ledger : first.ledger = second.ledger)
    (cover : HEq first.cover second.cover) : first = second := by
  cases first with
  | mk firstCodec firstLedger firstCover =>
    cases second with
    | mk secondCodec secondLedger secondCover =>
      simp only at codec ledger
      subst codec
      subst ledger
      have coverEq : firstCover = secondCover := eq_of_heq cover
      subst coverEq
      rfl

/-- The actual residue channel attached to the state.  It is the green source-bound channel; the
ordering and multiplicity of links are retained and the atom equivalence is the same
`encodedAtomEquiv` used by every other field. -/
def channel (ingress : ResidueIngress Locant base enumeration) : ResidueLedgerChannel V :=
  sourceBoundChannel ingress.codec enumeration base ingress.ledger ingress.cover

/-- The attached channel's residue count is the ledger's residue count. -/
@[simp] theorem channel_residueCount (ingress : ResidueIngress Locant base enumeration) :
    ingress.channel.residueCount = ingress.ledger.residueCount :=
  sourceBoundChannel_residueCount ingress.codec enumeration base ingress.ledger ingress.cover

/-- Decoding the attached annotation with the same codec and enumeration recovers exactly the
ledger's observable view. -/
@[simp] theorem channel_decodeView (ingress : ResidueIngress Locant base enumeration) :
    decodeView? ingress.codec (encodedAtomEquiv base.graph enumeration)
        ingress.channel.annotation =
      some (viewOfLedger ingress.ledger) :=
  sourceBoundChannel_decodeView ingress.codec enumeration base ingress.ledger ingress.cover

/-- Full dependent reconstruction of the supplied ledger from the attached channel plus the
proof-only source-bound validity certificate; the ledger payload is not stored in the state. -/
theorem channel_reconstruct (ingress : ResidueIngress Locant base enumeration) :
    ∃ view : ResidueLedgerView Locant
        (base.graph.certifiedEncoding enumeration).input.molecule.atomCount
        (base.graph.certifiedEncoding enumeration).input.molecule.interactions.length
        ingress.ledger.residueCount,
      decodeView? ingress.codec (encodedAtomEquiv base.graph enumeration)
          ingress.channel.annotation = some view ∧
      ∃ valid : SourceBoundViewValidity (Locant := Locant) base.graph enumeration view,
        viewToLedger view valid.link_source_mem valid.link_target_mem = ingress.ledger :=
  sourceBoundChannel_reconstruct ingress.codec enumeration base ingress.ledger ingress.cover

/-- Every link of the ingress ledger binds its source endpoint to a participant of the actual
base-graph interaction occurrence named by the link. -/
theorem endpoint_bound (ingress : ResidueIngress Locant base enumeration)
    {link : DirectedResidueLink Locant (Fin ingress.ledger.residueCount)
      (base.graph.certifiedEncoding enumeration).input.molecule.interactions.length}
    (member : link ∈ ingress.ledger.links) :
    ∃ atom : Fin (base.graph.certifiedEncoding enumeration).input.molecule.atomCount,
      (ingress.ledger.residue link.source).incidence link.sourceLocant = some atom ∧
        sourceAtomOfEncoded base.graph enumeration atom ∈
          (base.graph.interactions.get
            (residueSourceInteractionIndex base.graph enumeration link.interaction)).1 :=
  sourceBound_ledger_link_source_correct enumeration base ingress.ledger member

end ResidueIngress

/-! ## Packed encoded residue metadata

The packed residue metadata is indexed by the *actual* residue channel of the assembled state.
It stores no view and no ledger.  It retains only the locant codec, the interaction-count alignment
of the channel, the raw locant cover lists (with their duplicate-freeness proofs), and two
functions that are applied at decode time to the view actually obtained by `decodeView?` from the
state's own channel annotation.  The first function supplies the source-bound validity certificate
for that decoded view; the second supplies the cover-completeness proof for the ledger reconstructed
from that view.  Thus the raw ledger payload is not copied into the output. -/
structure PackedResidue (Locant : Type v) (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (channel : ResidueLedgerChannel V) where
  /-- The locant codec used to decode the channel annotation. -/
  codec : LocantCodec Locant
  /-- The channel's interaction budget is the encoded source interaction-list length. -/
  count_eq : channel.interactionCount =
    (graph.certifiedEncoding enumeration).input.molecule.interactions.length
  /-- The raw locant cover lists, one per residue. -/
  cover : Fin channel.residueCount → List Locant
  /-- Each retained cover list is duplicate-free. -/
  cover_nodup : ∀ index, (cover index).Nodup
  /-- Source-bound validity for the view actually decoded from the state channel. -/
  validOf : (view : ResidueLedgerView Locant
        (graph.certifiedEncoding enumeration).input.molecule.atomCount
        (graph.certifiedEncoding enumeration).input.molecule.interactions.length
        channel.residueCount) →
      decodeView? codec (encodedAtomEquiv graph enumeration)
        (count_eq ▸ channel.annotation) = some view →
      SourceBoundViewValidity (Locant := Locant) graph enumeration view
  /-- Cover completeness for the ledger reconstructed from that decoded view. -/
  coversOf : (view : ResidueLedgerView Locant
        (graph.certifiedEncoding enumeration).input.molecule.atomCount
        (graph.certifiedEncoding enumeration).input.molecule.interactions.length
        channel.residueCount) →
      (decoded : decodeView? codec (encodedAtomEquiv graph enumeration)
        (count_eq ▸ channel.annotation) = some view) →
      (valid : SourceBoundViewValidity (Locant := Locant) graph enumeration view) →
      ∀ (index : Fin channel.residueCount) (locant : Locant)
        (atom : Fin (graph.certifiedEncoding enumeration).input.molecule.atomCount),
        ((viewToLedger view valid.link_source_mem valid.link_target_mem).residue index).incidence
            locant = some atom →
          locant ∈ cover index

namespace PackedResidue

variable {graph : FiniteAtomInteractionHypergraph V}
variable {enumeration : V ≃ Fin (Fintype.card V)}
variable {channel : ResidueLedgerChannel V}

/-- The view decoded by `decodeView?` from the actual channel annotation retained in the state. -/
noncomputable def decodedView? (packed : PackedResidue Locant graph enumeration channel) :
    Option (ResidueLedgerView Locant
      (graph.certifiedEncoding enumeration).input.molecule.atomCount
      (graph.certifiedEncoding enumeration).input.molecule.interactions.length
      channel.residueCount) :=
  decodeView? packed.codec (encodedAtomEquiv graph enumeration)
    (packed.count_eq ▸ channel.annotation)

/-- Rebuild the full residue ingress from the decoded view plus the packed metadata.  The ledger is
reconstructed from the view and the validity certificate; the cover's data and proofs are the
retained metadata and the cover-completeness proof for that same ledger. -/
noncomputable def toIngress (base : WholeState V E B)
    (packed : PackedResidue Locant base.graph enumeration channel)
    (view : ResidueLedgerView Locant
      (base.graph.certifiedEncoding enumeration).input.molecule.atomCount
      (base.graph.certifiedEncoding enumeration).input.molecule.interactions.length
      channel.residueCount)
    (decoded : packed.decodedView? = some view) :
    ResidueIngress Locant base enumeration :=
  let valid := packed.validOf view decoded
  { codec := packed.codec
    ledger := viewToLedger view valid.link_source_mem valid.link_target_mem
    cover :=
      { cover := packed.cover
        nodup := packed.cover_nodup
        covers := packed.coversOf view decoded valid } }

/-- `viewToLedger` at the observable view of a ledger returns that ledger for *any* participant
certificates of the same endpoints: the participant fields are propositions and do not affect the
ledger's data fields. -/
theorem viewToLedger_viewOfLedger_any {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Locant input)
    (link_source_mem : ∀ link ∈ (viewOfLedger ledger).links,
      ∃ atom : Fin input.input.molecule.atomCount,
        ((viewOfLedger ledger).residue link.source).incidence link.sourceLocant = some atom ∧
          atom.val ∈ (input.input.molecule.interactions.get link.interaction).participants)
    (link_target_mem : ∀ link ∈ (viewOfLedger ledger).links,
      ∃ atom : Fin input.input.molecule.atomCount,
        ((viewOfLedger ledger).residue link.target).incidence link.targetLocant = some atom ∧
          atom.val ∈ (input.input.molecule.interactions.get link.interaction).participants) :
    viewToLedger (viewOfLedger ledger) link_source_mem link_target_mem = ledger := by
  cases ledger with
  | mk residueCount residue links sourceMem targetMem hierarchy =>
    simp [viewOfLedger, viewToLedger]

/-- At the observable view, reconstructing the ledger with any participant certificates gives back
the original ledger's residue incidences.  This avoids rewriting a ledger equality in a proof whose
index is typed by the channel's (definitionally equal) residue count. -/
private theorem residue_incidence_of_viewToLedger_viewOfLedger
    {input : CertifiedAuthoritativeChemicalInput}
    (ledger : ResidueIncidenceLedger Locant input)
    (link_source_mem : ∀ link ∈ (viewOfLedger ledger).links,
      ∃ atom : Fin input.input.molecule.atomCount,
        ((viewOfLedger ledger).residue link.source).incidence link.sourceLocant = some atom ∧
          atom.val ∈ (input.input.molecule.interactions.get link.interaction).participants)
    (link_target_mem : ∀ link ∈ (viewOfLedger ledger).links,
      ∃ atom : Fin input.input.molecule.atomCount,
        ((viewOfLedger ledger).residue link.target).incidence link.targetLocant = some atom ∧
          atom.val ∈ (input.input.molecule.interactions.get link.interaction).participants)
    {index : Fin ledger.residueCount} {locant : Locant}
    {atom : Fin input.input.molecule.atomCount}
    (found : ((viewToLedger (viewOfLedger ledger) link_source_mem
      link_target_mem).residue index).incidence locant = some atom) :
    (ledger.residue index).incidence locant = some atom := by
  cases ledger with
  | mk residueCount residue links sourceMem targetMem hierarchy =>
    simpa [viewOfLedger, viewToLedger] using found

/-- Encode a genuine source-bound ingress into the packed metadata.  The view is not stored: the
functions recover, from whatever view the decoder obtains, the validity and cover facts of the
original ledger. -/
noncomputable def ofIngress {base : WholeState V E B}
    (ingress : ResidueIngress Locant base enumeration) :
    PackedResidue Locant base.graph enumeration ingress.channel where
  codec := ingress.codec
  count_eq := rfl
  cover := ingress.cover.cover
  cover_nodup := ingress.cover.nodup
  validOf := by
    intro view decoded
    have original := ResidueIngress.channel_decodeView ingress
    have viewEq : view = viewOfLedger ingress.ledger := by
      have : some (viewOfLedger ingress.ledger) = some view := by
        rw [← original]
        exact decoded
      exact (Option.some.inj this).symm
    subst viewEq
    exact sourceBoundViewValidityOfLedger base.graph enumeration ingress.ledger
  coversOf := by
    intro view decoded valid index locant atom found
    have original := ResidueIngress.channel_decodeView ingress
    have viewEq : view = viewOfLedger ingress.ledger := by
      have : some (viewOfLedger ingress.ledger) = some view := by
        rw [← original]
        exact decoded
      exact (Option.some.inj this).symm
    subst viewEq
    exact ingress.cover.covers index locant atom
      (residue_incidence_of_viewToLedger_viewOfLedger ingress.ledger valid.link_source_mem
        valid.link_target_mem found)

/-- The canonical decoded view of the packing of a genuine ingress is that ingress's observable
ledger view. -/
@[simp] theorem decodedView_ofIngress {base : WholeState V E B}
    (ingress : ResidueIngress Locant base enumeration) :
    (ofIngress ingress).decodedView? = some (viewOfLedger ingress.ledger) := by
  simp [decodedView?, ofIngress]

/-- Comparing two `LocantCover`s at the same ledger only requires comparing their raw cover lists;
the duplicate-free and completeness fields are propositions. -/
private theorem locantCover_eq_of_cover_eq {input : CertifiedAuthoritativeChemicalInput}
    {ledger : ResidueIncidenceLedger Locant input} {first second : LocantCover ledger}
    (h : first.cover = second.cover) : first = second := by
  cases first with
  | mk firstCover firstNodup firstCovers =>
    cases second with
    | mk secondCover secondNodup secondCovers =>
      simp only at h
      cases h
      simp

/-- The reconstructed ingress of a packed genuine ingress is exactly the original ingress: the
decoded view is the original ledger's observable view, the validity proof is proof-irrelevant, and
the cover is recovered exactly. -/
theorem toIngress_ofIngress {base : WholeState V E B}
    (ingress : ResidueIngress Locant base enumeration)
    (decoded : (ofIngress ingress).decodedView? = some (viewOfLedger ingress.ledger)) :
    toIngress base (ofIngress ingress) (viewOfLedger ingress.ledger) decoded = ingress := by
  have decodedEq : decoded = decodedView_ofIngress ingress := Subsingleton.elim _ _
  rw [decodedEq]
  cases ingress with
  | mk codec ledger cover =>
    have hled : (toIngress base (ofIngress ⟨codec, ledger, cover⟩)
        (viewOfLedger ledger) (decodedView_ofIngress ⟨codec, ledger, cover⟩)).ledger =
        ledger := by
      simp only [toIngress]
      exact viewToLedger_viewOfLedger_any ledger _ _
    cases hled
    apply ResidueIngress.ext
    · rfl
    · rfl
    · apply heq_of_eq
      exact locantCover_eq_of_cover_eq rfl

end PackedResidue

/-- The residue sidecar indexed by the *actual* residue-channel option of the assembled state.
The `none` constructor records that the state carries no residue channel; the `some` constructor
carries the packed metadata for exactly the channel the state carries. -/
inductive PackedResidueMeta (Locant : Type v) (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    Option (ResidueLedgerChannel V) → Type (max u v) where
  | none : PackedResidueMeta Locant graph enumeration none
  | some {channel : ResidueLedgerChannel V}
      (packed : PackedResidue Locant graph enumeration channel) :
      PackedResidueMeta Locant graph enumeration (some channel)

namespace PackedResidueMeta

variable {graph : FiniteAtomInteractionHypergraph V}
variable {enumeration : V ≃ Fin (Fintype.card V)}

/-- Rebuild the residue ingress from the state-indexed packed metadata.  The metadata's type index
is exactly the residue-channel option of the packed state, so the `some` node carries a
`PackedResidue` indexed by the state's own channel; the observable view is decoded from that
channel's annotation, and the ingress is rebuilt from the decoded view plus the proof-only validity
and cover metadata.  No view and no ledger are read from storage. -/
noncomputable def toIngress? {base : WholeState V E B}
    {channelOption : Option (ResidueLedgerChannel V)}
    (packedMeta : PackedResidueMeta Locant base.graph enumeration channelOption) :
    Option (ResidueIngress Locant base enumeration) :=
  match packedMeta with
  | PackedResidueMeta.none => Option.none
  | PackedResidueMeta.some packedResidue =>
      match hview : packedResidue.decodedView? with
      | Option.some view =>
          Option.some (PackedResidue.toIngress base packedResidue view hview)
      | Option.none => Option.none

/-- Rebuilding is invariant under transport of the metadata's type index: the `none` node carries no
data and the result type does not depend on the index. -/
theorem toIngress?_irrel {base : WholeState V E B}
    {channelOption₁ channelOption₂ : Option (ResidueLedgerChannel V)}
    (h : channelOption₁ = channelOption₂)
    (packedMeta : PackedResidueMeta Locant base.graph enumeration channelOption₁) :
    toIngress? (base := base) (h ▸ packedMeta) = toIngress? (base := base) packedMeta := by
  cases h
  rfl

/-- Rebuilding from the packed image of a genuine ingress returns exactly that ingress: the decoded
view is the original ledger's observable view and the proof-only metadata reconstructs the original
ledger and cover. -/
@[simp] theorem toIngress?_ofIngress {base : WholeState V E B}
    (ingress : ResidueIngress Locant base enumeration) :
    toIngress? (base := base)
        (PackedResidueMeta.some (PackedResidue.ofIngress ingress)) = Option.some ingress := by
  simp only [toIngress?]
  split
  · rename_i view hview
    have canonical := PackedResidue.decodedView_ofIngress ingress
    have viewEq : view = viewOfLedger ingress.ledger := by
      apply Option.some.inj
      rw [← hview, canonical]
    cases viewEq
    rw [PackedResidue.toIngress_ofIngress ingress hview]
  · rename_i hview
    rw [PackedResidue.decodedView_ofIngress] at hview
    cases hview

end PackedResidueMeta

/-- The explicit packed output of a shared case request at a fixed base.  It contains the actual
assembled state, the single enumeration, the ordered interleaving tags, a certificate sidecar
indexed by the *actual* case channels extracted from `state`, and residue metadata indexed by the
actual residue-channel option of `state`.  Neither the raw ordered case list nor the raw ledger
payload is stored.  The sidecar is required because a `WholeState` alone loses the interleaving and
the optional coplanarity presence. -/
structure PackedIngress (Locant : Type v) (base : WholeState V E B) where
  /-- The single common enumeration. -/
  enumeration : V ≃ Fin (Fintype.card V)
  /-- The actual assembled whole state. -/
  state : WholeState V E B
  /-- The ordered interleaving tags (one per case). -/
  tags : List CaseShape
  /-- The certificate sidecar, indexed by the state's own extracted case channels. -/
  sidecar : BundleSidecar (SharedPhysicalContext.ofState base enumeration)
    (CaseBundle.extractCases state) tags
  /-- Residue metadata, indexed by the state's own residue-channel option. -/
  residueMeta : PackedResidueMeta Locant base.graph enumeration state.residueLedger?

/-! ## One common-source ingress request and its assembly -/

/-- A minimal shared physical case request.  It supplies the genuine ingress substrate `base`, one
encoding enumeration, an arbitrary ordered list of independently supplied cases indexed by the
canonical context `SharedPhysicalContext.ofState base enumeration`, and an optional residue ingress
bound to the same encoded graph.  The empty-channel hypotheses are exactly the conditions needed to
recover the base state from the assembled output; no assembled state and no round-trip equality is
assumed. -/
structure SharedCaseRequest (Locant : Type v) (base : WholeState V E B) where
  /-- The single common enumeration. -/
  enumeration : V ≃ Fin (Fintype.card V)
  /-- The arbitrary ordered independent case collection. -/
  cases : List (PhysicalCase (SharedPhysicalContext.ofState base enumeration))
  /-- Optional source-bound residue ledger on the same encoded graph. -/
  residue? : Option (ResidueIngress Locant base enumeration) := none
  /-- The base supplies no prior case metadata, so attachment is an exact inverse. -/
  empty : CaseChannelsEmpty base
  /-- The base supplies no prior residue ledger, so residue attachment is an exact inverse. -/
  residue_empty : base.residueLedger? = none

namespace SharedCaseRequest

variable {base : WholeState V E B}

/-- The canonical shared physical context of the request. -/
def context (request : SharedCaseRequest Locant base) : SharedPhysicalContext V :=
  SharedPhysicalContext.ofState base request.enumeration

/-- The graph of the request context is literally the base graph. -/
@[simp] theorem context_graph (request : SharedCaseRequest Locant base) :
    request.context.graph = base.graph := rfl

/-- The inventory of the request context is literally the base inventory. -/
@[simp] theorem context_electronic? (request : SharedCaseRequest Locant base) :
    request.context.electronic? = base.electronic? := rfl

/-- The conformation of the request context is literally the base conformation. -/
@[simp] theorem context_conformation (request : SharedCaseRequest Locant base) :
    request.context.conformation = base.conformation := rfl

/-- The certified encoding of the complete ordered collection. -/
def encoded (request : SharedCaseRequest Locant base) : EncodedCollection request.context :=
  EncodedCollection.encode request.cases

/-- The ordered case bundle derived from the collection. -/
def caseBundle (request : SharedCaseRequest Locant base) : CaseBundle V :=
  bundleOfCases request.cases

/-- The four-channel attachment of the collection, before any residue ingress. -/
def assembleCaseChannels (request : SharedCaseRequest Locant base) : WholeState V E B :=
  assembleCases base request.cases

/-- The actual assembled ingress: attach the whole ordered case bundle, then (if supplied) attach
the source-bound residue ledger on the same encoded graph. -/
def assemble (request : SharedCaseRequest Locant base) : WholeState V E B :=
  match request.residue? with
  | none => request.assembleCaseChannels
  | some ingress =>
      attachSourceBoundResidueLedger request.assembleCaseChannels ingress.channel

/-- Case channels of an assembled state are exactly the request's ordered channels. -/
@[simp] theorem assembleCaseChannels_extractCases (request : SharedCaseRequest Locant base) :
    CaseBundle.extractCases request.assembleCaseChannels = request.caseBundle := by
  simp [assembleCaseChannels, caseBundle, assembleCases]

/-- Residue attachment does not change the four case channels. -/
@[simp] theorem extractCases_attachSourceBoundResidueLedger (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    CaseBundle.extractCases (attachSourceBoundResidueLedger state channel) =
      CaseBundle.extractCases state := by
  apply CaseBundle.extEq <;>
    simp [CaseBundle.extractCases, attachSourceBoundResidueLedger, withResidueLedger]

/-- Case channels of the final assembled state are still exactly the request's ordered channels,
including every duplicate occurrence. -/
@[simp] theorem assemble_extractedCases (request : SharedCaseRequest Locant base) :
    CaseBundle.extractCases request.assemble = request.caseBundle := by
  cases h : request.residue? with
  | none =>
      simp only [assemble, h, assembleCaseChannels, caseBundle, assembleCases]
      exact extractCases_attachCases base (bundleOfCases request.cases)
  | some ingress =>
      simp [assemble, h, assembleCaseChannels, caseBundle, assembleCases,
        extractCases_attachSourceBoundResidueLedger,
        extractCases_attachCases base (bundleOfCases request.cases)]

/-- Assembly preserves the base graph literally. -/
@[simp] theorem assemble_graph (request : SharedCaseRequest Locant base) :
    request.assemble.graph = base.graph := by
  cases h : request.residue? with
  | none => simp [assemble, h, assembleCaseChannels, assembleCases]
  | some ingress => simp [assemble, h, assembleCaseChannels, assembleCases]

/-- Assembly preserves the base inventory literally. -/
@[simp] theorem assemble_electronic? (request : SharedCaseRequest Locant base) :
    request.assemble.electronic? = base.electronic? := by
  cases h : request.residue? with
  | none => simp [assemble, h, assembleCaseChannels, assembleCases]
  | some ingress => simp [assemble, h, assembleCaseChannels, assembleCases]

/-- Assembly preserves the base conformation literally. -/
@[simp] theorem assemble_conformation (request : SharedCaseRequest Locant base) :
    request.assemble.conformation = base.conformation := by
  cases h : request.residue? with
  | none => simp [assemble, h, assembleCaseChannels, assembleCases]
  | some ingress => simp [assemble, h, assembleCaseChannels, assembleCases]

/-- The final residue ledger is exactly `none` or the attached source-bound channel. -/
@[simp] theorem assemble_residueLedger? (request : SharedCaseRequest Locant base) :
    request.assemble.residueLedger? =
      request.residue?.map ResidueIngress.channel := by
  cases h : request.residue? with
  | none => simp [assemble, h, assembleCaseChannels, assembleCases, request.residue_empty]
  | some ingress => simp [assemble, h, assembleCaseChannels, assembleCases]

/-- The attached residue channel for a supplied ingress. -/
@[simp] theorem assemble_residueLedger?_some (request : SharedCaseRequest Locant base)
    (ingress : ResidueIngress Locant base request.enumeration)
    (present : request.residue? = some ingress) :
    request.assemble.residueLedger? = some ingress.channel := by
  rw [assemble_residueLedger?, present]
  rfl

/-- Clearing the residue ledger, leaving all other fields intact. -/
def clearResidueLedger (state : WholeState V E B) : WholeState V E B :=
  { state with residueLedger? := none }

/-- Clear both the four case channels and the residue ledger.  This is the exact observation
map used to recover the ingress substrate from the assembled state. -/
def clearIngressChannels (state : WholeState V E B) : WholeState V E B :=
  clearResidueLedger (clearCases state)

/-- Clearing the case channels commutes with residue attachment: the residue update touches only
`residueLedger?`, while clearing touches only the four case channels. -/
@[simp] theorem clearCases_attachSourceBoundResidueLedger (state : WholeState V E B)
    (channel : ResidueLedgerChannel V) :
    clearCases (attachSourceBoundResidueLedger state channel) =
      attachSourceBoundResidueLedger (clearCases state) channel := by
  apply WholeState.extEq <;>
    simp [clearCases, attachSourceBoundResidueLedger, withResidueLedger]

/-- Clearing the residue ledger after attaching one yields the cleared prior ledger. -/
@[simp] theorem clearResidueLedger_attachSourceBoundResidueLedger
    (state : WholeState V E B) (channel : ResidueLedgerChannel V) :
    clearResidueLedger (attachSourceBoundResidueLedger state channel) =
      clearResidueLedger state := by
  apply WholeState.extEq <;>
    simp [clearResidueLedger, attachSourceBoundResidueLedger, withResidueLedger]

/-- Clearing the ingress channels after assembly forgets exactly the same prior data as clearing
the base: the base's case channels and residue ledger. -/
@[simp] theorem clearIngressChannels_assemble (request : SharedCaseRequest Locant base) :
    clearIngressChannels request.assemble = clearIngressChannels base := by
  cases h : request.residue? with
  | none =>
      simp [clearIngressChannels, clearResidueLedger, assemble, h, assembleCaseChannels,
        assembleCases, clearCases_attachCases]
  | some ingress =>
      simp [clearIngressChannels, clearResidueLedger, clearCases, assemble, h,
        assembleCaseChannels, assembleCases, attachSourceBoundResidueLedger,
        withResidueLedger]

/-- Under the request's empty-channel hypotheses, clearing the ingress channels returns the
genuine base state exactly. -/
@[simp] theorem clearIngressChannels_base (request : SharedCaseRequest Locant base) :
    clearIngressChannels base = base := by
  apply WholeState.extEq
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp [clearIngressChannels, clearResidueLedger, clearCases, request.empty.fragments]
  · simp [clearIngressChannels, clearResidueLedger, clearCases, request.empty.conventions]
  · simp [clearIngressChannels, clearResidueLedger, clearCases, request.empty.cages]
  · simp [clearIngressChannels, clearResidueLedger, request.residue_empty]
  · simp [clearIngressChannels, clearResidueLedger, clearCases, request.empty.frames]

/-- Both the base state and the whole ordered new case collection are recovered: the assembled
state's own channels are the encoded bundle, decoding the certificate sidecar (which carries the
optional coplanarity presence as data, not merely proofs) returns the original collection in
order, and clearing the ingress channels returns the base exactly. -/
theorem universal_ordered_recovery (request : SharedCaseRequest Locant base) :
    (EncodedCollection.encode request.cases).decode = request.cases ∧
    CaseBundle.extractCases request.assemble =
      (EncodedCollection.encode request.cases).bundle ∧
    clearIngressChannels request.assemble = base := by
  refine ⟨EncodedCollection.decode_encode request.cases, ?_, ?_⟩
  · rw [request.assemble_extractedCases]
    exact (EncodedCollection.encode_bundle request.cases).symm
  · rw [clearIngressChannels_assemble request, request.clearIngressChannels_base]

/-- Pack a request into its explicit output: the assembled state, the enumeration, the ordered
interleaving tags, the state-indexed certificate sidecar and the state-indexed residue metadata.
The output stores no raw case list and no raw ledger. -/
def pack (request : SharedCaseRequest Locant base) : PackedIngress Locant base :=
  match request.residue? with
  | none =>
      { enumeration := request.enumeration
        state := assembleCases base request.cases
        tags := request.cases.map PhysicalCase.shape
        sidecar := ChannelSidecar.ofCases request.cases
        residueMeta := request.residue_empty.symm ▸ PackedResidueMeta.none }
  | some ingress =>
      { enumeration := request.enumeration
        state := attachSourceBoundResidueLedger (assembleCases base request.cases) ingress.channel
        tags := request.cases.map PhysicalCase.shape
        sidecar := ChannelSidecar.ofCases request.cases
        residueMeta := PackedResidueMeta.some (PackedResidue.ofIngress ingress) }

/-- The packed state is exactly the assembled state. -/
@[simp] theorem pack_state (request : SharedCaseRequest Locant base) :
    request.pack.state = request.assemble := by
  cases request with
  | mk enumeration cases residue? empty residue_empty =>
    cases residue? <;> rfl

/-- The packed enumeration is the request enumeration. -/
@[simp] theorem pack_enumeration (request : SharedCaseRequest Locant base) :
    request.pack.enumeration = request.enumeration := by
  cases request with
  | mk enumeration cases residue? empty residue_empty =>
    cases residue? <;> rfl

/-- The packed tags are exactly the ordered shape tags of the collection. -/
@[simp] theorem pack_tags (request : SharedCaseRequest Locant base) :
    request.pack.tags = request.cases.map PhysicalCase.shape := by
  cases request with
  | mk enumeration cases residue? empty residue_empty =>
    cases residue? <;> rfl

/-- The packed sidecar is the certificate tree built from the collection, indexed by the state's
own channels.  The two types are definitionally equal because `attachCases` and residue attachment
set exactly the state channels the sidecar is indexed by. -/
theorem pack_sidecar (request : SharedCaseRequest Locant base) :
    HEq request.pack.sidecar (ChannelSidecar.ofCases request.cases) := by
  cases request with
  | mk enumeration cases residue? empty residue_empty =>
    cases residue? <;> exact HEq.refl _

/-- The packed residue metadata for an absent residue ingredient is the `none` node. -/
theorem pack_residueMeta_none (request : SharedCaseRequest Locant base)
    (h : request.residue? = none) :
    HEq request.pack.residueMeta
      (PackedResidueMeta.none (Locant := Locant) (graph := base.graph)
        (enumeration := request.enumeration)) := by
  cases request with
  | mk enumeration cases residue? empty residue_empty =>
    cases residue? with
    | none =>
        exact eqRec_heq residue_empty.symm
          (PackedResidueMeta.none (Locant := Locant) (graph := base.graph)
            (enumeration := enumeration))
    | some ingress => cases h

/-- The packed residue metadata for a present residue ingredient is the `some` node holding exactly
the attached channel and its packed metadata. -/
theorem pack_residueMeta_some (request : SharedCaseRequest Locant base)
    (ingress : ResidueIngress Locant base request.enumeration)
    (h : request.residue? = some ingress) :
    HEq request.pack.residueMeta
      (PackedResidueMeta.some (PackedResidue.ofIngress ingress)) := by
  cases request with
  | mk enumeration cases residue? empty residue_empty =>
    cases residue? with
    | none => cases h
    | some actual =>
        have actualEq : actual = ingress := Option.some.inj h
        subst actualEq
        exact HEq.refl _

/-- The packed state's case channels are exactly the ordered request channels; this is the
state-coherence equality exposed by the packed output. -/
@[simp] theorem pack_state_extractCases (request : SharedCaseRequest Locant base) :
    CaseBundle.extractCases request.pack.state = request.caseBundle := by
  rw [pack_state]
  exact request.assemble_extractedCases

/-- The packed state preserves the base graph. -/
@[simp] theorem pack_state_graph (request : SharedCaseRequest Locant base) :
    request.pack.state.graph = base.graph := by
  rw [pack_state]
  exact request.assemble_graph

/-- The packed state preserves the base inventory. -/
@[simp] theorem pack_state_electronic? (request : SharedCaseRequest Locant base) :
    request.pack.state.electronic? = base.electronic? := by
  rw [pack_state]
  exact request.assemble_electronic?

/-- The packed state preserves the base conformation. -/
@[simp] theorem pack_state_conformation (request : SharedCaseRequest Locant base) :
    request.pack.state.conformation = base.conformation := by
  rw [pack_state]
  exact request.assemble_conformation

end SharedCaseRequest

namespace PackedIngress

variable {base : WholeState V E B}

/-- Reconstruct the optional residue ingress from the packed output.  The packed residue metadata
is indexed by the *state's own* residue-channel option, so its `some` node is exactly the state's
channel; the observable view is then obtained by `decodeView?` from that channel's annotation, and
the ingress is rebuilt from the decoded view plus the packed validity and cover metadata.  The
auxiliary view and ledger payloads are never read from storage. -/
noncomputable def residueIngress? (packed : PackedIngress Locant base) :
    Option (ResidueIngress Locant base packed.enumeration) :=
  PackedResidueMeta.toIngress? (base := base) (enumeration := packed.enumeration)
    packed.residueMeta

/-- Decode a packed output back into a shared case request.  The enumeration is read from the
packed output, the cases from the state-indexed certificate sidecar, and the optional residue
ingredient from the state's own channel plus the minimal packed metadata.  The base's
empty-channel facts are parameters because they are properties of the fixed base, not encoded
data. -/
noncomputable def decode (packed : PackedIngress Locant base)
    (empty : CaseChannelsEmpty base) (residue_empty : base.residueLedger? = none) :
    SharedCaseRequest Locant base where
  enumeration := packed.enumeration
  cases := packed.sidecar.decode
  residue? := packed.residueIngress?
  empty := empty
  residue_empty := residue_empty

/-- Decoding reads the cases out of the state-indexed certificate sidecar. -/
@[simp] theorem decode_cases (packed : PackedIngress Locant base)
    (empty : CaseChannelsEmpty base) (residue_empty : base.residueLedger? = none) :
    (packed.decode empty residue_empty).cases = packed.sidecar.decode := rfl

/-- Decoding reads the enumeration from the packed output. -/
@[simp] theorem decode_enumeration (packed : PackedIngress Locant base)
    (empty : CaseChannelsEmpty base) (residue_empty : base.residueLedger? = none) :
    (packed.decode empty residue_empty).enumeration = packed.enumeration := rfl

/-- Decoding reads the optional residue ingredient from the state channel and packed metadata. -/
@[simp] theorem decode_residue? (packed : PackedIngress Locant base)
    (empty : CaseChannelsEmpty base) (residue_empty : base.residueLedger? = none) :
    (packed.decode empty residue_empty).residue? = packed.residueIngress? := rfl

/-- The packed output of a request with no residue ingredient has no residue ingress: the state's
own residue channel is absent and the packed node is `none`. -/
@[simp] theorem pack_residueIngress?_none (request : SharedCaseRequest Locant base)
    (h : request.residue? = none) :
    (SharedCaseRequest.pack request).residueIngress? = none := by
  cases request with
  | mk enumeration cases residue? empty residue_empty =>
    cases residue? with
    | none =>
        show PackedResidueMeta.toIngress? (base := base) (enumeration := enumeration)
            (residue_empty.symm ▸ (PackedResidueMeta.none (Locant := Locant)
              (graph := base.graph) (enumeration := enumeration))) = Option.none
        rw [PackedResidueMeta.toIngress?_irrel (base := base)
          (channelOption₁ := Option.none) (channelOption₂ := base.residueLedger?)
          residue_empty.symm (PackedResidueMeta.none (Locant := Locant)
            (graph := base.graph) (enumeration := enumeration))]
        rfl
    | some ingress => cases h

/-- The packed output of a request with a genuine residue ingress recovers exactly that ingress:
the state carries the source-bound channel, the decoded view is the original ledger's observable
view, and the proof-only packed metadata rebuilds the original ledger and cover. -/
@[simp] theorem pack_residueIngress?_some (request : SharedCaseRequest Locant base)
    (ingress : ResidueIngress Locant base request.enumeration)
    (h : request.residue? = some ingress) :
    HEq (SharedCaseRequest.pack request).residueIngress? (Option.some ingress) := by
  cases request with
  | mk enumeration cases residue? empty residue_empty =>
    cases residue? with
    | none => cases h
    | some actual =>
        cases h
        show HEq (PackedResidueMeta.toIngress? (base := base) (enumeration := enumeration)
            (PackedResidueMeta.some (PackedResidue.ofIngress actual))) (Option.some actual)
        exact heq_of_eq (PackedResidueMeta.toIngress?_ofIngress actual)

/-- Full-request left inverse: packing an actual request and decoding the packed output returns
that request, including its optional residue ingredient, with no raw case list or raw ledger
stored in the output. -/
@[simp] theorem decode_pack (request : SharedCaseRequest Locant base) :
    (SharedCaseRequest.pack request).decode request.empty request.residue_empty = request := by
  cases request with
  | mk enumeration cases residue? empty residue_empty =>
    cases residue? with
    | none =>
        dsimp only [decode]
        rw [pack_residueIngress?_none
          ⟨enumeration, cases, none, empty, residue_empty⟩ rfl]
        dsimp only [SharedCaseRequest.pack]
        simp only [ChannelSidecar.decode_ofCases]
    | some ingress =>
        dsimp only [decode]
        have step :
            (SharedCaseRequest.pack
              ⟨enumeration, cases, some ingress, empty, residue_empty⟩).residueIngress? =
              some ingress :=
          eq_of_heq (pack_residueIngress?_some
            ⟨enumeration, cases, some ingress, empty, residue_empty⟩ ingress rfl)
        rw [step]
        dsimp only [SharedCaseRequest.pack]
        simp only [ChannelSidecar.decode_ofCases]

/-- Decoding and re-assembling a packed actual request returns exactly the packed state. -/
theorem decode_assemble (request : SharedCaseRequest Locant base) :
    ((SharedCaseRequest.pack request).decode request.empty request.residue_empty).assemble =
      request.pack.state := by
  rw [decode_pack]
  exact (request.pack_state).symm

/-- Packing is injective on requests: decoding is a left inverse. -/
theorem pack_injective :
    Function.Injective (SharedCaseRequest.pack (Locant := Locant) (base := base)) := by
  intro first second same
  have hfirst := decode_pack first
  have hsecond := decode_pack second
  rw [← hfirst, same]
  exact hsecond

/-- Arbitrary-set image inverse for the full packed-request map. -/
theorem pack_set_image_inverse (requests : Set (SharedCaseRequest Locant base)) :
    SharedCaseRequest.pack ⁻¹'
        (SharedCaseRequest.pack '' requests) = requests := by
  ext request
  constructor
  · rintro ⟨other, hother, same⟩
    have : other = request := pack_injective same
    simpa [this] using hother
  · intro member
    exact ⟨request, member, rfl⟩

/-- The complete packed output exposes the assembled state, the state-indexed sidecar, and decodes
to the original full request. -/
theorem full_request_recovery (request : SharedCaseRequest Locant base) :
    request.pack.state = request.assemble ∧
    HEq request.pack.sidecar (ChannelSidecar.ofCases request.cases) ∧
    request.pack.decode request.empty request.residue_empty = request :=
  ⟨request.pack_state, request.pack_sidecar, decode_pack request⟩

end PackedIngress

end

end OrganicStereoSharedPhysicalCaseIngress
end TetraStereo.OneCenter
