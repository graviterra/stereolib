import TetraStereo.OneCenter.OrganicStereoFiniteEncoding
import TetraStereo.OneCenter.OrganicStereoJointCoreEncoding
import TetraStereo.OneCenter.OrganicStereoIndependentBandEncoding
import TetraStereo.OneCenter.OrganicStereoIndependentPathEncoding
import TetraStereo.OneCenter.OrganicStereoDiagramEncoding
import TetraStereo.OneCenter.OrganicStereoElectronicSites
import TetraStereo.OneCenter.OrganicStereoIndependentElectronicEncoding
import TetraStereo.OneCenter.OrganicStereoSpecialistAnnotations
import TetraStereo.OneCenter.OrganicStereoResidueLinkAnnotations
import TetraStereo.OneCenter.OrganicStereoDrawingConventions
import TetraStereo.OneCenter.OrganicStereoCageAnnotations
import TetraStereo.OneCenter.OrganicStereoFrameAnnotations
import TetraStereo.OneCenter.OrganicStereoEmbeddedBands
import TetraStereo.OneCenter.OrganicStereoRealConfiguration
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

open scoped unitInterval
open OrganicStereoElectronicSites
open OrganicStereoIndependentElectronicEncoding
open OrganicStereoIndependentBandEncoding
open OrganicStereoEmbeddedBands
open JointCoreEncoding

noncomputable section

/-!
# Finite classical stereo description on an arbitrary finite atom type

This module builds the whole-state record for an independently specified finite physical
description over an arbitrary finite atom type `V`, an arbitrary finite edge type `E` and an
arbitrary finite band type `B`, together with

* concrete fieldwise relabelling by one common atom equivalence,
* encoding into the same schema at `Fin (Fintype.card V)` / `Fin (Fintype.card E)` /
  `Fin (Fintype.card B)` and decoding using only the equivalence and the encoded payload,
* involution, injectivity and set-recovery theorems for the whole record,
* adapters to the repository's existing independent joint-core, band, path, diagram,
  fragment-annotation, frame-annotation, residue-ledger, drawing-convention and cage encodings.

The record never stores a `V`-labelled original source in the encoded form: encoding changes the
atom, edge and band index types themselves.  All shared, state-dependent data (conformation,
role ledger, electronic-site geometry, bond paths, band family, drawing evidence, fragment
annotations, ordered frame-reference annotations, residue links and hierarchy, drawing conventions
and cage annotations) lives in one record, so cross-channel correlations are retained through
encoding and decoding.

The frame channel is the existing `OrganicStereoFrameAnnotations.FrameAnnotation` sum, retained as
an ordered `List`.  It is transported by the same `relabelFrameAnnotation` operation as every other
channel, so ordered atom references, reference roles, explicit selected electronic site identities
(inventory, owner, kind and numeric slot), exact real reference planes, torsion participants and
polyhedral geometry-position metadata are preserved literally.  Raw frame metadata does not by
itself assert common inventory, source or geometry compatibility; that remains a separate physical
assembly obligation and is not claimed here.
-/

/-! ## Relabelling a finite atom-labelled interaction hypergraph -/

/-- Relabel one ordered hyperedge by applying the common atom equivalence to its participant list.
The semantic interaction kind (including any electron count or authority code) is copied
literally. -/
def relabelInteractionEdge {V W : Type*} (e : V ≃ W)
    (edge : List V × SemanticInteractionKind) : List W × SemanticInteractionKind :=
  (edge.1.map e, edge.2)

/-- Relabel the whole finite atom-labelled hypergraph by one atom equivalence.  Atom data is
reindexed, participant lists are mapped in order, and the interaction list keeps its order,
length and kinds. -/
def relabelGraph {V W : Type*} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]
    (e : V ≃ W) (graph : FiniteAtomInteractionHypergraph V) :
    FiniteAtomInteractionHypergraph W where
  atomData := fun atom => graph.atomData (e.symm atom)
  interactions := graph.interactions.map (relabelInteractionEdge e)
  arity_ge_two := by
    intro edge member
    rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
    simpa [relabelInteractionEdge] using graph.arity_ge_two original originalMember
  participants_nodup := by
    intro edge member
    rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
    simpa [relabelInteractionEdge] using
      (graph.participants_nodup original originalMember).map e.injective

variable {V W : Type*} [DecidableEq V] [Fintype V] [DecidableEq W] [Fintype W]

/-- Relabelling preserves the interaction-list length. -/
@[simp] theorem relabelGraph_interactions_length (e : V ≃ W)
    (graph : FiniteAtomInteractionHypergraph V) :
    (relabelGraph e graph).interactions.length = graph.interactions.length := by
  simp [relabelGraph]

/-- The image of a source occurrence index in the relabelled interaction list. -/
def relabelInteractionIndex (e : V ≃ W) {graph : FiniteAtomInteractionHypergraph V}
    (index : Fin graph.interactions.length) :
    Fin (relabelGraph e graph).interactions.length :=
  Fin.cast (relabelGraph_interactions_length e graph).symm index

/-- Exact lookup at a relabelled interaction index: the relabelled hyperedge is the source
hyperedge with participants mapped through the same equivalence.  Order and kind are unchanged. -/
theorem relabelGraph_interactions_get (e : V ≃ W)
    (graph : FiniteAtomInteractionHypergraph V) (index : Fin graph.interactions.length) :
    (relabelGraph e graph).interactions.get (relabelInteractionIndex e index) =
      relabelInteractionEdge e (graph.interactions.get index) := by
  show (graph.interactions.map (relabelInteractionEdge e)).get
      (Fin.cast (relabelGraph_interactions_length e graph).symm index) = _
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
  rfl

/-- The index transport is preserved by the inverse equivalence at the level of index values. -/
@[simp] theorem relabelInteractionIndex_val (e : V ≃ W)
    {graph : FiniteAtomInteractionHypergraph V} (index : Fin graph.interactions.length) :
    (relabelInteractionIndex e index).val = index.val :=
  rfl

/-- Relabelling twice by an equivalence and its inverse is the identity hypergraph. -/
theorem relabelGraph_symm (e : V ≃ W) (graph : FiniteAtomInteractionHypergraph V) :
    relabelGraph e.symm (relabelGraph e graph) = graph := by
  apply FiniteAtomInteractionHypergraph.ext_of_atomData_interactions
  · funext atom
    simp [relabelGraph]
  · simp only [relabelGraph, List.map_map]
    have h : relabelInteractionEdge e.symm ∘ relabelInteractionEdge e = id := by
      funext edge
      obtain ⟨participants, kind⟩ := edge
      simp [relabelInteractionEdge]
    rw [h, List.map_id]

/-- A graph with the same atom data and interaction list is the same graph. -/
theorem relabelGraph_atomData_apply (e : V ≃ W)
    (graph : FiniteAtomInteractionHypergraph V) (atom : W) :
    (relabelGraph e graph).atomData atom = graph.atomData (e.symm atom) := rfl

/-! ## Relabelling one physical role -/

/-- Relabel every atom reference of a physical role by the common equivalence.  Constructor,
order, bond order, donor/acceptor direction, electron counts and duplicate-free evidence are
preserved. -/
def relabelPhysicalRole {V W : Type*} (e : V ≃ W) : PhysicalRole V → PhysicalRole W
  | PhysicalRole.ordinaryBond bondOrder left right distinct =>
      PhysicalRole.ordinaryBond bondOrder (e left) (e right)
        (fun equal => distinct (e.injective equal))
  | PhysicalRole.directed donor acceptor distinct =>
      PhysicalRole.directed (e donor) (e acceptor)
        (fun equal => distinct (e.injective equal))
  | PhysicalRole.haptic centre donors nonempty nodup centreNotMem =>
      PhysicalRole.haptic (e centre) (donors.map e)
        (by simpa using nonempty)
        (nodup.map e.injective)
        (by
          intro member
          rcases List.mem_map.mp member with ⟨donor, donorMember, equal⟩
          exact centreNotMem (by
            have : donor = centre := e.injective equal
            simpa [this] using donorMember))
  | PhysicalRole.multicenter participants nodup arity electronCount =>
      PhysicalRole.multicenter (participants.map e) (nodup.map e.injective)
        (by simpa using arity) electronCount
  | PhysicalRole.delocalized participants nodup arity electronCount =>
      PhysicalRole.delocalized (participants.map e) (nodup.map e.injective)
        (by simpa using arity) electronCount

/-- The ordered participant support of a relabelled role is the mapped ordered support. -/
@[simp] theorem relabelPhysicalRole_supportList (e : V ≃ W) (role : PhysicalRole V) :
    (relabelPhysicalRole e role).supportList = role.supportList.map e := by
  cases role <;>
    simp [relabelPhysicalRole, PhysicalRole.supportList, PhysicalRole.supportKind]

/-- The semantic kind of a relabelled role, including every electron count, is unchanged. -/
@[simp] theorem relabelPhysicalRole_kind (e : V ≃ W) (role : PhysicalRole V) :
    (relabelPhysicalRole e role).kind = role.kind := by
  cases role <;> rfl

/-- The participant count of a relabelled role is unchanged. -/
@[simp] theorem relabelPhysicalRole_supportLength (e : V ≃ W) (role : PhysicalRole V) :
    (relabelPhysicalRole e role).supportLength = role.supportLength := by
  simp [PhysicalRole.supportLength, relabelPhysicalRole_supportList]

/-- Mapping a list through an equivalence and taking its finite set is the image of the original
finite set. -/
theorem toFinset_map_eq_image {A B : Type*} [DecidableEq A] [DecidableEq B]
    (f : A → B) (values : List A) :
    (values.map f).toFinset = values.toFinset.image f := by
  ext value
  simp

/-- The unordered participant support of a relabelled role is the image of the original support. -/
@[simp] theorem relabelPhysicalRole_supportFinset (e : V ≃ W) (role : PhysicalRole V) :
    (relabelPhysicalRole e role).supportFinset = role.supportFinset.image e := by
  rw [PhysicalRole.supportFinset, PhysicalRole.supportFinset,
    relabelPhysicalRole_supportList, toFinset_map_eq_image]

/-- Relabelling a physical role twice by an equivalence and its inverse is the identity. -/
theorem relabelPhysicalRole_symm (e : V ≃ W) (role : PhysicalRole V) :
    relabelPhysicalRole e.symm (relabelPhysicalRole e role) = role := by
  cases role <;> simp [relabelPhysicalRole]

/-- Compatibility with a source interaction occurrence is preserved by one common relabelling. -/
theorem compatible_relabel (e : V ≃ W) {graph : FiniteAtomInteractionHypergraph V}
    {index : Fin graph.interactions.length} {role : PhysicalRole V}
    (compatible : Compatible graph index role) :
    Compatible (relabelGraph e graph) (relabelInteractionIndex e index)
      (relabelPhysicalRole e role) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [relabelPhysicalRole_supportFinset, relabelGraph_interactions_get]
    change role.supportFinset.image e =
      ((graph.interactions.get index).1.map e).toFinset
    rw [toFinset_map_eq_image]
    exact congrArg (Finset.image e) compatible.1
  · rw [relabelGraph_interactions_get]
    simpa [relabelInteractionEdge, relabelPhysicalRole_kind] using compatible.2.1
  · rw [relabelGraph_interactions_get]
    simpa [relabelInteractionEdge, relabelPhysicalRole_supportLength] using compatible.2.2

/-! ## The graph-independent annotation channels

Every annotation below is stated on the physical atom labels only.  Its connection to the
interaction graph is a proposition-valued validity field of the whole state, so that relabelling
and its inverse are literal fieldwise operations.
-/

/-- A role annotation: one concrete interaction occurrence index (as a natural number, checked by
the whole-state validity field) together with an independent physical role. -/
structure RoleAnnotation (V : Type*) where
  interactionIndex : ℕ
  role : PhysicalRole V

/-- Relabel the role of an annotation; the occurrence index is unchanged. -/
def relabelRoleAnnotation {V W : Type*} (e : V ≃ W)
    (annotation : RoleAnnotation V) : RoleAnnotation W where
  interactionIndex := annotation.interactionIndex
  role := relabelPhysicalRole e annotation.role

/-- Relabelling a role annotation twice by an equivalence and its inverse is the identity. -/
theorem relabelRoleAnnotation_symm (e : V ≃ W) (annotation : RoleAnnotation V) :
    relabelRoleAnnotation e.symm (relabelRoleAnnotation e annotation) = annotation := by
  obtain ⟨index, role⟩ := annotation
  simpa [relabelRoleAnnotation, relabelPhysicalRole_symm]

/-! ## Relabelling independently supplied electronic site data

The electronic channel reuses the staged `OrganicStereoIndependentElectronicEncoding` vocabulary.
A present channel stores the actual `IndependentSiteCounts` plus, for every supplied owner and site
kind, the ordered list of per-slot reference evidence.  The list length is proved equal to the
supplied count, so a list position is an actual slot of an actual `IndependentSiteIdentity`
(`owner`, `kind`, `slot`), not an unbound annotation list.  `electronic? = none` records that no
electronic inventory was supplied; `some` with declared zero counts records a known empty inventory.
-/

/-- Reindex independently supplied site counts along the common atom equivalence. -/
def relabelIndependentSiteCounts {V W : Type*} (e : V ≃ W)
    (counts : IndependentSiteCounts V) : IndependentSiteCounts W where
  counts atom := counts.counts (e.symm atom)

/-- The count record at the image of a label is the original record. -/
@[simp] theorem relabelIndependentSiteCounts_image {V W : Type*} (e : V ≃ W)
    (counts : IndependentSiteCounts V) (atom : V) :
    (relabelIndependentSiteCounts e counts).counts (e atom) = counts.counts atom := by
  simp [relabelIndependentSiteCounts]

/-- Relabelling counts twice by an equivalence and its inverse is the identity. -/
theorem relabelIndependentSiteCounts_symm {V W : Type*} (e : V ≃ W)
    (counts : IndependentSiteCounts V) :
    relabelIndependentSiteCounts e.symm (relabelIndependentSiteCounts e counts) = counts := by
  cases counts with
  | mk values =>
      simp [relabelIndependentSiteCounts]

/-- Extensionality for counted site identities.  The slot comparison is heterogeneous because the
two slot types mention the owner and kind, which are themselves compared above. -/
theorem IndependentSiteIdentity.ext {siteCounts : IndependentSiteCounts V}
    {first second : IndependentSiteIdentity siteCounts}
    (owner : first.owner = second.owner) (kind : first.kind = second.kind)
    (slot : HEq first.slot second.slot) : first = second := by
  obtain ⟨firstOwner, firstKind, firstSlot⟩ := first
  obtain ⟨secondOwner, secondKind, secondSlot⟩ := second
  dsimp only at owner kind slot
  cases owner
  cases kind
  cases eq_of_heq slot
  rfl

/-- The identity equivalence on counted site identities induced by relabelling owner labels.
Owners move; kind and slot values are retained. -/
def relabelIndependentSiteIdentity {V W : Type*} [DecidableEq V] [Fintype V]
    [DecidableEq W] [Fintype W] (e : V ≃ W) (counts : IndependentSiteCounts V) :
    IndependentSiteIdentity counts ≃
      IndependentSiteIdentity (relabelIndependentSiteCounts e counts) where
  toFun identity :=
    ⟨e identity.owner, identity.kind, Fin.cast (by simp) identity.slot⟩
  invFun identity :=
    ⟨e.symm identity.owner, identity.kind, Fin.cast (by rfl) identity.slot⟩
  left_inv identity := by
    obtain ⟨owner, kind, slot⟩ := identity
    apply IndependentSiteIdentity.ext
    · simp
    · rfl
    · apply (Fin.heq_ext_iff (by simp)).mpr
      simp
  right_inv identity := by
    obtain ⟨owner, kind, slot⟩ := identity
    apply IndependentSiteIdentity.ext
    · simp
    · rfl
    · apply (Fin.heq_ext_iff (by simp)).mpr
      simp

/-- One independently supplied electronic channel.  Its data is indexed by atom labels only and is
therefore graph-independent; the whole state ties it to the graph through the unpaired-electron
agreement field.  `evidence owner kind` is ordered by slot and has exactly the supplied count of
entries, so no slot can be missing or invented. -/
structure ElectronicChannel (V : Type*) [DecidableEq V] [Fintype V] where
  /-- The actual independently supplied per-label counts. -/
  counts : IndependentSiteCounts V
  /-- Per-owner, per-kind ordered slot evidence. -/
  evidence : V → SiteKind → List ReferenceGeometryEvidence
  /-- The number of evidence entries at an owner and kind is exactly the supplied multiplicity. -/
  evidence_length : ∀ owner kind,
    (evidence owner kind).length = (counts.counts owner).count kind

/-- Extensionality for electronic channels; the length field is proposition-valued. -/
@[ext] theorem ElectronicChannel.ext {first second : ElectronicChannel V}
    (counts : first.counts = second.counts)
    (evidence : first.evidence = second.evidence) : first = second := by
  obtain ⟨firstCounts, firstEvidence, firstLength⟩ := first
  obtain ⟨secondCounts, secondEvidence, secondLength⟩ := second
  dsimp only at counts evidence
  cases counts
  cases evidence
  have lengthEq : firstLength = secondLength := Subsingleton.elim _ _
  cases lengthEq
  rfl

/-- Relabel an electronic channel: owner labels move, the counts are reindexed, and every
owner/kind evidence list keeps its order and each evidence value literally. -/
def relabelElectronicChannel {V W : Type*} [DecidableEq V] [Fintype V]
    [DecidableEq W] [Fintype W] (e : V ≃ W)
    (channel : ElectronicChannel V) : ElectronicChannel W where
  counts := relabelIndependentSiteCounts e channel.counts
  evidence owner kind := channel.evidence (e.symm owner) kind
  evidence_length owner kind := by
    show (channel.evidence (e.symm owner) kind).length =
      (channel.counts.counts (e.symm owner)).count kind
    exact channel.evidence_length (e.symm owner) kind

/-- Double relabelling of an electronic channel is the identity. -/
theorem relabelElectronicChannel_symm {V W : Type*} [DecidableEq V] [Fintype V]
    [DecidableEq W] [Fintype W] (e : V ≃ W)
    (channel : ElectronicChannel V) :
    relabelElectronicChannel e.symm (relabelElectronicChannel e channel) = channel := by
  obtain ⟨counts, evidence, lengthProof⟩ := channel
  apply ElectronicChannel.ext
  · exact relabelIndependentSiteCounts_symm e counts
  · funext owner kind
    simp [relabelElectronicChannel]

/-- The staged independent site assignment view of a present channel: evidence at exactly the
counted owner/kind/slot identities.  The slot bound is discharged by `evidence_length`, not
assumed. -/
def ElectronicChannel.toSiteAssignment (channel : ElectronicChannel V) :
    IndependentSiteAssignment channel.counts ReferenceGeometryEvidence where
  valueAt identity :=
    (channel.evidence identity.owner identity.kind).get
      ⟨identity.slot.val, by
        rw [channel.evidence_length identity.owner identity.kind]
        exact identity.slot.isLt⟩


/-- One per-band attachment family on the physical atom labels.  The whole conformation and the
band/full-geometry record are kept outside this per-band structure (in the whole state), so an
empty band index type preserves every atom position and every band-independent field. -/
structure BandAttachment (V : Type*) where
  /-- The geometric band, retained literally. -/
  band : Band
  /-- The finite attachment-record type of this band. -/
  Attachment : Type
  /-- Finiteness of the attachment-record type. -/
  fintypeAttachment : Fintype Attachment
  /-- The physical atom label named by each attachment record. -/
  atom : Attachment → V
  /-- The band parameter named by each attachment record. -/
  parameter : Attachment → RibbonDomain

/-- Relabel the atom references of one band attachment family.  The band, its geometry, the
attachment index type and every parameter point are unchanged. -/
def relabelBandAttachment {V W : Type*} (e : V ≃ W)
    (attachment : BandAttachment V) : BandAttachment W where
  band := attachment.band
  Attachment := attachment.Attachment
  fintypeAttachment := attachment.fintypeAttachment
  atom := fun record => e (attachment.atom record)
  parameter := attachment.parameter

/-- Relabelling a band attachment family twice is the identity. -/
theorem relabelBandAttachment_symm (e : V ≃ W) (attachment : BandAttachment V) :
    relabelBandAttachment e.symm (relabelBandAttachment e attachment) = attachment := by
  obtain ⟨band, Attachment, fintypeAttachment, atom, parameter⟩ := attachment
  have hatom : (fun record => e.symm (e (atom record))) = atom := by
    funext record
    simp
  simp [relabelBandAttachment, hatom]

/-- One bond-path annotation on the physical atom labels.  The interaction occurrence is a natural
number checked by the whole-state validity field; the oriented endpoints and the continuous arc are
literal data.  The endpoint agreement with the shared conformation is likewise stored once in the
whole state. -/
structure PathAnnotation (V : Type*) where
  /-- The concrete source interaction occurrence realized by this edge. -/
  interactionIndex : ℕ
  /-- Oriented first endpoint atom label. -/
  source : V
  /-- Oriented second endpoint atom label. -/
  target : V
  /-- The two endpoints are distinct. -/
  source_ne_target : source ≠ target
  /-- Arbitrary continuous arc in ambient real three-space. -/
  arc : C(I, EmbeddedReal3)

/-- Extensionality for path annotations.  The endpoint-distinctness field is proposition-valued. -/
theorem PathAnnotation.extEq {path other : PathAnnotation V}
    (index : path.interactionIndex = other.interactionIndex)
    (source : path.source = other.source) (target : path.target = other.target)
    (arc : path.arc = other.arc) : path = other := by
  obtain ⟨pathIndex, pathSource, pathTarget, pathDistinct, pathArc⟩ := path
  obtain ⟨otherIndex, otherSource, otherTarget, otherDistinct, otherArc⟩ := other
  dsimp only at index source target arc
  cases index
  cases source
  cases target
  cases arc
  have distinct : pathDistinct = otherDistinct := Subsingleton.elim _ _
  cases distinct
  rfl

/-- Relabel the oriented endpoints of a path annotation.  The occurrence index, the arc and the
endpoint-distinctness evidence are transported; no arc is rotated or reparameterized. -/
def relabelPathAnnotation {V W : Type*} (e : V ≃ W)
    (path : PathAnnotation V) : PathAnnotation W where
  interactionIndex := path.interactionIndex
  source := e path.source
  target := e path.target
  source_ne_target := fun equal => path.source_ne_target (e.injective equal)
  arc := path.arc

/-- Relabelling a path annotation twice is the identity. -/
theorem relabelPathAnnotation_symm (e : V ≃ W) (path : PathAnnotation V) :
    relabelPathAnnotation e.symm (relabelPathAnnotation e path) = path := by
  apply PathAnnotation.extEq
  · rfl
  · simp [relabelPathAnnotation]
  · simp [relabelPathAnnotation]
  · rfl

/-- One raw sparse incidence row: the drawing-bond occurrence position and the source interaction
occurrence it is associated with.  It carries no atom labels, so relabelling leaves it unchanged;
its validity is recorded propositionally in the whole state. -/
structure DiagramIncidenceRow where
  /-- Position of the drawing-bond occurrence in the ordered source bond list. -/
  bondIndex : ℕ
  /-- Concrete source interaction occurrence. -/
  interactionIndex : ℕ
  deriving DecidableEq, Repr

/-! ## Relabelling the optional diagram source -/

/-- Relabel one source drawing bond: endpoint labels are mapped, style and scope are copied. -/
def relabelDiagramBond {V W : Type*} (e : V ≃ W)
    (bond : SourceDiagramBond V) : SourceDiagramBond W where
  source := e bond.source
  target := e bond.target
  style := bond.style
  scope := bond.scope

/-- Relabelling a drawing bond twice is the identity. -/
theorem relabelDiagramBond_symm (e : V ≃ W) (bond : SourceDiagramBond V) :
    relabelDiagramBond e.symm (relabelDiagramBond e bond) = bond := by
  obtain ⟨source, target, style, scope⟩ := bond
  simp [relabelDiagramBond]

/-- Relabel one atom-parity annotation: the atom label is mapped, parity and scope are copied. -/
def relabelDiagramAtomConfiguration {V W : Type*} (e : V ≃ W)
    (configuration : SourceDiagramAtom V) : SourceDiagramAtom W where
  atom := e configuration.atom
  parity := configuration.parity
  scope := configuration.scope

/-- Relabelling an atom-parity annotation twice is the identity. -/
theorem relabelDiagramAtomConfiguration_symm (e : V ≃ W)
    (configuration : SourceDiagramAtom V) :
    relabelDiagramAtomConfiguration e.symm
        (relabelDiagramAtomConfiguration e configuration) = configuration := by
  obtain ⟨atom, parity, scope⟩ := configuration
  simp [relabelDiagramAtomConfiguration]

/-- Relabel the optional drawing data fieldwise.  Optional positions stay `none` when absent; when
present they are reindexed through the same equivalence (never copied as old `Fin` positions).  Bond
and atom-configuration lists keep their order and multiplicity. -/
def relabelDiagramSource {V W : Type*} (e : V ≃ W)
    (source : OrganicDiagramSource V) : OrganicDiagramSource W where
  positions? := source.positions?.map (fun positions atom => positions (e.symm atom))
  bonds := source.bonds.map (relabelDiagramBond e)
  atomConfigurations := source.atomConfigurations.map (relabelDiagramAtomConfiguration e)

/-- Extensionality for source drawing data. -/
theorem OrganicDiagramSource.extEq {source other : OrganicDiagramSource V}
    (positions : source.positions? = other.positions?)
    (bonds : source.bonds = other.bonds)
    (atomConfigurations : source.atomConfigurations = other.atomConfigurations) :
    source = other := by
  obtain ⟨sourcePositions, sourceBonds, sourceAtoms⟩ := source
  obtain ⟨otherPositions, otherBonds, otherAtoms⟩ := other
  dsimp only at positions bonds atomConfigurations
  cases positions
  cases bonds
  cases atomConfigurations
  rfl

/-- Relabelling the drawing data twice is the identity.  In particular an absent position channel
stays absent, and a present one returns to the original source-labelled function. -/
theorem relabelDiagramSource_symm (e : V ≃ W) (source : OrganicDiagramSource V) :
    relabelDiagramSource e.symm (relabelDiagramSource e source) = source := by
  apply OrganicDiagramSource.extEq
  · cases hpositions : source.positions? with
    | none => simp [relabelDiagramSource, hpositions]
    | some positions =>
        simp only [relabelDiagramSource, hpositions, Option.map_some]
        congr 1
        funext atom
        simp
  · simp only [relabelDiagramSource, List.map_map]
    have hbonds : relabelDiagramBond e.symm ∘ relabelDiagramBond e = id := by
      funext bond
      exact relabelDiagramBond_symm e bond
    rw [hbonds, List.map_id]
  · simp only [relabelDiagramSource, List.map_map]
    have hatoms :
        relabelDiagramAtomConfiguration e.symm ∘ relabelDiagramAtomConfiguration e = id := by
      funext configuration
      exact relabelDiagramAtomConfiguration_symm e configuration
    rw [hatoms, List.map_id]

/-- Relabelling preserves the drawing-bond list length. -/
@[simp] theorem relabelDiagramSource_bonds_length (e : V ≃ W)
    (source : OrganicDiagramSource V) :
    (relabelDiagramSource e source).bonds.length = source.bonds.length := by
  simp [relabelDiagramSource]

/-- Exact lookup in the relabelled drawing-bond list. -/
theorem relabelDiagramSource_bonds_get (e : V ≃ W)
    (source : OrganicDiagramSource V) (index : Fin source.bonds.length) :
    (relabelDiagramSource e source).bonds.get
        (Fin.cast (relabelDiagramSource_bonds_length e source).symm index) =
      relabelDiagramBond e (source.bonds.get index) := by
  show (source.bonds.map (relabelDiagramBond e)).get
      (Fin.cast (relabelDiagramSource_bonds_length e source).symm index) = _
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_map]
  rfl

/-! ## Sparse partial drawing positions

`OrganicDiagramSource.positions?` is all-or-nothing.  The independent sparse sidecar below records,
atom by atom, either a supplied exact rational coordinate or the genuine absence of one.  Absence is
`none` and is never identified with an origin coordinate. -/

/-- Relabel a sparse partial-position sidecar; each supplied rational coordinate is retained. -/
def relabelSourcePartialPositions {V W : Type*} (e : V ≃ W)
    (partialPositions : SourcePartialPositions V) : SourcePartialPositions W where
  positions atom := partialPositions.positions (e.symm atom)

/-- Double relabelling of sparse partial positions is the identity. -/
theorem relabelSourcePartialPositions_symm {V W : Type*} (e : V ≃ W)
    (partialPositions : SourcePartialPositions V) :
    relabelSourcePartialPositions e.symm
        (relabelSourcePartialPositions e partialPositions) = partialPositions := by
  obtain ⟨positions⟩ := partialPositions
  simp [relabelSourcePartialPositions]

/-! ## The residue-link and naming-hierarchy channel

The existing `ResidueLedgerAnnotation` is indexed by two finite occurrence budgets: the number of
residue scopes and the number of source interaction occurrences.  Those budgets are carried as data
of the channel so every ordered link keeps its residue and interaction bounds under one declared
enumeration; no certified original input is stored. -/

/-- Optional residue-link and naming-hierarchy channel.  The channel records its own two finite
occurrence budgets together with the typed `ResidueLedgerAnnotation`; the annotation itself keeps
the ordered link list, every link's scope/residue/interaction references and the optional naming
parent hierarchy. -/
structure ResidueLedgerChannel (V : Type*) where
  /-- Number of residue scopes referenced by links. -/
  residueCount : ℕ
  /-- Number of source interaction occurrences referenced by links. -/
  interactionCount : ℕ
  /-- The typed ledger annotation, in the same atom language `V`. -/
  annotation : ResidueLedgerAnnotation V residueCount interactionCount

namespace ResidueLedgerChannel

/-- Atom relabelling maps only the fragment atom references.  Both occurrence budgets, the ordered
link list (including every residue and interaction index) and the naming hierarchy are copied
verbatim. -/
def relabel {V W : Type*} (e : V ≃ W) (channel : ResidueLedgerChannel V) :
    ResidueLedgerChannel W :=
  ⟨channel.residueCount, channel.interactionCount, channel.annotation.relabel e⟩

@[simp] theorem relabel_residueCount {V W : Type*} (e : V ≃ W)
    (channel : ResidueLedgerChannel V) :
    (relabel e channel).residueCount = channel.residueCount := rfl

@[simp] theorem relabel_interactionCount {V W : Type*} (e : V ≃ W)
    (channel : ResidueLedgerChannel V) :
    (relabel e channel).interactionCount = channel.interactionCount := rfl

@[simp] theorem relabel_annotation {V W : Type*} (e : V ≃ W)
    (channel : ResidueLedgerChannel V) :
    (relabel e channel).annotation = channel.annotation.relabel e := rfl

/-- Relabelling by an equivalence and then by its inverse is the identity on the whole channel. -/
theorem relabel_symm {V W : Type*} (e : V ≃ W) (channel : ResidueLedgerChannel V) :
    relabel e.symm (relabel e channel) = channel := by
  obtain ⟨residueCount, interactionCount, annotation⟩ := channel
  dsimp only [relabel]
  rw [ResidueLedgerAnnotation.relabel_relabel_symm]

/-- The opposite composition. -/
theorem relabel_apply_symm {V W : Type*} (e : V ≃ W) (channel : ResidueLedgerChannel W) :
    relabel e (relabel e.symm channel) = channel := by
  obtain ⟨residueCount, interactionCount, annotation⟩ := channel
  dsimp only [relabel]
  rw [ResidueLedgerAnnotation.relabel_symm_relabel]

end ResidueLedgerChannel

/-! ## The whole-state record -/

variable {E E' B B' : Type*} [Fintype E] [Fintype E'] [Fintype B] [Fintype B']

/-- The complete independent finite physical description on arbitrary finite atom labels `V`,
arbitrary finite bond-path edges `E` and arbitrary finite band indices `B`.

All channels are fields of this one record, so a state-dependent conformation, role ledger,
electronic-site geometry, bond paths, band family, drawing evidence, frame-reference annotations
and the sparse incidence ledger remain correlated.  The graph is part of the record; no channel
stores a second copy of it.  Empty families are genuine empty families: an empty `E` leaves paths
absent, an empty `B` leaves the band family empty while the whole conformation and the full
band-independent geometry remain present, an empty frame list is genuine absence of frame
metadata, and `diagram? = none` preserves the absence of drawing data. -/
structure WholeState (V E B : Type*) [DecidableEq V] [Fintype V] [Fintype E] [Fintype B] where
  /-- The independently specified finite atom-labelled interaction hypergraph. -/
  graph : FiniteAtomInteractionHypergraph V
  /-- Optional independently supplied electronic inventory.  `none` records that no inventory was
  supplied; `some` with declared zero counts records a known empty inventory. -/
  electronic? : Option (ElectronicChannel V) := none
  /-- The single declared tie of a present electronic inventory to the graph: the supplied
  unpaired-electron count equals the graph atom data at every atom label. -/
  electronic_unpaired : ∀ channel, electronic? = some channel → ∀ owner,
    (channel.counts.counts owner).unpairedElectronPositions =
      (graph.atomData owner).unpairedElectrons
  /-- One full real conformation, shared by every channel. -/
  conformation : MolecularConformation V
  /-- Optional exact rational provenance for the shared conformation.  Absence is genuine; a
  supplied point is tied to the real conformation pointwise. -/
  rationalPositions? : Option (V → CartesianPoint3) := none
  /-- Every supplied rational point is exactly the shared real conformation at that atom. -/
  rationalPositions_valid : ∀ positions, rationalPositions? = some positions →
    ∀ atom, (positions atom).toEuclideanPoint = conformation atom
  /-- Ordered finite role ledger.  Order and multiplicity are those of the list. -/
  roles : List (RoleAnnotation V)
  /-- Every role annotation names an actual source interaction occurrence and is compatible with
  it.  The ledger is not required to be total. -/
  role_valid : ∀ annotation ∈ roles,
    ∃ bound : annotation.interactionIndex < graph.interactions.length,
      Compatible graph ⟨annotation.interactionIndex, bound⟩ annotation.role
  /-- Finite bond-path family indexed by the arbitrary edge type `E`.  Empty `E` means no paths. -/
  paths : E → PathAnnotation V
  /-- Every path annotation realizes an actual two-participant source interaction of a selected
  pair-bond kind.  Occurrence injectivity and geometric non-degeneracy are separate adapter
  hypotheses, not hidden fields. -/
  path_valid : ∀ edge,
    ∃ bound : (paths edge).interactionIndex < graph.interactions.length,
      (graph.interactions.get ⟨(paths edge).interactionIndex, bound⟩).1 =
          [(paths edge).source, (paths edge).target] ∧
        SemanticInteractionKind.isSelectedPairKind
          (graph.interactions.get ⟨(paths edge).interactionIndex, bound⟩).2 = true
  /-- Arc start points coincide with the shared conformation. -/
  path_source_endpoint : ∀ edge, (paths edge).arc 0 = conformation ((paths edge).source)
  /-- Arc end points coincide with the shared conformation. -/
  path_target_endpoint : ∀ edge, (paths edge).arc 1 = conformation ((paths edge).target)
  /-- The band attachment family.  Empty `B` is allowed and loses no whole-state data. -/
  bandFamily : B → BandAttachment V
  /-- Exact positional agreement of every attachment record with the shared conformation. -/
  band_agreement : ∀ band (record : (bandFamily band).Attachment),
    (bandFamily band).band.strip ((bandFamily band).parameter record) =
      conformation ((bandFamily band).atom record)
  /-- Optional drawing data; `none` records genuine absence. -/
  diagram? : Option (OrganicDiagramSource V) := none
  /-- Optional sparse per-atom rational coordinates, preserving missing coordinates as `none`
  independently of the all-or-nothing `OrganicDiagramSource.positions?` channel. -/
  diagramPartial? : Option (SourcePartialPositions V) := none
  /-- Sparse raw incidence ledger.  Several rows may name the same bond occurrence and a bond may
  have no row. -/
  diagramIncidence : List DiagramIncidenceRow := []
  /-- Every raw incidence row is backed by actual bounded source-interaction membership in the
  drawing data and the graph.  This is proposition-valued evidence, not additional data. -/
  diagram_valid : ∀ row ∈ diagramIncidence,
    ∃ source : OrganicDiagramSource V,
      diagram? = some source ∧
        ∃ bondBound : row.bondIndex < source.bonds.length,
          ∃ interactionBound : row.interactionIndex < graph.interactions.length,
            (source.bonds.get ⟨row.bondIndex, bondBound⟩).source ∈
                (graph.interactions.get ⟨row.interactionIndex, interactionBound⟩).1 ∧
              (source.bonds.get ⟨row.bondIndex, bondBound⟩).target ∈
                (graph.interactions.get ⟨row.interactionIndex, interactionBound⟩).1
  /-- Ordered residue/fragment annotation channel.  Each entry keeps its finite atom support and
  its ordered scoped locant bindings in the same atom language `V`; order, duplicates and
  unresolved bindings are retained.  An empty list is genuine absence of fragment metadata. -/
  fragments : List (FragmentAnnotation V) := []
  /-- The ordered drawing-convention channel.  It is a genuine list, so order, duplicates,
  omissions and an empty channel all remain distinguishable. -/
  conventions : ConventionChannel V := []
  /-- Ordered numbered cage/face annotation channel.  Cage numbering, ordered vertices, edges,
  faces and addend interactions are retained literally. -/
  cages : List (NumberedCageAnnotation V) := []
  /-- Optional residue-link and naming-hierarchy channel.  `none` records that no ledger was
  supplied; `some` keeps the channel's own finite occurrence budgets, its ordered links with
  residue and interaction bounds, and its optional naming hierarchy.  No certified original input
  is stored. -/
  residueLedger? : Option (ResidueLedgerChannel V) := none
  /-- Ordered caller-supplied frame-reference annotations.  This is the existing
  `FrameAnnotation` sum retained verbatim, including ordered atom references, participant
  identities, explicit selected electronic site identities (inventory, owner, kind and numeric
  slot), exact real reference planes, torsion angles and polyhedral geometry-position metadata.
  Order, duplicates and an empty list are meaningful.  Raw metadata alone does not assert common
  inventory, source or geometry compatibility with the other channels. -/
  frames : List (FrameAnnotation V) := []

/-- Extensionality for whole states.  The validity fields are proposition-valued and are
identified by proof irrelevance once the data fields agree. -/
theorem WholeState.extEq {state other : WholeState V E B}
    (graph : state.graph = other.graph)
    (electronic : state.electronic? = other.electronic?)
    (conformation : state.conformation = other.conformation)
    (rationalPositions : state.rationalPositions? = other.rationalPositions?)
    (roles : state.roles = other.roles)
    (paths : state.paths = other.paths)
    (bandFamily : state.bandFamily = other.bandFamily)
    (diagram : state.diagram? = other.diagram?)
    (diagramPartial : state.diagramPartial? = other.diagramPartial?)
    (diagramIncidence : state.diagramIncidence = other.diagramIncidence)
    (fragments : state.fragments = other.fragments)
    (conventions : state.conventions = other.conventions)
    (cages : state.cages = other.cages)
    (residueLedger : state.residueLedger? = other.residueLedger?)
    (frames : state.frames = other.frames) :
    state = other := by
  obtain ⟨graph₁, electronic₁, unpaired₁, conformation₁, rational₁, rationalValid₁,
    roles₁, roleValid₁, paths₁, pathValid₁, sourceEndpoint₁, targetEndpoint₁,
    bands₁, bandAgreement₁, diagram₁, diagramPartial₁, incidence₁, diagramValid₁,
    fragments₁, conventions₁, cages₁, residueLedger₁, frames₁⟩ := state
  obtain ⟨graph₂, electronic₂, unpaired₂, conformation₂, rational₂, rationalValid₂,
    roles₂, roleValid₂, paths₂, pathValid₂, sourceEndpoint₂, targetEndpoint₂,
    bands₂, bandAgreement₂, diagram₂, diagramPartial₂, incidence₂, diagramValid₂,
    fragments₂, conventions₂, cages₂, residueLedger₂, frames₂⟩ := other
  dsimp only at graph electronic conformation rationalPositions roles paths bandFamily diagram diagramPartial diagramIncidence fragments conventions cages residueLedger frames
  cases graph
  cases electronic
  cases conformation
  cases rationalPositions
  cases roles
  cases paths
  cases bandFamily
  cases diagram
  cases diagramPartial
  cases diagramIncidence
  cases fragments
  cases conventions
  cases cages
  cases residueLedger
  cases frames
  have unpaired : unpaired₁ = unpaired₂ := by
    funext channel present owner
    exact Subsingleton.elim _ _
  have rationalValid : rationalValid₁ = rationalValid₂ := by
    funext positions present atom
    exact Subsingleton.elim _ _
  have roleValid : roleValid₁ = roleValid₂ := by
    funext annotation member
    exact Subsingleton.elim _ _
  have pathValid : pathValid₁ = pathValid₂ := by
    funext edge
    exact Subsingleton.elim _ _
  have sourceEndpoint : sourceEndpoint₁ = sourceEndpoint₂ := by
    funext edge
    exact Subsingleton.elim _ _
  have targetEndpoint : targetEndpoint₁ = targetEndpoint₂ := by
    funext edge
    exact Subsingleton.elim _ _
  have bandAgreement : bandAgreement₁ = bandAgreement₂ := by
    funext band record
    exact Subsingleton.elim _ _
  have diagramValid : diagramValid₁ = diagramValid₂ := by
    funext row member
    exact Subsingleton.elim _ _
  cases unpaired
  cases rationalValid
  cases roleValid
  cases pathValid
  cases sourceEndpoint
  cases targetEndpoint
  cases bandAgreement
  cases diagramValid
  rfl

/-! ## Fieldwise relabelling of the whole state -/

/-- Relabel all atom references of a whole state by one common equivalence.  The graph, the
electronic counts, the single conformation, roles, site annotations, path endpoints, band
attachment atoms, drawing data and every ordered frame annotation are relabelled together;
occurrence indices, list order, arcs, band parameters, band geometry, evidence content, selected
frame site slots/inventories, exact real frame planes and the raw incidence ledger are preserved. -/
def relabelWholeState (e : V ≃ W) (state : WholeState V E B) : WholeState W E B :=
  let graph' := relabelGraph e state.graph
  let electronic' := state.electronic?.map (relabelElectronicChannel e)
  let rational' :=
    state.rationalPositions?.map (fun positions atom => positions (e.symm atom))
  let roles' := state.roles.map (relabelRoleAnnotation e)
  let paths' : E → PathAnnotation W := fun edge => relabelPathAnnotation e (state.paths edge)
  let bandFamily' : B → BandAttachment W :=
    fun band => relabelBandAttachment e (state.bandFamily band)
  let diagram' := state.diagram?.map (relabelDiagramSource e)
  let diagramPartial' := state.diagramPartial?.map (relabelSourcePartialPositions e)
  let fragments' := state.fragments.map (fun annotation => annotation.relabel e)
  let conventions' := ConventionChannel.encode e state.conventions
  let cages' := NumberedCageAnnotation.relabelList e state.cages
  let residueLedger' := state.residueLedger?.map (ResidueLedgerChannel.relabel e)
  let frames' := state.frames.map (relabelFrameAnnotation e)
  { graph := graph'
    electronic? := electronic'
    electronic_unpaired := by
      intro channel present owner
      have present' : Option.map (relabelElectronicChannel e) state.electronic? =
          some channel := by simpa [electronic'] using present
      obtain ⟨sourceChannel, hsource, rfl⟩ := Option.map_eq_some_iff.mp present'
      show (sourceChannel.counts.counts (e.symm owner)).unpairedElectronPositions =
        (state.graph.atomData (e.symm owner)).unpairedElectrons
      exact state.electronic_unpaired sourceChannel hsource (e.symm owner)
    conformation := MolecularConformation.reindex e state.conformation
    rationalPositions? := rational'
    rationalPositions_valid := by
      intro positions present atom
      have present' : Option.map (fun positions atom => positions (e.symm atom))
          state.rationalPositions? = some positions := by simpa [rational'] using present
      obtain ⟨sourcePositions, hsource, rfl⟩ := Option.map_eq_some_iff.mp present'
      show (sourcePositions (e.symm atom)).toEuclideanPoint =
        state.conformation (e.symm atom)
      exact state.rationalPositions_valid sourcePositions hsource (e.symm atom)
    roles := roles'
    role_valid := by
      intro annotation member
      rcases List.mem_map.mp member with ⟨original, originalMember, rfl⟩
      rcases state.role_valid original originalMember with ⟨bound, compatible⟩
      have bound' : original.interactionIndex < graph'.interactions.length := by
        simpa [graph', relabelGraph_interactions_length] using bound
      refine ⟨bound', ?_⟩
      simpa [relabelRoleAnnotation, graph'] using compatible_relabel e compatible
    paths := paths'
    path_valid := by
      intro edge
      rcases state.path_valid edge with ⟨bound, participants, kindSelected⟩
      have bound' : (paths' edge).interactionIndex < graph'.interactions.length := by
        have hlen : graph'.interactions.length = state.graph.interactions.length := by
          simp [graph']
        rw [hlen]
        simpa [paths', relabelPathAnnotation] using bound
      have indexEq :
          (⟨(paths' edge).interactionIndex, bound'⟩ : Fin graph'.interactions.length) =
            relabelInteractionIndex e
              ⟨(state.paths edge).interactionIndex, bound⟩ :=
        Fin.ext rfl
      refine ⟨bound', ?_, ?_⟩
      · rw [indexEq, relabelGraph_interactions_get]
        change (state.graph.interactions.get
          ⟨(state.paths edge).interactionIndex, bound⟩).1.map e =
            [(paths' edge).source, (paths' edge).target]
        rw [participants]
        simp [paths', relabelPathAnnotation]
      · rw [indexEq, relabelGraph_interactions_get]
        simpa [relabelInteractionEdge, relabelPathAnnotation] using kindSelected
    path_source_endpoint := by
      intro edge
      rw [show (paths' edge).arc = (state.paths edge).arc from rfl,
        show (paths' edge).source = e (state.paths edge).source from rfl]
      simp only [MolecularConformation.reindex, Equiv.symm_apply_apply]
      exact state.path_source_endpoint edge
    path_target_endpoint := by
      intro edge
      rw [show (paths' edge).arc = (state.paths edge).arc from rfl,
        show (paths' edge).target = e (state.paths edge).target from rfl]
      simp only [MolecularConformation.reindex, Equiv.symm_apply_apply]
      exact state.path_target_endpoint edge
    bandFamily := bandFamily'
    band_agreement := by
      intro band record
      simpa [bandFamily', relabelBandAttachment, MolecularConformation.reindex] using
        state.band_agreement band record
    diagram? := diagram'
    diagramPartial? := diagramPartial'
    diagramIncidence := state.diagramIncidence
    diagram_valid := by
      intro row member
      rcases state.diagram_valid row member with
        ⟨source, sourceEq, bondBound, interactionBound, sourceMem, targetMem⟩
      let source' := relabelDiagramSource e source
      have sourceEq' : diagram' = some source' := by
        simp [diagram', sourceEq, source']
      have bondBound' : row.bondIndex < source'.bonds.length := by
        simpa [source', relabelDiagramSource_bonds_length] using bondBound
      have interactionBound' : row.interactionIndex < graph'.interactions.length := by
        simpa [graph', relabelGraph_interactions_length] using interactionBound
      refine ⟨source', sourceEq', bondBound', interactionBound', ?_, ?_⟩
      · have bondIndexEq :
            (⟨row.bondIndex, bondBound'⟩ : Fin source'.bonds.length) =
              Fin.cast (relabelDiagramSource_bonds_length e source).symm
                ⟨row.bondIndex, bondBound⟩ :=
          Fin.ext rfl
        have interactionIndexEq :
            (⟨row.interactionIndex, interactionBound'⟩ : Fin graph'.interactions.length) =
              relabelInteractionIndex e ⟨row.interactionIndex, interactionBound⟩ :=
          Fin.ext rfl
        rw [bondIndexEq, interactionIndexEq, relabelDiagramSource_bonds_get,
          relabelGraph_interactions_get]
        simp only [relabelDiagramBond, relabelInteractionEdge]
        exact List.mem_map.mpr ⟨_, sourceMem, rfl⟩
      · have bondIndexEq :
            (⟨row.bondIndex, bondBound'⟩ : Fin source'.bonds.length) =
              Fin.cast (relabelDiagramSource_bonds_length e source).symm
                ⟨row.bondIndex, bondBound⟩ :=
          Fin.ext rfl
        have interactionIndexEq :
            (⟨row.interactionIndex, interactionBound'⟩ : Fin graph'.interactions.length) =
              relabelInteractionIndex e ⟨row.interactionIndex, interactionBound⟩ :=
          Fin.ext rfl
        rw [bondIndexEq, interactionIndexEq, relabelDiagramSource_bonds_get,
          relabelGraph_interactions_get]
        simp only [relabelDiagramBond, relabelInteractionEdge]
        exact List.mem_map.mpr ⟨_, targetMem, rfl⟩
    fragments := fragments'
    conventions := conventions'
    cages := cages'
    residueLedger? := residueLedger'
    frames := frames' }

/-- Relabelling the whole state twice by an equivalence and its inverse is the identity. -/
theorem relabelWholeState_symm (e : V ≃ W) (state : WholeState V E B) :
    relabelWholeState e.symm (relabelWholeState e state) = state := by
  apply WholeState.extEq
  · simp only [relabelWholeState]
    exact relabelGraph_symm e state.graph
  · simp only [relabelWholeState, Option.map_map]
    have hcomp : (relabelElectronicChannel e.symm ∘ relabelElectronicChannel e) = id := by
      funext channel
      exact relabelElectronicChannel_symm e channel
    rw [hcomp, Option.map_id]
    rfl
  · simp only [relabelWholeState]
    exact MolecularConformation.reindex_reindex e state.conformation
  · simp only [relabelWholeState]
    cases h : state.rationalPositions? with
    | none => simp [h]
    | some positions =>
        simp only [h, Option.map_some, Option.some.injEq]
        funext atom
        simp
  · simp only [relabelWholeState, List.map_map]
    have h : relabelRoleAnnotation e.symm ∘ relabelRoleAnnotation e = id := by
      funext annotation
      exact relabelRoleAnnotation_symm e annotation
    rw [h, List.map_id]
  · simp only [relabelWholeState]
    funext edge
    exact relabelPathAnnotation_symm e (state.paths edge)
  · simp only [relabelWholeState]
    funext band
    exact relabelBandAttachment_symm e (state.bandFamily band)
  · simp only [relabelWholeState]
    cases hdiagram : state.diagram? with
    | none => simp [hdiagram]
    | some source => simp [hdiagram, relabelDiagramSource_symm]
  · simp only [relabelWholeState]
    cases hpartial : state.diagramPartial? with
    | none => simp [hpartial]
    | some partialPositions => simp [hpartial, relabelSourcePartialPositions_symm]
  · simp only [relabelWholeState]
  · simp only [relabelWholeState, List.map_map]
    have h : (FragmentAnnotation.relabel e.symm ∘ FragmentAnnotation.relabel e) = id := by
      funext annotation
      exact FragmentAnnotation.relabel_relabel_symm e annotation
    rw [h, List.map_id]
  · simp only [relabelWholeState, ConventionChannel.encode, List.map_map]
    have h : (OrganicConventionSource.encode e.symm ∘ OrganicConventionSource.encode e) = id := by
      funext source
      exact OrganicConventionSource.decode_encode e source
    rw [h, List.map_id]
  · simp only [relabelWholeState]
    exact NumberedCageAnnotation.relabelList_symm_relabel e state.cages
  · simp only [relabelWholeState, Option.map_map]
    have h : (ResidueLedgerChannel.relabel e.symm ∘ ResidueLedgerChannel.relabel e) = id := by
      funext channel
      exact ResidueLedgerChannel.relabel_symm e channel
    rw [h, Option.map_id]
    rfl
  · simp only [relabelWholeState, List.map_map]
    have h : (relabelFrameAnnotation (V := W) (W := V) e.symm) ∘
        (relabelFrameAnnotation (V := V) (W := W) e) = id := by
      funext annotation
      exact relabelFrameAnnotation_symm e annotation
    rw [h, List.map_id]

/-! ## Frame-channel projections

The ordered frame list is a literal channel of the state.  The projections below show that the
common relabelling acts on it exactly by `relabelFrameAnnotation`, preserving list order,
duplicates, the ordered atom references, explicit selected-site identities and exact real planes.
-/

/-- Relabelling the whole state maps the ordered frame list elementwise by the same equivalence.
No frame is dropped, reordered or duplicated. -/
@[simp] theorem relabelWholeState_frames (e : V ≃ W) (state : WholeState V E B) :
    (relabelWholeState e state).frames =
      state.frames.map (relabelFrameAnnotation e) := rfl

/-- The frame-list length is preserved exactly. -/
@[simp] theorem relabelWholeState_frames_length (e : V ≃ W) (state : WholeState V E B) :
    (relabelWholeState e state).frames.length = state.frames.length := by
  simp [relabelWholeState_frames]

/-- The ordered atom references of the whole frame channel are mapped elementwise.  Thus frame
order, multiplicities and every optional/selected atom reference are retained. -/
@[simp] theorem relabelWholeState_frames_atomRefs (e : V ≃ W)
    (state : WholeState V E B) :
    (relabelWholeState e state).frames.map FrameAnnotation.atomRefs =
      (state.frames.map FrameAnnotation.atomRefs).map (List.map e) := by
  simp only [relabelWholeState_frames, List.map_map,
    atomRefs_relabelFrameAnnotation, Function.comp_def]

/-- Exact real reference planes are retained literally: relabelling atoms does not move, rotate or
rationalize a supplied real frame plane. -/
@[simp] theorem relabelWholeState_frames_realPlane? (e : V ≃ W)
    (state : WholeState V E B) :
    (relabelWholeState e state).frames.map FrameAnnotation.realPlane? =
      state.frames.map FrameAnnotation.realPlane? := by
  simp only [relabelWholeState_frames, List.map_map,
    realPlane?_relabelFrameAnnotation, Function.comp_def]

/-- Duplicate-free ordered frame lists stay duplicate-free under the common relabelling. -/
theorem relabelWholeState_frames_nodup (e : V ≃ W) (state : WholeState V E B)
    (nodup : state.frames.Nodup) :
    (relabelWholeState e state).frames.Nodup := by
  rw [relabelWholeState_frames]
  exact nodup.map (relabelFrameAnnotation_injective e)

/-! ## Reindexing the independent edge and band index types -/

/-- Reindex the bond-path family from `E` to an equivalent finite type `E'`.  Nothing else in the
whole state changes. -/
def reindexEdges (equivalence : E ≃ E') (state : WholeState V E B) : WholeState V E' B where
  graph := state.graph
  electronic? := state.electronic?
  electronic_unpaired := state.electronic_unpaired
  conformation := state.conformation
  rationalPositions? := state.rationalPositions?
  rationalPositions_valid := state.rationalPositions_valid
  roles := state.roles
  role_valid := state.role_valid
  paths := fun edge => state.paths (equivalence.symm edge)
  path_valid := fun edge => state.path_valid (equivalence.symm edge)
  path_source_endpoint := fun edge => state.path_source_endpoint (equivalence.symm edge)
  path_target_endpoint := fun edge => state.path_target_endpoint (equivalence.symm edge)
  bandFamily := state.bandFamily
  band_agreement := state.band_agreement
  diagram? := state.diagram?
  diagramPartial? := state.diagramPartial?
  diagramIncidence := state.diagramIncidence
  diagram_valid := state.diagram_valid
  fragments := state.fragments
  conventions := state.conventions
  cages := state.cages
  residueLedger? := state.residueLedger?
  frames := state.frames

/-- Edge reindexing leaves the ordered frame channel unchanged. -/
@[simp] theorem reindexEdges_frames (equivalence : E ≃ E') (state : WholeState V E B) :
    (reindexEdges equivalence state).frames = state.frames := rfl

/-- Reindexing the edge family twice by an equivalence and its inverse is the identity. -/
theorem reindexEdges_symm_reindex (equivalence : E ≃ E') (state : WholeState V E B) :
    reindexEdges equivalence.symm (reindexEdges equivalence state) = state := by
  apply WholeState.extEq
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [reindexEdges]
    funext edge
    simp
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The opposite composition for edge reindexing. -/
theorem reindexEdges_apply_symm (equivalence : E ≃ E')
    (state : WholeState V E' B) :
    reindexEdges equivalence (reindexEdges equivalence.symm state) = state := by
  simpa using reindexEdges_symm_reindex equivalence.symm state

/-- Reindex the band attachment family from `B` to an equivalent finite type `B'`.  The whole
conformation, all other channels and every band-independent field are unchanged. -/
def reindexBands (equivalence : B ≃ B') (state : WholeState V E B) :
    WholeState V E B' where
  graph := state.graph
  electronic? := state.electronic?
  electronic_unpaired := state.electronic_unpaired
  conformation := state.conformation
  rationalPositions? := state.rationalPositions?
  rationalPositions_valid := state.rationalPositions_valid
  roles := state.roles
  role_valid := state.role_valid
  paths := state.paths
  path_valid := state.path_valid
  path_source_endpoint := state.path_source_endpoint
  path_target_endpoint := state.path_target_endpoint
  bandFamily := fun band => state.bandFamily (equivalence.symm band)
  band_agreement := fun band record => state.band_agreement (equivalence.symm band) record
  diagram? := state.diagram?
  diagramPartial? := state.diagramPartial?
  diagramIncidence := state.diagramIncidence
  diagram_valid := state.diagram_valid
  fragments := state.fragments
  conventions := state.conventions
  cages := state.cages
  residueLedger? := state.residueLedger?
  frames := state.frames

/-- Band reindexing leaves the ordered frame channel unchanged. -/
@[simp] theorem reindexBands_frames (equivalence : B ≃ B') (state : WholeState V E B) :
    (reindexBands equivalence state).frames = state.frames := rfl

/-- Reindexing the band family twice by an equivalence and its inverse is the identity. -/
theorem reindexBands_symm_reindex (equivalence : B ≃ B') (state : WholeState V E B) :
    reindexBands equivalence.symm (reindexBands equivalence state) = state := by
  apply WholeState.extEq
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [reindexBands]
    funext band
    simp
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- The opposite composition for band reindexing. -/
theorem reindexBands_apply_symm (equivalence : B ≃ B')
    (state : WholeState V E B') :
    reindexBands equivalence (reindexBands equivalence.symm state) = state := by
  simpa using reindexBands_symm_reindex equivalence.symm state

/-! ## The description type and its explicit `Fin` schema -/

/-- The complete finite classical stereo description.  It is the whole state; the name records the
intended public role. -/
abbrev FiniteClassicalStereoDescription (V E B : Type*) [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] :=
  WholeState V E B

/-- The same-schema encoded description at explicit cardinalities.  No `V`, `E` or `B` occurs in
the type arguments: only `Fin nV`, `Fin nE`, `Fin nB`. -/
abbrev EncodedDescription (nV nE nB : ℕ) :=
  FiniteClassicalStereoDescription (Fin nV) (Fin nE) (Fin nB)

/-- The public relabelling operation on descriptions. -/
def relabelDescription (e : V ≃ W) (description : FiniteClassicalStereoDescription V E B) :
    FiniteClassicalStereoDescription W E B :=
  relabelWholeState e description

/-- Double relabelling of a description is the identity. -/
theorem relabelDescription_symm (e : V ≃ W)
    (description : FiniteClassicalStereoDescription V E B) :
    relabelDescription e.symm (relabelDescription e description) = description :=
  relabelWholeState_symm e description

/-- The opposite composition: relabelling back by the forward equivalence after the inverse
relabelling is also the identity.  This orientation is the one needed for encoding a decoded
payload. -/
theorem relabelDescription_apply_symm (e : V ≃ W)
    (description : FiniteClassicalStereoDescription W E B) :
    relabelDescription e (relabelDescription e.symm description) = description := by
  simpa using relabelWholeState_symm e.symm description

/-- The public description relabelling maps the ordered frame list by the same common atom
equivalence, preserving order and duplicates. -/
@[simp] theorem relabelDescription_frames (e : V ≃ W)
    (description : FiniteClassicalStereoDescription V E B) :
    (relabelDescription e description).frames =
      description.frames.map (relabelFrameAnnotation e) := rfl

/-! ## Encoding into the same schema at `Fin` cardinalities and decoding -/

/-- Encode a description into the same schema.  The atom, edge and band index types are replaced
by `Fin` types through the three supplied equivalences; the graph, all atom references and all
channel data are relabelled by exactly those equivalences.  The result type contains no `V`, `E` or
`B`. -/
noncomputable def encodeDescription
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B) :=
  reindexBands eB (reindexEdges eE (relabelDescription eV description))

/-- Decode an encoded description using only the three equivalences and the encoded payload.  No
original description and no `V`-labelled source is required or available. -/
noncomputable def decodeDescription
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (encoded : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :
    FiniteClassicalStereoDescription V E B :=
  relabelDescription eV.symm (reindexEdges eE.symm (reindexBands eB.symm encoded))

/-- Decoding an encoded description recovers the original description exactly. -/
theorem decodeDescription_encodeDescription
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    decodeDescription eV eE eB (encodeDescription eV eE eB description) = description := by
  unfold decodeDescription encodeDescription
  rw [reindexBands_symm_reindex, reindexEdges_symm_reindex, relabelDescription_symm]

/-- Encoding a decoded payload recovers the payload exactly. -/
theorem encodeDescription_decodeDescription
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (encoded : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :
    encodeDescription eV eE eB (decodeDescription eV eE eB encoded) = encoded := by
  unfold decodeDescription encodeDescription
  rw [relabelDescription_apply_symm, reindexEdges_apply_symm, reindexBands_apply_symm]

/-- Encoding exposes exactly the source frame list relabelled by the atom enumeration.  Order,
duplicates, selected site identities and exact real planes are retained, and no original
`V`-labelled frame source is stored. -/
@[simp] theorem encodeDescription_frames
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (encodeDescription eV eE eB description).frames =
      description.frames.map (relabelFrameAnnotation eV) := by
  unfold encodeDescription reindexBands reindexEdges relabelDescription relabelWholeState
  rfl

/-- Decoding recovers exactly the encoded frame list relabelled by the inverse enumeration.  Only
the encoded payload and the equivalence are used. -/
@[simp] theorem decodeDescription_frames
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (encoded : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :
    (decodeDescription eV eE eB encoded).frames =
      encoded.frames.map (relabelFrameAnnotation eV.symm) := by
  unfold decodeDescription reindexBands reindexEdges relabelDescription relabelWholeState
  rfl

/-- Whole encoded-frame recovery: decoding an encoded description returns the source frame list
exactly, including order and duplicates. -/
theorem decodeDescription_encodeDescription_frames
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (description : FiniteClassicalStereoDescription V E B) :
    (decodeDescription eV eE eB (encodeDescription eV eE eB description)).frames =
      description.frames := by
  rw [decodeDescription_encodeDescription]

/-- Whole encoded-frame recovery in the opposite direction: re-encoding a decoded payload returns
exactly its frame list, including order and duplicates. -/
theorem encodeDescription_decodeDescription_frames
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (encoded : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :
    (encodeDescription eV eE eB (decodeDescription eV eE eB encoded)).frames =
      encoded.frames := by
  rw [encodeDescription_decodeDescription]

/-- Encoding is injective. -/
theorem encodeDescription_injective
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) :
    Function.Injective (encodeDescription eV eE eB) := by
  intro first second equal
  calc
    first = decodeDescription eV eE eB (encodeDescription eV eE eB first) :=
      (decodeDescription_encodeDescription eV eE eB first).symm
    _ = decodeDescription eV eE eB (encodeDescription eV eE eB second) := by rw [equal]
    _ = second := decodeDescription_encodeDescription eV eE eB second

/-- Encoding is bijective onto the same-schema encoded type. -/
theorem encodeDescription_bijective
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) :
    Function.Bijective (encodeDescription eV eE eB) :=
  ⟨encodeDescription_injective eV eE eB, fun encoded =>
    ⟨decodeDescription eV eE eB encoded,
      encodeDescription_decodeDescription eV eE eB encoded⟩⟩

/-- The image of a set of whole descriptions under encoding. -/
noncomputable def encodeDescriptionSet
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (descriptions : Set (FiniteClassicalStereoDescription V E B)) :
    Set (EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :=
  encodeDescription eV eE eB '' descriptions

/-- Whole-set recovery: decoding the encoded image of a set of descriptions gives back exactly that
set.  Because the operation is applied to whole records, all cross-channel correlations are
retained; no channel is decoded independently. -/
theorem decodeDescription_image_encodeDescriptionSet
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (descriptions : Set (FiniteClassicalStereoDescription V E B)) :
    decodeDescription eV eE eB '' encodeDescriptionSet eV eE eB descriptions = descriptions := by
  rw [encodeDescriptionSet, Set.image_image]
  have h : (decodeDescription eV eE eB ∘ encodeDescription eV eE eB) = id := by
    funext description
    exact decodeDescription_encodeDescription eV eE eB description
  change (decodeDescription eV eE eB ∘ encodeDescription eV eE eB) '' descriptions =
    descriptions
  rw [h, Set.image_id]

/-! ## Public adapters to the existing independent encodings -/

/-- Convert one independently stored role annotation (with its membership in the ledger) to the
existing broad joint-core annotation.  The occurrence bound and compatibility proof are taken from
the whole-state validity field, not assumed. -/
noncomputable def toBroadAnnotation (state : WholeState V E B)
    (annotation : RoleAnnotation V) (member : annotation ∈ state.roles) :
    BroadAnnotation state.graph :=
  let bound := Classical.choose (state.role_valid annotation member)
  { index := ⟨annotation.interactionIndex, bound⟩
    role := annotation.role
    compatible := Classical.choose_spec (state.role_valid annotation member) }

/-- View the whole role channel as the existing broad joint state: the shared conformation plus the
ordered ledger of broad annotations.  The ledger order and multiplicity are preserved. -/
noncomputable def toBroadJointState (state : WholeState V E B) :
    BroadJointState state.graph where
  conformation := state.conformation
  ledger := state.roles.attach.map fun annotation =>
    toBroadAnnotation state annotation.1 annotation.2

/-- Compose the broad joint state with the existing `broadDecoration` bridge, producing the encoded
role decorations at the certified source.  This is a composition of existing constructors. -/
noncomputable def encodedRoleDecorations (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    List (InteractionRoles.RoleDecoration
      (state.graph.certifiedEncoding enumeration).input.molecule) :=
  (toBroadJointState state).ledger.map
    (JointCoreEncoding.broadDecoration state.graph enumeration)

/-- View a present electronic channel as the staged `IndependentElectronicSiteSource`: the actual
counts and the unpaired tie are taken from the whole state, not assumed. -/
def toIndependentElectronicSiteSource (state : WholeState V E B)
    (channel : ElectronicChannel V) (present : state.electronic? = some channel) :
    IndependentElectronicSiteSource state.graph where
  siteCounts := channel.counts
  unpaired_tied := state.electronic_unpaired channel present

/-- The staged per-site evidence assignment of a present channel, indexed by actual counted
owner/kind/slot identities. -/
def electronicAssignment (state : WholeState V E B)
    (channel : ElectronicChannel V) (_present : state.electronic? = some channel) :
    IndependentSiteAssignment channel.counts ReferenceGeometryEvidence :=
  channel.toSiteAssignment

/-- The optional staged electronic source.  An absent inventory stays absent; a present inventory
is tied to the graph through the whole-state unpaired agreement. -/
def electronicSource? (state : WholeState V E B) :
    Option (ElectronicChannel V × IndependentElectronicSiteSource state.graph) :=
  match h : state.electronic? with
  | none => none
  | some channel =>
      some ⟨channel, toIndependentElectronicSiteSource state channel h⟩

section BandAdapter

variable {V₀ : Type} [DecidableEq V₀] [Fintype V₀] {E₀ B₀ : Type} [Fintype E₀] [Fintype B₀]

/-- View the whole band channel as the existing independent band attachment family.  The shared
independent band carrier is universe-zero (`IndependentBandAttachment` is declared with
`V : Type`), so this adapter is stated at universe zero.  The graph and the single shared
conformation are supplied from the whole state, and every per-band attachment type, atom function,
parameter function and agreement proof is reused literally. -/
def toIndependentBandAttachment (state : WholeState V₀ E₀ B₀) :
    OrganicStereoIndependentBandEncoding.IndependentBandAttachment V₀ where
  graph := state.graph
  conformation := state.conformation
  bandIndex := B₀
  fintypeBandIndex := inferInstance
  band := fun band => (state.bandFamily band).band
  Attachment := fun band => (state.bandFamily band).Attachment
  fintypeAttachment := fun band => (state.bandFamily band).fintypeAttachment
  atom := fun band record => (state.bandFamily band).atom record
  parameter := fun band record => (state.bandFamily band).parameter record
  agreement := fun band record => state.band_agreement band record

/-- Compose with the existing `encodeFamily`: one certified partial band per independent band
index. -/
noncomputable def encodedBandFamily (state : WholeState V₀ E₀ B₀)
    (enumeration : V₀ ≃ Fin (Fintype.card V₀)) (band : B₀) :
    CertifiedPartialBand (state.graph.certifiedEncoding enumeration) :=
  OrganicStereoIndependentBandEncoding.encodeFamily
    (toIndependentBandAttachment state) enumeration band

/-- Compose with the existing `encodeAll`: the band family enumerated by `Fin (Fintype.card B₀)`.
No band is required, so an empty band type gives an empty `Fin 0` family. -/
noncomputable def encodedBandAt (state : WholeState V₀ E₀ B₀)
    (enumeration : V₀ ≃ Fin (Fintype.card V₀)) (index : Fin (Fintype.card B₀)) :
    CertifiedPartialBand (state.graph.certifiedEncoding enumeration) :=
  OrganicStereoIndependentBandEncoding.encodeAll
    (toIndependentBandAttachment state) enumeration index

end BandAdapter

/-- The explicit physical non-degeneracy hypotheses needed to reuse the existing independent
bond-path type.  These are not fields of the description; they are a visible adapter argument. -/
structure PathGeometryValid (state : WholeState V E B) : Prop where
  /-- Two distinct edges never name the same source interaction occurrence. -/
  occurrence_injective :
    Function.Injective fun edge => (state.paths edge).interactionIndex
  /-- Distinct atoms occupy distinct points. -/
  atom_injective : Function.Injective state.conformation
  /-- Every arc is injective on the unit interval. -/
  arc_injective : ∀ edge, Function.Injective (state.paths edge).arc
  /-- Arc interiors avoid every atom position. -/
  interior_avoids_atoms : ∀ edge (t : I), t ≠ 0 → t ≠ 1 → ∀ atom,
    (state.paths edge).arc t ≠ state.conformation atom
  /-- Distinct arcs meet only at a common endpoint atom. -/
  intersects_only_at_common_endpoints :
    ∀ edge other (t s : I), edge ≠ other →
      (state.paths edge).arc t = (state.paths other).arc s →
        ∃ atom : V,
          sourceEndpointAt? (fun edge => (state.paths edge).source)
              (fun edge => (state.paths edge).target) edge t = some atom ∧
            sourceEndpointAt? (fun edge => (state.paths edge).source)
              (fun edge => (state.paths edge).target) other s = some atom

/-- View the whole path channel as the existing `IndependentBondPathData`, using the shared graph
and conformation and the explicit physical non-degeneracy hypotheses. -/
noncomputable def toIndependentBondPathData (state : WholeState V E B)
    (valid : PathGeometryValid state) : IndependentBondPathData V E where
  graph := state.graph
  conformation := state.conformation
  interactionOccurrence := fun edge => (state.paths edge).interactionIndex
  interactionOccurrence_lt := fun edge => Classical.choose (state.path_valid edge)
  interactionOccurrence_injective := valid.occurrence_injective
  source := fun edge => (state.paths edge).source
  target := fun edge => (state.paths edge).target
  source_ne_target := fun edge => (state.paths edge).source_ne_target
  arc := fun edge => (state.paths edge).arc
  participants_exact := fun edge =>
    (Classical.choose_spec (state.path_valid edge)).1
  kind_selected := fun edge =>
    (Classical.choose_spec (state.path_valid edge)).2
  source_endpoint := fun edge => state.path_source_endpoint edge
  target_endpoint := fun edge => state.path_target_endpoint edge
  atom_injective := valid.atom_injective
  arc_injective := valid.arc_injective
  interior_avoids_atoms := valid.interior_avoids_atoms
  intersects_only_at_common_endpoints := valid.intersects_only_at_common_endpoints

/-- Compose with the existing `toBondPathTable`: the realization table at the encoded graph and the
encoded conformation. -/
noncomputable def toBondPathTable (state : WholeState V E B)
    (valid : PathGeometryValid state) (enumeration : V ≃ Fin (Fintype.card V)) :=
  (toIndependentBondPathData state valid).toBondPathTable enumeration

/-- Encode the optional exact rational provenance through the same enumeration.  Absence stays
absent and every supplied rational coordinate is retained literally. -/
def encodedRationalPositions? (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    Option (Fin (Fintype.card V) → CartesianPoint3) :=
  state.rationalPositions?.map fun positions index => positions (enumeration.symm index)

/-- Encode the sparse partial drawing positions.  A missing coordinate remains `none` at its
encoded atom index; an explicitly supplied origin remains `some origin`. -/
def encodedDiagramPartial? (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V)) :
    Option (Fin (Fintype.card V) → Option CartesianPoint2) :=
  state.diagramPartial?.map (SourcePartialPositions.encode enumeration)

/-- The encoded public drawing channel: absent stays absent, and present positions are encoded
through the same enumeration by the existing `OrganicDiagramSource.encodeDiagram`. -/
def encodedDiagram? (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V)) : Option DiagramConfiguration :=
  state.diagram?.map (OrganicDiagramSource.encodeDiagram enumeration)

/-- The existing authoritative-source bridge with the encoded graph and the optional public
drawing channel attached.  The spatial channel stays absent, exactly as in the existing
constructor; independently labelled diagram positions are preserved when present. -/
def encodedAuthoritativeView (state : WholeState V E B)
    (enumeration : V ≃ Fin (Fintype.card V)) : AuthoritativeChemicalInput :=
  encodeAuthoritativeWithDiagram state.graph enumeration state.diagram? none

/-! ## Public frame-annotation updater -/

/-- Attach an ordered frame-annotation list to a whole state without changing any physical
channel.  The list is the existing `FrameAnnotation` sum, retained verbatim in order: duplicates
and repeated references remain meaningful, and each annotation keeps its own ordered atom
references, selected site identities and exact real plane. -/
def withFrames (state : WholeState V E B) (frames : List (FrameAnnotation V)) :
    WholeState V E B :=
  { state with frames := frames }

/-- The attached frame list is recovered exactly. -/
@[simp] theorem withFrames_frames (state : WholeState V E B)
    (frames : List (FrameAnnotation V)) :
    (withFrames state frames).frames = frames := rfl

/-- Attaching frames leaves the interaction graph unchanged. -/
@[simp] theorem withFrames_graph (state : WholeState V E B)
    (frames : List (FrameAnnotation V)) :
    (withFrames state frames).graph = state.graph := rfl

/-- Attaching frames leaves the shared real conformation unchanged. -/
@[simp] theorem withFrames_conformation (state : WholeState V E B)
    (frames : List (FrameAnnotation V)) :
    (withFrames state frames).conformation = state.conformation := rfl

/-- Attaching frames leaves the ordered role ledger unchanged. -/
@[simp] theorem withFrames_roles (state : WholeState V E B)
    (frames : List (FrameAnnotation V)) :
    (withFrames state frames).roles = state.roles := rfl

/-- Attaching frames leaves the ordered fragment channel unchanged. -/
@[simp] theorem withFrames_fragments (state : WholeState V E B)
    (frames : List (FrameAnnotation V)) :
    (withFrames state frames).fragments = state.fragments := rfl

/-- Attaching frames leaves the optional residue ledger unchanged. -/
@[simp] theorem withFrames_residueLedger? (state : WholeState V E B)
    (frames : List (FrameAnnotation V)) :
    (withFrames state frames).residueLedger? = state.residueLedger? := rfl

/-- The frame updater commutes with the common atom relabelling: attaching then relabelling is the
same as relabelling the supplied list elementwise and then attaching. -/
@[simp] theorem relabelWholeState_withFrames (e : V ≃ W)
    (state : WholeState V E B) (frames : List (FrameAnnotation V)) :
    relabelWholeState e (withFrames state frames) =
      withFrames (relabelWholeState e state)
        (frames.map (relabelFrameAnnotation e)) := by
  apply WholeState.extEq <;> simp [withFrames, relabelWholeState]

/-! ## Public fragment-annotation adapter -/

/-- Attach an ordered fragment-annotation list to a whole state without changing any physical
channel.  The list remains the existing `FragmentAnnotation` payload, with its atom support and
ordered scoped bindings in the same atom language. -/
def withFragments (state : WholeState V E B) (fragments : List (FragmentAnnotation V)) :
    WholeState V E B :=
  { state with fragments := fragments }

/-- Public adapter composing the existing `encodeFragment` constructor: a list of residue fragments
already encoded at `Fin n` becomes an ordered `FragmentAnnotation V` channel.  Each fragment's
locant cover is supplied explicitly by the caller; this module never enumerates a locant family. -/
def fragmentAnnotationsOfEncoded {Locant : Type*} (codec : LocantCodec Locant) {n : ℕ}
    (enumeration : V ≃ Fin n) (fragments : List (ResidueFragment Locant n))
    (cover : ResidueFragment Locant n → List Locant) : List (FragmentAnnotation V) :=
  fragments.map fun fragment => encodeFragment codec enumeration fragment (cover fragment)

/-- Decoding the adapted list by the existing `decodeFragment` recovers every original encoded
residue fragment.  The cover hypotheses are exactly the pointwise hypotheses of the existing
recovery theorem, lifted over the ordered list. -/
theorem decodeFragmentAnnotations_encode {Locant : Type*} (codec : LocantCodec Locant) {n : ℕ}
    (enumeration : V ≃ Fin n) (fragments : List (ResidueFragment Locant n))
    (cover : ResidueFragment Locant n → List Locant)
    (coverNodup : ∀ fragment ∈ fragments, (cover fragment).Nodup)
    (covers : ∀ fragment ∈ fragments, ∀ (locant : Locant) (atom : Fin n),
      fragment.incidence locant = some atom → locant ∈ cover fragment) :
    (fragmentAnnotationsOfEncoded codec enumeration fragments cover).map
        (decodeFragment codec enumeration) = fragments := by
  unfold fragmentAnnotationsOfEncoded
  rw [List.map_map]
  calc
    fragments.map (decodeFragment codec enumeration ∘
        fun fragment => encodeFragment codec enumeration fragment (cover fragment)) =
        fragments.map id := by
      apply List.map_congr_left
      intro fragment member
      exact decodeFragment_encodeFragment codec enumeration fragment (cover fragment)
        (coverNodup fragment member) (covers fragment member)
    _ = fragments := List.map_id fragments

/-! ## Public residue-ledger adapter -/

/-- Attach an optional residue-link and naming-hierarchy channel without changing any physical
channel of the whole state. -/
def withResidueLedger (state : WholeState V E B) (ledger : ResidueLedgerChannel V) :
    WholeState V E B :=
  { state with residueLedger? := some ledger }

/-- Public adapter composing the existing `encode` constructor from a real residue incidence ledger
and its certified input.  The ledger's residue count and the source interaction-list length become
the channel's declared finite occurrence budgets; fragment atom references are encoded through the
same external equivalence `e` that the caller uses for the rest of the record.  The certified
original input itself is not stored in the channel. -/
def residueLedgerChannelOfEncoded {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) : ResidueLedgerChannel V where
  residueCount := ledger.residueCount
  interactionCount := input.input.molecule.interactions.length
  annotation := TetraStereo.OneCenter.encode codec e ledger cover

@[simp] theorem residueLedgerChannelOfEncoded_residueCount {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) :
    (residueLedgerChannelOfEncoded codec e ledger cover).residueCount =
      ledger.residueCount := rfl

@[simp] theorem residueLedgerChannelOfEncoded_interactionCount {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant) :
    (residueLedgerChannelOfEncoded codec e ledger cover).interactionCount =
      input.input.molecule.interactions.length := rfl

/-- Decoding the adapted channel's annotation by the existing `decodeView?` recovers exactly the
observable ledger content: every residue fragment, the ordered link list and the optional naming
hierarchy.  The cover hypotheses are precisely the existing constructor's recovery hypotheses. -/
theorem decodeView?_residueLedgerChannelOfEncoded {Locant V : Type*}
    {input : CertifiedAuthoritativeChemicalInput}
    (codec : LocantCodec Locant) (e : V ≃ Fin input.input.molecule.atomCount)
    (ledger : ResidueIncidenceLedger Locant input)
    (cover : Fin ledger.residueCount → List Locant)
    (coverNodup : ∀ index, (cover index).Nodup)
    (covers : ∀ (index : Fin ledger.residueCount) (locant : Locant)
      (atom : Fin input.input.molecule.atomCount),
        (ledger.residue index).incidence locant = some atom → locant ∈ cover index) :
    decodeView? codec e (residueLedgerChannelOfEncoded codec e ledger cover).annotation =
      some (viewOfLedger ledger) := by
  unfold residueLedgerChannelOfEncoded
  exact decodeView?_encode codec e ledger cover coverNodup covers

/-! ## A concrete non-vacuous example -/

namespace FiniteClassicalStereoDescriptionExample

/-- The hydrogen element (atomic number one). -/
def hydrogen : PeriodicElement where
  atomicNumber := 1
  positive := by decide
  atMost118 := by decide

/-- A two-atom hydrogen graph with one covalent interaction. -/
def graph : FiniteAtomInteractionHypergraph (Fin 2) where
  atomData := fun _ => { element := hydrogen }
  interactions := [([0, 1], SemanticInteractionKind.covalent 1)]
  arity_ge_two := by
    intro edge member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl
    decide
  participants_nodup := by
    intro edge member
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
    rcases member with rfl
    decide

/-- Two distinct real positions. -/
def conformation : MolecularConformation (Fin 2) :=
  fun index =>
    if index = 0 then (0 : EuclideanSpace ℝ (Fin 3))
    else EuclideanSpace.single 0 (1 : ℝ)

/-- The straight segment arc between two points. -/
def segmentArc (start finish : EuclideanSpace ℝ (Fin 3)) : C(I, EmbeddedReal3) where
  toFun parameter := (1 - (parameter : ℝ)) • start + (parameter : ℝ) • finish
  continuous_toFun := by continuity

@[simp] theorem segmentArc_zero (start finish : EuclideanSpace ℝ (Fin 3)) :
    segmentArc start finish 0 = start := by
  simp [segmentArc]

@[simp] theorem segmentArc_one (start finish : EuclideanSpace ℝ (Fin 3)) :
    segmentArc start finish 1 = finish := by
  simp [segmentArc]

/-- One ordinary-bond role on the single interaction. -/
def role : RoleAnnotation (Fin 2) where
  interactionIndex := 0
  role := PhysicalRole.ordinaryBond 1 0 1 (by decide)

/-- One path from atom zero to atom one along the segment. -/
def path : PathAnnotation (Fin 2) where
  interactionIndex := 0
  source := 0
  target := 1
  source_ne_target := by decide
  arc := segmentArc (conformation 0) (conformation 1)

/-- The example description: one interaction, one role, one path, no bands, no electronic
inventory and no drawing data.  It is deliberately non-vacuous in the
interaction, role and path channels while all optional channels are genuinely absent (`none`, not a
fabricated zero). -/
def description : FiniteClassicalStereoDescription (Fin 2) (Fin 1) (Fin 0) where
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
  roles := [role]
  role_valid := by
    intro annotation member
    simp only [List.mem_singleton] at member
    subst annotation
    refine ⟨by simp [graph, role], ?_⟩
    simp [Compatible, PhysicalRole.supportFinset, PhysicalRole.supportList,
      PhysicalRole.supportLength, PhysicalRole.supportKind, PhysicalRole.kind,
      graph, role]
  paths := fun _ => path
  path_valid := by
    intro edge
    fin_cases edge
    refine ⟨by simp [graph, path], ?_, ?_⟩
    · simp [graph, path]
    · simp [graph, path, SemanticInteractionKind.isSelectedPairKind]
  path_source_endpoint := by
    intro edge
    fin_cases edge
    simp [path, segmentArc, conformation]
  path_target_endpoint := by
    intro edge
    fin_cases edge
    simp [path, segmentArc, conformation]
  bandFamily := fun band => Fin.elim0 band
  band_agreement := by
    intro band record
    exact Fin.elim0 band
  diagram? := none
  diagramPartial? := none
  diagramIncidence := []
  diagram_valid := by
    intro row member
    simp at member

/-- The example has exactly one interaction. -/
theorem description_interactions_length : description.graph.interactions.length = 1 := rfl

/-- The example has exactly one role annotation. -/
theorem description_roles_length : description.roles.length = 1 := rfl

/-- The example has exactly one path. -/
theorem description_paths_card : Fintype.card (Fin 1) = 1 := rfl

/-- The concrete example round-trips through the same-schema encoding at its own cardinalities. -/
theorem description_roundtrip :
    decodeDescription (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1)) (Equiv.refl (Fin 0))
        (encodeDescription (Equiv.refl (Fin 2)) (Equiv.refl (Fin 1))
          (Equiv.refl (Fin 0)) description) = description :=
  decodeDescription_encodeDescription _ _ _ description

end FiniteClassicalStereoDescriptionExample

end

end TetraStereo.OneCenter
