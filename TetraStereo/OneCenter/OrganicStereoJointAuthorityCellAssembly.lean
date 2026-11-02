import TetraStereo.OneCenter.OrganicStereoAllAuthorityEntries
import TetraStereo.OneCenter.OrganicStereoSpatialSupportMolecularAssembly
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false






















































namespace TetraStereo.OneCenter
namespace OrganicStereoJointAuthorityCellAssembly

open OrganicStereoAllAuthorityEntries
open OrganicStereoSpatialSupportMolecularAssembly
open OrganicStereoMolecularCanonicalTransport
open OrganicStereoMolecularEvidenceAssembly
open OrganicStereoMixedSourceAssembly
open OrganicStereoAuthorityMixedSourceAssembly
open OrganicStereoNativeP94SourceContext
open OccurrenceSpatialSupportExperiment

variable {V : Type} [DecidableEq V] [Fintype V]
variable {LigandId LigandKind FragmentId FragmentKind : Type}
variable {State Framework : Type}
variable {BaseName Numbering Locant Prefix : Type}

/-! ## The joint request -/

/-- The joint source record: one independent spatial molecular evidence (which carries the actual
core and the heterogeneous cells), one enumeration, the one structural certificate of the
reconstructed source, the complete policy record, and one ordered heterogeneous raw-entry list at
that core. -/
structure JointRequest (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type) where
  /-- The complete authority policy record. -/
  policies : AllAuthorityPolicies
  /-- The actual independent molecular evidence together with its occurrence-bound cells. -/
  spatial : OrganicSpatialMolecularEvidence V
  /-- The one explicit atom enumeration. -/
  enumeration : V ≃ Fin (Fintype.card V)
  /-- The structural certificate of the reconstructed common source. -/
  source_well_formed : (recoveredSource spatial.core enumeration).StructurallyWellFormed
  /-- The one ordered heterogeneous raw-entry list, at the spatial evidence's own core. -/
  entries : List (RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix policies spatial.core enumeration)

/-! ## The joint target -/

/-- The joint representation: one actual canonical molecular output, the one ordered list of
native entries at that output's *decoded* core and *actual* atom equivalence, and the encoded
cell family indexed by the actual canonical graph, conformation and ordered role ledger. -/
structure JointRepresentation (V : Type) [DecidableEq V] [Fintype V]
    (LigandId LigandKind FragmentId FragmentKind : Type)
    (State Framework : Type)
    (BaseName Numbering Locant Prefix : Type) where
  /-- The complete authority policy record. -/
  policies : AllAuthorityPolicies
  /-- The one actual canonical molecular output. -/
  canonical : CanonicalOrganicMolecularRepresentation V
  /-- The transported structural certificate of the source reconstructed from the decoded core.
  This is a proposition about the decoded source, not a stored source record. -/
  source_well_formed :
    (recoveredSource (decodedCore canonical) canonical.atomEquiv).StructurallyWellFormed
  /-- The one ordered heterogeneous native entry list at the recovered core. -/
  entries : List (NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
    BaseName Numbering Locant Prefix policies (decodedCore canonical) canonical.atomEquiv)
  /-- The encoded cell family over the actual canonical graph, conformation and role ledger. -/
  cells : List (EncodedSpatialMolecularCell (Fintype.card V)
    canonical.state.graph canonical.state.conformation canonical.state.roles)

/-! ## Assembly

The canonical representation is assembled exactly once, by `assembleSpatial`; its cells are reused
verbatim.  The entry list is encoded row by row with the concrete union codec and transported along
the proved canonical core inverse `decodedCore (canonicalAssemble e core) = core`. -/

/-- The canonical assembly's decoded core is the supplied core, stated at the *same* decoder
`decodedCore` that the spatial assembly uses.  Keeping both sides of the transport at the concrete
decoder makes the dependent transports syntactically aligned. -/
theorem decodedCore_canonicalAssemble (enumeration : V ≃ Fin (Fintype.card V))
    (request : OrganicMolecularEvidence V) :
    decodedCore (canonicalAssemble enumeration request) = request :=
  decode_canonicalAssemble enumeration request

/-- Assemble the joint output. -/
noncomputable def assembleJoint
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    JointRepresentation (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix where
  policies := request.policies
  canonical := (assembleSpatial request.enumeration request.spatial).canonical
  source_well_formed :=
    (decodedCore_canonicalAssemble request.enumeration request.spatial.core).symm ▸
      request.source_well_formed
  entries :=
    (decodedCore_canonicalAssemble request.enumeration request.spatial.core).symm ▸
      request.entries.map
        (encodeEntry request.spatial.core request.enumeration request.source_well_formed)
  cells := (assembleSpatial request.enumeration request.spatial).cells

/-- Decode the joint output.  The cells are decoded by the actual `decodeSpatial` at the canonical
output's own atom equivalence; the rows are decoded by the concrete `decodeEntry` at the same
recovered core `decodedCore canonical`. -/
noncomputable def decodeJoint
    (representation : JointRepresentation (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix where
  policies := representation.policies
  spatial := OrganicStereoSpatialSupportMolecularAssembly.decodeSpatial
    representation.canonical.atomEquiv
    { canonical := representation.canonical, cells := representation.cells }
  enumeration := representation.canonical.atomEquiv
  source_well_formed := representation.source_well_formed
  entries := representation.entries.map
    (decodeEntry (decodedCore representation.canonical) representation.canonical.atomEquiv)

/-! ## Definitional projections -/

@[simp] theorem assembleJoint_policies
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (assembleJoint request).policies = request.policies := rfl

@[simp] theorem assembleJoint_canonical
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (assembleJoint request).canonical =
      (assembleSpatial request.enumeration request.spatial).canonical := rfl

@[simp] theorem assembleJoint_entries
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (assembleJoint request).entries =
      (decodedCore_canonicalAssemble request.enumeration request.spatial.core).symm ▸
        request.entries.map
          (encodeEntry request.spatial.core request.enumeration request.source_well_formed) := rfl

@[simp] theorem assembleJoint_cells
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (assembleJoint request).cells =
      (assembleSpatial request.enumeration request.spatial).cells := rfl

@[simp] theorem decodeJoint_policies
    (representation : JointRepresentation (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint representation).policies = representation.policies := rfl

@[simp] theorem decodeJoint_spatial
    (representation : JointRepresentation (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint representation).spatial =
      OrganicStereoSpatialSupportMolecularAssembly.decodeSpatial
        representation.canonical.atomEquiv
        { canonical := representation.canonical, cells := representation.cells } := rfl

@[simp] theorem decodeJoint_enumeration
    (representation : JointRepresentation (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint representation).enumeration = representation.canonical.atomEquiv := rfl

@[simp] theorem decodeJoint_entries
    (representation : JointRepresentation (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint representation).entries =
      representation.entries.map
        (decodeEntry (decodedCore representation.canonical)
          representation.canonical.atomEquiv) := rfl

/-! ## The full source-record inverse -/

/-- The spatial component of the joint inverse: the decoded evidence, with its exact core and its
exact heterogeneous cell family, is the supplied evidence. -/
theorem decodeJoint_assembleJoint_spatial
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint (assembleJoint request)).spatial = request.spatial := by
  simpa only [decodeJoint, assembleJoint] using
    decodeSpatial_assembleSpatial request.enumeration request.spatial

/-- The structural certificate component is recovered: the transported certificate in the actual
output and the supplied certificate are proofs of the reconstructed source propositions, so they
are heterogeneously equal by proof irrelevance (and propositionally equal by `propext`). -/
theorem decodeJoint_assembleJoint_source_well_formed
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    HEq (decodeJoint (assembleJoint request)).source_well_formed
      request.source_well_formed :=
  proof_irrel_heq _ _

/-- The ordered entry list is recovered heterogeneously at the decoded and the supplied core. -/
theorem decodeJoint_assembleJoint_entries_heq
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    HEq (decodeJoint (assembleJoint request)).entries request.entries := by
  show HEq (((decodedCore_canonicalAssemble request.enumeration request.spatial.core).symm ▸
      request.entries.map (encodeEntry request.spatial.core request.enumeration
        request.source_well_formed)).map
      (decodeEntry (decodedCore (canonicalAssemble request.enumeration request.spatial.core))
        request.enumeration)) request.entries
  exact map_decodeEntry_encodeEntry_eqRec
    (first := decodedCore (canonicalAssemble request.enumeration request.spatial.core))
    (second := request.spatial.core)
    (policies := request.policies)
    (enumeration := request.enumeration)
    (equal := decodedCore_canonicalAssemble request.enumeration request.spatial.core)
    (source_well_formed := request.source_well_formed)
    (entries := request.entries)

/-- Extensionality of joint requests.  The proposition-valued source certificate is identified by
proof irrelevance once the policies, the spatial evidence, the enumeration and the ordered entries
agree. -/
theorem JointRequest.extEq
    {first second : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix}
    (policies_eq : first.policies = second.policies)
    (spatial_eq : first.spatial = second.spatial)
    (enumeration_eq : first.enumeration = second.enumeration)
    (entries : HEq first.entries second.entries) : first = second := by
  obtain ⟨firstPolicies, firstSpatial, firstEnumeration, firstWellFormed,
    firstEntries⟩ := first
  obtain ⟨secondPolicies, secondSpatial, secondEnumeration, secondWellFormed,
    secondEntries⟩ := second
  dsimp only at policies_eq spatial_eq enumeration_eq entries
  cases policies_eq
  cases spatial_eq
  cases enumeration_eq
  have entriesEq : firstEntries = secondEntries := eq_of_heq entries
  cases entriesEq
  rfl

/-- **Full source-record inverse.**  Decoding the joint assembly of an arbitrary joint request
returns the whole source record literally: the policy record, the complete independent spatial
evidence (core and every cell), the enumeration, the source certificate, and the one ordered
heterogeneous entry list with every family payload, interleaving, repetition and cross-family
correlation retained. -/
theorem decodeJoint_assembleJoint
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    decodeJoint (assembleJoint request) = request := by
  apply JointRequest.extEq
    (first := decodeJoint (assembleJoint request)) (second := request)
  · simp [decodeJoint, assembleJoint]
  · exact decodeJoint_assembleJoint_spatial request
  · simp [decodeJoint, assembleJoint]
  · exact decodeJoint_assembleJoint_entries_heq request

/-! ## Ordered individual-row recovery

The list is recovered position by position.  The pointwise statement is proved by the same
constructor-level inverse `decodeEntry_encodeEntry` used by the whole-list theorem, so this is a
genuine per-row recovery and not a cast of a stored native row. -/

/-- Pointwise form of the dependent ordered-list inverse: at every position the decoded row is the
supplied row. -/
theorem map_decodeEntry_encodeEntry_getElem?_heq
    {first second : OrganicMolecularEvidence V}
    {policies : AllAuthorityPolicies}
    {enumeration : V ≃ Fin (Fintype.card V)}
    (equal : first = second)
    (source_well_formed : (recoveredSource second enumeration).StructurallyWellFormed)
    (entries : List (RawEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix policies second enumeration))
    (index : ℕ) :
    HEq (((equal.symm ▸ entries.map
        (encodeEntry second enumeration source_well_formed)).map
      (decodeEntry first enumeration))[index]?) (entries[index]?) := by
  cases equal
  induction entries generalizing index with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      cases index with
      | zero =>
          simp only [List.map_cons, List.getElem?_cons_zero]
          exact heq_of_eq (congrArg some
            (decodeEntry_encodeEntry first enumeration source_well_formed head))
      | succ index =>
          simp only [List.map_cons, List.getElem?_cons_succ]
          exact inductionHypothesis index

/-- Every ordered position of the decoded joint entry list is exactly the supplied raw row at the
same position. -/
theorem decodeJoint_assembleJoint_entry_heq
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) (index : ℕ) :
    HEq ((decodeJoint (assembleJoint request)).entries[index]?)
      (request.entries[index]?) := by
  show HEq ((((decodedCore_canonicalAssemble request.enumeration request.spatial.core).symm ▸
      request.entries.map (encodeEntry request.spatial.core request.enumeration
        request.source_well_formed)).map
      (decodeEntry (decodedCore (canonicalAssemble request.enumeration request.spatial.core))
        request.enumeration))[index]?) (request.entries[index]?)
  exact map_decodeEntry_encodeEntry_getElem?_heq
    (first := decodedCore (canonicalAssemble request.enumeration request.spatial.core))
    (second := request.spatial.core)
    (policies := request.policies)
    (enumeration := request.enumeration)
    (equal := decodedCore_canonicalAssemble request.enumeration request.spatial.core)
    (source_well_formed := request.source_well_formed)
    (entries := request.entries)
    (index := index)

/-- The number of ordered rows is preserved exactly. -/
theorem decodeJoint_assembleJoint_entries_length
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint (assembleJoint request)).entries.length = request.entries.length := by
  have transported := eqRec_list_length
    (P := fun core => NativeEntry V LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix request.policies core request.enumeration)
    (decodedCore_canonicalAssemble request.enumeration request.spatial.core)
    (request.entries.map
      (encodeEntry request.spatial.core request.enumeration request.source_well_formed))
  simpa [decodeJoint_entries, assembleJoint_entries, List.length_map] using transported

/-- The decoded core of the joint assembly is exactly the supplied core. -/
theorem decodeJoint_assembleJoint_core
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint (assembleJoint request)).spatial.core = request.spatial.core :=
  congrArg OrganicSpatialMolecularEvidence.core
    (decodeJoint_assembleJoint_spatial request)

/-- The transported homogeneous form of the ordered-list inverse: read back at the supplied core,
the decoded list is the supplied list.  The transport is along the *proved decoded-core inverse*
`(decodeJoint (assembleJoint request)).spatial.core = request.spatial.core`, so the transported
list's index is syntactically the left-hand side of the used equality. -/
theorem decodeJoint_assembleJoint_entries_eq
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint_assembleJoint_core request) ▸
        (decodeJoint (assembleJoint request)).entries = request.entries :=
  eq_of_heq (eqRec_heq_iff.mpr (decodeJoint_assembleJoint_entries_heq request))

/-! ## Ordered individual-cell and full-map recovery -/

/-- The decoded cell family is the supplied cell family, with every occurrence index, anchor, full
continuous map and role position retained. -/
theorem decodeJoint_assembleJoint_cells
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint (assembleJoint request)).spatial.cells = request.spatial.cells :=
  congrArg OrganicSpatialMolecularEvidence.cells
    (decodeJoint_assembleJoint_spatial request)

/-- Every ordered cell position is recovered exactly. -/
theorem decodeJoint_assembleJoint_cell_getElem?_eq
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) (index : ℕ) :
    (decodeJoint (assembleJoint request)).spatial.cells[index]? =
      request.spatial.cells[index]? := by
  rw [decodeJoint_assembleJoint_cells]

/-- The dimension and the entire continuous map of the cell at every ordered position are
recovered exactly.  The map's codomain is dimension-dependent, so the pair is packed as a sigma
type. -/
theorem decodeJoint_assembleJoint_cell_map_getElem?_eq
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) (index : ℕ) :
    ((decodeJoint (assembleJoint request)).spatial.cells[index]?).map
        (fun cell : SpatialMolecularCell V =>
          (⟨cell.dimension, cell.map⟩ : Sigma (fun d : ℕ => C(Delta d, EmbeddedReal3)))) =
      (request.spatial.cells[index]?).map
        (fun cell : SpatialMolecularCell V =>
          (⟨cell.dimension, cell.map⟩ : Sigma (fun d : ℕ => C(Delta d, EmbeddedReal3)))) :=
  congrArg
    (fun cells => cells[index]?.map
      (fun cell : SpatialMolecularCell V =>
        (⟨cell.dimension, cell.map⟩ : Sigma (fun d : ℕ => C(Delta d, EmbeddedReal3)))))
    (decodeJoint_assembleJoint_cells request)

/-- At every present index the whole cell — including its dimension, its anchors, its ordered role
positions and its full continuous map — is recovered as the same cell. -/
theorem decodeJoint_assembleJoint_cell_eq_of_getElem?
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) (index : ℕ)
    (cell : SpatialMolecularCell V)
    (member : request.spatial.cells[index]? = some cell) :
    (decodeJoint (assembleJoint request)).spatial.cells[index]? = some cell := by
  rw [decodeJoint_assembleJoint_cell_getElem?_eq, member]

/-- The occurrence index of the cell at every ordered position is recovered exactly. -/
theorem decodeJoint_assembleJoint_cell_occurrence_getElem?
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) (index : ℕ) :
    ((decodeJoint (assembleJoint request)).spatial.cells[index]?).map
        (fun cell : SpatialMolecularCell V => cell.occurrenceIndex) =
      (request.spatial.cells[index]?).map
        (fun cell : SpatialMolecularCell V => cell.occurrenceIndex) :=
  congrArg
    (fun cells => cells[index]?.map (fun cell : SpatialMolecularCell V => cell.occurrenceIndex))
    (decodeJoint_assembleJoint_cells request)

/-! ## Actual graph, geometry, role, path and band projections -/

/-- The assembled canonical graph is exactly the canonically relabelled core graph. -/
theorem assembleJoint_canonical_state_graph
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (assembleJoint request).canonical.state.graph =
      relabelGraph request.enumeration request.spatial.core.graph :=
  canonicalAssemble_state_graph request.enumeration request.spatial.core

/-- The assembled canonical conformation is exactly the canonically reindexed core conformation. -/
theorem assembleJoint_canonical_state_conformation
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (assembleJoint request).canonical.state.conformation =
      MolecularConformation.reindex request.enumeration request.spatial.core.conformation :=
  canonicalAssemble_state_conformation request.enumeration request.spatial.core

/-- The assembled canonical ordered role ledger is exactly the canonically relabelled core role
ledger. -/
theorem assembleJoint_canonical_state_roles
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (assembleJoint request).canonical.state.roles =
      request.spatial.core.roles.map (relabelRoleAnnotation request.enumeration) :=
  canonicalAssemble_state_roles request.enumeration request.spatial.core

/-- The canonical output's atom equivalence is exactly the supplied enumeration. -/
@[simp] theorem assembleJoint_canonical_atomEquiv
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (assembleJoint request).canonical.atomEquiv = request.enumeration := rfl

/-- The assembled graph has exactly the interaction count of the source graph. -/
theorem assembleJoint_canonical_graph_length
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (assembleJoint request).canonical.state.graph.interactions.length =
      request.spatial.core.graph.interactions.length :=
  canonicalAssemble_graph_length request.enumeration request.spatial.core

/-- The canonical output preserves the exact optional path channel of the source core, including
`none` versus a supplied empty family. -/
theorem assembleJoint_decodedPaths?
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    decodedPaths? ((assembleJoint request).canonical |> canonicalDecode) =
      request.spatial.core.paths? :=
  assembleSpatial_paths? request.enumeration request.spatial

/-- The canonical output preserves the exact optional band channel of the source core. -/
theorem assembleJoint_decodedBands?
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    decodedBands? ((assembleJoint request).canonical |> canonicalDecode) =
      request.spatial.core.bands? :=
  assembleSpatial_bands? request.enumeration request.spatial

/-- The decoded graph is exactly the supplied core graph. -/
theorem decodeJoint_assembleJoint_graph
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint (assembleJoint request)).spatial.core.graph = request.spatial.core.graph :=
  congrArg (fun core : OrganicMolecularEvidence V => core.graph)
    (decodeJoint_assembleJoint_core request)

/-- The decoded conformation is exactly the supplied core conformation. -/
theorem decodeJoint_assembleJoint_conformation
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint (assembleJoint request)).spatial.core.conformation =
      request.spatial.core.conformation :=
  congrArg (fun core : OrganicMolecularEvidence V => core.conformation)
    (decodeJoint_assembleJoint_core request)

/-- The decoded ordered role ledger is exactly the supplied ordered role ledger. -/
theorem decodeJoint_assembleJoint_roles
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint (assembleJoint request)).spatial.core.roles = request.spatial.core.roles :=
  congrArg (fun core : OrganicMolecularEvidence V => core.roles)
    (decodeJoint_assembleJoint_core request)

/-- The decoded optional rational-coordinate channel is exactly the supplied channel. -/
theorem decodeJoint_assembleJoint_rationalPositions?
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint (assembleJoint request)).spatial.core.rationalPositions? =
      request.spatial.core.rationalPositions? :=
  congrArg (fun core : OrganicMolecularEvidence V => core.rationalPositions?)
    (decodeJoint_assembleJoint_core request)

/-- The decoded optional path channel is exactly the supplied channel. -/
theorem decodeJoint_assembleJoint_paths?
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint (assembleJoint request)).spatial.core.paths? =
      request.spatial.core.paths? :=
  congrArg (fun core : OrganicMolecularEvidence V => core.paths?)
    (decodeJoint_assembleJoint_core request)

/-- The decoded optional band channel is exactly the supplied channel. -/
theorem decodeJoint_assembleJoint_bands?
    (request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix) :
    (decodeJoint (assembleJoint request)).spatial.core.bands? =
      request.spatial.core.bands? :=
  congrArg (fun core : OrganicMolecularEvidence V => core.bands?)
    (decodeJoint_assembleJoint_core request)

/-! ## Injectivity and arbitrary correlated set recovery -/

/-- Joint assembly is injective. -/
theorem assembleJoint_injective :
    Function.Injective
      (fun request : JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
          State Framework BaseName Numbering Locant Prefix => assembleJoint request) := by
  intro first second equal
  have applied := congrArg decodeJoint equal
  rwa [decodeJoint_assembleJoint first, decodeJoint_assembleJoint second] at applied

/-- **Arbitrary correlated set-image recovery.**  For every set of joint requests, decoding the
assembled image recovers exactly the original set.  Since the whole record is recovered pointwise,
correlations between the core graph, conformation, optional electronic/path/band/drawing data, the
ordered role ledger, the continuous cell family and the ordered authority rows are retained. -/
theorem decodeJoint_image_assembleJoint_image
    (requests : Set (JointRequest (V := V) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix)) :
    decodeJoint '' (assembleJoint '' requests) = requests := by
  ext request
  constructor
  · rintro ⟨representation, ⟨original, member, rfl⟩, decoded⟩
    rw [← decoded, decodeJoint_assembleJoint]
    exact member
  · intro member
    exact ⟨assembleJoint request, ⟨request, member, rfl⟩, decodeJoint_assembleJoint request⟩

/-! ## The source-free P-94 context bridge

The active dependency reconstructs a P-94 certified source from a source-free
`NativeSourceContext` (optional native coordinates, optional native drawing data, and endpoint
distinctness).  Its molecule is always the *common* graph encoding; its spatial channel is the
native geometry.  Hence two native contexts over the same graph can carry different geometry while
sharing the same molecule.  No equality between the P-94 geometry and the core's rational
coordinate channel is assumed anywhere. -/

/-- The optional spatial channel of `OrganicFiniteSource` is injective at a fixed enumeration:
`none` stays `none`, and a present coordinate function is materialised in enumeration order. -/
theorem encodeSpatial?_injective (enumeration : V ≃ Fin (Fintype.card V)) :
    Function.Injective (OrganicFiniteSource.encodeSpatial? enumeration) := by
  intro first second equal
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some positions =>
          simp only [OrganicFiniteSource.encodeSpatial?_none,
            OrganicFiniteSource.encodeSpatial?_some, Option.some.injEq] at equal
          cases equal
  | some firstPositions =>
      cases second with
      | none =>
          simp only [OrganicFiniteSource.encodeSpatial?_none,
            OrganicFiniteSource.encodeSpatial?_some, Option.some.injEq] at equal
          cases equal
      | some secondPositions =>
          simp only [OrganicFiniteSource.encodeSpatial?_some,
            Option.some.injEq] at equal
          have listEqual :
              List.ofFn (fun index : Fin (Fintype.card V) =>
                  firstPositions (enumeration.symm index)) =
                List.ofFn (fun index : Fin (Fintype.card V) =>
                  secondPositions (enumeration.symm index)) := by
            simpa using congrArg SpatialConfiguration.positions equal
          have positionsEqual : firstPositions = secondPositions := by
            funext atom
            have pointwise := congrArg
              (fun list : List CartesianPoint3 => list[(enumeration atom).val]?)
              listEqual
            simpa using pointwise
          rw [positionsEqual]

/-- **Same graph, independent geometry.**  Two source-free native P-94 contexts over one common
graph and enumeration reconstruct certified sources with the *same molecule*, while their spatial
channels differ whenever the native geometry differs.  In particular the common graph carries no
obligation that the P-94 geometry equal the core's rational coordinate channel. -/
theorem p94_context_commonGraph_differentGeometry
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V))
    (first second : NativeSourceContext graph enumeration)
    (geometry : first.spatial? ≠ second.spatial?) :
    (decodeSourceContext graph enumeration first).input.molecule =
        (decodeSourceContext graph enumeration second).input.molecule ∧
      (decodeSourceContext graph enumeration first).input.spatial? ≠
        (decodeSourceContext graph enumeration second).input.spatial? := by
  refine ⟨by simp, ?_⟩
  rw [decodeSourceContext_spatial?, decodeSourceContext_spatial?]
  intro equal
  exact geometry (encodeSpatial?_injective enumeration equal)

/-- The observation-level form of the same bridge: two source-free native P-94 observations over
the same graph may carry different native geometry while reconstructing the same molecule. -/
theorem p94_observation_commonGraph_differentGeometry
    (graph : FiniteAtomInteractionHypergraph V)
    (enumeration : V ≃ Fin (Fintype.card V)) {policy : P94AuthorityPolicy}
    (first second : NativeAuthorityObservation graph enumeration policy)
    (geometry : first.context.spatial? ≠ second.context.spatial?) :
    (first.source graph enumeration).input.molecule =
        (second.source graph enumeration).input.molecule ∧
      (first.source graph enumeration).input.spatial? ≠
        (second.source graph enumeration).input.spatial? :=
  p94_context_commonGraph_differentGeometry graph enumeration
    first.context second.context geometry










theorem witnessSource_structurallyWellFormed :
    (recoveredSource witnessCore witnessEnumeration).StructurallyWellFormed := by
  refine ⟨?_, ?_, ?_⟩
  · simpa [recoveredSource, recoveredAcyclicSource, coreFiniteSource, witnessCore,
      OrganicFiniteSource.encode] using
      witnessCore.graph.encode_structurallyWellFormed witnessEnumeration
  · simp [recoveredSource, recoveredAcyclicSource, coreFiniteSource, witnessCore,
      OrganicFiniteSource.encode, AuthoritativeChemicalInput.SpatialIndicesWellFormed]
  · simp [recoveredSource, recoveredAcyclicSource, coreFiniteSource, witnessCore,
      OrganicFiniteSource.encode, AuthoritativeChemicalInput.DiagramIndicesWellFormed]

/-- The straight joint witness request over the caller's actual policy record and actual ordered
raw-entry list. -/
noncomputable def witnessJointStraight (policies : AllAuthorityPolicies)
    (entries : List (RawEntry (V := Fin 3) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policies witnessCore witnessEnumeration)) :
    JointRequest (V := Fin 3) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix where
  policies := policies
  spatial := witnessRequestStraight
  enumeration := witnessEnumeration
  source_well_formed := witnessSource_structurallyWellFormed
  entries := entries

/-- The curved joint witness request over the same actual policy record and actual ordered
raw-entry list. -/
noncomputable def witnessJointCurved (policies : AllAuthorityPolicies)
    (entries : List (RawEntry (V := Fin 3) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policies witnessCore witnessEnumeration)) :
    JointRequest (V := Fin 3) LigandId LigandKind FragmentId FragmentKind State Framework
      BaseName Numbering Locant Prefix where
  policies := policies
  spatial := witnessRequestCurved
  enumeration := witnessEnumeration
  source_well_formed := witnessSource_structurallyWellFormed
  entries := entries

/-- The two joint witnesses have exactly the same canonical output even when the caller supplies
different ordered raw-entry lists, because the canonical output depends only on the shared core and
enumeration. -/
theorem assembleJoint_witness_canonical_same (policies : AllAuthorityPolicies)
    (straightEntries curvedEntries : List (RawEntry (V := Fin 3) LigandId LigandKind FragmentId
      FragmentKind State Framework BaseName Numbering Locant Prefix policies witnessCore
      witnessEnumeration)) :
    (assembleJoint (witnessJointStraight policies straightEntries)).canonical =
      (assembleJoint (witnessJointCurved policies curvedEntries)).canonical := rfl

/-- The straight joint cell family is exactly the approved encoded straight cell. -/
theorem assembleJoint_witness_cells_straight (policies : AllAuthorityPolicies)
    (entries : List (RawEntry (V := Fin 3) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policies witnessCore witnessEnumeration)) :
    (assembleJoint (witnessJointStraight policies entries)).cells =
      [witnessEncodedCellStraight] := by
  have step : (assembleJoint (witnessJointStraight policies entries)).cells =
      witnessRepresentationStraight.cells := rfl
  rw [step]
  exact witnessRepresentationStraight_cells

/-- The curved joint cell family is exactly the approved encoded curved cell. -/
theorem assembleJoint_witness_cells_curved (policies : AllAuthorityPolicies)
    (entries : List (RawEntry (V := Fin 3) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policies witnessCore witnessEnumeration)) :
    (assembleJoint (witnessJointCurved policies entries)).cells =
      [witnessEncodedCellCurved] := by
  have step : (assembleJoint (witnessJointCurved policies entries)).cells =
      witnessRepresentationCurved.cells := rfl
  rw [step]
  exact witnessRepresentationCurved_cells

/-- The joint native row list is the same for the straight and the curved witness, because both
transport the caller's actual raw rows along the same canonical core inverse. -/
theorem assembleJoint_witness_entries_same (policies : AllAuthorityPolicies)
    (entries : List (RawEntry (V := Fin 3) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policies witnessCore witnessEnumeration)) :
    (assembleJoint (witnessJointStraight policies entries)).entries =
      (assembleJoint (witnessJointCurved policies entries)).entries := rfl

/-- **Integration does not erase the distinction.**  The two joint outputs have the same canonical
output but different encoded cell families. -/
theorem assembleJoint_witness_cells_differ (policies : AllAuthorityPolicies)
    (entries : List (RawEntry (V := Fin 3) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policies witnessCore witnessEnumeration)) :
    (assembleJoint (witnessJointStraight policies entries)).cells ≠
      (assembleJoint (witnessJointCurved policies entries)).cells := by
  have straight : (assembleJoint (witnessJointStraight policies entries)).cells =
      witnessRepresentationStraight.cells := rfl
  have curved : (assembleJoint (witnessJointCurved policies entries)).cells =
      witnessRepresentationCurved.cells := rfl
  exact fun equal => witnessRepresentation_encoded_cells_differ
    (straight.symm.trans (equal.trans curved))

/-- The two joint outputs agree on the whole boundary of the two-simplex: the actual encoded cells
recovered from the joint cell families have the same value at every boundary point. -/
theorem assembleJoint_witness_boundary_agreement (policies : AllAuthorityPolicies)
    (entries : List (RawEntry (V := Fin 3) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policies witnessCore witnessEnumeration))
    (w : Delta 2) (boundary : Delta.Boundary w) :
    (assembleJoint (witnessJointStraight policies entries)).cells =
        [witnessEncodedCellStraight] ∧
      (assembleJoint (witnessJointCurved policies entries)).cells =
        [witnessEncodedCellCurved] ∧
      witnessEncodedCellStraight.map w = witnessEncodedCellCurved.map w :=
  ⟨assembleJoint_witness_cells_straight policies entries,
    assembleJoint_witness_cells_curved policies entries,
    witnessEncodedCells_boundary_agreement w boundary⟩

/-- The lifted joint interiors keep the approved values: the straight joint interior has third
coordinate zero, and the curved joint interior has third coordinate `1/27`. -/
theorem assembleJoint_witness_interior_third (policies : AllAuthorityPolicies)
    (entries : List (RawEntry (V := Fin 3) LigandId LigandKind FragmentId FragmentKind
      State Framework BaseName Numbering Locant Prefix policies witnessCore witnessEnumeration)) :
    ((assembleJoint (witnessJointStraight policies entries)).cells.map
        encodedInteriorValue).map (fun point => point 2) = [0] ∧
      ((assembleJoint (witnessJointCurved policies entries)).cells.map
        encodedInteriorValue).map (fun point => point 2) = [1 / 27] := by
  have straight : (assembleJoint (witnessJointStraight policies entries)).cells =
      witnessRepresentationStraight.cells := rfl
  have curved : (assembleJoint (witnessJointCurved policies entries)).cells =
      witnessRepresentationCurved.cells := rfl
  constructor
  · rw [straight]
    exact witnessRepresentationStraight_interior_third
  · rw [curved]
    exact witnessRepresentationCurved_interior_third

end OrganicStereoJointAuthorityCellAssembly
end TetraStereo.OneCenter

/-! ## Kernel checks of the decisive endpoints -/

#print axioms TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.decodeJoint_assembleJoint
#print axioms TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.decodeJoint_assembleJoint_entry_heq
#print axioms TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.decodeJoint_assembleJoint_cells
#print axioms TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.decodeJoint_image_assembleJoint_image
#print axioms TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.assembleJoint_injective
#print axioms TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.p94_context_commonGraph_differentGeometry
#print axioms TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.assembleJoint_witness_cells_differ
#print axioms TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.assembleJoint_witness_boundary_agreement
#print axioms TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.assembleJoint_witness_interior_third

/-! ## Kernel-authority guards for the decisive endpoints

Any compiler-trust, `sorryAx`, or project axiom in these closures is rejected at build time. -/

assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.decodeJoint_assembleJoint
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.decodeJoint_assembleJoint_entry_heq
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.decodeJoint_assembleJoint_cells
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.decodeJoint_image_assembleJoint_image
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.assembleJoint_injective
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.p94_context_commonGraph_differentGeometry
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.assembleJoint_witness_cells_differ
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.assembleJoint_witness_boundary_agreement
assert_kernel_only TetraStereo.OneCenter.OrganicStereoJointAuthorityCellAssembly.assembleJoint_witness_interior_third
