import TetraStereo.OneCenter.OrganicStereoMolecularCanonicalTransport

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

namespace TetraStereo.OneCenter

namespace OrganicStereoCanonicalTransportCompletion

open scoped unitInterval
open OrganicStereoMolecularCanonicalTransport
open OrganicStereoMolecularEvidenceAssembly

noncomputable section

variable {V : Type} [DecidableEq V] [Fintype V]

/-!
# Completion of the canonical finite transport

`OrganicStereoMolecularCanonicalTransport` constructs the canonical finite record
`CanonicalOrganicMolecularRepresentation V` from an assembled `OrganicMolecularRepresentation V`
and proves the source-side inverse `canonicalDecode (canonicalize representation ...) =
representation`.  This module completes the missing direction: the *index-normalization
two-sided triangle*

`canonicalize (canonicalDecode canonical) canonical.atomEquiv canonical.edgeEquiv
  canonical.bandEquiv = canonical`,

for an arbitrary canonical record.  The retained source shapes and the retained equivalence
witnesses are used literally: the theorem is **not** a statement about graph isomorphism, and no
canonical record is silently normalized to a different edge/band equivalence.

The triangle rests on the actual codec inverse `encodeDescription_decodeDescription` (the
opposite direction of the codec round trip already used upstream), on destructing the record and
on proof irrelevance for the proposition-valued validity field.

From the two triangle sides we derive:

* an extensionality principle for the canonical record;
* the exact predicate `HasCanonicalIndexData` describing canonical records whose retained index
  data are literally the canonical `Fin` witnesses, together with
  `mem_range_canonicalizeFin_iff_hasCanonicalIndexData` identifying it with the range of
  `canonicalizeFin`;
* a genuine `Equiv` between `OrganicMolecularRepresentation V` and that subtype;
* exact set-image inverses in both directions, for arbitrary correlated sets of requests /
  representations, and on arbitrary sets of canonical records *where valid* (i.e. contained in the
  actual canonical image).  We do not assume the unavailable `assemble (decode r) = r` triangle;
  the reverse direction is restricted exactly to the range where the composite is the identity.

Finally, the module transports `PathGeometryValid` along the existing common relabelling
`relabelWholeState` / `relabelPathAnnotation` (and along the `Fin` reindexings of
`encodeDescription`) with no additional geometric assumptions: arcs are retained literally,
conformations are read through the inverse atom equivalence, and all five geometric fields are
transported directly from the source witness.

Scope: this is an algebra/transport layer only.  It does not assert chemical completeness,
graph-isomorphism canonicalization, or any new geometric existence statement; the only geometric
input is the source `PathGeometryValid` witness.
-/

/-! ## Extensionality of the canonical record

The canonical record has a `Type`-valued retained edge shape, a `Type`-valued retained band shape,
their (subsingleton) `Fintype` instances, the equivalence witnesses into the canonical `Fin`
index types, the canonical state and the proof-only path-validity field.  The lemma below records
that records with the same presence tags, atom enumeration, retained shapes, heterogeneously equal
index equivalences and heterogeneously equal states are equal.  The remaining fields are
`Fintype` structures (subsingletons) and proposition-valued validity (proof irrelevance). -/

/-- Extensionality for `CanonicalOrganicMolecularRepresentation` across its dependent
`Type`-valued index-shape fields. -/
theorem canonicalOrganicMolecularRepresentation_extEq
    {first second : CanonicalOrganicMolecularRepresentation V}
    (pathPresent : first.pathPresent = second.pathPresent)
    (bandPresent : first.bandPresent = second.bandPresent)
    (atomEquiv : first.atomEquiv = second.atomEquiv)
    (edgeShape : first.edgeShape = second.edgeShape)
    (edgeEquiv : HEq first.edgeEquiv second.edgeEquiv)
    (bandShape : first.bandShape = second.bandShape)
    (bandEquiv : HEq first.bandEquiv second.bandEquiv)
    (state : HEq first.state second.state) : first = second := by
  obtain ⟨firstPath, firstBand, firstAtom, firstEdgeShape, firstEdgeFintype,
    firstEdgeEquiv, firstBandShape, firstBandFintype, firstBandEquiv,
    firstState, firstValid⟩ := first
  obtain ⟨secondPath, secondBand, secondAtom, secondEdgeShape, secondEdgeFintype,
    secondEdgeEquiv, secondBandShape, secondBandFintype, secondBandEquiv,
    secondState, secondValid⟩ := second
  dsimp only at pathPresent bandPresent atomEquiv edgeShape edgeEquiv bandShape bandEquiv state
  cases pathPresent
  cases bandPresent
  cases atomEquiv
  cases edgeShape
  cases bandShape
  have fintypeEdge : firstEdgeFintype = secondEdgeFintype := Subsingleton.elim _ _
  have fintypeBand : firstBandFintype = secondBandFintype := Subsingleton.elim _ _
  cases fintypeEdge
  cases fintypeBand
  have edgeEquivEq : firstEdgeEquiv = secondEdgeEquiv := eq_of_heq edgeEquiv
  have bandEquivEq : firstBandEquiv = secondBandEquiv := eq_of_heq bandEquiv
  have stateEq : firstState = secondState := eq_of_heq state
  cases edgeEquivEq
  cases bandEquivEq
  cases stateEq
  have validEq : firstValid = secondValid := by
    funext present
    exact Subsingleton.elim _ _
  cases validEq
  rfl

/-! ## The missing triangle

The state component of the triangle is the actual `encodeDescription_decodeDescription` inverse
applied to the canonical payload.  The upstream module already proves the opposite orientation
`decodeDescription_encodeDescription` and uses it in `canonicalize`. -/

/-- **State triangle.**  Encoding the decoded canonical state through the same retained
equivalences returns exactly the canonical state.  This is the actual
`encodeDescription_decodeDescription` inverse, not an assumed assembly triangle. -/
theorem canonicalize_canonicalDecode_state
    (canonical : CanonicalOrganicMolecularRepresentation V) :
    (canonicalize (canonicalDecode canonical) canonical.atomEquiv canonical.edgeEquiv
      canonical.bandEquiv).state = canonical.state := by
  simp only [canonicalize, canonicalDecode, encodeDescription_decodeDescription]

/-- **Index-normalization two-sided triangle.**  Re-encoding an arbitrary canonical record with
exactly its own retained atom enumeration, edge equivalence and band equivalence returns that same
record.  No equivalence or shape is normalized away and no graph-isomorphism quotient is
asserted. -/
theorem canonicalize_canonicalDecode
    (canonical : CanonicalOrganicMolecularRepresentation V) :
    canonicalize (canonicalDecode canonical) canonical.atomEquiv canonical.edgeEquiv
      canonical.bandEquiv = canonical := by
  apply canonicalOrganicMolecularRepresentation_extEq
  · rfl
  · rfl
  · rfl
  · rfl
  · exact HEq.rfl
  · rfl
  · exact HEq.rfl
  · exact heq_of_eq (canonicalize_canonicalDecode_state canonical)

/-! ## Fixed retained index data and the range of `canonicalizeFin`

`canonicalizeFin` chooses the noncomputable `Fintype.equivFin` witnesses for the edge and band
shapes.  The predicate below says exactly that a canonical record carries those witnesses at a
fixed atom enumeration.  It is a proposition about the retained shapes and equivalence witnesses,
not about graph isomorphism. -/

/-- A canonical record carries the canonical `Fin` index data at a fixed atom enumeration: the
atom enumeration is the fixed one, and the retained edge/band shapes carry `Fintype.equivFin` as
their actual equivalence witnesses. -/
def HasCanonicalIndexData (atomEquiv : V ≃ Fin (Fintype.card V))
    (canonical : CanonicalOrganicMolecularRepresentation V) : Prop :=
  canonical.atomEquiv = atomEquiv ∧
    canonical.edgeEquiv = @Fintype.equivFin canonical.edgeShape canonical.fintypeEdgeShape ∧
    canonical.bandEquiv = @Fintype.equivFin canonical.bandShape canonical.fintypeBandShape

/-- `canonicalizeFin` always lands in the fixed-index subtype. -/
theorem canonicalizeFin_hasCanonicalIndexData
    (representation : OrganicMolecularRepresentation V)
    (atomEquiv : V ≃ Fin (Fintype.card V)) :
    HasCanonicalIndexData atomEquiv (canonicalizeFin representation atomEquiv) := by
  refine ⟨rfl, ?_, ?_⟩ <;> rfl

/-- **Second triangle at the canonical `Fin` witnesses.**  On a canonical record whose retained
index data are literally `Fintype.equivFin`, canonicalizing its decoder at the fixed atom
enumeration returns the record. -/
theorem canonicalizeFin_canonicalDecode_of_hasCanonicalIndexData
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (canonical : CanonicalOrganicMolecularRepresentation V)
    (fixed : HasCanonicalIndexData atomEquiv canonical) :
    canonicalizeFin (canonicalDecode canonical) atomEquiv = canonical := by
  obtain ⟨hAtom, hEdge, hBand⟩ := fixed
  unfold canonicalizeFin
  rw [show @Fintype.equivFin (canonicalDecode canonical).edgeIndex
        (canonicalDecode canonical).fintypeEdgeIndex = canonical.edgeEquiv from hEdge.symm,
      show @Fintype.equivFin (canonicalDecode canonical).bandIndex
        (canonicalDecode canonical).fintypeBandIndex = canonical.bandEquiv from hBand.symm,
      ← hAtom]
  exact canonicalize_canonicalDecode canonical

/-- Canonical records with the fixed canonical index data are exactly the range of
`canonicalizeFin` at the fixed atom enumeration. -/
theorem mem_range_canonicalizeFin_iff_hasCanonicalIndexData
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (canonical : CanonicalOrganicMolecularRepresentation V) :
    canonical ∈ Set.range (fun representation => canonicalizeFin representation atomEquiv) ↔
      HasCanonicalIndexData atomEquiv canonical := by
  constructor
  · rintro ⟨representation, rfl⟩
    exact canonicalizeFin_hasCanonicalIndexData representation atomEquiv
  · intro fixed
    exact ⟨canonicalDecode canonical,
      canonicalizeFin_canonicalDecode_of_hasCanonicalIndexData atomEquiv canonical fixed⟩

/-! ## The equivalence and its bijectivity -/

/-- The subtype of canonical records carrying the fixed canonical index data. -/
abbrev FixedCanonicalRepresentations (atomEquiv : V ≃ Fin (Fintype.card V)) :=
  {canonical : CanonicalOrganicMolecularRepresentation V //
    HasCanonicalIndexData atomEquiv canonical}

/-- **Actual equivalence.**  For a fixed atom enumeration, canonicalization and decoding are
mutually inverse between assembled representations and canonical records with the fixed retained
index data.  The two inverse laws are the source-side inverse
`canonicalDecode_canonicalizeFin` and the index-normalization triangle above. -/
noncomputable def canonicalizeFinEquiv (atomEquiv : V ≃ Fin (Fintype.card V)) :
    OrganicMolecularRepresentation V ≃ FixedCanonicalRepresentations atomEquiv where
  toFun representation :=
    ⟨canonicalizeFin representation atomEquiv,
      canonicalizeFin_hasCanonicalIndexData representation atomEquiv⟩
  invFun canonical := canonicalDecode canonical.1
  left_inv representation := canonicalDecode_canonicalizeFin representation atomEquiv
  right_inv canonical := by
    apply Subtype.ext
    exact canonicalizeFin_canonicalDecode_of_hasCanonicalIndexData atomEquiv canonical.1
      canonical.2

/-- The equivalence sends a representation to its canonical `Fin` record. -/
@[simp] theorem canonicalizeFinEquiv_apply
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (representation : OrganicMolecularRepresentation V) :
    (canonicalizeFinEquiv atomEquiv representation).1 =
      canonicalizeFin representation atomEquiv := rfl

/-- The inverse of the equivalence is the representation decoder. -/
@[simp] theorem canonicalizeFinEquiv_symm_apply
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (canonical : FixedCanonicalRepresentations atomEquiv) :
    (canonicalizeFinEquiv atomEquiv).symm canonical = canonicalDecode canonical.1 := rfl

/-- **Bijectivity.**  At a fixed atom enumeration, canonicalization is a bijection from assembled
representations onto canonical records carrying exactly the fixed retained index data. -/
theorem canonicalizeFin_bijective_fixed
    (atomEquiv : V ≃ Fin (Fintype.card V)) :
    Function.Bijective (fun representation =>
      (⟨canonicalizeFin representation atomEquiv,
        canonicalizeFin_hasCanonicalIndexData representation atomEquiv⟩ :
        FixedCanonicalRepresentations atomEquiv)) :=
  (canonicalizeFinEquiv atomEquiv).bijective

/-! ## Exact correlated set images in both directions

Sets are always sets of whole records, so every cross-channel correlation is carried at once.
The forward direction is exact for arbitrary sets.  The reverse direction is exact precisely on
the canonical image; this is the honest "where valid" restriction, since the opposite assembly
triangle `assemble (decode r) = r` is not available for arbitrary representations and is not
assumed anywhere. -/

/-- **Forward set image at the representation level.**  Decoding the canonical image of an
arbitrary set of representations returns exactly that set. -/
theorem canonicalDecode_image_canonicalizeFin_image
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (representations : Set (OrganicMolecularRepresentation V)) :
    canonicalDecode ''
        ((fun representation => canonicalizeFin representation atomEquiv) '' representations) =
      representations := by
  rw [Set.image_image]
  have pointwise :
      (fun representation => canonicalDecode (canonicalizeFin representation atomEquiv)) = id := by
    funext representation
    exact canonicalDecode_canonicalizeFin representation atomEquiv
  rw [pointwise, Set.image_id]

/-- **Reverse set image at the representation level.**  On any set of canonical records contained
in the actual canonical image, canonicalizing and then decoding returns exactly the original set.
-/
theorem canonicalizeFin_image_canonicalDecode_image_of_subset_range
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (canonicals : Set (CanonicalOrganicMolecularRepresentation V))
    (subset : canonicals ⊆
      Set.range (fun representation => canonicalizeFin representation atomEquiv)) :
    (fun representation => canonicalizeFin representation atomEquiv) ''
        (canonicalDecode '' canonicals) = canonicals := by
  rw [Set.image_image]
  have pointwise : ∀ canonical ∈ canonicals,
      canonicalizeFin (canonicalDecode canonical) atomEquiv = canonical := by
    intro canonical member
    obtain ⟨representation, rfl⟩ := subset member
    exact canonicalizeFin_canonicalDecode_of_hasCanonicalIndexData atomEquiv _
      (canonicalizeFin_hasCanonicalIndexData representation atomEquiv)
  apply Set.Subset.antisymm
  · rintro canonical ⟨source, member, rfl⟩
    show canonicalizeFin (canonicalDecode source) atomEquiv ∈ canonicals
    rw [pointwise source member]
    exact member
  · intro canonical member
    exact ⟨canonical, member, pointwise canonical member⟩

/-- The same reverse set image stated through the explicit retained index witnesses
`HasCanonicalIndexData`, rather than through range membership. -/
theorem canonicalizeFin_image_canonicalDecode_image_of_hasCanonicalIndexData
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (canonicals : Set (CanonicalOrganicMolecularRepresentation V))
    (subset : ∀ canonical ∈ canonicals, HasCanonicalIndexData atomEquiv canonical) :
    (fun representation => canonicalizeFin representation atomEquiv) ''
        (canonicalDecode '' canonicals) = canonicals := by
  apply canonicalizeFin_image_canonicalDecode_image_of_subset_range
  intro canonical member
  exact (mem_range_canonicalizeFin_iff_hasCanonicalIndexData atomEquiv canonical).mpr
    (subset canonical member)

/-- **Forward set image for arbitrary correlated requests.**  For an arbitrary set of independently
supplied requests, the composite canonical assembly / canonical decode / source decode returns
exactly the original set.  This is the upstream exact set recovery of the whole correlated
request. -/
theorem decode_image_canonicalDecode_image_canonicalAssemble_image_completion
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (requests : Set (OrganicMolecularEvidence V)) :
    decode '' (canonicalDecode ''
        ((fun request => canonicalAssemble atomEquiv request) '' requests)) = requests :=
  decode_image_canonicalDecode_image_canonicalAssemble_image atomEquiv requests

/-- **Reverse set image for arbitrary correlated requests, on the canonical image.**  For any set
of canonical records contained in the actual range of `canonicalAssemble`, the source decode,
canonical decode and canonical assembly return exactly the original set.  The hypothesis is the
precise "where valid" condition; no assembly/decoding triangle beyond the proved request recovery
is used. -/
theorem canonicalAssemble_image_canonicalDecode_image_decode_image_of_subset_range
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (canonicals : Set (CanonicalOrganicMolecularRepresentation V))
    (subset : canonicals ⊆
      Set.range (fun request => canonicalAssemble atomEquiv request)) :
    (fun request => canonicalAssemble atomEquiv request) ''
        (decode '' (canonicalDecode '' canonicals)) = canonicals := by
  rw [Set.image_image, Set.image_image]
  have pointwise : ∀ canonical ∈ canonicals,
      canonicalAssemble atomEquiv (decode (canonicalDecode canonical)) = canonical := by
    intro canonical member
    obtain ⟨request, rfl⟩ := subset member
    simpa only [canonicalAssemble, canonicalDecode_canonicalizeFin, decode_assemble]
  apply Set.Subset.antisymm
  · rintro canonical ⟨source, member, rfl⟩
    show canonicalAssemble atomEquiv (decode (canonicalDecode source)) ∈ canonicals
    rw [pointwise source member]
    exact member
  · intro canonical member
    exact ⟨canonical, member, pointwise canonical member⟩

/-- **Both directions on an arbitrary set of requests.**  The composite
`canonicalAssemble ∘ decode ∘ canonicalDecode` is the identity on the canonical image of every
arbitrary request set, so the forward and reverse recoveries compose exactly. -/
theorem canonicalAssemble_image_canonicalDecode_image_decode_image_image
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (requests : Set (OrganicMolecularEvidence V)) :
    (fun request => canonicalAssemble atomEquiv request) ''
        (decode '' (canonicalDecode ''
          ((fun request => canonicalAssemble atomEquiv request) '' requests))) =
      (fun request => canonicalAssemble atomEquiv request) '' requests := by
  apply canonicalAssemble_image_canonicalDecode_image_decode_image_of_subset_range
  rintro canonical ⟨request, _member, rfl⟩
  exact ⟨request, rfl⟩

/-! ## Transport of the physical path geometry along the common relabelling

`PathGeometryValid` has five geometric fields, all stated directly about the bond-path arcs and
the single shared conformation of a `WholeState`.  A common atom relabelling changes the incidence
graph, the electronic/graph tie, the endpoint labels and all other atom references, but it
preserves the geometry: it keeps every arc literally (including arbitrary curved arcs), and it
reads every conformation point through the inverse atom equivalence.  Consequently the geometry
witness transports with no additional geometric assumption. -/

section Geometry

variable {W : Type} [DecidableEq W] [Fintype W]
variable {E B : Type} [Fintype E] [Fintype B]
variable {E' B' : Type} [Fintype E'] [Fintype B']

/-- The endpoint lookup commutes with a common atom relabelling: it is the mapped lookup. -/
theorem sourceEndpointAt?_relabel (atomEquiv : V ≃ W) {E₀ : Type}
    (source target : E₀ → V) (index : E₀) (t : I) :
    sourceEndpointAt? (fun position => atomEquiv (source position))
        (fun position => atomEquiv (target position)) index t =
      (sourceEndpointAt? source target index t).map atomEquiv := by
  by_cases zero : t = 0
  · simp [sourceEndpointAt?, zero]
  · by_cases one : t = 1
    · simp [sourceEndpointAt?, zero, one]
    · simp [sourceEndpointAt?, zero, one]

/-- **Path-geometry transport under a common atom relabelling.**  Every field is transported
literally from the source witness; arcs are unchanged and conformation points are read through the
inverse atom equivalence `atomEquiv.symm`. -/
theorem pathGeometryValid_relabelWholeState
    (atomEquiv : V ≃ W) (state : WholeState V E B)
    (valid : PathGeometryValid state) :
    PathGeometryValid (relabelWholeState atomEquiv state) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro edge other equal
    exact valid.occurrence_injective
      (by simpa only [relabelWholeState, relabelPathAnnotation] using equal)
  · intro atom other equal
    have preimage : atomEquiv.symm atom = atomEquiv.symm other :=
      valid.atom_injective
        (by simpa only [relabelWholeState, MolecularConformation.reindex] using equal)
    exact atomEquiv.symm.injective preimage
  · intro edge
    exact valid.arc_injective edge
  · intro edge t zero one atom
    exact valid.interior_avoids_atoms edge t zero one (atomEquiv.symm atom)
  · intro edge other t s different meet
    obtain ⟨atom, hfirst, hsecond⟩ :=
      valid.intersects_only_at_common_endpoints edge other t s different
        (by simpa only [relabelWholeState, relabelPathAnnotation] using meet)
    have hsource :
        (fun index => ((relabelWholeState atomEquiv state).paths index).source) =
          fun index => atomEquiv ((state.paths index).source) := rfl
    have htarget :
        (fun index => ((relabelWholeState atomEquiv state).paths index).target) =
          fun index => atomEquiv ((state.paths index).target) := rfl
    refine ⟨atomEquiv atom, ?_, ?_⟩
    · rw [hsource, htarget, sourceEndpointAt?_relabel, hfirst]
      rfl
    · rw [hsource, htarget, sourceEndpointAt?_relabel, hsecond]
      rfl

/-- Path geometry is unchanged by reindexing the finite edge family. -/
theorem pathGeometryValid_reindexEdges
    (equivalence : E ≃ E') (state : WholeState V E B)
    (valid : PathGeometryValid state) :
    PathGeometryValid (reindexEdges equivalence state) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro edge other equal
    exact equivalence.symm.injective (valid.occurrence_injective
      (by simpa only [reindexEdges] using equal))
  · exact valid.atom_injective
  · intro edge
    exact valid.arc_injective (equivalence.symm edge)
  · intro edge t zero one atom
    exact valid.interior_avoids_atoms (equivalence.symm edge) t zero one atom
  · intro edge other t s different meet
    obtain ⟨atom, hfirst, hsecond⟩ :=
      valid.intersects_only_at_common_endpoints (equivalence.symm edge) (equivalence.symm other)
        t s (fun same => different (by simpa using congrArg equivalence same))
        (by simpa only [reindexEdges] using meet)
    exact ⟨atom, by simpa only [reindexEdges] using hfirst,
      by simpa only [reindexEdges] using hsecond⟩

/-- Path geometry is unchanged by reindexing the finite band family: every geometric field
mentions only the bond paths and the single shared conformation. -/
theorem pathGeometryValid_reindexBands
    (equivalence : B ≃ B') (state : WholeState V E B)
    (valid : PathGeometryValid state) :
    PathGeometryValid (reindexBands equivalence state) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro edge other equal
    exact valid.occurrence_injective (by simpa only [reindexBands] using equal)
  · exact valid.atom_injective
  · intro edge
    exact valid.arc_injective edge
  · intro edge t zero one atom
    exact valid.interior_avoids_atoms edge t zero one atom
  · intro edge other t s different meet
    obtain ⟨atom, hfirst, hsecond⟩ :=
      valid.intersects_only_at_common_endpoints edge other t s different
        (by simpa only [reindexBands] using meet)
    exact ⟨atom, by simpa only [reindexBands] using hfirst,
      by simpa only [reindexBands] using hsecond⟩

/-- **Path-geometry transport through the actual encoder.**  The canonical `Fin`-encoded state of
a valid source description is again geometrically valid.  This is composition of the common atom
relabelling with the two index reindexings; no source validity is assumed beyond the explicit
`PathGeometryValid` argument. -/
theorem pathGeometryValid_encodeDescription
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E))
    (bandEquiv : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (valid : PathGeometryValid state) :
    PathGeometryValid (encodeDescription atomEquiv edgeEquiv bandEquiv state) := by
  unfold encodeDescription
  exact pathGeometryValid_reindexBands bandEquiv _
    (pathGeometryValid_reindexEdges edgeEquiv _
      (pathGeometryValid_relabelWholeState atomEquiv state valid))

/-! ### The encoded geometry, exposed

These projections make explicit that the encoder retains every arc literally and moves only the
atom labels.  They are the concrete content of the geometric transport above and are used to read
the canonical state's geometry without any hidden reparameterization. -/

/-- The encoded conformation is the source conformation read through the inverse atom
enumeration. -/
theorem encodeDescription_conformation
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E))
    (bandEquiv : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) :
    (encodeDescription atomEquiv edgeEquiv bandEquiv state).conformation =
      MolecularConformation.reindex atomEquiv state.conformation := rfl

/-- The encoded path at a canonical `Fin` index is the source path at the inverse edge index. -/
theorem encodeDescription_paths
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E))
    (bandEquiv : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (index : Fin (Fintype.card E)) :
    (encodeDescription atomEquiv edgeEquiv bandEquiv state).paths index =
      relabelPathAnnotation atomEquiv (state.paths (edgeEquiv.symm index)) := rfl

/-- Every encoded arc is literally the source arc: arbitrary curved arcs are retained, never
reparameterized or replaced. -/
theorem encodeDescription_path_arc
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E))
    (bandEquiv : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (index : Fin (Fintype.card E)) :
    ((encodeDescription atomEquiv edgeEquiv bandEquiv state).paths index).arc =
      (state.paths (edgeEquiv.symm index)).arc := rfl

/-- Every encoded source endpoint is the relabelled source endpoint. -/
theorem encodeDescription_path_source
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E))
    (bandEquiv : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (index : Fin (Fintype.card E)) :
    ((encodeDescription atomEquiv edgeEquiv bandEquiv state).paths index).source =
      atomEquiv (state.paths (edgeEquiv.symm index)).source := rfl

/-- Every encoded target endpoint is the relabelled source target endpoint. -/
theorem encodeDescription_path_target
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E))
    (bandEquiv : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (index : Fin (Fintype.card E)) :
    ((encodeDescription atomEquiv edgeEquiv bandEquiv state).paths index).target =
      atomEquiv (state.paths (edgeEquiv.symm index)).target := rfl

/-- The interaction occurrence referenced by an encoded path is retained literally. -/
theorem encodeDescription_path_interactionIndex
    (atomEquiv : V ≃ Fin (Fintype.card V))
    (edgeEquiv : E ≃ Fin (Fintype.card E))
    (bandEquiv : B ≃ Fin (Fintype.card B))
    (state : WholeState V E B) (index : Fin (Fintype.card E)) :
    ((encodeDescription atomEquiv edgeEquiv bandEquiv state).paths index).interactionIndex =
      (state.paths (edgeEquiv.symm index)).interactionIndex := rfl

end Geometry

end

end OrganicStereoCanonicalTransportCompletion

end TetraStereo.OneCenter
