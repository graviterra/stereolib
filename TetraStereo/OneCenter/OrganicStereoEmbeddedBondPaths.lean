import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.CIPFrontier
import Mathlib.Topology.ContinuousMap.Defs
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false

namespace TetraStereo.OneCenter

open scoped unitInterval

/-!
# Source-indexed embedded bond paths

The existing authoritative chemical input (`AuthoritativeChemicalInput`, and its checked variant
`CertifiedAuthoritativeChemicalInput`) records a finite semantic molecule together with optional
rational atom coordinates.  Rational coordinates name atom positions but carry no information
about the continuous spatial extent of a bond.  This module adds exactly that missing layer:
a finite, source-indexed table of embedded bond paths in real three-space.  The conformation type
is `MolecularConformation` from `TetraStereo.OneCenter.CIPFrontier`; this is the same definition
reused by the repository's `OrganicStereoRealConfiguration` (via `SourceConformation`), so
real-source geometries there can feed the tables below without any conversion of type.

The module provides representation and transport results for *supplied, already-valid*
finite-edge tables.  The statements are conditional, not unconditional: the geometric realization
obligations (exact coverage of the documented subset, endpoint equations, atom and arc
injectivity, and non-intersection of distinct arcs) are premises carried in the table data, and
no embedding is constructed here from a bare molecule plus conformation.

* The molecule is an arbitrary `SemanticMolecule`.  Nothing is asserted about which interactions
  exist; the caller supplies an explicit finite set `documented` of interaction indices.  Every
  documented index is proved (in the data) to be a genuine pair bond: generic binary endpoint
  data (exactly two distinct in-range participants, in source orientation order) plus the
  module's fixed default pair-bond kind selection (`IsGenuinePairBondAt`).  That default covers
  covalent/unspecified-covalent, aromatic, coordinate and delocalized *binary* interactions;
  `multicenter`, `ionic`, `metallic`, `hydrogenBond` and `other` interactions are never selected,
  and every hyperedge is rejected by the binary endpoint condition.  The generic predicate
  `IsSelectedPairBondWith` accepts another kind selection, but it does not parameterize the
  realization structures: `RealizesSourceBondPaths` and the tables use the fixed default.
  Nothing is flattened into a pair bond; unselected interactions stay in the source untouched.
  `CompleteForSourcePairBonds` makes the optional "the documented subset is the whole fixed
  default selection" hypothesis explicit.
* A path table is indexed by `Fin edgeCount` (or, in the independent input form, by an arbitrary
  finite edge type `E`).  Every entry records its `sourceInteraction` index, its oriented
  endpoint atoms, the exact oriented participant equation, and a continuous arc
  `C(I, ℝ³)`.
* `RealizesSourceBondPaths` bundles the geometric realization obligations: exact source
  participant agreement, exact coverage of the documented subset (each documented interaction
  index is realized by exactly one edge), endpoint equations, atom injectivity, arc injectivity,
  and the condition that distinct arcs meet only at a common endpoint atom.  These obligations
  are supplied premises of the structure, not consequences derived from the source molecule.
* `EdgeIndexedSourceBoundInput` is the independent finite-edge-indexed input over an arbitrary
  finite edge type.  `BondPathTable.encode`/`decode` implement the constructive encoding into
  the `Fin edgeCount` source-bound record via the explicit equivalence `Fintype.equivFin E`, with
  exact recovery of every arc value, endpoint, atom position and interaction index, and a
  two-sided inverse on the full data.
* Ambient homeomorphisms of real three-space act on realizations, preserving the source, the
  documented interaction identity, the orientation and every endpoint.

Scope boundaries (explicitly *not* claimed here):

* No rational/piecewise-linear universalization of the conformation is asserted.  The arcs are
  arbitrary continuous real-valued maps.
* No finite-byte serialization of arbitrary reals or of arbitrary continuous functions is
  claimed.
* No mod-2 linking number, chirality, link classification or knot/link invariant is defined.
* No assertion is made that the supplied embedded graph models excluded-volume effects,
  rotaxane kinetics, or band framing.
* Catenanes, knots and other mechanical graphs are represented only as *supplied* embedded graph
  data.  The module never turns a desired label into a coverage assumption, and makes no
  acyclicity, planarity or classification claim about the graph.
* This is a representation/transport layer.  It does not claim full organic coverage from a
  single component; chemical applicability remains a separate predicate over the source.
-/

noncomputable section

/-- Ambient real three-space used for embedded molecular configurations. -/
abbrev EmbeddedReal3 : Type := EuclideanSpace ℝ (Fin 3)

/-! ### Genuine pair bonds -/

namespace SemanticInteractionKind

/-- The chosen concrete pair-bond kinds for the embedded bond-path graph: covalent (any bond
order), aromatic, coordinate, and delocalized interactions.

Being selected here is necessary but not sufficient: a selected interaction is a pair bond only
when it also has exactly two participants (`SemanticInteraction.IsSelectedPairBond`).  In
particular a `.delocalized` or `.aromatic` interaction with more than two participants is *not*
selected, and `multicenter`, `ionic`, `metallic`, `hydrogenBond` and `other` interactions are
never selected.  Hyperedges are therefore never flattened into pair bonds. -/
def isSelectedPairKind : SemanticInteractionKind → Bool
  | .unspecifiedCovalent => true
  | .covalent _ => true
  | .aromatic => true
  | .coordinate => true
  | .delocalized _ => true
  | _ => false

/-- The covalent/unspecified-covalent sub-selection of pair-bond kinds. -/
def isCovalentPairKind : SemanticInteractionKind → Bool
  | .unspecifiedCovalent => true
  | .covalent _ => true
  | _ => false

/-- The aromatic sub-selection of pair-bond kinds.  Only binary aromatic interactions become
pair bonds; a multi-participant aromatic interaction is rejected by the binary endpoint
condition. -/
def isAromaticPairKind : SemanticInteractionKind → Bool
  | .aromatic => true
  | _ => false

/-- The coordinate sub-selection of pair-bond kinds. -/
def isCoordinatePairKind : SemanticInteractionKind → Bool
  | .coordinate => true
  | _ => false

/-- The delocalized sub-selection of pair-bond kinds.  Only binary delocalized interactions
become pair bonds; a genuinely multicenter delocalized interaction is rejected by the binary
endpoint condition. -/
def isDelocalizedPairKind : SemanticInteractionKind → Bool
  | .delocalized _ => true
  | _ => false

end SemanticInteractionKind

namespace SemanticInteraction

/-- Generic binary interaction endpoint data, independent of interaction kind: exactly two
distinct in-range participants, recorded in the source orientation order.

Every bond path uses this endpoint shape.  It says nothing on its own about whether the
interaction is a selected pair bond. -/
def HasBinaryEndpoints (interaction : SemanticInteraction) (atomCount : ℕ) : Prop :=
  ∃ source target : ℕ,
    source < atomCount ∧ target < atomCount ∧ source ≠ target ∧
      interaction.participants = [source, target]

/-- A generic pair-bond specification over an explicitly supplied kind selection: the kind
selection promoted to a binary selection.  The binary endpoint condition rules out every
hyperedge, so no multicenter flattening can occur even for a permissive kind predicate.

This predicate is generic over the kind selection, but it does *not* parameterize the structures
below: `RealizesSourceBondPaths`, `BondPathTable`, `CompleteBondPathTable` and
`CompleteForSourcePairBonds` are all stated against the fixed default selection
`IsGenuinePairBondAt`.  Passing a different predicate to `IsSelectedPairBondWith` alone therefore
does not let a caller customize the actual tables; parameterizing the tables over a selection
would be a separate change and is not done in this module. -/
def IsSelectedPairBondWith (kindSelected : SemanticInteractionKind → Bool)
    (interaction : SemanticInteraction) (atomCount : ℕ) : Prop :=
  kindSelected interaction.kind = true ∧ interaction.HasBinaryEndpoints atomCount

/-- The default selected pair-bond specification: all chosen concrete pair kinds (covalent,
aromatic, coordinate, delocalized), restricted to binary interactions. -/
def IsSelectedPairBond (interaction : SemanticInteraction) (atomCount : ℕ) : Prop :=
  interaction.IsSelectedPairBondWith SemanticInteractionKind.isSelectedPairKind atomCount

/-- A genuine pair bond is exactly a selected binary source pair bond. -/
def IsGenuinePairBond (interaction : SemanticInteraction) (atomCount : ℕ) : Prop :=
  interaction.IsSelectedPairBond atomCount

end SemanticInteraction

/-- Molecule-level genuine pair-bond predicate at an interaction index. -/
def IsGenuinePairBondAt (molecule : SemanticMolecule)
    (index : Fin molecule.interactions.length) : Prop :=
  (molecule.interactions.get index).IsGenuinePairBond molecule.atomCount

/-- Completeness for the module's fixed default source pair-bond specification: every source
interaction that is a selected binary pair bond according to `IsGenuinePairBondAt` is in the
documented subset.

This is an explicit *optional* hypothesis.  Realization by itself only requires exact coverage of
whatever subset is documented; completeness says the documented subset is the whole selected
pair-bond specification.  It is not implied by any earlier structure and it makes no claim of
chemical coverage beyond the fixed default selection. -/
def CompleteForSourcePairBonds (molecule : SemanticMolecule)
    (documented : Finset (Fin molecule.interactions.length)) : Prop :=
  ∀ index, IsGenuinePairBondAt molecule index → index ∈ documented

/-! ### One source-indexed bond path -/

/-- One source-indexed embedded bond path.

`sourceInteraction` records exactly which interaction of the source molecule this path
represents (duplicate source entries are distinct interaction indices and stay distinct).
`participants_exact` records the exact oriented endpoint agreement with the source: the
participant list of that interaction is literally `[source, target]`, so neither orientation nor
interaction identity is lost.  The arc is an arbitrary continuous map on the unit interval;
the endpoint equations relating it to the conformation are imposed by
`RealizesSourceBondPaths`. -/
structure SourceBondPath (molecule : SemanticMolecule) where
  /-- Index of the represented source interaction. -/
  sourceInteraction : Fin molecule.interactions.length
  /-- Oriented first endpoint atom. -/
  source : Fin molecule.atomCount
  /-- Oriented second endpoint atom. -/
  target : Fin molecule.atomCount
  /-- The two endpoint atoms are distinct. -/
  source_ne_target : source ≠ target
  /-- Exact oriented participant agreement with the source interaction. -/
  participants_exact :
    (molecule.interactions.get sourceInteraction).participants = [source.val, target.val]
  /-- Continuous arc in ambient real three-space. -/
  arc : C(I, EmbeddedReal3)

namespace SourceBondPath

variable {molecule : SemanticMolecule}

/-- The atom endpoint of an arc parameter, when that parameter is an endpoint of the arc. -/
def endpointAt? (path : SourceBondPath molecule) (t : I) : Option (Fin molecule.atomCount) :=
  if t = 0 then some path.source else if t = 1 then some path.target else none

@[simp] theorem endpointAt?_zero (path : SourceBondPath molecule) :
    path.endpointAt? 0 = some path.source := by
  simp [endpointAt?]

@[simp] theorem endpointAt?_one (path : SourceBondPath molecule) :
    path.endpointAt? 1 = some path.target := by
  simp [endpointAt?]

/-- Image of a bond path under an ambient homeomorphism of real three-space.

The source interaction index, the oriented endpoints and the participant equation are unchanged;
only the arc is composed with the homeomorphism. -/
def mapHomeomorph (h : EmbeddedReal3 ≃ₜ EmbeddedReal3) (path : SourceBondPath molecule) :
    SourceBondPath molecule where
  sourceInteraction := path.sourceInteraction
  source := path.source
  target := path.target
  source_ne_target := path.source_ne_target
  participants_exact := path.participants_exact
  arc := (⟨h, h.continuous⟩ : C(EmbeddedReal3, EmbeddedReal3)).comp path.arc

@[simp] theorem mapHomeomorph_sourceInteraction (h : EmbeddedReal3 ≃ₜ EmbeddedReal3)
    (path : SourceBondPath molecule) :
    (path.mapHomeomorph h).sourceInteraction = path.sourceInteraction :=
  rfl

@[simp] theorem mapHomeomorph_source (h : EmbeddedReal3 ≃ₜ EmbeddedReal3)
    (path : SourceBondPath molecule) :
    (path.mapHomeomorph h).source = path.source :=
  rfl

@[simp] theorem mapHomeomorph_target (h : EmbeddedReal3 ≃ₜ EmbeddedReal3)
    (path : SourceBondPath molecule) :
    (path.mapHomeomorph h).target = path.target :=
  rfl

@[simp] theorem mapHomeomorph_arc (h : EmbeddedReal3 ≃ₜ EmbeddedReal3)
    (path : SourceBondPath molecule) (t : I) :
    (path.mapHomeomorph h).arc t = h (path.arc t) :=
  rfl

end SourceBondPath

/-! ### Realization obligations -/

/-- The obligations that turn a finite source-indexed edge table into an embedded bond-path
realization of an explicitly documented subset of genuine source pair bonds.

* `documented_genuine`: every documented interaction index is a genuine pair bond.
* `edge_documented` / `exact_coverage`: the documented subset is covered exactly once (duplicate
  source interaction entries have distinct indices and are each realized separately).
* `source_endpoint` / `target_endpoint`: the arc endpoints are the atom positions.
* `atom_injective`: distinct atoms occupy distinct points.
* `arc_injective`: each arc is injective on the unit interval.
* `interior_avoids_atoms`: an arc's interior never passes through an atom position.
* `intersects_only_at_common_endpoints`: two distinct arcs can meet only at a common endpoint
  atom.

`documented_genuine` uses the module's fixed default selection `IsGenuinePairBondAt`; the kind
selection is not a parameter of this structure.  Interactions outside `documented` are not
mentioned by any edge and are retained unchanged in the source. -/
structure RealizesSourceBondPaths (E : Type*) [Fintype E]
    (molecule : SemanticMolecule)
    (conformation : MolecularConformation (Fin molecule.atomCount))
    (documented : Finset (Fin molecule.interactions.length))
    (edge : E → SourceBondPath molecule) : Prop where
  /-- Every documented index is a genuine two-centre source pair bond. -/
  documented_genuine : ∀ index, index ∈ documented → IsGenuinePairBondAt molecule index
  /-- Every edge represents a documented source interaction. -/
  edge_documented : ∀ e, (edge e).sourceInteraction ∈ documented
  /-- Exact coverage: each documented interaction index is realized by exactly one edge. -/
  exact_coverage : ∀ index, index ∈ documented → ∃! e : E, (edge e).sourceInteraction = index
  /-- Arc start points coincide with the atom positions. -/
  source_endpoint : ∀ e, (edge e).arc 0 = conformation (edge e).source
  /-- Arc end points coincide with the atom positions. -/
  target_endpoint : ∀ e, (edge e).arc 1 = conformation (edge e).target
  /-- Distinct atoms occupy distinct points. -/
  atom_injective : Function.Injective conformation
  /-- Every arc is injective on the unit interval. -/
  arc_injective : ∀ e, Function.Injective (edge e).arc
  /-- Arc interiors avoid every atom position. -/
  interior_avoids_atoms :
    ∀ e (t : I), t ≠ 0 → t ≠ 1 → ∀ a, (edge e).arc t ≠ conformation a
  /-- Distinct arcs meet only at a common endpoint atom. -/
  intersects_only_at_common_endpoints :
    ∀ e f (t s : I), e ≠ f → (edge e).arc t = (edge f).arc s →
      ∃ a : Fin molecule.atomCount,
        (edge e).endpointAt? t = some a ∧ (edge f).endpointAt? s = some a

/-! ### The finite edge table -/

/-- An explicit finite bond-edge table indexed by an arbitrary finite edge type `E`.

This is the independent input form: only the *edge* index type is abstract.  Atom indices remain
the source's `Fin molecule.atomCount` and interaction indices remain the source's
`Fin molecule.interactions.length`; that is exactly the source indexing required for exact
participant agreement.  The `Fin`-indexed form is `BondPathRealization`, and
`BondPathTable.encode`/`decode` relate the two. -/
structure BondPathTable (E : Type*) [Fintype E] (molecule : SemanticMolecule)
    (conformation : MolecularConformation (Fin molecule.atomCount)) where
  /-- The explicitly documented subset of source interaction indices. -/
  documented : Finset (Fin molecule.interactions.length)
  /-- The finite family of source-indexed embedded bond paths. -/
  edge : E → SourceBondPath molecule
  /-- The realization obligations. -/
  valid : RealizesSourceBondPaths E molecule conformation documented edge

/-- The main finite bond-edge table indexed by `Fin edgeCount`, with oriented endpoint atoms in
`Fin atomCount`, a `sourceInteraction` index in `Fin molecule.interactions.length`, and a
continuous arc `C(I, ℝ³)` per edge.  Definitionally the generic table at edge type
`Fin edgeCount`. -/
abbrev BondPathRealization (molecule : SemanticMolecule) (edgeCount : ℕ)
    (conformation : MolecularConformation (Fin molecule.atomCount)) : Type :=
  BondPathTable (Fin edgeCount) molecule conformation

namespace BondPathTable

variable {E F G : Type*} [Fintype E] [Fintype F] [Fintype G]
variable {molecule : SemanticMolecule}
variable {conformation : MolecularConformation (Fin molecule.atomCount)}

/-- Extensionality for bond-path tables: the two data fields determine the table, because the
realization field is a proposition. -/
@[ext]
theorem ext_of_documented_edge {t₁ t₂ : BondPathTable E molecule conformation}
    (hd : t₁.documented = t₂.documented) (he : t₁.edge = t₂.edge) : t₁ = t₂ := by
  cases t₁ with
  | mk d₁ e₁ v₁ =>
  cases t₂ with
  | mk d₂ e₂ v₂ =>
  simp only at hd he
  cases hd
  cases he
  rw [Subsingleton.elim v₁ v₂]

/-- Explicit equivalence from the arbitrary finite edge type to `Fin (Fintype.card E)`; this is
the equivalence used for the constructive encoding. -/
def edgeEquivFin (E : Type*) [Fintype E] : E ≃ Fin (Fintype.card E) :=
  Fintype.equivFin E

/-- Reindex a finite bond-path table along an explicit equivalence of edge types.

The documented subset, the source interaction indices, the oriented endpoints and every arc value
are transported unchanged; only the indexing changes. -/
def reindex (sigma : E ≃ F) (table : BondPathTable E molecule conformation) :
    BondPathTable F molecule conformation where
  documented := table.documented
  edge f := table.edge (sigma.symm f)
  valid :=
    { documented_genuine := table.valid.documented_genuine
      edge_documented := fun f => table.valid.edge_documented (sigma.symm f)
      exact_coverage := by
        intro index hindex
        obtain ⟨e, he, huniq⟩ := table.valid.exact_coverage index hindex
        refine ⟨sigma e, ?_, ?_⟩
        · simpa using he
        · intro f hf
          have hfe : sigma.symm f = e := huniq (sigma.symm f) (by simpa using hf)
          calc
            f = sigma (sigma.symm f) := (sigma.apply_symm_apply f).symm
            _ = sigma e := by rw [hfe]
      source_endpoint := fun f => table.valid.source_endpoint (sigma.symm f)
      target_endpoint := fun f => table.valid.target_endpoint (sigma.symm f)
      atom_injective := table.valid.atom_injective
      arc_injective := fun f => table.valid.arc_injective (sigma.symm f)
      interior_avoids_atoms := fun f t ht0 ht1 a =>
        table.valid.interior_avoids_atoms (sigma.symm f) t ht0 ht1 a
      intersects_only_at_common_endpoints := by
        intro f g t s hfg hmeet
        exact table.valid.intersects_only_at_common_endpoints (sigma.symm f) (sigma.symm g) t s
          (fun h => hfg (sigma.symm.injective h)) hmeet }

@[simp] theorem reindex_documented (sigma : E ≃ F) (table : BondPathTable E molecule conformation) :
    (table.reindex sigma).documented = table.documented :=
  rfl

@[simp] theorem reindex_edge (sigma : E ≃ F) (table : BondPathTable E molecule conformation) (f : F) :
    (table.reindex sigma).edge f = table.edge (sigma.symm f) :=
  rfl

@[simp] theorem reindex_sourceInteraction (sigma : E ≃ F)
    (table : BondPathTable E molecule conformation) (f : F) :
    ((table.reindex sigma).edge f).sourceInteraction = (table.edge (sigma.symm f)).sourceInteraction :=
  rfl

@[simp] theorem reindex_source (sigma : E ≃ F) (table : BondPathTable E molecule conformation) (f : F) :
    ((table.reindex sigma).edge f).source = (table.edge (sigma.symm f)).source :=
  rfl

@[simp] theorem reindex_target (sigma : E ≃ F) (table : BondPathTable E molecule conformation) (f : F) :
    ((table.reindex sigma).edge f).target = (table.edge (sigma.symm f)).target :=
  rfl

@[simp] theorem reindex_arc (sigma : E ≃ F) (table : BondPathTable E molecule conformation) (f : F)
    (t : I) :
    ((table.reindex sigma).edge f).arc t = (table.edge (sigma.symm f)).arc t :=
  rfl

theorem reindex_reindex (sigma : E ≃ F) (tau : F ≃ G)
    (table : BondPathTable E molecule conformation) :
    (table.reindex sigma).reindex tau = table.reindex (sigma.trans tau) := by
  apply ext_of_documented_edge
  · rfl
  · funext g
    simp [reindex]

theorem reindex_symm_reindex (sigma : E ≃ F) (table : BondPathTable E molecule conformation) :
    (table.reindex sigma).reindex sigma.symm = table := by
  apply ext_of_documented_edge
  · rfl
  · funext e
    simp [reindex]

/-- Reindexing along the identity equivalence is the identity on tables. -/
@[simp] theorem reindex_refl (table : BondPathTable E molecule conformation) :
    table.reindex (Equiv.refl E) = table := by
  apply ext_of_documented_edge
  · rfl
  · funext e
    simp [reindex]

/-- Constructive encoding of an arbitrary finite edge-indexed table into the `Fin`-indexed form,
using the explicit equivalence `Fintype.equivFin E`. -/
def encode (table : BondPathTable E molecule conformation) :
    BondPathRealization molecule (Fintype.card E) conformation :=
  table.reindex (Fintype.equivFin E)

/-- Decoding back out of the `Fin`-indexed form, inverse to `encode`. -/
def decode (table : BondPathRealization molecule (Fintype.card E) conformation) :
    BondPathTable E molecule conformation :=
  table.reindex (Fintype.equivFin E).symm

/-- Encoding followed by decoding recovers the full arbitrary-edge-type table exactly. -/
theorem decode_encode (table : BondPathTable E molecule conformation) :
    decode (encode table) = table := by
  simp [decode, encode, reindex_symm_reindex]

/-- Decoding followed by encoding recovers the full `Fin`-indexed table exactly. -/
theorem encode_decode (table : BondPathRealization molecule (Fintype.card E) conformation) :
    encode (decode table) = table := by
  simp [decode, encode, reindex_reindex]

/-- The constructive encoding is injective on full data (it has a left inverse, `decode`). -/
theorem encode_injective :
    Function.Injective
      (fun table : BondPathTable E molecule conformation => encode table) := by
  intro a b h
  have h' := congrArg decode h
  simpa [decode_encode] using h'

/-! #### Exact recovery of all data -/

/-- Exact recovery of every arc value after encoding. -/
theorem encode_arc (table : BondPathTable E molecule conformation) (e : E) (t : I) :
    ((encode table).edge (Fintype.equivFin E e)).arc t = (table.edge e).arc t := by
  simp [encode, reindex]

/-- Exact recovery of the oriented source atom after encoding. -/
theorem encode_source (table : BondPathTable E molecule conformation) (e : E) :
    ((encode table).edge (Fintype.equivFin E e)).source = (table.edge e).source := by
  simp [encode, reindex]

/-- Exact recovery of the oriented target atom after encoding. -/
theorem encode_target (table : BondPathTable E molecule conformation) (e : E) :
    ((encode table).edge (Fintype.equivFin E e)).target = (table.edge e).target := by
  simp [encode, reindex]

/-- Exact recovery of the source interaction index after encoding. -/
theorem encode_sourceInteraction (table : BondPathTable E molecule conformation) (e : E) :
    ((encode table).edge (Fintype.equivFin E e)).sourceInteraction =
      (table.edge e).sourceInteraction := by
  simp [encode, reindex]

/-- Exact recovery of the documented interaction subset after encoding. -/
theorem encode_documented (table : BondPathTable E molecule conformation) :
    (encode table).documented = table.documented :=
  rfl

/-- Exact recovery of every path value after decoding. -/
theorem decode_arc (table : BondPathRealization molecule (Fintype.card E) conformation)
    (e : E) (t : I) :
    ((decode table).edge e).arc t = (table.edge (Fintype.equivFin E e)).arc t := by
  simp [decode, reindex]

/-- Exact recovery of the oriented source atom after decoding. -/
theorem decode_source (table : BondPathRealization molecule (Fintype.card E) conformation)
    (e : E) :
    ((decode table).edge e).source = (table.edge (Fintype.equivFin E e)).source := by
  simp [decode, reindex]

/-- Exact recovery of the oriented target atom after decoding. -/
theorem decode_target (table : BondPathRealization molecule (Fintype.card E) conformation)
    (e : E) :
    ((decode table).edge e).target = (table.edge (Fintype.equivFin E e)).target := by
  simp [decode, reindex]

/-- Exact recovery of the source interaction index after decoding. -/
theorem decode_sourceInteraction
    (table : BondPathRealization molecule (Fintype.card E) conformation) (e : E) :
    ((decode table).edge e).sourceInteraction =
      (table.edge (Fintype.equivFin E e)).sourceInteraction := by
  simp [decode, reindex]

/-- Exact coverage implies that the number of documented source pair bonds equals the number of
edges.  This is a cardinality corollary of `exact_coverage`, not an extra assumption. -/
theorem card_documented_eq_card_edges (table : BondPathTable E molecule conformation) :
    table.documented.card = Fintype.card E := by
  let f : E → {i // i ∈ table.documented} :=
    fun e => ⟨(table.edge e).sourceInteraction, table.valid.edge_documented e⟩
  have hf_inj : Function.Injective f := by
    intro e₁ e₂ h
    have h₁ : (table.edge e₁).sourceInteraction = (table.edge e₂).sourceInteraction :=
      congrArg Subtype.val h
    obtain ⟨e, he, huniq⟩ :=
      table.valid.exact_coverage (table.edge e₁).sourceInteraction
        (table.valid.edge_documented e₁)
    have hA : e₁ = e := huniq e₁ rfl
    have hB : e₂ = e := huniq e₂ h₁.symm
    exact hA.trans hB.symm
  have hf_surj : Function.Surjective f := by
    intro i
    obtain ⟨e, he, _huniq⟩ := table.valid.exact_coverage i.1 i.2
    exact ⟨e, Subtype.ext he⟩
  have hcard : Fintype.card E = table.documented.card := by
    calc
      Fintype.card E = Fintype.card {i // i ∈ table.documented} :=
        Fintype.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)
      _ = table.documented.card := Fintype.card_coe table.documented
  exact hcard.symm

/-! #### Source preservation -/

/-- The exact oriented participant agreement of an edge with its source interaction. -/
theorem edge_participants_exact (table : BondPathTable E molecule conformation) (e : E) :
    (molecule.interactions.get (table.edge e).sourceInteraction).participants =
      [(table.edge e).source.val, (table.edge e).target.val] :=
  (table.edge e).participants_exact

/-- Every edge represents a documented interaction. -/
theorem edge_sourceInteraction_mem (table : BondPathTable E molecule conformation) (e : E) :
    (table.edge e).sourceInteraction ∈ table.documented :=
  table.valid.edge_documented e

/-- Interactions outside the documented pair-bond subset are never used as an edge source, so
they are retained unchanged in the source molecule. -/
theorem not_realized_of_not_documented (table : BondPathTable E molecule conformation)
    {index : Fin molecule.interactions.length} (hindex : index ∉ table.documented) :
    ¬ ∃ e : E, (table.edge e).sourceInteraction = index := by
  rintro ⟨e, he⟩
  exact hindex (he ▸ table.valid.edge_documented e)

/-! #### Transport along ambient homeomorphisms -/

/-- Transport a finite bond-path table along an ambient homeomorphism of real three-space.

The source molecule, the documented interaction subset, the edge type and every source
interaction index are unchanged; only the arcs and atom positions are moved.  Every realization
obligation is preserved because a homeomorphism is injective and the ambient space is mapped to
itself. -/
def mapHomeomorph (h : EmbeddedReal3 ≃ₜ EmbeddedReal3)
    (table : BondPathTable E molecule conformation) :
    BondPathTable E molecule (fun a => h (conformation a)) where
  documented := table.documented
  edge e := (table.edge e).mapHomeomorph h
  valid :=
    { documented_genuine := table.valid.documented_genuine
      edge_documented := table.valid.edge_documented
      exact_coverage := table.valid.exact_coverage
      source_endpoint := by
        intro e
        simp [SourceBondPath.mapHomeomorph, table.valid.source_endpoint e]
      target_endpoint := by
        intro e
        simp [SourceBondPath.mapHomeomorph, table.valid.target_endpoint e]
      atom_injective := by
        intro a b hab
        exact table.valid.atom_injective (h.injective hab)
      arc_injective := by
        intro e t s hts
        exact table.valid.arc_injective e (h.injective hts)
      interior_avoids_atoms := by
        intro e t ht0 ht1 a hEq
        exact table.valid.interior_avoids_atoms e t ht0 ht1 a (h.injective hEq)
      intersects_only_at_common_endpoints := by
        intro e f t s hne hmeet
        exact table.valid.intersects_only_at_common_endpoints e f t s hne
          (h.injective hmeet) }

@[simp] theorem mapHomeomorph_documented (h : EmbeddedReal3 ≃ₜ EmbeddedReal3)
    (table : BondPathTable E molecule conformation) :
    (table.mapHomeomorph h).documented = table.documented :=
  rfl

@[simp] theorem mapHomeomorph_arc (h : EmbeddedReal3 ≃ₜ EmbeddedReal3)
    (table : BondPathTable E molecule conformation) (e : E) (t : I) :
    ((table.mapHomeomorph h).edge e).arc t = h ((table.edge e).arc t) :=
  rfl

@[simp] theorem mapHomeomorph_sourceInteraction (h : EmbeddedReal3 ≃ₜ EmbeddedReal3)
    (table : BondPathTable E molecule conformation) (e : E) :
    ((table.mapHomeomorph h).edge e).sourceInteraction =
      (table.edge e).sourceInteraction :=
  rfl

@[simp] theorem mapHomeomorph_source (h : EmbeddedReal3 ≃ₜ EmbeddedReal3)
    (table : BondPathTable E molecule conformation) (e : E) :
    ((table.mapHomeomorph h).edge e).source = (table.edge e).source :=
  rfl

@[simp] theorem mapHomeomorph_target (h : EmbeddedReal3 ≃ₜ EmbeddedReal3)
    (table : BondPathTable E molecule conformation) (e : E) :
    ((table.mapHomeomorph h).edge e).target = (table.edge e).target :=
  rfl

end BondPathTable

/-- A bond-path table together with an explicit completeness proof for the selected source
pair-bond specification.  This is the constructor-level form of "all chosen pair bonds are
represented".  It assumes realization validity as supplied data and asserts no embedding
existence, no chemical admissibility and no coverage beyond the fixed default selection
`IsGenuinePairBondAt`; a different kind selection would require a differently parameterized
structure, which this module does not provide. -/
structure CompleteBondPathTable (E : Type*) [Fintype E] (molecule : SemanticMolecule)
    (conformation : MolecularConformation (Fin molecule.atomCount)) where
  /-- The underlying realized bond-path table. -/
  table : BondPathTable E molecule conformation
  /-- Every selected binary source pair bond is documented. -/
  complete : CompleteForSourcePairBonds molecule table.documented

namespace CompleteBondPathTable

variable {E : Type*} [Fintype E]
variable {molecule : SemanticMolecule}
variable {conformation : MolecularConformation (Fin molecule.atomCount)}

/-- Exact coverage of the *entire* selected source pair-bond specification: every selected
binary pair bond is realized by exactly one edge.  This combines the caller's completeness
hypothesis with the realization table's exact coverage. -/
theorem exact_coverage_of_selected (table : CompleteBondPathTable E molecule conformation)
    {index : Fin molecule.interactions.length}
    (hindex : IsGenuinePairBondAt molecule index) :
    ∃! e : E, (table.table.edge e).sourceInteraction = index :=
  table.table.valid.exact_coverage index (table.complete index hindex)

/-- The cardinality of a complete documented subset is the number of edges. -/
theorem card_documented_eq_card_edges (table : CompleteBondPathTable E molecule conformation) :
    table.table.documented.card = Fintype.card E :=
  table.table.card_documented_eq_card_edges

end CompleteBondPathTable

/-! ### Source-bound record and the independent finite-edge input -/

/-- The independent finite-edge-indexed input over an arbitrary finite edge type `E`.

Only the edge index type `E` is arbitrary.  Atom and interaction indices remain source-indexed
by `Fin source.molecule.atomCount` and `Fin source.molecule.interactions.length`.
`EdgeIndexedSourceBoundInput.encode` constructively maps this to
`SourceBoundEmbeddedBondPaths` using the explicit equivalence `Fintype.equivFin E`, and the
surrounding theorems show exact recovery of all data. -/
structure EdgeIndexedSourceBoundInput (E : Type*) [Fintype E] where
  /-- The complete authoritative chemical source, retained unchanged. -/
  source : AuthoritativeChemicalInput
  /-- Real-valued atom positions. -/
  conformation : MolecularConformation (Fin source.molecule.atomCount)
  /-- The finite bond-path table over the arbitrary edge type `E`. -/
  table : BondPathTable E source.molecule conformation

/-- A complete source-bound embedded bond-path configuration: a full authoritative chemical
input, a `Fin edgeCount` bond-path table realizing an explicitly documented subset of its
genuine pair bonds, and a real-valued conformation of its atoms.

The source (`source.molecule`, its atom list and its interaction list) is stored verbatim; the
path data is additional structure and never rewrites the source. -/
structure SourceBoundEmbeddedBondPaths where
  /-- The complete authoritative chemical source, retained unchanged. -/
  source : AuthoritativeChemicalInput
  /-- Number of embedded bond paths. -/
  edgeCount : ℕ
  /-- Real-valued atom positions. -/
  conformation : MolecularConformation (Fin source.molecule.atomCount)
  /-- The finite bond-edge table realizing a documented subset of source pair bonds. -/
  table : BondPathRealization source.molecule edgeCount conformation

namespace SourceBoundEmbeddedBondPaths

/-- Forget every path datum, retaining only the chemical source. -/
def sourceProjection (input : SourceBoundEmbeddedBondPaths) : AuthoritativeChemicalInput :=
  input.source

@[simp] theorem sourceProjection_mk (source : AuthoritativeChemicalInput) (edgeCount : ℕ)
    (conformation : MolecularConformation (Fin source.molecule.atomCount))
    (table : BondPathRealization source.molecule edgeCount conformation) :
    sourceProjection ⟨source, edgeCount, conformation, table⟩ = source :=
  rfl

/-- The source interaction list is retained verbatim. -/
theorem source_interactions_preserved (input : SourceBoundEmbeddedBondPaths) :
    input.source.molecule.interactions = input.source.molecule.interactions :=
  rfl

/-- The source atom list is retained verbatim. -/
theorem source_atoms_preserved (input : SourceBoundEmbeddedBondPaths) :
    input.source.molecule.atoms = input.source.molecule.atoms :=
  rfl

/-- Recover the independent edge-indexed input form along an explicit equivalence of the edge
type with `Fin input.edgeCount`.  This is the inverse direction of the constructive encoding. -/
def toEdgeIndexed (input : SourceBoundEmbeddedBondPaths) (E : Type*) [Fintype E]
    (sigma : E ≃ Fin input.edgeCount) : EdgeIndexedSourceBoundInput E where
  source := input.source
  conformation := input.conformation
  table := input.table.reindex sigma.symm

end SourceBoundEmbeddedBondPaths

namespace EdgeIndexedSourceBoundInput

variable {E : Type*} [Fintype E]

/-- Constructive encoding of an independent finite-edge-indexed input into the source-bound
`Fin (Fintype.card E)` record.  The source and the conformation are copied verbatim; only the
edge index is transported along `Fintype.equivFin E`. -/
def encode (input : EdgeIndexedSourceBoundInput E) : SourceBoundEmbeddedBondPaths where
  source := input.source
  edgeCount := Fintype.card E
  conformation := input.conformation
  table := input.table.reindex (Fintype.equivFin E)

@[simp] theorem encode_source (input : EdgeIndexedSourceBoundInput E) :
    (input.encode).source = input.source :=
  rfl

@[simp] theorem encode_conformation (input : EdgeIndexedSourceBoundInput E) :
    (input.encode).conformation = input.conformation :=
  rfl

@[simp] theorem encode_edgeCount (input : EdgeIndexedSourceBoundInput E) :
    (input.encode).edgeCount = Fintype.card E :=
  rfl

/-- Exact recovery of every arc value after encoding. -/
theorem encode_arc (input : EdgeIndexedSourceBoundInput E) (e : E) (t : I) :
    ((input.encode).table.edge (Fintype.equivFin E e)).arc t = (input.table.edge e).arc t :=
  BondPathTable.encode_arc input.table e t

/-- Exact recovery of the oriented source atom after encoding. -/
theorem encode_atom_source (input : EdgeIndexedSourceBoundInput E) (e : E) :
    ((input.encode).table.edge (Fintype.equivFin E e)).source =
      (input.table.edge e).source :=
  BondPathTable.encode_source input.table e

/-- Exact recovery of the oriented target atom after encoding. -/
theorem encode_atom_target (input : EdgeIndexedSourceBoundInput E) (e : E) :
    ((input.encode).table.edge (Fintype.equivFin E e)).target =
      (input.table.edge e).target :=
  BondPathTable.encode_target input.table e

/-- Exact recovery of the source interaction index after encoding. -/
theorem encode_sourceInteraction (input : EdgeIndexedSourceBoundInput E) (e : E) :
    ((input.encode).table.edge (Fintype.equivFin E e)).sourceInteraction =
      (input.table.edge e).sourceInteraction :=
  BondPathTable.encode_sourceInteraction input.table e

/-- The encoding is a left inverse of `toEdgeIndexed` along `Fintype.equivFin E`: the full
source-bound record is recovered exactly. -/
theorem encode_toEdgeIndexed (input : EdgeIndexedSourceBoundInput E) :
    (input.encode).toEdgeIndexed E (Fintype.equivFin E) = input := by
  cases input with
  | mk source conformation table =>
    simp only [EdgeIndexedSourceBoundInput.encode, SourceBoundEmbeddedBondPaths.toEdgeIndexed]
    rw [BondPathTable.reindex_symm_reindex]

end EdgeIndexedSourceBoundInput

/-! ### The source-only projection is not injective

The conformation is not recoverable from the chemical source alone.  We exhibit two distinct
configurations over one and the same source, both with the empty edge table, so the witness
isolates the loss of atom geometry.  It does *not* exhibit two different path families over
identical atom positions, and it is not a universal claim: it only refutes injectivity of the
forgetful source projection. -/

/-- A one-atom source used solely for the non-injectivity witness. -/
def singletonSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [{ element :=
             { atomicNumber := 1, positive := by decide, atMost118 := by decide }
           isotopeMassNumber? := none
           formalCharge := 0
           unpairedElectrons := 0
           aromaticInput := false }]
      interactions := [] }
  spatial? := none
  diagram? := none

/-- The unique atom index of `singletonSource`. -/
def singletonAtomIndex : Fin singletonSource.molecule.atomCount :=
  ⟨0, by decide⟩

/-- A nonzero ambient point, chosen classically; used only to separate two conformations. -/
def chosenNonzeroPoint : EmbeddedReal3 :=
  Classical.choose (exists_ne (0 : EmbeddedReal3))

theorem chosenNonzeroPoint_ne_zero : chosenNonzeroPoint ≠ 0 :=
  Classical.choose_spec (exists_ne (0 : EmbeddedReal3))

/-- The zero conformation of the one-atom source. -/
def zeroConformation :
    MolecularConformation (Fin singletonSource.molecule.atomCount) :=
  fun _ => 0

/-- The nonzero conformation of the one-atom source. -/
def nonzeroConformation :
    MolecularConformation (Fin singletonSource.molecule.atomCount) :=
  fun _ => chosenNonzeroPoint

/-- Injectivity of the zero conformation: the domain has one atom. -/
theorem zeroConformation_injective : Function.Injective zeroConformation := by
  intro a b _
  apply Fin.ext
  rw [Nat.lt_one_iff.mp a.isLt, Nat.lt_one_iff.mp b.isLt]

/-- Injectivity of the nonzero conformation: the domain has one atom. -/
theorem nonzeroConformation_injective : Function.Injective nonzeroConformation := by
  intro a b _
  apply Fin.ext
  rw [Nat.lt_one_iff.mp a.isLt, Nat.lt_one_iff.mp b.isLt]

/-- The empty bond-path table over the zero conformation. -/
def zeroTable : BondPathRealization singletonSource.molecule 0 zeroConformation where
  documented := ∅
  edge := fun e => Fin.elim0 e
  valid :=
    { documented_genuine := by
        intro index h
        exact absurd h (by simp)
      edge_documented := by
        intro e
        exact Fin.elim0 e
      exact_coverage := by
        intro index h
        exact absurd h (by simp)
      source_endpoint := by
        intro e
        exact Fin.elim0 e
      target_endpoint := by
        intro e
        exact Fin.elim0 e
      atom_injective := zeroConformation_injective
      arc_injective := by
        intro e
        exact Fin.elim0 e
      interior_avoids_atoms := by
        intro e
        exact Fin.elim0 e
      intersects_only_at_common_endpoints := by
        intro e
        exact Fin.elim0 e }

/-- The empty bond-path table over the nonzero conformation. -/
def nonzeroTable : BondPathRealization singletonSource.molecule 0 nonzeroConformation where
  documented := ∅
  edge := fun e => Fin.elim0 e
  valid :=
    { documented_genuine := by
        intro index h
        exact absurd h (by simp)
      edge_documented := by
        intro e
        exact Fin.elim0 e
      exact_coverage := by
        intro index h
        exact absurd h (by simp)
      source_endpoint := by
        intro e
        exact Fin.elim0 e
      target_endpoint := by
        intro e
        exact Fin.elim0 e
      atom_injective := nonzeroConformation_injective
      arc_injective := by
        intro e
        exact Fin.elim0 e
      interior_avoids_atoms := by
        intro e
        exact Fin.elim0 e
      intersects_only_at_common_endpoints := by
        intro e
        exact Fin.elim0 e }

/-- One source-bound configuration over `singletonSource`. -/
def zeroConfiguration : SourceBoundEmbeddedBondPaths where
  source := singletonSource
  edgeCount := 0
  conformation := zeroConformation
  table := zeroTable

/-- A second source-bound configuration over the same source. -/
def nonzeroConfiguration : SourceBoundEmbeddedBondPaths where
  source := singletonSource
  edgeCount := 0
  conformation := nonzeroConformation
  table := nonzeroTable

/-- The two configurations are distinct.  The `conformation` projection is dependent on the
source field, so instead of comparing conformations directly we compare their set-theoretic ranges,
which are ordinary sets of ambient points. -/
theorem zeroConfiguration_ne_nonzeroConfiguration :
    zeroConfiguration ≠ nonzeroConfiguration := by
  intro h
  have hrange :
      Set.range zeroConfiguration.conformation = Set.range nonzeroConfiguration.conformation :=
    congrArg (fun configuration => Set.range configuration.conformation) h
  have hmem : (0 : EmbeddedReal3) ∈ Set.range nonzeroConfiguration.conformation := by
    rw [← hrange]
    exact ⟨⟨0, by decide⟩, rfl⟩
  obtain ⟨a, ha⟩ := hmem
  have hzero : chosenNonzeroPoint = 0 := by
    simpa [nonzeroConfiguration, nonzeroConformation] using ha
  exact chosenNonzeroPoint_ne_zero hzero

/-- The source-only forgetful projection is not injective: two distinct embedded bond-path
configurations share the same authoritative chemical source.

Precisely: this witness varies only the atom geometry, and both tables realize the empty
documented subset over the one-atom source.  It establishes that the source alone does not
determine the geometric configuration (so the source-only projection has no inverse).  It is not
a claim that two distinct realizations of the same nonempty bond-path table share a source, and
it is not a witness that two different path families can be realized at identical atom
positions: the two configurations differ in their conformations, not in their (both empty) path
data. -/
theorem sourceProjection_not_injective :
    ¬ Function.Injective SourceBoundEmbeddedBondPaths.sourceProjection := by
  intro hinj
  have hEq : zeroConfiguration = nonzeroConfiguration := hinj rfl
  exact zeroConfiguration_ne_nonzeroConfiguration hEq

end

end TetraStereo.OneCenter
