import TetraStereo.OneCenter.OrganicStereoAuthoritativeSourceBridge
import TetraStereo.OneCenter.OrganicStereoFiniteClassicalDescriptionRecovery

set_option autoImplicit false

namespace TetraStereo.OneCenter

open IUPACDrawing2006.ST6

noncomputable section

/-!
# Ingress from independent finite sources into whole-state evidence completions

`OrganicStereoAuthoritativeSourceBridge` proves that every `CertifiedAuthoritativeChemicalInput`
decodes to an independent-label `OrganicFiniteSource (Fin atomCount)` and that re-encoding that
source recovers the original input exactly, including the optional rational spatial channel and the
optional drawing channel.

This module interprets such a finite source as a *set of whole states*: the Cartesian
evidence-completions of the source.  Every completion is an actual `WholeState V (Fin 0) (Fin 0)`
record, not a summary and not a per-channel product.  In a completion

* the interaction hypergraph is exactly the source graph,
* `rationalPositions?` is exactly the source spatial channel (absence stays `none`),
* `diagram?` is exactly the source drawing data (absence stays `none`, and present data is retained
  literally, including every bond occurrence and every atom-parity token),
* the shared real conformation agrees pointwise with every *supplied* rational position (this is the
  `rationalPositions_valid` field of the whole state, so it is a genuine constraint carried by the
  state rather than an extra axiom),
* the electronic inventory is absent, the role ledger, sparse partial positions, incidence ledger,
  fragments, drawing conventions, cages, residue ledger and frames are empty, and the path and band
  index types are `Fin 0`, so no bond-path or band data is invented.

When the source supplies no rational positions at all, `rationalPositions?` is `none`.  Then the
whole-state validity field is vacuous and **every** real conformation is admitted.  The set is
therefore not a singleton and is never identified with a zero coordinate; the zero vector is used
only as one explicit nonemptiness witness.  When positions are supplied, every admitted
conformation takes exactly the embedded rational value at every atom.

The projection `sourceOfState` reads a whole state back to its graph, rational positions and
drawing data.  Every completion projects to the original source, and encoding that projection
through the existing `OrganicFiniteSource.encode` reproduces the source exactly.  Consequently,
for every certified authoritative input, every completion of the ingress source of `certified.decode`
encodes back to `certified.input` exactly, through the existing `encode_decode` theorem.

## Scope boundaries

The completions are a *Cartesian evidence-completion*.  They record exactly the geometric
information that the source supplies as rational coordinates.  Drawing wedges, bond styles,
atom-parity tokens and diagram scopes are preserved as drawing data; this module does **not** derive
additional three-dimensional constraints from them, does not interpret them physically, and does not
claim that structurally well-formed input is physically realizable.  Nothing here is a desired-answer
premise: the completion set is defined from the source alone, and no original input is stored inside
a completion.

The optional packaging into `FiniteClassicalInformation.ofStates` keeps the supplied
`ConfigurationKnowledge` tag as metadata only.  Consistency of the resulting information is proved
from the mathematical nonemptiness of the completion set, never from the tag.
-/

/-! ## The conformation constraint supplied by rational positions -/

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- The real conformations admissible for a finite source.  A conformation belongs to this set when
it agrees with every rational position that the source actually supplies.  If `spatial? = none`
there is no constraint; the set is `Set.univ` (proved below).  If `spatial? = some positions` the
conformation is fixed pointwise to the exact rational embedding (proved below). -/
def sourceConformations (source : OrganicFiniteSource V) : Set (MolecularConformation V) :=
  { conformation | ∀ positions : V → CartesianPoint3,
      source.spatial? = some positions → ∀ atom : V,
        (positions atom).toEuclideanPoint = conformation atom }

/-- Membership unfolds to exactly the whole-state rational-position agreement condition. -/
theorem mem_sourceConformations_iff (source : OrganicFiniteSource V)
    (conformation : MolecularConformation V) :
    conformation ∈ sourceConformations source ↔
      ∀ positions : V → CartesianPoint3, source.spatial? = some positions → ∀ atom : V,
        (positions atom).toEuclideanPoint = conformation atom :=
  Iff.rfl

/-! ## The complete source projection of a whole state -/

/-- Project a whole state to an independent source using exactly the three ingress channels: the
interaction graph, the optional rational positions and the optional drawing data.  All other
channels of the whole state are deliberately dropped; this is the projection that the ingress set
must invert.  In particular the existing `encodedAuthoritativeView` is not used, because it drops the
spatial channel. -/
def sourceOfState (state : WholeState V (Fin 0) (Fin 0)) : OrganicFiniteSource V where
  graph := state.graph
  spatial? := state.rationalPositions?
  diagram? := state.diagram?

@[simp] theorem sourceOfState_graph (state : WholeState V (Fin 0) (Fin 0)) :
    (sourceOfState state).graph = state.graph := rfl

@[simp] theorem sourceOfState_spatial? (state : WholeState V (Fin 0) (Fin 0)) :
    (sourceOfState state).spatial? = state.rationalPositions? := rfl

@[simp] theorem sourceOfState_diagram? (state : WholeState V (Fin 0) (Fin 0)) :
    (sourceOfState state).diagram? = state.diagram? := rfl

/-! ## The default completion for one admissible conformation -/

/-- The whole state determined by the source and one admissible real conformation.  The graph,
rational positions and drawing data come from the source; every unsupplied channel is genuinely
absent or empty.  In particular `Fin 0` path and band index types contain no data, `diagram?` keeps
the source drawing data literally, and no coordinate is invented: `rationalPositions?` is exactly
the source channel. -/
def defaultCompletion (source : OrganicFiniteSource V)
    (conformation : MolecularConformation V)
    (valid : conformation ∈ sourceConformations source) :
    WholeState V (Fin 0) (Fin 0) where
  graph := source.graph
  electronic? := none
  electronic_unpaired := by
    intro channel present
    cases present
  conformation := conformation
  rationalPositions? := source.spatial?
  rationalPositions_valid := valid
  roles := []
  role_valid := by
    intro annotation member
    simp at member
  paths := fun edge => Fin.elim0 edge
  path_valid := by
    intro edge
    exact Fin.elim0 edge
  path_source_endpoint := by
    intro edge
    exact Fin.elim0 edge
  path_target_endpoint := by
    intro edge
    exact Fin.elim0 edge
  bandFamily := fun band => Fin.elim0 band
  band_agreement := by
    intro band record
    exact Fin.elim0 band
  diagram? := source.diagram?
  diagramPartial? := none
  diagramIncidence := []
  diagram_valid := by
    intro row member
    simp at member
  fragments := []
  conventions := []
  cages := []
  residueLedger? := none
  frames := []

@[simp] theorem defaultCompletion_graph (source : OrganicFiniteSource V)
    (conformation : MolecularConformation V)
    (valid : conformation ∈ sourceConformations source) :
    (defaultCompletion source conformation valid).graph = source.graph := rfl

@[simp] theorem defaultCompletion_conformation (source : OrganicFiniteSource V)
    (conformation : MolecularConformation V)
    (valid : conformation ∈ sourceConformations source) :
    (defaultCompletion source conformation valid).conformation = conformation := rfl

@[simp] theorem defaultCompletion_rationalPositions? (source : OrganicFiniteSource V)
    (conformation : MolecularConformation V)
    (valid : conformation ∈ sourceConformations source) :
    (defaultCompletion source conformation valid).rationalPositions? = source.spatial? := rfl

@[simp] theorem defaultCompletion_diagram? (source : OrganicFiniteSource V)
    (conformation : MolecularConformation V)
    (valid : conformation ∈ sourceConformations source) :
    (defaultCompletion source conformation valid).diagram? = source.diagram? := rfl

@[simp] theorem defaultCompletion_electronic? (source : OrganicFiniteSource V)
    (conformation : MolecularConformation V)
    (valid : conformation ∈ sourceConformations source) :
    (defaultCompletion source conformation valid).electronic? = none := rfl

@[simp] theorem defaultCompletion_roles (source : OrganicFiniteSource V)
    (conformation : MolecularConformation V)
    (valid : conformation ∈ sourceConformations source) :
    (defaultCompletion source conformation valid).roles = [] := rfl

@[simp] theorem defaultCompletion_frames (source : OrganicFiniteSource V)
    (conformation : MolecularConformation V)
    (valid : conformation ∈ sourceConformations source) :
    (defaultCompletion source conformation valid).frames = [] := rfl

/-! ## The completion set of a finite source -/

/-- The **set of whole-state completions** of a finite source.  A state belongs to this set exactly
when it is the default state of some admissible real conformation.  Thus the only freedom is the
shared real conformation, and it is constrained only by the rational positions the source actually
supplies.  Other channels are fixed to their default empty or absent values. -/
def completions (source : OrganicFiniteSource V) :
    Set (WholeState V (Fin 0) (Fin 0)) :=
  { state | ∃ (conformation : MolecularConformation V)
      (valid : conformation ∈ sourceConformations source),
      defaultCompletion source conformation valid = state }

/-- Membership is exactly the existence of an admissible conformation whose default state is the
given state. -/
theorem mem_completions_iff (source : OrganicFiniteSource V)
    (state : WholeState V (Fin 0) (Fin 0)) :
    state ∈ completions source ↔
      ∃ (conformation : MolecularConformation V)
        (valid : conformation ∈ sourceConformations source),
        defaultCompletion source conformation valid = state :=
  Iff.rfl

/-- Every default completion belongs to the completion set. -/
theorem defaultCompletion_mem_completions (source : OrganicFiniteSource V)
    (conformation : MolecularConformation V)
    (valid : conformation ∈ sourceConformations source) :
    defaultCompletion source conformation valid ∈ completions source :=
  ⟨conformation, valid, rfl⟩

/-! ## Nonemptiness of the completion set -/

/-- An explicit admissible conformation.  When the source supplies rational positions, it is forced
to the exact rational embedding.  When the source supplies none, we use the zero vector as **one**
witness of nonemptiness; this is not a semantic identification of unknown coordinates with zero. -/
def canonicalConformation (source : OrganicFiniteSource V) : MolecularConformation V :=
  match source.spatial? with
  | none => fun _ => (0 : EuclideanSpace ℝ (Fin 3))
  | some positions => fun atom => (positions atom).toEuclideanPoint

/-- The canonical conformation is admissible. -/
theorem canonicalConformation_mem (source : OrganicFiniteSource V) :
    canonicalConformation source ∈ sourceConformations source := by
  intro positions present atom
  cases observed : source.spatial? with
  | none =>
      rw [observed] at present
      cases present
  | some actual =>
      rw [observed] at present
      injection present with equal
      subst equal
      simp only [canonicalConformation, observed]

/-- The canonical completion of a source. -/
def canonicalCompletion (source : OrganicFiniteSource V) :
    WholeState V (Fin 0) (Fin 0) :=
  defaultCompletion source (canonicalConformation source)
    (canonicalConformation_mem source)

/-- The canonical completion belongs to the completion set. -/
theorem canonicalCompletion_mem (source : OrganicFiniteSource V) :
    canonicalCompletion source ∈ completions source :=
  defaultCompletion_mem_completions source (canonicalConformation source)
    (canonicalConformation_mem source)

/-- **The completion set is nonempty**, constructively, for every finite source. -/
theorem completions_nonempty (source : OrganicFiniteSource V) :
    (completions source).Nonempty :=
  ⟨canonicalCompletion source, canonicalCompletion_mem source⟩

/-! ## Absent and present spatial channels -/

/-- If the source supplies no positions, every real conformation is admissible. -/
theorem mem_sourceConformations_of_absent (source : OrganicFiniteSource V)
    (absent : source.spatial? = none) (conformation : MolecularConformation V) :
    conformation ∈ sourceConformations source := by
  intro positions present
  rw [absent] at present
  cases present

/-- With no supplied positions the admissible-conformation set is the whole function space: the
absence of spatial evidence is genuine unknown geometry, not a single zero configuration. -/
theorem sourceConformations_eq_univ_of_absent (source : OrganicFiniteSource V)
    (absent : source.spatial? = none) :
    sourceConformations source = Set.univ := by
  ext conformation
  exact ⟨fun _ => Set.mem_univ conformation, fun _ =>
    mem_sourceConformations_of_absent source absent conformation⟩

/-- With no supplied positions, an arbitrary conformation occurs in some completion.  Thus the
completion set is not a singleton and does not silently choose a coordinate origin. -/
theorem exists_completion_of_absent (source : OrganicFiniteSource V)
    (absent : source.spatial? = none) (conformation : MolecularConformation V) :
    ∃ state ∈ completions source, state.conformation = conformation :=
  ⟨defaultCompletion source conformation
      (mem_sourceConformations_of_absent source absent conformation),
    defaultCompletion_mem_completions source conformation
      (mem_sourceConformations_of_absent source absent conformation),
    rfl⟩

/-- Every admissible conformation agrees pointwise with each supplied rational position. -/
theorem conformations_fix_of_present (source : OrganicFiniteSource V)
    {positions : V → CartesianPoint3} (present : source.spatial? = some positions)
    (conformation : MolecularConformation V)
    (member : conformation ∈ sourceConformations source) (atom : V) :
    conformation atom = (positions atom).toEuclideanPoint :=
  (member positions present atom).symm

/-- A present spatial channel fixes the admissible conformation pointwise, hence uniquely. -/
theorem sourceConformations_present_subsingleton (source : OrganicFiniteSource V)
    {positions : V → CartesianPoint3} (present : source.spatial? = some positions) :
    (sourceConformations source).Subsingleton := by
  intro first hfirst second hsecond
  funext atom
  rw [conformations_fix_of_present source present first hfirst atom,
    conformations_fix_of_present source present second hsecond atom]

/-! ## Projections of an arbitrary completion -/

/-- The graph of a completion is the source graph. -/
theorem completion_graph_eq {source : OrganicFiniteSource V}
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    state.graph = source.graph := by
  rcases member with ⟨conformation, valid, rfl⟩
  rfl

/-- The rational spatial channel of a completion is exactly the source spatial channel, with
absence preserved. -/
theorem completion_rationalPositions?_eq {source : OrganicFiniteSource V}
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    state.rationalPositions? = source.spatial? := by
  rcases member with ⟨conformation, valid, rfl⟩
  rfl

/-- The drawing channel of a completion is exactly the source drawing channel, with absence
preserved.  Present drawing data is retained literally; no wedge or parity token is interpreted. -/
theorem completion_diagram?_eq {source : OrganicFiniteSource V}
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    state.diagram? = source.diagram? := by
  rcases member with ⟨conformation, valid, rfl⟩
  rfl

/-- The shared real conformation of a completion agrees pointwise with every supplied rational
position.  This is the genuine Cartesian constraint of the completion. -/
theorem completion_conformation_agrees (source : OrganicFiniteSource V)
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source)
    {positions : V → CartesianPoint3} (present : source.spatial? = some positions) (atom : V) :
    (positions atom).toEuclideanPoint = state.conformation atom := by
  rcases member with ⟨conformation, valid, rfl⟩
  exact valid positions present atom

/-- Every completion of a source with a present spatial channel has the same conformation at each
atom, namely the exact embedded rational position. -/
theorem completions_present_spatial_conformation_eq (source : OrganicFiniteSource V)
    {positions : V → CartesianPoint3} (present : source.spatial? = some positions)
    {first second : WholeState V (Fin 0) (Fin 0)}
    (hfirst : first ∈ completions source) (hsecond : second ∈ completions source) (atom : V) :
    first.conformation atom = second.conformation atom := by
  rw [← completion_conformation_agrees source hfirst present atom,
    ← completion_conformation_agrees source hsecond present atom]

/-- The electronic inventory of a completion is absent. -/
theorem completion_electronic?_eq_none {source : OrganicFiniteSource V}
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    state.electronic? = none := by
  rcases member with ⟨conformation, valid, rfl⟩
  rfl

/-- The ordered role ledger of a completion is empty. -/
theorem completion_roles_eq_nil {source : OrganicFiniteSource V}
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    state.roles = [] := by
  rcases member with ⟨conformation, valid, rfl⟩
  rfl

/-- The sparse partial drawing positions of a completion are absent. -/
theorem completion_diagramPartial?_eq_none {source : OrganicFiniteSource V}
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    state.diagramPartial? = none := by
  rcases member with ⟨conformation, valid, rfl⟩
  rfl

/-- The sparse incidence ledger of a completion is empty. -/
theorem completion_diagramIncidence_eq_nil {source : OrganicFiniteSource V}
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    state.diagramIncidence = [] := by
  rcases member with ⟨conformation, valid, rfl⟩
  rfl

/-- The fragment channel of a completion is empty. -/
theorem completion_fragments_eq_nil {source : OrganicFiniteSource V}
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    state.fragments = [] := by
  rcases member with ⟨conformation, valid, rfl⟩
  rfl

/-- The drawing-convention channel of a completion is empty. -/
theorem completion_conventions_eq_nil {source : OrganicFiniteSource V}
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    state.conventions = [] := by
  rcases member with ⟨conformation, valid, rfl⟩
  rfl

/-- The cage-annotation channel of a completion is empty. -/
theorem completion_cages_eq_nil {source : OrganicFiniteSource V}
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    state.cages = [] := by
  rcases member with ⟨conformation, valid, rfl⟩
  rfl

/-- The residue-link ledger of a completion is absent. -/
theorem completion_residueLedger?_eq_none {source : OrganicFiniteSource V}
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    state.residueLedger? = none := by
  rcases member with ⟨conformation, valid, rfl⟩
  rfl

/-- The frame-annotation channel of a completion is empty. -/
theorem completion_frames_eq_nil {source : OrganicFiniteSource V}
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    state.frames = [] := by
  rcases member with ⟨conformation, valid, rfl⟩
  rfl

/-! ## Completions reconstruct the exact source -/

/-- The source projection of a default completion is the original source. -/
@[simp] theorem sourceOfState_defaultCompletion (source : OrganicFiniteSource V)
    (conformation : MolecularConformation V)
    (valid : conformation ∈ sourceConformations source) :
    sourceOfState (defaultCompletion source conformation valid) = source := by
  cases source with
  | mk graph spatial? diagram? => rfl

/-- **Every completion projects to the original source.**  The projection uses exactly graph,
`rationalPositions?` and `diagram?`; no hidden payload is consulted. -/
theorem sourceOfState_of_mem_completions {source : OrganicFiniteSource V}
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    sourceOfState state = source := by
  rcases member with ⟨conformation, valid, rfl⟩
  exact sourceOfState_defaultCompletion source conformation valid

/-- **Every completion re-encodes to the original source** at any external enumeration. -/
theorem encode_sourceOfState_of_mem_completions (source : OrganicFiniteSource V)
    (enumeration : V ≃ Fin (Fintype.card V))
    {state : WholeState V (Fin 0) (Fin 0)} (member : state ∈ completions source) :
    (sourceOfState state).encode enumeration = source.encode enumeration := by
  rw [sourceOfState_of_mem_completions member]

/-! ## Ingress of a certified authoritative input -/

namespace CertifiedAuthoritativeChemicalInput

/-- Every completion of the ingress source of a certified input projects to exactly
`certified.decode`. -/
theorem sourceOfState_completion_eq_decode (certified : CertifiedAuthoritativeChemicalInput)
    {state : WholeState (Fin certified.input.molecule.atomCount) (Fin 0) (Fin 0)}
    (member : state ∈ completions (decode certified)) :
    sourceOfState state = decode certified :=
  sourceOfState_of_mem_completions member

/-- **Exact input reconstruction for every completion of every certified input.**  The construction
uses the existing `decode` ingress and the existing `encode_decode` round-trip theorem; the original
input is not stored in any completion and is not assumed. -/
theorem encode_sourceOfState_completion (certified : CertifiedAuthoritativeChemicalInput)
    {state : WholeState (Fin certified.input.molecule.atomCount) (Fin 0) (Fin 0)}
    (member : state ∈ completions (decode certified)) :
    (sourceOfState state).encode
        (identityEnumeration certified.input.molecule.atomCount) = certified.input := by
  rw [encode_sourceOfState_of_mem_completions (decode certified)
    (identityEnumeration certified.input.molecule.atomCount) member]
  exact encode_decode certified

/-- Every certified input has at least one completion: the ingress is never vacuously applicable. -/
theorem completions_nonempty_of_decode (certified : CertifiedAuthoritativeChemicalInput) :
    (completions (decode certified)).Nonempty :=
  completions_nonempty (decode certified)

/-- If the certified input supplies no spatial data, an arbitrary real conformation occurs in a
completion of its ingress source. -/
theorem exists_completion_of_absent_spatial (certified : CertifiedAuthoritativeChemicalInput)
    (absent : certified.input.spatial? = none)
    (conformation : MolecularConformation (Fin certified.input.molecule.atomCount)) :
    ∃ state ∈ completions (decode certified), state.conformation = conformation :=
  exists_completion_of_absent (decode certified)
    (decode_spatial?_eq_none certified absent) conformation

/-- If the certified input supplies a spatial configuration, every completion of the ingress source
takes exactly the decoded rational position at every atom, pointwise. -/
theorem completion_conformation_of_present_spatial
    (certified : CertifiedAuthoritativeChemicalInput)
    (spatial : SpatialConfiguration) (observed : certified.input.spatial? = some spatial)
    {state : WholeState (Fin certified.input.molecule.atomCount) (Fin 0) (Fin 0)}
    (member : state ∈ completions (decode certified))
    (atom : Fin certified.input.molecule.atomCount) :
    state.conformation atom =
      (decodeSpatial spatial certified.input.molecule.atomCount
        (spatialFits_of_wf certified.input certified.structurallyWellFormed.2.1 spatial
          observed) atom).toEuclideanPoint := by
  have present : (decode certified).spatial? =
      some (decodeSpatial spatial certified.input.molecule.atomCount
        (spatialFits_of_wf certified.input certified.structurallyWellFormed.2.1 spatial
          observed)) := by
    rw [decode_spatial?]
    exact decodeSpatial?_some certified.input certified.structurallyWellFormed.2.1 spatial
      observed
  exact (completion_conformation_agrees (decode certified) member present atom).symm

end CertifiedAuthoritativeChemicalInput

/-! ## The zero-atom edge case

When the atom type is `Fin 0` there is exactly one possible conformation, so the completion set is a
subsingleton.  This is stated explicitly so that no two-distinct-configuration claim is ever made
for an empty atom carrier.  The general construction still has a (unique) completion, so it remains
nonempty. -/

/-- There is exactly one real conformation on an empty atom carrier. -/
theorem molecularConformation_fin_zero_subsingleton :
    Subsingleton (MolecularConformation (Fin 0)) :=
  ⟨fun first second => by
    funext atom
    exact Fin.elim0 atom⟩

/-- On an empty atom carrier the admissible-conformation set is still the whole (singleton) function
space; no position can be supplied at an atom because there are none. -/
theorem sourceConformations_fin_zero_eq_univ (source : OrganicFiniteSource (Fin 0)) :
    sourceConformations source = Set.univ := by
  ext conformation
  exact ⟨fun _ => Set.mem_univ conformation, fun _ => by
    intro positions present atom
    exact Fin.elim0 atom⟩

/-- The completion set on an empty atom carrier is a subsingleton.  In particular the construction
never asserts two distinct completions (or two distinct conformations) in that case. -/
theorem completions_fin_zero_subsingleton (source : OrganicFiniteSource (Fin 0)) :
    Subsingleton (completions source) := by
  refine ⟨fun first second => ?_⟩
  have hstate : first.1 = second.1 := by
    rcases first.2 with ⟨firstConformation, firstValid, hfirst⟩
    rcases second.2 with ⟨secondConformation, secondValid, hsecond⟩
    rw [← hfirst, ← hsecond]
    have hconf : firstConformation = secondConformation :=
      Subsingleton.elim _ _
    subst hconf
    apply WholeState.extEq <;> simp [defaultCompletion]
  exact Subtype.ext hstate

/-! ## Packaging as finite classical information -/

/-- Store the full joint completion set as `FiniteClassicalInformation`, keeping the caller-supplied
`ConfigurationKnowledge` tag as metadata only.  The joint set is exactly `completions source`; it is
not projected per channel and it is not replaced by a singleton. -/
def information (knowledge : ConfigurationKnowledge)
    (source : OrganicFiniteSource V) :
    FiniteClassicalInformation V (Fin 0) (Fin 0) :=
  FiniteClassicalInformation.ofStates knowledge (completions source)

@[simp] theorem information_knowledge (knowledge : ConfigurationKnowledge)
    (source : OrganicFiniteSource V) :
    (information knowledge source).knowledge = knowledge := rfl

@[simp] theorem information_possible (knowledge : ConfigurationKnowledge)
    (source : OrganicFiniteSource V) :
    (information knowledge source).possible = completions source := rfl

@[simp] theorem information_scopes (knowledge : ConfigurationKnowledge)
    (source : OrganicFiniteSource V) :
    (information knowledge source).scopes = [] := rfl

@[simp] theorem information_diagram? (knowledge : ConfigurationKnowledge)
    (source : OrganicFiniteSource V) :
    (information knowledge source).diagram? = none := rfl

/-- The arbitrary joint completion set is preserved verbatim; this is the general `ofStates`
projection, restated for the ingress packaging. -/
theorem information_possible_ofStates (knowledge : ConfigurationKnowledge)
    (possible : Set (WholeState V (Fin 0) (Fin 0))) :
    (FiniteClassicalInformation.ofStates knowledge possible).possible = possible := rfl

/-- Consistency of the packaged information is exactly mathematical nonemptiness of the completion
set.  It is proved from `completions_nonempty`; the knowledge tag never contributes a consistency
claim. -/
theorem information_consistent_iff (knowledge : ConfigurationKnowledge)
    (source : OrganicFiniteSource V) :
    (information knowledge source).Consistent ↔ (completions source).Nonempty := by
  rw [FiniteClassicalInformation.consistent_iff_possible_nonempty, information_possible]

/-- Every source therefore yields consistent packaged information, for any metadata tag. -/
theorem information_consistent (knowledge : ConfigurationKnowledge)
    (source : OrganicFiniteSource V) :
    (information knowledge source).Consistent :=
  (information_consistent_iff knowledge source).mpr (completions_nonempty source)

end

end TetraStereo.OneCenter
