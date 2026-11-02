import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoAuthoritativeInformationIngress
import TetraStereo.OneCenter.OrganicStereoCorrelatedInformation
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Function.Basic

set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace TetraStereo
namespace OneCenter

noncomputable section

universe u v w

/-!
# Sparse partial three-dimensional information over all compatible whole states

This module supplies the missing bridge between a *partial* three-dimensional observation and the
existing complete finite stereo state `WholeState`.

The central object is `compatibleStates graph K`, a filter (preimage) over the sigma
`FiniteState V = Σ p : ℕ, Σ b : ℕ, WholeState V (Fin p) (Fin b)` of **all** finite path counts,
**all** finite band counts and **all** channels of the existing whole-state record.  Only two
conditions are imposed:

* the state graph is the independently supplied graph, and
* the shared conformation belongs to the supplied conformation set `K`.

Every other channel — electronic inventory, rational provenance, role ledger, bond paths, band
families, drawing data, sparse partial positions, incidence ledger, fragments, conventions, cages,
residue ledger and frames — is unconstrained and remains part of the state.  The set is therefore
*not* the image of `defaultCompletion`.

`defaultCompletion` is used only as an explicit zero-family existence witness (path count `0`, band
count `0`).  The nonemptiness, projection and geometric results below are about the full compatible
set, not about that witness.

## Contents

* membership, coverage, conformation projection and nonemptiness of `compatibleStates`;
* the pointwise observed-value predicate `observationConformations`, the rational
  `CartesianPoint3` adapter, nonemptiness, exact observation recovery, injectivity on fully
  specified observations, variation of unknown coordinates, and the equivalence between
  simultaneous observation conflict and actual overlap disagreement;
* a concrete two-atom example with identical observed coordinates but different optional channels,
  both included in the compatible set and one excluded from the default-completion image;
* lifting of the existing `encodeDescription`/`decodeDescription` codec to the actual sigma,
  retaining the path and band counts, with exact round trips, injectivity, surjectivity and set
  inverse, together with compatibility recovery;
* `geometricCompatibleStates`, which additionally requires `PathGeometryValid`, and the exact
  conformation projection `{c ∈ K | Function.Injective c}` for the zero-path witness;
* a nondegenerate two-atom correlation witness `c 1 = c 0 + (1,0,0)` with full marginals, a proper
  subset of the product of its marginals, and distinct atom positions in every member;
* `assert_kernel_only` guards for the exported theorem endpoints.

## Scope boundaries

No chemical, physical or geometric realizability is claimed.  In particular a zero-path
`PathGeometryValid` state is *not* a statement of complete bond coverage; the theorem
`zeroPathGeometryValid_not_completeBondCoverage` makes that separation explicit.  Structural
existence of injective partial position extensions is intentionally not duplicated here; that is
the separate `c_partial_injective_position_extension` deliverable.  No new authority or multicenter
sidecar is introduced, and no default channel is presented as chemically selected.
-/

/-! ## Sparse observations and the independent partial input -/

/-- A sparse three-dimensional observation: every atom either carries an exact real point or no
coordinate at all.  Absence (`none`) is a genuine unknown, not the origin. -/
abbrev PartialCoordinateObservation (V : Type u) : Type u :=
  V → Option (EuclideanSpace ℝ (Fin 3))

/-- The independent partial three-dimensional input.  The interaction graph and the sparse point
observation are two independent channels over the same finite atom labels; the graph carries no
coordinate and the observation does not have to mention every atom. -/
structure PartialCoordinateInput (V : Type u) [DecidableEq V] [Fintype V] : Type u where
  /-- The independently specified finite atom-labelled interaction hypergraph. -/
  graph : FiniteAtomInteractionHypergraph V
  /-- The sparse point observation over the same atom labels. -/
  observation : PartialCoordinateObservation V

/-- The rational Cartesian-point adapter.  A sparse rational observation is mapped pointwise by
the existing exact rational-to-real embedding `CartesianPoint3.toEuclideanPoint`; absence stays
absence and no real value is approximated. -/
def rationalObservation {V : Type u} (positions : V → Option CartesianPoint3) :
    PartialCoordinateObservation V :=
  fun atom => (positions atom).map CartesianPoint3.toEuclideanPoint

/-- The rational adapter preserves absence exactly. -/
@[simp] theorem rationalObservation_none_iff {V : Type u}
    (positions : V → Option CartesianPoint3) (atom : V) :
    rationalObservation positions atom = none ↔ positions atom = none := by
  unfold rationalObservation
  cases positions atom <;> simp

/-- The rational adapter exposes exactly the supplied rational point, mapped by the exact
embedding. -/
theorem rationalObservation_some_iff {V : Type u}
    (positions : V → Option CartesianPoint3) (atom : V)
    (value : EuclideanSpace ℝ (Fin 3)) :
    rationalObservation positions atom = some value ↔
      ∃ point : CartesianPoint3, positions atom = some point ∧
        point.toEuclideanPoint = value := by
  unfold rationalObservation
  cases positions atom <;> simp

/-- A supplied rational point is observed at its exact real embedding. -/
theorem rationalObservation_eq_some_toEuclideanPoint {V : Type u}
    (positions : V → Option CartesianPoint3) (atom : V) (point : CartesianPoint3)
    (present : positions atom = some point) :
    rationalObservation positions atom = some point.toEuclideanPoint := by
  simp [rationalObservation, present]

/-- The independent partial input obtained from a graph and a sparse rational observation. -/
def PartialCoordinateInput.ofRational {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (positions : V → Option CartesianPoint3) :
    PartialCoordinateInput V :=
  { graph := graph, observation := rationalObservation positions }

/-- The coordinate constraint set of a sparse observation: the explicit pointwise predicate that
the conformation takes the observed value at every observed atom.  Unobserved atoms are
unconstrained. -/
def observationConformations {V : Type u}
    (observation : PartialCoordinateObservation V) : Set (MolecularConformation V) :=
  { conformation | ∀ atom value, observation atom = some value → conformation atom = value }

/-- Membership in `observationConformations` is exactly the pointwise observed-value condition. -/
@[simp] theorem mem_observationConformations_iff {V : Type u}
    (observation : PartialCoordinateObservation V)
    (conformation : MolecularConformation V) :
    conformation ∈ observationConformations observation ↔
      ∀ atom value, observation atom = some value → conformation atom = value :=
  Iff.rfl

/-- The rational adapter's constraint set is exactly the pointwise rational equality. -/
theorem rational_observationConformations_iff {V : Type u}
    (positions : V → Option CartesianPoint3) (conformation : MolecularConformation V) :
    conformation ∈ observationConformations (rationalObservation positions) ↔
      ∀ atom point, positions atom = some point →
        conformation atom = point.toEuclideanPoint := by
  constructor
  · intro member atom point present
    exact member atom point.toEuclideanPoint
      (rationalObservation_eq_some_toEuclideanPoint positions atom point present)
  · intro member atom value observed
    obtain ⟨point, present, valueEq⟩ :=
      (rationalObservation_some_iff positions atom value).mp observed
    rw [member atom point present, valueEq]

/-! ## The full finite-state sigma and the compatible-state filter -/

/-- The complete family of finite whole states.  The natural numbers `p` and `b` are retained
literally: `FiniteState` ranges over every finite path count and every finite band count, with all
`WholeState` channels present. -/
abbrev FiniteState (V : Type u) [DecidableEq V] [Fintype V] :=
  Sigma fun p : ℕ => Sigma fun b : ℕ => WholeState V (Fin p) (Fin b)

/-- The compatible whole states of a graph and a conformation set.

This is a filter/preimage over the whole sigma of all finite path and band counts and all channels.
It constrains only the graph and the shared conformation; no other channel is fixed and the set is
not the image of `defaultCompletion`. -/
def compatibleStates {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V)) :
    Set (FiniteState V) :=
  { state | state.2.2.graph = graph ∧ state.2.2.conformation ∈ K }

/-- Direct membership: an arbitrary whole state belongs exactly when its graph is the supplied
graph and its shared conformation belongs to the supplied conformation set.  Nothing is said about
the path count, the band count or any other channel. -/
@[simp] theorem mem_compatibleStates_iff {V : Type u} [DecidableEq V] [Fintype V]
    {graph : FiniteAtomInteractionHypergraph V} {K : Set (MolecularConformation V)}
    (state : FiniteState V) :
    state ∈ compatibleStates graph K ↔
      state.2.2.graph = graph ∧ state.2.2.conformation ∈ K :=
  Iff.rfl

/-- Coverage of every actually compatible whole state, independent of all other channels. -/
theorem compatibleStates_coverage {V : Type u} [DecidableEq V] [Fintype V]
    {graph : FiniteAtomInteractionHypergraph V} {K : Set (MolecularConformation V)}
    (state : FiniteState V)
    (graphEq : state.2.2.graph = graph)
    (conformationMem : state.2.2.conformation ∈ K) :
    state ∈ compatibleStates graph K :=
  ⟨graphEq, conformationMem⟩

/-- Two whole states that agree on the graph and on the shared conformation are either both
compatible or both incompatible, regardless of every other channel. -/
theorem compatibleStates_other_channels_irrelevant {V : Type u} [DecidableEq V] [Fintype V]
    {graph : FiniteAtomInteractionHypergraph V} {K : Set (MolecularConformation V)}
    {state other : FiniteState V}
    (member : state ∈ compatibleStates graph K)
    (sameGraph : other.2.2.graph = graph)
    (sameConformation : other.2.2.conformation = state.2.2.conformation) :
    other ∈ compatibleStates graph K := by
  rw [mem_compatibleStates_iff] at member ⊢
  refine ⟨sameGraph, ?_⟩
  rw [sameConformation]
  exact member.2

/-- The conformation projection of a set of whole states. -/
def conformationProjection {V : Type u} [DecidableEq V] [Fintype V]
    (states : Set (FiniteState V)) : Set (MolecularConformation V) :=
  { conformation | ∃ state ∈ states, state.2.2.conformation = conformation }

/-! ## The zero-family witness obtained from the existing `defaultCompletion` -/

/-- The canonical independent source of a graph, with both optional evidence channels absent. -/
def sourceOfGraph {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) : OrganicFiniteSource V where
  graph := graph
  spatial? := none
  diagram? := none

@[simp] theorem sourceOfGraph_graph {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) :
    (sourceOfGraph graph).graph = graph := rfl

/-- The existing `defaultCompletion` as a whole state with zero paths and zero bands.  This is the
only place the default completion is used: as an explicit existence witness, never as a definition
of the compatible-state set. -/
def defaultFiniteState {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (conformation : MolecularConformation V) :
    FiniteState V :=
  ⟨0, 0, defaultCompletion (sourceOfGraph graph) conformation
    (mem_sourceConformations_of_absent (sourceOfGraph graph) rfl conformation)⟩

@[simp] theorem defaultFiniteState_graph {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (conformation : MolecularConformation V) :
    (defaultFiniteState graph conformation).2.2.graph = graph := rfl

@[simp] theorem defaultFiniteState_conformation {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (conformation : MolecularConformation V) :
    (defaultFiniteState graph conformation).2.2.conformation = conformation := rfl

@[simp] theorem defaultFiniteState_diagramPartial? {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (conformation : MolecularConformation V) :
    (defaultFiniteState graph conformation).2.2.diagramPartial? = none := rfl

/-- The same zero-family witness with a present sparse partial-position channel.  The channel is
unconstrained by `WholeState`, so this is a genuine whole state; it is used to expose that the
default-completion image is strictly smaller than the compatible set. -/
def presentPartialFiniteState {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (conformation : MolecularConformation V)
    (positions : SourcePartialPositions V) : FiniteState V :=
  ⟨0, 0, { defaultCompletion (sourceOfGraph graph) conformation
      (mem_sourceConformations_of_absent (sourceOfGraph graph) rfl conformation) with
      diagramPartial? := some positions }⟩

@[simp] theorem presentPartialFiniteState_graph {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (conformation : MolecularConformation V)
    (positions : SourcePartialPositions V) :
    (presentPartialFiniteState graph conformation positions).2.2.graph = graph := rfl

@[simp] theorem presentPartialFiniteState_conformation {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (conformation : MolecularConformation V)
    (positions : SourcePartialPositions V) :
    (presentPartialFiniteState graph conformation positions).2.2.conformation = conformation := rfl

@[simp] theorem presentPartialFiniteState_diagramPartial? {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (conformation : MolecularConformation V)
    (positions : SourcePartialPositions V) :
    (presentPartialFiniteState graph conformation positions).2.2.diagramPartial? =
      some positions := rfl

/-- The default-completion image at a graph: the whole states that are the zero-family default
witness of some conformation.  This is recorded only to compare the default image with the full
compatible set. -/
def defaultCompletionImage {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) : Set (FiniteState V) :=
  { state | ∃ conformation : MolecularConformation V,
      defaultFiniteState graph conformation = state }

/-! ## Projection and nonemptiness of the compatible-state filter -/

/-- The shared-conformation projection of the compatible states is exactly `K`. -/
theorem conformationProjection_compatibleStates {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V)) :
    conformationProjection (compatibleStates graph K) = K := by
  ext conformation
  constructor
  · rintro ⟨state, member, conformationEq⟩
    rw [mem_compatibleStates_iff] at member
    rw [← conformationEq]
    exact member.2
  · intro conformationMem
    exact ⟨defaultFiniteState graph conformation,
      ⟨defaultFiniteState_graph graph conformation, conformationMem⟩,
      defaultFiniteState_conformation graph conformation⟩

/-- The compatible set is nonempty exactly when the conformation set is nonempty.  The forward
direction reads the shared conformation of any member; the reverse direction uses the zero-family
`defaultCompletion` witness. -/
theorem compatibleStates_nonempty_iff {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V)) :
    (compatibleStates graph K).Nonempty ↔ K.Nonempty := by
  constructor
  · rintro ⟨state, member⟩
    rw [mem_compatibleStates_iff] at member
    exact ⟨state.2.2.conformation, member.2⟩
  · rintro ⟨conformation, conformationMem⟩
    exact ⟨defaultFiniteState graph conformation,
      ⟨defaultFiniteState_graph graph conformation, conformationMem⟩⟩

/-! ## Partial observations: consistency, recovery, variation and conflict -/

/-- The canonical conformation of a sparse observation: observed atoms take their observed value,
unobserved atoms take the origin as **one** nonemptiness witness.  This is not a semantic
identification of unknown coordinates with zero. -/
def canonicalConformationOfObservation {V : Type u}
    (observation : PartialCoordinateObservation V) : MolecularConformation V :=
  fun atom =>
    match observation atom with
    | none => 0
    | some value => value

/-- The canonical conformation satisfies every observed value. -/
theorem canonicalConformationOfObservation_mem {V : Type u}
    (observation : PartialCoordinateObservation V) :
    canonicalConformationOfObservation observation ∈
      observationConformations observation := by
  intro atom value observed
  simp [canonicalConformationOfObservation, observed]

/-- Every sparse observation admits at least one conformation: coordinate consistency alone, with
no constraint relating distinct atoms, distances, bonds or any other channel. -/
theorem observationConformations_nonempty {V : Type u}
    (observation : PartialCoordinateObservation V) :
    (observationConformations observation).Nonempty :=
  ⟨canonicalConformationOfObservation observation,
    canonicalConformationOfObservation_mem observation⟩

/-- Every graph together with a sparse observation has a nonempty compatible whole-state set. -/
theorem compatibleStates_observation_nonempty {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V)
    (observation : PartialCoordinateObservation V) :
    (compatibleStates graph (observationConformations observation)).Nonempty :=
  (compatibleStates_nonempty_iff graph (observationConformations observation)).mpr
    (observationConformations_nonempty observation)

/-- The realized full observation of a conformation. -/
def realizedObservation {V : Type u} (conformation : MolecularConformation V) :
    PartialCoordinateObservation V :=
  fun atom => some (conformation atom)

/-- Realizing a full observation from a conformation is injective. -/
theorem realizedObservation_injective {V : Type u} :
    Function.Injective (realizedObservation (V := V)) := by
  intro first second equal
  funext atom
  have coordinateEq := congrFun equal atom
  simpa [realizedObservation] using coordinateEq

/-- Exact source-observation recovery: every observed value of the source is realized by every
conformation in the constraint set. -/
theorem realizedObservation_recovers {V : Type u}
    {observation : PartialCoordinateObservation V}
    {conformation : MolecularConformation V}
    (member : conformation ∈ observationConformations observation) :
    ∀ atom value, observation atom = some value →
      realizedObservation conformation atom = some value := by
  intro atom value observed
  simp [realizedObservation, member atom value observed]

/-- On every atom that the source actually observes, the realized observation equals the source
observation. -/
theorem observation_recovery_on_observed {V : Type u}
    {observation : PartialCoordinateObservation V}
    {conformation : MolecularConformation V}
    (member : conformation ∈ observationConformations observation) :
    ∀ atom, observation atom ≠ none →
      realizedObservation conformation atom = observation atom := by
  intro atom present
  cases observed : observation atom with
  | none => exact absurd observed present
  | some value => simp [realizedObservation, member atom value observed]

/-- A fully specified observation fixes the conformation uniquely.  This is a statement about the
conformation channel only; it does not assert equality of whole states. -/
theorem observationConformations_subsingleton_of_fullySpecified {V : Type u}
    {observation : PartialCoordinateObservation V}
    (full : ∀ atom, observation atom ≠ none) :
    (observationConformations observation).Subsingleton := by
  intro first firstMember second secondMember
  funext atom
  cases observed : observation atom with
  | none => exact absurd observed (full atom)
  | some value =>
      rw [firstMember atom value observed, secondMember atom value observed]

/-- An unknown coordinate can take any value: if the source does not observe `atom`, then every
point occurs as that atom's position in some member of the constraint set. -/
theorem unknownCoordinate_vary {V : Type u} [DecidableEq V]
    {observation : PartialCoordinateObservation V} {atom : V}
    (unknown : observation atom = none) (value : EuclideanSpace ℝ (Fin 3)) :
    ∃ conformation ∈ observationConformations observation, conformation atom = value := by
  refine ⟨Function.update (canonicalConformationOfObservation observation) atom value, ?_, ?_⟩
  · intro other otherValue observedOther
    by_cases equal : other = atom
    · subst equal
      rw [unknown] at observedOther
      cases observedOther
    · rw [Function.update_of_ne equal]
      exact canonicalConformationOfObservation_mem observation other otherValue observedOther
  · exact Function.update_self atom value (canonicalConformationOfObservation observation)

/-- Two sparse observations agree on their overlap when every atom observed by both is assigned
the same point by both. -/
def OverlapAgrees {V : Type u} (first second : PartialCoordinateObservation V) : Prop :=
  ∀ atom (firstValue secondValue : EuclideanSpace ℝ (Fin 3)),
    first atom = some firstValue → second atom = some secondValue →
      firstValue = secondValue

/-- Simultaneous observation conflict is the negation of overlap agreement. -/
def ObservationsConflict {V : Type u} (first second : PartialCoordinateObservation V) : Prop :=
  ¬ OverlapAgrees first second

/-- Combine two sparse observations by giving the first channel priority; at atoms where the first
channel is absent the second channel is used. -/
def combineObservations {V : Type u} (first second : PartialCoordinateObservation V) :
    PartialCoordinateObservation V :=
  fun atom =>
    match first atom with
    | some value => some value
    | none => second atom

/-- If two observations agree on their overlap, the combined observation refines both constraint
sets simultaneously. -/
theorem observationConformations_combine_subset {V : Type u}
    {first second : PartialCoordinateObservation V}
    (agrees : OverlapAgrees first second) :
    observationConformations (combineObservations first second) ⊆
      observationConformations first ∩ observationConformations second := by
  intro conformation member
  constructor
  · intro atom value observed
    have combined : combineObservations first second atom = some value := by
      simp [combineObservations, observed]
    exact member atom value combined
  · intro atom value observed
    cases firstObserved : first atom with
    | some firstValue =>
        have combined : combineObservations first second atom = some firstValue := by
          simp [combineObservations, firstObserved]
        have conformationValue : conformation atom = firstValue :=
          member atom firstValue combined
        have valuesEqual : firstValue = value :=
          agrees atom firstValue value firstObserved observed
        rw [conformationValue, valuesEqual]
    | none =>
        have combined : combineObservations first second atom = some value := by
          simp [combineObservations, firstObserved, observed]
        exact member atom value combined

/-- **Simultaneous observation consistency**: the intersection of the two constraint sets is
nonempty exactly when the two observations agree on their actual overlap. -/
theorem observationConformations_inter_nonempty_iff {V : Type u}
    (first second : PartialCoordinateObservation V) :
    ((observationConformations first) ∩ (observationConformations second)).Nonempty ↔
      OverlapAgrees first second := by
  constructor
  · rintro ⟨conformation, member⟩
    obtain ⟨memberFirst, memberSecond⟩ := member
    intro atom firstValue secondValue firstObserved secondObserved
    exact (memberFirst atom firstValue firstObserved).symm.trans
      (memberSecond atom secondValue secondObserved)
  · intro agrees
    obtain ⟨conformation, member⟩ :=
      observationConformations_nonempty (combineObservations first second)
    exact ⟨conformation, observationConformations_combine_subset agrees member⟩

/-- **Simultaneous observation conflict**: the two constraint sets have empty intersection exactly
when the observations conflict. -/
theorem observationConformations_inter_eq_empty_iff_conflict {V : Type u}
    (first second : PartialCoordinateObservation V) :
    (observationConformations first ∩ observationConformations second) = ∅ ↔
      ObservationsConflict first second := by
  rw [ObservationsConflict, ← observationConformations_inter_nonempty_iff]
  constructor
  · intro empty nonempty
    rw [empty] at nonempty
    rcases nonempty with ⟨conformation, member⟩
    simp at member
  · intro notNonempty
    ext conformation
    constructor
    · intro member
      exact absurd ⟨conformation, member⟩ notNonempty
    · intro member
      simp at member

/-- Conflict is exactly the existence of an atom observed by both channels with different values:
the actual overlap disagreement. -/
theorem observationsConflict_iff_exists_overlap_disagreement {V : Type u}
    (first second : PartialCoordinateObservation V) :
    ObservationsConflict first second ↔
      ∃ atom : V, ∃ firstValue secondValue : EuclideanSpace ℝ (Fin 3),
        first atom = some firstValue ∧ second atom = some secondValue ∧
          firstValue ≠ secondValue := by
  unfold ObservationsConflict OverlapAgrees
  constructor
  · intro conflict
    by_contra noDisagreement
    apply conflict
    intro atom firstValue secondValue firstObserved secondObserved
    by_contra valuesDifferent
    exact noDisagreement ⟨atom, firstValue, secondValue, firstObserved, secondObserved,
      valuesDifferent⟩
  · rintro ⟨atom, firstValue, secondValue, firstObserved, secondObserved, valuesDifferent⟩
    intro agrees
    exact valuesDifferent (agrees atom firstValue secondValue firstObserved secondObserved)

/-- The optional sparse partial-position channel of a finite whole state. -/
def finiteStateDiagramPartial? {V : Type u} [DecidableEq V] [Fintype V]
    (state : FiniteState V) : Option (SourcePartialPositions V) :=
  state.2.2.diagramPartial?

/-- The default witness and the present-partial witness are distinct whole states because their
optional partial-position channels differ (`none` versus `some`). -/
theorem defaultFiniteState_ne_presentPartialFiniteState {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (conformation : MolecularConformation V)
    (positions : SourcePartialPositions V) :
    defaultFiniteState graph conformation ≠
      presentPartialFiniteState graph conformation positions := by
  intro equal
  have channel : (defaultFiniteState graph conformation).2.2.diagramPartial? =
      (presentPartialFiniteState graph conformation positions).2.2.diagramPartial? :=
    congrArg (fun state : FiniteState V => state.2.2.diagramPartial?) equal
  rw [defaultFiniteState_diagramPartial? graph conformation,
    presentPartialFiniteState_diagramPartial? graph conformation positions] at channel
  cases channel

/-- A present-partial witness is never in the default-completion image at the same graph: every
default image member has `diagramPartial? = none`, while the witness has `some positions`. -/
theorem presentPartialFiniteState_not_defaultImage {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (conformation : MolecularConformation V)
    (positions : SourcePartialPositions V) :
    presentPartialFiniteState graph conformation positions ∉
      defaultCompletionImage graph := by
  rintro ⟨other, equal⟩
  have channel : (defaultFiniteState graph other).2.2.diagramPartial? =
      (presentPartialFiniteState graph conformation positions).2.2.diagramPartial? :=
    congrArg (fun state : FiniteState V => state.2.2.diagramPartial?) equal
  rw [defaultFiniteState_diagramPartial? graph other,
    presentPartialFiniteState_diagramPartial? graph conformation positions] at channel
  cases channel

/-- Fully specified coordinates determine the conformation but not the whole state.  The two
witnesses below have the same conformation and the same graph yet differ in the optional sparse
partial-position channel; both are compatible. -/
theorem fullySpecified_conformation_only {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V)
    (observation : PartialCoordinateObservation V)
    (conformation : MolecularConformation V)
    (member : conformation ∈ observationConformations observation) :
    ∃ first second : FiniteState V,
      first ∈ compatibleStates graph (observationConformations observation) ∧
      second ∈ compatibleStates graph (observationConformations observation) ∧
      first.2.2.conformation = second.2.2.conformation ∧ first ≠ second := by
  let positions : SourcePartialPositions V := { positions := fun _ => none }
  refine ⟨defaultFiniteState graph conformation,
    presentPartialFiniteState graph conformation positions, ?_, ?_, ?_, ?_⟩
  · exact ⟨defaultFiniteState_graph graph conformation, member⟩
  · exact ⟨presentPartialFiniteState_graph graph conformation positions, member⟩
  · rw [defaultFiniteState_conformation, presentPartialFiniteState_conformation]
  · intro equal
    exact defaultFiniteState_ne_presentPartialFiniteState graph conformation positions equal

/-! ## Lifting the existing description codec to the whole-state sigma -/

/-- The encoded sigma of finite whole states.  The natural path and band counts are retained
literally; only the index types are transported to `Fin (Fintype.card _)`, exactly the form
required by the existing `encodeDescription`/`decodeDescription` codec. -/
abbrev EncodedFiniteState (V : Type u) [Fintype V] :=
  Sigma fun p : ℕ => Sigma fun b : ℕ =>
    WholeState (Fin (Fintype.card V))
      (Fin (Fintype.card (Fin p))) (Fin (Fintype.card (Fin b)))

/-- The whole-state graph of a description is the relabelled graph. -/
@[simp] theorem relabelWholeState_graph {V W E B : Type u} [DecidableEq V] [Fintype V]
    [DecidableEq W] [Fintype W] [Fintype E] [Fintype B]
    (equivalence : V ≃ W) (state : WholeState V E B) :
    (relabelWholeState equivalence state).graph = relabelGraph equivalence state.graph := rfl

/-- The whole-state conformation of a description is the reindexed conformation. -/
@[simp] theorem relabelWholeState_conformation {V W E B : Type u} [DecidableEq V] [Fintype V]
    [DecidableEq W] [Fintype W] [Fintype E] [Fintype B]
    (equivalence : V ≃ W) (state : WholeState V E B) :
    (relabelWholeState equivalence state).conformation =
      MolecularConformation.reindex equivalence state.conformation := rfl

/-- Edge reindexing leaves the graph unchanged. -/
@[simp] theorem reindexEdges_graph {V E E' B : Type u} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype E'] [Fintype B]
    (equivalence : E ≃ E') (state : WholeState V E B) :
    (reindexEdges equivalence state).graph = state.graph := rfl

/-- Edge reindexing leaves the conformation unchanged. -/
@[simp] theorem reindexEdges_conformation {V E E' B : Type u} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype E'] [Fintype B]
    (equivalence : E ≃ E') (state : WholeState V E B) :
    (reindexEdges equivalence state).conformation = state.conformation := rfl

/-- Band reindexing leaves the graph unchanged. -/
@[simp] theorem reindexBands_graph {V E B B' : Type u} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] [Fintype B']
    (equivalence : B ≃ B') (state : WholeState V E B) :
    (reindexBands equivalence state).graph = state.graph := rfl

/-- Band reindexing leaves the conformation unchanged. -/
@[simp] theorem reindexBands_conformation {V E B B' : Type u} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] [Fintype B']
    (equivalence : B ≃ B') (state : WholeState V E B) :
    (reindexBands equivalence state).conformation = state.conformation := rfl

/-- The existing encoding exposes the relabelled graph. -/
theorem encodeDescription_graph {V E B : Type u} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B]
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (description : WholeState V E B) :
    (encodeDescription eV eE eB description).graph =
      relabelGraph eV description.graph := rfl

/-- The existing encoding exposes the reindexed conformation. -/
theorem encodeDescription_conformation {V E B : Type u} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B]
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B)) (description : WholeState V E B) :
    (encodeDescription eV eE eB description).conformation =
      MolecularConformation.reindex eV description.conformation := rfl

/-- The existing decoding exposes the inversely relabelled graph. -/
theorem decodeDescription_graph {V E B : Type u} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B]
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (encoded : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :
    (decodeDescription eV eE eB encoded).graph = relabelGraph eV.symm encoded.graph := rfl

/-- The existing decoding exposes the inversely reindexed conformation. -/
theorem decodeDescription_conformation {V E B : Type u} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B]
    (eV : V ≃ Fin (Fintype.card V)) (eE : E ≃ Fin (Fintype.card E))
    (eB : B ≃ Fin (Fintype.card B))
    (encoded : EncodedDescription (Fintype.card V) (Fintype.card E) (Fintype.card B)) :
    (decodeDescription eV eE eB encoded).conformation =
      MolecularConformation.reindex eV.symm encoded.conformation := rfl

/-- Encode a whole state sigma, retaining the path count and the band count literally and using
the existing description codec only on the inner record. -/
noncomputable def encodeFiniteState {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) (state : FiniteState V) :
    EncodedFiniteState V :=
  ⟨state.1, state.2.1,
    encodeDescription enumerate (Fintype.equivFin (Fin state.1))
      (Fintype.equivFin (Fin state.2.1)) state.2.2⟩

/-- Decode a whole state sigma using the existing concrete inverse codec.  Only the enumeration and
the encoded payload are used; the path and band counts are read from the encoded sigma. -/
noncomputable def decodeFiniteState {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) (state : EncodedFiniteState V) :
    FiniteState V :=
  ⟨state.1, state.2.1,
    decodeDescription enumerate (Fintype.equivFin (Fin state.1))
      (Fintype.equivFin (Fin state.2.1)) state.2.2⟩

/-- Decoding an encoded whole state recovers it exactly, including its path and band counts. -/
theorem decodeFiniteState_encodeFiniteState {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) (state : FiniteState V) :
    decodeFiniteState enumerate (encodeFiniteState enumerate state) = state := by
  obtain ⟨p, b, description⟩ := state
  simp [decodeFiniteState, encodeFiniteState, decodeDescription_encodeDescription]

/-- Encoding a decoded whole state recovers it exactly. -/
theorem encodeFiniteState_decodeFiniteState {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) (state : EncodedFiniteState V) :
    encodeFiniteState enumerate (decodeFiniteState enumerate state) = state := by
  obtain ⟨p, b, description⟩ := state
  simp [decodeFiniteState, encodeFiniteState, encodeDescription_decodeDescription]

/-- The lifted encoder is injective. -/
theorem encodeFiniteState_injective {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) :
    Function.Injective (encodeFiniteState (V := V) enumerate) := by
  intro first second equal
  calc
    first = decodeFiniteState enumerate (encodeFiniteState enumerate first) :=
      (decodeFiniteState_encodeFiniteState enumerate first).symm
    _ = decodeFiniteState enumerate (encodeFiniteState enumerate second) := by rw [equal]
    _ = second := decodeFiniteState_encodeFiniteState enumerate second

/-- The lifted encoder is surjective. -/
theorem encodeFiniteState_surjective {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) :
    Function.Surjective (encodeFiniteState (V := V) enumerate) :=
  fun encoded => ⟨decodeFiniteState enumerate encoded,
    encodeFiniteState_decodeFiniteState enumerate encoded⟩

/-- Encoding exposes the relabelled graph of the underlying whole state. -/
@[simp] theorem encodeFiniteState_graph {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) (state : FiniteState V) :
    (encodeFiniteState enumerate state).2.2.graph =
      relabelGraph enumerate state.2.2.graph := rfl

/-- Encoding exposes the reindexed conformation of the underlying whole state. -/
@[simp] theorem encodeFiniteState_conformation {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) (state : FiniteState V) :
    (encodeFiniteState enumerate state).2.2.conformation =
      MolecularConformation.reindex enumerate state.2.2.conformation := rfl

/-- Decoding exposes the inversely relabelled graph of the underlying whole state. -/
@[simp] theorem decodeFiniteState_graph {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) (state : EncodedFiniteState V) :
    (decodeFiniteState enumerate state).2.2.graph =
      relabelGraph enumerate.symm state.2.2.graph := rfl

/-- Decoding exposes the inversely reindexed conformation of the underlying whole state. -/
@[simp] theorem decodeFiniteState_conformation {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) (state : EncodedFiniteState V) :
    (decodeFiniteState enumerate state).2.2.conformation =
      MolecularConformation.reindex enumerate.symm state.2.2.conformation := rfl

/-- The image of a set of whole states under the lifted encoder. -/
def encodeFiniteStateSet {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) (states : Set (FiniteState V)) :
    Set (EncodedFiniteState V) :=
  { encoded | ∃ state ∈ states, encodeFiniteState enumerate state = encoded }

/-- The image of a set of encoded whole states under the lifted decoder. -/
def decodeFiniteStateSet {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) (states : Set (EncodedFiniteState V)) :
    Set (FiniteState V) :=
  { state | ∃ encoded ∈ states, decodeFiniteState enumerate encoded = state }

/-- Membership in the encoded image. -/
@[simp] theorem mem_encodeFiniteStateSet_iff {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) {states : Set (FiniteState V)}
    {encoded : EncodedFiniteState V} :
    encoded ∈ encodeFiniteStateSet enumerate states ↔
      ∃ state ∈ states, encodeFiniteState enumerate state = encoded :=
  Iff.rfl

/-- Membership in the decoded image. -/
@[simp] theorem mem_decodeFiniteStateSet_iff {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) {states : Set (EncodedFiniteState V)}
    {state : FiniteState V} :
    state ∈ decodeFiniteStateSet enumerate states ↔
      ∃ encoded ∈ states, decodeFiniteState enumerate encoded = state :=
  Iff.rfl

/-- Set inversion: decoding the encoded image of a set of whole states recovers the set exactly. -/
theorem decodeFiniteStateSet_encodeFiniteStateSet {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) (states : Set (FiniteState V)) :
    decodeFiniteStateSet enumerate (encodeFiniteStateSet enumerate states) = states := by
  ext state
  constructor
  · rintro ⟨encoded, ⟨original, originalMember, encodedEq⟩, stateEq⟩
    have stateOriginal : state = original := by
      rw [← stateEq, ← encodedEq, decodeFiniteState_encodeFiniteState]
    rw [stateOriginal]
    exact originalMember
  · intro stateMember
    exact ⟨encodeFiniteState enumerate state, ⟨state, stateMember, rfl⟩,
      decodeFiniteState_encodeFiniteState enumerate state⟩

/-- The opposite set inversion: encoding the decoded image of a set of encoded states recovers the
set exactly. -/
theorem encodeFiniteStateSet_decodeFiniteStateSet {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) (states : Set (EncodedFiniteState V)) :
    encodeFiniteStateSet enumerate (decodeFiniteStateSet enumerate states) = states := by
  ext encoded
  constructor
  · rintro ⟨state, ⟨original, originalMember, stateEq⟩, encodedEq⟩
    have encodedOriginal : encoded = original := by
      rw [← encodedEq, ← stateEq, encodeFiniteState_decodeFiniteState]
    rw [encodedOriginal]
    exact originalMember
  · intro encodedMember
    exact ⟨decodeFiniteState enumerate encoded, ⟨encoded, encodedMember, rfl⟩,
      encodeFiniteState_decodeFiniteState enumerate encoded⟩

/-- The encoded compatible-state set. -/
def encodedCompatibleStates {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V)) :
    Set (EncodedFiniteState V) :=
  encodeFiniteStateSet enumerate (compatibleStates graph K)

/-- Compatibility recovery: decoding an encoded state lands in the compatible set exactly when
that encoded state belongs to the encoded compatible set. -/
theorem decodeFiniteState_mem_compatibleStates_iff {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V))
    (encoded : EncodedFiniteState V) :
    decodeFiniteState enumerate encoded ∈ compatibleStates graph K ↔
      encoded ∈ encodedCompatibleStates enumerate graph K := by
  constructor
  · intro member
    exact ⟨decodeFiniteState enumerate encoded, member,
      encodeFiniteState_decodeFiniteState enumerate encoded⟩
  · rintro ⟨state, member, encodedEq⟩
    rw [← encodedEq, decodeFiniteState_encodeFiniteState]
    exact member

/-- Set-level compatibility recovery through the concrete existing inverse. -/
theorem decodeFiniteStateSet_encodedCompatibleStates {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V)) :
    decodeFiniteStateSet enumerate (encodedCompatibleStates enumerate graph K) =
      compatibleStates graph K :=
  decodeFiniteStateSet_encodeFiniteStateSet enumerate (compatibleStates graph K)

/-! ## Geometric compatible states and the zero-path boundary -/

/-- The geometric predicate at explicit path and band counts.  The explicit `p` and `b` let Lean
infer the index types of the existing `PathGeometryValid` structure without projecting them out of
the sigma. -/
def geometricWholeState {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V))
    (p b : ℕ) (state : WholeState V (Fin p) (Fin b)) : Prop :=
  state.graph = graph ∧ state.conformation ∈ K ∧ PathGeometryValid state

/-- Geometric compatible states: compatible whole states that additionally satisfy the existing
`PathGeometryValid` non-degeneracy hypotheses of the whole path channel. -/
def geometricCompatibleStates {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V)) :
    Set (FiniteState V) :=
  { state | geometricWholeState graph K state.1 state.2.1 state.2.2 }

/-- The zero-family `defaultCompletion` witness satisfies `PathGeometryValid` exactly when its
shared conformation is injective: the path-indexed laws are vacuous over `Fin 0`. -/
theorem defaultFiniteState_pathGeometryValid {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (conformation : MolecularConformation V)
    (injective : Function.Injective conformation) :
    PathGeometryValid ((defaultFiniteState graph conformation).2.2 :
      WholeState V (Fin 0) (Fin 0)) := by
  refine ⟨?_, injective, ?_, ?_, ?_⟩
  · intro edge
    exact Fin.elim0 edge
  · intro edge
    exact Fin.elim0 edge
  · intro edge parameter _ _ atom
    exact Fin.elim0 edge
  · intro edge other parameter otherParameter _ _
    exact Fin.elim0 edge

/-- The conformation projection of the geometric compatible set is exactly the set of injective
conformations in `K`.  The reverse direction uses the zero-path witness; the forward direction
reads `PathGeometryValid.atom_injective` from the state. -/
theorem conformationProjection_geometricCompatibleStates {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (K : Set (MolecularConformation V)) :
    conformationProjection (geometricCompatibleStates graph K) =
      { conformation | conformation ∈ K ∧ Function.Injective conformation } := by
  ext conformation
  constructor
  · rintro ⟨state, member, conformationEq⟩
    simp only [geometricCompatibleStates, geometricWholeState] at member
    obtain ⟨graphEq, conformationMem, valid⟩ := member
    refine ⟨?_, ?_⟩
    · rw [← conformationEq]
      exact conformationMem
    · rw [← conformationEq]
      exact valid.atom_injective
  · rintro ⟨conformationMem, injective⟩
    refine ⟨defaultFiniteState graph conformation, ?_,
      defaultFiniteState_conformation graph conformation⟩
    exact ⟨defaultFiniteState_graph graph conformation, conformationMem,
      defaultFiniteState_pathGeometryValid graph conformation injective⟩

/-- Complete bond coverage of a whole state: every source interaction occurrence is named by at
least one finite bond-path edge.  This is a genuine coverage predicate, distinct from the
non-degeneracy fields of `PathGeometryValid`. -/
def PathCoversAllInteractions {V : Type u} {E : Type v} {B : Type w} [DecidableEq V] [Fintype V]
    [Fintype E] [Fintype B] (state : WholeState V E B) : Prop :=
  ∀ index : Fin state.graph.interactions.length,
    ∃ edge : E, (state.paths edge).interactionIndex = index.val

/-- Zero-path `PathGeometryValid` is **not** complete bond coverage.  With a zero path family the
geometry laws are vacuous, while a nontrivial interaction occurrence remains uncovered.  This keeps
the zero-family witness from being misread as a physical bond-realization claim. -/
theorem zeroPathGeometryValid_not_completeBondCoverage {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (conformation : MolecularConformation V)
    (injective : Function.Injective conformation)
    (index : Fin graph.interactions.length) :
    PathGeometryValid ((defaultFiniteState graph conformation).2.2 :
        WholeState V (Fin 0) (Fin 0)) ∧
      ¬ PathCoversAllInteractions ((defaultFiniteState graph conformation).2.2 :
        WholeState V (Fin 0) (Fin 0)) := by
  refine ⟨defaultFiniteState_pathGeometryValid graph conformation injective, ?_⟩
  intro covers
  obtain ⟨edge, _⟩ := covers index
  exact Fin.elim0 edge

/-! ## A nondegenerate two-atom correlation witness -/

/-- The unit displacement along the first coordinate of real three-space. -/
def correlationDisplacement : EuclideanSpace ℝ (Fin 3) :=
  EuclideanSpace.single (0 : Fin 3) (1 : ℝ)

/-- The displacement is nonzero. -/
theorem correlationDisplacement_ne_zero : correlationDisplacement ≠ 0 := by
  intro zero
  have coordinate : correlationDisplacement 0 =
      (0 : EuclideanSpace ℝ (Fin 3)) 0 :=
    congrArg (fun value : EuclideanSpace ℝ (Fin 3) => value 0) zero
  have oneZero : (1 : ℝ) = 0 := by
    simp [correlationDisplacement] at coordinate
  exact one_ne_zero oneZero

/-- The nondegenerate two-atom correlation relation: the second atom is the first atom shifted by
one unit along the first coordinate.  This is a proper subset of the product of its two marginals,
not merely an inequality between two independent coordinates. -/
def correlationRelation : Set (MolecularConformation (Fin 2)) :=
  { conformation | conformation 1 = conformation 0 + correlationDisplacement }

/-- The first coordinate of a two-atom conformation. -/
def correlationFirst (conformation : MolecularConformation (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) :=
  conformation 0

/-- The second coordinate of a two-atom conformation. -/
def correlationSecond (conformation : MolecularConformation (Fin 2)) :
    EuclideanSpace ℝ (Fin 3) :=
  conformation 1

/-- The correlated pair with a prescribed first coordinate. -/
def correlationCouple (first : EuclideanSpace ℝ (Fin 3)) :
    MolecularConformation (Fin 2) :=
  fun index => if index = 0 then first else first + correlationDisplacement

@[simp] theorem correlationCouple_zero (first : EuclideanSpace ℝ (Fin 3)) :
    correlationCouple first 0 = first := by
  unfold correlationCouple
  exact if_pos rfl

@[simp] theorem correlationCouple_one (first : EuclideanSpace ℝ (Fin 3)) :
    correlationCouple first 1 = first + correlationDisplacement := by
  unfold correlationCouple
  have different : (1 : Fin 2) ≠ 0 := by decide
  exact if_neg different

/-- The correlated pair belongs to the relation. -/
theorem correlationCouple_mem (first : EuclideanSpace ℝ (Fin 3)) :
    correlationCouple first ∈ correlationRelation := by
  show correlationCouple first 1 =
    correlationCouple first 0 + correlationDisplacement
  rw [correlationCouple_one, correlationCouple_zero]

/-- The first marginal of a two-atom relation. -/
def correlationFirstMarginal (relation : Set (MolecularConformation (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  { value | ∃ conformation ∈ relation, correlationFirst conformation = value }

/-- The second marginal of a two-atom relation. -/
def correlationSecondMarginal (relation : Set (MolecularConformation (Fin 2))) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  { value | ∃ conformation ∈ relation, correlationSecond conformation = value }

/-- The product reconstruction induced by the two marginal sets. -/
def correlationProduct (relation : Set (MolecularConformation (Fin 2))) :
    Set (MolecularConformation (Fin 2)) :=
  { conformation |
      correlationFirst conformation ∈ correlationFirstMarginal relation ∧
        correlationSecond conformation ∈ correlationSecondMarginal relation }

/-- The first marginal of the correlation relation is the whole of real three-space. -/
@[simp] theorem correlationFirstMarginal_eq_univ :
    correlationFirstMarginal correlationRelation = Set.univ := by
  ext value
  constructor
  · intro _
    exact Set.mem_univ value
  · intro _
    exact ⟨correlationCouple value, correlationCouple_mem value,
      correlationCouple_zero value⟩

/-- The second marginal of the correlation relation is the whole of real three-space. -/
@[simp] theorem correlationSecondMarginal_eq_univ :
    correlationSecondMarginal correlationRelation = Set.univ := by
  ext value
  constructor
  · intro _
    exact Set.mem_univ value
  · intro _
    refine ⟨correlationCouple (value - correlationDisplacement),
      correlationCouple_mem _, ?_⟩
    show correlationCouple (value - correlationDisplacement) 1 = value
    rw [correlationCouple_one]
    exact sub_add_cancel value correlationDisplacement

/-- The product reconstruction from both full marginals is the whole function space. -/
@[simp] theorem correlationProduct_eq_univ :
    correlationProduct correlationRelation = Set.univ := by
  ext conformation
  simp [correlationProduct, correlationFirstMarginal_eq_univ,
    correlationSecondMarginal_eq_univ]

/-- The relation is contained in the product of its marginals. -/
theorem correlationRelation_subset_product :
    correlationRelation ⊆ correlationProduct correlationRelation := by
  intro conformation _
  rw [correlationProduct_eq_univ]
  exact Set.mem_univ conformation

/-- Every member of the relation assigns distinct points to the two atoms. -/
theorem correlationRelation_atoms_distinct
    {conformation : MolecularConformation (Fin 2)}
    (member : conformation ∈ correlationRelation) :
    conformation 0 ≠ conformation 1 := by
  intro equal
  have relation : conformation 1 = conformation 0 + correlationDisplacement := member
  rw [equal] at relation
  have cancelled : conformation 1 + 0 =
      conformation 1 + correlationDisplacement := by
    rw [add_zero]
    exact relation
  have zeroEq : (0 : EuclideanSpace ℝ (Fin 3)) = correlationDisplacement :=
    add_left_cancel cancelled
  exact correlationDisplacement_ne_zero zeroEq.symm

/-- The constantly-zero conformation is outside the relation. -/
def correlationZero : MolecularConformation (Fin 2) :=
  fun _ => 0

theorem correlationZero_not_mem : correlationZero ∉ correlationRelation := by
  intro member
  have relation : correlationZero 1 = correlationZero 0 + correlationDisplacement := member
  have zeroEq : (0 : EuclideanSpace ℝ (Fin 3)) = correlationDisplacement := by
    simpa [correlationZero] using relation
  exact correlationDisplacement_ne_zero zeroEq.symm

/-- The product reconstruction is strictly larger than the correlation relation. -/
theorem correlationRelation_ne_product :
    correlationRelation ≠ correlationProduct correlationRelation := by
  intro equal
  have member : correlationZero ∈ correlationProduct correlationRelation := by
    rw [correlationProduct_eq_univ]
    exact Set.mem_univ _
  rw [← equal] at member
  exact correlationZero_not_mem member

/-- The nondegenerate two-atom correlation witness: both marginals are all of real three-space,
the relation is a proper subset of their product, and every member assigns distinct points to the
two atoms. -/
theorem nondegenerate_correlation_witness :
    correlationFirstMarginal correlationRelation = Set.univ ∧
      correlationSecondMarginal correlationRelation = Set.univ ∧
      correlationRelation ⊆ correlationProduct correlationRelation ∧
      correlationRelation ≠ correlationProduct correlationRelation ∧
      (∀ conformation ∈ correlationRelation, conformation 0 ≠ conformation 1) :=
  ⟨correlationFirstMarginal_eq_univ, correlationSecondMarginal_eq_univ,
    correlationRelation_subset_product, correlationRelation_ne_product,
    fun _ member => correlationRelation_atoms_distinct member⟩

/-- The correlation relation packaged with the existing `CorrelatedInformation` carrier.  The
knowledge tag is retained metadata only; no theorem derives it from the relation. -/
def correlationInformation : CorrelatedInformation (MolecularConformation (Fin 2)) :=
  CorrelatedInformation.ofPossible
    IUPACDrawing2006.ST6.ConfigurationKnowledge.experimentallyUnknown []
    correlationRelation

/-- The packaged correlation information is consistent (its joint possible set is nonempty). -/
theorem correlationInformation_consistent : correlationInformation.Consistent := by
  rw [CorrelatedInformation.consistent_iff]
  exact ⟨correlationCouple 0,
    by simpa [correlationInformation] using correlationCouple_mem (0 : EuclideanSpace ℝ (Fin 3))⟩

/-- The packaged correlation information entails the nondegenerate relation. -/
theorem correlationInformation_entails_relation :
    correlationInformation.Entails
      (fun conformation : MolecularConformation (Fin 2) =>
        conformation 1 = conformation 0 + correlationDisplacement) := by
  intro conformation member
  simpa [correlationInformation] using member

/-! ## Concrete typed examples -/

namespace PartialCoordinateExample

/-- Carbon, atomic number 6. -/
def carbon : PeriodicElement where
  atomicNumber := 6
  positive := by decide
  atMost118 := by decide

/-- Two carbon atoms with no interactions. -/
def twoCarbonGraph : FiniteAtomInteractionHypergraph (Fin 2) where
  atomData := fun _ => { element := carbon }
  interactions := []
  arity_ge_two := by
    intro edge member
    simp at member
  participants_nodup := by
    intro edge member
    simp at member

/-- Two carbon atoms with one explicit covalent interaction occurrence. -/
def bondedCarbonGraph : FiniteAtomInteractionHypergraph (Fin 2) where
  atomData := fun _ => { element := carbon }
  interactions := [([0, 1], SemanticInteractionKind.covalent 1)]
  arity_ge_two := by
    intro edge member
    simp at member
    rcases member with rfl
    decide
  participants_nodup := by
    intro edge member
    simp at member
    rcases member with rfl
    decide

/-- A fully specified observation: both atoms are observed at the origin. -/
def exampleObservation : PartialCoordinateObservation (Fin 2) :=
  fun _ => some 0

/-- The constant-origin conformation satisfying the example observation. -/
def exampleConformation : MolecularConformation (Fin 2) :=
  fun _ => 0

theorem exampleConformation_mem :
    exampleConformation ∈ observationConformations exampleObservation := by
  intro atom value observed
  simpa [exampleConformation, exampleObservation] using observed

theorem exampleObservation_fullySpecified : ∀ atom, exampleObservation atom ≠ none := by
  intro atom
  simp [exampleObservation]

/-- The default zero-family state of the example. -/
def exampleStateAbsent : FiniteState (Fin 2) :=
  defaultFiniteState twoCarbonGraph exampleConformation

/-- The same graph and conformation with a present (but entirely unknown) sparse partial-position
channel.  This state is genuinely compatible and genuinely different from the default state. -/
def exampleStatePresent : FiniteState (Fin 2) :=
  presentPartialFiniteState twoCarbonGraph exampleConformation
    { positions := fun _ => none }

theorem exampleStateAbsent_mem :
    exampleStateAbsent ∈ compatibleStates twoCarbonGraph
      (observationConformations exampleObservation) := by
  exact ⟨by simp [exampleStateAbsent], exampleConformation_mem⟩

theorem exampleStatePresent_mem :
    exampleStatePresent ∈ compatibleStates twoCarbonGraph
      (observationConformations exampleObservation) := by
  exact ⟨by simp [exampleStatePresent], exampleConformation_mem⟩

theorem exampleStateAbsent_mem_defaultImage :
    exampleStateAbsent ∈ defaultCompletionImage twoCarbonGraph :=
  ⟨exampleConformation, rfl⟩

theorem exampleStatePresent_not_defaultImage :
    exampleStatePresent ∉ defaultCompletionImage twoCarbonGraph := by
  intro member
  exact presentPartialFiniteState_not_defaultImage twoCarbonGraph exampleConformation
    { positions := fun _ => none } member

theorem exampleStates_distinct : exampleStateAbsent ≠ exampleStatePresent := by
  intro equal
  exact defaultFiniteState_ne_presentPartialFiniteState twoCarbonGraph exampleConformation
    { positions := fun _ => none } equal

/-- Both states are compatible although they share the same observed coordinates; only the default
state is in the default-completion image.  This is the concrete default-image incompleteness
witness. -/
theorem example_partial_image_incompleteness :
    exampleStateAbsent ∈ compatibleStates twoCarbonGraph
        (observationConformations exampleObservation) ∧
      exampleStatePresent ∈ compatibleStates twoCarbonGraph
        (observationConformations exampleObservation) ∧
      exampleStateAbsent ∈ defaultCompletionImage twoCarbonGraph ∧
      exampleStatePresent ∉ defaultCompletionImage twoCarbonGraph :=
  ⟨exampleStateAbsent_mem, exampleStatePresent_mem, exampleStateAbsent_mem_defaultImage,
    exampleStatePresent_not_defaultImage⟩

/-- The two example states are distinct but have the same graph and conformation. -/
theorem example_same_conformation :
    exampleStateAbsent.2.2.graph = exampleStatePresent.2.2.graph ∧
      exampleStateAbsent.2.2.conformation = exampleStatePresent.2.2.conformation ∧
      exampleStateAbsent ≠ exampleStatePresent :=
  ⟨rfl, rfl, exampleStates_distinct⟩

/-- Every element of `Fin 2` is zero or one. -/
theorem fin_two_eq_zero_or_one (index : Fin 2) : index = 0 ∨ index = 1 := by
  have all : ∀ other : Fin 2, other = 0 ∨ other = 1 :=
    Fin.forall_fin_two.mpr ⟨Or.inl rfl, Or.inr rfl⟩
  exact all index

/-- An injective conformation on two atoms, needed for the geometric zero-path witness.  Unlike the
fully observed constant-origin conformation, this one separates the two atom positions. -/
def exampleInjectiveConformation : MolecularConformation (Fin 2) :=
  correlationCouple 0

theorem exampleInjectiveConformation_injective :
    Function.Injective exampleInjectiveConformation := by
  intro first second equal
  rcases fin_two_eq_zero_or_one first with rfl | rfl <;>
    rcases fin_two_eq_zero_or_one second with rfl | rfl
  · rfl
  · exfalso
    simp [exampleInjectiveConformation, correlationCouple_zero, correlationCouple_one] at equal
    exact correlationDisplacement_ne_zero equal.symm
  · exfalso
    simp [exampleInjectiveConformation, correlationCouple_zero, correlationCouple_one] at equal
    exact correlationDisplacement_ne_zero equal
  · rfl

/-- The bonded example's interaction occurrence is not covered by the zero-path witness even
though that witness satisfies `PathGeometryValid`. -/
theorem bondedExample_zeroPath_not_coverage :
    PathGeometryValid ((defaultFiniteState bondedCarbonGraph
        exampleInjectiveConformation).2.2 :
        WholeState (Fin 2) (Fin 0) (Fin 0)) ∧
      ¬ PathCoversAllInteractions
        ((defaultFiniteState bondedCarbonGraph exampleInjectiveConformation).2.2 :
          WholeState (Fin 2) (Fin 0) (Fin 0)) := by
  refine zeroPathGeometryValid_not_completeBondCoverage bondedCarbonGraph
    exampleInjectiveConformation exampleInjectiveConformation_injective ⟨0, by decide⟩

end PartialCoordinateExample

end

end OneCenter
end TetraStereo

/-! ## Kernel-authority guards -/

assert_kernel_only TetraStereo.OneCenter.mem_compatibleStates_iff
assert_kernel_only TetraStereo.OneCenter.compatibleStates_coverage
assert_kernel_only TetraStereo.OneCenter.compatibleStates_other_channels_irrelevant
assert_kernel_only TetraStereo.OneCenter.conformationProjection_compatibleStates
assert_kernel_only TetraStereo.OneCenter.compatibleStates_nonempty_iff
assert_kernel_only TetraStereo.OneCenter.rationalObservation_none_iff
assert_kernel_only TetraStereo.OneCenter.rationalObservation_some_iff
assert_kernel_only TetraStereo.OneCenter.rationalObservation_eq_some_toEuclideanPoint
assert_kernel_only TetraStereo.OneCenter.rational_observationConformations_iff
assert_kernel_only TetraStereo.OneCenter.canonicalConformationOfObservation_mem
assert_kernel_only TetraStereo.OneCenter.observationConformations_nonempty
assert_kernel_only TetraStereo.OneCenter.compatibleStates_observation_nonempty
assert_kernel_only TetraStereo.OneCenter.realizedObservation_injective
assert_kernel_only TetraStereo.OneCenter.realizedObservation_recovers
assert_kernel_only TetraStereo.OneCenter.observation_recovery_on_observed
assert_kernel_only TetraStereo.OneCenter.observationConformations_subsingleton_of_fullySpecified
assert_kernel_only TetraStereo.OneCenter.unknownCoordinate_vary
assert_kernel_only TetraStereo.OneCenter.observationConformations_combine_subset
assert_kernel_only TetraStereo.OneCenter.observationConformations_inter_nonempty_iff
assert_kernel_only TetraStereo.OneCenter.observationConformations_inter_eq_empty_iff_conflict
assert_kernel_only TetraStereo.OneCenter.observationsConflict_iff_exists_overlap_disagreement
assert_kernel_only TetraStereo.OneCenter.fullySpecified_conformation_only
assert_kernel_only TetraStereo.OneCenter.defaultFiniteState_ne_presentPartialFiniteState
assert_kernel_only TetraStereo.OneCenter.presentPartialFiniteState_not_defaultImage
assert_kernel_only TetraStereo.OneCenter.encodeDescription_graph
assert_kernel_only TetraStereo.OneCenter.encodeDescription_conformation
assert_kernel_only TetraStereo.OneCenter.decodeDescription_graph
assert_kernel_only TetraStereo.OneCenter.decodeDescription_conformation
assert_kernel_only TetraStereo.OneCenter.decodeFiniteState_encodeFiniteState
assert_kernel_only TetraStereo.OneCenter.encodeFiniteState_decodeFiniteState
assert_kernel_only TetraStereo.OneCenter.encodeFiniteState_injective
assert_kernel_only TetraStereo.OneCenter.encodeFiniteState_surjective
assert_kernel_only TetraStereo.OneCenter.encodeFiniteState_graph
assert_kernel_only TetraStereo.OneCenter.encodeFiniteState_conformation
assert_kernel_only TetraStereo.OneCenter.decodeFiniteState_graph
assert_kernel_only TetraStereo.OneCenter.decodeFiniteState_conformation
assert_kernel_only TetraStereo.OneCenter.decodeFiniteStateSet_encodeFiniteStateSet
assert_kernel_only TetraStereo.OneCenter.encodeFiniteStateSet_decodeFiniteStateSet
assert_kernel_only TetraStereo.OneCenter.decodeFiniteState_mem_compatibleStates_iff
assert_kernel_only TetraStereo.OneCenter.decodeFiniteStateSet_encodedCompatibleStates
assert_kernel_only TetraStereo.OneCenter.defaultFiniteState_pathGeometryValid
assert_kernel_only TetraStereo.OneCenter.conformationProjection_geometricCompatibleStates
assert_kernel_only TetraStereo.OneCenter.zeroPathGeometryValid_not_completeBondCoverage
assert_kernel_only TetraStereo.OneCenter.correlationDisplacement_ne_zero
assert_kernel_only TetraStereo.OneCenter.correlationCouple_mem
assert_kernel_only TetraStereo.OneCenter.correlationFirstMarginal_eq_univ
assert_kernel_only TetraStereo.OneCenter.correlationSecondMarginal_eq_univ
assert_kernel_only TetraStereo.OneCenter.correlationProduct_eq_univ
assert_kernel_only TetraStereo.OneCenter.correlationRelation_subset_product
assert_kernel_only TetraStereo.OneCenter.correlationRelation_atoms_distinct
assert_kernel_only TetraStereo.OneCenter.correlationZero_not_mem
assert_kernel_only TetraStereo.OneCenter.correlationRelation_ne_product
assert_kernel_only TetraStereo.OneCenter.nondegenerate_correlation_witness
assert_kernel_only TetraStereo.OneCenter.correlationInformation_consistent
assert_kernel_only TetraStereo.OneCenter.correlationInformation_entails_relation
assert_kernel_only TetraStereo.OneCenter.PartialCoordinateExample.exampleConformation_mem
assert_kernel_only TetraStereo.OneCenter.PartialCoordinateExample.exampleObservation_fullySpecified
assert_kernel_only TetraStereo.OneCenter.PartialCoordinateExample.exampleStateAbsent_mem
assert_kernel_only TetraStereo.OneCenter.PartialCoordinateExample.exampleStatePresent_mem
assert_kernel_only TetraStereo.OneCenter.PartialCoordinateExample.exampleStateAbsent_mem_defaultImage
assert_kernel_only TetraStereo.OneCenter.PartialCoordinateExample.exampleStatePresent_not_defaultImage
assert_kernel_only TetraStereo.OneCenter.PartialCoordinateExample.exampleStates_distinct
assert_kernel_only TetraStereo.OneCenter.PartialCoordinateExample.example_partial_image_incompleteness
assert_kernel_only TetraStereo.OneCenter.PartialCoordinateExample.example_same_conformation
assert_kernel_only TetraStereo.OneCenter.PartialCoordinateExample.bondedExample_zeroPath_not_coverage
