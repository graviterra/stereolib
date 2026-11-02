import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoPartialCoordinateStateCompletion
import TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension
import TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Complete selected-pair bond-path data from sparse atom coordinates

This module supplies the constructive composition that was still missing between three existing
results:

* `OrganicStereoPartialInjectivePositionExtension.exists_injective_extension_iff` — a sparse real
  position table has an injective total extension exactly when it is known-injective;
* `OrganicStereoPrescribedMolecularPathCompletion.exists_prescribedData` (and its explicit
  `prescribedData` construction) — an arbitrary finite atom interaction hypergraph together with an
  arbitrary injective total position family has actual independent bond-path data with the exact
  source graph, the structural selected occurrence indices, the structural oriented endpoints,
  occurrence injectivity and completeness for every atom enumeration;
* `OrganicStereoPartialCoordinateStateCompletion.conformationProjection_geometricCompatibleStates`
  — the conformation projection of the geometric compatible whole states is exactly the set of
  injective conformations satisfying the supplied observation.

The headline result is

`exists_completeSelectedPairPathData_iff`:

> for an arbitrary finite atom interaction hypergraph `graph` and an arbitrary sparse real
> observation `p`, there exists complete selected-pair molecular bond-path data whose graph is
> exactly `graph` and whose conformation reproduces every supplied coordinate **if and only if**
> `KnownInjective p`.

The forward direction uses the *actual* injectivity of the data's full conformation (and the
pointwise agreement with the observed coordinates); the reverse direction uses the explicit
injective completion `complete p` and then the actual selected-pair data construction.  No finished
path object, embedding, arc family, coverage hypothesis or geometric law is an input: the endpoint
maps, occurrence indices, non-loop condition and completeness proof are derived from the source
graph.  Parallel bonds between the same two atoms remain distinct because the edge type is the
selected occurrence subtype `SelectedBondIndex graph`, not an unordered atom pair.

## Sparse observations

`observationConformations` is proved injective as a map from sparse observations to sets of full
conformations.  Consequently the existing encoded compatible-state set distinguishes a missing
coordinate (`none`) from a present coordinate (`some x`), including the present value zero; no
absent coordinate is silently identified with the origin.  The rational specialization uses the
existing exact rational-to-real embedding `CartesianPoint3.toEuclideanPoint`, with the exact
injectivity correspondence `knownInjective_map_toEuclideanPoint`, and preserves every rational
value as its exact real image.

## Scope

This is geometric realization only.  The lossless source channel may retain conflicting coordinate
observations; such a table is a perfectly well-typed `PartialCoordinateInput`, but it has no
injective completion and therefore no data produced by this theorem.  `KnownInjective` is an
explicit input condition and the equivalence is sharp: finiteness of the atom type alone neither
makes an arbitrary observation realizable nor is used as a gate on the representation.  Nothing
here asserts bond lengths, angles, energies, chemical truth or topological classification, and no
unselected interaction (multicenter, ionic, metallic, hydrogen-bond, `.other`, or a selected kind
with non-binary arity) is realized as a path.  Contradictory observations stay contradictory source
data; the module proves only the exact geometric realization criterion.
-/

namespace TetraStereo.OneCenter
namespace OrganicStereoPartialPositionPathCompletion

noncomputable section

universe u

open TetraStereo.OneCenter.JointCoreEncoding
open TetraStereo.OneCenter.OrganicStereoEmbeddedMolecularGraphCoverage
open TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion
open TetraStereo.OneCenter.OrganicStereoPartialInjectivePositionExtension

/-! ## Sparse observation sets are injective

A sparse observation determines the set of full conformations satisfying it.  Conversely, two
different sparse observations determine different sets: a differing observed value separates the
sets by the value itself, while an atom observed in one channel and absent in the other is
separated by varying the missing coordinate to a point different from the observed one. -/

theorem observationConformations_injective {V : Type u} [DecidableEq V] :
    Function.Injective (observationConformations (V := V)) := by
  intro first second equal
  by_contra hne
  have hdiff : ∃ atom : V, first atom ≠ second atom := by
    by_contra hnone
    apply hne
    funext atom
    by_contra hatom
    exact hnone ⟨atom, hatom⟩
  obtain ⟨atom, hatom⟩ := hdiff
  cases hfirst : first atom with
  | none =>
      cases hsecond : second atom with
      | none => exact hatom (by rw [hfirst, hsecond])
      | some value =>
          obtain ⟨conformation, member, valueEq⟩ :=
            unknownCoordinate_vary (observation := first) hfirst
              (value + correlationDisplacement)
          have memberSecond : conformation ∈ observationConformations second := by
            rw [← equal]
            exact member
          have atomValue : conformation atom = value :=
            memberSecond atom value hsecond
          have displacementZero : correlationDisplacement = 0 := by
            have equalValues : value + correlationDisplacement = value := by
              rw [← valueEq]
              exact atomValue
            have equalValues' : value + correlationDisplacement = value + 0 := by
              rw [add_zero]
              exact equalValues
            exact add_left_cancel equalValues'
          exact correlationDisplacement_ne_zero displacementZero
  | some value =>
      cases hsecond : second atom with
      | none =>
          obtain ⟨conformation, member, valueEq⟩ :=
            unknownCoordinate_vary (observation := second) hsecond
              (value + correlationDisplacement)
          have memberFirst : conformation ∈ observationConformations first := by
            rw [equal]
            exact member
          have atomValue : conformation atom = value :=
            memberFirst atom value hfirst
          have displacementZero : correlationDisplacement = 0 := by
            have equalValues : value + correlationDisplacement = value := by
              rw [← valueEq]
              exact atomValue
            have equalValues' : value + correlationDisplacement = value + 0 := by
              rw [add_zero]
              exact equalValues
            exact add_left_cancel equalValues'
          exact correlationDisplacement_ne_zero displacementZero
      | some otherValue =>
          have valuesDifferent : value ≠ otherValue := by
            intro valuesEqual
            exact hatom (by rw [hfirst, hsecond, valuesEqual])
          have canonicalMember := canonicalConformationOfObservation_mem first
          have canonicalNotSecond :
              canonicalConformationOfObservation first ∉ observationConformations second := by
            intro memberSecond
            have atomOther : canonicalConformationOfObservation first atom = otherValue :=
              memberSecond atom otherValue hsecond
            have atomValue : canonicalConformationOfObservation first atom = value := by
              simp [canonicalConformationOfObservation, hfirst]
            exact valuesDifferent (atomValue.symm.trans atomOther)
          rw [equal] at canonicalMember
          exact canonicalNotSecond canonicalMember

/-- A missing coordinate and a present coordinate always give different observation sets, even
when the present value is the origin.  Hence the existing compatible-state construction retains
sparse observations and does not identify absence with a coordinate value. -/
theorem observationConformations_ne_of_absent_present {V : Type u} [DecidableEq V]
    {observation other : PartialCoordinateObservation V} {atom : V}
    {value : EuclideanSpace ℝ (Fin 3)}
    (absent : observation atom = none) (present : other atom = some value) :
    observationConformations observation ≠ observationConformations other := by
  intro equal
  have observationsEqual : observation = other := observationConformations_injective equal
  have atomEqual : observation atom = other atom := congrFun observationsEqual atom
  rw [absent, present] at atomEqual
  cases atomEqual

/-! ## The encoded compatible-state set also retains sparse observations

The lifted encoder `encodeFiniteState` is injective, so its set image is injective and the encoded
compatible-state set inherits observation-set injectivity.  This is why an encoded compatible-state
set can distinguish a `none` observation from a `some` observation without a new sidecar. -/

theorem encodeFiniteStateSet_injective {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V)) :
    Function.Injective (encodeFiniteStateSet enumerate) := by
  intro first second equal
  calc
    first = decodeFiniteStateSet enumerate (encodeFiniteStateSet enumerate first) :=
      (decodeFiniteStateSet_encodeFiniteStateSet enumerate first).symm
    _ = decodeFiniteStateSet enumerate (encodeFiniteStateSet enumerate second) := by rw [equal]
    _ = second := decodeFiniteStateSet_encodeFiniteStateSet enumerate second

/-- The compatible-state construction is injective in the conformation constraint set: two
compatible-state sets with the same graph are equal only when their conformation sets are equal.
The graph and every other channel are held fixed, and the conformation projection recovers the
constraint set exactly. -/
theorem compatibleStates_injective {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) :
    Function.Injective (compatibleStates graph) := by
  intro first second equal
  have projectionEqual := congrArg conformationProjection equal
  rw [conformationProjection_compatibleStates graph first,
    conformationProjection_compatibleStates graph second] at projectionEqual
  exact projectionEqual

theorem encodedCompatibleStates_injective {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V) :
    Function.Injective (encodedCompatibleStates enumerate graph) := by
  intro first second equal
  exact compatibleStates_injective graph (encodeFiniteStateSet_injective enumerate equal)

theorem encodedCompatibleStates_observation_ne_of_absent_present
    {V : Type u} [DecidableEq V] [Fintype V]
    (enumerate : V ≃ Fin (Fintype.card V))
    (graph : FiniteAtomInteractionHypergraph V)
    {observation other : PartialCoordinateObservation V} {atom : V}
    {value : EuclideanSpace ℝ (Fin 3)}
    (absent : observation atom = none) (present : other atom = some value) :
    encodedCompatibleStates enumerate graph (observationConformations observation) ≠
      encodedCompatibleStates enumerate graph (observationConformations other) := by
  intro equal
  exact observationConformations_ne_of_absent_present absent present
    (encodedCompatibleStates_injective enumerate graph equal)

/-! ## The geometric compatible-state projection

`conformationProjection_geometricCompatibleStates` identifies the shared-conformation projection
with `{c ∈ K | Function.Injective c}`.  For the observation constraint set `K` this is exactly the
set of injective total extensions of the sparse observation. -/

theorem mem_observationConformations_iff_extends {V : Type u}
    (p : PartialPosition V) (conformation : MolecularConformation V) :
    conformation ∈ observationConformations p ↔ Extends p conformation :=
  ⟨fun member atom value observed => member atom value observed,
    fun member atom value observed => member observed⟩

theorem conformationProjection_geometricCompatibleStates_observation
    {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (p : PartialPosition V) :
    conformationProjection (geometricCompatibleStates graph (observationConformations p)) =
      { conformation : MolecularConformation V |
        Extends p conformation ∧ Function.Injective conformation } := by
  rw [conformationProjection_geometricCompatibleStates]
  ext conformation
  constructor
  · rintro ⟨observedMem, injective⟩
    exact ⟨(mem_observationConformations_iff_extends p conformation).mp observedMem, injective⟩
  · rintro ⟨extendsMem, injective⟩
    exact ⟨(mem_observationConformations_iff_extends p conformation).mpr extendsMem, injective⟩

/-- Geometric compatible whole states for the observation constraint set are nonempty exactly when
the sparse observation is known-injective.  This composes the partial-position existence criterion
with the geometric compatible-state projection: no path object or extra channel is supplied. -/
theorem geometricCompatibleStates_observation_nonempty_iff
    {V : Type u} [DecidableEq V] [Fintype V]
    (graph : FiniteAtomInteractionHypergraph V) (p : PartialPosition V) :
    (geometricCompatibleStates graph (observationConformations p)).Nonempty ↔
      KnownInjective p := by
  constructor
  · rintro ⟨state, stateMem⟩
    have projectionMem : state.2.2.conformation ∈
        conformationProjection (geometricCompatibleStates graph
          (observationConformations p)) :=
      ⟨state, stateMem, rfl⟩
    rw [conformationProjection_geometricCompatibleStates_observation] at projectionMem
    exact (exists_injective_extension_iff p).mp
      ⟨state.2.2.conformation, projectionMem.1, projectionMem.2⟩
  · intro hp
    obtain ⟨full, extendsFull, injectiveFull⟩ := (exists_injective_extension_iff p).mpr hp
    have projectionMem : full ∈
        conformationProjection (geometricCompatibleStates graph
          (observationConformations p)) := by
      rw [conformationProjection_geometricCompatibleStates_observation]
      exact ⟨extendsFull, injectiveFull⟩
    obtain ⟨state, stateMem, _⟩ := projectionMem
    exact ⟨state, stateMem⟩

/-! ## Complete selected-pair bond-path data agreeing with a partial observation -/

variable {V : Type} [DecidableEq V] [Fintype V]

/-- **The realization predicate.**  Actual independent selected-pair bond-path data of the exact
source graph, agreeing with every supplied coordinate, with the structural selected occurrence
indices and oriented endpoints, injective occurrences (so parallel occurrences stay distinct),
injective full geometry, and completeness of the selected-pair family for every external atom
enumeration.

The remaining fields of `IndependentBondPathData` (arc injectivity, interior avoidance, common
endpoints and the non-loop condition) are part of the structure itself and are therefore also
present; the non-loop condition is the derived `source_ne_target` field of the data. -/
structure CompleteSelectedPairPathDataAgrees
    (graph : FiniteAtomInteractionHypergraph V) (p : PartialPosition V)
    (data : IndependentBondPathData V (SelectedBondIndex graph)) : Prop where
  /-- The data's graph is exactly the supplied source graph. -/
  graph_eq : data.graph = graph
  /-- Every supplied coordinate is reproduced exactly by the full conformation. -/
  extends_observation : Extends p data.conformation
  /-- The full geometry is injective. -/
  atom_injective : Function.Injective data.conformation
  /-- Different selected occurrences, including parallel bonds between the same atoms, stay
  distinct. -/
  occurrence_injective : Function.Injective data.interactionOccurrence
  /-- Each edge names the structural selected source occurrence. -/
  occurrence_eq : ∀ edge : SelectedBondIndex graph,
    data.interactionOccurrence edge = selectedOccurrence graph edge
  /-- Each oriented first endpoint is the structural source participant. -/
  source_eq : ∀ edge : SelectedBondIndex graph,
    data.source edge = selectedSource graph edge
  /-- Each oriented second endpoint is the structural target participant. -/
  target_eq : ∀ edge : SelectedBondIndex graph,
    data.target edge = selectedTarget graph edge
  /-- Every selected binary pair bond of the encoded source is documented, for every external
  atom enumeration. -/
  complete_paths : ∀ enumeration : V ≃ Fin (Fintype.card V),
    data.CompleteForSourcePairBonds enumeration

/-- The explicit construction: complete the sparse observation with `complete`, which keeps every
supplied coordinate verbatim, then build the actual selected-pair bond-path data of the source
graph at that injective total family.  Only the graph, the observation and the known-injectivity
proof are inputs; occurrences, endpoints, non-loop conditions and completeness are derived. -/
def completedSelectedPairData (graph : FiniteAtomInteractionHypergraph V)
    (p : PartialPosition V) (hp : KnownInjective p) :
    IndependentBondPathData V (SelectedBondIndex graph) :=
  prescribedData graph (complete p) (complete_injective p hp)

/-- The explicit construction satisfies the realization predicate. -/
theorem prescribedData_completeAgrees (graph : FiniteAtomInteractionHypergraph V)
    (p : PartialPosition V) (hp : KnownInjective p) :
    CompleteSelectedPairPathDataAgrees graph p
      (prescribedData graph (complete p) (complete_injective p hp)) where
  graph_eq := prescribedData_graph graph (complete p) (complete_injective p hp)
  extends_observation := by
    intro atom value observed
    rw [prescribedData_conformation]
    exact complete_extends p observed
  atom_injective :=
    prescribedData_atom_injective graph (complete p) (complete_injective p hp)
  occurrence_injective :=
    prescribedData_occurrence_injective graph (complete p) (complete_injective p hp)
  occurrence_eq := fun edge =>
    prescribedData_occurrence graph (complete p) (complete_injective p hp) edge
  source_eq := fun edge =>
    prescribedData_source graph (complete p) (complete_injective p hp) edge
  target_eq := fun edge =>
    prescribedData_target graph (complete p) (complete_injective p hp) edge
  complete_paths := fun enumeration =>
    prescribedData_complete graph (complete p) (complete_injective p hp) enumeration

/-- The constructed data satisfies the realization predicate. -/
theorem completedSelectedPairData_agrees (graph : FiniteAtomInteractionHypergraph V)
    (p : PartialPosition V) (hp : KnownInjective p) :
    CompleteSelectedPairPathDataAgrees graph p (completedSelectedPairData graph p hp) :=
  prescribedData_completeAgrees graph p hp

/-- **Headline equivalence.**  Complete selected-pair bond-path data agreeing with the sparse
observation exists exactly when the observation is known-injective.

Forward: the data's full conformation is injective and reproduces the observed values, so two
vertices observed at the same point coincide.  Reverse: `complete` gives an injective total
extension preserving every observed value, and the prescribed selected-pair construction realizes
it completely for every enumeration.

The statement is deliberately an equivalence with `KnownInjective`: it is not an unconditional
coordinate-completion principle, and finiteness of the atom type alone does not supply the
injectivity side condition. -/
theorem exists_completeSelectedPairPathData_iff
    (graph : FiniteAtomInteractionHypergraph V) (p : PartialPosition V) :
    (∃ data : IndependentBondPathData V (SelectedBondIndex graph),
        CompleteSelectedPairPathDataAgrees graph p data) ↔ KnownInjective p := by
  constructor
  · rintro ⟨data, dataAgrees⟩
    exact knownInjective_of_extension dataAgrees.extends_observation dataAgrees.atom_injective
  · intro hp
    exact ⟨completedSelectedPairData graph p hp,
      completedSelectedPairData_agrees graph p hp⟩

/-- The same existence criterion composed with the geometric compatible-state projection. -/
theorem exists_completeSelectedPairPathData_iff_geometricStates_nonempty
    (graph : FiniteAtomInteractionHypergraph V) (p : PartialPosition V) :
    (∃ data : IndependentBondPathData V (SelectedBondIndex graph),
        CompleteSelectedPairPathDataAgrees graph p data) ↔
      (geometricCompatibleStates graph (observationConformations p)).Nonempty :=
  (exists_completeSelectedPairPathData_iff graph p).trans
    (geometricCompatibleStates_observation_nonempty_iff graph p).symm

/-- **Sharp obstruction.**  Two distinct atoms supplied the same point obstruct every completion:
no selected-pair data of any graph can agree with the observation. -/
theorem not_exists_completeSelectedPairPathData_of_conflict
    (graph : FiniteAtomInteractionHypergraph V) (p : PartialPosition V)
    {first second : V} (different : first ≠ second) {value : EmbeddedReal3}
    (firstObserved : p first = some value) (secondObserved : p second = some value) :
    ¬ ∃ data : IndependentBondPathData V (SelectedBondIndex graph),
        CompleteSelectedPairPathDataAgrees graph p data := by
  rintro ⟨data, dataAgrees⟩
  exact not_exists_injective_extension_of_conflict different firstObserved secondObserved
    ⟨data.conformation, dataAgrees.extends_observation, dataAgrees.atom_injective⟩

/-! ### Exact structural endpoints of the constructed data -/

@[simp] theorem completedSelectedPairData_graph (graph : FiniteAtomInteractionHypergraph V)
    (p : PartialPosition V) (hp : KnownInjective p) :
    (completedSelectedPairData graph p hp).graph = graph :=
  prescribedData_graph graph (complete p) (complete_injective p hp)

@[simp] theorem completedSelectedPairData_conformation
    (graph : FiniteAtomInteractionHypergraph V) (p : PartialPosition V)
    (hp : KnownInjective p) :
    (completedSelectedPairData graph p hp).conformation = complete p :=
  prescribedData_conformation graph (complete p) (complete_injective p hp)

/-- The constructed occurrence index is exactly the structural selected occurrence index. -/
@[simp] theorem completedSelectedPairData_occurrence
    (graph : FiniteAtomInteractionHypergraph V) (p : PartialPosition V)
    (hp : KnownInjective p) (edge : SelectedBondIndex graph) :
    (completedSelectedPairData graph p hp).interactionOccurrence edge =
      selectedOccurrence graph edge :=
  prescribedData_occurrence graph (complete p) (complete_injective p hp) edge

/-- The constructed first endpoint is exactly the structural source participant. -/
@[simp] theorem completedSelectedPairData_source
    (graph : FiniteAtomInteractionHypergraph V) (p : PartialPosition V)
    (hp : KnownInjective p) (edge : SelectedBondIndex graph) :
    (completedSelectedPairData graph p hp).source edge = selectedSource graph edge :=
  prescribedData_source graph (complete p) (complete_injective p hp) edge

/-- The constructed second endpoint is exactly the structural target participant. -/
@[simp] theorem completedSelectedPairData_target
    (graph : FiniteAtomInteractionHypergraph V) (p : PartialPosition V)
    (hp : KnownInjective p) (edge : SelectedBondIndex graph) :
    (completedSelectedPairData graph p hp).target edge = selectedTarget graph edge :=
  prescribedData_target graph (complete p) (complete_injective p hp) edge

/-- Two distinct selected occurrences, including parallel bonds between the same atoms, obtain
distinct occurrence indices in the constructed data. -/
theorem completedSelectedPairData_occurrence_injective
    (graph : FiniteAtomInteractionHypergraph V) (p : PartialPosition V)
    (hp : KnownInjective p) :
    Function.Injective (completedSelectedPairData graph p hp).interactionOccurrence :=
  prescribedData_occurrence_injective graph (complete p) (complete_injective p hp)

/-- The constructed selected-pair family is complete for every external atom enumeration. -/
theorem completedSelectedPairData_complete
    (graph : FiniteAtomInteractionHypergraph V) (p : PartialPosition V)
    (hp : KnownInjective p) (enumeration : V ≃ Fin (Fintype.card V)) :
    (completedSelectedPairData graph p hp).CompleteForSourcePairBonds enumeration :=
  prescribedData_complete graph (complete p) (complete_injective p hp) enumeration

/-- The documented encoded occurrences are exactly the images of the structural selected source
occurrences, for every enumeration. -/
theorem completedSelectedPairData_documented
    (graph : FiniteAtomInteractionHypergraph V) (p : PartialPosition V)
    (hp : KnownInjective p) (enumeration : V ≃ Fin (Fintype.card V)) :
    (completedSelectedPairData graph p hp).documented enumeration =
      Finset.univ.image (fun edge : SelectedBondIndex graph =>
        encodedIndex graph enumeration edge.1) :=
  prescribedData_documented_eq_selected_image graph (complete p)
    (complete_injective p hp) enumeration

/-- For any data satisfying the realization predicate, the start of the arc of a selected edge is
the supplied coordinate of its structural source atom, whenever that coordinate is observed. -/
theorem arc_source_eq_of_observed {graph : FiniteAtomInteractionHypergraph V}
    {p : PartialPosition V}
    {data : IndependentBondPathData V (SelectedBondIndex graph)}
    (dataAgrees : CompleteSelectedPairPathDataAgrees graph p data)
    (edge : SelectedBondIndex graph) {value : EmbeddedReal3}
    (observed : p (selectedSource graph edge) = some value) :
    data.arc edge 0 = value := by
  rw [data.source_endpoint edge, dataAgrees.source_eq edge]
  exact dataAgrees.extends_observation observed

/-- For any data satisfying the realization predicate, the end of the arc of a selected edge is the
supplied coordinate of its structural target atom, whenever that coordinate is observed. -/
theorem arc_target_eq_of_observed {graph : FiniteAtomInteractionHypergraph V}
    {p : PartialPosition V}
    {data : IndependentBondPathData V (SelectedBondIndex graph)}
    (dataAgrees : CompleteSelectedPairPathDataAgrees graph p data)
    (edge : SelectedBondIndex graph) {value : EmbeddedReal3}
    (observed : p (selectedTarget graph edge) = some value) :
    data.arc edge 1 = value := by
  rw [data.target_endpoint edge, dataAgrees.target_eq edge]
  exact dataAgrees.extends_observation observed

/-! ## Exact rational partial observations

The rational adapter `rationalObservation` maps each supplied exact rational point by the existing
embedding `CartesianPoint3.toEuclideanPoint`; absence stays absence.  The injectivity condition
transfers in both directions through `knownInjective_map_toEuclideanPoint`, and every observed
rational value is preserved as its exact real image. -/

theorem knownInjective_rationalObservation_iff {V : Type u} [Fintype V]
    {q : V → Option CartesianPoint3} :
    KnownInjective (rationalObservation q) ↔ KnownInjective q := by
  simpa [rationalObservation] using
    (knownInjective_map_toEuclideanPoint (V := V) (q := q))

/-- Rational specialization of the headline equivalence. -/
theorem exists_completeSelectedPairPathData_rational_iff
    (graph : FiniteAtomInteractionHypergraph V) (q : V → Option CartesianPoint3) :
    (∃ data : IndependentBondPathData V (SelectedBondIndex graph),
        CompleteSelectedPairPathDataAgrees graph (rationalObservation q) data) ↔
      KnownInjective q :=
  (exists_completeSelectedPairPathData_iff graph (rationalObservation q)).trans
    (knownInjective_rationalObservation_iff (q := q))

/-- Every supplied rational point is preserved by any data satisfying the realization predicate,
as its exact real embedding. -/
theorem rational_observed_position_preserved
    (graph : FiniteAtomInteractionHypergraph V) {q : V → Option CartesianPoint3}
    {data : IndependentBondPathData V (SelectedBondIndex graph)}
    (dataAgrees : CompleteSelectedPairPathDataAgrees graph (rationalObservation q) data)
    {atom : V} {point : CartesianPoint3} (present : q atom = some point) :
    data.conformation atom = point.toEuclideanPoint :=
  dataAgrees.extends_observation
    (rationalObservation_eq_some_toEuclideanPoint q atom point present)

/-- Every supplied rational point is preserved by the explicit construction. -/
theorem completedSelectedPairData_rational_preserves
    (graph : FiniteAtomInteractionHypergraph V) {q : V → Option CartesianPoint3}
    (hq : KnownInjective q) {atom : V} {point : CartesianPoint3}
    (present : q atom = some point) :
    (completedSelectedPairData graph (rationalObservation q)
      (knownInjective_rationalObservation_iff.mpr hq)).conformation atom =
        point.toEuclideanPoint :=
  rational_observed_position_preserved graph
    (completedSelectedPairData_agrees graph (rationalObservation q)
      (knownInjective_rationalObservation_iff.mpr hq)) present

/-! ## Sharpness fixtures

Finiteness of the atom type does not make an arbitrary observation realizable: the constant-origin
table on two atoms is well-typed but not known-injective, so no complete data agreeing with it
exists.  Conversely, an injective partial table on the coplanar four-atom fixture does have
complete data. -/

theorem constantPartialPosition_not_knownInjective :
    ¬ KnownInjective (fun _ : Fin 2 => some (0 : EmbeddedReal3)) := by
  intro known
  have equal : (0 : Fin 2) = 1 := known (a := 0) (b := 1) rfl rfl
  have values : (0 : ℕ) = 1 := by
    simpa using congrArg Fin.val equal
  exact Nat.zero_ne_one values

/-- The conflicting table has no complete agreeing data for any graph on the same atom type. -/
theorem constantPartialPosition_no_completeData
    (graph : FiniteAtomInteractionHypergraph (Fin 2)) :
    ¬ ∃ data : IndependentBondPathData (Fin 2) (SelectedBondIndex graph),
        CompleteSelectedPairPathDataAgrees graph
          (fun _ : Fin 2 => some (0 : EmbeddedReal3)) data := by
  intro existsData
  exact constantPartialPosition_not_knownInjective
    ((exists_completeSelectedPairPathData_iff graph _).mp existsData)

/-- A sparse observation of the coplanar four-atom fixture: the first atom is unobserved, the
other three carry their exact coplanar positions. -/
def fixturePartialPosition : PartialPosition (Fin 4) :=
  fun atom =>
    if atom = 0 then none
    else some
      (TetraStereo.OneCenter.OrganicStereoPrescribedPositionGraphEmbedding.coplanarPosition atom)

/-- The sparse coplanar observation is known-injective, because the underlying total coplanar
family is injective.  The unobserved atom supplies no constraint. -/
theorem fixturePartialPosition_knownInjective :
    KnownInjective fixturePartialPosition := by
  refine knownInjective_of_injective_supplied
    (f := TetraStereo.OneCenter.OrganicStereoPrescribedPositionGraphEmbedding.coplanarPosition)
    TetraStereo.OneCenter.OrganicStereoPrescribedPositionGraphEmbedding.coplanarPosition_injective ?_
  intro atom value observed
  by_cases zero : atom = 0
  · simp [fixturePartialPosition, zero] at observed
  · simp [fixturePartialPosition, zero] at observed ⊢
    exact observed.symm

/-- The fixture observation has complete selected-pair data on the exact prescribed fixture
graph. -/
theorem exists_fixture_completeData :
    ∃ data : IndependentBondPathData (Fin 4)
        (SelectedBondIndex
          TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.fixtureGraph),
      CompleteSelectedPairPathDataAgrees
        TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.fixtureGraph
        fixturePartialPosition data :=
  (exists_completeSelectedPairPathData_iff _ _).mpr fixturePartialPosition_knownInjective

/-- The explicit fixture construction reproduces the supplied coordinate of the second atom. -/
theorem fixture_completeData_preserves_observed :
    (completedSelectedPairData
      TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.fixtureGraph
      fixturePartialPosition fixturePartialPosition_knownInjective).conformation 1 =
        TetraStereo.OneCenter.OrganicStereoPrescribedPositionGraphEmbedding.coplanarPosition 1 :=
  (completedSelectedPairData_agrees
    TetraStereo.OneCenter.OrganicStereoPrescribedMolecularPathCompletion.fixtureGraph
    fixturePartialPosition fixturePartialPosition_knownInjective).extends_observation (by
      simp [fixturePartialPosition])

end

end OrganicStereoPartialPositionPathCompletion
end TetraStereo.OneCenter

/-! ## Kernel-authority guards

The decisive endpoints are checked to depend only on the standard kernel principles permitted by
`assert_kernel_only`.  No proof placeholder, new axiom, evaluator trust or compiler trust is used. -/

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.observationConformations_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.observationConformations_ne_of_absent_present
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.encodeFiniteStateSet_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.compatibleStates_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.encodedCompatibleStates_injective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.encodedCompatibleStates_observation_ne_of_absent_present
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.mem_observationConformations_iff_extends
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.conformationProjection_geometricCompatibleStates_observation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.geometricCompatibleStates_observation_nonempty_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.CompleteSelectedPairPathDataAgrees
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.completedSelectedPairData
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.prescribedData_completeAgrees
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.completedSelectedPairData_agrees
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.exists_completeSelectedPairPathData_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.exists_completeSelectedPairPathData_iff_geometricStates_nonempty
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.not_exists_completeSelectedPairPathData_of_conflict
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.completedSelectedPairData_documented
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.arc_source_eq_of_observed
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.arc_target_eq_of_observed
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.knownInjective_rationalObservation_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.exists_completeSelectedPairPathData_rational_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.rational_observed_position_preserved
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.completedSelectedPairData_rational_preserves
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.constantPartialPosition_not_knownInjective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.constantPartialPosition_no_completeData
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.fixturePartialPosition_knownInjective
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.exists_fixture_completeData
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoPartialPositionPathCompletion.fixture_completeData_preserves_observed
