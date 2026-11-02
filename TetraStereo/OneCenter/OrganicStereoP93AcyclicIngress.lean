import TetraStereo.OneCenter.IUPACP93AcyclicAuthorityCarrier
import TetraStereo.OneCenter.OrganicStereoP93PhysicalFrameIngress

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# V-native ingress for acyclic P-93 authority assignments and observations

The carrier `IUPACP93AcyclicAuthorityCarrier` stores five distinct kinds of information in one
`P93AcyclicAuthorityAssignment`:

* the physical unit (`P93AuthorityPhysicalUnit`, raw `Nat` atom indices);
* an **optional** citation token (`Option P93AuthorityCitationToken`);
* parent-name component metadata (`policy.Component`);
* the independent `UnitKind`; and
* the independent `Descriptor`.

The older `OrganicStereoSuppliedCitationIngress.SuppliedLocatedAssignment` cannot represent this
shape: it has a mandatory citation and only `unit`/`citation`/`descriptor` fields.  A valid
uncited single-center assignment (P-93.4.1.1) therefore has no lossless representation there.
This module supplies the missing codec.

## What is relabelled and what is copied

Only the six physical-unit constructors contain atom references.  They are relabelled with
`OrganicStereoSuppliedCitationIngress.relabelUnit` / `unrelabelUnit`.  Everything else is source
nomenclature or source metadata and is copied literally:

* `citation?` keeps `none` as `none` and `some token` as `some token`; no token is invented and
  the `none`/`some` distinction is preserved as an equality, not just up to some projection;
* citation components, prime counts and token keys are naming data, **not** atom indices;
* `component`, `kind` and `descriptor` are copied literally.

## Observations

Every concrete acyclic observation record in `IUPACP93AcyclicAuthorityCarrier` is mirrored
field-for-field with its physical assignments relabelled.  The eleven records are:

1. `P93AcyclicSingleCenterAuthorityObservation` (locant requirement, isotopic-affix presence and
   affix order);
2. `P93AcyclicMultipleCenterDescriptorsAuthorityObservation`;
3. `P93AcyclicPrefixComponentAuthorityObservation` (prefix component position);
4. `P93AcyclicDoubleBondAuthorityObservation` (naming context and carbon context);
5. `P93AcyclicHeteroDoubleBondAuthorityObservation`;
6. `P93AcyclicMultipleDoubleBondAuthorityObservation`;
7. `P93AcyclicEvenCumuleneAuthorityObservation` (general/preferred descriptors and context);
8. `P93AcyclicOddCumuleneAuthorityObservation` (terminal geometry);
9. `P93AcyclicPlacedAssignment`;
10. `P93AcyclicMultipleUnitsAuthorityObservation` (placed assignments plus
    `P93AcyclicNumberingCompetition`);
11. a *bare* `P93AcyclicAuthorityAssignment`: one independently judged unit with its optional
    citation, component, kind and descriptor, and **no** placement or observed-position field.

The bare assignment is the payload shape of the two acyclic source rows (`acyclicCenters` and
`ordinaryDoubleBonds`), whose actual record is a single assignment rather than one of the ten
structured observations.  It introduces no fabricated `observedPosition`: bare validity is exactly
the pre-existing `P93AcyclicAuthorityAssignment.ValidFor`, so no placement requirement is imposed.

They are combined in a tagged sum `AcyclicObservation V policy`.  The sum has one constructor per
pre-existing record type plus the bare assignment, and the codec handles every constructor
explicitly; there is no rejection branch.  The original whole observation is never stored as an opaque payload.  Instead the actual
physical units are reindexed and every other field is passed through transparently, so exact
record recovery is proved field-by-field.

## Bounds and source validity

`P93AuthorityPhysicalUnit.BoundedIn` (re-exported here as `UnitBoundedIn`) is an explicit
hypothesis of the core codec.  Where the source predicate already provides it,
`physicalUnitBoundedIn_of_validFor` derives it from the actual `ValidFor` at the source's own
`atomCount` (the polyhedral case uses the certified spatial length fact, not an assumption).
Nothing assumes that encoding is an inverse: both inverse directions are proved.

## What is not claimed

No chemistry validity oracle, descriptor selection, naming inference or external source approval
is introduced.  A supplied observation is only *decoded* back to the original `Nat`-indexed
record, and validity is consumed at that same source and policy.  In particular this module does
**not** claim that `ValidFor` is invariant under an arbitrary renumbering of `Nat` atom indices:
the `Nat`-ordered constraints (`first < second`, canonical path orientation, ordered `Nodup`) are
not transported.  Every validity statement below is `ValidFor` of the exact decoded record at the
same `source` and `policy`.

The shared source context is the existing molecule-codec binding
`OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding`: the graph, coordinate channel
and diagram channel are tied to the authoritative input by actual equalities, and atom-count
agreement is derived from `encode_atomCount`, never assumed from a count alone.
-/

namespace OrganicStereoP93AcyclicIngress

open BlueBookP93.Acyclic
open TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress
open TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress.P93AuthorityPhysicalUnit

variable {V : Type*} {n : ℕ} {policy : P93AcyclicAuthorityPolicy}

/-- Explicit bound predicate on a physical unit, re-exported under a name that cannot be confused
with the tagged-observation bound below. -/
abbrev UnitBoundedIn (n : ℕ) (unit : P93AuthorityPhysicalUnit) : Prop :=
  TetraStereo.OneCenter.OrganicStereoSuppliedCitationIngress.P93AuthorityPhysicalUnit.BoundedIn
    n unit

/-! ## Assignments with all five fields -/

/-- A P-93 acyclic assignment over an arbitrary finite atom type `V`.

The five fields correspond one-for-one to `P93AcyclicAuthorityAssignment`: the physical unit is
relabelled into `V`, while the optional citation, component, kind and descriptor are source
metadata copied literally. -/
structure SuppliedAcyclicAssignment (V : Type*) (Component : Type*) where
  unit : SuppliedPhysicalUnit V
  citation? : Option P93AuthorityCitationToken
  component : Component
  kind : UnitKind
  descriptor : Descriptor

/-- Relabel the physical unit of one acyclic assignment.  All four non-unit fields are copied
literally. -/
def relabelAcyclicAssignment [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit) :
    SuppliedAcyclicAssignment V policy.Component where
  unit := relabelUnit e assignment.unit bounded
  citation? := assignment.citation?
  component := assignment.component
  kind := assignment.kind
  descriptor := assignment.descriptor

/-- Decode a supplied acyclic assignment to the raw carrier assignment. -/
def unrelabelAcyclicAssignment [DecidableEq V] (e : V ≃ Fin n)
    (assignment : SuppliedAcyclicAssignment V policy.Component) :
    P93AcyclicAuthorityAssignment policy where
  unit := unrelabelUnit e assignment.unit
  citation? := assignment.citation?
  component := assignment.component
  kind := assignment.kind
  descriptor := assignment.descriptor

/-! ### Fieldwise preservation -/

@[simp] theorem relabelAcyclicAssignment_unit [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit) :
    (relabelAcyclicAssignment e assignment bounded).unit =
      relabelUnit e assignment.unit bounded := rfl

@[simp] theorem relabelAcyclicAssignment_citation? [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit) :
    (relabelAcyclicAssignment e assignment bounded).citation? =
      assignment.citation? := rfl

@[simp] theorem relabelAcyclicAssignment_component [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit) :
    (relabelAcyclicAssignment e assignment bounded).component =
      assignment.component := rfl

@[simp] theorem relabelAcyclicAssignment_kind [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit) :
    (relabelAcyclicAssignment e assignment bounded).kind = assignment.kind := rfl

@[simp] theorem relabelAcyclicAssignment_descriptor [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit) :
    (relabelAcyclicAssignment e assignment bounded).descriptor =
      assignment.descriptor := rfl

@[simp] theorem unrelabelAcyclicAssignment_unit [DecidableEq V] (e : V ≃ Fin n)
    (assignment : SuppliedAcyclicAssignment V policy.Component) :
    (unrelabelAcyclicAssignment e assignment).unit =
      unrelabelUnit e assignment.unit := rfl

@[simp] theorem unrelabelAcyclicAssignment_citation? [DecidableEq V] (e : V ≃ Fin n)
    (assignment : SuppliedAcyclicAssignment V policy.Component) :
    (unrelabelAcyclicAssignment e assignment).citation? =
      assignment.citation? := rfl

@[simp] theorem unrelabelAcyclicAssignment_component [DecidableEq V] (e : V ≃ Fin n)
    (assignment : SuppliedAcyclicAssignment V policy.Component) :
    (unrelabelAcyclicAssignment e assignment).component =
      assignment.component := rfl

@[simp] theorem unrelabelAcyclicAssignment_kind [DecidableEq V] (e : V ≃ Fin n)
    (assignment : SuppliedAcyclicAssignment V policy.Component) :
    (unrelabelAcyclicAssignment e assignment).kind = assignment.kind := rfl

@[simp] theorem unrelabelAcyclicAssignment_descriptor [DecidableEq V] (e : V ≃ Fin n)
    (assignment : SuppliedAcyclicAssignment V policy.Component) :
    (unrelabelAcyclicAssignment e assignment).descriptor =
      assignment.descriptor := rfl

/-- The optional citation is preserved exactly: absence stays absence. -/
theorem relabelAcyclicAssignment_citation?_eq_none_iff [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit) :
    (relabelAcyclicAssignment e assignment bounded).citation? = none ↔
      assignment.citation? = none := by
  rw [relabelAcyclicAssignment_citation?]

/-- The optional citation is preserved exactly: a present token is neither dropped nor replaced. -/
theorem relabelAcyclicAssignment_citation?_eq_some_iff [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit)
    (token : P93AuthorityCitationToken) :
    (relabelAcyclicAssignment e assignment bounded).citation? = some token ↔
      assignment.citation? = some token := by
  rw [relabelAcyclicAssignment_citation?]

/-- Citation token keys (values and prime counts) are naming data, not atom indices, and are
preserved literally. -/
theorem relabelAcyclicAssignment_citationKey [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit) :
    (relabelAcyclicAssignment e assignment bounded).citation?.map
        P93AuthorityCitationToken.key =
      assignment.citation?.map P93AuthorityCitationToken.key := by
  rw [relabelAcyclicAssignment_citation?]

/-- Citation components are preserved literally, in order and multiplicity. -/
theorem relabelAcyclicAssignment_citationComponents [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit) :
    (relabelAcyclicAssignment e assignment bounded).citation?.map
        (fun token => token.components) =
      assignment.citation?.map (fun token => token.components) := by
  rw [relabelAcyclicAssignment_citation?]

/-! ### Assignment inverse -/

/-- Exact recovery of one acyclic assignment, including `none`/`some` citation shape,
component, kind and descriptor. -/
theorem unrelabelAcyclicAssignment_relabelAcyclicAssignment [DecidableEq V]
    (e : V ≃ Fin n) (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit) :
    unrelabelAcyclicAssignment e (relabelAcyclicAssignment e assignment bounded) =
      assignment := by
  rcases assignment with ⟨unit, citation?, component, kind, descriptor⟩
  simp [unrelabelAcyclicAssignment, relabelAcyclicAssignment,
    unrelabelUnit_relabelUnit]

/-- Relabelling a decoded assignment returns the supplied assignment.  This is a representation
inverse and needs no source validity. -/
theorem relabelAcyclicAssignment_unrelabelAcyclicAssignment [DecidableEq V]
    (e : V ≃ Fin n) (assignment : SuppliedAcyclicAssignment V policy.Component) :
    relabelAcyclicAssignment e (unrelabelAcyclicAssignment e assignment)
        (unrelabelUnitBounded e assignment.unit) = assignment := by
  rcases assignment with ⟨unit, citation?, component, kind, descriptor⟩
  simp [unrelabelAcyclicAssignment, relabelAcyclicAssignment,
    relabelUnit_unrelabelUnit]

/-! ## Ordered assignment lists -/

/-- Relabel an ordered list of bounded acyclic assignments.  Order and multiplicity, and the
optional citation of every entry, are preserved. -/
def relabelAcyclicAssignments [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (P93AcyclicAuthorityAssignment policy))
    (bounded : ∀ assignment ∈ assignments, UnitBoundedIn n assignment.unit) :
    List (SuppliedAcyclicAssignment V policy.Component) :=
  assignments.attach.map fun assignment =>
    relabelAcyclicAssignment e assignment.1 (bounded assignment.1 assignment.2)

/-- Decode an ordered list of supplied acyclic assignments. -/
def unrelabelAcyclicAssignments [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (SuppliedAcyclicAssignment V policy.Component)) :
    List (P93AcyclicAuthorityAssignment policy) :=
  assignments.map (unrelabelAcyclicAssignment e)

/-- Every decoded assignment in a list satisfies the same explicit bounds. -/
def unrelabelAcyclicAssignmentsBounded [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (SuppliedAcyclicAssignment V policy.Component)) :
    ∀ assignment ∈ unrelabelAcyclicAssignments e assignments,
      UnitBoundedIn n assignment.unit := by
  intro assignment member
  rw [unrelabelAcyclicAssignments, List.mem_map] at member
  rcases member with ⟨supplied, _suppliedMember, rfl⟩
  exact unrelabelUnitBounded e supplied.unit

@[simp] theorem relabelAcyclicAssignments_length [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (P93AcyclicAuthorityAssignment policy))
    (bounded : ∀ assignment ∈ assignments, UnitBoundedIn n assignment.unit) :
    (relabelAcyclicAssignments e assignments bounded).length =
      assignments.length := by
  simp [relabelAcyclicAssignments]

@[simp] theorem unrelabelAcyclicAssignments_length [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (SuppliedAcyclicAssignment V policy.Component)) :
    (unrelabelAcyclicAssignments e assignments).length = assignments.length := by
  simp [unrelabelAcyclicAssignments]

/-- Exact recovery of the ordered assignment list, including order, multiplicity and every
optional citation. -/
theorem unrelabelAcyclicAssignments_relabelAcyclicAssignments [DecidableEq V]
    (e : V ≃ Fin n) (assignments : List (P93AcyclicAuthorityAssignment policy))
    (bounded : ∀ assignment ∈ assignments, UnitBoundedIn n assignment.unit) :
    unrelabelAcyclicAssignments e (relabelAcyclicAssignments e assignments bounded) =
      assignments := by
  unfold unrelabelAcyclicAssignments relabelAcyclicAssignments
  rw [List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact unrelabelAcyclicAssignment_relabelAcyclicAssignment e assignment.1
      (bounded assignment.1 assignment.2)
  · exact List.attach_map_subtype_val assignments

/-- Relabelling a decoded assignment list returns the supplied list. -/
theorem relabelAcyclicAssignments_unrelabelAcyclicAssignments [DecidableEq V]
    (e : V ≃ Fin n)
    (assignments : List (SuppliedAcyclicAssignment V policy.Component)) :
    relabelAcyclicAssignments e (unrelabelAcyclicAssignments e assignments)
        (unrelabelAcyclicAssignmentsBounded e assignments) = assignments := by
  unfold relabelAcyclicAssignments unrelabelAcyclicAssignments
  rw [List.attach_map, List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro assignment _
    exact relabelAcyclicAssignment_unrelabelAcyclicAssignment e assignment.1
  · exact List.attach_map_subtype_val assignments

/-! ## Bounds from the actual physical-unit source predicate -/

/-- Bounds of a physical unit follow from its actual `ValidFor` at the source's own atom count.
The polyhedral case uses the certified spatial-length fact, supplied by the source binding, and
actual coordinate incidence; nothing is assumed. -/
theorem physicalUnitBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (observationPolicy : P93AuthorityPhysicalObservationPolicy)
    (unit : P93AuthorityPhysicalUnit)
    (valid : unit.ValidFor observationPolicy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    UnitBoundedIn source.molecule.atomCount unit := by
  cases unit with
  | atomCenter center =>
      simpa [UnitBoundedIn] using valid.1
  | bond first second =>
      exact ⟨valid.1, valid.2.1⟩
  | axis path =>
      simpa [UnitBoundedIn, P93AuthorityAtomsBounded] using
        valid.2.1
  | plane members =>
      rcases valid with ⟨frame, frameValid, _observationPolicy⟩
      rcases frameValid with ⟨setEq, _length, _nodup, bounded, _rest⟩
      intro atom member
      have listMember : atom ∈ frame.record.planeAtoms := by
        rw [← List.mem_toFinset, setEq]
        exact member
      exact bounded atom (by simp [listMember])
  | helix path =>
      rcases valid with ⟨frame, frameValid, _observationPolicy⟩
      rcases frameValid with ⟨pathEq, _descriptor, _length, bounded, _rest⟩
      intro atom member
      exact bounded atom
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  | polyhedron center positions =>
      rcases valid with ⟨geometry, frame, frameValid, _observationPolicy⟩
      rcases frameValid with
        ⟨centerEq, ligandSetEq, _ligandNodup, _geometryEq, _recognized,
          sourceSpatial, centerPointAt, positionsAt, _arity, _incidence, _roles,
          _orientation⟩
      have fits := spatialFits_of_wf
        source spatialWellFormed frame.spatial sourceSpatial
      refine ⟨?_, ?_⟩
      · have centerPointAt' :
            BlueBookP94.CoordinateRing.SpatialPointAt frame.spatial
              frame.record.center frame.centerPoint :=
          centerEq.symm ▸ centerPointAt
        rw [← centerEq]
        exact fits ▸
          OrganicStereoP93PhysicalFrameIngress.lt_length_of_spatialPointAt centerPointAt'
      · intro atom member
        have ligandMember : atom ∈ frame.record.ligands := by
          rw [← List.mem_toFinset, ligandSetEq]
          exact member
        exact fits ▸
          OrganicStereoP93PhysicalFrameIngress.spatialPointsAt_mem_lt
            frame.spatial positionsAt atom ligandMember

/-- The physical unit inside a valid acyclic assignment is bounded by the source atom count. -/
theorem assignmentUnitBoundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (valid : assignment.ValidFor policy source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    UnitBoundedIn source.molecule.atomCount assignment.unit :=
  physicalUnitBoundedIn_of_validFor source policy.physicalObservation
    assignment.unit valid.1 spatialWellFormed

/-! ## Supplied mirror records for every existing acyclic observation -/

/-- Mirror of `P93AcyclicSingleCenterAuthorityObservation`.  The locant requirement, isotopic
affix presence and the complete ordered affix list are copied literally. -/
structure SuppliedSingleCenterAuthorityObservation (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : SuppliedAcyclicAssignment V policy.Component
  centerNeedsLocantInBaseName : Bool
  isotopicAffixPresent : Bool
  observedAffixOrder : List AffixKind

/-- Mirror of `P93AcyclicMultipleCenterDescriptorsAuthorityObservation`. -/
structure SuppliedMultipleCenterDescriptorsAuthorityObservation (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignments : List (SuppliedAcyclicAssignment V policy.Component)

/-- Mirror of `P93AcyclicPrefixComponentAuthorityObservation`.  The observed citation position,
including any component reference, is copied literally. -/
structure SuppliedPrefixComponentAuthorityObservation (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : SuppliedAcyclicAssignment V policy.Component
  observedPosition : CitationPosition policy.Component

/-- Mirror of `P93AcyclicDoubleBondAuthorityObservation`. -/
structure SuppliedDoubleBondAuthorityObservation (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : SuppliedAcyclicAssignment V policy.Component
  context : NomenclatureContext
  carbonContext : CarbonDoubleBondContext

/-- Mirror of `P93AcyclicHeteroDoubleBondAuthorityObservation`. -/
structure SuppliedHeteroDoubleBondAuthorityObservation (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : SuppliedAcyclicAssignment V policy.Component
  context : NomenclatureContext

/-- Mirror of `P93AcyclicMultipleDoubleBondAuthorityObservation`. -/
structure SuppliedMultipleDoubleBondAuthorityObservation (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignments : List (SuppliedAcyclicAssignment V policy.Component)

/-- Mirror of `P93AcyclicEvenCumuleneAuthorityObservation`. -/
structure SuppliedEvenCumuleneAuthorityObservation (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : SuppliedAcyclicAssignment V policy.Component
  context : NomenclatureContext
  generalDescriptor : Descriptor
  preferredDescriptor : Descriptor

/-- Mirror of `P93AcyclicOddCumuleneAuthorityObservation`. -/
structure SuppliedOddCumuleneAuthorityObservation (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : SuppliedAcyclicAssignment V policy.Component
  geometry : OddCumuleneTerminalGeometry

/-- Mirror of `P93AcyclicPlacedAssignment`. -/
structure SuppliedPlacedAssignment (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignment : SuppliedAcyclicAssignment V policy.Component
  observedPosition : CitationPosition policy.Component

/-- Mirror of `P93AcyclicMultipleUnitsAuthorityObservation`: placed assignments together with the
audited `P93AcyclicNumberingCompetition`. -/
structure SuppliedMultipleUnitsAuthorityObservation (V : Type*)
    (policy : P93AcyclicAuthorityPolicy) where
  assignments : List (SuppliedPlacedAssignment V policy)
  numberingCompetition : P93AcyclicNumberingCompetition

/-! ## Tagged sums over the pre-existing records -/

/-- The native tagged payload: exactly one of the ten pre-existing acyclic observation shapes, or a
bare acyclic assignment (an independently judged unit with no placement field). -/
inductive AcyclicObservation (V : Type*) (policy : P93AcyclicAuthorityPolicy) where
  | singleCenter (observation : SuppliedSingleCenterAuthorityObservation V policy)
  | multipleCenterDescriptors
      (observation : SuppliedMultipleCenterDescriptorsAuthorityObservation V policy)
  | prefixComponent (observation : SuppliedPrefixComponentAuthorityObservation V policy)
  | doubleBond (observation : SuppliedDoubleBondAuthorityObservation V policy)
  | heteroDoubleBond (observation : SuppliedHeteroDoubleBondAuthorityObservation V policy)
  | multipleDoubleBond
      (observation : SuppliedMultipleDoubleBondAuthorityObservation V policy)
  | evenCumulene (observation : SuppliedEvenCumuleneAuthorityObservation V policy)
  | oddCumulene (observation : SuppliedOddCumuleneAuthorityObservation V policy)
  | placedAssignment (observation : SuppliedPlacedAssignment V policy)
  | multipleUnits (observation : SuppliedMultipleUnitsAuthorityObservation V policy)
  | bareAssignment (assignment : SuppliedAcyclicAssignment V policy.Component)

/-- The source-side tagged sum: exactly the pre-existing carrier records, plus the bare acyclic
assignment used by the two single-assignment acyclic rows. -/
inductive SourceAcyclicObservation (policy : P93AcyclicAuthorityPolicy) where
  | singleCenter (observation : P93AcyclicSingleCenterAuthorityObservation policy)
  | multipleCenterDescriptors
      (observation : P93AcyclicMultipleCenterDescriptorsAuthorityObservation policy)
  | prefixComponent (observation : P93AcyclicPrefixComponentAuthorityObservation policy)
  | doubleBond (observation : P93AcyclicDoubleBondAuthorityObservation policy)
  | heteroDoubleBond (observation : P93AcyclicHeteroDoubleBondAuthorityObservation policy)
  | multipleDoubleBond
      (observation : P93AcyclicMultipleDoubleBondAuthorityObservation policy)
  | evenCumulene (observation : P93AcyclicEvenCumuleneAuthorityObservation policy)
  | oddCumulene (observation : P93AcyclicOddCumuleneAuthorityObservation policy)
  | placedAssignment (observation : P93AcyclicPlacedAssignment policy)
  | multipleUnits (observation : P93AcyclicMultipleUnitsAuthorityObservation policy)
  | bareAssignment (assignment : P93AcyclicAuthorityAssignment policy)

/-! ## Bounds for tagged observations -/

/-- Every assignment in an ordered list has a bounded physical unit. -/
def assignmentsBoundedIn (n : ℕ)
    (assignments : List (P93AcyclicAuthorityAssignment policy)) : Prop :=
  ∀ assignment ∈ assignments, UnitBoundedIn n assignment.unit

/-- Explicit physical-unit bounds for a tagged source observation. -/
def SourceAcyclicObservation.BoundedIn (n : ℕ) :
    SourceAcyclicObservation policy → Prop
  | .singleCenter observation => UnitBoundedIn n observation.assignment.unit
  | .multipleCenterDescriptors observation =>
      assignmentsBoundedIn n observation.assignments
  | .prefixComponent observation => UnitBoundedIn n observation.assignment.unit
  | .doubleBond observation => UnitBoundedIn n observation.assignment.unit
  | .heteroDoubleBond observation => UnitBoundedIn n observation.assignment.unit
  | .multipleDoubleBond observation =>
      assignmentsBoundedIn n observation.assignments
  | .evenCumulene observation => UnitBoundedIn n observation.assignment.unit
  | .oddCumulene observation => UnitBoundedIn n observation.assignment.unit
  | .placedAssignment observation => UnitBoundedIn n observation.assignment.unit
  | .multipleUnits observation =>
      ∀ placed ∈ observation.assignments, UnitBoundedIn n placed.assignment.unit
  | .bareAssignment assignment => UnitBoundedIn n assignment.unit

/-! ## Placed-assignment lists -/

/-- Relabel an ordered list of placed assignments, retaining each observed citation position. -/
def relabelPlacedAssignments [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (P93AcyclicPlacedAssignment policy))
    (bounded : ∀ placed ∈ assignments, UnitBoundedIn n placed.assignment.unit) :
    List (SuppliedPlacedAssignment V policy) :=
  assignments.attach.map fun placed =>
    { assignment := relabelAcyclicAssignment e placed.1.assignment
        (bounded placed.1 placed.2)
      observedPosition := placed.1.observedPosition }

/-- Decode an ordered list of supplied placed assignments. -/
def unrelabelPlacedAssignments [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (SuppliedPlacedAssignment V policy)) :
    List (P93AcyclicPlacedAssignment policy) :=
  assignments.map fun placed =>
    { assignment := unrelabelAcyclicAssignment e placed.assignment
      observedPosition := placed.observedPosition }

/-- Every decoded placed assignment satisfies the same explicit bounds. -/
def unrelabelPlacedAssignmentsBounded [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (SuppliedPlacedAssignment V policy)) :
    ∀ placed ∈ unrelabelPlacedAssignments e assignments,
      UnitBoundedIn n placed.assignment.unit := by
  intro placed member
  rw [unrelabelPlacedAssignments, List.mem_map] at member
  rcases member with ⟨supplied, _suppliedMember, rfl⟩
  exact unrelabelUnitBounded e supplied.assignment.unit

@[simp] theorem relabelPlacedAssignments_length [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (P93AcyclicPlacedAssignment policy))
    (bounded : ∀ placed ∈ assignments, UnitBoundedIn n placed.assignment.unit) :
    (relabelPlacedAssignments e assignments bounded).length =
      assignments.length := by
  simp [relabelPlacedAssignments]

@[simp] theorem unrelabelPlacedAssignments_length [DecidableEq V] (e : V ≃ Fin n)
    (assignments : List (SuppliedPlacedAssignment V policy)) :
    (unrelabelPlacedAssignments e assignments).length = assignments.length := by
  simp [unrelabelPlacedAssignments]

/-- Exact recovery of the ordered placed-assignment list. -/
theorem unrelabelPlacedAssignments_relabelPlacedAssignments [DecidableEq V]
    (e : V ≃ Fin n) (assignments : List (P93AcyclicPlacedAssignment policy))
    (bounded : ∀ placed ∈ assignments, UnitBoundedIn n placed.assignment.unit) :
    unrelabelPlacedAssignments e (relabelPlacedAssignments e assignments bounded) =
      assignments := by
  unfold unrelabelPlacedAssignments relabelPlacedAssignments
  rw [List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro placed _
    rcases placed with ⟨placed, _member⟩
    simp [unrelabelAcyclicAssignment_relabelAcyclicAssignment]
  · exact List.attach_map_subtype_val assignments

/-- Relabelling a decoded placed-assignment list returns the supplied list. -/
theorem relabelPlacedAssignments_unrelabelPlacedAssignments [DecidableEq V]
    (e : V ≃ Fin n)
    (assignments : List (SuppliedPlacedAssignment V policy)) :
    relabelPlacedAssignments e (unrelabelPlacedAssignments e assignments)
        (unrelabelPlacedAssignmentsBounded e assignments) = assignments := by
  unfold relabelPlacedAssignments unrelabelPlacedAssignments
  rw [List.attach_map, List.map_map]
  trans assignments.attach.map Subtype.val
  · apply List.map_congr_left
    intro placed _
    rcases placed with ⟨placed, _member⟩
    simp [relabelAcyclicAssignment_unrelabelAcyclicAssignment]
  · exact List.attach_map_subtype_val assignments

/-! ## Observation codec -/

/-- Relabel one tagged source observation.  Physical units are reindexed; every other field is
copied literally. -/
def relabelObservation [DecidableEq V] (e : V ≃ Fin n) :
    (observation : SourceAcyclicObservation policy) →
      observation.BoundedIn n → AcyclicObservation V policy
  | .singleCenter observation, bounded =>
      .singleCenter
        { assignment := relabelAcyclicAssignment e observation.assignment bounded
          centerNeedsLocantInBaseName := observation.centerNeedsLocantInBaseName
          isotopicAffixPresent := observation.isotopicAffixPresent
          observedAffixOrder := observation.observedAffixOrder }
  | .multipleCenterDescriptors observation, bounded =>
      .multipleCenterDescriptors
        { assignments := relabelAcyclicAssignments e observation.assignments bounded }
  | .prefixComponent observation, bounded =>
      .prefixComponent
        { assignment := relabelAcyclicAssignment e observation.assignment bounded
          observedPosition := observation.observedPosition }
  | .doubleBond observation, bounded =>
      .doubleBond
        { assignment := relabelAcyclicAssignment e observation.assignment bounded
          context := observation.context
          carbonContext := observation.carbonContext }
  | .heteroDoubleBond observation, bounded =>
      .heteroDoubleBond
        { assignment := relabelAcyclicAssignment e observation.assignment bounded
          context := observation.context }
  | .multipleDoubleBond observation, bounded =>
      .multipleDoubleBond
        { assignments := relabelAcyclicAssignments e observation.assignments bounded }
  | .evenCumulene observation, bounded =>
      .evenCumulene
        { assignment := relabelAcyclicAssignment e observation.assignment bounded
          context := observation.context
          generalDescriptor := observation.generalDescriptor
          preferredDescriptor := observation.preferredDescriptor }
  | .oddCumulene observation, bounded =>
      .oddCumulene
        { assignment := relabelAcyclicAssignment e observation.assignment bounded
          geometry := observation.geometry }
  | .placedAssignment observation, bounded =>
      .placedAssignment
        { assignment := relabelAcyclicAssignment e observation.assignment bounded
          observedPosition := observation.observedPosition }
  | .multipleUnits observation, bounded =>
      .multipleUnits
        { assignments := relabelPlacedAssignments e observation.assignments bounded
          numberingCompetition := observation.numberingCompetition }
  | .bareAssignment assignment, bounded =>
      .bareAssignment (relabelAcyclicAssignment e assignment bounded)

/-- Decode one tagged observation to the exact pre-existing carrier record. -/
def unrelabelObservation [DecidableEq V] (e : V ≃ Fin n) :
    AcyclicObservation V policy → SourceAcyclicObservation policy
  | .singleCenter observation =>
      .singleCenter
        { assignment := unrelabelAcyclicAssignment e observation.assignment
          centerNeedsLocantInBaseName := observation.centerNeedsLocantInBaseName
          isotopicAffixPresent := observation.isotopicAffixPresent
          observedAffixOrder := observation.observedAffixOrder }
  | .multipleCenterDescriptors observation =>
      .multipleCenterDescriptors
        { assignments := unrelabelAcyclicAssignments e observation.assignments }
  | .prefixComponent observation =>
      .prefixComponent
        { assignment := unrelabelAcyclicAssignment e observation.assignment
          observedPosition := observation.observedPosition }
  | .doubleBond observation =>
      .doubleBond
        { assignment := unrelabelAcyclicAssignment e observation.assignment
          context := observation.context
          carbonContext := observation.carbonContext }
  | .heteroDoubleBond observation =>
      .heteroDoubleBond
        { assignment := unrelabelAcyclicAssignment e observation.assignment
          context := observation.context }
  | .multipleDoubleBond observation =>
      .multipleDoubleBond
        { assignments := unrelabelAcyclicAssignments e observation.assignments }
  | .evenCumulene observation =>
      .evenCumulene
        { assignment := unrelabelAcyclicAssignment e observation.assignment
          context := observation.context
          generalDescriptor := observation.generalDescriptor
          preferredDescriptor := observation.preferredDescriptor }
  | .oddCumulene observation =>
      .oddCumulene
        { assignment := unrelabelAcyclicAssignment e observation.assignment
          geometry := observation.geometry }
  | .placedAssignment observation =>
      .placedAssignment
        { assignment := unrelabelAcyclicAssignment e observation.assignment
          observedPosition := observation.observedPosition }
  | .multipleUnits observation =>
      .multipleUnits
        { assignments := unrelabelPlacedAssignments e observation.assignments
          numberingCompetition := observation.numberingCompetition }
  | .bareAssignment assignment =>
      .bareAssignment (unrelabelAcyclicAssignment e assignment)

/-! ## Inverse on the source side -/

/-- Exact recovery of every existing acyclic observation record.  This theorem is the total
constructor-by-constructor claim: no observation shape is rejected, and no original record is
stored as a payload. -/
theorem unrelabelObservation_relabelObservation [DecidableEq V] (e : V ≃ Fin n)
    (observation : SourceAcyclicObservation policy)
    (bounded : observation.BoundedIn n) :
    unrelabelObservation e (relabelObservation e observation bounded) = observation := by
  cases observation with
  | singleCenter observation =>
      rcases observation with ⟨assignment, needsLocant, isotopicPresent, affixOrder⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelAcyclicAssignment_relabelAcyclicAssignment]
  | multipleCenterDescriptors observation =>
      rcases observation with ⟨assignments⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelAcyclicAssignments_relabelAcyclicAssignments]
  | prefixComponent observation =>
      rcases observation with ⟨assignment, position⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelAcyclicAssignment_relabelAcyclicAssignment]
  | doubleBond observation =>
      rcases observation with ⟨assignment, context, carbonContext⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelAcyclicAssignment_relabelAcyclicAssignment]
  | heteroDoubleBond observation =>
      rcases observation with ⟨assignment, context⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelAcyclicAssignment_relabelAcyclicAssignment]
  | multipleDoubleBond observation =>
      rcases observation with ⟨assignments⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelAcyclicAssignments_relabelAcyclicAssignments]
  | evenCumulene observation =>
      rcases observation with ⟨assignment, context, generalDescriptor,
        preferredDescriptor⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelAcyclicAssignment_relabelAcyclicAssignment]
  | oddCumulene observation =>
      rcases observation with ⟨assignment, geometry⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelAcyclicAssignment_relabelAcyclicAssignment]
  | placedAssignment observation =>
      rcases observation with ⟨assignment, position⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelAcyclicAssignment_relabelAcyclicAssignment]
  | multipleUnits observation =>
      rcases observation with ⟨assignments, competition⟩
      simp [relabelObservation, unrelabelObservation,
        unrelabelPlacedAssignments_relabelPlacedAssignments]
  | bareAssignment assignment =>
      simp [relabelObservation, unrelabelObservation,
        unrelabelAcyclicAssignment_relabelAcyclicAssignment]

/-! ## Inverse on the supplied side -/

/-- Bounds of a decoded tagged observation. -/
def unrelabelObservationBounded [DecidableEq V] (e : V ≃ Fin n) :
    (observation : AcyclicObservation V policy) →
      (unrelabelObservation e observation).BoundedIn n
  | .singleCenter observation => unrelabelUnitBounded e observation.assignment.unit
  | .multipleCenterDescriptors observation =>
      unrelabelAcyclicAssignmentsBounded e observation.assignments
  | .prefixComponent observation => unrelabelUnitBounded e observation.assignment.unit
  | .doubleBond observation => unrelabelUnitBounded e observation.assignment.unit
  | .heteroDoubleBond observation => unrelabelUnitBounded e observation.assignment.unit
  | .multipleDoubleBond observation =>
      unrelabelAcyclicAssignmentsBounded e observation.assignments
  | .evenCumulene observation => unrelabelUnitBounded e observation.assignment.unit
  | .oddCumulene observation => unrelabelUnitBounded e observation.assignment.unit
  | .placedAssignment observation => unrelabelUnitBounded e observation.assignment.unit
  | .multipleUnits observation =>
      unrelabelPlacedAssignmentsBounded e observation.assignments
  | .bareAssignment assignment =>
      unrelabelUnitBounded e assignment.unit

/-- Relabelling a decoded tagged observation returns the supplied observation.  This is the
native representation inverse and requires no source validity. -/
theorem relabelObservation_unrelabelObservation [DecidableEq V] (e : V ≃ Fin n)
    (observation : AcyclicObservation V policy) :
    relabelObservation e (unrelabelObservation e observation)
        (unrelabelObservationBounded e observation) = observation := by
  cases observation with
  | singleCenter observation =>
      rcases observation with ⟨assignment, needsLocant, isotopicPresent, affixOrder⟩
      simp [relabelObservation, unrelabelObservation,
        relabelAcyclicAssignment_unrelabelAcyclicAssignment]
  | multipleCenterDescriptors observation =>
      rcases observation with ⟨assignments⟩
      simp [relabelObservation, unrelabelObservation,
        relabelAcyclicAssignments_unrelabelAcyclicAssignments]
  | prefixComponent observation =>
      rcases observation with ⟨assignment, position⟩
      simp [relabelObservation, unrelabelObservation,
        relabelAcyclicAssignment_unrelabelAcyclicAssignment]
  | doubleBond observation =>
      rcases observation with ⟨assignment, context, carbonContext⟩
      simp [relabelObservation, unrelabelObservation,
        relabelAcyclicAssignment_unrelabelAcyclicAssignment]
  | heteroDoubleBond observation =>
      rcases observation with ⟨assignment, context⟩
      simp [relabelObservation, unrelabelObservation,
        relabelAcyclicAssignment_unrelabelAcyclicAssignment]
  | multipleDoubleBond observation =>
      rcases observation with ⟨assignments⟩
      simp [relabelObservation, unrelabelObservation,
        relabelAcyclicAssignments_unrelabelAcyclicAssignments]
  | evenCumulene observation =>
      rcases observation with ⟨assignment, context, generalDescriptor,
        preferredDescriptor⟩
      simp [relabelObservation, unrelabelObservation,
        relabelAcyclicAssignment_unrelabelAcyclicAssignment]
  | oddCumulene observation =>
      rcases observation with ⟨assignment, geometry⟩
      simp [relabelObservation, unrelabelObservation,
        relabelAcyclicAssignment_unrelabelAcyclicAssignment]
  | placedAssignment observation =>
      rcases observation with ⟨assignment, position⟩
      simp [relabelObservation, unrelabelObservation,
        relabelAcyclicAssignment_unrelabelAcyclicAssignment]
  | multipleUnits observation =>
      rcases observation with ⟨assignments, competition⟩
      simp [relabelObservation, unrelabelObservation,
        relabelPlacedAssignments_unrelabelPlacedAssignments]
  | bareAssignment assignment =>
      simp [relabelObservation, unrelabelObservation,
        relabelAcyclicAssignment_unrelabelAcyclicAssignment]

/-! ## The bare-assignment constructor

The two single-assignment acyclic rows carry a `P93AcyclicAuthorityAssignment` directly.  The
`bareAssignment` constructor represents exactly that record: no placement field is fabricated, and
validity is the pre-existing assignment predicate. -/

/-- The bound of a bare tagged observation is exactly the bound of its assignment's physical
unit. -/
@[simp] theorem SourceAcyclicObservation.bareAssignment_boundedIn (n : ℕ)
    (assignment : P93AcyclicAuthorityAssignment policy) :
    (SourceAcyclicObservation.bareAssignment assignment).BoundedIn n =
      UnitBoundedIn n assignment.unit := rfl

/-- Relabelling a bare source assignment produces the bare native assignment. -/
@[simp] theorem relabelObservation_bareAssignment [DecidableEq V] (e : V ≃ Fin n)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit) :
    relabelObservation e (.bareAssignment assignment) bounded =
      .bareAssignment (relabelAcyclicAssignment e assignment bounded) := rfl

/-- Decoding a bare native assignment produces the bare source assignment. -/
@[simp] theorem unrelabelObservation_bareAssignment [DecidableEq V] (e : V ≃ Fin n)
    (assignment : SuppliedAcyclicAssignment V policy.Component) :
    unrelabelObservation e (.bareAssignment assignment) =
      .bareAssignment (unrelabelAcyclicAssignment e assignment) := rfl

/-- A genuine bare-assignment inverse specialization: the full tagged round trip at the bare
constructor recovers the exact assignment, including its optional citation, component, kind and
descriptor. -/
theorem unrelabelObservation_bareAssignment_relabelObservation [DecidableEq V]
    (e : V ≃ Fin n) (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit) :
    unrelabelObservation e (relabelObservation e (.bareAssignment assignment) bounded) =
      .bareAssignment assignment :=
  unrelabelObservation_relabelObservation e (.bareAssignment assignment) bounded

/-- The native-side bare-assignment inverse specialization. -/
theorem relabelObservation_unrelabelObservation_bareAssignment [DecidableEq V]
    (e : V ≃ Fin n) (assignment : SuppliedAcyclicAssignment V policy.Component) :
    relabelObservation e (unrelabelObservation e (.bareAssignment assignment))
        (unrelabelObservationBounded e (.bareAssignment assignment)) =
      .bareAssignment assignment :=
  relabelObservation_unrelabelObservation e (.bareAssignment assignment)

/-! ## Existing validity predicates, consumed at the same source and policy -/

/-- The existing `ValidFor` of each pre-existing record, dispatched on the tag.  This is a
dispatch only: every branch is the record's own pre-existing predicate, and no new validity
oracle is introduced.  `P93AcyclicPlacedAssignment` has no separate predicate in the carrier, so
its branch is the underlying assignment's existing `ValidFor`. -/
def SourceAcyclicObservation.ValidFor (source : AuthoritativeChemicalInput) :
    SourceAcyclicObservation policy → Prop
  | .singleCenter observation =>
      P93AcyclicSingleCenterAuthorityObservation.ValidFor policy source observation
  | .multipleCenterDescriptors observation =>
      P93AcyclicMultipleCenterDescriptorsAuthorityObservation.ValidFor
        policy source observation
  | .prefixComponent observation =>
      P93AcyclicPrefixComponentAuthorityObservation.ValidFor policy source observation
  | .doubleBond observation =>
      P93AcyclicDoubleBondAuthorityObservation.ValidFor policy source observation
  | .heteroDoubleBond observation =>
      P93AcyclicHeteroDoubleBondAuthorityObservation.ValidFor policy source observation
  | .multipleDoubleBond observation =>
      P93AcyclicMultipleDoubleBondAuthorityObservation.ValidFor
        policy source observation
  | .evenCumulene observation =>
      P93AcyclicEvenCumuleneAuthorityObservation.ValidFor policy source observation
  | .oddCumulene observation =>
      P93AcyclicOddCumuleneAuthorityObservation.ValidFor policy source observation
  | .placedAssignment observation =>
      P93AcyclicAuthorityAssignment.ValidFor policy source observation.assignment
  | .multipleUnits observation =>
      P93AcyclicMultipleUnitsAuthorityObservation.ValidFor policy source observation
  | .bareAssignment assignment =>
      P93AcyclicAuthorityAssignment.ValidFor policy source assignment

/-- Bare validity is the pre-existing assignment validity: no placement or observed-position
requirement is added. -/
@[simp] theorem SourceAcyclicObservation.bareAssignment_validFor
    (source : AuthoritativeChemicalInput)
    (assignment : P93AcyclicAuthorityAssignment policy) :
    (SourceAcyclicObservation.bareAssignment assignment).ValidFor source =
      P93AcyclicAuthorityAssignment.ValidFor policy source assignment := rfl

/-- **Decisive new-case endpoint.**  For a bare acyclic assignment, guarded by its explicit
physical-unit bound and its actual `ValidFor` at the same source and policy, the decode-inverse
round trip is exact, the decoded record satisfies the same bound, validity transports through the
decode, and the source-side bound at `source.molecule.atomCount` is derived from the actual
`ValidFor`.  No `observedPosition` is invented and no placement requirement is imposed. -/
theorem bareAssignment_roundtrip_bounds_validFor [DecidableEq V]
    (e : V ≃ Fin n) (source : AuthoritativeChemicalInput)
    (assignment : P93AcyclicAuthorityAssignment policy)
    (bounded : UnitBoundedIn n assignment.unit)
    (valid : P93AcyclicAuthorityAssignment.ValidFor policy source assignment)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    unrelabelObservation e (relabelObservation e (.bareAssignment assignment) bounded) =
        .bareAssignment assignment ∧
      (unrelabelObservation e (relabelObservation e
        (.bareAssignment assignment) bounded)).BoundedIn n ∧
      ((unrelabelObservation e (relabelObservation e
          (.bareAssignment assignment) bounded)).ValidFor source ↔
        P93AcyclicAuthorityAssignment.ValidFor policy source assignment) ∧
      UnitBoundedIn source.molecule.atomCount assignment.unit := by
  refine ⟨unrelabelObservation_bareAssignment_relabelObservation e assignment bounded,
    ?_, ?_, assignmentUnitBoundedIn_of_validFor source assignment valid spatialWellFormed⟩
  · rw [unrelabelObservation_bareAssignment_relabelObservation]
    exact bounded
  · rw [unrelabelObservation_bareAssignment_relabelObservation]
    exact Iff.rfl

/-- **Validity transport through the exact decode.**  For every tagged observation, the decoded
record's `ValidFor` at the same `source` and `policy` is equivalent to the original record's
`ValidFor`.  The equivalence is the record equality, not an invariance claim about renumbering. -/
theorem validFor_unrelabelObservation_relabelObservation_iff [DecidableEq V]
    (e : V ≃ Fin n) (source : AuthoritativeChemicalInput)
    (observation : SourceAcyclicObservation policy)
    (bounded : observation.BoundedIn n) :
    (unrelabelObservation e (relabelObservation e observation bounded)).ValidFor source ↔
      observation.ValidFor source := by
  rw [unrelabelObservation_relabelObservation]

/-- Forward validity preservation at the same source and policy. -/
theorem validFor_of_relabelObservation [DecidableEq V] (e : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    (observation : SourceAcyclicObservation policy)
    (bounded : observation.BoundedIn n)
    (valid : observation.ValidFor source) :
    (unrelabelObservation e (relabelObservation e observation bounded)).ValidFor source :=
  (validFor_unrelabelObservation_relabelObservation_iff e source observation bounded).mpr
    valid

/-- Validity transport for a decoded native observation through a full native round trip. -/
theorem validFor_unrelabelObservation_roundtrip_iff [DecidableEq V] (e : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    (observation : AcyclicObservation V policy) :
    (unrelabelObservation e
        (relabelObservation e (unrelabelObservation e observation)
          (unrelabelObservationBounded e observation))).ValidFor source ↔
      (unrelabelObservation e observation).ValidFor source := by
  rw [relabelObservation_unrelabelObservation]

/-- Bounds derived from the actual `ValidFor` of a tagged source observation. -/
theorem SourceAcyclicObservation.boundedIn_of_validFor
    (source : AuthoritativeChemicalInput)
    (observation : SourceAcyclicObservation policy)
    (valid : observation.ValidFor source)
    (spatialWellFormed : source.SpatialIndicesWellFormed) :
    observation.BoundedIn source.molecule.atomCount := by
  cases observation with
  | singleCenter observation =>
      exact assignmentUnitBoundedIn_of_validFor source
        observation.assignment valid.1 spatialWellFormed
  | multipleCenterDescriptors observation =>
      intro assignment member
      exact assignmentUnitBoundedIn_of_validFor source assignment
        (valid.1.2 assignment member) spatialWellFormed
  | prefixComponent observation =>
      exact assignmentUnitBoundedIn_of_validFor source
        observation.assignment valid.1 spatialWellFormed
  | doubleBond observation =>
      exact assignmentUnitBoundedIn_of_validFor source
        observation.assignment valid.1 spatialWellFormed
  | heteroDoubleBond observation =>
      exact assignmentUnitBoundedIn_of_validFor source
        observation.assignment valid.1 spatialWellFormed
  | multipleDoubleBond observation =>
      intro assignment member
      exact assignmentUnitBoundedIn_of_validFor source assignment
        (valid.1.2 assignment member) spatialWellFormed
  | evenCumulene observation =>
      exact assignmentUnitBoundedIn_of_validFor source
        observation.assignment valid.1 spatialWellFormed
  | oddCumulene observation =>
      exact assignmentUnitBoundedIn_of_validFor source
        observation.assignment valid.1 spatialWellFormed
  | placedAssignment observation =>
      exact assignmentUnitBoundedIn_of_validFor source
        observation.assignment valid spatialWellFormed
  | multipleUnits observation =>
      intro placed member
      exact assignmentUnitBoundedIn_of_validFor source
        placed.assignment (valid.2.1 placed member).1 spatialWellFormed
  | bareAssignment assignment =>
      exact assignmentUnitBoundedIn_of_validFor source assignment valid spatialWellFormed

/-! ## Ordered heterogeneous lists -/

/-- Relabel an ordered heterogeneous list of source observations. -/
def relabelObservationList [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (SourceAcyclicObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    List (AcyclicObservation V policy) :=
  observations.attach.map fun observation =>
    relabelObservation e observation.1 (bounded observation.1 observation.2)

/-- Decode an ordered heterogeneous list of native observations. -/
def unrelabelObservationList [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (AcyclicObservation V policy)) :
    List (SourceAcyclicObservation policy) :=
  observations.map (unrelabelObservation e)

/-- Every decoded element of a heterogeneous list satisfies the same explicit bounds. -/
def unrelabelObservationListBounded [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (AcyclicObservation V policy)) :
    ∀ observation ∈ unrelabelObservationList e observations,
      observation.BoundedIn n := by
  intro observation member
  rw [unrelabelObservationList, List.mem_map] at member
  rcases member with ⟨presented, _presentedMember, rfl⟩
  exact unrelabelObservationBounded e presented

@[simp] theorem relabelObservationList_length [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (SourceAcyclicObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    (relabelObservationList e observations bounded).length = observations.length := by
  simp [relabelObservationList]

@[simp] theorem unrelabelObservationList_length [DecidableEq V] (e : V ≃ Fin n)
    (observations : List (AcyclicObservation V policy)) :
    (unrelabelObservationList e observations).length = observations.length := by
  simp [unrelabelObservationList]

/-- Exact recovery of the ordered heterogeneous observation list, including order, multiplicity
and each concrete record shape. -/
theorem unrelabelObservationList_relabelObservationList [DecidableEq V]
    (e : V ≃ Fin n) (observations : List (SourceAcyclicObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    unrelabelObservationList e (relabelObservationList e observations bounded) =
      observations := by
  unfold unrelabelObservationList relabelObservationList
  rw [List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact unrelabelObservation_relabelObservation e observation.1
      (bounded observation.1 observation.2)
  · exact List.attach_map_subtype_val observations

/-- Relabelling a decoded heterogeneous list returns the supplied list. -/
theorem relabelObservationList_unrelabelObservationList [DecidableEq V]
    (e : V ≃ Fin n) (observations : List (AcyclicObservation V policy)) :
    relabelObservationList e (unrelabelObservationList e observations)
        (unrelabelObservationListBounded e observations) = observations := by
  unfold relabelObservationList unrelabelObservationList
  rw [List.attach_map, List.map_map]
  trans observations.attach.map Subtype.val
  · apply List.map_congr_left
    intro observation _
    exact relabelObservation_unrelabelObservation e observation.1
  · exact List.attach_map_subtype_val observations

/-! ## Correlated sets of observations -/

/-- Image of a set of source observations under the codec. -/
def relabelObservationSet [DecidableEq V] (e : V ≃ Fin n)
    (observations : Set (SourceAcyclicObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    Set (AcyclicObservation V policy) :=
  fun presented =>
    ∃ observation, ∃ member : observation ∈ observations,
      relabelObservation e observation (bounded observation member) = presented

/-- Preimage of a set of native observations under the codec. -/
def unrelabelObservationSet [DecidableEq V] (e : V ≃ Fin n)
    (observations : Set (AcyclicObservation V policy)) :
    Set (SourceAcyclicObservation policy) :=
  fun recovered =>
    ∃ presented ∈ observations,
      unrelabelObservation e presented = recovered

/-- Every decoded element of the image set satisfies the explicit bounds. -/
def unrelabelObservationSetBounded [DecidableEq V] (e : V ≃ Fin n)
    (observations : Set (AcyclicObservation V policy)) :
    ∀ observation ∈ unrelabelObservationSet e observations,
      observation.BoundedIn n := by
  rintro recovered ⟨presented, _presentedMember, rfl⟩
  exact unrelabelObservationBounded e presented

/-- The correlated-set inverse on the source side. -/
theorem unrelabelObservationSet_relabelObservationSet [DecidableEq V]
    (e : V ≃ Fin n) (observations : Set (SourceAcyclicObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n) :
    unrelabelObservationSet e (relabelObservationSet e observations bounded) =
      observations := by
  ext recovered
  constructor
  · rintro ⟨presented, ⟨observation, member, relabelEq⟩, decodeEq⟩
    rw [← relabelEq] at decodeEq
    rw [unrelabelObservation_relabelObservation] at decodeEq
    rw [← decodeEq]
    exact member
  · intro member
    exact ⟨relabelObservation e recovered (bounded recovered member),
      ⟨recovered, member, rfl⟩,
      unrelabelObservation_relabelObservation e recovered (bounded recovered member)⟩

/-- The relabelling of an observation does not inspect the proof of its boundedness. -/
theorem relabelObservation_bound_irrel [DecidableEq V] (e : V ≃ Fin n)
    (observation : SourceAcyclicObservation policy)
    (first second : observation.BoundedIn n) :
    relabelObservation e observation first = relabelObservation e observation second := by
  cases observation <;> rfl

/-- Relabelling respects equality of the underlying source observation, independently of how the
two boundedness proofs were obtained. -/
theorem relabelObservation_congr [DecidableEq V] (e : V ≃ Fin n)
    {first second : SourceAcyclicObservation policy} (h : first = second)
    (firstBounded : first.BoundedIn n) (secondBounded : second.BoundedIn n) :
    relabelObservation e first firstBounded =
      relabelObservation e second secondBounded := by
  cases h
  exact relabelObservation_bound_irrel e _ firstBounded secondBounded

/-- The correlated-set inverse on the native side. -/
theorem relabelObservationSet_unrelabelObservationSet [DecidableEq V]
    (e : V ≃ Fin n) (observations : Set (AcyclicObservation V policy)) :
    relabelObservationSet e (unrelabelObservationSet e observations)
        (unrelabelObservationSetBounded e observations) = observations := by
  ext presented
  constructor
  · rintro ⟨observation, ⟨presented₀, presentedMember, decodeEq⟩, relabelEq⟩
    have obsEq : unrelabelObservation e presented = observation := by
      have := congrArg (unrelabelObservation e) relabelEq.symm
      rwa [unrelabelObservation_relabelObservation] at this
    have decodeEq' : unrelabelObservation e presented₀ =
        unrelabelObservation e presented := by
      rw [decodeEq, ← obsEq]
    have key : relabelObservation e (unrelabelObservation e presented₀)
        (unrelabelObservationBounded e presented₀) = presented := by
      calc
        relabelObservation e (unrelabelObservation e presented₀)
            (unrelabelObservationBounded e presented₀) =
          relabelObservation e (unrelabelObservation e presented)
            (unrelabelObservationBounded e presented) :=
          relabelObservation_congr e decodeEq' _ _
        _ = presented := relabelObservation_unrelabelObservation e presented
    have presentedEq : presented = presented₀ := by
      rw [← key, relabelObservation_unrelabelObservation]
    simpa [presentedEq] using presentedMember
  · intro member
    exact ⟨unrelabelObservation e presented,
      ⟨presented, member, rfl⟩,
      relabelObservation_unrelabelObservation e presented⟩

/-- **Correlated validity for a set.**  A native observation belongs to the image of a set exactly
when its decoded record is one of the source observations; consequently its `ValidFor` at the same
source and policy is exactly the validity of that source observation. -/
theorem validFor_mem_relabelObservationSet_iff [DecidableEq V] (e : V ≃ Fin n)
    (source : AuthoritativeChemicalInput)
    (observations : Set (SourceAcyclicObservation policy))
    (bounded : ∀ observation ∈ observations, observation.BoundedIn n)
    (presented : AcyclicObservation V policy)
    (member : presented ∈ relabelObservationSet e observations bounded) :
    (unrelabelObservation e presented).ValidFor source ↔
      ∃ observation, ∃ observationMember : observation ∈ observations,
        relabelObservation e observation (bounded observation observationMember) =
          presented ∧ observation.ValidFor source := by
  constructor
  · intro valid
    rcases member with ⟨observation, observationMember, relabelEq⟩
    refine ⟨observation, observationMember, relabelEq, ?_⟩
    rw [← relabelEq] at valid
    rwa [unrelabelObservation_relabelObservation] at valid
  · rintro ⟨observation, observationMember, relabelEq, valid⟩
    rw [← relabelEq]
    rwa [unrelabelObservation_relabelObservation]

/-! ## Shared source context and the composable satellite -/

/-- The common source binding: the existing molecule-codec binding from
`OrganicStereoP93PhysicalFrameIngress`.  It ties a shared finite graph, coordinate channel and
diagram channel to the authoritative input by actual equalities. -/
abbrev AcyclicSourceBinding (V : Type*) [DecidableEq V] [Fintype V] :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding V

/-- Bounds of a tagged observation derived from its validity and the exact source binding. -/
theorem SourceAcyclicObservation.boundedIn_of_validFor_binding
    [DecidableEq V] [Fintype V]
    (binding : AcyclicSourceBinding V)
    (observation : SourceAcyclicObservation policy)
    (valid : observation.ValidFor binding.source) :
    observation.BoundedIn (Fintype.card V) := by
  have bounded := SourceAcyclicObservation.boundedIn_of_validFor binding.source
    observation valid binding.spatial_wellFormed
  rwa [binding.atomCount_eq] at bounded

/-- A raw acyclic observation source: the exact source binding plus an ordered list of
`Nat`-indexed carrier observations, each valid at the bound source. -/
structure RawAcyclicObservationSource (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93AcyclicAuthorityPolicy) where
  binding : AcyclicSourceBinding V
  observations : List (SourceAcyclicObservation policy)
  valid : ∀ observation ∈ observations, observation.ValidFor binding.source

/-- The composable native satellite.  It carries the same graph/spatial/diagram context as the
existing molecule codec and the ordered list of native observations.  No original observation and
no original `AuthoritativeChemicalInput` is stored here. -/
structure AcyclicObservationSatellite (V : Type*) [DecidableEq V] [Fintype V]
    (policy : P93AcyclicAuthorityPolicy) where
  graph : FiniteAtomInteractionHypergraph V
  spatial? : Option (V → CartesianPoint3) := none
  diagram? : Option (OrganicDiagramSource V) := none
  observations : List (AcyclicObservation V policy)

namespace AcyclicObservationSatellite

variable [DecidableEq V] [Fintype V]

/-- The shared finite source, with observations intentionally excluded. -/
def toFiniteSource (satellite : AcyclicObservationSatellite V policy) :
    OrganicFiniteSource V where
  graph := satellite.graph
  spatial? := satellite.spatial?
  diagram? := satellite.diagram?

end AcyclicObservationSatellite

/-- Adapt a raw source into the satellite: keep the exact shared finite source and relabel every
observation, deriving the physical-unit bounds from its actual `ValidFor`. -/
def adapt [DecidableEq V] [Fintype V] (raw : RawAcyclicObservationSource V policy) :
    AcyclicObservationSatellite V policy where
  graph := raw.binding.shared.graph
  spatial? := raw.binding.shared.spatial?
  diagram? := raw.binding.shared.diagram?
  observations := raw.observations.attach.map fun observation =>
    relabelObservation raw.binding.enumeration observation.1
      (SourceAcyclicObservation.boundedIn_of_validFor_binding raw.binding observation.1
        (raw.valid observation.1 observation.2))

@[simp] theorem adapt_graph [DecidableEq V] [Fintype V]
    (raw : RawAcyclicObservationSource V policy) :
    (adapt raw).graph = raw.binding.shared.graph := rfl

@[simp] theorem adapt_spatial? [DecidableEq V] [Fintype V]
    (raw : RawAcyclicObservationSource V policy) :
    (adapt raw).spatial? = raw.binding.shared.spatial? := rfl

@[simp] theorem adapt_diagram? [DecidableEq V] [Fintype V]
    (raw : RawAcyclicObservationSource V policy) :
    (adapt raw).diagram? = raw.binding.shared.diagram? := rfl

/-- The recovered source record: the exact authoritative input and the decoded observation list. -/
@[ext] structure RecoveredAcyclicObservationSource
    (policy : P93AcyclicAuthorityPolicy) where
  source : AuthoritativeChemicalInput
  observations : List (SourceAcyclicObservation policy)

/-- Decode a satellite into the recovered source record.  The authoritative input is the exact
encode of the shared finite source; observations are decoded with the same enumeration. -/
def suppliedSource [DecidableEq V] [Fintype V]
    (e : V ≃ Fin (Fintype.card V))
    (satellite : AcyclicObservationSatellite V policy) :
    RecoveredAcyclicObservationSource policy where
  source := satellite.toFiniteSource.encode e
  observations := unrelabelObservationList e satellite.observations

/-- **Exact full source recovery.**  Adapting a raw source and decoding it returns the exact
authoritative input (through the binding's actual source equality) and the exact ordered list of
pre-existing acyclic observation records. -/
theorem suppliedSource_adapt [DecidableEq V] [Fintype V]
    (raw : RawAcyclicObservationSource V policy) :
    suppliedSource raw.binding.enumeration (adapt raw) =
      { source := raw.binding.source, observations := raw.observations } := by
  apply RecoveredAcyclicObservationSource.ext
  · exact raw.binding.encode_shared
  · change unrelabelObservationList raw.binding.enumeration (adapt raw).observations =
      raw.observations
    rw [show (adapt raw).observations = raw.observations.attach.map (fun observation =>
        relabelObservation raw.binding.enumeration observation.1
          (SourceAcyclicObservation.boundedIn_of_validFor_binding raw.binding
            observation.1 (raw.valid observation.1 observation.2))) from rfl]
    exact unrelabelObservationList_relabelObservationList raw.binding.enumeration
      raw.observations (fun observation member =>
        SourceAcyclicObservation.boundedIn_of_validFor_binding raw.binding observation
          (raw.valid observation member))

/-- Validity is preserved for the whole recovered list at the same source and policy. -/
theorem suppliedSource_adapt_validFor [DecidableEq V] [Fintype V]
    (raw : RawAcyclicObservationSource V policy)
    (observation : SourceAcyclicObservation policy)
    (member : observation ∈ (suppliedSource raw.binding.enumeration (adapt raw)).observations) :
    observation.ValidFor raw.binding.source := by
  have listEq : (suppliedSource raw.binding.enumeration (adapt raw)).observations =
      raw.observations := by
    simpa using congrArg (RecoveredAcyclicObservationSource.observations)
      (suppliedSource_adapt raw)
  have sourceMember : observation ∈ raw.observations := by
    rw [← listEq]
    exact member
  exact raw.valid observation sourceMember

/-! ## Concrete certified-source adapter -/

/-- The concrete binding of a certified authoritative input to its exact finite ingress source,
reusing the existing molecule codec's certified binding. -/
def certifiedBinding (certified : CertifiedAuthoritativeChemicalInput) :
    AcyclicSourceBinding (Fin certified.input.molecule.atomCount) :=
  OrganicStereoP93PhysicalFrameIngress.PhysicalFrameSourceBinding.ofCertified certified

/-- Adapt a certified source together with an ordered list of valid carrier observations. -/
def adaptCertified (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceAcyclicObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor certified.input) :
    AcyclicObservationSatellite (Fin certified.input.molecule.atomCount) policy :=
  adapt { binding := certifiedBinding certified
          observations := observations
          valid := valid }

/-- **Concrete exact recovery from a certified source.** -/
theorem suppliedSource_adaptCertified
    (certified : CertifiedAuthoritativeChemicalInput)
    (observations : List (SourceAcyclicObservation policy))
    (valid : ∀ observation ∈ observations,
      observation.ValidFor certified.input) :
    suppliedSource (identityEnumeration certified.input.molecule.atomCount)
        (adaptCertified certified observations valid) =
      { source := certified.input, observations := observations } :=
  suppliedSource_adapt
    { binding := certifiedBinding certified
      observations := observations
      valid := valid }

end OrganicStereoP93AcyclicIngress

end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress.unrelabelAcyclicAssignment_relabelAcyclicAssignment
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress.unrelabelObservation_relabelObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress.validFor_unrelabelObservation_relabelObservation_iff
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress.suppliedSource_adapt
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress.unrelabelObservation_bareAssignment_relabelObservation
assert_kernel_only
  TetraStereo.OneCenter.OrganicStereoP93AcyclicIngress.bareAssignment_roundtrip_bounds_validFor
