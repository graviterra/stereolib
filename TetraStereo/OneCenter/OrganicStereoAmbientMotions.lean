import TetraStereo.OneCenter.OrganicStereoRealConfiguration
import TetraStereo.OneCenter.OrganicStereoEmbeddedBondPaths
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.UnitInterval

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter

/-!
# Ambient motions of real three-dimensional space

This module represents a *supplied* ambient deformation of real Euclidean 3-space over the unit
interval.  It is a concrete topological object, not an opaque caller relation:

* `AmbientMotion` is a family `map : unitInterval → (Real3 ≃ₜ Real3)` of homeomorphisms together
  with proofs that the forward evaluation map `(t, x) ↦ map t x` and the inverse evaluation map
  `(t, x) ↦ (map t).symm x` are jointly continuous, and that the family starts at the identity at
  time `0`;
* the identity family, the pointwise inverse family and the pointwise composition family
  `t ↦ (first.map t).trans (second.map t)` are motions.  Pointwise composition is used instead of
  concatenating two half-time intervals; it still starts at the identity and ends at the
  composition of the two endpoint homeomorphisms;
* endpoint homeomorphisms that are realizable by motions satisfy the subgroup closure laws
  (identity, inverse, composition).  Mathlib v4.28 does not give `Homeomorph X X` a `Group`
  instance, so the subgroup is presented as an explicit carrier with the three closure theorems
  and a bundled `RealizableEndpointSubgroup` record;
* `AmbientMotionEquivalent` relates two conformations when some motion transports the first to the
  second by its endpoint action.  It is proved to be an equivalence relation, both for an
  arbitrary atom type and for the source-bound `SourceConformation` type of
  `OrganicStereoRealConfiguration`.  Every atom follows a continuous trajectory in time;
* continuous curves are acted on pointwise, `applyCurve curve t = m_t(γ_t)`.  Here the single
  variable `t` is simultaneously the motion time and the spatial curve parameter: this is a
  genuine action on the trajectory space `C(I, Real3)`, but it is *not* embedded transport of a
  spatial arc and may lose spatial injectivity or shared-endpoint structure;
* a *fixed-time* action on source-indexed embedded bond-path tables is provided at the end:
  `BondPathTable.applyAt motion u` and `SourceBoundEmbeddedBondPaths.applyAt motion u` apply the
  single homeomorphism `motion.map u` to the conformation and to every arc, so the curve
  parameter `s` stays the spatial arc parameter (`s ↦ motion.map u (arc s)`).  The existing
  `BondPathTable.mapHomeomorph` theorem preserves every realization obligation, and the source,
  the documented interaction subset and all occurrence (source interaction and atom) indices are
  retained verbatim.  This uses the real `OrganicStereoEmbeddedBondPaths` module; it is a
  concrete integration layer, not a topological classification or kinetic claim.

## Scope

These are *allowed ambient deformations supplied as input*.  Nothing here asserts that every
physical trajectory of a molecule is of this form, that arbitrary continuous paths through
embeddings are ambient isotopies, or that label-preserving rigid congruence is the same as full
chemical isomer identity.  Atom automorphisms are a separate notion treated elsewhere; no
statement here relates them to this relation.  No chirality verdict, linking number, knot
classification, energy barrier or kinetic conclusion is drawn.  The pointwise curve action
`AmbientMotion.applyCurve` is kept only as a trajectory-space action; the embedded bond-path
integration is the fixed-time adapter `BondPathTable.applyAt` / `SourceBoundEmbeddedBondPaths.applyAt`,
which never mixes the motion time with the spatial arc parameter.
-/

/-- The concrete ambient space: real Euclidean 3-space. -/
abbrev Real3 : Type := EuclideanSpace ℝ (Fin 3)

/-- A continuous ambient deformation of `Real3` indexed by the unit interval, starting at the
identity.  Both the forward and the inverse evaluation maps are jointly continuous in time and
position.  The family is supplied data: it is not inferred from a path through embeddings. -/
structure AmbientMotion where
  /-- The homeomorphism of ambient space at each time. -/
  map : unitInterval → Real3 ≃ₜ Real3
  /-- Joint continuity of the forward evaluation map. -/
  continuous_uncurried : Continuous fun pair : unitInterval × Real3 => map pair.1 pair.2
  /-- Joint continuity of the inverse evaluation map. -/
  continuous_uncurried_inv :
    Continuous fun pair : unitInterval × Real3 => (map pair.1).symm pair.2
  /-- The deformation starts at the identity homeomorphism. -/
  starts_identity : map 0 = Homeomorph.refl Real3

namespace AmbientMotion

variable {V : Type*}

/-! ## Points and trajectories -/

/-- The position of a point at time `t`. -/
def applyPoint (motion : AmbientMotion) (t : unitInterval) (point : Real3) : Real3 :=
  motion.map t point

@[simp] theorem applyPoint_def (motion : AmbientMotion) (t : unitInterval) (point : Real3) :
    motion.applyPoint t point = motion.map t point := rfl

/-- At time zero every point is fixed. -/
@[simp] theorem applyPoint_zero (motion : AmbientMotion) (point : Real3) :
    motion.applyPoint 0 point = point := by
  rw [applyPoint_def, motion.starts_identity]
  rfl

/-- The forward evaluation map is exactly the joint continuity field. -/
theorem continuous_applyPoint (motion : AmbientMotion) :
    Continuous fun pair : unitInterval × Real3 => motion.applyPoint pair.1 pair.2 :=
  motion.continuous_uncurried

/-- The inverse evaluation map is exactly the inverse joint continuity field. -/
theorem continuous_applyPoint_inv (motion : AmbientMotion) :
    Continuous fun pair : unitInterval × Real3 =>
      (motion.map pair.1).symm pair.2 :=
  motion.continuous_uncurried_inv

/-- The trajectory of a single point is continuous in time. -/
theorem continuous_trajectory (motion : AmbientMotion) (point : Real3) :
    Continuous fun t : unitInterval => motion.applyPoint t point := by
  have pairContinuous : Continuous fun t : unitInterval => (t, point) :=
    continuous_id.prodMk (continuous_const : Continuous fun _ : unitInterval => point)
  simpa [applyPoint] using motion.continuous_uncurried.comp pairContinuous

/-- The inverse trajectory of a single point is continuous in time. -/
theorem continuous_trajectory_inv (motion : AmbientMotion) (point : Real3) :
    Continuous fun t : unitInterval => (motion.map t).symm point := by
  have pairContinuous : Continuous fun t : unitInterval => (t, point) :=
    continuous_id.prodMk (continuous_const : Continuous fun _ : unitInterval => point)
  simpa using motion.continuous_uncurried_inv.comp pairContinuous

/-! ## Identity, inverse and pointwise composition -/

/-- The constant identity motion. -/
def identity : AmbientMotion where
  map := fun _ => Homeomorph.refl Real3
  continuous_uncurried := by
    simpa using (continuous_snd : Continuous fun pair : unitInterval × Real3 => pair.2)
  continuous_uncurried_inv := by
    simpa using (continuous_snd : Continuous fun pair : unitInterval × Real3 => pair.2)
  starts_identity := rfl

/-- The pointwise inverse family of a motion. -/
def inverse (motion : AmbientMotion) : AmbientMotion where
  map := fun t => (motion.map t).symm
  continuous_uncurried := motion.continuous_uncurried_inv
  continuous_uncurried_inv := by
    simpa using motion.continuous_uncurried
  starts_identity := by
    rw [motion.starts_identity]
    exact Homeomorph.refl_symm

/-- The pointwise composition family `t ↦ (first.map t).trans (second.map t)`, i.e. apply `first`
at time `t` and then `second` at the same time.  This avoids any half-interval concatenation and
still starts at the identity. -/
def comp (first second : AmbientMotion) : AmbientMotion where
  map := fun t => (first.map t).trans (second.map t)
  continuous_uncurried := by
    have composed : Continuous fun pair : unitInterval × Real3 =>
        second.map pair.1 (first.map pair.1 pair.2) :=
      second.continuous_uncurried.comp
        (continuous_fst.prodMk
          (first.continuous_uncurried :
            Continuous fun pair : unitInterval × Real3 => first.map pair.1 pair.2))
    simpa [Homeomorph.trans_apply] using composed
  continuous_uncurried_inv := by
    have composed : Continuous fun pair : unitInterval × Real3 =>
        (first.map pair.1).symm ((second.map pair.1).symm pair.2) :=
      first.continuous_uncurried_inv.comp
        (continuous_fst.prodMk
          (second.continuous_uncurried_inv :
            Continuous fun pair : unitInterval × Real3 =>
              (second.map pair.1).symm pair.2))
    simpa [Homeomorph.symm_trans_apply] using composed
  starts_identity := by
    rw [show first.map 0 = Homeomorph.refl Real3 from first.starts_identity]
    rw [show second.map 0 = Homeomorph.refl Real3 from second.starts_identity]
    ext point
    simp

@[simp] theorem identity_map (t : unitInterval) :
    identity.map t = Homeomorph.refl Real3 := rfl

@[simp] theorem inverse_map (motion : AmbientMotion) (t : unitInterval) :
    motion.inverse.map t = (motion.map t).symm := rfl

@[simp] theorem comp_map (first second : AmbientMotion) (t : unitInterval) :
    (comp first second).map t = (first.map t).trans (second.map t) := rfl

/-! ## Endpoints and endpoint laws -/

/-- The endpoint homeomorphism of a motion. -/
def endpoint (motion : AmbientMotion) : Real3 ≃ₜ Real3 :=
  motion.map 1

@[simp] theorem endpoint_identity : identity.endpoint = Homeomorph.refl Real3 := rfl

@[simp] theorem endpoint_inverse (motion : AmbientMotion) :
    motion.inverse.endpoint = motion.endpoint.symm := rfl

@[simp] theorem endpoint_comp (first second : AmbientMotion) :
    (comp first second).endpoint = first.endpoint.trans second.endpoint := rfl

/-- The endpoint action on a molecular conformation: every atom is moved by the endpoint
homeomorphism.  This is the action used to define the conformation relation. -/
def applyEndpoint (motion : AmbientMotion) (conformation : MolecularConformation V) :
    MolecularConformation V :=
  fun atom => motion.endpoint (conformation atom)

@[simp] theorem applyEndpoint_apply (motion : AmbientMotion)
    (conformation : MolecularConformation V) (atom : V) :
    motion.applyEndpoint conformation atom = motion.endpoint (conformation atom) := rfl

@[simp] theorem applyEndpoint_identity (conformation : MolecularConformation V) :
    identity.applyEndpoint conformation = conformation := by
  funext atom
  simp [applyEndpoint]

@[simp] theorem applyEndpoint_inverse (motion : AmbientMotion)
    (conformation : MolecularConformation V) :
    motion.inverse.applyEndpoint (motion.applyEndpoint conformation) = conformation := by
  funext atom
  simp [applyEndpoint]

@[simp] theorem applyEndpoint_inverse_apply (motion : AmbientMotion)
    (conformation : MolecularConformation V) :
    motion.applyEndpoint (motion.inverse.applyEndpoint conformation) = conformation := by
  funext atom
  simp [applyEndpoint]

@[simp] theorem applyEndpoint_comp (first second : AmbientMotion)
    (conformation : MolecularConformation V) :
    (comp first second).applyEndpoint conformation =
      second.applyEndpoint (first.applyEndpoint conformation) := by
  funext atom
  simp [applyEndpoint, Homeomorph.trans_apply]

/-- Endpoint action is injective: the endpoint is a homeomorphism. -/
theorem applyEndpoint_injective (motion : AmbientMotion) :
    Function.Injective (motion.applyEndpoint (V := V)) := by
  intro first second equal
  funext atom
  exact (motion.endpoint).injective (by
    simpa [applyEndpoint] using congrFun equal atom)

/-- Endpoint action is surjective: the endpoint is a homeomorphism. -/
theorem applyEndpoint_surjective (motion : AmbientMotion) :
    Function.Surjective (motion.applyEndpoint (V := V)) := by
  intro conformation
  refine ⟨fun atom => (motion.endpoint).symm (conformation atom), ?_⟩
  funext atom
  simp [applyEndpoint]

/-- Endpoint action is bijective on every conformation space. -/
theorem applyEndpoint_bijective (motion : AmbientMotion) :
    Function.Bijective (motion.applyEndpoint (V := V)) :=
  ⟨motion.applyEndpoint_injective, motion.applyEndpoint_surjective⟩

/-- The conformation obtained at time `t` by applying the ambient motion pointwise. -/
def applyAt (motion : AmbientMotion) (t : unitInterval)
    (conformation : MolecularConformation V) : MolecularConformation V :=
  fun atom => motion.map t (conformation atom)

@[simp] theorem applyAt_apply (motion : AmbientMotion) (t : unitInterval)
    (conformation : MolecularConformation V) (atom : V) :
    motion.applyAt t conformation atom = motion.map t (conformation atom) := rfl

/-- At time zero the conformation is unchanged. -/
@[simp] theorem applyAt_zero (motion : AmbientMotion)
    (conformation : MolecularConformation V) :
    motion.applyAt 0 conformation = conformation := by
  funext atom
  rw [applyAt_apply, motion.starts_identity]
  rfl

/-- At time one the conformation is the endpoint action. -/
@[simp] theorem applyAt_one (motion : AmbientMotion)
    (conformation : MolecularConformation V) :
    motion.applyAt 1 conformation = motion.applyEndpoint conformation := rfl

@[simp] theorem applyAt_identity (t : unitInterval)
    (conformation : MolecularConformation V) :
    identity.applyAt t conformation = conformation := by
  funext atom
  simp [applyAt]

@[simp] theorem applyAt_inverse_apply (motion : AmbientMotion) (t : unitInterval)
    (conformation : MolecularConformation V) :
    motion.inverse.applyAt t (motion.applyAt t conformation) = conformation := by
  funext atom
  simp [applyAt]

@[simp] theorem applyAt_comp (first second : AmbientMotion) (t : unitInterval)
    (conformation : MolecularConformation V) :
    (comp first second).applyAt t conformation =
      second.applyAt t (first.applyAt t conformation) := rfl

/-! ## Pointwise atom transport -/

/-- The trajectory of one atom under a motion, as a continuous map on the unit interval. -/
def atomTrajectory (motion : AmbientMotion) (conformation : MolecularConformation V)
    (atom : V) : C(unitInterval, Real3) where
  toFun t := motion.applyAt t conformation atom
  continuous_toFun := by
    simpa [applyAt, applyPoint] using motion.continuous_trajectory (conformation atom)

@[simp] theorem atomTrajectory_apply (motion : AmbientMotion)
    (conformation : MolecularConformation V) (atom : V) (t : unitInterval) :
    motion.atomTrajectory conformation atom t = motion.applyAt t conformation atom := rfl

/-- A transported atom starts at its original source position. -/
@[simp] theorem atomTrajectory_zero (motion : AmbientMotion)
    (conformation : MolecularConformation V) (atom : V) :
    motion.atomTrajectory conformation atom 0 = conformation atom := by
  rw [atomTrajectory_apply, applyAt_zero]

/-- A transported atom finishes at the endpoint action on its source position. -/
@[simp] theorem atomTrajectory_one (motion : AmbientMotion)
    (conformation : MolecularConformation V) (atom : V) :
    motion.atomTrajectory conformation atom 1 = motion.endpoint (conformation atom) := by
  rw [atomTrajectory_apply, applyAt_one, applyEndpoint_apply]

/-- Pointwise atom transport: every atom keeps its source value at time zero and reaches the
endpoint action at time one, continuously throughout. -/
theorem atomTrajectory_transports (motion : AmbientMotion)
    (conformation : MolecularConformation V) (atom : V) :
    motion.atomTrajectory conformation atom 0 = conformation atom ∧
      motion.atomTrajectory conformation atom 1 =
        motion.endpoint (conformation atom) :=
  ⟨motion.atomTrajectory_zero conformation atom,
    motion.atomTrajectory_one conformation atom⟩

/-! ## The conformation relation -/

/-- Two conformations are ambient-motion equivalent when some motion carries the first to the
second by its endpoint action.  The motion is part of the supplied witness.  This is not asserted
to coincide with `MolecularConformation.ProperEquivalent`, with label-preserving rigid congruence,
or with full chemical isomer identity. -/
def AmbientMotionEquivalent (first second : MolecularConformation V) : Prop :=
  ∃ motion : AmbientMotion, ∀ atom, motion.endpoint (first atom) = second atom

theorem ambientMotionEquivalent_iff_exists_applyEndpoint
    {first second : MolecularConformation V} :
    AmbientMotionEquivalent first second ↔
      ∃ motion : AmbientMotion, motion.applyEndpoint first = second := by
  constructor
  · rintro ⟨motion, transported⟩
    exact ⟨motion, funext transported⟩
  · rintro ⟨motion, transported⟩
    exact ⟨motion, fun atom => congrFun transported atom⟩

theorem ambientMotionEquivalent_refl (conformation : MolecularConformation V) :
    AmbientMotionEquivalent conformation conformation :=
  ⟨identity, fun atom => by simp⟩

theorem ambientMotionEquivalent_symm {first second : MolecularConformation V}
    (related : AmbientMotionEquivalent first second) :
    AmbientMotionEquivalent second first := by
  obtain ⟨motion, transported⟩ := related
  refine ⟨motion.inverse, fun atom => ?_⟩
  calc
    motion.inverse.endpoint (second atom) = (motion.endpoint).symm (second atom) := by
      rw [endpoint_inverse]
    _ = (motion.endpoint).symm (motion.endpoint (first atom)) := by
      rw [transported atom]
    _ = first atom := by simp

theorem ambientMotionEquivalent_trans {first second third : MolecularConformation V}
    (firstSecond : AmbientMotionEquivalent first second)
    (secondThird : AmbientMotionEquivalent second third) :
    AmbientMotionEquivalent first third := by
  obtain ⟨firstMotion, firstTransported⟩ := firstSecond
  obtain ⟨secondMotion, secondTransported⟩ := secondThird
  refine ⟨firstMotion.comp secondMotion, fun atom => ?_⟩
  calc
    (firstMotion.comp secondMotion).endpoint (first atom) =
        secondMotion.endpoint (firstMotion.endpoint (first atom)) := by
      rw [endpoint_comp, Homeomorph.trans_apply]
    _ = secondMotion.endpoint (second atom) := by rw [firstTransported atom]
    _ = third atom := secondTransported atom

/-- Ambient-motion equivalence of conformations is a genuine equivalence relation. -/
theorem ambientMotionEquivalent_equivalence :
    Equivalence (@AmbientMotionEquivalent V) :=
  ⟨ambientMotionEquivalent_refl,
    fun related => ambientMotionEquivalent_symm related,
    fun firstSecond secondThird => ambientMotionEquivalent_trans firstSecond secondThird⟩

/-- The setoid of conformations up to supplied ambient-motion equivalence. -/
def ambientMotionSetoid : Setoid (MolecularConformation V) :=
  ⟨@AmbientMotionEquivalent V, ambientMotionEquivalent_equivalence⟩

/-! ## Source-bound conformations and source atom transport -/

/-- Ambient-motion equivalence specialized to the source-bound conformation type.  The source and
its atom index are retained; only real positions are moved. -/
abbrev SourceMotionEquivalent (source : CertifiedAuthoritativeChemicalInput)
    (first second : SourceConformation source) : Prop :=
  AmbientMotionEquivalent first second

/-- The source-bound relation is reflexive. -/
theorem sourceMotionEquivalent_refl (source : CertifiedAuthoritativeChemicalInput)
    (conformation : SourceConformation source) :
    SourceMotionEquivalent source conformation conformation :=
  ambientMotionEquivalent_refl conformation

/-- The source-bound relation is symmetric. -/
theorem sourceMotionEquivalent_symm (source : CertifiedAuthoritativeChemicalInput)
    {first second : SourceConformation source}
    (related : SourceMotionEquivalent source first second) :
    SourceMotionEquivalent source second first :=
  ambientMotionEquivalent_symm related

/-- The source-bound relation is transitive. -/
theorem sourceMotionEquivalent_trans (source : CertifiedAuthoritativeChemicalInput)
    {first second third : SourceConformation source}
    (firstSecond : SourceMotionEquivalent source first second)
    (secondThird : SourceMotionEquivalent source second third) :
    SourceMotionEquivalent source first third :=
  ambientMotionEquivalent_trans firstSecond secondThird

/-- The source-bound relation is a genuine equivalence relation. -/
theorem sourceMotionEquivalent_equivalence (source : CertifiedAuthoritativeChemicalInput) :
    Equivalence (SourceMotionEquivalent source) :=
  ambientMotionEquivalent_equivalence

/-- Endpoint action on a source-bound conformation, retaining the source atom index. -/
theorem source_applyEndpoint_apply (source : CertifiedAuthoritativeChemicalInput)
    (motion : AmbientMotion) (conformation : SourceConformation source)
    (atom : SourceAtomIndex source) :
    motion.applyEndpoint conformation atom = motion.endpoint (conformation atom) := rfl

/-- Every source atom has a continuous trajectory retaining its source point at time zero and
reaching the endpoint action at time one. -/
theorem source_atomTrajectory_transports (source : CertifiedAuthoritativeChemicalInput)
    (motion : AmbientMotion) (conformation : SourceConformation source)
    (atom : SourceAtomIndex source) :
    motion.atomTrajectory conformation atom 0 = conformation atom ∧
      motion.atomTrajectory conformation atom 1 =
        motion.endpoint (conformation atom) :=
  motion.atomTrajectory_transports conformation atom

/-! ## Endpoint homeomorphisms realizable by motions

Mathlib v4.28 does not install a `Group` instance on `Homeomorph X X`, so the subgroup of
realizable endpoints is presented by an explicit carrier and closure theorems, bundled in
`RealizableEndpointSubgroup`. -/

/-- A homeomorphism is an endpoint of some ambient motion starting at the identity. -/
def RealizableEndpoint (homeomorphism : Real3 ≃ₜ Real3) : Prop :=
  ∃ motion : AmbientMotion, motion.endpoint = homeomorphism

/-- The identity homeomorphism is realizable. -/
theorem realizableEndpoint_refl : RealizableEndpoint (Homeomorph.refl Real3) :=
  ⟨identity, rfl⟩

/-- Inverses of realizable endpoints are realizable, by the pointwise inverse motion. -/
theorem realizableEndpoint_symm {homeomorphism : Real3 ≃ₜ Real3}
    (realizable : RealizableEndpoint homeomorphism) :
    RealizableEndpoint homeomorphism.symm := by
  obtain ⟨motion, endpointEq⟩ := realizable
  refine ⟨motion.inverse, ?_⟩
  rw [endpoint_inverse, endpointEq]

/-- Compositions of realizable endpoints are realizable, by pointwise composition of motions. -/
theorem realizableEndpoint_trans {first second : Real3 ≃ₜ Real3}
    (firstRealizable : RealizableEndpoint first)
    (secondRealizable : RealizableEndpoint second) :
    RealizableEndpoint (first.trans second) := by
  obtain ⟨firstMotion, rfl⟩ := firstRealizable
  obtain ⟨secondMotion, rfl⟩ := secondRealizable
  exact ⟨firstMotion.comp secondMotion, endpoint_comp firstMotion secondMotion⟩

/-- The carrier set of endpoint homeomorphisms realizable by supplied ambient motions. -/
def realizableEndpointSet : Set (Real3 ≃ₜ Real3) :=
  {homeomorphism | RealizableEndpoint homeomorphism}

@[simp] theorem mem_realizableEndpointSet_iff {homeomorphism : Real3 ≃ₜ Real3} :
    homeomorphism ∈ realizableEndpointSet ↔ RealizableEndpoint homeomorphism :=
  Iff.rfl

/-- Explicit subgroup laws for the realizable endpoint homeomorphisms.  In the absence of a
Mathlib `Group` instance on `Homeomorph Real3 Real3`, this record records exactly the three
subgroup closure conditions on the carrier set. -/
structure RealizableEndpointSubgroup where
  /-- The underlying set of realizable endpoints. -/
  carrier : Set (Real3 ≃ₜ Real3)
  /-- The identity belongs to the carrier. -/
  refl_mem : Homeomorph.refl Real3 ∈ carrier
  /-- The carrier is closed under inverse. -/
  symm_mem : ∀ homeomorphism ∈ carrier, homeomorphism.symm ∈ carrier
  /-- The carrier is closed under composition. -/
  trans_mem : ∀ first ∈ carrier, ∀ second ∈ carrier, first.trans second ∈ carrier

/-- The realizable endpoint homeomorphisms form a subgroup in the explicit sense above. -/
def realizableEndpoints : RealizableEndpointSubgroup where
  carrier := realizableEndpointSet
  refl_mem := realizableEndpoint_refl
  symm_mem := fun _ realizable => realizableEndpoint_symm realizable
  trans_mem := fun _ firstRealizable _ secondRealizable =>
    realizableEndpoint_trans firstRealizable secondRealizable

/-! ## Pointwise curve action

This action uses one variable `t` both as motion time and as the spatial parameter of the
curve: `applyCurve curve t = motion.map t (curve t)`.  It is a genuine bijection of the whole
trajectory space `C(I, Real3)` (with inverse given by the inverse motion), but it is *not*
embedded bond transport: even when `curve` is injective, `applyCurve curve` may fail to be
injective, and two curves that share a point need not share that point afterwards because the
homeomorphism applied at that parameter need not be the same.  No such spatial claim is made
here.  The fixed-time bond-table adapter is `BondPathTable.applyAt` below, which fixes the
motion time and hence applies one single homeomorphism to the whole spatial configuration. -/

/-- A motion acts pointwise on continuous curves: at parameter/time `t`, the value at `t` of the
original curve is moved by `map t`.  The same variable indexes both the motion and the spatial
parameter, so this is an action on trajectories, not spatial transport of an embedded arc. -/
def applyCurve (motion : AmbientMotion) (curve : C(unitInterval, Real3)) :
    C(unitInterval, Real3) where
  toFun t := motion.map t (curve t)
  continuous_toFun := by
    have pairContinuous : Continuous fun t : unitInterval => (t, curve t) :=
      continuous_id.prodMk curve.continuous_toFun
    simpa using motion.continuous_uncurried.comp pairContinuous

@[simp] theorem applyCurve_apply (motion : AmbientMotion) (curve : C(unitInterval, Real3))
    (t : unitInterval) :
    motion.applyCurve curve t = motion.map t (curve t) := rfl

/-- Time zero leaves every value of the curve unchanged. -/
@[simp] theorem applyCurve_zero (motion : AmbientMotion) (curve : C(unitInterval, Real3)) :
    motion.applyCurve curve 0 = curve 0 := by
  rw [applyCurve_apply, motion.starts_identity]
  rfl

/-- Time one applies the endpoint homeomorphism to the value at time one. -/
@[simp] theorem applyCurve_one (motion : AmbientMotion) (curve : C(unitInterval, Real3)) :
    motion.applyCurve curve 1 = motion.endpoint (curve 1) := rfl

/-- The identity motion fixes every continuous curve. -/
@[simp] theorem identity_applyCurve (curve : C(unitInterval, Real3)) :
    identity.applyCurve curve = curve := by
  ext t
  simp [applyCurve]

/-- The inverse motion undoes the curve action. -/
@[simp] theorem inverse_applyCurve (motion : AmbientMotion) (curve : C(unitInterval, Real3)) :
    motion.inverse.applyCurve (motion.applyCurve curve) = curve := by
  ext t
  simp [applyCurve]

/-- The curve action of the inverse motion is also a right inverse. -/
@[simp] theorem applyCurve_inverse (motion : AmbientMotion) (curve : C(unitInterval, Real3)) :
    motion.applyCurve (motion.inverse.applyCurve curve) = curve := by
  ext t
  simp [applyCurve]

/-- Pointwise composition of motions acts as composition of curve actions. -/
@[simp] theorem comp_applyCurve (first second : AmbientMotion)
    (curve : C(unitInterval, Real3)) :
    (comp first second).applyCurve curve =
      second.applyCurve (first.applyCurve curve) := by
  ext t
  simp [applyCurve, Homeomorph.trans_apply]

/-- The curve action is injective. -/
theorem applyCurve_injective (motion : AmbientMotion) :
    Function.Injective motion.applyCurve := by
  intro first second equal
  have inversed := congrArg motion.inverse.applyCurve equal
  simpa using inversed

/-- The curve action is surjective. -/
theorem applyCurve_surjective (motion : AmbientMotion) :
    Function.Surjective motion.applyCurve :=
  fun curve => ⟨motion.inverse.applyCurve curve, motion.applyCurve_inverse curve⟩

/-- The curve action is bijective. -/
theorem applyCurve_bijective (motion : AmbientMotion) :
    Function.Bijective motion.applyCurve :=
  ⟨motion.applyCurve_injective, motion.applyCurve_surjective⟩

/-- Equivalence of continuous curves generated by ambient motions. -/
def CurveMotionEquivalent (first second : C(unitInterval, Real3)) : Prop :=
  ∃ motion : AmbientMotion, motion.applyCurve first = second

theorem curveMotionEquivalent_refl (curve : C(unitInterval, Real3)) :
    CurveMotionEquivalent curve curve :=
  ⟨identity, by simp⟩

theorem curveMotionEquivalent_symm {first second : C(unitInterval, Real3)}
    (related : CurveMotionEquivalent first second) :
    CurveMotionEquivalent second first := by
  obtain ⟨motion, transported⟩ := related
  refine ⟨motion.inverse, ?_⟩
  rw [← transported]
  simp

theorem curveMotionEquivalent_trans {first second third : C(unitInterval, Real3)}
    (firstSecond : CurveMotionEquivalent first second)
    (secondThird : CurveMotionEquivalent second third) :
    CurveMotionEquivalent first third := by
  obtain ⟨firstMotion, firstTransported⟩ := firstSecond
  obtain ⟨secondMotion, secondTransported⟩ := secondThird
  refine ⟨firstMotion.comp secondMotion, ?_⟩
  rw [comp_applyCurve, firstTransported, secondTransported]

/-- Ambient-motion equivalence of continuous curves is an equivalence relation. -/
theorem curveMotionEquivalent_equivalence : Equivalence CurveMotionEquivalent :=
  ⟨curveMotionEquivalent_refl,
    fun related => curveMotionEquivalent_symm related,
    fun firstSecond secondThird => curveMotionEquivalent_trans firstSecond secondThird⟩

/-! ## Parametrized arcs with recorded source and endpoint -/

/-- A continuous arc with its start and finish points recorded explicitly. -/
structure AmbientCurve (start finish : Real3) where
  /-- The underlying continuous curve. -/
  toCurve : C(unitInterval, Real3)
  /-- The value at time zero. -/
  starts : toCurve 0 = start
  /-- The value at time one. -/
  finishes : toCurve 1 = finish

namespace AmbientCurve

variable {start finish : Real3}

/-- Apply the *pointwise mixed-time* curve action of a motion to an arc (the operation is named
`transport` for API compatibility).  The value at parameter `0` is retained, every value is moved
by the homeomorphism at the same parameter, and the value at `1` becomes the endpoint action on
the original finish.  Because the homeomorphism varies with the spatial parameter, this is not
embedded bond transport: it makes no injectivity or common-endpoint claim for the resulting arc. -/
def transport (motion : AmbientMotion) (arc : AmbientCurve start finish) :
    AmbientCurve start (motion.endpoint finish) where
  toCurve := motion.applyCurve arc.toCurve
  starts := by rw [AmbientMotion.applyCurve_zero, arc.starts]
  finishes := by rw [AmbientMotion.applyCurve_one, arc.finishes]

@[simp] theorem transport_toCurve (motion : AmbientMotion) (arc : AmbientCurve start finish) :
    (transport motion arc).toCurve = motion.applyCurve arc.toCurve := rfl

/-- Every arc value is moved by the motion at the same time index. -/
@[simp] theorem transport_apply (motion : AmbientMotion) (arc : AmbientCurve start finish)
    (t : unitInterval) :
    (transport motion arc).toCurve t = motion.map t (arc.toCurve t) := rfl

/-- The source value at time zero is retained exactly. -/
@[simp] theorem transport_start (motion : AmbientMotion) (arc : AmbientCurve start finish) :
    (transport motion arc).toCurve 0 = start :=
  (transport motion arc).starts

/-- The finish value is the endpoint action on the original finish. -/
@[simp] theorem transport_finish (motion : AmbientMotion) (arc : AmbientCurve start finish) :
    (transport motion arc).toCurve 1 = motion.endpoint finish :=
  (transport motion arc).finishes

/-- The identity motion does not change the underlying curve. -/
@[simp] theorem identity_transport_toCurve (arc : AmbientCurve start finish) :
    (transport AmbientMotion.identity arc).toCurve = arc.toCurve := by
  simp

/-- Inverse transport recovers the underlying curve. -/
@[simp] theorem inverse_transport_toCurve (motion : AmbientMotion)
    (arc : AmbientCurve start finish) :
    (transport motion.inverse (transport motion arc)).toCurve = arc.toCurve := by
  simp

/-- Pointwise composed transport equals transporting successively. -/
@[simp] theorem comp_transport_toCurve (first second : AmbientMotion)
    (arc : AmbientCurve start finish) :
    (transport (first.comp second) arc).toCurve =
      (transport second (transport first arc)).toCurve := by
  simp

end AmbientCurve

/-! ## Explicit adapter surface for external curve data

This is a generic curve adapter for the pointwise trajectory action only.  It is *not* a
bond-path adapter and makes no chemical realizability claim; embedded bond-path data is handled
by the fixed-time adapter `BondPathTable.applyAt` / `SourceBoundEmbeddedBondPaths.applyAt`
below, which uses `OrganicStereoEmbeddedBondPaths.BondPathTable.mapHomeomorph`. -/

/-- A generic adapter from an external curve representation to an ambient continuous curve.
Calling `map` applies the pointwise trajectory action of a motion.  It carries no chemical
realizability claim, does not integrate any other state component, and is not used for
bond-path transport. -/
structure CurveAdapter (Curve : Type*) where
  /-- The ambient continuous curve supplied by the external representation. -/
  toAmbient : Curve → C(unitInterval, Real3)

namespace CurveAdapter

variable {Curve : Type*}

/-- Apply a motion to the ambient curve supplied by the adapter. -/
def map (adapter : CurveAdapter Curve) (motion : AmbientMotion) (curve : Curve) :
    C(unitInterval, Real3) :=
  motion.applyCurve (adapter.toAmbient curve)

@[simp] theorem map_def (adapter : CurveAdapter Curve) (motion : AmbientMotion)
    (curve : Curve) :
    adapter.map motion curve = motion.applyCurve (adapter.toAmbient curve) := rfl

/-- The identity motion returns the original ambient curve. -/
@[simp] theorem identity_map (adapter : CurveAdapter Curve) (curve : Curve) :
    adapter.map AmbientMotion.identity curve = adapter.toAmbient curve := by
  simp [map]

/-- The inverse motion undoes the curve action supplied by the adapter. -/
@[simp] theorem inverse_map (adapter : CurveAdapter Curve) (motion : AmbientMotion)
    (curve : Curve) :
    motion.inverse.applyCurve (adapter.map motion curve) = adapter.toAmbient curve := by
  simp [map]

/-- Composed motions act by successive curve actions on the adapter's curve. -/
@[simp] theorem comp_map (adapter : CurveAdapter Curve) (first second : AmbientMotion)
    (curve : Curve) :
    adapter.map (first.comp second) curve =
      second.applyCurve (adapter.map first curve) := by
  simp [map]

end CurveAdapter

end AmbientMotion

/-! ## Fixed-time action on source-indexed embedded bond-path tables

`AmbientMotion.applyCurve` above is an action on trajectories: its single parameter is both the
motion time and the spatial parameter of the curve.  It is not embedded bond transport and the
statements about it below make no spatial claim.

This section provides the actual integration with `OrganicStereoEmbeddedBondPaths`.  Given a
motion and a *fixed* motion time `u`, the single homeomorphism `motion.map u` is applied to the
atom conformation and to every bond arc at once.  The spatial parameter `s` of each arc remains
spatial:

`((BondPathTable.applyAt motion u table).edge e).arc s = motion.map u ((table.edge e).arc s)`.

Since the same homeomorphism is applied to every point, all realization obligations of
`RealizesSourceBondPaths` are preserved by the existing `BondPathTable.mapHomeomorph` theorem:
oriented endpoint equations, atom injectivity, arc injectivity, interior avoidance of atom
positions and the common-endpoint intersection property.  The source molecule, the documented
interaction subset, the edge index type, every source interaction (occurrence) index and every
oriented endpoint atom index are retained verbatim.

No topological classification, linking invariant, energy barrier or kinetic conclusion is drawn.
-/

namespace BondPathTable

variable {E : Type*} [Fintype E]
variable {molecule : SemanticMolecule}
variable {conformation : MolecularConformation (Fin molecule.atomCount)}

/-- Fixed-time ambient action on a source-indexed bond-path table: apply the single
homeomorphism `motion.map u` to the conformation and to every arc.  This is literally the
existing `BondPathTable.mapHomeomorph` transport; the source interaction indices, the oriented
endpoint atom indices and the documented subset are retained. -/
def applyAt (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) :
    BondPathTable E molecule (fun atom => motion.map u (conformation atom)) :=
  table.mapHomeomorph (motion.map u)

/-- The fixed-time action is exactly the existing homeomorphism transport theorem. -/
theorem applyAt_eq_mapHomeomorph (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) :
    table.applyAt motion u = table.mapHomeomorph (motion.map u) := rfl

@[simp] theorem applyAt_documented (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) :
    (table.applyAt motion u).documented = table.documented := rfl

/-- The source interaction (occurrence) index of every edge is retained. -/
@[simp] theorem applyAt_edge_sourceInteraction (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) (e : E) :
    ((table.applyAt motion u).edge e).sourceInteraction =
      (table.edge e).sourceInteraction := rfl

/-- The oriented source atom index of every edge is retained. -/
@[simp] theorem applyAt_edge_source (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) (e : E) :
    ((table.applyAt motion u).edge e).source = (table.edge e).source := rfl

/-- The oriented target atom index of every edge is retained. -/
@[simp] theorem applyAt_edge_target (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) (e : E) :
    ((table.applyAt motion u).edge e).target = (table.edge e).target := rfl

/-- At fixed motion time `u` the spatial arc parameter `s` stays spatial: every arc value is
moved by the single homeomorphism `motion.map u`. -/
@[simp] theorem applyAt_edge_arc (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) (e : E) (s : unitInterval) :
    ((table.applyAt motion u).edge e).arc s = motion.map u ((table.edge e).arc s) := rfl

/-- Every documented interaction index is still a genuine pair bond. -/
theorem applyAt_documented_genuine (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) :
    ∀ index, index ∈ (table.applyAt motion u).documented →
      IsGenuinePairBondAt molecule index :=
  (table.applyAt motion u).valid.documented_genuine

/-- Every adapted edge still represents a documented source interaction. -/
theorem applyAt_edge_documented (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) (e : E) :
    ((table.applyAt motion u).edge e).sourceInteraction ∈
      (table.applyAt motion u).documented :=
  (table.applyAt motion u).valid.edge_documented e

/-- Exact coverage of the documented interaction subset is preserved. -/
theorem applyAt_exact_coverage (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) :
    ∀ index, index ∈ (table.applyAt motion u).documented →
      ∃! e : E, ((table.applyAt motion u).edge e).sourceInteraction = index :=
  (table.applyAt motion u).valid.exact_coverage

/-- The adapted arc at parameter `0` is the moved source atom position. -/
theorem applyAt_source_endpoint (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) (e : E) :
    ((table.applyAt motion u).edge e).arc 0 =
      motion.map u (conformation ((table.edge e).source)) := by
  rw [applyAt_edge_arc, table.valid.source_endpoint e]

/-- The adapted arc at parameter `1` is the moved target atom position. -/
theorem applyAt_target_endpoint (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) (e : E) :
    ((table.applyAt motion u).edge e).arc 1 =
      motion.map u (conformation ((table.edge e).target)) := by
  rw [applyAt_edge_arc, table.valid.target_endpoint e]

/-- Atom injectivity of the conformation is preserved. -/
theorem applyAt_atom_injective (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) :
    Function.Injective (fun atom => motion.map u (conformation atom)) :=
  (table.applyAt motion u).valid.atom_injective

/-- Spatial injectivity of every arc is preserved. -/
theorem applyAt_arc_injective (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) (e : E) :
    Function.Injective ((table.applyAt motion u).edge e).arc :=
  (table.applyAt motion u).valid.arc_injective e

/-- Arc interiors still avoid every atom position. -/
theorem applyAt_interior_avoids_atoms (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) :
    ∀ e (s : unitInterval), s ≠ 0 → s ≠ 1 → ∀ a,
      ((table.applyAt motion u).edge e).arc s ≠
        (fun atom => motion.map u (conformation atom)) a :=
  (table.applyAt motion u).valid.interior_avoids_atoms

/-- Distinct adapted arcs still meet only at a common endpoint atom. -/
theorem applyAt_intersects_only_at_common_endpoints (motion : AmbientMotion) (u : unitInterval)
    (table : BondPathTable E molecule conformation) :
    ∀ e f (s t : unitInterval), e ≠ f →
      ((table.applyAt motion u).edge e).arc s =
        ((table.applyAt motion u).edge f).arc t →
      ∃ a : Fin molecule.atomCount,
        ((table.applyAt motion u).edge e).endpointAt? s = some a ∧
          ((table.applyAt motion u).edge f).endpointAt? t = some a :=
  (table.applyAt motion u).valid.intersects_only_at_common_endpoints

/-- The homeomorphism transport by the identity is the identity on tables. -/
theorem mapHomeomorph_refl (table : BondPathTable E molecule conformation) :
    table.mapHomeomorph (Homeomorph.refl EmbeddedReal3) = table := by
  apply ext_of_documented_edge
  · rfl
  · funext e
    change (table.edge e).mapHomeomorph (Homeomorph.refl EmbeddedReal3) = table.edge e
    cases table.edge e with
    | mk sourceInteraction source target source_ne_target participants_exact arc =>
      unfold SourceBondPath.mapHomeomorph
      congr 1

/-- Identity (time-zero) compatibility.  The conformation type is transported by the time-zero
identity, so the full table equality is heterogeneous; the data-level lemmas below give the
componentwise form (all indices and all arc values are unchanged). -/
theorem applyAt_zero_heq (motion : AmbientMotion)
    (table : BondPathTable E molecule conformation) :
    HEq (table.applyAt motion 0) table := by
  change HEq (table.mapHomeomorph (motion.map 0)) table
  rw [motion.starts_identity]
  exact heq_of_eq (mapHomeomorph_refl (conformation := conformation) table)

/-- At time zero the documented subset is unchanged. -/
@[simp] theorem applyAt_zero_documented (motion : AmbientMotion)
    (table : BondPathTable E molecule conformation) :
    (table.applyAt motion 0).documented = table.documented := rfl

/-- At time zero every source interaction (occurrence) index is unchanged. -/
@[simp] theorem applyAt_zero_edge_sourceInteraction (motion : AmbientMotion)
    (table : BondPathTable E molecule conformation) (e : E) :
    ((table.applyAt motion 0).edge e).sourceInteraction =
      (table.edge e).sourceInteraction := rfl

/-- At time zero every oriented source atom index is unchanged. -/
@[simp] theorem applyAt_zero_edge_source (motion : AmbientMotion)
    (table : BondPathTable E molecule conformation) (e : E) :
    ((table.applyAt motion 0).edge e).source = (table.edge e).source := rfl

/-- At time zero every oriented target atom index is unchanged. -/
@[simp] theorem applyAt_zero_edge_target (motion : AmbientMotion)
    (table : BondPathTable E molecule conformation) (e : E) :
    ((table.applyAt motion 0).edge e).target = (table.edge e).target := rfl

/-- At time zero every arc value is unchanged. -/
@[simp] theorem applyAt_zero_edge_arc (motion : AmbientMotion)
    (table : BondPathTable E molecule conformation) (e : E) (s : unitInterval) :
    ((table.applyAt motion 0).edge e).arc s = (table.edge e).arc s := by
  rw [applyAt_edge_arc, motion.starts_identity]
  rfl

/-- At time zero the adapted arc still starts at the original source atom position. -/
theorem applyAt_zero_source_endpoint (motion : AmbientMotion)
    (table : BondPathTable E molecule conformation) (e : E) :
    ((table.applyAt motion 0).edge e).arc 0 = conformation ((table.edge e).source) := by
  rw [applyAt_source_endpoint, motion.starts_identity]
  rfl

/-- End-time compatibility: at motion time `1` the fixed-time action is the transport by the
endpoint homeomorphism. -/
theorem applyAt_one (motion : AmbientMotion)
    (table : BondPathTable E molecule conformation) :
    table.applyAt motion 1 = table.mapHomeomorph motion.endpoint := rfl

/-- The identity motion acts trivially at every fixed time. -/
theorem applyAt_identity (u : unitInterval)
    (table : BondPathTable E molecule conformation) :
    table.applyAt AmbientMotion.identity u = table := by
  simp only [applyAt, AmbientMotion.identity_map]
  exact mapHomeomorph_refl table

end BondPathTable

/-! ### Source-bound configurations -/

namespace SourceBoundEmbeddedBondPaths

/-- Fixed-time ambient action on a complete source-bound embedded bond-path configuration.
The authoritative source, the edge count, every occurrence (source interaction) index, every
oriented endpoint atom index and the documented interaction subset are retained; the single
homeomorphism `motion.map u` is applied to the conformation and to every arc at once.  This is
the `OrganicStereoEmbeddedBondPaths` integration: it uses the real `BondPathTable` data rather
than the pointwise `applyCurve` trajectory action. -/
def applyAt (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) : SourceBoundEmbeddedBondPaths where
  source := input.source
  edgeCount := input.edgeCount
  conformation := fun atom => motion.map u (input.conformation atom)
  table := input.table.applyAt motion u

/-- The source is retained verbatim. -/
@[simp] theorem applyAt_source (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) :
    (input.applyAt motion u).source = input.source := rfl

/-- The edge count is retained. -/
@[simp] theorem applyAt_edgeCount (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) :
    (input.applyAt motion u).edgeCount = input.edgeCount := rfl

/-- The source conformation is moved by the fixed-time homeomorphism. -/
@[simp] theorem applyAt_conformation_apply (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) (atom : Fin input.source.molecule.atomCount) :
    (input.applyAt motion u).conformation atom = motion.map u (input.conformation atom) := rfl

/-- The adapted table is exactly the fixed-time bonded-table action. -/
@[simp] theorem applyAt_table (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) :
    (input.applyAt motion u).table = input.table.applyAt motion u := rfl

/-- The documented interaction subset is retained. -/
@[simp] theorem applyAt_documented (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) :
    (input.applyAt motion u).table.documented = input.table.documented := rfl

/-- Every source interaction (occurrence) index is retained. -/
@[simp] theorem applyAt_edge_sourceInteraction (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) :
    ((input.applyAt motion u).table.edge e).sourceInteraction =
      (input.table.edge e).sourceInteraction := rfl

/-- Every oriented source atom index is retained. -/
@[simp] theorem applyAt_edge_source (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) :
    ((input.applyAt motion u).table.edge e).source = (input.table.edge e).source := rfl

/-- Every oriented target atom index is retained. -/
@[simp] theorem applyAt_edge_target (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) :
    ((input.applyAt motion u).table.edge e).target = (input.table.edge e).target := rfl

/-- At fixed motion time `u`, the spatial arc parameter `s` stays spatial: the arc value is
moved by the single homeomorphism `motion.map u`. -/
@[simp] theorem applyAt_edge_arc (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) (s : unitInterval) :
    ((input.applyAt motion u).table.edge e).arc s =
      motion.map u ((input.table.edge e).arc s) := rfl

/-- The adapted arc at parameter `0` is the moved source atom position, via the original
realization endpoint equation. -/
theorem applyAt_source_endpoint (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) :
    ((input.applyAt motion u).table.edge e).arc 0 =
      motion.map u (input.conformation ((input.table.edge e).source)) := by
  rw [applyAt_edge_arc, input.table.valid.source_endpoint e]

/-- The adapted arc at parameter `1` is the moved target atom position, via the original
realization endpoint equation. -/
theorem applyAt_target_endpoint (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) :
    ((input.applyAt motion u).table.edge e).arc 1 =
      motion.map u (input.conformation ((input.table.edge e).target)) := by
  rw [applyAt_edge_arc, input.table.valid.target_endpoint e]

/-- The source conformation remains injective after the fixed-time action. -/
theorem applyAt_atom_injective (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) :
    Function.Injective (fun atom => motion.map u (input.conformation atom)) :=
  (input.applyAt motion u).table.valid.atom_injective

/-- Every adapted arc remains spatially injective. -/
theorem applyAt_arc_injective (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) :
    Function.Injective ((input.applyAt motion u).table.edge e).arc :=
  (input.applyAt motion u).table.valid.arc_injective e

/-- Adapted arc interiors still avoid every atom position. -/
theorem applyAt_interior_avoids_atoms (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) :
    ∀ e (s : unitInterval), s ≠ 0 → s ≠ 1 → ∀ a,
      ((input.applyAt motion u).table.edge e).arc s ≠
        (fun atom => motion.map u (input.conformation atom)) a :=
  (input.applyAt motion u).table.valid.interior_avoids_atoms

/-- Distinct adapted arcs still meet only at a common endpoint atom. -/
theorem applyAt_intersects_only_at_common_endpoints (motion : AmbientMotion) (u : unitInterval)
    (input : SourceBoundEmbeddedBondPaths) :
    ∀ e f (s t : unitInterval), e ≠ f →
      ((input.applyAt motion u).table.edge e).arc s =
        ((input.applyAt motion u).table.edge f).arc t →
      ∃ a : Fin input.source.molecule.atomCount,
        ((input.applyAt motion u).table.edge e).endpointAt? s = some a ∧
          ((input.applyAt motion u).table.edge f).endpointAt? t = some a :=
  (input.applyAt motion u).table.valid.intersects_only_at_common_endpoints

/-- At time zero the documented interaction subset is unchanged. -/
@[simp] theorem applyAt_zero_documented (motion : AmbientMotion)
    (input : SourceBoundEmbeddedBondPaths) :
    (input.applyAt motion 0).table.documented = input.table.documented := rfl

/-- At time zero every source interaction (occurrence) index is unchanged. -/
@[simp] theorem applyAt_zero_edge_sourceInteraction (motion : AmbientMotion)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) :
    ((input.applyAt motion 0).table.edge e).sourceInteraction =
      (input.table.edge e).sourceInteraction := rfl

/-- At time zero every oriented source atom index is unchanged. -/
@[simp] theorem applyAt_zero_edge_source (motion : AmbientMotion)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) :
    ((input.applyAt motion 0).table.edge e).source = (input.table.edge e).source := rfl

/-- At time zero every oriented target atom index is unchanged. -/
@[simp] theorem applyAt_zero_edge_target (motion : AmbientMotion)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) :
    ((input.applyAt motion 0).table.edge e).target = (input.table.edge e).target := rfl

/-- At time zero every arc value is unchanged. -/
@[simp] theorem applyAt_zero_edge_arc (motion : AmbientMotion)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) (s : unitInterval) :
    ((input.applyAt motion 0).table.edge e).arc s = (input.table.edge e).arc s := by
  rw [applyAt_edge_arc, motion.starts_identity]
  rfl

/-- At time zero the adapted arc still starts at the original source atom position. -/
theorem applyAt_zero_source_endpoint (motion : AmbientMotion)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) :
    ((input.applyAt motion 0).table.edge e).arc 0 =
      input.conformation ((input.table.edge e).source) := by
  rw [applyAt_source_endpoint, motion.starts_identity]
  rfl

/-- At time zero the adapted arc still finishes at the original target atom position. -/
theorem applyAt_zero_target_endpoint (motion : AmbientMotion)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) :
    ((input.applyAt motion 0).table.edge e).arc 1 =
      input.conformation ((input.table.edge e).target) := by
  rw [applyAt_target_endpoint, motion.starts_identity]
  rfl

/-- Identity (time-zero) compatibility: the whole source-bound configuration is unchanged at
motion time `0`. -/
theorem applyAt_zero (motion : AmbientMotion) (input : SourceBoundEmbeddedBondPaths) :
    input.applyAt motion 0 = input := by
  cases input with
  | mk source edgeCount conformation table =>
    simp only [applyAt, BondPathTable.applyAt]
    rw [motion.starts_identity]
    simp [BondPathTable.mapHomeomorph_refl]

/-- End-time compatibility: at motion time `1` the table is the transport by the endpoint
homeomorphism, while the source and the indices are unchanged. -/
@[simp] theorem applyAt_one_table (motion : AmbientMotion)
    (input : SourceBoundEmbeddedBondPaths) :
    (input.applyAt motion 1).table = input.table.mapHomeomorph motion.endpoint := rfl

/-- At motion time `1` every atom position is moved by the endpoint homeomorphism. -/
@[simp] theorem applyAt_one_conformation (motion : AmbientMotion)
    (input : SourceBoundEmbeddedBondPaths) (atom : Fin input.source.molecule.atomCount) :
    (input.applyAt motion 1).conformation atom = motion.endpoint (input.conformation atom) := rfl

/-- At motion time `1` every arc value is moved by the endpoint homeomorphism. -/
@[simp] theorem applyAt_one_edge_arc (motion : AmbientMotion)
    (input : SourceBoundEmbeddedBondPaths) (e : Fin input.edgeCount) (s : unitInterval) :
    ((input.applyAt motion 1).table.edge e).arc s =
      motion.endpoint ((input.table.edge e).arc s) := rfl

/-- The identity motion leaves every source-bound configuration unchanged at every fixed
time. -/
theorem applyAt_identity (u : unitInterval) (input : SourceBoundEmbeddedBondPaths) :
    input.applyAt AmbientMotion.identity u = input := by
  cases input with
  | mk source edgeCount conformation table =>
    simp only [applyAt, BondPathTable.applyAt, AmbientMotion.identity_map]
    simp [BondPathTable.mapHomeomorph_refl]

end SourceBoundEmbeddedBondPaths

end OneCenter
end TetraStereo
