/-
Copyright (c) 2026 TetraStereo contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import TetraStereo.KernelOnly
import TetraStereo.OneCenter.OrganicStereoConformationTrajectoryObstruction
import TetraStereo.OneCenter.OrganicStereoRealConfiguration
import TetraStereo.OneCenter.P94Conformation

set_option autoImplicit false

open scoped Classical

namespace TetraStereo
namespace OneCenter

open BlueBookP94

noncomputable section

/-!
# Atom-reindexed conformation trajectories and faithful P-94 transport

The existing continuous trajectory carrier is `ConformationTrajectory V` from
`OrganicStereoConformationTrajectoryObstruction`: a time-indexed real conformation together with
the proof that every atom path is continuous.  The existing atom reindexing operation on a single
conformation is `MolecularConformation.reindex` from `OrganicStereoRealConfiguration`, with the
proved inverse laws `reindex_reindex` and `reindex_reindex_symm`.

This module extends the *existing* `ConformationTrajectory` namespace (rather than introducing a
second trajectory wrapper) with the atom-reindexing action built from the actual
`MolecularConformation.reindex`:

* `ConformationTrajectory.reindex` reindexes the atom labels of the whole trajectory;
* `reindex_reindex` / `reindex_reindex_symm` are the full inverse laws (structure equality);
  `reindex_trajectory_reindex` / `reindex_trajectory_reindex_symm` are the pointwise laws;
* `continuous_reindex_atom` records that the reindexed trajectory still has a continuous path at
  every atom, and `reindex_trajectory_apply` exposes the path at a concrete atom;
* `initial_reindex` / `final_reindex` record preservation of both endpoints;
* `TrajectoryEnsemble` and its `reindex` act on an arbitrary set of allowed trajectories, with
  exact membership transport and exact image recovery in both directions
  (`reindex_reindex`, `reindex_reindex_symm`, `image_reindex_image`);
* `AmbientMotion.toConformationTrajectory` adapts the existing ambient-motion data (via the
  existing `AmbientMotion.continuous_trajectory`) to the continuous trajectory carrier.  It
  preserves the full parameterized trajectory, commutes with atom reindexing, preserves both
  endpoints, and transports arbitrary allowed sets of initial conformations
  (`AmbientMotion.allowedTrajectories`, `AmbientMotion.allowedTrajectories_reindex`);
* `ConformationTrajectory.snapshotSet` records the range of the time parameterization, and
  `SnapshotReparameterizationWitness.distinct_trajectories_same_snapshotSet` gives two *distinct*
  continuous trajectories (the forward and reverse traversals of one real segment) with exactly
  the same snapshot set.  The full parameterized function, not just its range, is therefore what
  the reindexing action preserves.

The second half transports the real P-94 P-94.1 interconversion relation.  The direct
single-bond-rotation relation is *supplied data*
`singleBondRotation : MolecularConformation V → MolecularConformation V → Prop`; nothing here
infers a rotation, a barrier, a rate, a kinetic pathway or chemical admissibility from the
continuity of a trajectory.  `TransportSingleBondRotation e rotation` is the honest image of that
relation under the atom equivalence `e`, and

* `transportSingleBondRotation_reindex_iff` and
  `transportSingleBondRotation_preimage_iff` prove that single steps are transported *and
  reflected*, without assuming the inverse transport law;
* `interconvertibleBySingleBondRotations_transport_iff` and
  `interconvertibleBySingleBondRotations_preimage_iff` prove that the *whole*
  `InterconvertibleBySingleBondRotations` transition relation is preserved in both directions;
* `directedRotationPath_map_reindex` shows that a complete ordered rotation path is retained,
  not merely its endpoints or its set of states;
* `interconvertibleBySingleBondRotations_initial_reindex_iff` and the `final` version use the same
  atom equivalence `e` simultaneously for trajectory transport and for relation transport.

Finally, `SingleBondRotationInformationWitness` exhibits two *different* supplied rotation
relations on the *same* set of real molecular conformations that have exactly the same set of
states occurring as rotation endpoints but different P-94.1 interconversion relations.  This is a
concrete statement that the transition relation is genuine information that is not recoverable
from the static endpoint set alone.  The witness conformations are genuine real
`MolecularConformation`s; no chemical admissibility of the witness edges is claimed.

## Scope

No result here asserts that any particular supplied edge is a physically allowed rotation, that
two interconvertible conformations are chemically distinct (P-94 requires that separately via
`AreConformers`), or that a continuous trajectory realizes a sequence of single-bond rotations.
The relation data is an independent input and is transported faithfully; it is not derived from
continuity.
-/

/-! ## Atom reindexing of the existing continuous trajectory carrier -/

namespace ConformationTrajectory

variable {V W : Type*}

/-- Atom reindexing of a whole conformation trajectory, built from the actual
`MolecularConformation.reindex`.  The continuity proof of the reindexed trajectory is the
continuity proof of the corresponding source atom path; no topology on the atom index is used. -/
def reindex (equivalent : V ≃ W) (trajectory : ConformationTrajectory V) :
    ConformationTrajectory W where
  trajectory time := MolecularConformation.reindex equivalent (trajectory.trajectory time)
  continuous_atom atom := trajectory.continuous_atom (equivalent.symm atom)

/-- The time-`t` conformation of a reindexed trajectory is the reindexed time-`t`
conformation. -/
@[simp] theorem reindex_trajectory (equivalent : V ≃ W)
    (trajectory : ConformationTrajectory V) (time : unitInterval) :
    (reindex equivalent trajectory).trajectory time =
      MolecularConformation.reindex equivalent (trajectory.trajectory time) := rfl

/-- Pointwise atom formula for a reindexed trajectory: the new atom `atom` follows exactly the
source trajectory of `equivalent.symm atom`. -/
@[simp] theorem reindex_trajectory_apply (equivalent : V ≃ W)
    (trajectory : ConformationTrajectory V) (time : unitInterval) (atom : W) :
    (reindex equivalent trajectory).trajectory time atom =
      trajectory.trajectory time (equivalent.symm atom) := rfl

/-- Every atom of a reindexed trajectory follows a continuous path in time. -/
theorem continuous_reindex_atom (equivalent : V ≃ W)
    (trajectory : ConformationTrajectory V) (atom : W) :
    Continuous fun time => (reindex equivalent trajectory).trajectory time atom :=
  (reindex equivalent trajectory).continuous_atom atom

/-- The same continuity obligation expressed on the source atom. -/
theorem continuous_reindex_atom_source (equivalent : V ≃ W)
    (trajectory : ConformationTrajectory V) (atom : W) :
    Continuous fun time => trajectory.trajectory time (equivalent.symm atom) :=
  trajectory.continuous_atom (equivalent.symm atom)

/-- Trajectories are determined by their underlying time-indexed conformation; the continuity
certificate is a proposition, so it carries no extra data. -/
theorem trajectory_ext {first second : ConformationTrajectory V}
    (trajectories : first.trajectory = second.trajectory) : first = second := by
  cases first with
  | mk firstTrajectory firstContinuous =>
    cases second with
    | mk secondTrajectory secondContinuous =>
      simp only at trajectories
      subst trajectories
      rw [Subsingleton.elim firstContinuous secondContinuous]

/-- Pointwise inverse law: reindexing by `e` and then by `e.symm` returns the original
time-`t` conformation. -/
theorem reindex_trajectory_reindex (equivalent : V ≃ W)
    (trajectory : ConformationTrajectory V) (time : unitInterval) :
    (reindex equivalent.symm (reindex equivalent trajectory)).trajectory time =
      trajectory.trajectory time := by
  rw [reindex_trajectory, reindex_trajectory]
  exact MolecularConformation.reindex_reindex equivalent (trajectory.trajectory time)

/-- Full inverse law: reindexing by `e` and then by `e.symm` returns the original trajectory. -/
theorem reindex_reindex (equivalent : V ≃ W) (trajectory : ConformationTrajectory V) :
    reindex equivalent.symm (reindex equivalent trajectory) = trajectory := by
  apply trajectory_ext
  funext time
  exact reindex_trajectory_reindex equivalent trajectory time

/-- Pointwise inverse law in the other direction. -/
theorem reindex_trajectory_reindex_symm (equivalent : V ≃ W)
    (trajectory : ConformationTrajectory W) (time : unitInterval) :
    (reindex equivalent (reindex equivalent.symm trajectory)).trajectory time =
      trajectory.trajectory time := by
  rw [reindex_trajectory, reindex_trajectory]
  exact MolecularConformation.reindex_reindex_symm equivalent (trajectory.trajectory time)

/-- Full inverse law in the other direction. -/
theorem reindex_reindex_symm (equivalent : V ≃ W)
    (trajectory : ConformationTrajectory W) :
    reindex equivalent (reindex equivalent.symm trajectory) = trajectory := by
  apply trajectory_ext
  funext time
  exact reindex_trajectory_reindex_symm equivalent trajectory time

/-- Trajectory reindexing is injective. -/
theorem reindex_injective (equivalent : V ≃ W) :
    Function.Injective (reindex (V := V) (W := W) equivalent) := by
  intro first second equal
  have transported := congrArg (reindex equivalent.symm) equal
  simpa [reindex_reindex] using transported

/-- Trajectory reindexing is surjective. -/
theorem reindex_surjective (equivalent : V ≃ W) :
    Function.Surjective (reindex (V := V) (W := W) equivalent) :=
  fun trajectory => ⟨reindex equivalent.symm trajectory,
    reindex_reindex_symm equivalent trajectory⟩

/-- Trajectory reindexing is a bijection on trajectories. -/
theorem reindex_bijective (equivalent : V ≃ W) :
    Function.Bijective (reindex (V := V) (W := W) equivalent) :=
  ⟨reindex_injective equivalent, reindex_surjective equivalent⟩

/-- The initial conformation of a trajectory. -/
def initial (trajectory : ConformationTrajectory V) : MolecularConformation V :=
  trajectory.trajectory 0

/-- The final conformation of a trajectory. -/
def final (trajectory : ConformationTrajectory V) : MolecularConformation V :=
  trajectory.trajectory 1

/-- The initial endpoint is preserved: it is the reindexed initial conformation. -/
@[simp] theorem initial_reindex (equivalent : V ≃ W)
    (trajectory : ConformationTrajectory V) :
    (reindex equivalent trajectory).initial =
      MolecularConformation.reindex equivalent trajectory.initial := rfl

/-- The final endpoint is preserved: it is the reindexed final conformation. -/
@[simp] theorem final_reindex (equivalent : V ≃ W)
    (trajectory : ConformationTrajectory V) :
    (reindex equivalent trajectory).final =
      MolecularConformation.reindex equivalent trajectory.final := rfl

/-! ### The snapshot range of a trajectory

A trajectory carries a whole time parameterization, not just the set of conformations it visits.
`snapshotSet` records that set (the range of the time map).  The witness below exhibits two
distinct continuous trajectories with exactly the same snapshot set.  The atom-reindexing
transport above acts on the parameterized function, not merely on this range. -/

/-- The set of conformations visited by a trajectory, i.e. the range of its time map. -/
def snapshotSet (trajectory : ConformationTrajectory V) : Set (MolecularConformation V) :=
  Set.range trajectory.trajectory

/-- The constant trajectory at one conformation. -/
def constant (conformation : MolecularConformation V) : ConformationTrajectory V where
  trajectory _ := conformation
  continuous_atom _ := continuous_const

/-- The snapshot range of a constant trajectory is the singleton of that conformation. -/
@[simp] theorem snapshotSet_constant (conformation : MolecularConformation V) :
    snapshotSet (constant conformation) = {conformation} := by
  ext candidate
  constructor
  · rintro ⟨time, imageEq⟩
    simpa using imageEq.symm
  · intro member
    exact ⟨0, member.symm⟩

/-- The two endpoints of the unit interval are distinct. -/
theorem unitInterval_zero_ne_one : (0 : unitInterval) ≠ 1 := by
  intro equal
  have values := congrArg (fun time : unitInterval => (time : ℝ)) equal
  norm_num at values

/-- The time map of a constant trajectory is not injective.  (The distinct-trajectory witness
`SnapshotReparameterizationWitness.distinct_trajectories_same_snapshotSet` is the separate
statement that the snapshot range alone loses the time parameterization.) -/
theorem constant_trajectory_noninjective (conformation : MolecularConformation V) :
    ¬ Function.Injective (constant conformation).trajectory := by
  intro injective
  have images : (constant conformation).trajectory 0 =
      (constant conformation).trajectory 1 := rfl
  exact unitInterval_zero_ne_one (injective images)

/-- The snapshot range is transported pointwise by atom reindexing. -/
theorem snapshotSet_reindex (equivalent : V ≃ W) (trajectory : ConformationTrajectory V) :
    snapshotSet (reindex equivalent trajectory) =
      MolecularConformation.reindex equivalent '' snapshotSet trajectory := by
  ext candidate
  constructor
  · rintro ⟨time, imageEq⟩
    exact ⟨trajectory.trajectory time, ⟨time, rfl⟩, imageEq⟩
  · rintro ⟨source, ⟨time, rfl⟩, imageEq⟩
    exact ⟨time, imageEq⟩

end ConformationTrajectory

/-! ## Two distinct trajectories with the same snapshot range

The forward and reverse traversals of one real segment visit exactly the same conformations but
are different parameterized trajectories (they differ at time zero).  This is a concrete
regression showing why the transport must retain the full trajectory rather than only its set of
visited conformations. -/

namespace SnapshotReparameterizationWitness

open ConformationTrajectory

/-- The nonzero real point `(1, 0, 0)` used as the path endpoint. -/
def snapshotEndpoint : Real3 :=
  WithLp.toLp 2 (fun index : Fin 3 => ![(1 : ℝ), 0, 0] index)

theorem snapshotEndpoint_ne_zero : snapshotEndpoint ≠ (0 : Real3) := by
  intro equal
  have coordinate := congrArg (fun point : Real3 => point 0) equal
  simp [snapshotEndpoint] at coordinate

/-- The straight path from the origin to `(1, 0, 0)` on a one-atom conformation. -/
def pathConformation (time : unitInterval) : MolecularConformation (Fin 1) :=
  fun _ => (time : ℝ) • snapshotEndpoint

/-- The same path traversed in the reverse time direction. -/
def reversePathConformation (time : unitInterval) : MolecularConformation (Fin 1) :=
  pathConformation (unitInterval.symm time)

theorem continuous_pathConformation :
    ∀ atom : Fin 1, Continuous fun time : unitInterval => pathConformation time atom := by
  intro atom
  simpa [pathConformation] using
    (continuous_subtype_val.smul
      (continuous_const : Continuous fun _ : unitInterval => snapshotEndpoint))

theorem continuous_reversePathConformation :
    ∀ atom : Fin 1, Continuous fun time : unitInterval => reversePathConformation time atom := by
  intro atom
  exact (continuous_pathConformation atom).comp unitInterval.continuous_symm

/-- The forward traversal. -/
def forwardPath : ConformationTrajectory (Fin 1) where
  trajectory := pathConformation
  continuous_atom := continuous_pathConformation

/-- The reverse traversal. -/
def reversePath : ConformationTrajectory (Fin 1) where
  trajectory := reversePathConformation
  continuous_atom := continuous_reversePathConformation

/-- The forward and reverse traversals visit exactly the same conformations. -/
theorem snapshotSet_reversePath_eq_forwardPath :
    snapshotSet reversePath = snapshotSet forwardPath := by
  ext candidate
  constructor
  · rintro ⟨time, imageEq⟩
    exact ⟨unitInterval.symm time, imageEq⟩
  · rintro ⟨time, imageEq⟩
    refine ⟨unitInterval.symm time, ?_⟩
    change pathConformation (unitInterval.symm (unitInterval.symm time)) = candidate
    rw [unitInterval.symm_symm]
    exact imageEq

/-- The two traversals are different trajectories: they assign different conformations at time
zero. -/
theorem forwardPath_ne_reversePath : forwardPath ≠ reversePath := by
  intro equal
  have trajectoryEqual := congrArg ConformationTrajectory.trajectory equal
  have timeEqual := congrFun trajectoryEqual 0
  have atomEqual := congrFun timeEqual 0
  have endpointZero : snapshotEndpoint = 0 := by
    simpa [forwardPath, reversePath, pathConformation, reversePathConformation]
      using atomEqual.symm
  exact snapshotEndpoint_ne_zero endpointZero

/-- **The snapshot range loses the time parameterization.**  Two distinct continuous
trajectories, the forward and reverse traversals of the same real segment, have exactly the same
snapshot range. -/
theorem distinct_trajectories_same_snapshotSet :
    forwardPath ≠ reversePath ∧ snapshotSet forwardPath = snapshotSet reversePath :=
  ⟨forwardPath_ne_reversePath, snapshotSet_reversePath_eq_forwardPath.symm⟩

end SnapshotReparameterizationWitness

/-! ## Arbitrary allowed sets of trajectories -/

/-- An arbitrary set of allowed conformation trajectories.  This is the trajectory analogue of the
existing `MolecularConformation.Ensemble`; it adds no new state wrapper. -/
abbrev TrajectoryEnsemble (V : Type*) := Set (ConformationTrajectory V)

namespace TrajectoryEnsemble

variable {V W : Type*}

/-- Transport an arbitrary allowed set of trajectories along an atom equivalence: the exact image
of the set under trajectory reindexing. -/
def reindex (equivalent : V ≃ W) (trajectories : TrajectoryEnsemble V) :
    TrajectoryEnsemble W :=
  ConformationTrajectory.reindex equivalent '' trajectories

/-- Membership in the transported set is exactly the existence of a source member mapping to the
given trajectory. -/
@[simp] theorem mem_reindex_iff (equivalent : V ≃ W)
    (trajectories : TrajectoryEnsemble V) (trajectory : ConformationTrajectory W) :
    trajectory ∈ reindex equivalent trajectories ↔
      ∃ source ∈ trajectories,
        ConformationTrajectory.reindex equivalent source = trajectory :=
  Iff.rfl

/-- Both directions of membership transport for actual source members: the reindexed image of a
source trajectory belongs to the transported set exactly when the source trajectory belongs to the
original set. -/
theorem reindex_mem_iff_of_source (equivalent : V ≃ W)
    (trajectories : TrajectoryEnsemble V) (trajectory : ConformationTrajectory V) :
    ConformationTrajectory.reindex equivalent trajectory ∈
        reindex equivalent trajectories ↔
      trajectory ∈ trajectories := by
  rw [mem_reindex_iff]
  constructor
  · rintro ⟨source, sourceMember, imageEq⟩
    have : source = trajectory :=
      ConformationTrajectory.reindex_injective equivalent imageEq
    simpa [this] using sourceMember
  · intro member
    exact ⟨trajectory, member, rfl⟩

/-- The image of a permitted source trajectory is permitted. -/
theorem reindex_mem (equivalent : V ≃ W) (trajectories : TrajectoryEnsemble V)
    {trajectory : ConformationTrajectory V} (member : trajectory ∈ trajectories) :
    ConformationTrajectory.reindex equivalent trajectory ∈
      reindex equivalent trajectories :=
  (reindex_mem_iff_of_source equivalent trajectories trajectory).mpr member

/-- Reindexing an arbitrary allowed trajectory set by `e` and then by `e.symm` recovers the
original set exactly. -/
theorem reindex_reindex (equivalent : V ≃ W) (trajectories : TrajectoryEnsemble V) :
    reindex equivalent.symm (reindex equivalent trajectories) = trajectories := by
  ext trajectory
  constructor
  · intro member
    rw [mem_reindex_iff] at member
    obtain ⟨middle, middleMember, middleEq⟩ := member
    rw [mem_reindex_iff] at middleMember
    obtain ⟨source, sourceMember, sourceEq⟩ := middleMember
    rw [← middleEq, ← sourceEq, ConformationTrajectory.reindex_reindex]
    exact sourceMember
  · intro member
    rw [mem_reindex_iff]
    exact ⟨ConformationTrajectory.reindex equivalent trajectory,
      ⟨trajectory, member, rfl⟩,
      ConformationTrajectory.reindex_reindex equivalent trajectory⟩

/-- The symmetric inverse law for arbitrary allowed trajectory sets. -/
theorem reindex_reindex_symm (equivalent : V ≃ W)
    (trajectories : TrajectoryEnsemble W) :
    reindex equivalent (reindex equivalent.symm trajectories) = trajectories := by
  ext trajectory
  constructor
  · intro member
    rw [mem_reindex_iff] at member
    obtain ⟨middle, middleMember, middleEq⟩ := member
    rw [mem_reindex_iff] at middleMember
    obtain ⟨source, sourceMember, sourceEq⟩ := middleMember
    rw [← middleEq, ← sourceEq, ConformationTrajectory.reindex_reindex_symm]
    exact sourceMember
  · intro member
    rw [mem_reindex_iff]
    exact ⟨ConformationTrajectory.reindex equivalent.symm trajectory,
      ⟨trajectory, member, rfl⟩,
      ConformationTrajectory.reindex_reindex_symm equivalent trajectory⟩

/-- Exact image recovery for an arbitrary allowed trajectory set: taking the reindexed image and
then the image under the inverse equivalence returns the original set. -/
theorem image_reindex_image (equivalent : V ≃ W)
    (trajectories : TrajectoryEnsemble V) :
    ConformationTrajectory.reindex equivalent.symm ''
        (ConformationTrajectory.reindex equivalent '' trajectories) = trajectories := by
  change reindex equivalent.symm (reindex equivalent trajectories) = trajectories
  exact reindex_reindex equivalent trajectories

/-- Exact image recovery in the opposite direction. -/
theorem image_reindex_image_symm (equivalent : V ≃ W)
    (trajectories : TrajectoryEnsemble W) :
    ConformationTrajectory.reindex equivalent ''
        (ConformationTrajectory.reindex equivalent.symm '' trajectories) = trajectories := by
  change reindex equivalent (reindex equivalent.symm trajectories) = trajectories
  exact reindex_reindex_symm equivalent trajectories

/-- Set-level reindexing is injective. -/
theorem reindex_injective (equivalent : V ≃ W) :
    Function.Injective (reindex (V := V) (W := W) equivalent) := by
  intro first second equal
  have transported := congrArg (reindex equivalent.symm) equal
  simpa [reindex_reindex] using transported

/-- Set-level reindexing is surjective. -/
theorem reindex_surjective (equivalent : V ≃ W) :
    Function.Surjective (reindex (V := V) (W := W) equivalent) :=
  fun trajectories => ⟨reindex equivalent.symm trajectories,
    reindex_reindex_symm equivalent trajectories⟩

end TrajectoryEnsemble

/-! ## Adapter from the existing ambient-motion data

`AmbientMotion` already supplies, for every supplied motion and every point, a continuous
trajectory `AmbientMotion.continuous_trajectory`.  The adapter below packages the pointwise
motion of a whole conformation into the existing continuous trajectory carrier, retaining the
full time parameterization. -/

namespace AmbientMotion

variable {V W : Type*}

/-- The continuous conformation trajectory generated by a supplied ambient motion applied
pointwise to an initial real conformation.  The continuity certificate is the existing
`AmbientMotion.continuous_trajectory` at each atom. -/
def toConformationTrajectory (motion : AmbientMotion)
    (conformation : MolecularConformation V) : ConformationTrajectory V where
  trajectory time := motion.applyAt time conformation
  continuous_atom atom := by
    simpa [applyAt, applyPoint] using motion.continuous_trajectory (conformation atom)

/-- The parameterized time map of the adapted trajectory is exactly the pointwise motion. -/
@[simp] theorem toConformationTrajectory_trajectory (motion : AmbientMotion)
    (conformation : MolecularConformation V) :
    (motion.toConformationTrajectory conformation).trajectory =
      fun time => motion.applyAt time conformation := rfl

/-- Pointwise atom form of the adapted trajectory. -/
@[simp] theorem toConformationTrajectory_apply (motion : AmbientMotion)
    (conformation : MolecularConformation V) (time : unitInterval) (atom : V) :
    (motion.toConformationTrajectory conformation).trajectory time atom =
      motion.map time (conformation atom) := rfl

/-- The adapted trajectory starts at the supplied conformation. -/
@[simp] theorem toConformationTrajectory_initial (motion : AmbientMotion)
    (conformation : MolecularConformation V) :
    (motion.toConformationTrajectory conformation).initial = conformation :=
  motion.applyAt_zero conformation

/-- The adapted trajectory ends at the endpoint action of the motion. -/
@[simp] theorem toConformationTrajectory_final (motion : AmbientMotion)
    (conformation : MolecularConformation V) :
    (motion.toConformationTrajectory conformation).final =
      motion.applyEndpoint conformation :=
  motion.applyAt_one conformation

/-- Atom reindexing commutes with the ambient-motion adapter: the same atom equivalence acts on
the parameterized trajectory and on the initial conformation, with no loss of the time
parameterization. -/
theorem toConformationTrajectory_reindex (equivalent : V ≃ W)
    (motion : AmbientMotion) (conformation : MolecularConformation V) :
    ConformationTrajectory.reindex equivalent
        (motion.toConformationTrajectory conformation) =
      motion.toConformationTrajectory
        (MolecularConformation.reindex equivalent conformation) := by
  apply ConformationTrajectory.trajectory_ext
  funext time
  rw [ConformationTrajectory.reindex_trajectory]
  funext atom
  rfl

/-- The set of trajectories generated by an ambient motion from an arbitrary allowed set of
initial conformations.  It keeps the whole parameterized trajectory of each admitted initial
conformation. -/
def allowedTrajectories (motion : AmbientMotion)
    (allowed : Set (MolecularConformation V)) : TrajectoryEnsemble V :=
  motion.toConformationTrajectory '' allowed

/-- Membership in the generated trajectory set is exactly being the adapted trajectory of an
admitted initial conformation. -/
@[simp] theorem mem_allowedTrajectories_iff (motion : AmbientMotion)
    (allowed : Set (MolecularConformation V)) (trajectory : ConformationTrajectory V) :
    trajectory ∈ motion.allowedTrajectories allowed ↔
      ∃ conformation ∈ allowed,
        motion.toConformationTrajectory conformation = trajectory :=
  Iff.rfl

/-- Transporting an ambient generated allowed trajectory set along an atom equivalence is exactly
the ambient generated set of the transported allowed initial conformations.  This is the set-level
form of the parametrized adapter commutation. -/
theorem allowedTrajectories_reindex (equivalent : V ≃ W)
    (motion : AmbientMotion) (allowed : Set (MolecularConformation V)) :
    TrajectoryEnsemble.reindex equivalent (motion.allowedTrajectories allowed) =
      motion.allowedTrajectories
        (MolecularConformation.reindex equivalent '' allowed) := by
  ext trajectory
  rw [TrajectoryEnsemble.mem_reindex_iff]
  constructor
  · rintro ⟨source, ⟨conformation, member, rfl⟩, rfl⟩
    exact ⟨MolecularConformation.reindex equivalent conformation,
      ⟨conformation, member, rfl⟩,
      (toConformationTrajectory_reindex equivalent motion conformation).symm⟩
  · rintro ⟨conformation, ⟨source, member, rfl⟩, rfl⟩
    exact ⟨motion.toConformationTrajectory source,
      ⟨source, member, rfl⟩,
      toConformationTrajectory_reindex equivalent motion source⟩

/-- Exact recovery of an ambient generated allowed trajectory set after reindexing and inverse
reindexing. -/
theorem allowedTrajectories_image_recovery (equivalent : V ≃ W)
    (motion : AmbientMotion) (allowed : Set (MolecularConformation V)) :
    ConformationTrajectory.reindex equivalent.symm ''
        (ConformationTrajectory.reindex equivalent ''
          motion.allowedTrajectories allowed) =
      motion.allowedTrajectories allowed :=
  TrajectoryEnsemble.image_reindex_image equivalent _

end AmbientMotion

/-! ## Faithful transport of the P-94.1 transition relation

`InterconvertibleBySingleBondRotations` from `P94Conformation` is an inductive relation over an
arbitrary state type.  Here its state type is instantiated at the *actual* real conformation type
`MolecularConformation V`, and the direct rotation relation is supplied as independent data. -/

namespace BlueBookP94

variable {V W : Type*}

/-- The image of a supplied direct single-bond-rotation relation under an atom equivalence.  A
transported step exists exactly when the target pair is the reindexed image of an actual source
step.  The relation is data: it is neither derived from nor constrained by trajectory
continuity. -/
def TransportSingleBondRotation (equivalent : V ≃ W)
    (singleBondRotation : MolecularConformation V → MolecularConformation V → Prop) :
    MolecularConformation W → MolecularConformation W → Prop :=
  fun first second =>
    ∃ firstSource secondSource : MolecularConformation V,
      MolecularConformation.reindex equivalent firstSource = first ∧
        MolecularConformation.reindex equivalent secondSource = second ∧
          singleBondRotation firstSource secondSource

/-- Single steps are transported and reflected exactly on reindexed states.  The proof uses the
proved injectivity of `MolecularConformation.reindex`; no inverse transport law is assumed. -/
theorem transportSingleBondRotation_reindex_iff (equivalent : V ≃ W)
    (singleBondRotation : MolecularConformation V → MolecularConformation V → Prop)
    (first second : MolecularConformation V) :
    TransportSingleBondRotation equivalent singleBondRotation
        (MolecularConformation.reindex equivalent first)
        (MolecularConformation.reindex equivalent second) ↔
      singleBondRotation first second := by
  constructor
  · rintro ⟨firstSource, secondSource, firstImage, secondImage, rotation⟩
    have firstEq : firstSource = first :=
      MolecularConformation.reindex_injective equivalent firstImage
    have secondEq : secondSource = second :=
      MolecularConformation.reindex_injective equivalent secondImage
    rw [firstEq, secondEq] at rotation
    exact rotation
  · intro rotation
    exact ⟨first, second, rfl, rfl, rotation⟩

/-- The transported relation at arbitrary target states is exactly the source relation read
through `equivalent.symm`. -/
theorem transportSingleBondRotation_preimage_iff (equivalent : V ≃ W)
    (singleBondRotation : MolecularConformation V → MolecularConformation V → Prop)
    (first second : MolecularConformation W) :
    TransportSingleBondRotation equivalent singleBondRotation first second ↔
      singleBondRotation (MolecularConformation.reindex equivalent.symm first)
        (MolecularConformation.reindex equivalent.symm second) := by
  constructor
  · rintro ⟨firstSource, secondSource, firstImage, secondImage, rotation⟩
    rw [← firstImage, ← secondImage]
    simpa only [MolecularConformation.reindex_reindex] using rotation
  · intro rotation
    exact ⟨MolecularConformation.reindex equivalent.symm first,
      MolecularConformation.reindex equivalent.symm second,
      MolecularConformation.reindex_reindex_symm equivalent first,
      MolecularConformation.reindex_reindex_symm equivalent second,
      rotation⟩

/-- The unoriented direct-rotation step relation is transported and reflected exactly. -/
theorem directRotationStep_transport_iff (equivalent : V ≃ W)
    (singleBondRotation : MolecularConformation V → MolecularConformation V → Prop)
    (first second : MolecularConformation V) :
    DirectRotationStep (TransportSingleBondRotation equivalent singleBondRotation)
        (MolecularConformation.reindex equivalent first)
        (MolecularConformation.reindex equivalent second) ↔
      DirectRotationStep singleBondRotation first second := by
  unfold DirectRotationStep
  rw [transportSingleBondRotation_reindex_iff,
    transportSingleBondRotation_reindex_iff]

/-- Reflection of a transported interconversion path: every P-94.1 path in the transported
relation between arbitrary target conformations yields a source path between their inverse
images. -/
theorem interconvertibleBySingleBondRotations_transport_reflect (equivalent : V ≃ W)
    (singleBondRotation : MolecularConformation V → MolecularConformation V → Prop)
    (first second : MolecularConformation W)
    (path : InterconvertibleBySingleBondRotations
      (TransportSingleBondRotation equivalent singleBondRotation) first second) :
    InterconvertibleBySingleBondRotations singleBondRotation
      (MolecularConformation.reindex equivalent.symm first)
      (MolecularConformation.reindex equivalent.symm second) := by
  induction path with
  | refl state => exact .refl _
  | step rotation =>
      exact .step ((transportSingleBondRotation_preimage_iff equivalent
        singleBondRotation _ _).mp rotation)
  | symm _ inductionHypothesis => exact .symm inductionHypothesis
  | trans _ _ firstHypothesis secondHypothesis =>
      exact .trans firstHypothesis secondHypothesis

/-- The whole P-94.1 interconversion relation is preserved and reflected along the same atom
equivalence that transports states: a source path exists exactly when the reindexed endpoints
are connected by a path of transported steps.  Both directions are proved; the inverse transport
law is derived from the existing `MolecularConformation.reindex_reindex`, never assumed. -/
theorem interconvertibleBySingleBondRotations_transport_iff (equivalent : V ≃ W)
    (singleBondRotation : MolecularConformation V → MolecularConformation V → Prop)
    (first second : MolecularConformation V) :
    InterconvertibleBySingleBondRotations singleBondRotation first second ↔
      InterconvertibleBySingleBondRotations
        (TransportSingleBondRotation equivalent singleBondRotation)
        (MolecularConformation.reindex equivalent first)
        (MolecularConformation.reindex equivalent second) := by
  constructor
  · intro path
    induction path with
    | refl state => exact .refl _
    | step rotation => exact .step ⟨_, _, rfl, rfl, rotation⟩
    | symm _ inductionHypothesis => exact .symm inductionHypothesis
    | trans _ _ firstHypothesis secondHypothesis =>
        exact .trans firstHypothesis secondHypothesis
  · intro path
    have reflected := interconvertibleBySingleBondRotations_transport_reflect equivalent
      singleBondRotation
      (MolecularConformation.reindex equivalent first)
      (MolecularConformation.reindex equivalent second) path
    simpa [MolecularConformation.reindex_reindex] using reflected

/-- Interconversion of arbitrary target conformations is equivalent to interconversion of their
inverse images in the source relation. -/
theorem interconvertibleBySingleBondRotations_preimage_iff (equivalent : V ≃ W)
    (singleBondRotation : MolecularConformation V → MolecularConformation V → Prop)
    (first second : MolecularConformation W) :
    InterconvertibleBySingleBondRotations
        (TransportSingleBondRotation equivalent singleBondRotation) first second ↔
      InterconvertibleBySingleBondRotations singleBondRotation
        (MolecularConformation.reindex equivalent.symm first)
        (MolecularConformation.reindex equivalent.symm second) := by
  constructor
  · exact interconvertibleBySingleBondRotations_transport_reflect equivalent
      singleBondRotation first second
  · intro path
    have transported :=
      (interconvertibleBySingleBondRotations_transport_iff equivalent singleBondRotation
        (MolecularConformation.reindex equivalent.symm first)
        (MolecularConformation.reindex equivalent.symm second)).mp path
    simpa [MolecularConformation.reindex_reindex_symm] using transported

/-! ### Ordered rotation paths

The P-94 path carrier `DirectedRotationPath` retains the ordered sequence of states, not only its
endpoints.  It is transported state by state under the same atom equivalence. -/

/-- Transport an ordered direct-rotation path state by state. -/
theorem directedRotationPath_map_reindex (equivalent : V ≃ W)
    (singleBondRotation : MolecularConformation V → MolecularConformation V → Prop)
    {states : List (MolecularConformation V)}
    (path : DirectedRotationPath singleBondRotation states) :
    DirectedRotationPath (TransportSingleBondRotation equivalent singleBondRotation)
      (states.map (MolecularConformation.reindex equivalent)) := by
  induction path with
  | singleton state => exact .singleton _
  | cons direct tail inductionHypothesis =>
      refine .cons ?_ inductionHypothesis
      rcases direct with forward | reverse
      · exact Or.inl ⟨_, _, rfl, rfl, forward⟩
      · exact Or.inr ⟨_, _, rfl, rfl, reverse⟩

/-- Replacing a relation pointwise by an equivalent relation preserves ordered paths. -/
theorem directedRotationPath_congr {State : Type*}
    {first second : State → State → Prop}
    (relations : ∀ left right, first left right ↔ second left right)
    {states : List State} (path : DirectedRotationPath first states) :
    DirectedRotationPath second states := by
  induction path with
  | singleton state => exact .singleton state
  | cons direct tail inductionHypothesis =>
      refine .cons ?_ inductionHypothesis
      rcases direct with forward | reverse
      · exact Or.inl ((relations _ _).mp forward)
      · exact Or.inr ((relations _ _).mp reverse)

/-- Reflection of an ordered path whose state list is the reindexed image of a source list. -/
theorem directedRotationPath_reindex_reflect (equivalent : V ≃ W)
    (singleBondRotation : MolecularConformation V → MolecularConformation V → Prop)
    {states : List (MolecularConformation V)}
    (path : DirectedRotationPath
      (TransportSingleBondRotation equivalent singleBondRotation)
      (states.map (MolecularConformation.reindex equivalent))) :
    DirectedRotationPath singleBondRotation states := by
  have mappedBack := directedRotationPath_map_reindex equivalent.symm
    (TransportSingleBondRotation equivalent singleBondRotation) path
  have stateList :
      (states.map (MolecularConformation.reindex equivalent)).map
        (MolecularConformation.reindex equivalent.symm) = states := by
    rw [List.map_map]
    have composite :
        (MolecularConformation.reindex equivalent.symm ∘
          MolecularConformation.reindex equivalent) = id := by
      funext conformation
      exact MolecularConformation.reindex_reindex equivalent conformation
    rw [composite, List.map_id]
  have relationEq : ∀ left right : MolecularConformation V,
      TransportSingleBondRotation equivalent.symm
          (TransportSingleBondRotation equivalent singleBondRotation) left right ↔
        singleBondRotation left right := by
    intro left right
    rw [transportSingleBondRotation_preimage_iff]
    simp only [Equiv.symm_symm]
    exact transportSingleBondRotation_reindex_iff equivalent singleBondRotation left right
  rw [stateList] at mappedBack
  exact directedRotationPath_congr relationEq mappedBack

/-! ### Endpoints of transported trajectories

The same equivalence transports the trajectory and the rotation relation.  The following two
endpoint statements make that consistency explicit. -/

/-- The P-94.1 relation between trajectory initial endpoints is transported, using the very same
atom equivalence that reindexes the trajectories. -/
theorem interconvertibleBySingleBondRotations_initial_reindex_iff (equivalent : V ≃ W)
    (singleBondRotation : MolecularConformation V → MolecularConformation V → Prop)
    (first second : ConformationTrajectory V) :
    InterconvertibleBySingleBondRotations
        (TransportSingleBondRotation equivalent singleBondRotation)
        (ConformationTrajectory.reindex equivalent first).initial
        (ConformationTrajectory.reindex equivalent second).initial ↔
      InterconvertibleBySingleBondRotations singleBondRotation
        first.initial second.initial := by
  rw [ConformationTrajectory.initial_reindex, ConformationTrajectory.initial_reindex]
  exact (interconvertibleBySingleBondRotations_transport_iff equivalent singleBondRotation
    first.initial second.initial).symm

/-- The same endpoint statement for the final endpoints. -/
theorem interconvertibleBySingleBondRotations_final_reindex_iff (equivalent : V ≃ W)
    (singleBondRotation : MolecularConformation V → MolecularConformation V → Prop)
    (first second : ConformationTrajectory V) :
    InterconvertibleBySingleBondRotations
        (TransportSingleBondRotation equivalent singleBondRotation)
        (ConformationTrajectory.reindex equivalent first).final
        (ConformationTrajectory.reindex equivalent second).final ↔
      InterconvertibleBySingleBondRotations singleBondRotation
        first.final second.final := by
  rw [ConformationTrajectory.final_reindex, ConformationTrajectory.final_reindex]
  exact (interconvertibleBySingleBondRotations_transport_iff equivalent singleBondRotation
    first.final second.final).symm

end BlueBookP94

/-! ## Why the transition relation is genuine information

The following witness lives on genuine real molecular conformations (`Fin 1` atoms with real
coordinates).  Two different supplied direct-rotation relations have exactly the same set of
conformations occurring as rotation endpoints, yet different P-94.1 interconversion relations.
Thus the static endpoint set does not determine the transition relation; the relation data must be
carried through the transport explicitly, as done above. -/

namespace SingleBondRotationInformationWitness

/-- The set of conformations occurring as the source or target of a supplied direct-rotation
relation.  This is the static "possible state" information of the relation. -/
def RotationEndpointSet {V : Type*}
    (singleBondRotation : MolecularConformation V → MolecularConformation V → Prop) :
    Set (MolecularConformation V) :=
  {conformation |
    (∃ other, singleBondRotation conformation other) ∨
      ∃ other, singleBondRotation other conformation}

/-! ### Four concrete real conformations -/

/-- The origin of real three-space. -/
def pointA : Real3 :=
  WithLp.toLp 2 (fun index : Fin 3 => ![(0 : ℝ), 0, 0] index)

/-- The point `(1, 0, 0)`. -/
def pointB : Real3 :=
  WithLp.toLp 2 (fun index : Fin 3 => ![(1 : ℝ), 0, 0] index)

/-- The point `(0, 1, 0)`. -/
def pointC : Real3 :=
  WithLp.toLp 2 (fun index : Fin 3 => ![(0 : ℝ), 1, 0] index)

/-- The point `(0, 0, 1)`. -/
def pointD : Real3 :=
  WithLp.toLp 2 (fun index : Fin 3 => ![(0 : ℝ), 0, 1] index)

theorem pointA_ne_pointB : pointA ≠ pointB := by
  intro equal
  have coordinate := congrArg (fun point : Real3 => point 0) equal
  simp [pointA, pointB] at coordinate

theorem pointA_ne_pointC : pointA ≠ pointC := by
  intro equal
  have coordinate := congrArg (fun point : Real3 => point 1) equal
  simp [pointA, pointC] at coordinate

theorem pointA_ne_pointD : pointA ≠ pointD := by
  intro equal
  have coordinate := congrArg (fun point : Real3 => point 2) equal
  simp [pointA, pointD] at coordinate

theorem pointB_ne_pointC : pointB ≠ pointC := by
  intro equal
  have coordinate := congrArg (fun point : Real3 => point 0) equal
  simp [pointB, pointC] at coordinate

theorem pointB_ne_pointD : pointB ≠ pointD := by
  intro equal
  have coordinate := congrArg (fun point : Real3 => point 0) equal
  simp [pointB, pointD] at coordinate

theorem pointC_ne_pointD : pointC ≠ pointD := by
  intro equal
  have coordinate := congrArg (fun point : Real3 => point 1) equal
  simp [pointC, pointD] at coordinate

/-- The first concrete real conformation: one atom at the origin. -/
def stateA : MolecularConformation (Fin 1) := fun _ => pointA

/-- The second concrete real conformation: one atom at `(1, 0, 0)`. -/
def stateB : MolecularConformation (Fin 1) := fun _ => pointB

/-- The third concrete real conformation: one atom at `(0, 1, 0)`. -/
def stateC : MolecularConformation (Fin 1) := fun _ => pointC

/-- The fourth concrete real conformation: one atom at `(0, 0, 1)`. -/
def stateD : MolecularConformation (Fin 1) := fun _ => pointD

theorem stateA_ne_stateB : stateA ≠ stateB :=
  fun equal => pointA_ne_pointB (congrFun equal 0)

theorem stateA_ne_stateC : stateA ≠ stateC :=
  fun equal => pointA_ne_pointC (congrFun equal 0)

theorem stateA_ne_stateD : stateA ≠ stateD :=
  fun equal => pointA_ne_pointD (congrFun equal 0)

theorem stateB_ne_stateC : stateB ≠ stateC :=
  fun equal => pointB_ne_pointC (congrFun equal 0)

theorem stateB_ne_stateD : stateB ≠ stateD :=
  fun equal => pointB_ne_pointD (congrFun equal 0)

theorem stateC_ne_stateD : stateC ≠ stateD :=
  fun equal => pointC_ne_pointD (congrFun equal 0)

theorem stateB_ne_stateA : stateB ≠ stateA := stateA_ne_stateB.symm

theorem stateC_ne_stateA : stateC ≠ stateA := stateA_ne_stateC.symm

theorem stateD_ne_stateA : stateD ≠ stateA := stateA_ne_stateD.symm

theorem stateC_ne_stateB : stateC ≠ stateB := stateB_ne_stateC.symm

theorem stateD_ne_stateB : stateD ≠ stateB := stateB_ne_stateD.symm

theorem stateD_ne_stateC : stateD ≠ stateC := stateC_ne_stateD.symm

/-! ### Two different relation data values with the same endpoint set -/

/-- The first supplied relation: the pair `stateA → stateB` together with `stateC → stateD`. -/
def matchingOne : MolecularConformation (Fin 1) → MolecularConformation (Fin 1) → Prop :=
  fun first second =>
    (first = stateA ∧ second = stateB) ∨ (first = stateC ∧ second = stateD)

/-- The second supplied relation: the pair `stateA → stateC` together with `stateB → stateD`. -/
def matchingTwo : MolecularConformation (Fin 1) → MolecularConformation (Fin 1) → Prop :=
  fun first second =>
    (first = stateA ∧ second = stateC) ∨ (first = stateB ∧ second = stateD)

/-- Both relations have exactly the same endpoint set, namely the four concrete conformations. -/
theorem same_rotationEndpointSet :
    RotationEndpointSet matchingOne = RotationEndpointSet matchingTwo := by
  have one :
      RotationEndpointSet matchingOne =
        ({stateA, stateB, stateC, stateD} : Set (MolecularConformation (Fin 1))) := by
    ext conformation
    constructor
    · rintro (⟨other, edge⟩ | ⟨other, edge⟩)
      · rcases edge with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
      · rcases edge with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
    · intro member
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact Or.inl ⟨stateB, Or.inl ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨stateA, Or.inl ⟨rfl, rfl⟩⟩
      · exact Or.inl ⟨stateD, Or.inr ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨stateC, Or.inr ⟨rfl, rfl⟩⟩
  have two :
      RotationEndpointSet matchingTwo =
        ({stateA, stateB, stateC, stateD} : Set (MolecularConformation (Fin 1))) := by
    ext conformation
    constructor
    · rintro (⟨other, edge⟩ | ⟨other, edge⟩)
      · rcases edge with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp
      · rcases edge with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> simp
    · intro member
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
      rcases member with rfl | rfl | rfl | rfl
      · exact Or.inl ⟨stateC, Or.inl ⟨rfl, rfl⟩⟩
      · exact Or.inl ⟨stateD, Or.inr ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨stateA, Or.inl ⟨rfl, rfl⟩⟩
      · exact Or.inr ⟨stateB, Or.inr ⟨rfl, rfl⟩⟩
  rw [one, two]

/-- The relation data really differ. -/
theorem matchingOne_ne_matchingTwo : matchingOne ≠ matchingTwo := by
  intro equal
  have atEdge : matchingOne stateA stateB := Or.inl ⟨rfl, rfl⟩
  rw [equal] at atEdge
  simp [matchingTwo, stateA_ne_stateB, stateB_ne_stateC] at atEdge

/-- The first relation connects `stateA` and `stateB` in one P-94.1 step. -/
theorem matchingOne_interconvertible :
    InterconvertibleBySingleBondRotations matchingOne stateA stateB :=
  .step (Or.inl ⟨rfl, rfl⟩)

/-- A Boolean label that is `true` exactly on the component `{stateA, stateC}` of
`matchingTwo`. -/
def inFirstComponent (conformation : MolecularConformation (Fin 1)) : Bool :=
  if conformation = stateA ∨ conformation = stateC then true else false

theorem inFirstComponent_stateA : inFirstComponent stateA = true := by
  simp [inFirstComponent]

theorem inFirstComponent_stateB : inFirstComponent stateB = false := by
  have notFirst : ¬(stateB = stateA ∨ stateB = stateC) := by
    rintro (same | same)
    · exact stateB_ne_stateA same
    · exact stateB_ne_stateC same
  simp [inFirstComponent, notFirst]

/-- Every `matchingTwo` edge preserves the component label. -/
theorem inFirstComponent_eq_of_matchingTwo_step
    {first second : MolecularConformation (Fin 1)} (edge : matchingTwo first second) :
    inFirstComponent first = inFirstComponent second := by
  rcases edge with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp [inFirstComponent]
  · have notFirstB : ¬(stateB = stateA ∨ stateB = stateC) := by
      rintro (same | same)
      · exact stateB_ne_stateA same
      · exact stateB_ne_stateC same
    have notFirstD : ¬(stateD = stateA ∨ stateD = stateC) := by
      rintro (same | same)
      · exact stateD_ne_stateA same
      · exact stateD_ne_stateC same
    simp [inFirstComponent, notFirstB, notFirstD]

/-- `matchingTwo` interconversion preserves the component label. -/
theorem inFirstComponent_eq_of_interconvertible
    {first second : MolecularConformation (Fin 1)}
    (path : InterconvertibleBySingleBondRotations matchingTwo first second) :
    inFirstComponent first = inFirstComponent second := by
  induction path with
  | refl state => rfl
  | step edge => exact inFirstComponent_eq_of_matchingTwo_step edge
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ firstHypothesis secondHypothesis =>
      exact firstHypothesis.trans secondHypothesis

/-- The second relation does not connect `stateA` and `stateB`. -/
theorem matchingTwo_not_interconvertible :
    ¬ InterconvertibleBySingleBondRotations matchingTwo stateA stateB := by
  intro path
  have labels := inFirstComponent_eq_of_interconvertible path
  rw [inFirstComponent_stateA, inFirstComponent_stateB] at labels
  simp at labels

/-- Two materially different supplied rotation relations on the same real molecular
conformations have the same static endpoint set but different P-94.1 interconversion relations.
This is why the transition relation itself, not merely its endpoint set, must be transported. -/
theorem same_endpointSet_different_interconversion :
    RotationEndpointSet matchingOne = RotationEndpointSet matchingTwo ∧
      matchingOne ≠ matchingTwo ∧
        InterconvertibleBySingleBondRotations matchingOne stateA stateB ∧
          ¬ InterconvertibleBySingleBondRotations matchingTwo stateA stateB :=
  ⟨same_rotationEndpointSet, matchingOne_ne_matchingTwo,
    matchingOne_interconvertible, matchingTwo_not_interconvertible⟩

end SingleBondRotationInformationWitness

end

end OneCenter
end TetraStereo

/-! ## Kernel receipts for the decisive closure and endpoint results -/

assert_kernel_only TetraStereo.OneCenter.ConformationTrajectory.reindex_reindex
assert_kernel_only TetraStereo.OneCenter.ConformationTrajectory.reindex_reindex_symm
assert_kernel_only TetraStereo.OneCenter.ConformationTrajectory.reindex_trajectory_reindex
assert_kernel_only TetraStereo.OneCenter.ConformationTrajectory.reindex_trajectory_reindex_symm
assert_kernel_only TetraStereo.OneCenter.ConformationTrajectory.snapshotSet_reindex
assert_kernel_only TetraStereo.OneCenter.SnapshotReparameterizationWitness.distinct_trajectories_same_snapshotSet
assert_kernel_only TetraStereo.OneCenter.TrajectoryEnsemble.image_reindex_image
assert_kernel_only TetraStereo.OneCenter.TrajectoryEnsemble.reindex_reindex
assert_kernel_only TetraStereo.OneCenter.TrajectoryEnsemble.reindex_reindex_symm
assert_kernel_only TetraStereo.OneCenter.AmbientMotion.toConformationTrajectory_reindex
assert_kernel_only TetraStereo.OneCenter.AmbientMotion.allowedTrajectories_reindex
assert_kernel_only TetraStereo.OneCenter.BlueBookP94.transportSingleBondRotation_reindex_iff
assert_kernel_only TetraStereo.OneCenter.BlueBookP94.transportSingleBondRotation_preimage_iff
assert_kernel_only TetraStereo.OneCenter.BlueBookP94.directRotationStep_transport_iff
assert_kernel_only TetraStereo.OneCenter.BlueBookP94.interconvertibleBySingleBondRotations_transport_iff
assert_kernel_only TetraStereo.OneCenter.BlueBookP94.interconvertibleBySingleBondRotations_preimage_iff
assert_kernel_only TetraStereo.OneCenter.BlueBookP94.directedRotationPath_map_reindex
assert_kernel_only TetraStereo.OneCenter.BlueBookP94.directedRotationPath_reindex_reflect
assert_kernel_only TetraStereo.OneCenter.BlueBookP94.interconvertibleBySingleBondRotations_initial_reindex_iff
assert_kernel_only TetraStereo.OneCenter.BlueBookP94.interconvertibleBySingleBondRotations_final_reindex_iff
assert_kernel_only TetraStereo.OneCenter.SingleBondRotationInformationWitness.same_endpointSet_different_interconversion

#print axioms TetraStereo.OneCenter.ConformationTrajectory.reindex_reindex
#print axioms TetraStereo.OneCenter.ConformationTrajectory.reindex_reindex_symm
#print axioms TetraStereo.OneCenter.TrajectoryEnsemble.image_reindex_image
#print axioms TetraStereo.OneCenter.AmbientMotion.toConformationTrajectory_reindex
#print axioms TetraStereo.OneCenter.AmbientMotion.allowedTrajectories_reindex
#print axioms TetraStereo.OneCenter.ConformationTrajectory.constant_trajectory_noninjective
#print axioms TetraStereo.OneCenter.SnapshotReparameterizationWitness.distinct_trajectories_same_snapshotSet
#print axioms TetraStereo.OneCenter.BlueBookP94.transportSingleBondRotation_reindex_iff
#print axioms TetraStereo.OneCenter.BlueBookP94.interconvertibleBySingleBondRotations_transport_iff
#print axioms TetraStereo.OneCenter.BlueBookP94.interconvertibleBySingleBondRotations_preimage_iff
#print axioms TetraStereo.OneCenter.BlueBookP94.interconvertibleBySingleBondRotations_initial_reindex_iff
#print axioms TetraStereo.OneCenter.SingleBondRotationInformationWitness.same_endpointSet_different_interconversion
