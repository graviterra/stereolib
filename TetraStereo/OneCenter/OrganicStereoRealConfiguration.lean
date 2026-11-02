import TetraStereo.OneCenter.AuthoritativeChemicalInput
import TetraStereo.OneCenter.CIPFrontier

set_option autoImplicit false

open scoped Classical

namespace TetraStereo
namespace OneCenter

/-!
# Source-indexed real geometric representation for certified chemical input

`AuthoritativeChemicalInput.SpatialConfiguration` records exact rational positions for one
conformer.  `CIPFrontier` already provides the representation-independent conformation types
`MolecularConformation V = V → EuclideanSpace ℝ (Fin 3)` and
`MolecularConformation.Ensemble V` (an arbitrary set of allowed conformations).  This module
connects the two without weakening either:

* a certified source is indexed by its own dependent atom type `Fin atomCount`, so a conformer has
  exactly one real point per source atom;
* every real conformation over that atom type is accepted; there is no rationality, boundedness or
  labelling restriction;
* exact rational `SpatialConfiguration` data is embedded constructively by casting each coordinate,
  with pointwise coordinate theorems, injectivity, and a partial rational view for points whose
  coordinates are rational.  No surjectivity `ℝ → ℚ` is asserted;
* arbitrary atom reindexing transports conformations and conformational ensembles in both
  directions, so an independent finite atom index related by a bijection can be encoded;
* finite collections of conformers can be embedded into an arbitrary allowed set.  Empty and
  unknown-scope collections are represented explicitly as empty allowed sets rather than as a
  claim about a physical mixture.

Substrate molecule and electronic labels are never modified: the representation is parameterized
by the certified source and carries no additional opaque data field.  This module makes no claim
about perception, CIP normative fidelity, chemical admissibility or taxonomy completeness.
-/

/-! ## Exact rational points inside real Euclidean space -/

namespace CartesianPoint3

/-- Exact embedding of a rational point into the existing real Euclidean 3-space.  This is a
constructive coordinate cast, not an identification of `ℝ` with `ℚ`. -/
noncomputable def toEuclideanPoint (point : CartesianPoint3) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.toLp 2 ![(point.x : ℝ), (point.y : ℝ), (point.z : ℝ)]

/-- The first real coordinate is exactly the cast of the first rational coordinate. -/
@[simp] theorem toEuclideanPoint_apply_zero (point : CartesianPoint3) :
    point.toEuclideanPoint 0 = (point.x : ℝ) := by
  simp [toEuclideanPoint]

/-- The second real coordinate is exactly the cast of the second rational coordinate. -/
@[simp] theorem toEuclideanPoint_apply_one (point : CartesianPoint3) :
    point.toEuclideanPoint 1 = (point.y : ℝ) := by
  simp [toEuclideanPoint]

/-- The third real coordinate is exactly the cast of the third rational coordinate. -/
@[simp] theorem toEuclideanPoint_apply_two (point : CartesianPoint3) :
    point.toEuclideanPoint 2 = (point.z : ℝ) := by
  simp [toEuclideanPoint]

/-- The rational embedding introduces no identifications: equal real points have equal rational
coordinates. -/
theorem toEuclideanPoint_injective : Function.Injective toEuclideanPoint := by
  intro first second equal
  have xCoords : first.x = second.x := by
    have := congrArg (fun point : EuclideanSpace ℝ (Fin 3) => point 0) equal
    simpa using this
  have yCoords : first.y = second.y := by
    have := congrArg (fun point : EuclideanSpace ℝ (Fin 3) => point 1) equal
    simpa using this
  have zCoords : first.z = second.z := by
    have := congrArg (fun point : EuclideanSpace ℝ (Fin 3) => point 2) equal
    simpa using this
  cases first with
  | mk x y z =>
      cases second with
      | mk x' y' z' =>
          simp_all

end CartesianPoint3

namespace RealPoint

/-- A real point is rational when it is the exact image of a rational point.  This is a property
of a point, not a decision procedure, and it is not claimed for all real points.  The predicate
lives outside the `CartesianPoint3` namespace because its argument is a real point. -/
def IsRational (point : EuclideanSpace ℝ (Fin 3)) : Prop :=
  ∃ rational : CartesianPoint3, rational.toEuclideanPoint = point

/-- Partial rational view of a real point.  It returns `none` exactly when some coordinate is not
the cast of a rational number; the module never asserts that such a coordinate does not exist. -/
noncomputable def rationalView? (point : EuclideanSpace ℝ (Fin 3)) : Option CartesianPoint3 :=
  if h : IsRational point then some (Classical.choose h) else none

/-- The rational view recognizes exactly the rational points and returns the unique rational
preimage. -/
@[simp] theorem rationalView?_eq_some_iff (point : EuclideanSpace ℝ (Fin 3))
    (rational : CartesianPoint3) :
    rationalView? point = some rational ↔ rational.toEuclideanPoint = point := by
  constructor
  · intro observed
    by_cases rational' : IsRational point
    · rw [rationalView?, dif_pos rational'] at observed
      injection observed with equality
      rw [← equality]
      exact Classical.choose_spec rational'
    · rw [rationalView?, dif_neg rational'] at observed
      exact absurd observed (by simp)
  · intro equality
    have rational' : IsRational point := ⟨rational, equality⟩
    rw [rationalView?, dif_pos rational']
    congr 1
    exact CartesianPoint3.toEuclideanPoint_injective
      ((Classical.choose_spec rational').trans equality.symm)

/-- Roundtrip: the rational view of an embedded rational point is that point. -/
@[simp] theorem rationalView?_toEuclideanPoint (rational : CartesianPoint3) :
    rationalView? rational.toEuclideanPoint = some rational :=
  (rationalView?_eq_some_iff _ _).mpr rfl

/-- The rational view is available exactly on rational points. -/
@[simp] theorem rationalView?_isSome_iff (point : EuclideanSpace ℝ (Fin 3)) :
    (rationalView? point).isSome = true ↔ IsRational point := by
  by_cases rational : IsRational point
  · rw [rationalView?, dif_pos rational]
    simp [rational]
  · rw [rationalView?, dif_neg rational]
    simp [rational]

end RealPoint

/-! ## The dependent atom index of a certified source -/

/-- The finite index type of a certified source: exactly one index per source atom. -/
abbrev SourceAtomIndex (source : CertifiedAuthoritativeChemicalInput) : Type :=
  Fin source.input.molecule.atomCount

/-- The source atom found at a dependent source index.  No atom is invented or dropped. -/
def sourceAtom (source : CertifiedAuthoritativeChemicalInput)
    (index : SourceAtomIndex source) : SemanticAtom :=
  source.input.molecule.atoms.get ⟨index.val, index.isLt⟩

/-- Every source index names a source atom. -/
@[simp] theorem sourceAtom_mem (source : CertifiedAuthoritativeChemicalInput)
    (index : SourceAtomIndex source) :
    sourceAtom source index ∈ source.input.molecule.atoms :=
  List.get_mem _ _

/-- Every source atom is reached by some dependent source index.  This is the no-atom-loss
statement for the source-indexed representation. -/
theorem sourceAtom_surjective_on_mem (source : CertifiedAuthoritativeChemicalInput)
    {atom : SemanticAtom} (member : atom ∈ source.input.molecule.atoms) :
    ∃ index : SourceAtomIndex source, sourceAtom source index = atom := by
  obtain ⟨index, observed⟩ := List.get_of_mem member
  refine ⟨⟨index.val, index.isLt⟩, ?_⟩
  simpa [sourceAtom] using observed

/-- The dependent source index has exactly as many elements as the source atom list. -/
@[simp] theorem sourceAtomIndex_card (source : CertifiedAuthoritativeChemicalInput) :
    Fintype.card (SourceAtomIndex source) = source.input.molecule.atoms.length := by
  simp [SourceAtomIndex, SemanticMolecule.atomCount]

/-- One real conformation over the source atom index: exactly one point per source atom. -/
abbrev SourceConformation (source : CertifiedAuthoritativeChemicalInput) : Type :=
  MolecularConformation (SourceAtomIndex source)

/-- An arbitrary allowed set of source conformations, reusing the existing `Ensemble` type. -/
abbrev SourceEnsemble (source : CertifiedAuthoritativeChemicalInput) : Type :=
  MolecularConformation.Ensemble (SourceAtomIndex source)

/-- A source-indexed real geometry.  The only field is the conformation; the source molecule and
its electronic labels are the fixed type parameter and are never rebuilt or relabelled. -/
structure RealSourceGeometry (source : CertifiedAuthoritativeChemicalInput) where
  conformation : SourceConformation source

namespace RealSourceGeometry

variable {source : CertifiedAuthoritativeChemicalInput}

/-- The source projection of a source-indexed real geometry. -/
def sourceOf (_representation : RealSourceGeometry source) : CertifiedAuthoritativeChemicalInput :=
  source

/-- The projection returns exactly the certified source that indexes the representation. -/
@[simp] theorem sourceOf_eq (representation : RealSourceGeometry source) :
    representation.sourceOf = source := rfl

/-- The representation does not modify the source input, including all electronic labels. -/
@[simp] theorem sourceOf_input_eq (representation : RealSourceGeometry source) :
    representation.sourceOf.input = source.input := rfl

/-- The atom count is unchanged by the geometric representation. -/
@[simp] theorem sourceOf_atomCount_eq (representation : RealSourceGeometry source) :
    representation.sourceOf.input.molecule.atomCount = source.input.molecule.atomCount := rfl

/-- Every source atom remains present at a dependent source index in the represented source. -/
theorem source_atom_indexed (representation : RealSourceGeometry source) {atom : SemanticAtom}
    (member : atom ∈ source.input.molecule.atoms) :
    ∃ index : SourceAtomIndex source, sourceAtom representation.sourceOf index = atom :=
  sourceAtom_surjective_on_mem source member

/-- Source-indexed geometries are determined by their conformation; there is no hidden label or
auxiliary data. -/
@[ext] theorem ext {first second : RealSourceGeometry source}
    (equal : first.conformation = second.conformation) : first = second := by
  cases first with
  | mk firstConformation =>
      cases second with
      | mk secondConformation =>
          simp_all

/-- Attach an arbitrary real conformation to a certified source.  This is the bridge from a pure
source (in particular one with `spatial? = none`) to explicitly provided real geometry; it never
inspects or requires the optional spatial evidence channel. -/
def ofConformation (source : CertifiedAuthoritativeChemicalInput)
    (conformation : SourceConformation source) : RealSourceGeometry source :=
  ⟨conformation⟩

@[simp] theorem ofConformation_conformation (source : CertifiedAuthoritativeChemicalInput)
    (conformation : SourceConformation source) :
    (ofConformation source conformation).conformation = conformation := rfl

/-- Attaching conformations is injective. -/
theorem ofConformation_injective (source : CertifiedAuthoritativeChemicalInput) :
    Function.Injective (ofConformation source) := by
  intro first second equal
  exact congrArg RealSourceGeometry.conformation equal

/-- Every real conformation over the source atom index is representable at that source.  No
rationality or other geometric restriction is imposed. -/
theorem exists_ofConformation (source : CertifiedAuthoritativeChemicalInput)
    (conformation : SourceConformation source) :
    ∃ representation : RealSourceGeometry source,
      representation.conformation = conformation :=
  ⟨ofConformation source conformation, rfl⟩

/-- Every certified source, including a source with no atoms and no interactions, has at least
one real source-indexed geometry.  This witness uses an explicitly provided conformation; it is
not used to fabricate geometry for a source whose optional spatial channel is absent. -/
theorem exists_zero (source : CertifiedAuthoritativeChemicalInput) :
    ∃ representation : RealSourceGeometry source,
      representation.conformation = fun _ => (0 : EuclideanSpace ℝ (Fin 3)) :=
  ⟨ofConformation source (fun _ => 0), rfl⟩

/-- An empty source atom index admits exactly one real conformation. -/
theorem subsingleton_of_atomCount_eq_zero (source : CertifiedAuthoritativeChemicalInput)
    (emptyCount : source.input.molecule.atomCount = 0) :
    Subsingleton (SourceConformation source) := by
  constructor
  intro first second
  funext index
  have bound : index.val < 0 := by
    simpa [emptyCount] using index.isLt
  exact absurd bound (Nat.not_lt_zero index.val)

/-- Two source-indexed conformations are equal exactly when they agree at every source atom. -/
@[simp] theorem conformation_ext_iff {first second : SourceConformation source} :
    first = second ↔ ∀ index : SourceAtomIndex source, first index = second index :=
  ⟨fun equal _ => congrFun equal _, fun equal => funext equal⟩

end RealSourceGeometry

/-! ## Exact rational geometry as a real source-indexed geometry -/

/-- The rational point at a fixed external atom count.  The proof of the actual position-list
length is carried explicitly, so no coordinate is silently duplicated or dropped. -/
def SpatialConfiguration.pointAt (spatial : SpatialConfiguration) (n : ℕ)
    (lengthExact : spatial.positions.length = n) (index : Fin n) : CartesianPoint3 :=
  spatial.positions.get ⟨index.val, by
    rw [lengthExact]
    exact index.isLt⟩

/-- Exact rational positions for one conformation, sectioned at an explicitly supplied atom
count.  Every coordinate is cast from `ℚ` to `ℝ` without rounding. -/
noncomputable def SpatialConfiguration.toConformationAt (spatial : SpatialConfiguration)
    (n : ℕ) (lengthExact : spatial.positions.length = n) : MolecularConformation (Fin n) :=
  fun index => (spatial.pointAt n lengthExact index).toEuclideanPoint

/-- Exact rational positions for one conformation, sectioned at their actual list length. -/
noncomputable def SpatialConfiguration.toConformation (spatial : SpatialConfiguration) :
    MolecularConformation (Fin spatial.positions.length) :=
  fun index => (spatial.positions.get index).toEuclideanPoint

@[simp] theorem SpatialConfiguration.toConformation_apply (spatial : SpatialConfiguration)
    (index : Fin spatial.positions.length) :
    spatial.toConformation index = (spatial.positions.get index).toEuclideanPoint := rfl

@[simp] theorem SpatialConfiguration.toConformationAt_apply (spatial : SpatialConfiguration)
    (n : ℕ) (lengthExact : spatial.positions.length = n) (index : Fin n) :
    spatial.toConformationAt n lengthExact index =
      (spatial.pointAt n lengthExact index).toEuclideanPoint := rfl

/-- Pointwise exact cast of the first coordinate. -/
@[simp] theorem SpatialConfiguration.toConformationAt_apply_zero (spatial : SpatialConfiguration)
    (n : ℕ) (lengthExact : spatial.positions.length = n) (index : Fin n) :
    (spatial.toConformationAt n lengthExact index) 0 =
      ((spatial.pointAt n lengthExact index).x : ℝ) := by
  simp [SpatialConfiguration.toConformationAt]

/-- Pointwise exact cast of the second coordinate. -/
@[simp] theorem SpatialConfiguration.toConformationAt_apply_one (spatial : SpatialConfiguration)
    (n : ℕ) (lengthExact : spatial.positions.length = n) (index : Fin n) :
    (spatial.toConformationAt n lengthExact index) 1 =
      ((spatial.pointAt n lengthExact index).y : ℝ) := by
  simp [SpatialConfiguration.toConformationAt]

/-- Pointwise exact cast of the third coordinate. -/
@[simp] theorem SpatialConfiguration.toConformationAt_apply_two (spatial : SpatialConfiguration)
    (n : ℕ) (lengthExact : spatial.positions.length = n) (index : Fin n) :
    (spatial.toConformationAt n lengthExact index) 2 =
      ((spatial.pointAt n lengthExact index).z : ℝ) := by
  simp [SpatialConfiguration.toConformationAt]

/-- Roundtrip through the rational view: the real embedding of exact rational geometry is
recognized as rational and recovers the original point at every index. -/
@[simp] theorem SpatialConfiguration.rationalView?_toConformationAt
    (spatial : SpatialConfiguration) (n : ℕ) (lengthExact : spatial.positions.length = n)
    (index : Fin n) :
    RealPoint.rationalView? (spatial.toConformationAt n lengthExact index) =
      some (spatial.pointAt n lengthExact index) := by
  simp [SpatialConfiguration.toConformationAt]

/-- The rational embedding is injective at a fixed atom count: distinct exact geometries have
distinct real conformations. -/
theorem SpatialConfiguration.toConformationAt_injective
    {first second : SpatialConfiguration} {n : ℕ}
    (firstLength : first.positions.length = n) (secondLength : second.positions.length = n)
    (equal : first.toConformationAt n firstLength = second.toConformationAt n secondLength) :
    first = second := by
  cases first with
  | mk firstPositions =>
      cases second with
      | mk secondPositions =>
          have listEqual : firstPositions = secondPositions := by
            apply List.ext_get (firstLength.trans secondLength.symm)
            intro index firstBound secondBound
            let firstIndex : Fin firstPositions.length := ⟨index, firstBound⟩
            let secondIndex : Fin secondPositions.length := ⟨index, secondBound⟩
            let commonIndex : Fin n := ⟨index, firstLength ▸ firstBound⟩
            have step := congrFun equal commonIndex
            simp only [SpatialConfiguration.toConformationAt,
              SpatialConfiguration.pointAt] at step
            have firstCast :
                (⟨index, by rw [firstLength]; exact commonIndex.isLt⟩ :
                  Fin firstPositions.length) = firstIndex :=
              Fin.ext rfl
            have secondCast :
                (⟨index, by rw [secondLength]; exact commonIndex.isLt⟩ :
                  Fin secondPositions.length) = secondIndex :=
              Fin.ext rfl
            rw [firstCast, secondCast] at step
            exact CartesianPoint3.toEuclideanPoint_injective step
          rw [listEqual]

/-- Conversely, any real conformation all of whose points are rational is obtained from an exact
rational `SpatialConfiguration` of the same actual length.  This is a roundtrip only on the
rational locus; it is not a claim that every real conformation is rational. -/
theorem SpatialConfiguration.exists_toConformationAt_of_rational {n : ℕ}
    (conformation : MolecularConformation (Fin n))
    (rational : ∀ index : Fin n, RealPoint.IsRational (conformation index)) :
    ∃ spatial : SpatialConfiguration, ∃ lengthExact : spatial.positions.length = n,
      spatial.toConformationAt n lengthExact = conformation := by
  let positions : List CartesianPoint3 :=
    List.ofFn fun index : Fin n => Classical.choose (rational index)
  have lengthExact : positions.length = n := by
    simp [positions]
  refine ⟨⟨positions⟩, lengthExact, ?_⟩
  funext index
  simp only [SpatialConfiguration.toConformationAt, SpatialConfiguration.pointAt]
  have getEqual :
      positions.get ⟨index.val, by rw [lengthExact]; exact index.isLt⟩ =
        Classical.choose (rational index) := by
    simp [positions, List.get_eq_getElem]
  rw [getEqual]
  exact Classical.choose_spec (rational index)

/-- Attach an exact rational spatial configuration to a certified source.  The proof obligation is
only the actual length equality `positions.length = atomCount`; the source's optional spatial
channel is irrelevant and is not required to be populated. -/
noncomputable def SpatialConfiguration.toSourceGeometry (spatial : SpatialConfiguration)
    (source : CertifiedAuthoritativeChemicalInput)
    (lengthExact : spatial.positions.length = source.input.molecule.atomCount) :
    RealSourceGeometry source where
  conformation := spatial.toConformationAt source.input.molecule.atomCount lengthExact

@[simp] theorem SpatialConfiguration.toSourceGeometry_conformation
    (spatial : SpatialConfiguration) (source : CertifiedAuthoritativeChemicalInput)
    (lengthExact : spatial.positions.length = source.input.molecule.atomCount) :
    (spatial.toSourceGeometry source lengthExact).conformation =
      spatial.toConformationAt source.input.molecule.atomCount lengthExact := rfl

@[simp] theorem SpatialConfiguration.toSourceGeometry_apply (spatial : SpatialConfiguration)
    (source : CertifiedAuthoritativeChemicalInput)
    (lengthExact : spatial.positions.length = source.input.molecule.atomCount)
    (index : SourceAtomIndex source) :
    (spatial.toSourceGeometry source lengthExact).conformation index =
      (spatial.pointAt source.input.molecule.atomCount lengthExact index).toEuclideanPoint := rfl

/-- Pointwise exact rational-to-real cast at the first coordinate of a source geometry. -/
@[simp] theorem SpatialConfiguration.toSourceGeometry_apply_zero
    (spatial : SpatialConfiguration) (source : CertifiedAuthoritativeChemicalInput)
    (lengthExact : spatial.positions.length = source.input.molecule.atomCount)
    (index : SourceAtomIndex source) :
    ((spatial.toSourceGeometry source lengthExact).conformation index) 0 =
      ((spatial.pointAt source.input.molecule.atomCount lengthExact index).x : ℝ) := by
  simp [SpatialConfiguration.toSourceGeometry, SpatialConfiguration.toConformationAt]

/-- Pointwise exact rational-to-real cast at the second coordinate of a source geometry. -/
@[simp] theorem SpatialConfiguration.toSourceGeometry_apply_one
    (spatial : SpatialConfiguration) (source : CertifiedAuthoritativeChemicalInput)
    (lengthExact : spatial.positions.length = source.input.molecule.atomCount)
    (index : SourceAtomIndex source) :
    ((spatial.toSourceGeometry source lengthExact).conformation index) 1 =
      ((spatial.pointAt source.input.molecule.atomCount lengthExact index).y : ℝ) := by
  simp [SpatialConfiguration.toSourceGeometry, SpatialConfiguration.toConformationAt]

/-- Pointwise exact rational-to-real cast at the third coordinate of a source geometry. -/
@[simp] theorem SpatialConfiguration.toSourceGeometry_apply_two
    (spatial : SpatialConfiguration) (source : CertifiedAuthoritativeChemicalInput)
    (lengthExact : spatial.positions.length = source.input.molecule.atomCount)
    (index : SourceAtomIndex source) :
    ((spatial.toSourceGeometry source lengthExact).conformation index) 2 =
      ((spatial.pointAt source.input.molecule.atomCount lengthExact index).z : ℝ) := by
  simp [SpatialConfiguration.toSourceGeometry, SpatialConfiguration.toConformationAt]

/-- Use already-certified rational spatial evidence as real source geometry.  The length equality
is derived from the source's structural certificate; the optional channel is not assumed by the
general construction above. -/
noncomputable def CertifiedAuthoritativeChemicalInput.spatialGeometry
    (source : CertifiedAuthoritativeChemicalInput) (spatial : SpatialConfiguration)
    (observed : source.input.spatial? = some spatial) : RealSourceGeometry source :=
  spatial.toSourceGeometry source (by
    have wellFormed : source.input.SpatialIndicesWellFormed :=
      source.structurallyWellFormed.2.1
    simpa [AuthoritativeChemicalInput.SpatialIndicesWellFormed, observed] using wellFormed)

@[simp] theorem CertifiedAuthoritativeChemicalInput.spatialGeometry_conformation
    (source : CertifiedAuthoritativeChemicalInput) (spatial : SpatialConfiguration)
    (observed : source.input.spatial? = some spatial) :
    (source.spatialGeometry spatial observed).conformation =
      spatial.toConformationAt source.input.molecule.atomCount (by
        have wellFormed : source.input.SpatialIndicesWellFormed :=
          source.structurallyWellFormed.2.1
        simpa [AuthoritativeChemicalInput.SpatialIndicesWellFormed, observed] using wellFormed) :=
  rfl

/-! ## Atom reindexing transport -/

namespace MolecularConformation

variable {V W : Type*}

/-- Transport a conformation along a bijection of atom indices. -/
def reindex (equivalent : V ≃ W) (conformation : MolecularConformation V) :
    MolecularConformation W :=
  fun atom => conformation (equivalent.symm atom)

@[simp] theorem reindex_apply (equivalent : V ≃ W) (conformation : MolecularConformation V)
    (atom : W) :
    reindex equivalent conformation atom = conformation (equivalent.symm atom) := rfl

/-- Reindexing by a bijection is reversed by reindexing by its inverse. -/
theorem reindex_reindex (equivalent : V ≃ W) (conformation : MolecularConformation V) :
    reindex equivalent.symm (reindex equivalent conformation) = conformation := by
  funext atom
  simp [reindex]

/-- The symmetric direction of the reindexing inverse law. -/
theorem reindex_reindex_symm (equivalent : V ≃ W)
    (conformation : MolecularConformation W) :
    reindex equivalent (reindex equivalent.symm conformation) = conformation := by
  funext atom
  simp [reindex]

/-- Naturality of reindexing under composition of atom bijections. -/
theorem reindex_trans {U : Type*} (first : V ≃ W) (second : W ≃ U)
    (conformation : MolecularConformation V) :
    reindex (first.trans second) conformation =
      reindex second (reindex first conformation) := by
  funext atom
  simp [reindex]

/-- Reindexing is injective. -/
theorem reindex_injective (equivalent : V ≃ W) :
    Function.Injective (reindex equivalent) := by
  intro first second equal
  have := congrArg (reindex equivalent.symm) equal
  simpa [reindex_reindex] using this

/-- Reindexing is surjective. -/
theorem reindex_surjective (equivalent : V ≃ W) :
    Function.Surjective (reindex equivalent) := by
  intro conformation
  exact ⟨reindex equivalent.symm conformation,
    by simp [reindex_reindex_symm]⟩

/-- Reindexing is a bijection on conformations. -/
theorem reindex_bijective (equivalent : V ≃ W) :
    Function.Bijective (reindex equivalent) :=
  ⟨reindex_injective equivalent, reindex_surjective equivalent⟩

end MolecularConformation

namespace MolecularConformation.Ensemble

variable {V W : Type*}

/-- Transport an allowed conformational set along a bijection of atom indices. -/
def reindex (equivalent : V ≃ W) (ensemble : Ensemble V) : Ensemble W where
  allowed :=
    { conformation | MolecularConformation.reindex equivalent.symm conformation ∈ ensemble.allowed }

@[simp] theorem reindex_allowed (equivalent : V ≃ W) (ensemble : Ensemble V) :
    (reindex equivalent ensemble).allowed =
      { conformation |
        MolecularConformation.reindex equivalent.symm conformation ∈ ensemble.allowed } := rfl

/-- Membership in a reindexed ensemble is membership of the inversely transported conformation. -/
@[simp] theorem reindex_mem_iff (equivalent : V ≃ W) (ensemble : Ensemble V)
    (conformation : MolecularConformation W) :
    conformation ∈ (reindex equivalent ensemble).allowed ↔
      MolecularConformation.reindex equivalent.symm conformation ∈ ensemble.allowed :=
  Iff.rfl

/-- Both directions of membership transport: the forward image of a conformation is allowed in
the reindexed ensemble exactly when the original conformation is allowed. -/
theorem reindex_mem_iff_of_source (equivalent : V ≃ W) (ensemble : Ensemble V)
    (conformation : MolecularConformation V) :
    MolecularConformation.reindex equivalent conformation ∈
        (reindex equivalent ensemble).allowed ↔
      conformation ∈ ensemble.allowed := by
  rw [reindex_mem_iff]
  simp [MolecularConformation.reindex_reindex]

/-- Reindexing ensembles by a bijection is reversed by reindexing by its inverse. -/
theorem reindex_reindex (equivalent : V ≃ W) (ensemble : Ensemble V) :
    reindex equivalent.symm (reindex equivalent ensemble) = ensemble := by
  cases ensemble with
  | mk allowed =>
      simp only [reindex]
      congr 1
      funext conformation
      apply propext
      change MolecularConformation.reindex equivalent.symm
          (MolecularConformation.reindex equivalent conformation) ∈ allowed ↔
        conformation ∈ allowed
      rw [MolecularConformation.reindex_reindex]

/-- The symmetric direction of the ensemble reindexing inverse law. -/
theorem reindex_reindex_symm (equivalent : V ≃ W) (ensemble : Ensemble W) :
    reindex equivalent (reindex equivalent.symm ensemble) = ensemble := by
  cases ensemble with
  | mk allowed =>
      simp only [reindex]
      congr 1
      funext conformation
      apply propext
      change MolecularConformation.reindex equivalent
          (MolecularConformation.reindex equivalent.symm conformation) ∈ allowed ↔
        conformation ∈ allowed
      rw [MolecularConformation.reindex_reindex_symm]

/-- Naturality of ensemble reindexing under composition of atom bijections. -/
theorem reindex_trans {U : Type*} (first : V ≃ W) (second : W ≃ U) (ensemble : Ensemble V) :
    reindex (first.trans second) ensemble =
      reindex second (reindex first ensemble) := rfl

end MolecularConformation.Ensemble

namespace RealSourceGeometry

variable {source : CertifiedAuthoritativeChemicalInput}

/-- Encode a source-indexed geometry on an independent finite atom index related to the source
index by a bijection. -/
def reindex (representation : RealSourceGeometry source) {ι : Type}
    (equivalent : SourceAtomIndex source ≃ ι) : MolecularConformation ι :=
  MolecularConformation.reindex equivalent representation.conformation

/-- The independent-index encoding roundtrips back to the original source conformation. -/
@[simp] theorem reindex_reindex (representation : RealSourceGeometry source) {ι : Type}
    (equivalent : SourceAtomIndex source ≃ ι) :
    MolecularConformation.reindex equivalent.symm (representation.reindex equivalent) =
      representation.conformation :=
  MolecularConformation.reindex_reindex equivalent representation.conformation

/-- Reindexing a source geometry is injective. -/
theorem reindex_injective (_representation : RealSourceGeometry source) {ι : Type}
    (equivalent : SourceAtomIndex source ≃ ι) :
    Function.Injective (fun conformation : SourceConformation source =>
      MolecularConformation.reindex equivalent conformation) :=
  MolecularConformation.reindex_injective equivalent

end RealSourceGeometry

/-- A source-level conformational ensemble with reindexing transport. -/
structure RealSourceEnsemble (source : CertifiedAuthoritativeChemicalInput) where
  ensemble : SourceEnsemble source

namespace RealSourceEnsemble

variable {source : CertifiedAuthoritativeChemicalInput}

/-- Transport an allowed source ensemble to an independent finite atom index. -/
def reindex (representation : RealSourceEnsemble source) {ι : Type}
    (equivalent : SourceAtomIndex source ≃ ι) : MolecularConformation.Ensemble ι :=
  MolecularConformation.Ensemble.reindex equivalent representation.ensemble

/-- Membership in the transported ensemble is membership of the inversely transported
conformation, in both directions. -/
@[simp] theorem reindex_mem_iff (representation : RealSourceEnsemble source) {ι : Type}
    (equivalent : SourceAtomIndex source ≃ ι) (conformation : MolecularConformation ι) :
    conformation ∈ (representation.reindex equivalent).allowed ↔
      MolecularConformation.reindex equivalent.symm conformation ∈
        representation.ensemble.allowed :=
  Iff.rfl

/-- Source-side membership transport for a reindexed ensemble. -/
theorem reindex_mem_iff_of_source (representation : RealSourceEnsemble source) {ι : Type}
    (equivalent : SourceAtomIndex source ≃ ι) (conformation : SourceConformation source) :
    MolecularConformation.reindex equivalent conformation ∈
        (representation.reindex equivalent).allowed ↔
      conformation ∈ representation.ensemble.allowed :=
  MolecularConformation.Ensemble.reindex_mem_iff_of_source equivalent
    representation.ensemble conformation

/-- Reindexing an ensemble onto an independent atom index roundtrips back to the source ensemble. -/
@[simp] theorem reindex_reindex (representation : RealSourceEnsemble source) {ι : Type}
    (equivalent : SourceAtomIndex source ≃ ι) :
    MolecularConformation.Ensemble.reindex equivalent.symm
        (representation.reindex equivalent) = representation.ensemble :=
  MolecularConformation.Ensemble.reindex_reindex equivalent representation.ensemble

end RealSourceEnsemble

/-! ## Finite conformer collections embedded into arbitrary allowed sets -/

/-- Explicit scope of a finite conformer collection.  `empty` records a positively empty
collection and `unknown` records missing information; both contribute no allowed conformations.
`selected` records the listed conformers only and does not assert that they form a physical
mixture or a complete conformational space. -/
inductive ConformerScope where
  | empty
  | selected
  | unknown
  deriving DecidableEq, Repr

/-- A finite indexed collection of source conformers. -/
structure FiniteConformerCollection (source : CertifiedAuthoritativeChemicalInput) where
  scope : ConformerScope
  count : ℕ
  conformer : Fin count → SourceConformation source

namespace FiniteConformerCollection

variable {source : CertifiedAuthoritativeChemicalInput}

/-- Empty and unknown-scope collections must not list conformers.  `selected` collections may list
any finite number. -/
def WellScoped (collection : FiniteConformerCollection source) : Prop :=
  match collection.scope with
  | ConformerScope.empty => collection.count = 0
  | ConformerScope.unknown => collection.count = 0
  | ConformerScope.selected => True

/-- The explicitly empty finite collection. -/
def empty (source : CertifiedAuthoritativeChemicalInput) : FiniteConformerCollection source where
  scope := ConformerScope.empty
  count := 0
  conformer := Fin.elim0

/-- A collection whose conformer scope is unknown.  It contributes no conformers rather than
silently claiming that every conformation is allowed. -/
def unknown (source : CertifiedAuthoritativeChemicalInput) : FiniteConformerCollection source where
  scope := ConformerScope.unknown
  count := 0
  conformer := Fin.elim0

/-- An explicitly selected finite family of conformers. -/
def ofFamily {n : ℕ} (conformer : Fin n → SourceConformation source) :
    FiniteConformerCollection source where
  scope := ConformerScope.selected
  count := n
  conformer := conformer

@[simp] theorem empty_scope (source : CertifiedAuthoritativeChemicalInput) :
    (empty source).scope = ConformerScope.empty := rfl

@[simp] theorem empty_count (source : CertifiedAuthoritativeChemicalInput) :
    (empty source).count = 0 := rfl

@[simp] theorem unknown_scope (source : CertifiedAuthoritativeChemicalInput) :
    (unknown source).scope = ConformerScope.unknown := rfl

@[simp] theorem unknown_count (source : CertifiedAuthoritativeChemicalInput) :
    (unknown source).count = 0 := rfl

@[simp] theorem ofFamily_scope {n : ℕ} (conformer : Fin n → SourceConformation source) :
    (ofFamily conformer).scope = ConformerScope.selected := rfl

@[simp] theorem ofFamily_count {n : ℕ} (conformer : Fin n → SourceConformation source) :
    (ofFamily conformer).count = n := rfl

theorem empty_wellScoped (source : CertifiedAuthoritativeChemicalInput) :
    (empty source).WellScoped := rfl

theorem unknown_wellScoped (source : CertifiedAuthoritativeChemicalInput) :
    (unknown source).WellScoped := rfl

theorem ofFamily_wellScoped {n : ℕ} (conformer : Fin n → SourceConformation source) :
    (ofFamily conformer).WellScoped := trivial

/-- The allowed set contributed by a finite collection: exactly the range of its conformer
indexing.  It is finite and is never silently enlarged to `Set.univ`. -/
def toEnsemble (collection : FiniteConformerCollection source) : SourceEnsemble source where
  allowed := Set.range collection.conformer

@[simp] theorem mem_toEnsemble_iff (collection : FiniteConformerCollection source)
    (conformation : SourceConformation source) :
    conformation ∈ collection.toEnsemble.allowed ↔
      ∃ index : Fin collection.count, collection.conformer index = conformation :=
  Iff.rfl

/-- Every listed conformer belongs to its finite ensemble. -/
theorem mem_toEnsemble (collection : FiniteConformerCollection source)
    (index : Fin collection.count) :
    collection.conformer index ∈ collection.toEnsemble.allowed :=
  ⟨index, rfl⟩

/-- Distinct listed conformers remain distinct members of the finite ensemble.  A selected finite
collection is not collapsed to a single snapshot conformation. -/
theorem distinct_members (collection : FiniteConformerCollection source)
    {first second : Fin collection.count}
    (distinct : collection.conformer first ≠ collection.conformer second) :
    collection.conformer first ∈ collection.toEnsemble.allowed ∧
      collection.conformer second ∈ collection.toEnsemble.allowed ∧
        collection.conformer first ≠ collection.conformer second :=
  ⟨mem_toEnsemble collection first, mem_toEnsemble collection second, distinct⟩

/-- Embed a finite collection into an arbitrary allowed set, given that every listed conformer is
allowed there.  The result is the finite collection intersected with the supplied set, so it can
never exceed either. -/
def embedInto (collection : FiniteConformerCollection source) (target : SourceEnsemble source)
    (_member : ∀ index : Fin collection.count,
      collection.conformer index ∈ target.allowed) : SourceEnsemble source where
  allowed := Set.range collection.conformer ∩ target.allowed

@[simp] theorem mem_embedInto_iff (collection : FiniteConformerCollection source)
    (target : SourceEnsemble source)
    (member : ∀ index : Fin collection.count,
      collection.conformer index ∈ target.allowed)
    (conformation : SourceConformation source) :
    conformation ∈ (collection.embedInto target member).allowed ↔
      (∃ index : Fin collection.count, collection.conformer index = conformation) ∧
        conformation ∈ target.allowed :=
  Iff.rfl

/-- The embedded finite ensemble is contained in the arbitrary allowed set. -/
theorem embedInto_allowed_subset (collection : FiniteConformerCollection source)
    (target : SourceEnsemble source)
    (member : ∀ index : Fin collection.count,
      collection.conformer index ∈ target.allowed) :
    (collection.embedInto target member).allowed ⊆ target.allowed := by
  rintro conformation ⟨_, allowed⟩
  exact allowed

/-- Every listed conformer survives embedding into an allowed set that contains it. -/
theorem mem_embedInto (collection : FiniteConformerCollection source)
    (target : SourceEnsemble source)
    (member : ∀ index : Fin collection.count,
      collection.conformer index ∈ target.allowed)
    (index : Fin collection.count) :
    collection.conformer index ∈ (collection.embedInto target member).allowed :=
  ⟨⟨index, rfl⟩, member index⟩

/-- The empty collection contributes the empty allowed set. -/
@[simp] theorem empty_toEnsemble_allowed (source : CertifiedAuthoritativeChemicalInput) :
    (empty source).toEnsemble.allowed = (∅ : Set (SourceConformation source)) := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro conformation
  rintro ⟨index, _⟩
  exact Fin.elim0 index

/-- An unknown-scope collection also contributes the empty allowed set.  This records the absence
of information explicitly instead of asserting an actual physical mixture. -/
@[simp] theorem unknown_toEnsemble_allowed (source : CertifiedAuthoritativeChemicalInput) :
    (unknown source).toEnsemble.allowed = (∅ : Set (SourceConformation source)) := by
  rw [Set.eq_empty_iff_forall_notMem]
  intro conformation
  rintro ⟨index, _⟩
  exact Fin.elim0 index

end FiniteConformerCollection

/-! ## Certified finite conformer collections

The raw `FiniteConformerCollection` above is deliberately uncertified: its scope field is not
bundled with evidence that the scope is honoured.  Downstream chemical consumers must use the
certified wrapper below, which bundles `WellScoped`.  In particular an `.empty` or `.unknown`
certified collection provably has count zero and contributes the empty allowed set.  The
`.unknown` case records only that no conformers were supplied; it is never evidence that no
physical conformation exists, and the scope metadata remains available on the certified value. -/

/-- A finite collection bundled with the proof that its declared scope is honoured. -/
structure CertifiedFiniteConformerCollection
    (source : CertifiedAuthoritativeChemicalInput) where
  collection : FiniteConformerCollection source
  wellScoped : collection.WellScoped

namespace CertifiedFiniteConformerCollection

variable {source : CertifiedAuthoritativeChemicalInput}

/-- The scope metadata is retained on the certified value. -/
def scope (certified : CertifiedFiniteConformerCollection source) : ConformerScope :=
  certified.collection.scope

/-- The declared number of conformers is retained on the certified value. -/
def count (certified : CertifiedFiniteConformerCollection source) : ℕ :=
  certified.collection.count

/-- The indexed conformer family is retained on the certified value. -/
def conformer (certified : CertifiedFiniteConformerCollection source) :
    Fin certified.collection.count → SourceConformation source :=
  certified.collection.conformer

@[simp] theorem collection_scope (certified : CertifiedFiniteConformerCollection source) :
    certified.collection.scope = certified.scope := rfl

@[simp] theorem collection_count (certified : CertifiedFiniteConformerCollection source) :
    certified.collection.count = certified.count := rfl

/-- Certification forces zero count for an explicitly empty scope. -/
theorem count_eq_zero_of_empty_scope (certified : CertifiedFiniteConformerCollection source)
    (emptyScope : certified.collection.scope = ConformerScope.empty) :
    certified.collection.count = 0 := by
  have wellScoped := certified.wellScoped
  unfold FiniteConformerCollection.WellScoped at wellScoped
  rw [emptyScope] at wellScoped
  exact wellScoped

/-- Certification forces zero count for an unknown scope. -/
theorem count_eq_zero_of_unknown_scope (certified : CertifiedFiniteConformerCollection source)
    (unknownScope : certified.collection.scope = ConformerScope.unknown) :
    certified.collection.count = 0 := by
  have wellScoped := certified.wellScoped
  unfold FiniteConformerCollection.WellScoped at wellScoped
  rw [unknownScope] at wellScoped
  exact wellScoped

/-- The certified empty collection. -/
def empty (source : CertifiedAuthoritativeChemicalInput) :
    CertifiedFiniteConformerCollection source where
  collection := FiniteConformerCollection.empty source
  wellScoped := FiniteConformerCollection.empty_wellScoped source

/-- The certified unknown-scope collection.  It carries no conformers and asserts nothing about
which physical conformations exist. -/
def unknown (source : CertifiedAuthoritativeChemicalInput) :
    CertifiedFiniteConformerCollection source where
  collection := FiniteConformerCollection.unknown source
  wellScoped := FiniteConformerCollection.unknown_wellScoped source

/-- A certified explicitly selected finite family of conformers. -/
def ofFamily {n : ℕ} (conformer : Fin n → SourceConformation source) :
    CertifiedFiniteConformerCollection source where
  collection := FiniteConformerCollection.ofFamily conformer
  wellScoped := FiniteConformerCollection.ofFamily_wellScoped conformer

@[simp] theorem empty_scope (source : CertifiedAuthoritativeChemicalInput) :
    (empty source).scope = ConformerScope.empty := rfl

@[simp] theorem empty_count (source : CertifiedAuthoritativeChemicalInput) :
    (empty source).count = 0 := rfl

@[simp] theorem unknown_scope (source : CertifiedAuthoritativeChemicalInput) :
    (unknown source).scope = ConformerScope.unknown := rfl

@[simp] theorem unknown_count (source : CertifiedAuthoritativeChemicalInput) :
    (unknown source).count = 0 := rfl

@[simp] theorem ofFamily_scope {n : ℕ} (conformer : Fin n → SourceConformation source) :
    (ofFamily conformer).scope = ConformerScope.selected := rfl

@[simp] theorem ofFamily_count {n : ℕ} (conformer : Fin n → SourceConformation source) :
    (ofFamily conformer).count = n := rfl

/-- The allowed set contributed by a certified finite collection.  It is exactly the range of the
retained conformer indexing; the scope metadata is not discarded from the certified value. -/
def toEnsemble (certified : CertifiedFiniteConformerCollection source) :
    SourceEnsemble source :=
  certified.collection.toEnsemble

@[simp] theorem toEnsemble_allowed (certified : CertifiedFiniteConformerCollection source) :
    certified.toEnsemble.allowed = Set.range certified.collection.conformer := rfl

@[simp] theorem mem_toEnsemble_iff (certified : CertifiedFiniteConformerCollection source)
    (conformation : SourceConformation source) :
    conformation ∈ certified.toEnsemble.allowed ↔
      ∃ index : Fin certified.collection.count,
        certified.collection.conformer index = conformation :=
  Iff.rfl

/-- Every listed conformer belongs to the certified finite ensemble. -/
theorem mem_toEnsemble (certified : CertifiedFiniteConformerCollection source)
    (index : Fin certified.collection.count) :
    certified.collection.conformer index ∈ certified.toEnsemble.allowed :=
  FiniteConformerCollection.mem_toEnsemble certified.collection index

/-- A certified empty-scope collection contributes exactly the empty allowed set. -/
theorem toEnsemble_allowed_eq_empty_of_empty_scope
    (certified : CertifiedFiniteConformerCollection source)
    (emptyScope : certified.collection.scope = ConformerScope.empty) :
    certified.toEnsemble.allowed = (∅ : Set (SourceConformation source)) := by
  have countZero := certified.count_eq_zero_of_empty_scope emptyScope
  rw [Set.eq_empty_iff_forall_notMem]
  intro conformation
  rintro ⟨index, _⟩
  exact Fin.elim0 (countZero ▸ index)

/-- A certified unknown-scope collection contributes exactly the empty allowed set.  This is a
statement about the supplied conformers only, not about the physically allowed space. -/
theorem toEnsemble_allowed_eq_empty_of_unknown_scope
    (certified : CertifiedFiniteConformerCollection source)
    (unknownScope : certified.collection.scope = ConformerScope.unknown) :
    certified.toEnsemble.allowed = (∅ : Set (SourceConformation source)) := by
  have countZero := certified.count_eq_zero_of_unknown_scope unknownScope
  rw [Set.eq_empty_iff_forall_notMem]
  intro conformation
  rintro ⟨index, _⟩
  exact Fin.elim0 (countZero ▸ index)

/-- Any certified collection whose scope is not `selected` contributes the empty allowed set. -/
theorem toEnsemble_allowed_eq_empty_of_not_selected
    (certified : CertifiedFiniteConformerCollection source)
    (notSelected : certified.collection.scope ≠ ConformerScope.selected) :
    certified.toEnsemble.allowed = (∅ : Set (SourceConformation source)) := by
  cases scopeEq : certified.collection.scope with
  | empty => exact certified.toEnsemble_allowed_eq_empty_of_empty_scope scopeEq
  | selected => exact absurd scopeEq notSelected
  | unknown => exact certified.toEnsemble_allowed_eq_empty_of_unknown_scope scopeEq

/-- Embed a certified finite collection into an arbitrary allowed set, given that every listed
conformer is allowed there. -/
def embedInto (certified : CertifiedFiniteConformerCollection source)
    (target : SourceEnsemble source)
    (member : ∀ index : Fin certified.collection.count,
      certified.collection.conformer index ∈ target.allowed) :
    SourceEnsemble source :=
  certified.collection.embedInto target member

/-- The certified embedded ensemble is contained in the arbitrary allowed set. -/
theorem embedInto_allowed_subset (certified : CertifiedFiniteConformerCollection source)
    (target : SourceEnsemble source)
    (member : ∀ index : Fin certified.collection.count,
      certified.collection.conformer index ∈ target.allowed) :
    (certified.embedInto target member).allowed ⊆ target.allowed :=
  FiniteConformerCollection.embedInto_allowed_subset certified.collection target member

/-- Every listed conformer survives certified embedding into an allowed set containing it. -/
theorem mem_embedInto (certified : CertifiedFiniteConformerCollection source)
    (target : SourceEnsemble source)
    (member : ∀ index : Fin certified.collection.count,
      certified.collection.conformer index ∈ target.allowed)
    (index : Fin certified.collection.count) :
    certified.collection.conformer index ∈
      (certified.embedInto target member).allowed :=
  FiniteConformerCollection.mem_embedInto certified.collection target member index

end CertifiedFiniteConformerCollection

/-! ## Small formal example

One carbon atom, one rational origin point, and a certified source with no optional spatial
channel.  The example is a formal witness that the general construction does not require the
source to already carry spatial evidence.
-/

namespace ExampleOneAtom

/-- Carbon, atomic number 6. -/
def carbon : PeriodicElement where
  atomicNumber := 6
  positive := by decide
  atMost118 := by decide

/-- The single carbon atom. -/
def carbonAtom : SemanticAtom := { element := carbon }

/-- A structurally certified one-carbon source with neither optional evidence channel. -/
def source : CertifiedAuthoritativeChemicalInput where
  input :=
    { molecule := { atoms := [carbonAtom], interactions := [] }
      spatial? := none
      diagram? := none }
  structurallyWellFormed := by
    refine ⟨?_, trivial, trivial⟩
    simp [SemanticMolecule.StructurallyWellFormed]

/-- The rational origin. -/
def origin : CartesianPoint3 := { x := 0, y := 0, z := 0 }

/-- One rational conformation with one point for the one source atom. -/
noncomputable def spatial : SpatialConfiguration := { positions := [origin] }

theorem spatial_length : spatial.positions.length = source.input.molecule.atomCount := rfl

/-- Attach the rational geometry to the pure source. -/
noncomputable def geometry : RealSourceGeometry source :=
  spatial.toSourceGeometry source spatial_length

/-- The attached conformation casts the first rational coordinate exactly. -/
theorem geometry_apply_zero :
    ((geometry.conformation ⟨0, by simp [source, SemanticMolecule.atomCount]⟩) 0) =
      (origin.x : ℝ) := by
  change ((spatial.toConformationAt source.input.molecule.atomCount spatial_length
      ⟨0, by simp [source, SemanticMolecule.atomCount]⟩) 0) = (origin.x : ℝ)
  rw [SpatialConfiguration.toConformationAt_apply_zero]
  simp [spatial, origin, SpatialConfiguration.pointAt]

/-- The source projection is exactly the original pure source. -/
theorem geometry_source : geometry.sourceOf = source := rfl

end ExampleOneAtom

end OneCenter
end TetraStereo
