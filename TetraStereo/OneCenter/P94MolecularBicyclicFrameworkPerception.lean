import TetraStereo.OneCenter.P94MolecularTwistInOutRequestScheduler

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace BlueBookP94.P94MolecularBicyclicFramework

open CoordinateTwistInOut
open P94MolecularRequestScheduler

/-!
# Finite molecular perception of P-94 bicyclic frameworks

For the P-94.3.2.6 in/out family, a bicyclic framework is represented by its graph-theoretic
theta core: two bridgeheads joined by exactly three simple bonded paths whose interiors are
pairwise disjoint.  Every path and every framework is enumerated over the finite raw molecule;
there is no depth fuel and no caller-selected graph candidate.

This layer deliberately does not guess the remaining source-sensitive facts.  Whether a named
bridge is sufficiently long, which exact point is the cage interior, and whether a bridgehead has
a lone pair remain explicit premises.  `graphDerivedPremises` replaces only the two relations that
the molecular graph determines here: theta-framework identity and full-framework atom membership.
-/

/-! ## Simple bonded paths between two bridgeheads -/

/-- A finite simple molecular path with the stated ordered endpoints. -/
def BondedPathBetween (molecule : RawMolecule) (first second : ℕ)
    (path : List ℕ) : Prop :=
  path.Nodup ∧
    (∀ atom ∈ path, atom < molecule.atomCount) ∧
    path.head? = some first ∧
    path.getLast? = some second ∧
    2 ≤ path.length ∧
    P94ConformationUnit.ConsecutivelyBonded molecule path

noncomputable instance bondedPathBetweenDecidable
    (molecule : RawMolecule) (first second : ℕ) (path : List ℕ) :
    Decidable (BondedPathBetween molecule first second path) :=
  Classical.propDecidable _

/-- All simple bonded paths between two atoms of one finite molecule. -/
noncomputable def bondedPathsBetween (molecule : RawMolecule) (first second : ℕ) :
    Finset (List ℕ) :=
  (boundedNodupStatePaths (List.range molecule.atomCount)).filter
    (BondedPathBetween molecule first second)

theorem mem_bondedPathsBetween_iff (molecule : RawMolecule) (first second : ℕ)
    (path : List ℕ) :
    path ∈ bondedPathsBetween molecule first second ↔
      BondedPathBetween molecule first second path := by
  constructor
  · intro present
    exact (Finset.mem_filter.mp present).2
  · intro valid
    apply Finset.mem_filter.mpr
    refine ⟨(mem_boundedNodupStatePaths_iff
      (List.range molecule.atomCount) path).mpr ⟨valid.1, ?_⟩, valid⟩
    intro atom membership
    exact List.mem_range.mpr (valid.2.1 atom membership)

/-! ## Theta frameworks and complete finite enumeration -/

/-- A graph-theoretic bicyclic theta core.  `bridges` is a set rather than an ordered triple, so
permuting the three bridges cannot manufacture a second framework record. -/
structure ThetaFramework where
  firstBridgehead : ℕ
  secondBridgehead : ℕ
  bridges : Finset (List ℕ)
  deriving DecidableEq

namespace ThetaFramework

/-- Remove both endpoints from a path. -/
def pathInterior (path : List ℕ) : List ℕ :=
  path.tail.dropLast

/-- The three bridges may meet only at their two common endpoints. -/
def PairwiseInternallyDisjoint (framework : ThetaFramework) : Prop :=
  ∀ first ∈ framework.bridges, ∀ second ∈ framework.bridges,
    first ≠ second → List.Disjoint (pathInterior first) (pathInterior second)

noncomputable instance pairwiseInternallyDisjointDecidable (framework : ThetaFramework) :
    Decidable framework.PairwiseInternallyDisjoint :=
  Classical.propDecidable _

/-- Exact finite-graph meaning of one represented bicyclic framework.  Ordering the bridgeheads
by atom index gives every undirected theta core one endpoint orientation. -/
def Valid (molecule : RawMolecule) (framework : ThetaFramework) : Prop :=
  framework.firstBridgehead < framework.secondBridgehead ∧
    framework.secondBridgehead < molecule.atomCount ∧
    framework.bridges.card = 3 ∧
    (∀ path ∈ framework.bridges,
      BondedPathBetween molecule framework.firstBridgehead framework.secondBridgehead path) ∧
    framework.PairwiseInternallyDisjoint

noncomputable instance validDecidable (molecule : RawMolecule) (framework : ThetaFramework) :
    Decidable (framework.Valid molecule) :=
  Classical.propDecidable _

/-- Full-framework membership, not merely membership in the currently named bridge. -/
def ContainsAtom (framework : ThetaFramework) (atom : ℕ) : Prop :=
  ∃ path ∈ framework.bridges, atom ∈ path

/-- The actual bridgehead sites of the represented theta core are exactly its two common path
endpoints.  This is intentionally stricter than `ContainsAtom`. -/
def IsBridgehead (framework : ThetaFramework) (atom : ℕ) : Prop :=
  atom = framework.firstBridgehead ∨ atom = framework.secondBridgehead

/-- Turn one bridge path into the molecule-local carrier expected by the P-94 analyzer. -/
def bridgeUnit (path : List ℕ) : P94ConformationUnit :=
  { kind := .bicyclicBridge, atoms := path }

noncomputable def bridgeUnits (framework : ThetaFramework) : Finset P94ConformationUnit :=
  framework.bridges.image bridgeUnit

def NamesBridge (framework : ThetaFramework) (unit : P94ConformationUnit) : Prop :=
  unit ∈ framework.bridgeUnits

noncomputable instance namesBridgeDecidable
    (framework : ThetaFramework) (unit : P94ConformationUnit) :
    Decidable (framework.NamesBridge unit) :=
  Classical.propDecidable _

/-- A valid theta framework whose named P-94 carrier is one of its three complete bridges. -/
def ValidFor (framework : ThetaFramework) (molecule : RawMolecule)
    (unit : P94ConformationUnit) : Prop :=
  framework.Valid molecule ∧ framework.NamesBridge unit

noncomputable instance validForDecidable (framework : ThetaFramework)
    (molecule : RawMolecule) (unit : P94ConformationUnit) :
    Decidable (framework.ValidFor molecule unit) :=
  Classical.propDecidable _

end ThetaFramework

private noncomputable def thetaFrameworkUniverse (molecule : RawMolecule) :
    Finset ThetaFramework :=
  (((List.range molecule.atomCount).toFinset.product
      (List.range molecule.atomCount).toFinset).product
    ((boundedNodupStatePaths (List.range molecule.atomCount)).powerset)).image fun entry =>
      { firstBridgehead := entry.1.1
        secondBridgehead := entry.1.2
        bridges := entry.2 }

private theorem mem_thetaFrameworkUniverse_iff (molecule : RawMolecule)
    (framework : ThetaFramework) :
    framework ∈ thetaFrameworkUniverse molecule ↔
      framework.firstBridgehead < molecule.atomCount ∧
        framework.secondBridgehead < molecule.atomCount ∧
        framework.bridges ⊆ boundedNodupStatePaths (List.range molecule.atomCount) := by
  constructor
  · intro present
    rcases Finset.mem_image.mp present with ⟨entry, entryPresent, equal⟩
    rcases Finset.mem_product.mp entryPresent with ⟨endpointsPresent, bridgesPresent⟩
    rcases Finset.mem_product.mp endpointsPresent with ⟨firstPresent, secondPresent⟩
    cases equal
    exact ⟨List.mem_range.mp (List.mem_toFinset.mp firstPresent),
      List.mem_range.mp (List.mem_toFinset.mp secondPresent),
      Finset.mem_powerset.mp bridgesPresent⟩
  · rintro ⟨firstBounded, secondBounded, bridgesBounded⟩
    apply Finset.mem_image.mpr
    refine ⟨((framework.firstBridgehead, framework.secondBridgehead), framework.bridges), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨Finset.mem_product.mpr
          ⟨List.mem_toFinset.mpr (List.mem_range.mpr firstBounded),
            List.mem_toFinset.mpr (List.mem_range.mpr secondBounded)⟩,
          Finset.mem_powerset.mpr bridgesBounded⟩
    · cases framework
      rfl

/-- Every graph-theoretically valid theta framework in the finite molecule, with no traversal
fuel and no nominated bridgehead or bridge set. -/
noncomputable def thetaFrameworks (molecule : RawMolecule) : Finset ThetaFramework :=
  (thetaFrameworkUniverse molecule).filter (ThetaFramework.Valid molecule)

theorem mem_thetaFrameworks_iff (molecule : RawMolecule) (framework : ThetaFramework) :
    framework ∈ thetaFrameworks molecule ↔ framework.Valid molecule := by
  constructor
  · intro present
    exact (Finset.mem_filter.mp present).2
  · intro valid
    apply Finset.mem_filter.mpr
    refine ⟨(mem_thetaFrameworkUniverse_iff molecule framework).mpr
      ⟨Nat.lt_trans valid.1 valid.2.1, valid.2.1, ?_⟩, valid⟩
    intro path pathPresent
    have pathValid := valid.2.2.2.1 path pathPresent
    exact (mem_boundedNodupStatePaths_iff
      (List.range molecule.atomCount) path).mpr ⟨pathValid.1, fun atom atomPresent =>
        List.mem_range.mpr (pathValid.2.1 atom atomPresent)⟩

/-- A graph-derived framework can name only a molecularly valid P-94 bicyclic-bridge carrier. -/
theorem validFor_unit_validFor (molecule : RawMolecule) (unit : P94ConformationUnit)
    (framework : ThetaFramework) (valid : framework.ValidFor molecule unit) :
    unit.ValidFor molecule := by
  rcases Finset.mem_image.mp valid.2 with ⟨path, pathPresent, unitEqual⟩
  have pathValid := valid.1.2.2.2.1 path pathPresent
  subst unit
  exact ⟨pathValid.1, pathValid.2.1, rfl, pathValid.2.2.2.2.1,
    pathValid.2.2.2.2.2⟩

/-! ## Exact adapter into the independent P-94 in/out authority boundary -/

/-- The three P-94 premises intentionally retained after graph-derived framework perception. -/
structure RetainedInOutPremises where
  BridgeLongEnough : RawMolecule → P94ConformationUnit → ThetaFramework → Prop
  InteriorWitness : RawMolecule → P94ConformationUnit → ThetaFramework →
    ℕ → SpatialConfiguration → CartesianPoint3 → Prop
  LonePairAt : RawMolecule → ℕ → Prop

def graphDerivedPremises (retained : RetainedInOutPremises) :
    IndependentInOutPremises ThetaFramework :=
  { BicyclicFramework := fun molecule unit framework => framework.ValidFor molecule unit
    BridgeLongEnough := retained.BridgeLongEnough
    InteriorWitness := retained.InteriorWitness
    AtomInFramework := fun _molecule _unit framework atom => framework.ContainsAtom atom
    BridgeheadInFramework := fun molecule unit framework atom =>
      framework.ValidFor molecule unit ∧ framework.IsBridgehead atom
    LonePairAt := retained.LonePairAt }

theorem graphDerivedPremises_bicyclicFramework_iff (retained : RetainedInOutPremises)
    (molecule : RawMolecule) (unit : P94ConformationUnit) (framework : ThetaFramework) :
    (graphDerivedPremises retained).BicyclicFramework molecule unit framework ↔
      framework.ValidFor molecule unit :=
  Iff.rfl

theorem graphDerivedPremises_atomInFramework_iff (retained : RetainedInOutPremises)
    (molecule : RawMolecule) (unit : P94ConformationUnit) (framework : ThetaFramework)
    (atom : ℕ) :
    (graphDerivedPremises retained).AtomInFramework molecule unit framework atom ↔
      ∃ path ∈ framework.bridges, atom ∈ path :=
  Iff.rfl

theorem graphDerivedPremises_bridgeheadInFramework_iff (retained : RetainedInOutPremises)
    (molecule : RawMolecule) (unit : P94ConformationUnit) (framework : ThetaFramework)
    (atom : ℕ) :
    (graphDerivedPremises retained).BridgeheadInFramework molecule unit framework atom ↔
      framework.ValidFor molecule unit ∧ framework.IsBridgehead atom :=
  Iff.rfl

/-! ## Exhaustive observation scheduling over every valid framework for one named bridge -/

noncomputable def thetaFrameworksForUnit (molecule : RawMolecule)
    (unit : P94ConformationUnit) : Finset ThetaFramework :=
  (thetaFrameworks molecule).filter fun framework => framework.NamesBridge unit

theorem mem_thetaFrameworksForUnit_iff (molecule : RawMolecule)
    (unit : P94ConformationUnit) (framework : ThetaFramework) :
    framework ∈ thetaFrameworksForUnit molecule unit ↔
      framework.ValidFor molecule unit := by
  rw [thetaFrameworksForUnit, Finset.mem_filter, mem_thetaFrameworks_iff]
  rfl

/-- All coordinate/electron data for an in/out observation except the graph-derived framework. -/
structure CoordinateInOutObservationTemplate where
  spatial : SpatialConfiguration
  virtualPoints : CoordinateTorsion.VirtualTorsionPointLedger
  bridgehead : ℕ
  directedParticipant : TorsionParticipant ℕ
  interior : CartesianPoint3

def CoordinateInOutObservationTemplate.toObservation
    (template : CoordinateInOutObservationTemplate) (framework : ThetaFramework) :
    CoordinateInOutObservation ThetaFramework :=
  { framework := framework
    spatial := template.spatial
    virtualPoints := template.virtualPoints
    bridgehead := template.bridgehead
    directedParticipant := template.directedParticipant
    interior := template.interior }

/-- Every supplied coordinate observation template instantiated at every graph-derived framework
which contains the named bridge unit. -/
noncomputable def scheduledCoordinateInOutObservations (molecule : RawMolecule)
    (unit : P94ConformationUnit) (templates : List CoordinateInOutObservationTemplate) :
    List (CoordinateInOutObservation ThetaFramework) :=
  (thetaFrameworksForUnit molecule unit).toList.flatMap fun framework =>
    templates.map fun template => template.toObservation framework

theorem mem_scheduledCoordinateInOutObservations_iff (molecule : RawMolecule)
    (unit : P94ConformationUnit) (templates : List CoordinateInOutObservationTemplate)
    (observation : CoordinateInOutObservation ThetaFramework) :
    observation ∈ scheduledCoordinateInOutObservations molecule unit templates ↔
      ∃ framework, framework.ValidFor molecule unit ∧
        ∃ template ∈ templates, template.toObservation framework = observation := by
  simp only [scheduledCoordinateInOutObservations, List.mem_flatMap, List.mem_map,
    Finset.mem_toList, mem_thetaFrameworksForUnit_iff]

/-- The graph-derived observation list packaged for the existing all-ordered-pairs scheduler. -/
noncomputable def scheduledCoordinateInOutLedger (molecule : RawMolecule)
    (unit : P94ConformationUnit) (templates : List CoordinateInOutObservationTemplate) :
    CoordinateInOutLedger ThetaFramework :=
  { unit := unit
    observations := scheduledCoordinateInOutObservations molecule unit templates }

end BlueBookP94.P94MolecularBicyclicFramework
end TetraStereo.OneCenter
