import TetraStereo.OneCenter.CanonicalRule3SourceObservationFidelitySmiles
import TetraStereo.OneCenter.LocalizedRule3Spatial
import TetraStereo.KernelOnly

set_option autoImplicit false

namespace TetraStereo
namespace OneCenter
namespace Rule3PhysicalMultiplicityFidelity

open ChemistryNormalizationResult
open RawMolecule
























/-- Atom list.  Indices are stable across `withExplicitHydrogens`: appended hydrogens receive
indices past the end of this list. -/
def atoms : List AtomSpec :=
  [ { element := Element.C, tetrahedral? := some TetrahedralInputParity.clockwise }, -- 0 centre
    { element := Element.C },  -- 1 chain root / near reference of unit 2=3
    { element := Element.C },  -- 2 near endpoint of unit 2=3
    { element := Element.C },  -- 3 far endpoint of unit 2=3
    { element := Element.C },  -- 4 spacer / far reference of unit 2=3, entry of unit 5=6
    { element := Element.C },  -- 5 near endpoint of unit 5=6
    { element := Element.C },  -- 6 far endpoint of unit 5=6
    { element := Element.F },  -- 7 centre ligand F
    { element := Element.Cl }, -- 8 centre ligand Cl
    { element := Element.H },  -- 9 centre ligand H
    { element := Element.Cl } ] -- 10 far reference of unit 5=6

/-- One raw bond record. -/
def bond (source target : ℕ) (kind : ParsedBondKind) : RawBond :=
  { source := source, target := target, kind := kind }

/-- Bond list.  The four centre bonds come first so that `ligandsWithLonePair 0` is
`[1, 7, 8, 9]` in bond-list fallback order. -/
def bonds : List RawBond :=
  [ bond 0 1 ParsedBondKind.single,
    bond 0 7 ParsedBondKind.single,
    bond 0 8 ParsedBondKind.single,
    bond 0 9 ParsedBondKind.single,
    bond 1 2 ParsedBondKind.down,
    bond 2 3 ParsedBondKind.double,
    bond 3 4 ParsedBondKind.up,
    bond 4 5 ParsedBondKind.down,
    bond 5 6 ParsedBondKind.double,
    bond 6 10 ParsedBondKind.up ]

/-- The raw molecule. -/
def mol : RawMolecule :=
  { atoms := atoms, bonds := bonds }

/-- Production normalization.  There is no stereo override: the directional markers are the
source markers, and the `E/Z` perception below runs through the CIP-senior reader. -/
def result : ChemistryNormalizationResult :=
  normalizeRawMolecule mol

/-- Hydrogen-materialised parsed molecule, exactly as `seniorSideAt?` builds it. -/
def expanded : RawMolecule :=
  result.parsed.withExplicitHydrogens

/-- The fuel used by `seniorSideAt?`. -/
def expandedFuel : ℕ :=
  2 * expanded.atomCount + 2

/-! ## Admission and raw structure -/

/-- The raw molecule passes the shared structural admission contract. -/
theorem mol_admissible : mol.admissible? = true := by decide

/-- The raw molecule passes stereochemical admission: the written-neighbour view is exact. -/
theorem mol_stereochemicalAdmissible : mol.stereochemicalAdmissible? = true := by decide

/-- The raw molecule passes the encoded valence-table contract. -/
theorem mol_valenceOK : mol.valenceOK? = true := by decide

/-- The centre is tetrahedral. -/
theorem center_tetrahedral : rule3CenterTetrahedral mol 0 = true := by decide

/-- The centre is acyclic. -/
theorem center_not_cyclic :
    mol.atomLiesInCycle (2 * mol.atomCount + 2) 0 = false := by decide

/-! ## The two physical units -/

/-- First physical unit: near endpoint `2`, far endpoint `3`, branch entry `1`. -/
def unitA : Rule3SourceUnit :=
  { near := 2, far := 3, entry? := some 1 }

/-- Second physical unit: near endpoint `5`, far endpoint `6`, branch entry `4`. -/
def unitB : Rule3SourceUnit :=
  { near := 5, far := 6, entry? := some 4 }

/-- The near reference chosen by the CIP-senior reading of unit `2=3` is atom `1`. -/
def unitANearReferenceAtom : ℕ := 1

/-- The far reference chosen by the CIP-senior reading of unit `2=3` is atom `4`. -/
def unitAFarReferenceAtom : ℕ := 4

/-- The near reference chosen by the CIP-senior reading of unit `5=6` is atom `4`. -/
def unitBNearReferenceAtom : ℕ := 4

/-- The far reference chosen by the CIP-senior reading of unit `5=6` is atom `10`. -/
def unitBFarReferenceAtom : ℕ := 10

/-- The branch entry of unit `2=3` is exactly the CIP-senior substituent at its near endpoint. -/
theorem unitA_entry_is_senior : unitA.entry? = some unitANearReferenceAtom := rfl

/-- The branch entry of unit `5=6` is exactly the CIP-senior substituent at its near endpoint. -/
theorem unitB_entry_is_senior : unitB.entry? = some unitBNearReferenceAtom := rfl

/-- The CIP-senior substituents at both endpoints of unit `2=3`, read from the
hydrogen-materialised molecule by the same function used by `seniorSideAt?`. -/
theorem unitA_senior_references :
    expanded.seniorAlkeneSubstituent? expandedFuel 2 3 = some unitANearReferenceAtom ∧
      expanded.seniorAlkeneSubstituent? expandedFuel 3 2 = some unitAFarReferenceAtom := by
  decide

/-- The CIP-senior substituents at both endpoints of unit `5=6`. -/
theorem unitB_senior_references :
    expanded.seniorAlkeneSubstituent? expandedFuel 5 6 = some unitBNearReferenceAtom ∧
      expanded.seniorAlkeneSubstituent? expandedFuel 6 5 = some unitBFarReferenceAtom := by
  decide

/-- The source markers give `Z` for unit `2=3` (`seqcis` under P-92.4.1). -/
theorem perceived_unitA_Z :
    result.perceivedDoubleBondStereo? 2 3 = some DoubleBondStereo.Z := by decide

/-- The source markers give `Z` for unit `5=6`. -/
theorem perceived_unitB_Z :
    result.perceivedDoubleBondStereo? 5 6 = some DoubleBondStereo.Z := by decide

/-- The reoriented side markers at unit `2=3` are both `up`. -/
theorem seniorSide_unitA :
    result.seniorSideAt? 2 3 = some DirectionalBondMarker.up ∧
      result.seniorSideAt? 3 2 = some DirectionalBondMarker.up := by
  decide

/-- The reoriented side markers at unit `5=6` are both `up`. -/
theorem seniorSide_unitB :
    result.seniorSideAt? 5 6 = some DirectionalBondMarker.up ∧
      result.seniorSideAt? 6 5 = some DirectionalBondMarker.up := by
  decide

/-- Absolute Rule-3 geometry of unit `2=3`. -/
theorem absolute_unitA :
    rule3AbsoluteGeometry? result mol 2 3 = some OfficialRule3Geometry.seqcis := by decide

/-- Absolute Rule-3 geometry of unit `5=6`. -/
theorem absolute_unitB :
    rule3AbsoluteGeometry? result mol 5 6 = some OfficialRule3Geometry.seqcis := by decide

/-- The entry-relative source reading of unit `2=3`: the entry `1` is the senior side there,
so it agrees with the absolute reading. -/
theorem entryGeometry_unitA :
    rule3EntryGeometry? result mol 2 3 1 = some OfficialRule3Geometry.seqcis := by decide

/-- The entry-relative source reading of unit `5=6`: the entry `4` is the senior side there,
so it agrees with the absolute reading. -/
theorem entryGeometry_unitB :
    rule3EntryGeometry? result mol 5 6 4 = some OfficialRule3Geometry.seqcis := by decide

/-! ## The actual production policy

The two units are the only evidence on the chain ligand `1`, they are distinct, they are admitted,
and their source geometry is known.  The policy preserves both source-reference geometries and leaves `flipped` empty. -/

/-- The canonical source evidence on ligand `1` is exactly the two units `2=3` and `5=6`. -/
theorem evidence_ligand1 :
    rule3SourceEvidenceOnBranch result mol 0 true false 1 = [unitA, unitB] := by decide

/-- The exact production policy at the tetrahedral acyclic centre. -/
theorem centerPolicy_eq :
    rule3CenterPolicy result mol 0 =
      { cyclic := false, coupled := false, excluded := [], flipped := [] } := by decide

/-- The actual policy never requests a count-based geometry flip. -/
theorem centerPolicy_flipped :
    (rule3CenterPolicy result mol 0).flipped = [] := by
  rw [centerPolicy_eq]

/-- The actual policy is the non-cyclic, non-coupled case. -/
theorem centerPolicy_cyclic :
    (rule3CenterPolicy result mol 0).cyclic = false := by
  rw [centerPolicy_eq]

/-- The actual policy excludes no addressed occurrence. -/
theorem centerPolicy_excluded :
    (rule3CenterPolicy result mol 0).excluded = [] := by
  rw [centerPolicy_eq]

/-! ## The actual observer on the two source nodes

The two nodes are the real canonical nodes at which the units are read.  Their histories are the
ones built by `canonicalChildren` from the root `canonicalRoot 0 1`. -/

/-- The canonical source node for unit `2=3`. -/
def nodeA : CanonicalBranchNode :=
  { atom := 3, parent := 2, history := [3, 2, 1, 0],
    provenance := CanonicalNodeProvenance.realAtom }

/-- The canonical source node for unit `5=6`. -/
def nodeB : CanonicalBranchNode :=
  { atom := 6, parent := 5, history := [6, 5, 4, 3, 2, 1, 0],
    provenance := CanonicalNodeProvenance.realAtom }

/-- The first source node is a member of the actual canonical source walk. -/
theorem nodeA_mem_sourceNodes :
    nodeA ∈ rule3SourceNodes mol 0 (analysisFuel mol)
      [RawMolecule.canonicalRoot 0 1] := by decide

/-- The second source node is a member of the actual canonical source walk. -/
theorem nodeB_mem_sourceNodes :
    nodeB ∈ rule3SourceNodes mol 0 (analysisFuel mol)
      [RawMolecule.canonicalRoot 0 1] := by decide

/-- The observation record written for unit `2=3`, parameterised by its geometry. -/
def observationA (geometry : OfficialRule3Geometry) : CanonicalRule3Observation :=
  { unit := (2, 3), near := 2, far := 3, entry? := some 1, geometry := geometry }

/-- The observation record written for unit `5=6`, parameterised by its geometry. -/
def observationB (geometry : OfficialRule3Geometry) : CanonicalRule3Observation :=
  { unit := (5, 6), near := 5, far := 6, entry? := some 4, geometry := geometry }

/-- The actual observer preserves source `seqcis` on unit `2=3`. -/
theorem actual_observer_unitA :
    rule3BranchObserver result mol 0 (rule3CenterPolicy result mol 0) 1 nodeA =
      some (some (observationA OfficialRule3Geometry.seqcis)) := by
  rw [centerPolicy_eq]
  decide

/-- The actual observer preserves source `seqcis` on unit `5=6`. -/
theorem actual_observer_unitB :
    rule3BranchObserver result mol 0 (rule3CenterPolicy result mol 0) 1 nodeB =
      some (some (observationB OfficialRule3Geometry.seqcis)) := by
  rw [centerPolicy_eq]
  decide

/-- Extract the geometry field of an observation result. -/
def observerGeometry? (policy : Rule3CenterPolicy) (ligand : ℕ)
    (node : CanonicalBranchNode) : Option OfficialRule3Geometry :=
  (rule3BranchObserver result mol 0 policy ligand node).bind fun observed =>
    observed.map fun observation => observation.geometry

/-- Actual geometry observed for unit `2=3`. -/
theorem actual_observerGeometry_unitA :
    observerGeometry? (rule3CenterPolicy result mol 0) 1 nodeA =
      some OfficialRule3Geometry.seqcis := by
  simp [observerGeometry?, actual_observer_unitA, observationA]

/-- Actual geometry observed for unit `5=6`. -/
theorem actual_observerGeometry_unitB :
    observerGeometry? (rule3CenterPolicy result mol 0) 1 nodeB =
      some OfficialRule3Geometry.seqcis := by
  simp [observerGeometry?, actual_observer_unitB, observationB]

/-! ## The same intended reference, read spatially

The coordinates below place the two endpoints of each unit and the two CIP-senior substituents
selected above.  For unit `2=3` the reference positions are atom `1` (near) and atom `4` (far);
for unit `5=6` they are atom `4` (near) and atom `10` (far).  These are the same reference atoms
whose selection is proved in `unitA_senior_references` and `unitB_senior_references`.

`rule3GeometryOfSpatialReferences?` classifies the exact rational configuration.  The existing
`rule3GeometryOfSpatialReferences?_swap` theorem shows that reading the same physical unit from
the other endpoint, with the same two references exchanged accordingly, does not change the
geometry.  A bare descriptor flip without exchanging the references is therefore not a change of
reading direction. -/

/-- Rational point constructor. -/
def point (x y z : ℚ) : CartesianPoint3 :=
  { x := x, y := y, z := z }

/-- One partial coordinate map for the source atoms involved in the two alkene readings.
The shared atom `4` has one position in both readings.  This is a spatial realization of the
local references; it does not assert a full molecular conformation or a normalization theorem. -/
def sourceAtomPosition? : ℕ → Option CartesianPoint3
  | 1 => some (point 0 1 0)
  | 2 => some (point 0 0 0)
  | 3 => some (point 1 0 0)
  | 4 => some (point 1 1 0)
  | 5 => some (point 2 0 0)
  | 6 => some (point 3 0 0)
  | 10 => some (point 3 1 0)
  | _ => none

/-- Endpoint `2` of unit `2=3`. -/
def unitAEndpointNear : CartesianPoint3 := point 0 0 0

/-- Endpoint `3` of unit `2=3`. -/
def unitAEndpointFar : CartesianPoint3 := point 1 0 0

/-- Position of the near reference atom `1`. -/
def unitANearReference : CartesianPoint3 := point 0 1 0

/-- Position of the far reference atom `4`. -/
def unitAFarReference : CartesianPoint3 := point 1 1 0

/-- Endpoint `5` of unit `5=6`. -/
def unitBEndpointNear : CartesianPoint3 := point 2 0 0

/-- Endpoint `6` of unit `5=6`. -/
def unitBEndpointFar : CartesianPoint3 := point 3 0 0

/-- Position of the near reference atom `4`, shared with the first unit. -/
def unitBNearReference : CartesianPoint3 := unitAFarReference

/-- Position of the far reference atom `10`. -/
def unitBFarReference : CartesianPoint3 := point 3 1 0

/-- Both reference frames are projections of the same source-atom coordinate map. -/
theorem spatial_source_positions :
    sourceAtomPosition? unitA.near = some unitAEndpointNear ∧
      sourceAtomPosition? unitA.far = some unitAEndpointFar ∧
      sourceAtomPosition? unitANearReferenceAtom = some unitANearReference ∧
      sourceAtomPosition? unitAFarReferenceAtom = some unitAFarReference ∧
      sourceAtomPosition? unitB.near = some unitBEndpointNear ∧
      sourceAtomPosition? unitB.far = some unitBEndpointFar ∧
      sourceAtomPosition? unitBNearReferenceAtom = some unitBNearReference ∧
      sourceAtomPosition? unitBFarReferenceAtom = some unitBFarReference := by decide

/-- Exact spatial geometry of unit `2=3` with the CIP-senior references: `seqcis`. -/
theorem spatial_unitA :
    rule3GeometryOfSpatialReferences? unitAEndpointNear unitAEndpointFar
        unitANearReference unitAFarReference =
      some OfficialRule3Geometry.seqcis := by norm_num [rule3GeometryOfSpatialReferences?, CartesianPoint3.rule3Coplanarity,
    CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
    RationalVector3.cross, RationalVector3.dot, unitAEndpointNear,
    unitAEndpointFar, unitANearReference, unitAFarReference, point]

/-- Reversing the physical axis of unit `2=3` while exchanging its two senior references
preserves the geometry; this is the existing swap law instantiated on the two reference atoms. -/
theorem spatial_unitA_reverse_eq :
    rule3GeometryOfSpatialReferences? unitAEndpointFar unitAEndpointNear
        unitAFarReference unitANearReference =
      rule3GeometryOfSpatialReferences? unitAEndpointNear unitAEndpointFar
        unitANearReference unitAFarReference :=
  rule3GeometryOfSpatialReferences?_swap unitAEndpointNear unitAEndpointFar
    unitANearReference unitAFarReference

/-- The reverse reading is still `seqcis`. -/
theorem spatial_unitA_reverse :
    rule3GeometryOfSpatialReferences? unitAEndpointFar unitAEndpointNear
        unitAFarReference unitANearReference =
      some OfficialRule3Geometry.seqcis := by
  rw [spatial_unitA_reverse_eq]
  exact spatial_unitA

/-- Exact spatial geometry of unit `5=6` with the CIP-senior references: `seqcis`. -/
theorem spatial_unitB :
    rule3GeometryOfSpatialReferences? unitBEndpointNear unitBEndpointFar
        unitBNearReference unitBFarReference =
      some OfficialRule3Geometry.seqcis := by norm_num [rule3GeometryOfSpatialReferences?, CartesianPoint3.rule3Coplanarity,
    CartesianPoint3.rule3SideProduct, CartesianPoint3.displacement,
    RationalVector3.cross, RationalVector3.dot, unitBEndpointNear,
    unitBEndpointFar, unitBNearReference, unitBFarReference, unitAFarReference, point]

/-- Reversing the physical axis of unit `5=6` with exchanged references preserves the geometry. -/
theorem spatial_unitB_reverse_eq :
    rule3GeometryOfSpatialReferences? unitBEndpointFar unitBEndpointNear
        unitBFarReference unitBNearReference =
      rule3GeometryOfSpatialReferences? unitBEndpointNear unitBEndpointFar
        unitBNearReference unitBFarReference :=
  rule3GeometryOfSpatialReferences?_swap unitBEndpointNear unitBEndpointFar
    unitBNearReference unitBFarReference

/-- The reverse reading of unit `5=6` is still `seqcis`. -/
theorem spatial_unitB_reverse :
    rule3GeometryOfSpatialReferences? unitBEndpointFar unitBEndpointNear
        unitBFarReference unitBNearReference =
      some OfficialRule3Geometry.seqcis := by
  rw [spatial_unitB_reverse_eq]
  exact spatial_unitB

/-! ## Production geometry agrees with the source reader -/

/-- The first unit keeps its source geometry even though the ligand carries two double bonds. -/
theorem actual_geometry_matches_source_unitA :
    observerGeometry? (rule3CenterPolicy result mol 0) 1 nodeA =
      rule3CenterGeometry? result mol 0 true false unitA := by
  rw [actual_observerGeometry_unitA]
  exact absolute_unitA.symm

/-- The second unit also keeps its source geometry. -/
theorem actual_geometry_matches_source_unitB :
    observerGeometry? (rule3CenterPolicy result mol 0) 1 nodeB =
      rule3CenterGeometry? result mol 0 true false unitB := by
  rw [actual_observerGeometry_unitB]
  exact absolute_unitB.symm

assert_kernel_only actual_geometry_matches_source_unitA
assert_kernel_only actual_geometry_matches_source_unitB

assert_kernel_only mol_admissible
assert_kernel_only mol_stereochemicalAdmissible
assert_kernel_only mol_valenceOK
assert_kernel_only center_tetrahedral
assert_kernel_only center_not_cyclic
assert_kernel_only unitA_entry_is_senior
assert_kernel_only unitB_entry_is_senior
assert_kernel_only unitA_senior_references
assert_kernel_only unitB_senior_references
assert_kernel_only perceived_unitA_Z
assert_kernel_only perceived_unitB_Z
assert_kernel_only seniorSide_unitA
assert_kernel_only seniorSide_unitB
assert_kernel_only absolute_unitA
assert_kernel_only absolute_unitB
assert_kernel_only entryGeometry_unitA
assert_kernel_only entryGeometry_unitB
assert_kernel_only evidence_ligand1
assert_kernel_only centerPolicy_eq
assert_kernel_only centerPolicy_flipped
assert_kernel_only centerPolicy_cyclic
assert_kernel_only centerPolicy_excluded
assert_kernel_only nodeA_mem_sourceNodes
assert_kernel_only nodeB_mem_sourceNodes
assert_kernel_only actual_observer_unitA
assert_kernel_only actual_observer_unitB
assert_kernel_only actual_observerGeometry_unitA
assert_kernel_only actual_observerGeometry_unitB
assert_kernel_only spatial_source_positions
assert_kernel_only spatial_unitA
assert_kernel_only spatial_unitA_reverse_eq
assert_kernel_only spatial_unitA_reverse
assert_kernel_only spatial_unitB
assert_kernel_only spatial_unitB_reverse_eq
assert_kernel_only spatial_unitB_reverse

end Rule3PhysicalMultiplicityFidelity
end OneCenter
end TetraStereo
