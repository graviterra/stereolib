import TetraStereo.OneCenter.OfficialNoncenterDetectors
import TetraStereo.OneCenter.CIPAuthoritativeOccurrenceComparator
import TetraStereo.OneCenter.IR9PolyhedralSemantics
import TetraStereo.OneCenter.IR9FaceMonocappedOctahedron7ExecutableIndex
import TetraStereo.OneCenter.IR9SquareFaceMonocappedTrigonalPrism7ExecutableIndex
import TetraStereo.OneCenter.IR9CubeExecutableIndex
import TetraStereo.OneCenter.IR9SquareAntiprism8ExecutableIndex
import TetraStereo.OneCenter.IR9TrigonalDodecahedron8ExecutableIndex
import TetraStereo.OneCenter.IR9TransBicappedOctahedron8ExecutableIndex
import TetraStereo.OneCenter.IR9TriangularFaceBicappedTrigonalPrism8ExecutableIndex
import TetraStereo.OneCenter.IR9SquareFaceBicappedTrigonalPrism8ExecutableIndex
import TetraStereo.OneCenter.IR9SquareFaceTricappedTrigonalPrism9ExecutableIndex

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Geometry-annotated CIP analysis

A molecular graph cannot determine a conformer's axial, planar, or helical handedness by itself.
This module exposes the typed geometry-ingress path at the same public assignment surface as native
tetrahedral, alkene, cumulene, and extended-tetrahedral analysis.  Every referenced atom is checked
against the normalized molecule before an assignment is admitted.

These annotations are configuration observations, not priority assertions: downstream Rule 4/5
contexts still use the official descriptor environment.  Proving that an external coordinate or
drawing importer produced the observation correctly remains an explicit upstream obligation.
-/

/-! ## Raw handedness observations

The legacy indexed records below can carry a final descriptor supplied by a toolkit.  The
chemistry-facing observation API instead accepts only an orientation sense.  Lean constructs the
descriptor, and for an axis independently verifies both stated high/low ligand pairs with the
complete encoded CIP comparison. -/

structure IndexedAxialGeometryObservation where
  axisStart : ℕ
  axisEnd : ℕ
  startFirst : ℕ
  startSecond : ℕ
  endFirst : ℕ
  endSecond : ℕ
  sense : StereoSense
  deriving DecidableEq, Repr

structure IndexedPlanarGeometryObservation where
  planeAtoms : List ℕ
  pilotAtom : ℕ
  firstReference : ℕ
  secondReference : ℕ
  sense : StereoSense
  deriving DecidableEq, Repr

structure IndexedHelicalGeometryObservation where
  helixPath : List ℕ
  frontReference : ℕ
  backReference : ℕ
  sense : StereoSense
  deriving DecidableEq, Repr

/-- The two IR-9.3.5.3 molecular grouping bases.  Whole repeated ligand occurrences are derived
without additional input.  For symmetry-related fragments inside one ligand, an importer supplies
only the donor-atom subsets which constitute the fragments; production verifies the component
membership and a full ligand-component automorphism relating every represented fragment. -/
inductive IndexedPolyhedralPrimingObservation where
  | repeatedPolydentateLigands
  | symmetryRelatedCoordinatingFragments (fragmentDonors : List (List Nat))
  deriving DecidableEq, Repr

/-- A geometry importer supplies typed IR-9 geometry-recognition and spatial-role observations.  It
does not supply priority numbers or an untyped configuration-index list: positions are derived from
the geometry-specific `configurationPositions` constructor below. -/
structure IndexedPolyhedralGeometryObservation where
  center : ℕ
  geometry : PolyhedralGeometry
  /-- Source-level IR-9.3.2 observation from which the geometry label must follow.  Qualitative
  words such as "significantly" remain experimental evidence, exactly as in the source; production
  checks that the selected geometry is the consequence of this typed observation. -/
  recognition : RedBookIR9.GeometryRecognitionObservation
  ligands : List ℕ
  configurationPositions : RedBookIR9.ConfigurationPositionObservation
  absoluteOrientation : RedBookIR9.AbsoluteOrientationObservation
  priming : IndexedPolyhedralPrimingObservation := .repeatedPolydentateLigands
  deriving DecidableEq, Repr

/-- The production geometry label is accepted exactly when it is entailed by the typed IR-9.3.2
recognition observation. -/
def IndexedPolyhedralGeometryObservation.geometryRecognitionOK?
    (record : IndexedPolyhedralGeometryObservation) : Bool :=
  record.recognition.recognizedGeometry? ==
    some (BlueBookP93.geometryOfProduction record.geometry)

/-- Convert the independent orientation vocabulary back to the production descriptor vocabulary. -/
def PolyhedralRotationSense.ofIndependent :
    BlueBookP93.RotationSense → PolyhedralRotationSense
  | .clockwise => .clockwise
  | .counterclockwise => .counterclockwise

structure IndexedCIPGeometryObservations where
  axes : List IndexedAxialGeometryObservation := []
  planes : List IndexedPlanarGeometryObservation := []
  helices : List IndexedHelicalGeometryObservation := []
  polyhedra : List IndexedPolyhedralGeometryObservation := []
  deriving DecidableEq, Repr

/-- Descriptor state used only to rank geometry-unit reference ligands. -/
def ChemistryNormalizationResult.geometryPriorityState (result : ChemistryNormalizationResult) :
    RawMolecule × ℕ × RawDescriptorState :=
  let expanded := result.parsed.withExplicitHydrogens
  let fuel := analysisFuel expanded
  (expanded, fuel, discoverRawDescriptors result expanded fuel)

/-! ## Molecular derivation of repeated-polydentate-ligand groups -/

/-- Configuration label used when deciding whether two complete ligand components are of the same
kind.  Incidental discovery evidence is omitted, but uppercase/lowercase descriptor class and
descriptor sense are preserved. -/
def RawDescriptorState.ligandKindLabelAt?
    (state : RawDescriptorState) (atom : Nat) : Option (RS × Bool) :=
  (state.factAt? atom).map fun fact => (fact.descriptor, fact.uppercase)

/-- Normalized E/Z label of one bond, independent of endpoint order. -/
def ChemistryNormalizationResult.doubleBondStereoBetween?
    (result : ChemistryNormalizationResult) (left right : Nat) : Option DoubleBondStereo :=
  (result.stereobonds.doubleBondAssignments.find? fun assignment =>
    (assignment.1 == left && assignment.2.1 == right) ||
      (assignment.1 == right && assignment.2.1 == left)).map fun assignment => assignment.2.2

/-- Equality of finite atom sets represented as duplicate-free reachability lists. -/
def sameFiniteAtomSet (left right : List Nat) : Bool :=
  left.length == right.length && left.all right.contains && right.all left.contains

/-- The complete connected ligand component reached from one donor after deleting the coordination
center.  `atomCount + 1` is a complete bound for a finite simple molecular graph. -/
def RawMolecule.coordinationLigandComponent
    (mol : RawMolecule) (center donor : Nat) : List Nat :=
  mol.reachableAvoiding (mol.atomCount + 1) center [donor] [donor]

/-- Atom label relevant to chemical ligand-kind identity.  Raw `@`/`@@` parity is deliberately not
compared directly because it depends on written neighbor order; its normalized CIP descriptor in
`state` is compared instead. -/
def sameCoordinationLigandAtom
    (mol : RawMolecule) (state : RawDescriptorState) (left right : Nat) : Bool :=
  match mol.atomAt? left, mol.atomAt? right with
  | some leftSpec, some rightSpec =>
      leftSpec.element == rightSpec.element && leftSpec.isotope? == rightSpec.isotope? &&
        leftSpec.charge == rightSpec.charge && leftSpec.aromatic == rightSpec.aromatic &&
        leftSpec.explicitHydrogens? == rightSpec.explicitHydrogens? &&
        state.ligandKindLabelAt? left == state.ligandKindLabelAt? right
  | _, _ => false

/-- Validate one explicit bijection candidate between two center-deleted ligand components.
Besides atom labels and every induced bond/nonbond relation, this preserves donor attachment to the
coordination center and normalized E/Z labels.  Localized mancude placements are compared by their
constitutional resonance class rather than by an arbitrary Kekulé form. -/
def ChemistryNormalizationResult.coordinationComponentMappingOK?
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (source targetOrder : List Nat) : Bool :=
  let positions := List.range source.length
  let mancudeEdges := mol.localizedMancudeEdges
  source.length == targetOrder.length &&
    positions.all (fun position =>
      let left := source.getD position 0
      let right := targetOrder.getD position 0
      sameCoordinationLigandAtom mol state left right &&
        mol.constitutionBondClass mancudeEdges center left ==
          mol.constitutionBondClass mancudeEdges center right) &&
    positions.all (fun leftPosition => positions.all fun rightPosition =>
      let sourceLeft := source.getD leftPosition 0
      let sourceRight := source.getD rightPosition 0
      let targetLeft := targetOrder.getD leftPosition 0
      let targetRight := targetOrder.getD rightPosition 0
      mol.constitutionBondClass mancudeEdges sourceLeft sourceRight ==
          mol.constitutionBondClass mancudeEdges targetLeft targetRight &&
        result.doubleBondStereoBetween? sourceLeft sourceRight ==
          result.doubleBondStereoBetween? targetLeft targetRight)

/-- Complete finite ligand-kind isomorphism test.  Every permutation of the target component is
considered.  This factorial reference implementation is total on every finite molecule; a later
partition-refinement search may optimize the candidate generation without changing this checked
relation. -/
def ChemistryNormalizationResult.coordinationComponentsSameKind?
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (source target : List Nat) : Bool :=
  source.length == target.length &&
    target.permutations.any fun targetOrder =>
      result.coordinationComponentMappingOK? mol state center source targetOrder

/-- First donor position belonging to the same center-deleted ligand component. -/
def firstCoordinationComponentPosition?
    (components : List (List Nat)) (position : Nat) : Option Nat := do
  let component ← components[position]?
  (List.range components.length).find? fun other =>
    sameFiniteAtomSet component (components.getD other [])

/-- Source-defined repeated-ligand membership expected at one donor position.  A donor receives a
membership exactly when its component is polydentate and there is another, distinct polydentate
component of the same fully labeled ligand kind.  `family` identifies the ligand kind and `group`
the actual connected ligand occurrence; both use first donor positions only as opaque equality
labels. -/
def ChemistryNormalizationResult.expectedRepeatedLigandMembershipAt?
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (ligands : List Nat) (components : List (List Nat))
    (position : Nat) : Option RedBookIR9.PrimingMembership := do
  let component ← components[position]?
  let group ← firstCoordinationComponentPosition? components position
  let positions := List.range ligands.length
  let componentDonors := positions.filter fun other =>
    sameFiniteAtomSet component (components.getD other [])
  if componentDonors.length < 2 then none else
  let sameKindPositions := positions.filter fun other =>
    let otherComponent := components.getD other []
    let otherDonors := positions.filter fun candidate =>
      sameFiniteAtomSet otherComponent (components.getD candidate [])
    2 ≤ otherDonors.length &&
      result.coordinationComponentsSameKind? mol state center component otherComponent
  let occurrenceGroups := (sameKindPositions.filterMap fun other =>
    firstCoordinationComponentPosition? components other).eraseDups
  if occurrenceGroups.length < 2 then none else
  let family ← sameKindPositions.head?
  some { family := family, group := group }

/-- Candidate molecular priming frame for repeated polydentate ligands. -/
def ChemistryNormalizationResult.candidateRepeatedLigandPrimingMemberships
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (ligands : List Nat) : List (Option RedBookIR9.PrimingMembership) :=
  let components := ligands.map fun donor => mol.coordinationLigandComponent center donor
  (List.range ligands.length).map fun position =>
    result.expectedRepeatedLigandMembershipAt? mol state center ligands components position

/-- Validate the entire candidate against the molecular repeated-ligand relation.  Candidate
generation is not trusted by the descriptor path. -/
def ChemistryNormalizationResult.repeatedLigandPrimingMembershipsOK?
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (ligands : List Nat)
    (memberships : List (Option RedBookIR9.PrimingMembership)) : Bool :=
  let components := ligands.map fun donor => mol.coordinationLigandComponent center donor
  memberships.length == ligands.length &&
    (List.range ligands.length).all fun position =>
      RedBookIR9.finitePrimingMembershipAt memberships position ==
        result.expectedRepeatedLigandMembershipAt? mol state center ligands components position

/-- Derive, then validate, every repeated-polydentate-ligand family and occurrence group. -/
def ChemistryNormalizationResult.deriveRepeatedLigandPrimingMemberships?
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (ligands : List Nat) :
    Option (List (Option RedBookIR9.PrimingMembership)) :=
  let candidate := result.candidateRepeatedLigandPrimingMemberships mol state center ligands
  if !result.repeatedLigandPrimingMembershipsOK? mol state center ligands candidate then none
  else some candidate

/-! ### Symmetry-related coordinating fragments within one ligand -/

/-- Transport one atom through a component mapping represented positionally. -/
def mappedCoordinationComponentAtom?
    (source targetOrder : List Nat) (atom : Nat) : Option Nat := do
  let position ← RawMolecule.firstNatIndex? atom source
  targetOrder[position]?

/-- Two donor subsets of one ligand are symmetry-related exactly when some checked automorphism of
the complete labeled ligand component carries the first subset onto the second.  Exhaustive target
permutations make the test total for every finite component. -/
def ChemistryNormalizationResult.coordinatingFragmentsSymmetryRelated?
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (component sourceFragment targetFragment : List Nat) : Bool :=
  !sourceFragment.isEmpty && !targetFragment.isEmpty &&
    sourceFragment.eraseDups.length == sourceFragment.length &&
    targetFragment.eraseDups.length == targetFragment.length &&
    sourceFragment.all component.contains && targetFragment.all component.contains &&
    component.permutations.any fun targetOrder =>
      result.coordinationComponentMappingOK? mol state center component targetOrder &&
        match sourceFragment.mapM (mappedCoordinationComponentAtom? component targetOrder) with
        | none => false
        | some mapped => sameFiniteAtomSet mapped targetFragment

/-- A concrete checked component automorphism is a kernel-checkable witness that two coordinating
fragments are symmetry-related.  This theorem exposes the mathematical witness hidden behind the
exhaustive finite search, so downstream certificates need not reduce every other permutation. -/
theorem ChemistryNormalizationResult.coordinatingFragmentsSymmetryRelated_of_witness
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (component sourceFragment targetFragment targetOrder : List Nat)
    (sourceNonempty : (!sourceFragment.isEmpty) = true)
    (targetNonempty : (!targetFragment.isEmpty) = true)
    (sourceNodup : (sourceFragment.eraseDups.length == sourceFragment.length) = true)
    (targetNodup : (targetFragment.eraseDups.length == targetFragment.length) = true)
    (sourceSubset : sourceFragment.all component.contains = true)
    (targetSubset : targetFragment.all component.contains = true)
    (permutation : targetOrder ∈ component.permutations)
    (mapping : result.coordinationComponentMappingOK? mol state center component targetOrder = true)
    (mappedFragment :
      (match sourceFragment.mapM (mappedCoordinationComponentAtom? component targetOrder) with
       | none => false
       | some mapped => sameFiniteAtomSet mapped targetFragment) = true) :
    result.coordinatingFragmentsSymmetryRelated? mol state center component sourceFragment
        targetFragment = true := by
  unfold ChemistryNormalizationResult.coordinatingFragmentsSymmetryRelated?
  simp only [Bool.and_eq_true, List.any_eq_true]
  refine ⟨?_, ?_⟩
  · exact And.intro
      (And.intro
        (And.intro
          (And.intro
            (And.intro sourceNonempty targetNonempty)
            sourceNodup)
          targetNodup)
        sourceSubset)
      targetSubset
  · exact ⟨targetOrder, permutation, mapping, mappedFragment⟩

/-- First observed coordinating-fragment position containing a donor. -/
def firstCoordinatingFragmentPosition?
    (fragmentDonors : List (List Nat)) (donor : Nat) : Option Nat :=
  (List.range fragmentDonors.length).find? fun position =>
    (fragmentDonors.getD position []).contains donor

/-- A fragment observation is chemically admissible for the finite molecular frame when every
listed fragment is a nonempty duplicate-free donor subset of one polydentate ligand, every donor is
listed at most once, and every fragment has a distinct symmetry-related mate in that same ligand.
Donors outside the repeated fragment families may be omitted and remain unprimed. -/
def ChemistryNormalizationResult.coordinatingFragmentObservationOK?
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (ligands : List Nat) (fragmentDonors : List (List Nat)) : Bool :=
  let positions := List.range ligands.length
  let components := ligands.map fun donor => mol.coordinationLigandComponent center donor
  !fragmentDonors.isEmpty &&
    fragmentDonors.all (fun fragment =>
      !fragment.isEmpty && fragment.eraseDups.length == fragment.length &&
        fragment.all ligands.contains &&
        match fragment.head? with
        | none => false
        | some firstDonor =>
            match RawMolecule.firstNatIndex? firstDonor ligands with
            | none => false
            | some firstPosition =>
                let component := components.getD firstPosition []
                let componentDonors := positions.filter fun position =>
                  component.contains (ligands.getD position 0)
                2 ≤ componentDonors.length && fragment.all component.contains &&
                  fragmentDonors.any fun other =>
                    !sameFiniteAtomSet fragment other &&
                      other.all component.contains &&
                      result.coordinatingFragmentsSymmetryRelated? mol state center component
                        fragment other) &&
    ligands.all (fun donor =>
      (fragmentDonors.filter fun fragment => fragment.contains donor).length ≤ 1)

/-- Expected family/group membership for one donor under a checked coordinating-fragment
observation.  Family identity is the first symmetry-related fragment; group identity is the actual
fragment occurrence. -/
def ChemistryNormalizationResult.expectedCoordinatingFragmentMembershipAt?
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (ligands : List Nat) (fragmentDonors : List (List Nat))
    (position : Nat) : Option RedBookIR9.PrimingMembership := do
  let donor ← ligands[position]?
  let fragmentPosition ← firstCoordinatingFragmentPosition? fragmentDonors donor
  let fragment ← fragmentDonors[fragmentPosition]?
  let component := mol.coordinationLigandComponent center donor
  let sameKindFragments := (List.range fragmentDonors.length).filter fun other =>
    result.coordinatingFragmentsSymmetryRelated? mol state center component fragment
      (fragmentDonors.getD other [])
  if sameKindFragments.length < 2 then none else
  let family ← sameKindFragments.head?
  some { family := family, group := fragmentPosition }

def ChemistryNormalizationResult.candidateCoordinatingFragmentPrimingMemberships
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (ligands : List Nat) (fragmentDonors : List (List Nat)) :
    List (Option RedBookIR9.PrimingMembership) :=
  (List.range ligands.length).map fun position =>
    result.expectedCoordinatingFragmentMembershipAt? mol state center ligands fragmentDonors
      position

/-- Full molecular validator for a derived within-ligand fragment frame. -/
def ChemistryNormalizationResult.coordinatingFragmentPrimingMembershipsOK?
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (ligands : List Nat) (fragmentDonors : List (List Nat))
    (memberships : List (Option RedBookIR9.PrimingMembership)) : Bool :=
  result.coordinatingFragmentObservationOK? mol state center ligands fragmentDonors &&
    memberships.length == ligands.length &&
    (List.range ligands.length).all fun position =>
      RedBookIR9.finitePrimingMembershipAt memberships position ==
        result.expectedCoordinatingFragmentMembershipAt? mol state center ligands fragmentDonors
          position

def ChemistryNormalizationResult.deriveCoordinatingFragmentPrimingMemberships?
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (ligands : List Nat) (fragmentDonors : List (List Nat)) :
    Option (List (Option RedBookIR9.PrimingMembership)) :=
  let candidate := result.candidateCoordinatingFragmentPrimingMemberships
    mol state center ligands fragmentDonors
  if !result.coordinatingFragmentPrimingMembershipsOK?
      mol state center ligands fragmentDonors candidate then none
  else some candidate

/-- Convert an observed axial sense after independently deriving the high and low ligand at each
end.  The observation supplies two unordered candidates per end; their input order is irrelevant. -/
def ChemistryNormalizationResult.axialGeometryObservationAssignment?
    (result : ChemistryNormalizationResult) (record : IndexedAxialGeometryObservation) :
    Option StereoAssignment := do
  let _ ← result.atomFin? record.axisStart
  let _ ← result.atomFin? record.axisEnd
  let _ ← result.atomFin? record.startFirst
  let _ ← result.atomFin? record.startSecond
  let _ ← result.atomFin? record.endFirst
  let _ ← result.atomFin? record.endSecond
  if record.axisStart == record.axisEnd || record.startFirst == record.startSecond ||
      record.endFirst == record.endSecond then none else
  let context := result.geometryPriorityState
  let mol := context.1
  let fuel := context.2.1
  let state := context.2.2
  if !(mol.writtenNeighbors record.axisStart).contains record.startFirst ||
      !(mol.writtenNeighbors record.axisStart).contains record.startSecond ||
      !(mol.writtenNeighbors record.axisEnd).contains record.endFirst ||
      !(mol.writtenNeighbors record.axisEnd).contains record.endSecond then none else
  let startDecision := compareBranchesThroughOfficialContext? result mol state fuel record.axisStart
    record.startFirst record.startSecond
  let endDecision := compareBranchesThroughOfficialContext? result mol state fuel record.axisEnd
    record.endFirst record.endSecond
  let strict := fun decision => decision == some Ordering.gt || decision == some Ordering.lt
  if !strict startDecision || !strict endDecision then none else
  let descriptor := AxialDescriptor.ofSense record.sense
  some { unit := StereoUnit.axis record.axisStart record.axisEnd,
         outcome := StereoOutcome.axial descriptor }

/-- A planar handedness observation is converted only after atom-range and nondegenerate frame
checks.  Its coordinate/drawing sense remains the explicit upstream geometry obligation. -/
def ChemistryNormalizationResult.planarGeometryObservationAssignment?
    (result : ChemistryNormalizationResult) (record : IndexedPlanarGeometryObservation) :
    Option StereoAssignment := do
  let _ ← result.atomFinList? record.planeAtoms
  let _ ← result.atomFin? record.pilotAtom
  let _ ← result.atomFin? record.firstReference
  let _ ← result.atomFin? record.secondReference
  if record.planeAtoms.length < 3 || record.planeAtoms.eraseDups.length != record.planeAtoms.length ||
      record.firstReference == record.secondReference then none else
  some { unit := StereoUnit.plane record.planeAtoms,
         outcome := StereoOutcome.planar (PlanarDescriptor.ofSense record.sense) }

/-- A helical handedness observation is converted only for a non-self-intersecting indexed path
with two distinct terminal references. -/
def ChemistryNormalizationResult.helicalGeometryObservationAssignment?
    (result : ChemistryNormalizationResult) (record : IndexedHelicalGeometryObservation) :
    Option StereoAssignment := do
  let _ ← result.atomFinList? record.helixPath
  let _ ← result.atomFin? record.frontReference
  let _ ← result.atomFin? record.backReference
  if record.helixPath.length < 3 || record.helixPath.eraseDups.length != record.helixPath.length ||
      record.frontReference == record.backReference then none else
  some { unit := StereoUnit.helix record.helixPath,
         outcome := StereoOutcome.helical (HelicalDescriptor.ofSense record.sense) }

/-! ## P-93 polyhedral geometry observations -/

/-- Number of distinguished positions consumed by each complete configuration-index constructor.
The seven-position OCF-7 and TPRS-7 cases and the higher-coordinate 8/9-position cases use their
proved symmetry-complete mathematical words, not unpublished short source recipes. -/
def PolyhedralGeometry.configurationIndexArity? : PolyhedralGeometry → Option ℕ
  | .linear | .angular | .trigonalPlanar | .trigonalPyramid | .tetrahedron => some 0
  | .tShape | .squarePlanar | .squarePyramid4 => some 1
  | .seeSaw | .trigonalBipyramid | .squarePyramid | .octahedron => some 2
  | .trigonalPrism => some 6
  | .faceMonocappedOctahedron | .squareFaceMonocappedTrigonalPrism
  | .pentagonalBipyramid => some 7
  | .hexagonalBipyramid => some 8
  | .cube | .squareAntiprism | .dodecahedron
  | .transBicappedOctahedron | .triangularFaceBicappedTrigonalPrism
  | .squareFaceBicappedTrigonalPrism => some 8
  | .heptagonalBipyramid | .squareFaceTricappedTrigonalPrism => some 9

/-- Derive strict CIP priority numbers for a complete center-local ligand frame.  This retained
specializer is useful to callers that require pairwise-distinct priorities; the public polyhedral
assignment below uses `polyhedralPriorityNumbers?`, which also supports equal base tiers and
separately observed IR-9 priming groups. -/
def ChemistryNormalizationResult.strictPolyhedralPriorityNumbers?
    (result : ChemistryNormalizationResult) (center : ℕ) (geometry : PolyhedralGeometry)
    (ligands : List ℕ) : Option (List PolyhedralPriorityNumber) := do
  let context := result.geometryPriorityState
  let mol := context.1
  let fuel := context.2.1
  let state := context.2.2
  let _ ← mol.atomAt? center
  let _ ← ligands.mapM mol.atomAt?
  if ligands.length != geometry.coordinationNumber ||
      ligands.eraseDups.length != ligands.length then none else
  let neighbors := (mol.writtenNeighbors center).eraseDups
  if neighbors.length != ligands.length ||
      !(ligands.all fun ligand => neighbors.contains ligand) then none else
  let positions := List.range ligands.length
  let atomOf := fun position => ligands.getD position 0
  let compareAt := fun left right =>
    compareBranchesThroughOfficialContext? result mol state fuel center
      (atomOf left) (atomOf right)
  let sorted := sortDescBy (fun left right => compareAt left right != some Ordering.lt) positions
  let strict := (List.range (sorted.length - 1)).all fun index =>
    match sorted[index]?, sorted[index + 1]? with
    | some left, some right => compareAt left right == some Ordering.gt
    | _, _ => false
  if !strict then none else
  positions.mapM fun position => do
    let ranked ← sorted.zipIdx.find? fun entry => entry.1 == position
    some { number := ranked.2 + 1 }

/-- State for assigning dense IR-9 priority numbers to a comparator-sorted ligand list. -/
structure PolyhedralDenseRankState where
  previous? : Option ℕ := none
  currentRank : ℕ := 0
  assignments : List (ℕ × ℕ) := []

/-- Assign equal positions the same number and increment only at a strict priority boundary. -/
def densePolyhedralRanks
    (compareAt : ℕ → ℕ → Option Ordering) (sorted : List ℕ) : List (ℕ × ℕ) :=
  (sorted.foldl (fun (state : PolyhedralDenseRankState) position =>
    let rank := match state.previous? with
      | none => 1
      | some previous =>
          if compareAt previous position == some Ordering.eq
          then state.currentRank else state.currentRank + 1
    { previous? := some position
      currentRank := rank
      assignments := (position, rank) :: state.assignments })
    ({} : PolyhedralDenseRankState)).assignments

/-- Executable interpretation of one resolved comparison against two proposed base priority
numbers. -/
def priorityDecisionAgreesNumbering?
    (decision : Option Ordering) (leftNumber rightNumber : Nat) : Bool :=
  match decision with
  | some .gt => leftNumber < rightNumber
  | some .eq => leftNumber == rightNumber
  | some .lt => leftNumber > rightNumber
  | none => false

/-- Check every IR-9.3.5.2 obligation on a proposed finite donor numbering.  In addition to all
pairwise CIP decisions, this checks positivity, the number-one condition for every maximal donor,
and absence of skipped tier numbers. -/
def densePolyhedralPriorityNumberingOK?
    (count : Nat) (compareAt : Nat → Nat → Option Ordering) (numbers : List Nat) : Bool :=
  let positions := List.range count
  numbers.length == count &&
    positions.all (fun position => 0 < numbers.getD position 0) &&
    positions.all (fun left => positions.all fun right =>
      priorityDecisionAgreesNumbering? (compareAt left right)
        (numbers.getD left 0) (numbers.getD right 0)) &&
    positions.all (fun position =>
      if positions.all (fun other => compareAt other position != some Ordering.gt)
      then numbers.getD position 0 == 1 else true) &&
    positions.all (fun position =>
      (List.range (numbers.getD position 0 - 1)).all fun offset =>
        positions.any fun higher => numbers.getD higher 0 == offset + 1)

/-- Produce the insertion-sort candidate before any normative validation. -/
def candidateDensePolyhedralBasePriorityNumbers?
    (count : Nat) (compareAt : Nat → Nat → Option Ordering) : Option (List Nat) := do
  let positions := List.range count
  let sorted := sortDescBy (fun left right => compareAt left right != some Ordering.lt) positions
  let ranked := densePolyhedralRanks compareAt sorted
  positions.mapM fun position => do
    let assignment ← ranked.find? fun entry => entry.1 == position
    some assignment.2

/-- Pure finite derivation of dense IR-9.3.5.2 base numbers.  The insertion-sort candidate is not
trusted: it is returned only after `densePolyhedralPriorityNumberingOK?` validates the complete
relational specification. -/
def deriveDensePolyhedralBasePriorityNumbers?
    (count : Nat) (compareAt : Nat → Nat → Option Ordering) : Option (List Nat) := do
  let baseNumbers ← candidateDensePolyhedralBasePriorityNumbers? count compareAt
  if !densePolyhedralPriorityNumberingOK? count compareAt baseNumbers then none else
  some baseNumbers

/-- Expand the convenient empty observation to the complete finite no-priming frame. -/
def effectivePolyhedralPrimingMemberships (donorCount : Nat)
    (memberships : List (Option RedBookIR9.PrimingMembership)) :
    List (Option RedBookIR9.PrimingMembership) :=
  if memberships.isEmpty then List.replicate donorCount none else memberships

/-- Candidate dense prime counts, independently restarting at zero for each represented family.
Family and occurrence-group labels are used only for equality; first occurrence chooses the
source-permitted arbitrary unprimed group. -/
def candidateCanonicalPolyhedralPrimeCounts?
    (donorCount : Nat) (memberships : List (Option RedBookIR9.PrimingMembership)) :
    Option (List Nat) :=
  (List.range donorCount).mapM fun position => do
    match RedBookIR9.finitePrimingMembershipAt memberships position with
    | none => some 0
    | some member =>
        let familyGroups := (memberships.filterMap fun candidate =>
          match candidate with
          | none => none
          | some candidateMember =>
              if candidateMember.family == member.family then some candidateMember.group else none
          ).eraseDups
        let ranked ← familyGroups.zipIdx.find? fun entry => entry.1 == member.group
        some ranked.2

/-- Check the complete independently transcribed finite IR-9.3.5.3 family assignment. -/
def familyPolyhedralPrimeCountsOK?
    (donorCount : Nat) (memberships : List (Option RedBookIR9.PrimingMembership))
    (primeCounts : List Nat) : Bool :=
  RedBookIR9.finitePrimingAssignmentOK donorCount memberships primeCounts

/-- Canonicalize IR-9.3.5.3 family/group memberships to dense prime counts.  The candidate
algorithm is not trusted: it is returned only after the complete independent family-local
relation validates it. -/
def canonicalPolyhedralPrimeCounts? (donorCount : Nat)
    (memberships : List (Option RedBookIR9.PrimingMembership)) : Option (List Nat) := do
  let effective := effectivePolyhedralPrimingMemberships donorCount memberships
  let primeCounts ← candidateCanonicalPolyhedralPrimeCounts? donorCount effective
  if !familyPolyhedralPrimeCountsOK? donorCount effective primeCounts then none else
  some primeCounts

/-- Validate a complete center-local donor frame and expose its internally derived CIP comparison.
The returned function compares ligand-list positions; neither priority numbers nor ordering are
accepted from the geometry importer. -/
def ChemistryNormalizationResult.polyhedralPriorityComparisonFrame?
    (result : ChemistryNormalizationResult) (center : ℕ) (geometry : PolyhedralGeometry)
    (ligands : List ℕ) : Option (Nat → Nat → Option Ordering) := do
  let context := result.geometryPriorityState
  let mol := context.1
  let fuel := context.2.1
  let state := context.2.2
  let _ ← mol.atomAt? center
  let _ ← ligands.mapM mol.atomAt?
  if ligands.length != geometry.coordinationNumber ||
      ligands.eraseDups.length != ligands.length then none else
  let neighbors := (mol.writtenNeighbors center).eraseDups
  if neighbors.length != ligands.length ||
      !(ligands.all fun ligand => neighbors.contains ligand) then none else
  let atomOf := fun position => ligands.getD position 0
  some fun left right =>
    compareBranchesThroughOfficialContext? result mol state fuel center
      (atomOf left) (atomOf right)

/-- Derive dense IR-9.3.5.2 base priority numbers, including equal-priority ligand tiers, then add
IR-9.3.5.3 primes from audited grouping observations.  Every pairwise CIP decision must resolve,
and the final dense ranking is checked back against every ordered pair before it is admitted. -/
def ChemistryNormalizationResult.polyhedralPriorityNumbers?
    (result : ChemistryNormalizationResult) (center : ℕ) (geometry : PolyhedralGeometry)
    (ligands : List ℕ)
    (primingMemberships : List (Option RedBookIR9.PrimingMembership)) :
    Option (List PolyhedralPriorityNumber) := do
  let compareAt ← result.polyhedralPriorityComparisonFrame? center geometry ligands
  let baseNumbers ← deriveDensePolyhedralBasePriorityNumbers? ligands.length compareAt
  let primeCounts ← canonicalPolyhedralPrimeCounts? ligands.length primingMemberships
  baseNumbers.zipWithM (fun number primes =>
    some { number := number, primes := primes }) primeCounts

/-- Safe molecular donor-priority ingress.  Repeated polydentate ligand families and occurrences
are derived from the normalized molecular graph; a geometry observation cannot assert its own
prime labels.  The within-one-ligand coordinating-fragment case uses the separate checked ingress
below because connectivity alone does not define fragment boundaries. -/
def ChemistryNormalizationResult.molecularPolyhedralPriorityNumbers?
    (result : ChemistryNormalizationResult) (center : Nat) (geometry : PolyhedralGeometry)
    (ligands : List Nat) : Option (List PolyhedralPriorityNumber) := do
  let context := result.geometryPriorityState
  let mol := context.1
  let state := context.2.2
  let memberships ← result.deriveRepeatedLigandPrimingMemberships? mol state center ligands
  result.polyhedralPriorityNumbers? center geometry ligands memberships

/-- Safe priority ingress selected by the two source-defined IR-9.3.5.3 grouping bases. -/
def ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?
    (result : ChemistryNormalizationResult) (center : Nat) (geometry : PolyhedralGeometry)
    (ligands : List Nat) (priming : IndexedPolyhedralPrimingObservation) :
    Option (List PolyhedralPriorityNumber) :=
  match priming with
  | .repeatedPolydentateLigands =>
      result.molecularPolyhedralPriorityNumbers? center geometry ligands
  | .symmetryRelatedCoordinatingFragments fragmentDonors => do
      let context := result.geometryPriorityState
      let mol := context.1
      let state := context.2.2
      let memberships ← result.deriveCoordinatingFragmentPrimingMemberships?
        mol state center ligands fragmentDonors
      result.polyhedralPriorityNumbers? center geometry ligands memberships

/-! ## Symmetry-complete seven-coordinate relative indices -/

namespace SevenCoordinateMathematicalIndex

abbrev OCF7Position :=
  RedBookIR9.FaceMonocappedOctahedron7SourceIndexCompleteness.Position

abbrev TPRS7Position :=
  RedBookIR9.SquareFaceMonocappedTrigonalPrism7FiniteSymmetry.Position

/-- Decode the lexicographic internal digit without losing its IR-9 number or prime count. -/
def digitToProduction
    (digit : RedBookIR9.FiniteSymmetry.CanonicalPriorityDigit) :
    PolyhedralPriorityNumber :=
  { number := (ofLex digit).1, primes := (ofLex digit).2 }

/-- Typed OCF-7 placement in cap, capped-face, opposite-face order. -/
def ocf7Placement (cap capped0 capped1 capped2 opposite0 opposite1 opposite2 :
    PolyhedralPriorityNumber) : OCF7Position → PolyhedralPriorityNumber
  | .cap => cap
  | .cappedFace corner => ![capped0, capped1, capped2] corner
  | .oppositeFace corner => ![opposite0, opposite1, opposite2] corner

/-- Typed TPRS-7 placement in cap, first triangular face, second triangular face order. -/
def tprs7Placement (cap first0 first1 first2 second0 second1 second2 :
    PolyhedralPriorityNumber) : TPRS7Position → PolyhedralPriorityNumber
  | .cap => cap
  | .prismVertex face corner =>
      ![![first0, first1, first2], ![second0, second1, second2]] face corner

end SevenCoordinateMathematicalIndex

/-- Complete executable OCF-7 relative word.  This is the proved finite-symmetry completion of
IR-9.3.3.2, not a geometry-specific short digit recipe. -/
def ocf7MathematicalConfigurationIndex
    (cap capped0 capped1 capped2 opposite0 opposite1 opposite2 :
      PolyhedralPriorityNumber) : List PolyhedralPriorityNumber :=
  (RedBookIR9.FaceMonocappedOctahedron7SourceIndexCompleteness.executableFaceMonocappedOctahedronConfigurationIndex
      (SevenCoordinateMathematicalIndex.ocf7Placement cap capped0 capped1 capped2
        opposite0 opposite1 opposite2)).map
    SevenCoordinateMathematicalIndex.digitToProduction

/-- Complete executable TPRS-7 relative word.  This is the proved finite-symmetry completion of
IR-9.3.3.2, not a geometry-specific short digit recipe. -/
def tprs7MathematicalConfigurationIndex
    (cap first0 first1 first2 second0 second1 second2 :
      PolyhedralPriorityNumber) : List PolyhedralPriorityNumber :=
  (RedBookIR9.SquareFaceMonocappedTrigonalPrism7SourceIndexCompleteness.executableSquareFaceMonocappedTrigonalPrismConfigurationIndex
      (SevenCoordinateMathematicalIndex.tprs7Placement cap first0 first1 first2
        second0 second1 second2)).map
    SevenCoordinateMathematicalIndex.digitToProduction

/-- Complete executable CU-8 relative word over all 48 ideal-cube frames.  It is the mathematical
completion of IR-9.3.3.2, not an unpublished short source recipe. -/
def cubeMathematicalConfigurationIndex
    (v000 v001 v010 v011 v100 v101 v110 v111 : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber :=
  (RedBookIR9.CubeSourceIndexCompleteness.executableCubeConfigurationIndex
      (RedBookIR9.CubeSourceIndexCompleteness.placementOfEntries
        v000 v001 v010 v011 v100 v101 v110 v111)).map
    SevenCoordinateMathematicalIndex.digitToProduction

/-- Complete executable SAPR-8 relative word over all sixteen ideal square-antiprism frames.  It
is the mathematical completion of IR-9.3.3.2, not an unpublished short source recipe. -/
def squareAntiprismMathematicalConfigurationIndex
    (v0 v1 v2 v3 v4 v5 v6 v7 : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber :=
  (RedBookIR9.SquareAntiprism8SourceIndexCompleteness.executableSquareAntiprismConfigurationIndex
      (RedBookIR9.SquareAntiprism8SourceIndexCompleteness.placementOfEntries
        v0 v1 v2 v3 v4 v5 v6 v7)).map
    SevenCoordinateMathematicalIndex.digitToProduction

/-- Complete executable DD-8 relative word over the eight diagonal `D2d` frames, preserving the
two four-site A/B families. -/
def dodecahedronMathematicalConfigurationIndex
    (a0 a1 a2 a3 b0 b1 b2 b3 : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber :=
  (RedBookIR9.TrigonalDodecahedron8SourceIndexCompleteness.executableDodecahedronConfigurationIndex
      (RedBookIR9.TrigonalDodecahedron8SourceIndexCompleteness.placementOfEntries
        a0 a1 a2 a3 b0 b1 b2 b3)).map
    SevenCoordinateMathematicalIndex.digitToProduction

/-- Complete executable OCT-8 relative word over the twelve cap-side/pair frames. -/
def transBicappedOctahedronMathematicalConfigurationIndex
    (cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2 : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber :=
  (RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness.executableTransBicappedOctahedronConfigurationIndex
      (RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness.placementOfEntries
        cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2)).map
    SevenCoordinateMathematicalIndex.digitToProduction

/-- Complete executable TPRT-8 relative word over the twelve face/corner frames.  The coordinate
action is shared with OCT-8, while this constructor retains TPRT-specific incidence semantics. -/
def triangularFaceBicappedTrigonalPrismMathematicalConfigurationIndex
    (cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber :=
  (RedBookIR9.TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness.executableTriangularFaceBicappedTrigonalPrismConfigurationIndex
      (RedBookIR9.TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness.placementOfEntries
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2)).map
    SevenCoordinateMathematicalIndex.digitToProduction

/-- Complete executable TPRS-8 relative word over its four triangular-face/selected-face
frames. -/
def squareFaceBicappedTrigonalPrismMathematicalConfigurationIndex
    (cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber :=
  (RedBookIR9.SquareFaceBicappedTrigonalPrism8SourceIndexCompleteness.executableSquareFaceBicappedTrigonalPrismConfigurationIndex
      (RedBookIR9.SquareFaceBicappedTrigonalPrism8SourceIndexCompleteness.placementOfEntries
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2)).map
    SevenCoordinateMathematicalIndex.digitToProduction

/-- Complete executable TPRS-9 relative word over its twelve triangular-face/corner frames. -/
def squareFaceTricappedTrigonalPrismMathematicalConfigurationIndex
    (cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : PolyhedralPriorityNumber) :
    List PolyhedralPriorityNumber :=
  (RedBookIR9.SquareFaceTricappedTrigonalPrism9SourceIndexCompleteness.executableSquareFaceTricappedTrigonalPrismConfigurationIndex
      (RedBookIR9.SquareFaceTricappedTrigonalPrism9SourceIndexCompleteness.placementOfEntries
        cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2)).map
    SevenCoordinateMathematicalIndex.digitToProduction

/-- Construct a geometry-specific P-93 configuration index from the priority numbers occupying
the already validated distinguished positions.  Factoring this pure router from position lookup
makes its chemical rule surface independently auditable. -/
def polyhedralConfigurationIndexOfEntries? (geometry : PolyhedralGeometry)
    (entries : List PolyhedralPriorityNumber) :
    Option (List (List PolyhedralPriorityNumber)) :=
  match geometry, entries with
  | .linear, [] | .angular, [] | .trigonalPlanar, []
  | .trigonalPyramid, [] | .tetrahedron, [] => some []
  | .tShape, [stem] => some [tShapeConfigurationIndex stem]
  | .squarePlanar, [transToOne] => some [squarePlanarConfigurationIndex transToOne]
  | .squarePyramid4, [transToSenior] =>
      some [squarePyramid4ConfigurationIndex transToSenior]
  | .seeSaw, [first, second] => some [seeSawConfigurationIndex first second]
  | .trigonalBipyramid, [first, second] =>
      some [trigonalBipyramidConfigurationIndex first second]
  | .squarePyramid, [apical, transToSeniorBase] =>
      some [squarePyramidConfigurationIndex apical transToSeniorBase]
  | .octahedron, [transToOne, transToSeniorPlane] =>
      some [octahedronConfigurationIndex transToOne transToSeniorPlane]
  | .trigonalPrism, [first0, first1, first2, second0, second1, second2] =>
      some [trigonalPrismConfigurationIndex
        [first0, first1, first2] [second0, second1, second2]]
  | .faceMonocappedOctahedron,
      [cap, capped0, capped1, capped2, opposite0, opposite1, opposite2] =>
      some [ocf7MathematicalConfigurationIndex cap capped0 capped1 capped2
        opposite0 opposite1 opposite2]
  | .squareFaceMonocappedTrigonalPrism,
      [cap, first0, first1, first2, second0, second1, second2] =>
      some [tprs7MathematicalConfigurationIndex cap first0 first1 first2
        second0 second1 second2]
  | .cube, [v000, v001, v010, v011, v100, v101, v110, v111] =>
      some [cubeMathematicalConfigurationIndex
        v000 v001 v010 v011 v100 v101 v110 v111]
  | .squareAntiprism, [v0, v1, v2, v3, v4, v5, v6, v7] =>
      some [squareAntiprismMathematicalConfigurationIndex
        v0 v1 v2 v3 v4 v5 v6 v7]
  | .dodecahedron, [a0, a1, a2, a3, b0, b1, b2, b3] =>
      some [dodecahedronMathematicalConfigurationIndex
        a0 a1 a2 a3 b0 b1 b2 b3]
  | .transBicappedOctahedron, [cap0, cap1, s0p0, s0p1, s0p2, s1p0, s1p1, s1p2] =>
      some [transBicappedOctahedronMathematicalConfigurationIndex
        cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2]
  | .triangularFaceBicappedTrigonalPrism,
      [cap0, cap1, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2] =>
      some [triangularFaceBicappedTrigonalPrismMathematicalConfigurationIndex
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2]
  | .squareFaceBicappedTrigonalPrism,
      [cap0, cap1, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2] =>
      some [squareFaceBicappedTrigonalPrismMathematicalConfigurationIndex
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2]
  | .squareFaceTricappedTrigonalPrism,
      [cap0, cap1, cap2, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2] =>
      some [squareFaceTricappedTrigonalPrismMathematicalConfigurationIndex
        cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2]
  | .pentagonalBipyramid, firstAxial :: secondAxial :: perpendicularPlane =>
      some (bipyramidalConfigurationIndex firstAxial secondAxial perpendicularPlane)
  | .hexagonalBipyramid, firstAxial :: secondAxial :: perpendicularPlane =>
      some (bipyramidalConfigurationIndex firstAxial secondAxial perpendicularPlane)
  | .heptagonalBipyramid, firstAxial :: secondAxial :: perpendicularPlane =>
      some (bipyramidalConfigurationIndex firstAxial secondAxial perpendicularPlane)
  | _, _ => none

/-- Construct the geometry-specific P-93 configuration index from internally derived priorities. -/
def polyhedralConfigurationIndex? (geometry : PolyhedralGeometry)
    (priorities : List PolyhedralPriorityNumber) (positions : List ℕ) :
    Option (List (List PolyhedralPriorityNumber)) := do
  let arity ← geometry.configurationIndexArity?
  if positions.length != arity ||
      positions.eraseDups.length != positions.length then none else
  let entries ← positions.mapM fun position => priorities[position]?
  polyhedralConfigurationIndexOfEntries? geometry entries

/-- Public OCF-7 routing computes the complete mathematical word on a concrete seven-position
frame. -/
@[simp] theorem ocf7ConfigurationIndex?_exact
    (cap capped0 capped1 capped2 opposite0 opposite1 opposite2 :
      PolyhedralPriorityNumber) :
    polyhedralConfigurationIndex? .faceMonocappedOctahedron
        [cap, capped0, capped1, capped2, opposite0, opposite1, opposite2]
        [0, 1, 2, 3, 4, 5, 6] =
      some [ocf7MathematicalConfigurationIndex cap capped0 capped1 capped2
        opposite0 opposite1 opposite2] := by
  have distinct : [0, 1, 2, 3, 4, 5, 6].eraseDups.length = 7 := by decide
  simp [polyhedralConfigurationIndex?, polyhedralConfigurationIndexOfEntries?,
    PolyhedralGeometry.configurationIndexArity?, distinct]

/-- Public TPRS-7 routing computes the complete mathematical word on a concrete seven-position
frame. -/
@[simp] theorem tprs7ConfigurationIndex?_exact
    (cap first0 first1 first2 second0 second1 second2 :
      PolyhedralPriorityNumber) :
    polyhedralConfigurationIndex? .squareFaceMonocappedTrigonalPrism
        [cap, first0, first1, first2, second0, second1, second2]
        [0, 1, 2, 3, 4, 5, 6] =
      some [tprs7MathematicalConfigurationIndex cap first0 first1 first2
        second0 second1 second2] := by
  have distinct : [0, 1, 2, 3, 4, 5, 6].eraseDups.length = 7 := by decide
  simp [polyhedralConfigurationIndex?, polyhedralConfigurationIndexOfEntries?,
    PolyhedralGeometry.configurationIndexArity?, distinct]

/-- Public CU-8 routing computes the complete mathematical word on one concrete binary-coordinate
frame. -/
@[simp] theorem cubeConfigurationIndex?_exact
    (v000 v001 v010 v011 v100 v101 v110 v111 : PolyhedralPriorityNumber) :
    polyhedralConfigurationIndex? .cube
        [v000, v001, v010, v011, v100, v101, v110, v111]
        [0, 1, 2, 3, 4, 5, 6, 7] =
      some [cubeMathematicalConfigurationIndex
        v000 v001 v010 v011 v100 v101 v110 v111] := by
  have distinct : [0, 1, 2, 3, 4, 5, 6, 7].eraseDups.length = 8 := by decide
  simp [polyhedralConfigurationIndex?, polyhedralConfigurationIndexOfEntries?,
    PolyhedralGeometry.configurationIndexArity?, distinct]

/-- Public SAPR-8 routing computes the complete mathematical word on one concrete
alternating-rim frame. -/
@[simp] theorem squareAntiprismConfigurationIndex?_exact
    (v0 v1 v2 v3 v4 v5 v6 v7 : PolyhedralPriorityNumber) :
    polyhedralConfigurationIndex? .squareAntiprism
        [v0, v1, v2, v3, v4, v5, v6, v7]
        [0, 1, 2, 3, 4, 5, 6, 7] =
      some [squareAntiprismMathematicalConfigurationIndex
        v0 v1 v2 v3 v4 v5 v6 v7] := by
  have distinct : [0, 1, 2, 3, 4, 5, 6, 7].eraseDups.length = 8 := by decide
  simp [polyhedralConfigurationIndex?, polyhedralConfigurationIndexOfEntries?,
    PolyhedralGeometry.configurationIndexArity?, distinct]

/-- Public DD-8 routing computes the complete mathematical word on one concrete A/B-site
frame. -/
@[simp] theorem dodecahedronConfigurationIndex?_exact
    (a0 a1 a2 a3 b0 b1 b2 b3 : PolyhedralPriorityNumber) :
    polyhedralConfigurationIndex? .dodecahedron
        [a0, a1, a2, a3, b0, b1, b2, b3]
        [0, 1, 2, 3, 4, 5, 6, 7] =
      some [dodecahedronMathematicalConfigurationIndex
        a0 a1 a2 a3 b0 b1 b2 b3] := by
  have distinct : [0, 1, 2, 3, 4, 5, 6, 7].eraseDups.length = 8 := by decide
  simp [polyhedralConfigurationIndex?, polyhedralConfigurationIndexOfEntries?,
    PolyhedralGeometry.configurationIndexArity?, distinct]

/-- Public OCT-8 routing computes the complete mathematical word on one concrete cap/base
frame. -/
@[simp] theorem transBicappedOctahedronConfigurationIndex?_exact
    (cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2 : PolyhedralPriorityNumber) :
    polyhedralConfigurationIndex? .transBicappedOctahedron
        [cap0, cap1, s0p0, s0p1, s0p2, s1p0, s1p1, s1p2]
        [0, 1, 2, 3, 4, 5, 6, 7] =
      some [transBicappedOctahedronMathematicalConfigurationIndex
        cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2] := by
  have distinct : [0, 1, 2, 3, 4, 5, 6, 7].eraseDups.length = 8 := by decide
  simp [polyhedralConfigurationIndex?, polyhedralConfigurationIndexOfEntries?,
    PolyhedralGeometry.configurationIndexArity?, distinct]

/-- Public TPRT-8 routing computes the complete mathematical word on one concrete cap/face
frame. -/
@[simp] theorem triangularFaceBicappedTrigonalPrismConfigurationIndex?_exact
    (cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : PolyhedralPriorityNumber) :
    polyhedralConfigurationIndex? .triangularFaceBicappedTrigonalPrism
        [cap0, cap1, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2]
        [0, 1, 2, 3, 4, 5, 6, 7] =
      some [triangularFaceBicappedTrigonalPrismMathematicalConfigurationIndex
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2] := by
  have distinct : [0, 1, 2, 3, 4, 5, 6, 7].eraseDups.length = 8 := by decide
  simp [polyhedralConfigurationIndex?, polyhedralConfigurationIndexOfEntries?,
    PolyhedralGeometry.configurationIndexArity?, distinct]

/-- Public TPRS-8 routing computes the complete mathematical word on one concrete cap/face
frame. -/
@[simp] theorem squareFaceBicappedTrigonalPrismConfigurationIndex?_exact
    (cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : PolyhedralPriorityNumber) :
    polyhedralConfigurationIndex? .squareFaceBicappedTrigonalPrism
        [cap0, cap1, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2]
        [0, 1, 2, 3, 4, 5, 6, 7] =
      some [squareFaceBicappedTrigonalPrismMathematicalConfigurationIndex
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2] := by
  have distinct : [0, 1, 2, 3, 4, 5, 6, 7].eraseDups.length = 8 := by decide
  simp [polyhedralConfigurationIndex?, polyhedralConfigurationIndexOfEntries?,
    PolyhedralGeometry.configurationIndexArity?, distinct]

/-- Public TPRS-9 routing computes the complete mathematical word on one concrete cap/face
frame. -/
@[simp] theorem squareFaceTricappedTrigonalPrismConfigurationIndex?_exact
    (cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : PolyhedralPriorityNumber) :
    polyhedralConfigurationIndex? .squareFaceTricappedTrigonalPrism
        [cap0, cap1, cap2, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2]
        [0, 1, 2, 3, 4, 5, 6, 7, 8] =
      some [squareFaceTricappedTrigonalPrismMathematicalConfigurationIndex
        cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2] := by
  have distinct : [0, 1, 2, 3, 4, 5, 6, 7, 8].eraseDups.length = 9 := by decide
  simp [polyhedralConfigurationIndex?, polyhedralConfigurationIndexOfEntries?,
    PolyhedralGeometry.configurationIndexArity?, distinct]

/-- Validate which absolute-configuration convention belongs to each P-93 geometry. -/
def polyhedralAbsoluteConfiguration?
    (geometry : PolyhedralGeometry) (rotation? : Option PolyhedralRotationSense) :
    Option (Option PolyhedralAbsoluteConfiguration) :=
  match geometry, rotation? with
  | .trigonalPyramid, some sense => some (some (.rs (trigonalPyramidDescriptorOfRotation sense)))
  | .trigonalPyramid, none => some none
  | .seeSaw, some sense | .trigonalBipyramid, some sense
  | .pentagonalBipyramid, some sense | .hexagonalBipyramid, some sense
  | .heptagonalBipyramid, some sense
  | .squarePyramid4, some sense | .squarePyramid, some sense | .octahedron, some sense =>
      some (some (.ac (PolyhedralChiralitySymbol.ofRotation sense)))
  | .trigonalPrism, some sense =>
      some (some (.ac (PolyhedralChiralitySymbol.ofRotation sense)))
  | .seeSaw, none | .trigonalBipyramid, none
  | .pentagonalBipyramid, none | .hexagonalBipyramid, none
  | .heptagonalBipyramid, none
  | .squarePyramid4, none | .squarePyramid, none | .octahedron, none
  | .trigonalPrism, none
  | .faceMonocappedOctahedron, none
  | .squareFaceMonocappedTrigonalPrism, none
  | .cube, none
  | .squareAntiprism, none
  | .dodecahedron, none
  | .transBicappedOctahedron, none
  | .triangularFaceBicappedTrigonalPrism, none
  | .squareFaceBicappedTrigonalPrism, none
  | .squareFaceTricappedTrigonalPrism, none
  | .linear, none | .angular, none | .trigonalPlanar, none
  | .tShape, none | .tetrahedron, none | .squarePlanar, none => some none
  | _, some _ => none

/-- CU-8 admits a relative mathematical index without claiming an absolute suffix. -/
@[simp] theorem cubeAbsoluteConfiguration?_none :
    polyhedralAbsoluteConfiguration? .cube none = some none :=
  rfl

/-- CU-8 has no source-defined absolute `A`/`C` convention in the represented IR-9 vocabulary. -/
@[simp] theorem cubeAbsoluteConfiguration?_some (rotation : PolyhedralRotationSense) :
    polyhedralAbsoluteConfiguration? .cube (some rotation) = none := by
  cases rotation <;> rfl

/-- SAPR-8 admits a relative mathematical index without claiming an absolute suffix. -/
@[simp] theorem squareAntiprismAbsoluteConfiguration?_none :
    polyhedralAbsoluteConfiguration? .squareAntiprism none = some none :=
  rfl

/-- SAPR-8 has no source-defined absolute `A`/`C` convention in the represented IR-9
vocabulary. -/
@[simp] theorem squareAntiprismAbsoluteConfiguration?_some
    (rotation : PolyhedralRotationSense) :
    polyhedralAbsoluteConfiguration? .squareAntiprism (some rotation) = none := by
  cases rotation <;> rfl

/-- DD-8 admits a relative mathematical index without claiming an absolute suffix. -/
@[simp] theorem dodecahedronAbsoluteConfiguration?_none :
    polyhedralAbsoluteConfiguration? .dodecahedron none = some none :=
  rfl

/-- DD-8 has no source-defined absolute `A`/`C` convention in the represented IR-9 vocabulary. -/
@[simp] theorem dodecahedronAbsoluteConfiguration?_some
    (rotation : PolyhedralRotationSense) :
    polyhedralAbsoluteConfiguration? .dodecahedron (some rotation) = none := by
  cases rotation <;> rfl

/-- OCT-8 admits a relative mathematical index without claiming an absolute suffix. -/
@[simp] theorem transBicappedOctahedronAbsoluteConfiguration?_none :
    polyhedralAbsoluteConfiguration? .transBicappedOctahedron none = some none :=
  rfl

/-- OCT-8 has no source-defined absolute `A`/`C` convention in the represented IR-9
vocabulary. -/
@[simp] theorem transBicappedOctahedronAbsoluteConfiguration?_some
    (rotation : PolyhedralRotationSense) :
    polyhedralAbsoluteConfiguration? .transBicappedOctahedron (some rotation) = none := by
  cases rotation <;> rfl

/-- TPRT-8 admits a relative mathematical index without claiming an absolute suffix. -/
@[simp] theorem triangularFaceBicappedTrigonalPrismAbsoluteConfiguration?_none :
    polyhedralAbsoluteConfiguration? .triangularFaceBicappedTrigonalPrism none = some none :=
  rfl

/-- TPRT-8 has no source-defined absolute `A`/`C` convention in the represented IR-9
vocabulary. -/
@[simp] theorem triangularFaceBicappedTrigonalPrismAbsoluteConfiguration?_some
    (rotation : PolyhedralRotationSense) :
    polyhedralAbsoluteConfiguration? .triangularFaceBicappedTrigonalPrism (some rotation) = none := by
  cases rotation <;> rfl

/-- TPRS-8 admits a relative mathematical index without claiming an absolute suffix. -/
@[simp] theorem squareFaceBicappedTrigonalPrismAbsoluteConfiguration?_none :
    polyhedralAbsoluteConfiguration? .squareFaceBicappedTrigonalPrism none = some none :=
  rfl

/-- TPRS-8 has no source-defined absolute `A`/`C` convention in the represented IR-9
vocabulary. -/
@[simp] theorem squareFaceBicappedTrigonalPrismAbsoluteConfiguration?_some
    (rotation : PolyhedralRotationSense) :
    polyhedralAbsoluteConfiguration? .squareFaceBicappedTrigonalPrism (some rotation) = none := by
  cases rotation <;> rfl

/-- TPRS-9 admits a relative mathematical index without claiming an absolute suffix. -/
@[simp] theorem squareFaceTricappedTrigonalPrismAbsoluteConfiguration?_none :
    polyhedralAbsoluteConfiguration? .squareFaceTricappedTrigonalPrism none = some none :=
  rfl

/-- TPRS-9 has no source-defined absolute `A`/`C` convention in the represented IR-9
vocabulary. -/
@[simp] theorem squareFaceTricappedTrigonalPrismAbsoluteConfiguration?_some
    (rotation : PolyhedralRotationSense) :
    polyhedralAbsoluteConfiguration? .squareFaceTricappedTrigonalPrism (some rotation) = none := by
  cases rotation <;> rfl

/-- Convert a validated P-93 frame to the public assignment surface.  Geometry and distinguished
positions remain observational inputs; ligand priority and the final descriptor are constructed in
Lean. -/
def ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?
    (result : ChemistryNormalizationResult) (record : IndexedPolyhedralGeometryObservation) :
    Option StereoAssignment := do
  if !record.geometryRecognitionOK? then none else
  let priorities ← result.observedPolyhedralPriorityNumbers? record.center record.geometry
    record.ligands record.priming
  let independentRotation? ← record.absoluteOrientation.rotationFor?
    (BlueBookP93.geometryOfProduction record.geometry)
  let rotation? := independentRotation?.map PolyhedralRotationSense.ofIndependent
  if rotation?.isSome && priorities.eraseDups.length != priorities.length then none else
  let positions ← record.configurationPositions.positionsFor?
    (BlueBookP93.geometryOfProduction record.geometry)
  let index ← polyhedralConfigurationIndex? record.geometry priorities positions
  let absolute ← polyhedralAbsoluteConfiguration? record.geometry rotation?
  some { unit := StereoUnit.polyhedron record.center
         outcome := StereoOutcome.polyhedral
           { geometry := record.geometry, configurationIndex := index,
             absolute? := absolute } }

/-- Convert one in-range axial geometry observation to the public assignment surface. -/
def ChemistryNormalizationResult.indexedAxialAssignment?
    (result : ChemistryNormalizationResult) (record : IndexedDetectedAxialUnit) :
    Option StereoAssignment := do
  let assignment ← result.detectedAxialRecord? record
  some
    { unit := StereoUnit.axis assignment.unit.axisStart.val assignment.unit.axisEnd.val
      outcome := StereoOutcome.axial assignment.descriptor }

/-- Convert one in-range planar geometry observation to the public assignment surface. -/
def ChemistryNormalizationResult.indexedPlanarAssignment?
    (result : ChemistryNormalizationResult) (record : IndexedDetectedPlanarUnit) :
    Option StereoAssignment := do
  let assignment ← result.detectedPlanarRecord? record
  some
    { unit := StereoUnit.plane (assignment.unit.planeAtoms.map Fin.val)
      outcome := StereoOutcome.planar assignment.descriptor }

/-- Convert one in-range helical geometry observation to the public assignment surface. -/
def ChemistryNormalizationResult.indexedHelicalAssignment?
    (result : ChemistryNormalizationResult) (record : IndexedDetectedHelicalUnit) :
    Option StereoAssignment := do
  let assignment ← result.detectedHelicalRecord? record
  some
    { unit := StereoUnit.helix (assignment.unit.helixPath.map Fin.val)
      outcome := StereoOutcome.helical assignment.descriptor }

/-- Retain a geometry key only when every validated observation for that key carries the same
descriptor. Duplicate agreeing observations collapse to one assignment; conflicting observations
are all refused rather than exposing two incompatible configurations. -/
def conflictFreeGeometryAssignments (assignments : List StereoAssignment) :
    List StereoAssignment :=
  (assignments.filter fun assignment =>
    ((assignments.filter fun other => other.unit == assignment.unit).map
      StereoAssignment.outcome).eraseDups.length == 1).eraseDups

/-- Validated non-center assignments supplied by a geometry-aware importer.

An axis already assigned by native extended-tetrahedral perception is not duplicated by an
external record.  Planar and helical units currently have no native public assignment path and are
therefore appended after atom-index validation. -/
def geometryAnnotatedAssignments (result : ChemistryNormalizationResult)
    (annotations : IndexedNoncenterStereoAnnotations)
    (native : List StereoAssignment := analyzeNormalized result) : List StereoAssignment :=
  if !result.expandedStereochemicalAdmissible? then [] else
  let axes := conflictFreeGeometryAssignments
    (annotations.axes.filterMap result.indexedAxialAssignment?) |>.filter fun assignment =>
      !(native.any fun existing => existing.unit == assignment.unit)
  let planes := conflictFreeGeometryAssignments
    (annotations.planes.filterMap result.indexedPlanarAssignment?)
  let helices := conflictFreeGeometryAssignments
    (annotations.helices.filterMap result.indexedHelicalAssignment?)
  axes ++ planes ++ helices

/-- Analyze native graph-visible units and append atom-range-validated geometry observations for
unit families whose handedness is not recoverable from a graph alone. -/
def analyzeNormalizedWithGeometry (result : ChemistryNormalizationResult)
    (annotations : IndexedNoncenterStereoAnnotations) : List StereoAssignment :=
  let native := analyzeNormalized result
  native ++ geometryAnnotatedAssignments result annotations native

/-! ## Certified authority-facing entry point -/

/-- Recompute an annotated ordinary tetrahedral assignment with the width-unbounded occurrence
comparator.  `none` is deliberately inconclusive: Rule 6 and several special production carriers
remain outside this comparator, so callers retain the existing fail-closed assignment in that
case. -/
def ChemistryNormalizationResult.authoritativeOccurrenceAssignment?
    (result : ChemistryNormalizationResult) (center : ℕ) : Option StereoAssignment := do
  let spec ← result.parsed.atomAt? center
  let _ ← spec.tetrahedral?
  let expanded := result.parsed.withExplicitHydrogens
  if expanded.isExtendedTetrahedralParityCarrier center then none else
  let fact ← tetrahedralOccurrenceFactAuthoritative? expanded (analysisFuel expanded) center
  let outcome :=
    if fact.uppercase then StereoOutcome.tetrahedral fact.descriptor
    else StereoOutcome.pseudoTetrahedral
      (match fact.descriptor with | RS.R => PseudoRS.r | RS.S => PseudoRS.s)
  some { unit := StereoUnit.tetrahedral center, outcome := outcome }

/-- Prefer the width-unbounded occurrence result at annotated tetrahedral centers while preserving
all other native assignments and every conservative refusal. -/
def ChemistryNormalizationResult.analyzeWithAuthoritativeOccurrences
    (result : ChemistryNormalizationResult) : List StereoAssignment :=
  (analyzeNormalized result).map fun assignment =>
    match assignment.unit with
    | StereoUnit.tetrahedral center =>
        (result.authoritativeOccurrenceAssignment? center).getD assignment
    | _ => assignment

/-- The authoritative occurrence override cannot bypass admission of the exact expanded ranking
graph, because it only replaces members already admitted by `analyzeNormalized`. -/
theorem ChemistryNormalizationResult.analyzeWithAuthoritativeOccurrences_member_admitted
    (result : ChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ result.analyzeWithAuthoritativeOccurrences) :
    result.ExpandedStereochemicalAdmissible := by
  rcases List.mem_map.mp member with ⟨base, baseMember, _⟩
  exact analyzeNormalized_member_expandedStereochemicalAdmissible result base baseMember

/-- Append validated raw geometry observations to a caller-supplied native assignment list. -/
def observedGeometryAssignments (result : ChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations) (native : List StereoAssignment) :
    List StereoAssignment :=
  if !result.expandedStereochemicalAdmissible? then [] else
  let axes := conflictFreeGeometryAssignments
    (observations.axes.filterMap result.axialGeometryObservationAssignment?) |>.filter
      fun assignment => !(native.any fun existing => existing.unit == assignment.unit)
  let planes := conflictFreeGeometryAssignments
    (observations.planes.filterMap result.planarGeometryObservationAssignment?)
  let helices := conflictFreeGeometryAssignments
    (observations.helices.filterMap result.helicalGeometryObservationAssignment?)
  let polyhedra := conflictFreeGeometryAssignments
    (observations.polyhedra.filterMap result.polyhedralGeometryObservationAssignment?) |>.filter
      fun assignment => !(native.any fun existing => existing.unit == assignment.unit)
  axes ++ planes ++ helices ++ polyhedra

/-- A validated polyhedral frame supersedes the graph-only tetrahedral shape hypothesis at the same
center.  Connectivity supplies coordination number but cannot distinguish, for example, T-4 from
SS-4 or SP-4. -/
def retainNativeAgainstObservedGeometry (native observed : List StereoAssignment) :
    List StereoAssignment :=
  let polyhedralCenters := observed.filterMap fun assignment =>
    match assignment.unit with
    | .polyhedron center => some center
    | _ => none
  native.filter fun assignment =>
    match assignment.unit with
    | .tetrahedral center => !(polyhedralCenters.contains center)
    | _ => true

/-- Public graph analysis plus raw orientation observations.  Duplicate agreeing observations
collapse; conflicting senses for the same unit are all rejected. -/
def analyzeNormalizedWithObservedGeometry (result : ChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations) : List StereoAssignment :=
  let native := analyzeNormalized result
  let observed := observedGeometryAssignments result observations native
  retainNativeAgainstObservedGeometry native observed ++ observed

/-- Certified-input analysis. The input carries kernel proofs of graph admissibility, the encoded
valence contract, and source-backed Rule-2 masses for the exact hydrogen-expanded ranking graph;
annotated tetrahedral occurrences use the width-unbounded comparator whenever it succeeds. -/
def analyzeCertifiedNormalized (certified : CertifiedChemistryNormalizationResult) :
    List StereoAssignment :=
  certified.result.analyzeWithAuthoritativeOccurrences

/-- Every assignment emitted by the certified authority-facing graph analyzer was ranked over an
exact, structurally admitted hydrogen-expanded molecule. -/
theorem analyzeCertifiedNormalized_member_admitted
    (certified : CertifiedChemistryNormalizationResult) (assignment : StereoAssignment)
    (member : assignment ∈ analyzeCertifiedNormalized certified) :
    certified.result.ExpandedStereochemicalAdmissible :=
  certified.result.analyzeWithAuthoritativeOccurrences_member_admitted assignment member

/-- Certified-input analysis plus raw conformational senses.  The graph-derived assignments use
the authoritative occurrence preference above, and observation records pass the same index,
nondegeneracy, conflict, and axial-CIP checks as the non-certified convenience API. -/
def analyzeCertifiedNormalizedWithObservedGeometry
    (certified : CertifiedChemistryNormalizationResult)
    (observations : IndexedCIPGeometryObservations) : List StereoAssignment :=
  let native := analyzeCertifiedNormalized certified
  let observed := observedGeometryAssignments certified.result observations native
  retainNativeAgainstObservedGeometry native observed ++ observed

@[simp] theorem analyzeNormalizedWithGeometry_empty
    (result : ChemistryNormalizationResult) :
    analyzeNormalizedWithGeometry result {} = analyzeNormalized result := by
  simp [analyzeNormalizedWithGeometry, geometryAnnotatedAssignments,
    conflictFreeGeometryAssignments]

end TetraStereo.OneCenter
