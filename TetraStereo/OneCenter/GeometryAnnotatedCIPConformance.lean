import TetraStereo.OneCenter.GeometryAnnotatedCIPAnalysis
import TetraStereo.OneCenter.IR9PolyhedralSemantics

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Geometry-observation to P-93 / IR-9 conformance

The graph-only detector cannot infer a three-coordinate heteroatom's spatial geometry.  This
module proves the downstream half of that boundary: once an observation identifies a
trigonal-pyramidal or other supported polyhedral frame, production's absolute descriptor
conversion agrees with the independently transcribed P-93/IR-9 convention.

The truth of the geometry observation remains an upstream coordinate/drawing obligation.  The
observation supplies no ligand priorities; production derives those with the CIP comparator.
-/

/-! ## Independent molecular interpretation of IR-9.3.5.3 -/

namespace RedBookIR9.MolecularPriming

/-- Relational equality of the complete ligand-kind atom label currently represented by the
normalized molecular layer.  Written `@`/`@@` parity is excluded because it is enumeration-relative;
the normalized descriptor sense and uppercase/lowercase class are included instead. -/
def AtomKindEquivalent (mol : RawMolecule) (state : RawDescriptorState)
    (left right : Nat) : Prop :=
  ∃ leftSpec rightSpec,
    mol.atomAt? left = some leftSpec ∧ mol.atomAt? right = some rightSpec ∧
    (((((leftSpec.element = rightSpec.element ∧
      leftSpec.isotope? = rightSpec.isotope?) ∧
      leftSpec.charge = rightSpec.charge) ∧
      leftSpec.aromatic = rightSpec.aromatic) ∧
      leftSpec.explicitHydrogens? = rightSpec.explicitHydrogens?) ∧
      state.ligandKindLabelAt? left = state.ligandKindLabelAt? right)

/-- Relational equality of two finite atom sets represented as duplicate-free lists. -/
def SameFiniteAtomSet (left right : List Nat) : Prop :=
  (left.length = right.length ∧
    (∀ atom, atom ∈ left → atom ∈ right)) ∧
    (∀ atom, atom ∈ right → atom ∈ left)

/-- One explicit full mapping between two center-deleted ligand components.  Positional lookup in
`targetOrder` is the bijection; its permutation provenance is supplied by `ComponentIsomorphism`
below. -/
def ComponentMapping
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (source targetOrder : List Nat) : Prop :=
  let positions := List.range source.length
  (source.length = targetOrder.length ∧
    (∀ position, position ∈ positions →
      let left := source.getD position 0
      let right := targetOrder.getD position 0
      AtomKindEquivalent mol state left right ∧
        mol.constitutionBondClass mol.localizedMancudeEdges center left =
          mol.constitutionBondClass mol.localizedMancudeEdges center right)) ∧
    (∀ leftPosition, leftPosition ∈ positions →
      ∀ rightPosition, rightPosition ∈ positions →
        let sourceLeft := source.getD leftPosition 0
        let sourceRight := source.getD rightPosition 0
        let targetLeft := targetOrder.getD leftPosition 0
        let targetRight := targetOrder.getD rightPosition 0
        mol.constitutionBondClass mol.localizedMancudeEdges sourceLeft sourceRight =
            mol.constitutionBondClass mol.localizedMancudeEdges targetLeft targetRight ∧
          result.doubleBondStereoBetween? sourceLeft sourceRight =
            result.doubleBondStereoBetween? targetLeft targetRight)

/-- Full finite labeled-component isomorphism.  Membership in `target.permutations` supplies a
bijection onto exactly the target component, while `ComponentMapping` supplies every chemical
label and induced-edge preservation obligation. -/
def ComponentIsomorphism
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (source target : List Nat) : Prop :=
  source.length = target.length ∧
    ∃ targetOrder, targetOrder ∈ target.permutations ∧
      ComponentMapping result mol state center source targetOrder

/-- Source-level meaning of two symmetry-related coordinating donor subsets inside one ligand. -/
def SymmetryRelatedFragments
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (component sourceFragment targetFragment : List Nat) : Prop :=
  (((((sourceFragment ≠ [] ∧ targetFragment ≠ []) ∧
    sourceFragment.eraseDups.length = sourceFragment.length) ∧
    targetFragment.eraseDups.length = targetFragment.length) ∧
    (∀ atom, atom ∈ sourceFragment → atom ∈ component)) ∧
    (∀ atom, atom ∈ targetFragment → atom ∈ component)) ∧
    ∃ targetOrder, targetOrder ∈ component.permutations ∧
      ComponentMapping result mol state center component targetOrder ∧
      ∃ mapped,
        sourceFragment.mapM (mappedCoordinationComponentAtom? component targetOrder) =
          some mapped ∧
        SameFiniteAtomSet mapped targetFragment

end RedBookIR9.MolecularPriming

@[simp] theorem sameCoordinationLigandAtom_eq_true_iff_IR9
    (mol : RawMolecule) (state : RawDescriptorState) (left right : Nat) :
    sameCoordinationLigandAtom mol state left right = true ↔
      RedBookIR9.MolecularPriming.AtomKindEquivalent mol state left right := by
  unfold sameCoordinationLigandAtom RedBookIR9.MolecularPriming.AtomKindEquivalent
  cases leftEq : mol.atomAt? left with
  | none => simp
  | some leftSpec =>
      cases rightEq : mol.atomAt? right with
      | none => simp
      | some rightSpec => simp

@[simp] theorem sameFiniteAtomSet_eq_true_iff_IR9 (left right : List Nat) :
    sameFiniteAtomSet left right = true ↔
      RedBookIR9.MolecularPriming.SameFiniteAtomSet left right := by
  simp [sameFiniteAtomSet, RedBookIR9.MolecularPriming.SameFiniteAtomSet,
    List.all_eq_true]

/-- The executable mapping validator reflects exactly to the independently stated full component
mapping relation. -/
theorem coordinationComponentMappingOK?_eq_true_iff_IR9
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (source targetOrder : List Nat) :
    result.coordinationComponentMappingOK? mol state center source targetOrder = true ↔
      RedBookIR9.MolecularPriming.ComponentMapping
        result mol state center source targetOrder := by
  simp [ChemistryNormalizationResult.coordinationComponentMappingOK?,
    RedBookIR9.MolecularPriming.ComponentMapping, List.all_eq_true,
    sameCoordinationLigandAtom_eq_true_iff_IR9]

/-- Exhaustive production ligand-kind comparison is exactly finite labeled-component
isomorphism. -/
theorem coordinationComponentsSameKind?_eq_true_iff_IR9
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (source target : List Nat) :
    result.coordinationComponentsSameKind? mol state center source target = true ↔
      RedBookIR9.MolecularPriming.ComponentIsomorphism
        result mol state center source target := by
  simp [ChemistryNormalizationResult.coordinationComponentsSameKind?,
    RedBookIR9.MolecularPriming.ComponentIsomorphism, List.any_eq_true,
    coordinationComponentMappingOK?_eq_true_iff_IR9]

private theorem mappedCoordinationFragment_eq_true_iff_IR9
    (component targetOrder sourceFragment targetFragment : List Nat) :
    (match sourceFragment.mapM
        (mappedCoordinationComponentAtom? component targetOrder) with
      | none => false
      | some mapped => sameFiniteAtomSet mapped targetFragment) = true ↔
      ∃ mapped,
        sourceFragment.mapM (mappedCoordinationComponentAtom? component targetOrder) =
          some mapped ∧
        RedBookIR9.MolecularPriming.SameFiniteAtomSet mapped targetFragment := by
  cases mappedEq : sourceFragment.mapM
      (mappedCoordinationComponentAtom? component targetOrder) with
  | none => simp
  | some mapped => simp [sameFiniteAtomSet_eq_true_iff_IR9]

/-- The within-ligand fragment symmetry check reflects exactly to transport by a full labeled
component automorphism. -/
theorem coordinatingFragmentsSymmetryRelated?_eq_true_iff_IR9
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (component sourceFragment targetFragment : List Nat) :
    result.coordinatingFragmentsSymmetryRelated?
        mol state center component sourceFragment targetFragment = true ↔
      RedBookIR9.MolecularPriming.SymmetryRelatedFragments
        result mol state center component sourceFragment targetFragment := by
  simp [ChemistryNormalizationResult.coordinatingFragmentsSymmetryRelated?,
    RedBookIR9.MolecularPriming.SymmetryRelatedFragments, List.all_eq_true,
    List.any_eq_true,
    coordinationComponentMappingOK?_eq_true_iff_IR9]
  intro _ _ _ _ _ _
  constructor
  · rintro ⟨targetOrder, permutation, mapping, transported⟩
    exact ⟨targetOrder, permutation, mapping,
      (mappedCoordinationFragment_eq_true_iff_IR9
        component targetOrder sourceFragment targetFragment).mp transported⟩
  · rintro ⟨targetOrder, permutation, mapping, transported⟩
    exact ⟨targetOrder, permutation, mapping,
      (mappedCoordinationFragment_eq_true_iff_IR9
        component targetOrder sourceFragment targetFragment).mpr transported⟩

/-- The executable geometry-evidence gate is exactly the independent IR-9.3.2 recognition
relation. -/
theorem geometryRecognitionOK?_eq_true_iff_IR9
    (record : IndexedPolyhedralGeometryObservation) :
    record.geometryRecognitionOK? = true ↔
      RedBookIR9.GeometryRecognized record.recognition
        (BlueBookP93.geometryOfProduction record.geometry) := by
  simp [IndexedPolyhedralGeometryObservation.geometryRecognitionOK?,
    RedBookIR9.GeometryRecognized]

@[simp] theorem rotationOfProduction_ofIndependent
    (sense : BlueBookP93.RotationSense) :
    BlueBookP93.rotationOfProduction (PolyhedralRotationSense.ofIndependent sense) = sense := by
  cases sense <;> rfl

namespace BlueBookP93.GeometryObservation

def effectivePrimingMemberships (donorCount : Nat)
    (memberships : List (Option RedBookIR9.PrimingMembership)) :
    List (Option RedBookIR9.PrimingMembership) :=
  if memberships.isEmpty then List.replicate donorCount none else memberships

def candidatePrimeCounts? (donorCount : Nat)
    (memberships : List (Option RedBookIR9.PrimingMembership)) : Option (List Nat) :=
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

def familyPrimeCountsOK? (donorCount : Nat)
    (memberships : List (Option RedBookIR9.PrimingMembership))
    (primeCounts : List Nat) : Bool :=
  RedBookIR9.finitePrimingAssignmentOK donorCount memberships primeCounts

/-- Independent executable choice permitted by IR-9.3.5.3.  Each particular ligand/fragment kind
is canonicalized separately; unrelated kinds may independently reuse zero, one, two, ... primes. -/
def canonicalPrimeCounts? (donorCount : Nat)
    (memberships : List (Option RedBookIR9.PrimingMembership)) : Option (List Nat) := do
  let effective := effectivePrimingMemberships donorCount memberships
  let primeCounts ← candidatePrimeCounts? donorCount effective
  if !familyPrimeCountsOK? donorCount effective primeCounts then none else
  some primeCounts

/-- Independent statement of the number of distinguished positions needed by each configuration
index construction that is complete in the observation pipeline.  OCF-7 and TPRS-7 use the proved
symmetry-complete mathematical construction; `none` remains intentional for geometries whose
complete construction has not yet been formalized. -/
def configurationIndexArity? : BlueBookP93.Geometry → Option ℕ
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

/-- Independent decoding of one canonical mathematical digit. -/
def digitToPriorityNumber
    (digit : RedBookIR9.FiniteSymmetry.CanonicalPriorityDigit) :
    BlueBookP93.PriorityNumber :=
  { number := (ofLex digit).1, primes := (ofLex digit).2 }

/-- Independent OCF-7 placement in its typed seven-position frame. -/
def ocf7Placement (cap capped0 capped1 capped2 opposite0 opposite1 opposite2 :
    BlueBookP93.PriorityNumber) :
    RedBookIR9.FaceMonocappedOctahedron7SourceIndexCompleteness.Position →
      BlueBookP93.PriorityNumber
  | .cap => cap
  | .cappedFace corner => ![capped0, capped1, capped2] corner
  | .oppositeFace corner => ![opposite0, opposite1, opposite2] corner

/-- Independent TPRS-7 placement in its typed seven-position frame. -/
def tprs7Placement (cap first0 first1 first2 second0 second1 second2 :
    BlueBookP93.PriorityNumber) :
    RedBookIR9.SquareFaceMonocappedTrigonalPrism7FiniteSymmetry.Position →
      BlueBookP93.PriorityNumber
  | .cap => cap
  | .prismVertex face corner =>
      ![![first0, first1, first2], ![second0, second1, second2]] face corner

/-- Independent complete OCF-7 mathematical word. -/
def ocf7MathematicalIndex
    (cap capped0 capped1 capped2 opposite0 opposite1 opposite2 :
      BlueBookP93.PriorityNumber) : List BlueBookP93.PriorityNumber :=
  (RedBookIR9.FaceMonocappedOctahedron7SourceIndexCompleteness.executableSourceIndex
    (ocf7Placement cap capped0 capped1 capped2 opposite0 opposite1 opposite2)).map
      digitToPriorityNumber

/-- Independent complete TPRS-7 mathematical word. -/
def tprs7MathematicalIndex
    (cap first0 first1 first2 second0 second1 second2 :
      BlueBookP93.PriorityNumber) : List BlueBookP93.PriorityNumber :=
  (RedBookIR9.SquareFaceMonocappedTrigonalPrism7SourceIndexCompleteness.executableSourceIndex
    (tprs7Placement cap first0 first1 first2 second0 second1 second2)).map
      digitToPriorityNumber

/-- Independent complete CU-8 mathematical word over all 48 signed-coordinate frames. -/
def cubeMathematicalIndex
    (v000 v001 v010 v011 v100 v101 v110 v111 : BlueBookP93.PriorityNumber) :
    List BlueBookP93.PriorityNumber :=
  (RedBookIR9.CubeSourceIndexCompleteness.executableSourceIndex
      (RedBookIR9.CubeSourceIndexCompleteness.placementOfEntries
        v000 v001 v010 v011 v100 v101 v110 v111)).map digitToPriorityNumber

/-- Independent complete SAPR-8 mathematical word over all sixteen alternating-rim frames. -/
def squareAntiprismMathematicalIndex
    (v0 v1 v2 v3 v4 v5 v6 v7 : BlueBookP93.PriorityNumber) :
    List BlueBookP93.PriorityNumber :=
  (RedBookIR9.SquareAntiprism8SourceIndexCompleteness.executableSourceIndex
      (RedBookIR9.SquareAntiprism8SourceIndexCompleteness.placementOfEntries
        v0 v1 v2 v3 v4 v5 v6 v7)).map digitToPriorityNumber

/-- Independent complete DD-8 mathematical word over all eight diagonal A/B-site frames. -/
def dodecahedronMathematicalIndex
    (a0 a1 a2 a3 b0 b1 b2 b3 : BlueBookP93.PriorityNumber) :
    List BlueBookP93.PriorityNumber :=
  (RedBookIR9.TrigonalDodecahedron8SourceIndexCompleteness.executableSourceIndex
      (RedBookIR9.TrigonalDodecahedron8SourceIndexCompleteness.placementOfEntries
        a0 a1 a2 a3 b0 b1 b2 b3)).map digitToPriorityNumber

/-- Independent complete OCT-8 mathematical word over all twelve cap-side/pair frames. -/
def transBicappedOctahedronMathematicalIndex
    (cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2 : BlueBookP93.PriorityNumber) :
    List BlueBookP93.PriorityNumber :=
  (RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness.executableSourceIndex
      (RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness.placementOfEntries
        cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2)).map digitToPriorityNumber

/-- Independent complete TPRT-8 mathematical word over its twelve face/corner frames. -/
def triangularFaceBicappedTrigonalPrismMathematicalIndex
    (cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : BlueBookP93.PriorityNumber) :
    List BlueBookP93.PriorityNumber :=
  (RedBookIR9.TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness.executableSourceIndex
      (RedBookIR9.TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness.placementOfEntries
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2)).map digitToPriorityNumber

/-- Independent complete TPRS-8 mathematical word over its four structural frames. -/
def squareFaceBicappedTrigonalPrismMathematicalIndex
    (cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : BlueBookP93.PriorityNumber) :
    List BlueBookP93.PriorityNumber :=
  (RedBookIR9.SquareFaceBicappedTrigonalPrism8SourceIndexCompleteness.executableSourceIndex
      (RedBookIR9.SquareFaceBicappedTrigonalPrism8SourceIndexCompleteness.placementOfEntries
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2)).map digitToPriorityNumber

/-- Independent complete TPRS-9 mathematical word over its twelve structural frames. -/
def squareFaceTricappedTrigonalPrismMathematicalIndex
    (cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : BlueBookP93.PriorityNumber) :
    List BlueBookP93.PriorityNumber :=
  (RedBookIR9.SquareFaceTricappedTrigonalPrism9SourceIndexCompleteness.executableSourceIndex
      (RedBookIR9.SquareFaceTricappedTrigonalPrism9SourceIndexCompleteness.placementOfEntries
        cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2)).map digitToPriorityNumber

/-- Independent index construction from the priority numbers at the geometry-defined positions. -/
def configurationIndexOfEntries? (geometry : BlueBookP93.Geometry)
    (entries : List BlueBookP93.PriorityNumber) :
    Option (List (List BlueBookP93.PriorityNumber)) :=
  match geometry, entries with
  | .linear, [] | .angular, [] | .trigonalPlanar, []
  | .trigonalPyramid, [] | .tetrahedron, [] => some []
  | .tShape, [stem] => some [BlueBookP93.tShapeIndex stem]
  | .squarePlanar, [transToOne] => some [BlueBookP93.squarePlanarIndex transToOne]
  | .squarePyramid4, [transToSenior] =>
      some [BlueBookP93.squarePyramid4Index transToSenior]
  | .seeSaw, [first, second] => some [BlueBookP93.seeSawIndex first second]
  | .trigonalBipyramid, [first, second] =>
      some [BlueBookP93.trigonalBipyramidIndex first second]
  | .squarePyramid, [apical, transToSeniorBase] =>
      some [BlueBookP93.squarePyramidIndex apical transToSeniorBase]
  | .octahedron, [transToOne, transToSeniorPlane] =>
      some [BlueBookP93.octahedronIndex transToOne transToSeniorPlane]
  | .trigonalPrism, [first0, first1, first2, second0, second1, second2] =>
      some [BlueBookP93.trigonalPrismIndex
        [first0, first1, first2] [second0, second1, second2]]
  | .faceMonocappedOctahedron,
      [cap, capped0, capped1, capped2, opposite0, opposite1, opposite2] =>
      some [ocf7MathematicalIndex cap capped0 capped1 capped2
        opposite0 opposite1 opposite2]
  | .squareFaceMonocappedTrigonalPrism,
      [cap, first0, first1, first2, second0, second1, second2] =>
      some [tprs7MathematicalIndex cap first0 first1 first2 second0 second1 second2]
  | .cube, [v000, v001, v010, v011, v100, v101, v110, v111] =>
      some [cubeMathematicalIndex v000 v001 v010 v011 v100 v101 v110 v111]
  | .squareAntiprism, [v0, v1, v2, v3, v4, v5, v6, v7] =>
      some [squareAntiprismMathematicalIndex v0 v1 v2 v3 v4 v5 v6 v7]
  | .dodecahedron, [a0, a1, a2, a3, b0, b1, b2, b3] =>
      some [dodecahedronMathematicalIndex a0 a1 a2 a3 b0 b1 b2 b3]
  | .transBicappedOctahedron, [cap0, cap1, s0p0, s0p1, s0p2, s1p0, s1p1, s1p2] =>
      some [transBicappedOctahedronMathematicalIndex
        cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2]
  | .triangularFaceBicappedTrigonalPrism,
      [cap0, cap1, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2] =>
      some [triangularFaceBicappedTrigonalPrismMathematicalIndex
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2]
  | .squareFaceBicappedTrigonalPrism,
      [cap0, cap1, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2] =>
      some [squareFaceBicappedTrigonalPrismMathematicalIndex
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2]
  | .squareFaceTricappedTrigonalPrism,
      [cap0, cap1, cap2, f0c0, f0c1, f0c2, f1c0, f1c1, f1c2] =>
      some [squareFaceTricappedTrigonalPrismMathematicalIndex
        cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2]
  | .pentagonalBipyramid, firstAxial :: secondAxial :: perpendicularPlane =>
      some (BlueBookP93.bipyramidalIndex firstAxial secondAxial perpendicularPlane)
  | .hexagonalBipyramid, firstAxial :: secondAxial :: perpendicularPlane =>
      some (BlueBookP93.bipyramidalIndex firstAxial secondAxial perpendicularPlane)
  | .heptagonalBipyramid, firstAxial :: secondAxial :: perpendicularPlane =>
      some (BlueBookP93.bipyramidalIndex firstAxial secondAxial perpendicularPlane)
  | _, _ => none

/-- Independent P-93/IR-9 configuration-index router over already assigned priority numbers and
geometry-defined distinguished positions.  It is deliberately stated with the independent
priority-number and geometry types, not by calling a production constructor. -/
def configurationIndex? (geometry : BlueBookP93.Geometry)
    (priorities : List BlueBookP93.PriorityNumber) (positions : List ℕ) :
    Option (List (List BlueBookP93.PriorityNumber)) := do
  let arity ← configurationIndexArity? geometry
  if positions.length != arity ||
      positions.eraseDups.length != positions.length then none else
  let entries ← positions.mapM fun position => priorities[position]?
  configurationIndexOfEntries? geometry entries

/-- Independent result family for the two absolute-configuration conventions used by the current
polyhedral observation path. -/
inductive AbsoluteConfiguration where
  | rs (descriptor : RS)
  | ca (descriptor : BlueBookP93.ChiralitySymbol)
  deriving DecidableEq, Repr

/-- Independent P-93/IR-9 absolute-configuration routing by recognized geometry. -/
def absoluteConfiguration?
    (geometry : BlueBookP93.Geometry) (rotation? : Option BlueBookP93.RotationSense) :
    Option (Option AbsoluteConfiguration) :=
  match geometry, rotation? with
  | .trigonalPyramid, some sense =>
      some (some (.rs (RedBookIR9.trigonalPyramidalRS
        { sequenceFromPriorityOne := sense
          viewedFromCenterTowardLeastPreferred := True
          phantomSite := .lonePairSite
          phantomHasLowestPriority := True })))
  | .trigonalPyramid, none => some none
  | .seeSaw, some sense | .trigonalBipyramid, some sense
  | .pentagonalBipyramid, some sense | .hexagonalBipyramid, some sense
  | .heptagonalBipyramid, some sense
  | .squarePyramid4, some sense | .squarePyramid, some sense | .octahedron, some sense =>
      some (some (.ca (BlueBookP93.chiralitySymbol sense)))
  | .trigonalPrism, some sense =>
      some (some (.ca (BlueBookP93.chiralitySymbol sense)))
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

end BlueBookP93.GeometryObservation

/-- Production's family-local priming choice is exactly the independent IR-9.3.5.3 choice,
including the no-priming default and malformed-frame refusal. -/
theorem canonicalPolyhedralPrimeCounts?_conforms_IR9
    (donorCount : ℕ) (memberships : List (Option RedBookIR9.PrimingMembership)) :
    canonicalPolyhedralPrimeCounts? donorCount memberships =
      BlueBookP93.GeometryObservation.canonicalPrimeCounts? donorCount memberships :=
  by
    unfold canonicalPolyhedralPrimeCounts?
      BlueBookP93.GeometryObservation.canonicalPrimeCounts?
      effectivePolyhedralPrimingMemberships
      BlueBookP93.GeometryObservation.effectivePrimingMemberships
      candidateCanonicalPolyhedralPrimeCounts?
      BlueBookP93.GeometryObservation.candidatePrimeCounts?
      familyPolyhedralPrimeCountsOK?
      BlueBookP93.GeometryObservation.familyPrimeCountsOK?
    rfl

/-- The executable family validator reflects exactly to the finite independent IR-9.3.5.3
relation. -/
theorem familyPolyhedralPrimeCountsOK?_eq_true_iff_IR9
    (donorCount : Nat) (memberships : List (Option RedBookIR9.PrimingMembership))
    (primeCounts : List Nat) :
    familyPolyhedralPrimeCountsOK? donorCount memberships primeCounts = true ↔
      RedBookIR9.FinitePrimingAssignment donorCount memberships primeCounts := by
  rfl

/-- Every successful production prime-count derivation has the complete finite IR-9.3.5.3
meaning: either priming is inapplicable and every count is zero, or the observed groups and emitted
counts form an admissible dense grouping assignment. -/
theorem canonicalPolyhedralPrimeCounts?_sound_IR9
    (donorCount : Nat) (memberships : List (Option RedBookIR9.PrimingMembership))
    (primeCounts : List Nat)
    (produced : canonicalPolyhedralPrimeCounts? donorCount memberships = some primeCounts) :
    RedBookIR9.FinitePrimingAssignment donorCount
      (effectivePolyhedralPrimingMemberships donorCount memberships) primeCounts := by
  unfold canonicalPolyhedralPrimeCounts? at produced
  let effective := effectivePolyhedralPrimingMemberships donorCount memberships
  cases candidateEq : candidateCanonicalPolyhedralPrimeCounts? donorCount effective with
  | none => simp [effective, candidateEq] at produced
  | some candidate =>
      by_cases checked : familyPolyhedralPrimeCountsOK? donorCount effective candidate = true
      · have countsEq : candidate = primeCounts := by
          simpa [effective, candidateEq, checked] using produced
        subst primeCounts
        exact (familyPolyhedralPrimeCountsOK?_eq_true_iff_IR9
          donorCount effective candidate).mp checked
      · simp [effective, candidateEq, checked] at produced

/-- A returned repeated-ligand frame has passed the complete molecular validation gate; candidate
generation itself is not trusted. -/
theorem ChemistryNormalizationResult.deriveRepeatedLigandPrimingMemberships?_sound
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (ligands : List Nat)
    (memberships : List (Option RedBookIR9.PrimingMembership))
    (derived : result.deriveRepeatedLigandPrimingMemberships? mol state center ligands =
      some memberships) :
    result.repeatedLigandPrimingMembershipsOK? mol state center ligands memberships = true := by
  unfold ChemistryNormalizationResult.deriveRepeatedLigandPrimingMemberships? at derived
  let candidate := result.candidateRepeatedLigandPrimingMemberships mol state center ligands
  by_cases checked :
      result.repeatedLigandPrimingMembershipsOK? mol state center ligands candidate = true
  · have candidateEq : candidate = memberships := by
      simpa [candidate, checked] using derived
    simpa [← candidateEq] using checked
  · simp [candidate, checked] at derived

/-- A returned within-ligand fragment frame has passed the complete component-membership and
automorphism validation gate. -/
theorem ChemistryNormalizationResult.deriveCoordinatingFragmentPrimingMemberships?_sound
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (ligands : List Nat) (fragmentDonors : List (List Nat))
    (memberships : List (Option RedBookIR9.PrimingMembership))
    (derived : result.deriveCoordinatingFragmentPrimingMemberships?
      mol state center ligands fragmentDonors = some memberships) :
    result.coordinatingFragmentPrimingMembershipsOK?
      mol state center ligands fragmentDonors memberships = true := by
  unfold ChemistryNormalizationResult.deriveCoordinatingFragmentPrimingMemberships? at derived
  let candidate := result.candidateCoordinatingFragmentPrimingMemberships
    mol state center ligands fragmentDonors
  by_cases checked : result.coordinatingFragmentPrimingMembershipsOK?
      mol state center ligands fragmentDonors candidate = true
  · have candidateEq : candidate = memberships := by
      simpa [candidate, checked] using derived
    simpa [← candidateEq] using checked
  · simp [candidate, checked] at derived

@[simp] theorem priorityDecisionAgreesNumbering?_eq_true_iff_IR9
    (decision : Option Ordering) (leftNumber rightNumber : Nat) :
    priorityDecisionAgreesNumbering? decision leftNumber rightNumber = true ↔
      RedBookIR9.PriorityDecisionAgrees decision leftNumber rightNumber := by
  cases decision with
  | none => simp [priorityDecisionAgreesNumbering?, RedBookIR9.PriorityDecisionAgrees]
  | some decision =>
      cases decision <;>
        simp [priorityDecisionAgreesNumbering?, RedBookIR9.PriorityDecisionAgrees]

/-- The executable finite numbering checker reflects exactly to the independently stated
IR-9.3.5.2 relation. -/
theorem densePolyhedralPriorityNumberingOK?_eq_true_iff_IR9
    (count : Nat) (compareAt : Nat → Nat → Option Ordering) (numbers : List Nat) :
    densePolyhedralPriorityNumberingOK? count compareAt numbers = true ↔
      RedBookIR9.FinitePriorityNumbering count compareAt numbers := by
  constructor
  · intro checked
    simp [densePolyhedralPriorityNumberingOK?, List.all_eq_true, List.any_eq_true,
      priorityDecisionAgreesNumbering?_eq_true_iff_IR9] at checked
    rcases checked with ⟨⟨⟨⟨lengthEq, positive⟩, comparison⟩, highest⟩, noGaps⟩
    refine
      { length_eq := lengthEq
        positive := ?_
        comparison := ?_
        highest_number_one := ?_
        no_gaps := ?_ }
    · intro position positionLt
      exact positive position positionLt
    · intro left right leftLt rightLt
      exact comparison left leftLt right rightLt
    · intro position positionLt noHigher
      rcases highest position positionLt with hasHigher | numberOne
      · obtain ⟨other, otherLt, higher⟩ := hasHigher
        exact False.elim ((noHigher other otherLt) higher)
      · exact numberOne
    · intro position positionLt number numberPositive numberLt
      obtain ⟨higher, higherLt, higherNumber⟩ :=
        noGaps position positionLt (number - 1) (by omega)
      refine ⟨higher, higherLt, ?_⟩
      omega
  · intro assignment
    simp [densePolyhedralPriorityNumberingOK?, List.all_eq_true, List.any_eq_true,
      priorityDecisionAgreesNumbering?_eq_true_iff_IR9]
    refine ⟨⟨⟨⟨assignment.length_eq, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro position positionLt
      exact assignment.positive position positionLt
    · intro left leftLt right rightLt
      exact assignment.comparison left right leftLt rightLt
    · intro position positionLt
      by_cases hasHigher : ∃ other, other < count ∧ compareAt other position = some .gt
      · exact Or.inl hasHigher
      · right
        exact assignment.highest_number_one position positionLt fun other otherLt higher =>
          hasHigher ⟨other, otherLt, higher⟩
    · intro position positionLt offset offsetLt
      have positionPositive := assignment.positive position positionLt
      obtain ⟨higher, higherLt, higherNumber⟩ := assignment.no_gaps
        position positionLt (offset + 1) (by omega) (by omega)
      exact ⟨higher, higherLt, higherNumber⟩

/-- Any base-number list returned by the production derivation satisfies every independent finite
IR-9.3.5.2 obligation.  The theorem relies on the reflected validator, not on correctness of the
candidate sorting routine. -/
theorem deriveDensePolyhedralBasePriorityNumbers?_sound_IR9
    (count : Nat) (compareAt : Nat → Nat → Option Ordering) (numbers : List Nat)
    (derived : deriveDensePolyhedralBasePriorityNumbers? count compareAt = some numbers) :
    RedBookIR9.FinitePriorityNumbering count compareAt numbers := by
  unfold deriveDensePolyhedralBasePriorityNumbers? at derived
  cases candidateEq : candidateDensePolyhedralBasePriorityNumbers? count compareAt with
  | none => simp [candidateEq] at derived
  | some candidate =>
      by_cases checked :
          densePolyhedralPriorityNumberingOK? count compareAt candidate = true
      · have candidateEqNumbers : candidate = numbers := by
          simpa [candidateEq, checked] using derived
        subst numbers
        exact
          (densePolyhedralPriorityNumberingOK?_eq_true_iff_IR9
            count compareAt candidate).mp checked
      · simp [candidateEq, checked] at derived

/-- Molecular donor numbering can succeed only with an internally derived comparison frame, an
IR-9-valid dense base numbering for that exact frame, canonical prime counts for the observed
groups, and an exact pointwise combination of those two lists. -/
theorem ChemistryNormalizationResult.polyhedralPriorityNumbers?_sound_IR9
    (result : ChemistryNormalizationResult) (center : Nat) (geometry : PolyhedralGeometry)
    (ligands : List Nat)
    (primingMemberships : List (Option RedBookIR9.PrimingMembership))
    (priorities : List PolyhedralPriorityNumber)
    (produced :
      result.polyhedralPriorityNumbers? center geometry ligands primingMemberships =
        some priorities) :
    ∃ compareAt baseNumbers primeCounts,
      result.polyhedralPriorityComparisonFrame? center geometry ligands = some compareAt ∧
      deriveDensePolyhedralBasePriorityNumbers? ligands.length compareAt = some baseNumbers ∧
      RedBookIR9.FinitePriorityNumbering ligands.length compareAt baseNumbers ∧
      canonicalPolyhedralPrimeCounts? ligands.length primingMemberships = some primeCounts ∧
      RedBookIR9.FinitePrimingAssignment ligands.length
        (effectivePolyhedralPrimingMemberships ligands.length primingMemberships) primeCounts ∧
      baseNumbers.zipWithM (fun number primes =>
        some { number := number, primes := primes }) primeCounts = some priorities := by
  unfold ChemistryNormalizationResult.polyhedralPriorityNumbers? at produced
  cases frameEq : result.polyhedralPriorityComparisonFrame? center geometry ligands with
  | none => simp [frameEq] at produced
  | some compareAt =>
      cases baseEq : deriveDensePolyhedralBasePriorityNumbers? ligands.length compareAt with
      | none => simp [frameEq, baseEq] at produced
      | some baseNumbers =>
          cases primeEq : canonicalPolyhedralPrimeCounts? ligands.length primingMemberships with
          | none => simp [frameEq, primeEq] at produced
          | some primeCounts =>
              refine ⟨compareAt, baseNumbers, primeCounts, rfl, baseEq, ?_, rfl, ?_, ?_⟩
              · exact deriveDensePolyhedralBasePriorityNumbers?_sound_IR9
                  ligands.length compareAt baseNumbers baseEq
              · exact canonicalPolyhedralPrimeCounts?_sound_IR9
                  ligands.length primingMemberships primeCounts primeEq
              · simpa [frameEq, baseEq, primeEq] using produced

/-- End-to-end donor-numbering certificate for the safe molecular polyhedral ingress.  Success
exposes a molecularly derived and validated repeated-ligand frame, followed by the complete finite
IR-9.3.5.2 and family-local IR-9.3.5.3 obligations for the exact emitted priorities. -/
theorem ChemistryNormalizationResult.molecularPolyhedralPriorityNumbers?_sound_IR9
    (result : ChemistryNormalizationResult) (center : Nat) (geometry : PolyhedralGeometry)
    (ligands : List Nat) (priorities : List PolyhedralPriorityNumber)
    (produced :
      result.molecularPolyhedralPriorityNumbers? center geometry ligands = some priorities) :
    ∃ memberships,
      result.deriveRepeatedLigandPrimingMemberships?
          result.geometryPriorityState.1 result.geometryPriorityState.2.2 center ligands =
        some memberships ∧
      result.repeatedLigandPrimingMembershipsOK?
          result.geometryPriorityState.1 result.geometryPriorityState.2.2 center ligands
          memberships = true ∧
      ∃ compareAt baseNumbers primeCounts,
        result.polyhedralPriorityComparisonFrame? center geometry ligands = some compareAt ∧
        deriveDensePolyhedralBasePriorityNumbers? ligands.length compareAt = some baseNumbers ∧
        RedBookIR9.FinitePriorityNumbering ligands.length compareAt baseNumbers ∧
        canonicalPolyhedralPrimeCounts? ligands.length memberships = some primeCounts ∧
        RedBookIR9.FinitePrimingAssignment ligands.length
          (effectivePolyhedralPrimingMemberships ligands.length memberships) primeCounts ∧
        baseNumbers.zipWithM (fun number primes =>
          some { number := number, primes := primes }) primeCounts = some priorities := by
  unfold ChemistryNormalizationResult.molecularPolyhedralPriorityNumbers? at produced
  let mol := result.geometryPriorityState.1
  let state := result.geometryPriorityState.2.2
  cases membershipsEq :
      result.deriveRepeatedLigandPrimingMemberships? mol state center ligands with
  | none => simp [mol, state, membershipsEq] at produced
  | some memberships =>
      have innerProduced :
          result.polyhedralPriorityNumbers? center geometry ligands memberships =
            some priorities := by
        simpa [mol, state, membershipsEq] using produced
      obtain ⟨compareAt, baseNumbers, primeCounts, frameEq, baseEq, baseValid,
          primeEq, primeValid, zipped⟩ :=
        result.polyhedralPriorityNumbers?_sound_IR9 center geometry ligands memberships
          priorities innerProduced
      refine ⟨memberships, ?_, ?_, compareAt, baseNumbers, primeCounts,
        frameEq, baseEq, baseValid, primeEq, primeValid, zipped⟩
      · simp
      · exact result.deriveRepeatedLigandPrimingMemberships?_sound mol state center ligands
          memberships membershipsEq

/-- A proof-relevant record of which source-defined IR-9.3.5.3 basis produced a molecular priming
frame. -/
inductive ValidatedMolecularPrimingFrame
    (result : ChemistryNormalizationResult) (mol : RawMolecule) (state : RawDescriptorState)
    (center : Nat) (ligands : List Nat) :
    IndexedPolyhedralPrimingObservation →
      List (Option RedBookIR9.PrimingMembership) → Prop where
  | repeated (memberships)
      (derived : result.deriveRepeatedLigandPrimingMemberships?
        mol state center ligands = some memberships)
      (valid : result.repeatedLigandPrimingMembershipsOK?
        mol state center ligands memberships = true) :
      ValidatedMolecularPrimingFrame result mol state center ligands
        .repeatedPolydentateLigands memberships
  | fragments (fragmentDonors memberships)
      (derived : result.deriveCoordinatingFragmentPrimingMemberships?
        mol state center ligands fragmentDonors = some memberships)
      (valid : result.coordinatingFragmentPrimingMembershipsOK?
        mol state center ligands fragmentDonors memberships = true) :
      ValidatedMolecularPrimingFrame result mol state center ligands
        (.symmetryRelatedCoordinatingFragments fragmentDonors) memberships

/-- Complete source-basis and finite-numbering certificate for every successful safe polyhedral
priority result. -/
theorem ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?_sound_IR9
    (result : ChemistryNormalizationResult) (center : Nat) (geometry : PolyhedralGeometry)
    (ligands : List Nat) (priming : IndexedPolyhedralPrimingObservation)
    (priorities : List PolyhedralPriorityNumber)
    (produced : result.observedPolyhedralPriorityNumbers?
      center geometry ligands priming = some priorities) :
    ∃ memberships,
      ValidatedMolecularPrimingFrame result result.geometryPriorityState.1
        result.geometryPriorityState.2.2 center ligands priming memberships ∧
      ∃ compareAt baseNumbers primeCounts,
        result.polyhedralPriorityComparisonFrame? center geometry ligands = some compareAt ∧
        deriveDensePolyhedralBasePriorityNumbers? ligands.length compareAt = some baseNumbers ∧
        RedBookIR9.FinitePriorityNumbering ligands.length compareAt baseNumbers ∧
        canonicalPolyhedralPrimeCounts? ligands.length memberships = some primeCounts ∧
        RedBookIR9.FinitePrimingAssignment ligands.length
          (effectivePolyhedralPrimingMemberships ligands.length memberships) primeCounts ∧
        baseNumbers.zipWithM (fun number primes =>
          some { number := number, primes := primes }) primeCounts = some priorities := by
  cases priming with
  | repeatedPolydentateLigands =>
      obtain ⟨memberships, derived, valid, compareAt, baseNumbers, primeCounts,
          frameEq, baseEq, baseValid, primeEq, primeValid, zipped⟩ :=
        result.molecularPolyhedralPriorityNumbers?_sound_IR9 center geometry ligands priorities
          (by simpa [ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?] using produced)
      exact ⟨memberships, .repeated memberships derived valid, compareAt, baseNumbers,
        primeCounts, frameEq, baseEq, baseValid, primeEq, primeValid, zipped⟩
  | symmetryRelatedCoordinatingFragments fragmentDonors =>
      unfold ChemistryNormalizationResult.observedPolyhedralPriorityNumbers? at produced
      let mol := result.geometryPriorityState.1
      let state := result.geometryPriorityState.2.2
      cases membershipsEq : result.deriveCoordinatingFragmentPrimingMemberships?
          mol state center ligands fragmentDonors with
      | none => simp [mol, state, membershipsEq] at produced
      | some memberships =>
          have innerProduced :
              result.polyhedralPriorityNumbers? center geometry ligands memberships =
                some priorities := by
            simpa [mol, state, membershipsEq] using produced
          obtain ⟨compareAt, baseNumbers, primeCounts, frameEq, baseEq, baseValid,
              primeEq, primeValid, zipped⟩ :=
            result.polyhedralPriorityNumbers?_sound_IR9 center geometry ligands memberships
              priorities innerProduced
          refine ⟨memberships, ?_, compareAt, baseNumbers, primeCounts,
            frameEq, baseEq, baseValid, primeEq, primeValid, zipped⟩
          exact .fragments fragmentDonors memberships (by simpa [mol, state] using membershipsEq)
            (result.deriveCoordinatingFragmentPrimingMemberships?_sound
              mol state center ligands fragmentDonors memberships membershipsEq)

/-- End-to-end certificate at the public polyhedral assignment boundary.  Every successful output
exposes the exact molecular priming basis, independently valid finite donor numbering, accepted
absolute-distinctness gate, geometry index, absolute configuration, and emitted descriptor. -/
theorem ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?_sound_IR9
    (result : ChemistryNormalizationResult) (record : IndexedPolyhedralGeometryObservation)
    (assignment : StereoAssignment)
    (produced : result.polyhedralGeometryObservationAssignment? record = some assignment) :
    ∃ priorities memberships independentRotation? rotation? positions index absolute,
      record.geometryRecognitionOK? = true ∧
      RedBookIR9.GeometryRecognized record.recognition
        (BlueBookP93.geometryOfProduction record.geometry) ∧
      result.observedPolyhedralPriorityNumbers? record.center record.geometry
          record.ligands record.priming = some priorities ∧
      ValidatedMolecularPrimingFrame result result.geometryPriorityState.1
        result.geometryPriorityState.2.2 record.center record.ligands record.priming
        memberships ∧
      (∃ compareAt baseNumbers primeCounts,
        result.polyhedralPriorityComparisonFrame? record.center record.geometry record.ligands =
            some compareAt ∧
        deriveDensePolyhedralBasePriorityNumbers? record.ligands.length compareAt =
            some baseNumbers ∧
        RedBookIR9.FinitePriorityNumbering record.ligands.length compareAt baseNumbers ∧
        canonicalPolyhedralPrimeCounts? record.ligands.length memberships = some primeCounts ∧
        RedBookIR9.FinitePrimingAssignment record.ligands.length
          (effectivePolyhedralPrimingMemberships record.ligands.length memberships) primeCounts ∧
        baseNumbers.zipWithM (fun number primes =>
          some { number := number, primes := primes }) primeCounts = some priorities) ∧
      RedBookIR9.ConfigurationPositionsRecognized record.configurationPositions
        (BlueBookP93.geometryOfProduction record.geometry) positions ∧
      RedBookIR9.AbsoluteOrientationRecognized record.absoluteOrientation
        (BlueBookP93.geometryOfProduction record.geometry) independentRotation? ∧
      rotation? = independentRotation?.map PolyhedralRotationSense.ofIndependent ∧
      (independentRotation?.isSome &&
        priorities.eraseDups.length != priorities.length) = false ∧
      polyhedralConfigurationIndex? record.geometry priorities positions = some index ∧
      polyhedralAbsoluteConfiguration? record.geometry rotation? = some absolute ∧
      assignment =
        { unit := StereoUnit.polyhedron record.center
          outcome := StereoOutcome.polyhedral
            { geometry := record.geometry, configurationIndex := index,
              absolute? := absolute } } := by
  unfold ChemistryNormalizationResult.polyhedralGeometryObservationAssignment? at produced
  cases priorityEq : result.observedPolyhedralPriorityNumbers?
      record.center record.geometry record.ligands record.priming with
  | none => simp [priorityEq] at produced
  | some priorities =>
    cases independentRotationEq : record.absoluteOrientation.rotationFor?
        (BlueBookP93.geometryOfProduction record.geometry) with
    | none => simp [priorityEq, independentRotationEq] at produced
    | some independentRotation? =>
      let rotation? := independentRotation?.map PolyhedralRotationSense.ofIndependent
      simp [priorityEq, independentRotationEq] at produced
      have recognitionOK : record.geometryRecognitionOK? = true := produced.1
      have recognitionValid : RedBookIR9.GeometryRecognized record.recognition
          (BlueBookP93.geometryOfProduction record.geometry) :=
        (geometryRecognitionOK?_eq_true_iff_IR9 record).mp recognitionOK
      have acceptedDistinctness : independentRotation?.isSome = true →
          priorities.eraseDups.length = priorities.length := produced.2.1
      have remaining := produced.2.2
      cases positionsEq : record.configurationPositions.positionsFor?
          (BlueBookP93.geometryOfProduction record.geometry) with
      | none => simp [positionsEq] at remaining
      | some positions =>
        cases indexEq : polyhedralConfigurationIndex?
            record.geometry priorities positions with
        | none => simp [positionsEq, indexEq] at remaining
        | some index =>
          cases absoluteEq : polyhedralAbsoluteConfiguration? record.geometry rotation? with
          | none => simp [positionsEq, rotation?, absoluteEq] at remaining
          | some absolute =>
              have assignmentEq : assignment =
                  { unit := StereoUnit.polyhedron record.center
                    outcome := StereoOutcome.polyhedral
                      { geometry := record.geometry, configurationIndex := index,
                        absolute? := absolute } } := by
                simpa [positionsEq, indexEq, rotation?, absoluteEq] using remaining.symm
              have guardFalse :
                  (independentRotation?.isSome &&
                    priorities.eraseDups.length != priorities.length) = false := by
                by_cases rotationPresent : independentRotation?.isSome = true
                · have distinct := acceptedDistinctness rotationPresent
                  simp [rotationPresent, distinct]
                · have rotationAbsent : independentRotation?.isSome = false :=
                    Bool.eq_false_of_not_eq_true rotationPresent
                  simp [rotationAbsent]
              obtain ⟨memberships, validFrame, finiteCertificate⟩ :=
                result.observedPolyhedralPriorityNumbers?_sound_IR9
                  record.center record.geometry record.ligands record.priming priorities priorityEq
              exact ⟨priorities, memberships, independentRotation?, rotation?, positions,
                index, absolute, recognitionOK, recognitionValid, rfl, validFrame,
                finiteCertificate, positionsEq, independentRotationEq, rfl,
                guardFalse, indexEq, (by simpa [rotation?] using absoluteEq), assignmentEq⟩

/-- Checked package for the complete currently executable IR-9.3.5 donor-numbering layer. -/
structure SupportedDonorPriorityConformance : Prop where
  baseChecker : ∀ count compareAt numbers,
    densePolyhedralPriorityNumberingOK? count compareAt numbers = true ↔
      RedBookIR9.FinitePriorityNumbering count compareAt numbers
  baseDerivation : ∀ count compareAt numbers,
    deriveDensePolyhedralBasePriorityNumbers? count compareAt = some numbers →
      RedBookIR9.FinitePriorityNumbering count compareAt numbers
  primingChecker : ∀ donorCount memberships primeCounts,
    familyPolyhedralPrimeCountsOK? donorCount memberships primeCounts = true ↔
      RedBookIR9.FinitePrimingAssignment donorCount memberships primeCounts
  primingDerivation : ∀ donorCount memberships primeCounts,
    canonicalPolyhedralPrimeCounts? donorCount memberships = some primeCounts →
      RedBookIR9.FinitePrimingAssignment donorCount
        (effectivePolyhedralPrimingMemberships donorCount memberships) primeCounts
  molecular : ∀ result center geometry ligands primingMemberships priorities,
    ChemistryNormalizationResult.polyhedralPriorityNumbers?
        result center geometry ligands primingMemberships = some priorities →
      ∃ compareAt baseNumbers primeCounts,
        result.polyhedralPriorityComparisonFrame? center geometry ligands = some compareAt ∧
        deriveDensePolyhedralBasePriorityNumbers? ligands.length compareAt = some baseNumbers ∧
        RedBookIR9.FinitePriorityNumbering ligands.length compareAt baseNumbers ∧
        canonicalPolyhedralPrimeCounts? ligands.length primingMemberships = some primeCounts ∧
        RedBookIR9.FinitePrimingAssignment ligands.length
          (effectivePolyhedralPrimingMemberships ligands.length primingMemberships) primeCounts ∧
        baseNumbers.zipWithM (fun number primes =>
          some { number := number, primes := primes }) primeCounts = some priorities
  safeMolecular : ∀ result center geometry ligands priorities,
    ChemistryNormalizationResult.molecularPolyhedralPriorityNumbers?
        result center geometry ligands = some priorities →
      ∃ memberships,
        result.deriveRepeatedLigandPrimingMemberships?
            result.geometryPriorityState.1 result.geometryPriorityState.2.2 center ligands =
          some memberships ∧
        result.repeatedLigandPrimingMembershipsOK?
            result.geometryPriorityState.1 result.geometryPriorityState.2.2 center ligands
            memberships = true ∧
        ∃ compareAt baseNumbers primeCounts,
          result.polyhedralPriorityComparisonFrame? center geometry ligands = some compareAt ∧
          deriveDensePolyhedralBasePriorityNumbers? ligands.length compareAt = some baseNumbers ∧
          RedBookIR9.FinitePriorityNumbering ligands.length compareAt baseNumbers ∧
          canonicalPolyhedralPrimeCounts? ligands.length memberships = some primeCounts ∧
          RedBookIR9.FinitePrimingAssignment ligands.length
            (effectivePolyhedralPrimingMemberships ligands.length memberships) primeCounts ∧
          baseNumbers.zipWithM (fun number primes =>
            some { number := number, primes := primes }) primeCounts = some priorities
  safeObserved : ∀ result center geometry ligands priming priorities,
    ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?
        result center geometry ligands priming = some priorities →
      ∃ memberships,
        ValidatedMolecularPrimingFrame result result.geometryPriorityState.1
          result.geometryPriorityState.2.2 center ligands priming memberships ∧
        ∃ compareAt baseNumbers primeCounts,
          result.polyhedralPriorityComparisonFrame? center geometry ligands = some compareAt ∧
          deriveDensePolyhedralBasePriorityNumbers? ligands.length compareAt = some baseNumbers ∧
          RedBookIR9.FinitePriorityNumbering ligands.length compareAt baseNumbers ∧
          canonicalPolyhedralPrimeCounts? ligands.length memberships = some primeCounts ∧
          RedBookIR9.FinitePrimingAssignment ligands.length
            (effectivePolyhedralPrimingMemberships ligands.length memberships) primeCounts ∧
          baseNumbers.zipWithM (fun number primes =>
            some { number := number, primes := primes }) primeCounts = some priorities

theorem supportedDonorPrioritiesConform_IR9 : SupportedDonorPriorityConformance where
  baseChecker := densePolyhedralPriorityNumberingOK?_eq_true_iff_IR9
  baseDerivation := deriveDensePolyhedralBasePriorityNumbers?_sound_IR9
  primingChecker := familyPolyhedralPrimeCountsOK?_eq_true_iff_IR9
  primingDerivation := canonicalPolyhedralPrimeCounts?_sound_IR9
  molecular := ChemistryNormalizationResult.polyhedralPriorityNumbers?_sound_IR9
  safeMolecular := ChemistryNormalizationResult.molecularPolyhedralPriorityNumbers?_sound_IR9
  safeObserved := ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?_sound_IR9

/-- The production OCF-7 complete word is exactly the independently constructed mathematical
word after priority-type translation. -/
theorem ocf7MathematicalConfigurationIndex_conforms_IR9
    (cap capped0 capped1 capped2 opposite0 opposite1 opposite2 :
      PolyhedralPriorityNumber) :
    (ocf7MathematicalConfigurationIndex cap capped0 capped1 capped2
        opposite0 opposite1 opposite2).map BlueBookP93.priorityOfProduction =
      BlueBookP93.GeometryObservation.ocf7MathematicalIndex
        (BlueBookP93.priorityOfProduction cap)
        (BlueBookP93.priorityOfProduction capped0)
        (BlueBookP93.priorityOfProduction capped1)
        (BlueBookP93.priorityOfProduction capped2)
        (BlueBookP93.priorityOfProduction opposite0)
        (BlueBookP93.priorityOfProduction opposite1)
        (BlueBookP93.priorityOfProduction opposite2) := by
  have placementEq :
      (fun position => BlueBookP93.priorityOfProduction
        (SevenCoordinateMathematicalIndex.ocf7Placement cap capped0 capped1 capped2
          opposite0 opposite1 opposite2 position)) =
        BlueBookP93.GeometryObservation.ocf7Placement
          (BlueBookP93.priorityOfProduction cap)
          (BlueBookP93.priorityOfProduction capped0)
          (BlueBookP93.priorityOfProduction capped1)
          (BlueBookP93.priorityOfProduction capped2)
          (BlueBookP93.priorityOfProduction opposite0)
          (BlueBookP93.priorityOfProduction opposite1)
          (BlueBookP93.priorityOfProduction opposite2) := by
    funext position
    cases position with
    | cap => rfl
    | cappedFace corner => fin_cases corner <;> rfl
    | oppositeFace corner => fin_cases corner <;> rfl
  unfold ocf7MathematicalConfigurationIndex
  unfold RedBookIR9.FaceMonocappedOctahedron7SourceIndexCompleteness.executableFaceMonocappedOctahedronConfigurationIndex
  rw [placementEq]
  simp [BlueBookP93.GeometryObservation.ocf7MathematicalIndex, List.map_map,
    SevenCoordinateMathematicalIndex.digitToProduction,
    BlueBookP93.GeometryObservation.digitToPriorityNumber,
    BlueBookP93.priorityOfProduction]

/-- The production TPRS-7 complete word is exactly the independently constructed mathematical
word after priority-type translation. -/
theorem tprs7MathematicalConfigurationIndex_conforms_IR9
    (cap first0 first1 first2 second0 second1 second2 :
      PolyhedralPriorityNumber) :
    (tprs7MathematicalConfigurationIndex cap first0 first1 first2
        second0 second1 second2).map BlueBookP93.priorityOfProduction =
      BlueBookP93.GeometryObservation.tprs7MathematicalIndex
        (BlueBookP93.priorityOfProduction cap)
        (BlueBookP93.priorityOfProduction first0)
        (BlueBookP93.priorityOfProduction first1)
        (BlueBookP93.priorityOfProduction first2)
        (BlueBookP93.priorityOfProduction second0)
        (BlueBookP93.priorityOfProduction second1)
        (BlueBookP93.priorityOfProduction second2) := by
  have placementEq :
      (fun position => BlueBookP93.priorityOfProduction
        (SevenCoordinateMathematicalIndex.tprs7Placement cap first0 first1 first2
          second0 second1 second2 position)) =
        BlueBookP93.GeometryObservation.tprs7Placement
          (BlueBookP93.priorityOfProduction cap)
          (BlueBookP93.priorityOfProduction first0)
          (BlueBookP93.priorityOfProduction first1)
          (BlueBookP93.priorityOfProduction first2)
          (BlueBookP93.priorityOfProduction second0)
          (BlueBookP93.priorityOfProduction second1)
          (BlueBookP93.priorityOfProduction second2) := by
    funext position
    cases position with
    | cap => rfl
    | prismVertex face corner => fin_cases face <;> fin_cases corner <;> rfl
  unfold tprs7MathematicalConfigurationIndex
  unfold RedBookIR9.SquareFaceMonocappedTrigonalPrism7SourceIndexCompleteness.executableSquareFaceMonocappedTrigonalPrismConfigurationIndex
  rw [placementEq]
  simp [BlueBookP93.GeometryObservation.tprs7MathematicalIndex, List.map_map,
    SevenCoordinateMathematicalIndex.digitToProduction,
    BlueBookP93.GeometryObservation.digitToPriorityNumber,
    BlueBookP93.priorityOfProduction]

/-- The production CU-8 complete word is exactly the independently constructed 48-frame word
after priority-type translation. -/
theorem cubeMathematicalConfigurationIndex_conforms_IR9
    (v000 v001 v010 v011 v100 v101 v110 v111 : PolyhedralPriorityNumber) :
    (cubeMathematicalConfigurationIndex
        v000 v001 v010 v011 v100 v101 v110 v111).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.GeometryObservation.cubeMathematicalIndex
        (BlueBookP93.priorityOfProduction v000)
        (BlueBookP93.priorityOfProduction v001)
        (BlueBookP93.priorityOfProduction v010)
        (BlueBookP93.priorityOfProduction v011)
        (BlueBookP93.priorityOfProduction v100)
        (BlueBookP93.priorityOfProduction v101)
        (BlueBookP93.priorityOfProduction v110)
        (BlueBookP93.priorityOfProduction v111) := by
  have placementEq :
      (fun position => BlueBookP93.priorityOfProduction
        (RedBookIR9.CubeSourceIndexCompleteness.placementOfEntries
          v000 v001 v010 v011 v100 v101 v110 v111 position)) =
        RedBookIR9.CubeSourceIndexCompleteness.placementOfEntries
          (BlueBookP93.priorityOfProduction v000)
          (BlueBookP93.priorityOfProduction v001)
          (BlueBookP93.priorityOfProduction v010)
          (BlueBookP93.priorityOfProduction v011)
          (BlueBookP93.priorityOfProduction v100)
          (BlueBookP93.priorityOfProduction v101)
          (BlueBookP93.priorityOfProduction v110)
          (BlueBookP93.priorityOfProduction v111) := by
    funext position
    by_cases h0 : position 0 <;> by_cases h1 : position 1 <;>
      by_cases h2 : position 2 <;>
      simp [RedBookIR9.CubeSourceIndexCompleteness.placementOfEntries,
        h0, h1, h2, BlueBookP93.priorityOfProduction]
  unfold cubeMathematicalConfigurationIndex
  unfold RedBookIR9.CubeSourceIndexCompleteness.executableCubeConfigurationIndex
  rw [placementEq]
  simp [BlueBookP93.GeometryObservation.cubeMathematicalIndex, List.map_map,
    SevenCoordinateMathematicalIndex.digitToProduction,
    BlueBookP93.GeometryObservation.digitToPriorityNumber,
    BlueBookP93.priorityOfProduction]

/-- The production SAPR-8 complete word is exactly the independently constructed sixteen-frame
word after priority-type translation. -/
theorem squareAntiprismMathematicalConfigurationIndex_conforms_IR9
    (v0 v1 v2 v3 v4 v5 v6 v7 : PolyhedralPriorityNumber) :
    (squareAntiprismMathematicalConfigurationIndex v0 v1 v2 v3 v4 v5 v6 v7).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.GeometryObservation.squareAntiprismMathematicalIndex
        (BlueBookP93.priorityOfProduction v0)
        (BlueBookP93.priorityOfProduction v1)
        (BlueBookP93.priorityOfProduction v2)
        (BlueBookP93.priorityOfProduction v3)
        (BlueBookP93.priorityOfProduction v4)
        (BlueBookP93.priorityOfProduction v5)
        (BlueBookP93.priorityOfProduction v6)
        (BlueBookP93.priorityOfProduction v7) := by
  have placementEq :
      (fun position => BlueBookP93.priorityOfProduction
        (RedBookIR9.SquareAntiprism8SourceIndexCompleteness.placementOfEntries
          v0 v1 v2 v3 v4 v5 v6 v7 position)) =
        RedBookIR9.SquareAntiprism8SourceIndexCompleteness.placementOfEntries
          (BlueBookP93.priorityOfProduction v0)
          (BlueBookP93.priorityOfProduction v1)
          (BlueBookP93.priorityOfProduction v2)
          (BlueBookP93.priorityOfProduction v3)
          (BlueBookP93.priorityOfProduction v4)
          (BlueBookP93.priorityOfProduction v5)
          (BlueBookP93.priorityOfProduction v6)
          (BlueBookP93.priorityOfProduction v7) := by
    funext position
    fin_cases position <;> rfl
  unfold squareAntiprismMathematicalConfigurationIndex
  unfold RedBookIR9.SquareAntiprism8SourceIndexCompleteness.executableSquareAntiprismConfigurationIndex
  rw [placementEq]
  simp [BlueBookP93.GeometryObservation.squareAntiprismMathematicalIndex,
    List.map_map, SevenCoordinateMathematicalIndex.digitToProduction,
    BlueBookP93.GeometryObservation.digitToPriorityNumber,
    BlueBookP93.priorityOfProduction]

/-- The production DD-8 complete word is exactly the independently constructed eight-frame word
after priority-type translation. -/
theorem dodecahedronMathematicalConfigurationIndex_conforms_IR9
    (a0 a1 a2 a3 b0 b1 b2 b3 : PolyhedralPriorityNumber) :
    (dodecahedronMathematicalConfigurationIndex a0 a1 a2 a3 b0 b1 b2 b3).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.GeometryObservation.dodecahedronMathematicalIndex
        (BlueBookP93.priorityOfProduction a0)
        (BlueBookP93.priorityOfProduction a1)
        (BlueBookP93.priorityOfProduction a2)
        (BlueBookP93.priorityOfProduction a3)
        (BlueBookP93.priorityOfProduction b0)
        (BlueBookP93.priorityOfProduction b1)
        (BlueBookP93.priorityOfProduction b2)
        (BlueBookP93.priorityOfProduction b3) := by
  have placementEq :
      (fun position => BlueBookP93.priorityOfProduction
        (RedBookIR9.TrigonalDodecahedron8SourceIndexCompleteness.placementOfEntries
          a0 a1 a2 a3 b0 b1 b2 b3 position)) =
        RedBookIR9.TrigonalDodecahedron8SourceIndexCompleteness.placementOfEntries
          (BlueBookP93.priorityOfProduction a0)
          (BlueBookP93.priorityOfProduction a1)
          (BlueBookP93.priorityOfProduction a2)
          (BlueBookP93.priorityOfProduction a3)
          (BlueBookP93.priorityOfProduction b0)
          (BlueBookP93.priorityOfProduction b1)
          (BlueBookP93.priorityOfProduction b2)
          (BlueBookP93.priorityOfProduction b3) := by
    funext position
    rcases position with ⟨site, slot⟩
    cases site <;> fin_cases slot <;> rfl
  unfold dodecahedronMathematicalConfigurationIndex
  unfold RedBookIR9.TrigonalDodecahedron8SourceIndexCompleteness.executableDodecahedronConfigurationIndex
  rw [placementEq]
  simp [BlueBookP93.GeometryObservation.dodecahedronMathematicalIndex,
    List.map_map, SevenCoordinateMathematicalIndex.digitToProduction,
    BlueBookP93.GeometryObservation.digitToPriorityNumber,
    BlueBookP93.priorityOfProduction]

/-- The production OCT-8 complete word is exactly the independently constructed twelve-frame
word after priority-type translation. -/
theorem transBicappedOctahedronMathematicalConfigurationIndex_conforms_IR9
    (cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2 : PolyhedralPriorityNumber) :
    (transBicappedOctahedronMathematicalConfigurationIndex
        cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.GeometryObservation.transBicappedOctahedronMathematicalIndex
        (BlueBookP93.priorityOfProduction cap0)
        (BlueBookP93.priorityOfProduction cap1)
        (BlueBookP93.priorityOfProduction s0p0)
        (BlueBookP93.priorityOfProduction s0p1)
        (BlueBookP93.priorityOfProduction s0p2)
        (BlueBookP93.priorityOfProduction s1p0)
        (BlueBookP93.priorityOfProduction s1p1)
        (BlueBookP93.priorityOfProduction s1p2) := by
  have placementEq :
      (fun position => BlueBookP93.priorityOfProduction
        (RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness.placementOfEntries
          cap0 cap1 s0p0 s0p1 s0p2 s1p0 s1p1 s1p2 position)) =
        RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness.placementOfEntries
          (BlueBookP93.priorityOfProduction cap0)
          (BlueBookP93.priorityOfProduction cap1)
          (BlueBookP93.priorityOfProduction s0p0)
          (BlueBookP93.priorityOfProduction s0p1)
          (BlueBookP93.priorityOfProduction s0p2)
          (BlueBookP93.priorityOfProduction s1p0)
          (BlueBookP93.priorityOfProduction s1p1)
          (BlueBookP93.priorityOfProduction s1p2) := by
    funext position
    cases position with
    | cap side => fin_cases side <;> rfl
    | baseVertex side pair => fin_cases side <;> fin_cases pair <;> rfl
  unfold transBicappedOctahedronMathematicalConfigurationIndex
  unfold RedBookIR9.TransBicappedOctahedron8SourceIndexCompleteness.executableTransBicappedOctahedronConfigurationIndex
  rw [placementEq]
  simp [BlueBookP93.GeometryObservation.transBicappedOctahedronMathematicalIndex,
    List.map_map, SevenCoordinateMathematicalIndex.digitToProduction,
    BlueBookP93.GeometryObservation.digitToPriorityNumber,
    BlueBookP93.priorityOfProduction]

/-- The production TPRT-8 complete word is exactly the independently constructed twelve-frame
word after priority-type translation. -/
theorem triangularFaceBicappedTrigonalPrismMathematicalConfigurationIndex_conforms_IR9
    (cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : PolyhedralPriorityNumber) :
    (triangularFaceBicappedTrigonalPrismMathematicalConfigurationIndex
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.GeometryObservation.triangularFaceBicappedTrigonalPrismMathematicalIndex
        (BlueBookP93.priorityOfProduction cap0)
        (BlueBookP93.priorityOfProduction cap1)
        (BlueBookP93.priorityOfProduction f0c0)
        (BlueBookP93.priorityOfProduction f0c1)
        (BlueBookP93.priorityOfProduction f0c2)
        (BlueBookP93.priorityOfProduction f1c0)
        (BlueBookP93.priorityOfProduction f1c1)
        (BlueBookP93.priorityOfProduction f1c2) := by
  have placementEq :
      (fun position => BlueBookP93.priorityOfProduction
        (RedBookIR9.TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness.placementOfEntries
          cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 position)) =
        RedBookIR9.TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness.placementOfEntries
          (BlueBookP93.priorityOfProduction cap0)
          (BlueBookP93.priorityOfProduction cap1)
          (BlueBookP93.priorityOfProduction f0c0)
          (BlueBookP93.priorityOfProduction f0c1)
          (BlueBookP93.priorityOfProduction f0c2)
          (BlueBookP93.priorityOfProduction f1c0)
          (BlueBookP93.priorityOfProduction f1c1)
          (BlueBookP93.priorityOfProduction f1c2) := by
    funext position
    cases position with
    | cap side => fin_cases side <;> rfl
    | baseVertex side corner => fin_cases side <;> fin_cases corner <;> rfl
  unfold triangularFaceBicappedTrigonalPrismMathematicalConfigurationIndex
  unfold RedBookIR9.TriangularFaceBicappedTrigonalPrism8SourceIndexCompleteness.executableTriangularFaceBicappedTrigonalPrismConfigurationIndex
  rw [placementEq]
  simp [BlueBookP93.GeometryObservation.triangularFaceBicappedTrigonalPrismMathematicalIndex,
    List.map_map, SevenCoordinateMathematicalIndex.digitToProduction,
    BlueBookP93.GeometryObservation.digitToPriorityNumber,
    BlueBookP93.priorityOfProduction]

/-- The production TPRS-8 complete word is exactly the independently constructed four-frame
word after priority-type translation. -/
theorem squareFaceBicappedTrigonalPrismMathematicalConfigurationIndex_conforms_IR9
    (cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : PolyhedralPriorityNumber) :
    (squareFaceBicappedTrigonalPrismMathematicalConfigurationIndex
        cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.GeometryObservation.squareFaceBicappedTrigonalPrismMathematicalIndex
        (BlueBookP93.priorityOfProduction cap0)
        (BlueBookP93.priorityOfProduction cap1)
        (BlueBookP93.priorityOfProduction f0c0)
        (BlueBookP93.priorityOfProduction f0c1)
        (BlueBookP93.priorityOfProduction f0c2)
        (BlueBookP93.priorityOfProduction f1c0)
        (BlueBookP93.priorityOfProduction f1c1)
        (BlueBookP93.priorityOfProduction f1c2) := by
  have placementEq :
      (fun position => BlueBookP93.priorityOfProduction
        (RedBookIR9.SquareFaceBicappedTrigonalPrism8SourceIndexCompleteness.placementOfEntries
          cap0 cap1 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 position)) =
        RedBookIR9.SquareFaceBicappedTrigonalPrism8SourceIndexCompleteness.placementOfEntries
          (BlueBookP93.priorityOfProduction cap0)
          (BlueBookP93.priorityOfProduction cap1)
          (BlueBookP93.priorityOfProduction f0c0)
          (BlueBookP93.priorityOfProduction f0c1)
          (BlueBookP93.priorityOfProduction f0c2)
          (BlueBookP93.priorityOfProduction f1c0)
          (BlueBookP93.priorityOfProduction f1c1)
          (BlueBookP93.priorityOfProduction f1c2) := by
    funext position
    cases position with
    | cap selectedFace => fin_cases selectedFace <;> rfl
    | prismVertex face corner => fin_cases face <;> fin_cases corner <;> rfl
  unfold squareFaceBicappedTrigonalPrismMathematicalConfigurationIndex
  unfold RedBookIR9.SquareFaceBicappedTrigonalPrism8SourceIndexCompleteness.executableSquareFaceBicappedTrigonalPrismConfigurationIndex
  rw [placementEq]
  simp [BlueBookP93.GeometryObservation.squareFaceBicappedTrigonalPrismMathematicalIndex,
    List.map_map, SevenCoordinateMathematicalIndex.digitToProduction,
    BlueBookP93.GeometryObservation.digitToPriorityNumber,
    BlueBookP93.priorityOfProduction]

/-- The production TPRS-9 complete word is exactly the independently constructed twelve-frame
word after priority-type translation. -/
theorem squareFaceTricappedTrigonalPrismMathematicalConfigurationIndex_conforms_IR9
    (cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 : PolyhedralPriorityNumber) :
    (squareFaceTricappedTrigonalPrismMathematicalConfigurationIndex
        cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2).map
        BlueBookP93.priorityOfProduction =
      BlueBookP93.GeometryObservation.squareFaceTricappedTrigonalPrismMathematicalIndex
        (BlueBookP93.priorityOfProduction cap0)
        (BlueBookP93.priorityOfProduction cap1)
        (BlueBookP93.priorityOfProduction cap2)
        (BlueBookP93.priorityOfProduction f0c0)
        (BlueBookP93.priorityOfProduction f0c1)
        (BlueBookP93.priorityOfProduction f0c2)
        (BlueBookP93.priorityOfProduction f1c0)
        (BlueBookP93.priorityOfProduction f1c1)
        (BlueBookP93.priorityOfProduction f1c2) := by
  have placementEq :
      (fun position => BlueBookP93.priorityOfProduction
        (RedBookIR9.SquareFaceTricappedTrigonalPrism9SourceIndexCompleteness.placementOfEntries
          cap0 cap1 cap2 f0c0 f0c1 f0c2 f1c0 f1c1 f1c2 position)) =
        RedBookIR9.SquareFaceTricappedTrigonalPrism9SourceIndexCompleteness.placementOfEntries
          (BlueBookP93.priorityOfProduction cap0)
          (BlueBookP93.priorityOfProduction cap1)
          (BlueBookP93.priorityOfProduction cap2)
          (BlueBookP93.priorityOfProduction f0c0)
          (BlueBookP93.priorityOfProduction f0c1)
          (BlueBookP93.priorityOfProduction f0c2)
          (BlueBookP93.priorityOfProduction f1c0)
          (BlueBookP93.priorityOfProduction f1c1)
          (BlueBookP93.priorityOfProduction f1c2) := by
    funext position
    cases position with
    | cap squareFace => fin_cases squareFace <;> rfl
    | prismVertex face corner => fin_cases face <;> fin_cases corner <;> rfl
  unfold squareFaceTricappedTrigonalPrismMathematicalConfigurationIndex
  unfold RedBookIR9.SquareFaceTricappedTrigonalPrism9SourceIndexCompleteness.executableSquareFaceTricappedTrigonalPrismConfigurationIndex
  rw [placementEq]
  simp [BlueBookP93.GeometryObservation.squareFaceTricappedTrigonalPrismMathematicalIndex,
    List.map_map, SevenCoordinateMathematicalIndex.digitToProduction,
    BlueBookP93.GeometryObservation.digitToPriorityNumber,
    BlueBookP93.priorityOfProduction]

/-- Production and the independent P-93/IR-9 router expose exactly the same implemented
configuration-index domain. -/
theorem polyhedralConfigurationIndexArity?_conforms_P93_IR9
    (geometry : PolyhedralGeometry) :
    geometry.configurationIndexArity? =
      BlueBookP93.GeometryObservation.configurationIndexArity?
        (BlueBookP93.geometryOfProduction geometry) := by
  cases geometry <;> rfl

/-- Mapping a production priority list into the independent priority-number type commutes with
looking up all geometry-selected positions. -/
private theorem map_priority_position_lookups
    (priorities : List PolyhedralPriorityNumber) (positions : List ℕ) :
    ((positions.mapM fun position => priorities[position]?).map
        (List.map BlueBookP93.priorityOfProduction)) =
      positions.mapM fun position =>
        (priorities.map BlueBookP93.priorityOfProduction)[position]? := by
  induction positions with
  | nil => rfl
  | cons position positions inductionHypothesis =>
      simp only [List.mapM_cons, List.getElem?_map]
      have normalizedInductionHypothesis :
          ((positions.mapM fun position => priorities[position]?).map
              (List.map BlueBookP93.priorityOfProduction)) =
            positions.mapM fun position =>
              Option.map BlueBookP93.priorityOfProduction priorities[position]? := by
        simpa only [List.getElem?_map] using inductionHypothesis
      cases positionLookup : priorities[position]? <;>
        cases restLookup : positions.mapM (fun position => priorities[position]?) <;>
        simp_all <;> rw [← inductionHypothesis] <;> rfl

/-- The six-position trigonal-prism router agrees even off its exact input arity.  Splitting this
case out keeps the general router proof structural: unlike the bipyramidal constructors, a
trigonal prism accepts exactly six entries rather than every list with a two-entry prefix. -/
private theorem trigonalPrismConfigurationIndexOfEntries?_conforms_P93_IR9
    (entries : List PolyhedralPriorityNumber) :
    (polyhedralConfigurationIndexOfEntries? .trigonalPrism entries).map
        (List.map (List.map BlueBookP93.priorityOfProduction)) =
      BlueBookP93.GeometryObservation.configurationIndexOfEntries?
        .trigonalPrism (entries.map BlueBookP93.priorityOfProduction) := by
  cases entries with
  | nil => rfl
  | cons first rest =>
      cases rest with
      | nil => rfl
      | cons second rest =>
          cases rest with
          | nil => rfl
          | cons third rest =>
              cases rest with
              | nil => rfl
              | cons fourth rest =>
                  cases rest with
                  | nil => rfl
                  | cons fifth rest =>
                      cases rest with
                      | nil => rfl
                      | cons sixth rest =>
                          cases rest with
                          | nil =>
                              simp [polyhedralConfigurationIndexOfEntries?,
                                BlueBookP93.GeometryObservation.configurationIndexOfEntries?,
                                trigonalPrismConfigurationIndex_conforms_IR9]
                          | cons seventh rest => rfl

/-- The exact-seven OCF-7 constructor agrees for every possible entry-list shape. -/
private theorem ocf7ConfigurationIndexOfEntries?_conforms_P93_IR9
    (entries : List PolyhedralPriorityNumber) :
    (polyhedralConfigurationIndexOfEntries? .faceMonocappedOctahedron entries).map
        (List.map (List.map BlueBookP93.priorityOfProduction)) =
      BlueBookP93.GeometryObservation.configurationIndexOfEntries?
        .faceMonocappedOctahedron
        (entries.map BlueBookP93.priorityOfProduction) := by
  cases entries with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => cases rest with
      | nil => rfl
      | cons third rest => cases rest with
        | nil => rfl
        | cons fourth rest => cases rest with
          | nil => rfl
          | cons fifth rest => cases rest with
            | nil => rfl
            | cons sixth rest => cases rest with
              | nil => rfl
              | cons seventh rest => cases rest with
                | nil =>
                    simp [polyhedralConfigurationIndexOfEntries?,
                      BlueBookP93.GeometryObservation.configurationIndexOfEntries?,
                      ocf7MathematicalConfigurationIndex_conforms_IR9]
                | cons eighth rest => rfl

/-- The exact-seven TPRS-7 constructor agrees for every possible entry-list shape. -/
private theorem tprs7ConfigurationIndexOfEntries?_conforms_P93_IR9
    (entries : List PolyhedralPriorityNumber) :
    (polyhedralConfigurationIndexOfEntries?
        .squareFaceMonocappedTrigonalPrism entries).map
        (List.map (List.map BlueBookP93.priorityOfProduction)) =
      BlueBookP93.GeometryObservation.configurationIndexOfEntries?
        .squareFaceMonocappedTrigonalPrism
        (entries.map BlueBookP93.priorityOfProduction) := by
  cases entries with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => cases rest with
      | nil => rfl
      | cons third rest => cases rest with
        | nil => rfl
        | cons fourth rest => cases rest with
          | nil => rfl
          | cons fifth rest => cases rest with
            | nil => rfl
            | cons sixth rest => cases rest with
              | nil => rfl
              | cons seventh rest => cases rest with
                | nil =>
                    simp [polyhedralConfigurationIndexOfEntries?,
                      BlueBookP93.GeometryObservation.configurationIndexOfEntries?,
                      tprs7MathematicalConfigurationIndex_conforms_IR9]
                | cons eighth rest => rfl

/-- The exact-eight CU-8 constructor agrees for every possible entry-list shape. -/
private theorem cubeConfigurationIndexOfEntries?_conforms_P93_IR9
    (entries : List PolyhedralPriorityNumber) :
    (polyhedralConfigurationIndexOfEntries? .cube entries).map
        (List.map (List.map BlueBookP93.priorityOfProduction)) =
      BlueBookP93.GeometryObservation.configurationIndexOfEntries? .cube
        (entries.map BlueBookP93.priorityOfProduction) := by
  cases entries with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => cases rest with
      | nil => rfl
      | cons third rest => cases rest with
        | nil => rfl
        | cons fourth rest => cases rest with
          | nil => rfl
          | cons fifth rest => cases rest with
            | nil => rfl
            | cons sixth rest => cases rest with
              | nil => rfl
              | cons seventh rest => cases rest with
                | nil => rfl
                | cons eighth rest => cases rest with
                  | nil =>
                      simp [polyhedralConfigurationIndexOfEntries?,
                        BlueBookP93.GeometryObservation.configurationIndexOfEntries?,
                        cubeMathematicalConfigurationIndex_conforms_IR9]
                  | cons ninth rest => rfl

/-- The exact-eight SAPR-8 constructor agrees for every possible entry-list shape. -/
private theorem squareAntiprismConfigurationIndexOfEntries?_conforms_P93_IR9
    (entries : List PolyhedralPriorityNumber) :
    (polyhedralConfigurationIndexOfEntries? .squareAntiprism entries).map
        (List.map (List.map BlueBookP93.priorityOfProduction)) =
      BlueBookP93.GeometryObservation.configurationIndexOfEntries? .squareAntiprism
        (entries.map BlueBookP93.priorityOfProduction) := by
  cases entries with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => cases rest with
      | nil => rfl
      | cons third rest => cases rest with
        | nil => rfl
        | cons fourth rest => cases rest with
          | nil => rfl
          | cons fifth rest => cases rest with
            | nil => rfl
            | cons sixth rest => cases rest with
              | nil => rfl
              | cons seventh rest => cases rest with
                | nil => rfl
                | cons eighth rest => cases rest with
                  | nil =>
                      simp [polyhedralConfigurationIndexOfEntries?,
                        BlueBookP93.GeometryObservation.configurationIndexOfEntries?,
                        squareAntiprismMathematicalConfigurationIndex_conforms_IR9]
                  | cons ninth rest => rfl

/-- The exact-eight DD-8 constructor agrees for every possible entry-list shape. -/
private theorem dodecahedronConfigurationIndexOfEntries?_conforms_P93_IR9
    (entries : List PolyhedralPriorityNumber) :
    (polyhedralConfigurationIndexOfEntries? .dodecahedron entries).map
        (List.map (List.map BlueBookP93.priorityOfProduction)) =
      BlueBookP93.GeometryObservation.configurationIndexOfEntries? .dodecahedron
        (entries.map BlueBookP93.priorityOfProduction) := by
  cases entries with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => cases rest with
      | nil => rfl
      | cons third rest => cases rest with
        | nil => rfl
        | cons fourth rest => cases rest with
          | nil => rfl
          | cons fifth rest => cases rest with
            | nil => rfl
            | cons sixth rest => cases rest with
              | nil => rfl
              | cons seventh rest => cases rest with
                | nil => rfl
                | cons eighth rest => cases rest with
                  | nil =>
                      simp [polyhedralConfigurationIndexOfEntries?,
                        BlueBookP93.GeometryObservation.configurationIndexOfEntries?,
                        dodecahedronMathematicalConfigurationIndex_conforms_IR9]
                  | cons ninth rest => rfl

/-- The exact-eight OCT-8 constructor agrees for every possible entry-list shape. -/
private theorem transBicappedOctahedronConfigurationIndexOfEntries?_conforms_P93_IR9
    (entries : List PolyhedralPriorityNumber) :
    (polyhedralConfigurationIndexOfEntries? .transBicappedOctahedron entries).map
        (List.map (List.map BlueBookP93.priorityOfProduction)) =
      BlueBookP93.GeometryObservation.configurationIndexOfEntries?
        .transBicappedOctahedron (entries.map BlueBookP93.priorityOfProduction) := by
  cases entries with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => cases rest with
      | nil => rfl
      | cons third rest => cases rest with
        | nil => rfl
        | cons fourth rest => cases rest with
          | nil => rfl
          | cons fifth rest => cases rest with
            | nil => rfl
            | cons sixth rest => cases rest with
              | nil => rfl
              | cons seventh rest => cases rest with
                | nil => rfl
                | cons eighth rest => cases rest with
                  | nil =>
                      simp [polyhedralConfigurationIndexOfEntries?,
                        BlueBookP93.GeometryObservation.configurationIndexOfEntries?,
                        transBicappedOctahedronMathematicalConfigurationIndex_conforms_IR9]
                  | cons ninth rest => rfl

/-- The exact-eight TPRT-8 constructor agrees for every possible entry-list shape. -/
private theorem triangularFaceBicappedTrigonalPrismConfigurationIndexOfEntries?_conforms_P93_IR9
    (entries : List PolyhedralPriorityNumber) :
    (polyhedralConfigurationIndexOfEntries?
        .triangularFaceBicappedTrigonalPrism entries).map
        (List.map (List.map BlueBookP93.priorityOfProduction)) =
      BlueBookP93.GeometryObservation.configurationIndexOfEntries?
        .triangularFaceBicappedTrigonalPrism
        (entries.map BlueBookP93.priorityOfProduction) := by
  cases entries with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => cases rest with
      | nil => rfl
      | cons third rest => cases rest with
        | nil => rfl
        | cons fourth rest => cases rest with
          | nil => rfl
          | cons fifth rest => cases rest with
            | nil => rfl
            | cons sixth rest => cases rest with
              | nil => rfl
              | cons seventh rest => cases rest with
                | nil => rfl
                | cons eighth rest => cases rest with
                  | nil =>
                      simp [polyhedralConfigurationIndexOfEntries?,
                        BlueBookP93.GeometryObservation.configurationIndexOfEntries?,
                        triangularFaceBicappedTrigonalPrismMathematicalConfigurationIndex_conforms_IR9]
                  | cons ninth rest => rfl

/-- The exact-eight TPRS-8 constructor agrees for every possible entry-list shape. -/
private theorem squareFaceBicappedTrigonalPrismConfigurationIndexOfEntries?_conforms_P93_IR9
    (entries : List PolyhedralPriorityNumber) :
    (polyhedralConfigurationIndexOfEntries?
        .squareFaceBicappedTrigonalPrism entries).map
        (List.map (List.map BlueBookP93.priorityOfProduction)) =
      BlueBookP93.GeometryObservation.configurationIndexOfEntries?
        .squareFaceBicappedTrigonalPrism
        (entries.map BlueBookP93.priorityOfProduction) := by
  cases entries with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => cases rest with
      | nil => rfl
      | cons third rest => cases rest with
        | nil => rfl
        | cons fourth rest => cases rest with
          | nil => rfl
          | cons fifth rest => cases rest with
            | nil => rfl
            | cons sixth rest => cases rest with
              | nil => rfl
              | cons seventh rest => cases rest with
                | nil => rfl
                | cons eighth rest => cases rest with
                  | nil =>
                      simp [polyhedralConfigurationIndexOfEntries?,
                        BlueBookP93.GeometryObservation.configurationIndexOfEntries?,
                        squareFaceBicappedTrigonalPrismMathematicalConfigurationIndex_conforms_IR9]
                  | cons ninth rest => rfl

/-- The exact-nine TPRS-9 constructor agrees for every possible entry-list shape. -/
private theorem squareFaceTricappedTrigonalPrismConfigurationIndexOfEntries?_conforms_P93_IR9
    (entries : List PolyhedralPriorityNumber) :
    (polyhedralConfigurationIndexOfEntries?
        .squareFaceTricappedTrigonalPrism entries).map
        (List.map (List.map BlueBookP93.priorityOfProduction)) =
      BlueBookP93.GeometryObservation.configurationIndexOfEntries?
        .squareFaceTricappedTrigonalPrism
        (entries.map BlueBookP93.priorityOfProduction) := by
  cases entries with
  | nil => rfl
  | cons first rest => cases rest with
    | nil => rfl
    | cons second rest => cases rest with
      | nil => rfl
      | cons third rest => cases rest with
        | nil => rfl
        | cons fourth rest => cases rest with
          | nil => rfl
          | cons fifth rest => cases rest with
            | nil => rfl
            | cons sixth rest => cases rest with
              | nil => rfl
              | cons seventh rest => cases rest with
                | nil => rfl
                | cons eighth rest => cases rest with
                  | nil => rfl
                  | cons ninth rest => cases rest with
                    | nil =>
                        simp [polyhedralConfigurationIndexOfEntries?,
                          BlueBookP93.GeometryObservation.configurationIndexOfEntries?,
                          squareFaceTricappedTrigonalPrismMathematicalConfigurationIndex_conforms_IR9]
                    | cons tenth rest => rfl

/-- The pure geometry-index constructor agrees for every possible entry list. -/
private theorem polyhedralConfigurationIndexOfEntries?_conforms_P93_IR9
    (geometry : PolyhedralGeometry) (entries : List PolyhedralPriorityNumber) :
    (polyhedralConfigurationIndexOfEntries? geometry entries).map
        (List.map (List.map BlueBookP93.priorityOfProduction)) =
      BlueBookP93.GeometryObservation.configurationIndexOfEntries?
        (BlueBookP93.geometryOfProduction geometry)
        (entries.map BlueBookP93.priorityOfProduction) := by
  cases geometry <;>
    first
    | exact trigonalPrismConfigurationIndexOfEntries?_conforms_P93_IR9 entries
    | exact ocf7ConfigurationIndexOfEntries?_conforms_P93_IR9 entries
    | exact tprs7ConfigurationIndexOfEntries?_conforms_P93_IR9 entries
    | exact cubeConfigurationIndexOfEntries?_conforms_P93_IR9 entries
    | exact squareAntiprismConfigurationIndexOfEntries?_conforms_P93_IR9 entries
    | exact dodecahedronConfigurationIndexOfEntries?_conforms_P93_IR9 entries
    | exact transBicappedOctahedronConfigurationIndexOfEntries?_conforms_P93_IR9 entries
    | exact triangularFaceBicappedTrigonalPrismConfigurationIndexOfEntries?_conforms_P93_IR9 entries
    | exact squareFaceBicappedTrigonalPrismConfigurationIndexOfEntries?_conforms_P93_IR9 entries
    | exact squareFaceTricappedTrigonalPrismConfigurationIndexOfEntries?_conforms_P93_IR9 entries
    | cases entries with
      | nil => rfl
      | cons first rest =>
          cases rest with
          | nil =>
              simp [polyhedralConfigurationIndexOfEntries?,
                BlueBookP93.GeometryObservation.configurationIndexOfEntries?,
                BlueBookP93.geometryOfProduction,
                tShapeConfigurationIndex_conforms_P93,
                squarePlanarConfigurationIndex_conforms_IR9,
                squarePyramid4ConfigurationIndex_conforms_IR9]
          | cons second tail =>
              cases tail with
              | nil =>
                  simp [polyhedralConfigurationIndexOfEntries?,
                    BlueBookP93.GeometryObservation.configurationIndexOfEntries?,
                    BlueBookP93.geometryOfProduction,
                    seeSawConfigurationIndex_conforms_P93,
                    trigonalBipyramidConfigurationIndex_conforms_P93,
                    squarePyramidConfigurationIndex_conforms_P93,
                    octahedronConfigurationIndex_conforms_P93,
                    bipyramidalConfigurationIndex_conforms_IR9]
              | cons third tail =>
                  simp [polyhedralConfigurationIndexOfEntries?,
                    BlueBookP93.GeometryObservation.configurationIndexOfEntries?,
                    BlueBookP93.geometryOfProduction,
                    bipyramidalConfigurationIndex_conforms_IR9]

/-- Every configuration-index routing decision—including every conservative refusal—agrees with
the independently transcribed P-93/IR-9 construction on the currently implemented domain. -/
theorem polyhedralConfigurationIndex?_conforms_P93_IR9
    (geometry : PolyhedralGeometry) (priorities : List PolyhedralPriorityNumber)
    (positions : List ℕ) :
    (polyhedralConfigurationIndex? geometry priorities positions).map
        (List.map (List.map BlueBookP93.priorityOfProduction)) =
      BlueBookP93.GeometryObservation.configurationIndex?
        (BlueBookP93.geometryOfProduction geometry)
        (priorities.map BlueBookP93.priorityOfProduction) positions := by
  unfold polyhedralConfigurationIndex?
    BlueBookP93.GeometryObservation.configurationIndex?
  rw [polyhedralConfigurationIndexArity?_conforms_P93_IR9]
  generalize arityEquation :
      BlueBookP93.GeometryObservation.configurationIndexArity?
        (BlueBookP93.geometryOfProduction geometry) = arity
  cases arity with
  | none => rfl
  | some arity =>
      change
        Option.map (List.map (List.map BlueBookP93.priorityOfProduction))
            (if positions.length != arity ||
                  positions.eraseDups.length != positions.length then none
              else (positions.mapM fun position => priorities[position]?).bind fun entries =>
                polyhedralConfigurationIndexOfEntries? geometry entries) =
          (if positions.length != arity ||
                positions.eraseDups.length != positions.length then none
            else (positions.mapM fun position =>
              (priorities.map BlueBookP93.priorityOfProduction)[position]?).bind fun entries =>
                BlueBookP93.GeometryObservation.configurationIndexOfEntries?
                  (BlueBookP93.geometryOfProduction geometry) entries)
      split
      · rfl
      ·
        cases entryLookup : positions.mapM (fun position => priorities[position]?) with
        | none =>
            rw [← map_priority_position_lookups priorities positions]
            simp [entryLookup]
        | some entries =>
            rw [← map_priority_position_lookups priorities positions]
            simpa [entryLookup] using
              polyhedralConfigurationIndexOfEntries?_conforms_P93_IR9 geometry entries

/-- Map a production absolute descriptor into the independent result family. -/
def PolyhedralAbsoluteConfiguration.toIndependent :
    PolyhedralAbsoluteConfiguration → BlueBookP93.GeometryObservation.AbsoluteConfiguration
  | .rs descriptor => .rs descriptor
  | .ac .A => .ca .A
  | .ac .C => .ca .C

/-- Every supported production absolute-configuration routing decision agrees extensionally with
the independent geometry-indexed P-93/IR-9 semantics. -/
theorem polyhedralAbsoluteConfiguration?_conforms_P93_IR9
    (geometry : PolyhedralGeometry) (rotation? : Option PolyhedralRotationSense) :
    (polyhedralAbsoluteConfiguration? geometry rotation?).map
        (Option.map PolyhedralAbsoluteConfiguration.toIndependent) =
      BlueBookP93.GeometryObservation.absoluteConfiguration?
        (BlueBookP93.geometryOfProduction geometry)
        (rotation?.map BlueBookP93.rotationOfProduction) := by
  cases geometry <;> cases rotation? with
  | none => rfl
  | some sense => cases sense <;> rfl

/-- In particular, the production TPY-3 rotation rule is exactly the independent IR-9 notional
tetrahedron construction with a lowest-priority lone-pair phantom. -/
theorem trigonalPyramidDescriptorOfRotation_conforms_IR9
    (sense : PolyhedralRotationSense) :
    trigonalPyramidDescriptorOfRotation sense =
      RedBookIR9.trigonalPyramidalRS
        { sequenceFromPriorityOne := BlueBookP93.rotationOfProduction sense
          viewedFromCenterTowardLeastPreferred := True
          phantomSite := .lonePairSite
          phantomHasLowestPriority := True } := by
  cases sense <;> rfl

/-- The production TPR-6 `A/C` symbol is exactly the independently transcribed IR-9.3.4.9
reading: viewed from the preferred triangular face, clockwise progression on the opposite face is
`C` and counterclockwise progression is `A`. -/
theorem trigonalPrismSymbolOfRotation_conforms_IR9
    (sense : PolyhedralRotationSense) :
    PolyhedralAbsoluteConfiguration.toIndependent
        (.ac (PolyhedralChiralitySymbol.ofRotation sense)) =
      .ca (RedBookIR9.trigonalPrismCASymbol
        { preferredFaceHasGreaterHighPriorityCount := True
          viewedFromAbovePreferredFace := True
          oppositeFacePriorityProgression := BlueBookP93.rotationOfProduction sense }) := by
  cases sense <;> rfl

/-- Exact success theorem for the six-position TPR-6 configuration-index router.  It states the
whole admissibility boundary explicitly: the six observed prism vertices are distinct and all six
priority lookups succeed in corresponding-face order. -/
theorem trigonalPrismConfigurationIndex?_exact
    (priorities : List PolyhedralPriorityNumber)
    (first0 first1 first2 second0 second1 second2 : Nat)
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber)
    (positionsDistinct :
      [first0, first1, first2, second0, second1, second2].eraseDups.length = 6)
    (lookups :
      [first0, first1, first2, second0, second1, second2].mapM
          (fun position => priorities[position]?) =
        some [priority0, priority1, priority2, priority3, priority4, priority5]) :
    polyhedralConfigurationIndex? .trigonalPrism priorities
        [first0, first1, first2, second0, second1, second2] =
      some [trigonalPrismConfigurationIndex
        [priority0, priority1, priority2] [priority3, priority4, priority5]] := by
  simp [polyhedralConfigurationIndex?, PolyhedralGeometry.configurationIndexArity?,
    positionsDistinct, lookups, polyhedralConfigurationIndexOfEntries?]

/-- Exact assignment theorem for a successfully CIP-ranked trigonal-pyramidal observation.

The observation supplies the TPY-3 geometry and rotation only.  The hypotheses record the
internally derived priority-number list and its required pairwise distinctness.  Production then
emits the empty TPY-3
configuration index and exactly the independent IR-9 `R/S` descriptor. -/
theorem trigonalPyramidalGeometryObservationAssignment_exact
    (result : ChemistryNormalizationResult) (center : Nat) (ligands : List Nat)
    (sense : PolyhedralRotationSense) (priorities : List PolyhedralPriorityNumber)
    (priorityEq :
      result.molecularPolyhedralPriorityNumbers? center .trigonalPyramid ligands = some priorities)
    (prioritiesDistinct : priorities.eraseDups.length = priorities.length) :
    result.polyhedralGeometryObservationAssignment?
        { center := center
          geometry := .trigonalPyramid
          recognition := .threeCoordinate .centerSignificantlyOutOfDonorPlane
          ligands := ligands
          configurationPositions := .noDistinguishedPositions
          absoluteOrientation := .trigonalPyramidRS
            (BlueBookP93.rotationOfProduction sense) } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .trigonalPyramid
              configurationIndex := []
              absolute? := some (.rs
                (RedBookIR9.trigonalPyramidalRS
                  { sequenceFromPriorityOne := BlueBookP93.rotationOfProduction sense
                    viewedFromCenterTowardLeastPreferred := True
                    phantomSite := .lonePairSite
                    phantomHasLowestPriority := True })) } } := by
  cases sense <;>
    simp [ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?,
      IndexedPolyhedralGeometryObservation.geometryRecognitionOK?,
      RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
      RedBookIR9.geometryOfThreeCoordinateObservation,
      RedBookIR9.ConfigurationPositionObservation.positionsFor?,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?,
      BlueBookP93.geometryOfProduction,
      PolyhedralRotationSense.ofIndependent,
      ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?, priorityEq,
      prioritiesDistinct,
      polyhedralConfigurationIndex?, polyhedralConfigurationIndexOfEntries?,
      PolyhedralGeometry.configurationIndexArity?,
      polyhedralAbsoluteConfiguration?, trigonalPyramidDescriptorOfRotation,
      BlueBookP93.rotationOfProduction, RedBookIR9.trigonalPyramidalRS,
      RedBookIR9.tetrahedralRS]

/-- Exact end-to-end assignment theorem for a molecularly ranked TPR-6 observation.

The importer supplies only the recognized prism, its two corresponding triangular faces, and the
IR-9.3.4.9 reading sense.  Molecular CIP analysis supplies all six priority numbers.  Under the
two necessary admissibility facts—distinct absolute priorities and six distinct in-range observed
positions—the public pipeline emits exactly the source-defined three-number prism index and the
source-defined `A/C` symbol. -/
theorem trigonalPrismGeometryObservationAssignment_exact
    (result : ChemistryNormalizationResult) (center : Nat) (ligands : List Nat)
    (sense : PolyhedralRotationSense) (priorities : List PolyhedralPriorityNumber)
    (first0 first1 first2 second0 second1 second2 : Nat)
    (priority0 priority1 priority2 priority3 priority4 priority5 :
      PolyhedralPriorityNumber)
    (priorityEq :
      result.molecularPolyhedralPriorityNumbers? center .trigonalPrism ligands = some priorities)
    (prioritiesDistinct : priorities.eraseDups.length = priorities.length)
    (positionsDistinct :
      [first0, first1, first2, second0, second1, second2].eraseDups.length = 6)
    (lookups :
      [first0, first1, first2, second0, second1, second2].mapM
          (fun position => priorities[position]?) =
        some [priority0, priority1, priority2, priority3, priority4, priority5]) :
    result.polyhedralGeometryObservationAssignment?
        { center := center
          geometry := .trigonalPrism
          recognition := .higherCoordinationNearestIdealized .trigonalPrism
          ligands := ligands
          configurationPositions := .trigonalPrism
            [first0, first1, first2] [second0, second1, second2]
          absoluteOrientation := .trigonalPrismAC
            (BlueBookP93.rotationOfProduction sense) } =
      some
        { unit := StereoUnit.polyhedron center
          outcome := StereoOutcome.polyhedral
            { geometry := .trigonalPrism
              configurationIndex := [trigonalPrismConfigurationIndex
                [priority0, priority1, priority2] [priority3, priority4, priority5]]
              absolute? := some (.ac (PolyhedralChiralitySymbol.ofRotation sense)) } } := by
  have indexEq := trigonalPrismConfigurationIndex?_exact priorities
    first0 first1 first2 second0 second1 second2
    priority0 priority1 priority2 priority3 priority4 priority5
    positionsDistinct lookups
  cases sense <;>
    simp [ChemistryNormalizationResult.polyhedralGeometryObservationAssignment?,
      IndexedPolyhedralGeometryObservation.geometryRecognitionOK?,
      RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
      BlueBookP93.Geometry.coordinationNumber,
      RedBookIR9.ConfigurationPositionObservation.positionsFor?,
      RedBookIR9.AbsoluteOrientationObservation.rotationFor?,
      BlueBookP93.geometryOfProduction,
      PolyhedralRotationSense.ofIndependent,
      ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?, priorityEq,
      prioritiesDistinct,
      indexEq,
      polyhedralAbsoluteConfiguration?, PolyhedralChiralitySymbol.ofRotation,
      BlueBookP93.rotationOfProduction]

/-- The public pipeline cannot successfully reinterpret a nontriangular `2+4`, `1+5`, or other
six-position partition as the two faces of TPR-6.  This is the necessary half of the exact face
shape boundary, derived from the end-to-end soundness certificate. -/
theorem trigonalPrismGeometryObservationAssignment_success_faces_are_triangles
    (result : ChemistryNormalizationResult) (center : Nat) (ligands : List Nat)
    (recognition : RedBookIR9.GeometryRecognitionObservation)
    (firstFace secondFace : List Nat)
    (absoluteOrientation : RedBookIR9.AbsoluteOrientationObservation)
    (priming : IndexedPolyhedralPrimingObservation)
    (assignment : StereoAssignment)
    (produced :
      result.polyhedralGeometryObservationAssignment?
          { center := center
            geometry := .trigonalPrism
            recognition := recognition
            ligands := ligands
            configurationPositions := .trigonalPrism firstFace secondFace
            absoluteOrientation := absoluteOrientation
            priming := priming } = some assignment) :
    firstFace.length = 3 ∧ secondFace.length = 3 := by
  obtain ⟨priorities, memberships, independentRotation?, rotation?, positions, index, absolute,
      recognitionOK, recognitionValid, priorityEq, validFrame, finiteCertificate,
      positionsRecognized, orientationRecognized, rotationEq, guardFalse, indexEq,
      absoluteEq, assignmentEq⟩ :=
    result.polyhedralGeometryObservationAssignment?_sound_IR9
      { center := center
        geometry := .trigonalPrism
        recognition := recognition
        ligands := ligands
        configurationPositions := .trigonalPrism firstFace secondFace
        absoluteOrientation := absoluteOrientation
        priming := priming }
      assignment produced
  have exactShape := (RedBookIR9.trigonalPrism_positionsFor?_eq_some_iff
    firstFace secondFace positions).mp (by simpa using positionsRecognized)
  exact ⟨exactShape.1, exactShape.2.1⟩

/-- Checked bundle for the currently connected geometry-to-absolute-descriptor layer. -/
structure SupportedGeometryDescriptorConformance : Prop where
  primingFamilies : ∀ donorCount memberships,
    canonicalPolyhedralPrimeCounts? donorCount memberships =
      BlueBookP93.GeometryObservation.canonicalPrimeCounts? donorCount memberships
  configurationIndexArity : ∀ geometry,
    geometry.configurationIndexArity? =
      BlueBookP93.GeometryObservation.configurationIndexArity?
        (BlueBookP93.geometryOfProduction geometry)
  configurationIndexRouting : ∀ geometry priorities positions,
    (polyhedralConfigurationIndex? geometry priorities positions).map
        (List.map (List.map BlueBookP93.priorityOfProduction)) =
      BlueBookP93.GeometryObservation.configurationIndex?
        (BlueBookP93.geometryOfProduction geometry)
        (priorities.map BlueBookP93.priorityOfProduction) positions
  absoluteRouting : ∀ geometry rotation?,
    (polyhedralAbsoluteConfiguration? geometry rotation?).map
        (Option.map PolyhedralAbsoluteConfiguration.toIndependent) =
      BlueBookP93.GeometryObservation.absoluteConfiguration?
        (BlueBookP93.geometryOfProduction geometry)
        (rotation?.map BlueBookP93.rotationOfProduction)
  trigonalPyramid : ∀ (result : ChemistryNormalizationResult) (center : Nat)
      (ligands : List Nat) (sense : PolyhedralRotationSense)
      (priorities : List PolyhedralPriorityNumber),
    result.molecularPolyhedralPriorityNumbers? center .trigonalPyramid ligands = some priorities →
      priorities.eraseDups.length = priorities.length →
      result.polyhedralGeometryObservationAssignment?
          { center := center, geometry := .trigonalPyramid,
            recognition := .threeCoordinate .centerSignificantlyOutOfDonorPlane,
            ligands := ligands,
            configurationPositions := .noDistinguishedPositions,
            absoluteOrientation := .trigonalPyramidRS
              (BlueBookP93.rotationOfProduction sense) } =
        some
          { unit := StereoUnit.polyhedron center
            outcome := StereoOutcome.polyhedral
              { geometry := .trigonalPyramid
                configurationIndex := []
                absolute? := some (.rs
                  (RedBookIR9.trigonalPyramidalRS
                    { sequenceFromPriorityOne := BlueBookP93.rotationOfProduction sense
                      viewedFromCenterTowardLeastPreferred := True
                      phantomSite := .lonePairSite
                      phantomHasLowestPriority := True })) } }

theorem supportedGeometryDescriptorsConform_P93_IR9 :
    SupportedGeometryDescriptorConformance where
  primingFamilies := canonicalPolyhedralPrimeCounts?_conforms_IR9
  configurationIndexArity := polyhedralConfigurationIndexArity?_conforms_P93_IR9
  configurationIndexRouting := polyhedralConfigurationIndex?_conforms_P93_IR9
  absoluteRouting := polyhedralAbsoluteConfiguration?_conforms_P93_IR9
  trigonalPyramid := trigonalPyramidalGeometryObservationAssignment_exact

end TetraStereo.OneCenter
