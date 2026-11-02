import TetraStereo.OneCenter.IUPACRule45CanonicalFamilyCompiler
import TetraStereo.OneCenter.AuthoritativeSemanticParserRule3Through6Conformance
import TetraStereo.OneCenter.ExplicitHydrogenDoubleBondEndpointCount
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through6Scheduler
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrenceRule3Through5FixedPoint
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeOccurrencePermutation
import TetraStereo.OneCenter.CIPDescriptorBearingPipelineAffineInvariance

set_option autoImplicit false

/-!
# Concrete nonvacuity for the canonical Rules 4b/5 provision family

One exact parser-backed molecule supplies the single active canonical trace used by every Rules
4b/5 projection.  Generic carrier and no-double-bond theorems discharge ligand-frame, Rule-3,
physical-topology, and partition totality.  The remaining chemical content is the enantiomorphic
branch-pair theorem below; no provision row owns a separate witness.

The exact coordinates are calibrated against the corrected tetrahedral contract: negative
oriented volume is `R` (clockwise written parity) and positive oriented volume is `S`
(anticlockwise written parity).  Reflection across `x = 0` reverses orientation, so the two
branches carry opposite descriptors; the concrete literals are `S` on the left branch and `R` on
the right branch.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision
namespace Rule45CanonicalFamilyNonvacuity

open AuthoritativeChemicalInput

def smiles : String := "F[C@](Cl)([C@H](Br)I)[C@@H](Br)I"

def raw : RawMolecule :=
  match parseOpenSMILES smiles with
  | .ok molecule => molecule
  | .error _ => { atoms := [], bonds := [] }

def normalized : ChemistryNormalizationResult := normalizeRawMolecule raw

def rawMolecule : RawMolecule := normalized.parsed.withExplicitHydrogens

/-- Exact coordinates symmetric under reflection across `x = 0`.  That reflection exchanges the
two enantiomorphic branches `3↔6`, `4↔7`, `5↔8`, and `9↔10`, while fixing the central,
fluorine, and chlorine atoms. -/
def symmetricPoint : Nat → CartesianPoint3
  | 0 => { x := 0, y := 1, z := 0 }
  | 1 => { x := 0, y := 0, z := 0 }
  | 2 => { x := 0, y := 0, z := 1 }
  | 3 => { x := 1, y := 0, z := 0 }
  | 4 => { x := 1, y := 1, z := 0 }
  | 5 => { x := 1, y := 0, z := 1 }
  | 6 => { x := -1, y := 0, z := 0 }
  | 7 => { x := -1, y := 1, z := 0 }
  | 8 => { x := -1, y := 0, z := 1 }
  | 9 => { x := 1, y := -1, z := -1 }
  | _ => { x := -1, y := -1, z := -1 }

def spatial : SpatialConfiguration :=
  { positions := (List.range rawMolecule.atomCount).map symmetricPoint }

@[simp] theorem spatial_length : spatial.positions.length = rawMolecule.atomCount := by
  simp [spatial]

theorem source_available :
    (rawMolecule.toAuthoritativeChemicalInputWithSpatial? spatial).isSome = true := by
  decide

def source : AuthoritativeChemicalInput :=
  match rawMolecule.toSemanticMolecule? with
  | none => { molecule := { atoms := [], interactions := [] } }
  | some semantic =>
      { molecule := semantic
        spatial? := some spatial
        diagram? := some rawMolecule.toDiagramConfiguration }

theorem source_exact :
    rawMolecule.toAuthoritativeChemicalInputWithSpatial? spatial = some source := by
  unfold RawMolecule.toAuthoritativeChemicalInputWithSpatial? source
  cases converted : rawMolecule.toSemanticMolecule? with
  | none =>
      have available := source_available
      simp [RawMolecule.toAuthoritativeChemicalInputWithSpatial?, converted] at available
  | some semantic => simp

theorem source_structurallyWellFormed : source.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by decide)

theorem converted : rawMolecule.toSemanticMolecule? = some source.molecule :=
  (rawMolecule.toAuthoritativeChemicalInputWithSpatial?_exact
    spatial source source_exact).1.1

theorem normalized_resolved :
    ∀ bond, bond ∈ normalized.parsed.bonds → bond.kind ≠ .unspecified := by
  simpa [normalized] using raw.normalizeUnspecifiedBonds_resolved

theorem raw_resolved :
    ∀ bond, bond ∈ rawMolecule.bonds → bond.kind ≠ .unspecified := by
  exact normalized.parsed.withExplicitHydrogens_preserves_noUnspecified normalized_resolved

theorem raw_writtenExact : rawMolecule.WrittenNeighborExact :=
  normalized.parsed.withExplicitHydrogens_writtenNeighborExact

def rawCenter : Fin rawMolecule.atomCount := ⟨1, by decide⟩

def rawCenterSpec : AtomSpec :=
  { element := .C
    explicitHydrogens? := some 0
    tetrahedral? := some .anticlockwise }

theorem raw_center_frame :
    rawMolecule.OrdinaryConnectivityOnlyTetrahedralFrameAt rawCenter := by
  refine ⟨⟨rawCenterSpec, by decide, by decide, by decide⟩, by decide⟩

def centerAtom : source.AromaticCanonicalAtom :=
  rawMolecule.convertedAtomIndex source converted rawCenter

theorem center_detected : centerAtom ∈ source.aromaticCanonicalTetrahedralCenterSet := by
  exact (rawMolecule.ordinaryConnectivityOnlyTetrahedralFrameAt_iff_convertedCenter_mem
    source converted raw_writtenExact raw_resolved rawCenter).mp raw_center_frame

def center : source.AromaticCanonicalTetrahedralCenter := ⟨centerAtom, center_detected⟩

@[simp] theorem center_index : center.1.val = 1 := rfl

def carrierFuel : Nat := 1

def ruleFuel : Nat := 4

noncomputable def target : source.AromaticCanonicalOccurrence carrierFuel :=
  source.aromaticCanonicalFinalOccurrence carrierFuel center

noncomputable def roots : List (source.AromaticCanonicalRerootCursor carrierFuel) :=
  source.aromaticCanonicalRerootChildren { occurrence := target, previous? := none }

theorem roots_computed :
    source.aromaticCanonicalOccurrenceLigandFrame? target = some roots := by
  rfl

set_option maxRecDepth 10000 in
theorem official_root_children_length :
    (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
      source.molecule.atomCount (OfficialCIPNode.root center.1)).length = 4 := by
  rfl

theorem roots_length : roots.length = 4 := by
  obtain ⟨exactRoots, exactRootsComputed, exactLength⟩ :=
    source.aromaticCanonicalOccurrenceLigandFrame_final_length carrierFuel center
  have exactRootsEq : exactRoots = roots := by
    have targetEq : source.aromaticCanonicalFinalOccurrence carrierFuel center = target := rfl
    rw [targetEq] at exactRootsComputed
    exact Option.some.inj (exactRootsComputed.symm.trans roots_computed)
  subst exactRoots
  exact exactLength.trans official_root_children_length

/-- Position-indexed access to the exact canonical ligand frame. -/
noncomputable def rootAt (position : Fin 4) :
    source.AromaticCanonicalRerootCursor carrierFuel :=
  roots.get (Fin.cast roots_length.symm position)

def branchAtomThree : source.AromaticCanonicalAtom := ⟨3, by decide⟩

def branchAtomSix : source.AromaticCanonicalAtom := ⟨6, by decide⟩

set_option maxRecDepth 10000 in
theorem rootAt_two_current :
    (rootAt ⟨2, by decide⟩).occurrence.1.node.current? = some branchAtomThree := by
  rfl

set_option maxRecDepth 10000 in
theorem rootAt_three_current :
    (rootAt ⟨3, by decide⟩).occurrence.1.node.current? = some branchAtomSix := by
  rfl

noncomputable def leftOccurrence : source.AromaticCanonicalOccurrence carrierFuel :=
  (rootAt ⟨2, by decide⟩).occurrence

noncomputable def rightOccurrence : source.AromaticCanonicalOccurrence carrierFuel :=
  (rootAt ⟨3, by decide⟩).occurrence

private def atom4 : source.AromaticCanonicalAtom := ⟨4, by decide⟩
private def atom5 : source.AromaticCanonicalAtom := ⟨5, by decide⟩
private def atom7 : source.AromaticCanonicalAtom := ⟨7, by decide⟩
private def atom8 : source.AromaticCanonicalAtom := ⟨8, by decide⟩
private def atom9 : source.AromaticCanonicalAtom := ⟨9, by decide⟩
private def atom10 : source.AromaticCanonicalAtom := ⟨10, by decide⟩

/-- Atom involution induced by reflection across `x = 0` in `symmetricPoint`. -/
def branchSwapAtomPermutation : Equiv.Perm source.AromaticCanonicalAtom :=
  (Equiv.swap branchAtomThree branchAtomSix) *
    (Equiv.swap atom4 atom7) *
      (Equiv.swap atom5 atom8) *
        (Equiv.swap atom9 atom10)

theorem branchSwapAtomPermutation_involutive :
    Function.Involutive branchSwapAtomPermutation := by
  intro atom
  fin_cases atom <;> decide

/-- The reflection preserves every atom datum, ordinary bond multiplicity, and mancude edge. -/
theorem branchSwapAtomPermutation_constitution :
    source.AromaticCanonicalConstitutionAutomorphism branchSwapAtomPermutation := by
  exact (source.aromaticCanonicalConstitutionAutomorphism?_eq_true_iff
    branchSwapAtomPermutation).mp (by decide)

theorem source_no_aromatic_edges : source.molecule.aromaticPairEdges = [] := by
  rfl

theorem source_aromaticCanonicalBondOrder_le_one :
    ∀ left right : source.AromaticCanonicalAtom,
      source.molecule.aromaticCanonicalBondOrder left.val right.val ≤ 1 := by
  decide

theorem source_aromaticCanonicalOfficialCIPChildrenAt_nodup
    (node : OfficialCIPNode source.AromaticCanonicalAtom) :
    (source.molecule.aromaticCanonicalOfficialCIPChildrenAt
      source.molecule.atomCount node).Nodup :=
  aromaticCanonicalOfficialCIPChildrenAt_nodup_of_no_edges_of_single
    source.molecule source.molecule.atomCount source_no_aromatic_edges
      source_aromaticCanonicalBondOrder_le_one node

/-- The proof-independent carrier involution induced by the molecular branch reflection. -/
noncomputable def branchSwapOccurrencePermutation :
    Equiv.Perm (source.AromaticCanonicalOccurrence carrierFuel) :=
  aromaticCanonicalOccurrencePermutationOfInvolution source carrierFuel
    branchSwapAtomPermutation branchSwapAtomPermutation_constitution
      branchSwapAtomPermutation_involutive source_no_aromatic_edges
        source_aromaticCanonicalOfficialCIPChildrenAt_nodup

set_option maxRecDepth 10000 in
theorem branchSwapOccurrencePermutation_maps_leftOccurrence :
    branchSwapOccurrencePermutation leftOccurrence = rightOccurrence := by
  apply Subtype.ext
  rfl

theorem branchSwapOccurrencePermutation_maps_rightOccurrence :
    branchSwapOccurrencePermutation rightOccurrence = leftOccurrence := by
  rw [← branchSwapOccurrencePermutation_maps_leftOccurrence]
  exact branchSwapOccurrencePermutation.left_inv leftOccurrence

/-- Every source-canonical occurrence has a branch-reflected carrier witness with mapped node and
the same dependency depth.  Address values may be renumbered, but their length is preserved. -/
theorem exists_branchReflectedOccurrence
    (occurrence : source.AromaticCanonicalOccurrence carrierFuel) :
    ∃ mappedOccurrence : source.AromaticCanonicalOccurrence carrierFuel,
      mappedOccurrence.1.root = branchSwapAtomPermutation occurrence.1.root ∧
      mappedOccurrence.1.address.length = occurrence.1.address.length ∧
      mappedOccurrence.1.node =
        mapAromaticCanonicalOfficialCIPNode branchSwapAtomPermutation occurrence.1.node ∧
      mappedOccurrence.1.remaining = occurrence.1.remaining :=
  source.exists_mapped_aromaticCanonicalOccurrence_of_no_edges carrierFuel
    branchSwapAtomPermutation branchSwapAtomPermutation_constitution
      source_no_aromatic_edges occurrence

theorem branchSwapAtomPermutation_maps_root :
    mapAromaticCanonicalOfficialCIPNode branchSwapAtomPermutation
        (OfficialCIPNode.rootFromEdge center.1 branchAtomThree) =
      OfficialCIPNode.rootFromEdge center.1 branchAtomSix := by
  decide

/-! ## Exact geometric reflection -/

def branchReflection : RationalAffineFrameTransform where
  m00 := -1
  m01 := 0
  m02 := 0
  m10 := 0
  m11 := 1
  m12 := 0
  m20 := 0
  m21 := 0
  m22 := 1
  offset := { x := 0, y := 0, z := 0 }

@[simp] theorem branchReflection_determinant : branchReflection.determinant = -1 := by
  norm_num [branchReflection, RationalAffineFrameTransform.determinant]

theorem branchReflection_orientationReversing : branchReflection.determinant < 0 := by
  norm_num

def branchSwapIndex : Nat → Nat
  | 3 => 6
  | 4 => 7
  | 5 => 8
  | 6 => 3
  | 7 => 4
  | 8 => 5
  | 9 => 10
  | 10 => 9
  | atom => atom

theorem branchSwapAtomPermutation_val (atom : source.AromaticCanonicalAtom) :
    (branchSwapAtomPermutation atom).val = branchSwapIndex atom.val := by
  fin_cases atom <;> decide

/-- The constitutional branch involution is realized pointwise by the exact affine reflection. -/
theorem symmetricPoint_branchSwap (atom : source.AromaticCanonicalAtom) :
    branchReflection.applyPoint (symmetricPoint atom.val) =
      symmetricPoint (branchSwapAtomPermutation atom).val := by
  rw [branchSwapAtomPermutation_val]
  fin_cases atom <;>
    norm_num [branchReflection, RationalAffineFrameTransform.applyPoint,
      symmetricPoint, branchSwapIndex]

def leftPriorityPoints : List CartesianPoint3 :=
  [symmetricPoint 5, symmetricPoint 4, symmetricPoint 1, symmetricPoint 9]

def rightPriorityPoints : List CartesianPoint3 :=
  [symmetricPoint 8, symmetricPoint 7, symmetricPoint 1, symmetricPoint 10]

theorem rightPriorityPoints_reflection :
    rightPriorityPoints = leftPriorityPoints.map branchReflection.applyPoint := by
  norm_num [rightPriorityPoints, leftPriorityPoints, branchReflection,
    RationalAffineFrameTransform.applyPoint, symmetricPoint]

/-- Reflecting all four priority-ordered points complements their exact rational descriptor. -/
theorem priorityGeometry_reflection :
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? rightPriorityPoints =
      (CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? leftPriorityPoints).map
        RS.swap := by
  rw [rightPriorityPoints_reflection]
  exact CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?_orientationReversingAffine
    branchReflection branchReflection_orientationReversing leftPriorityPoints

/-- The left branch has exact oriented volume `+3`, hence descriptor `S` under the corrected
contract (positive volume is anticlockwise written parity). -/
theorem leftPriorityPoints_descriptor :
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? leftPriorityPoints =
      some .S := by
  norm_num [leftPriorityPoints, symmetricPoint,
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints?,
    CertifiedLocalizedCIPInput.descriptorOfOrientedVolume?, CartesianPoint3.orientedVolume]

/-- The mirrored right branch has exact oriented volume `-3`, hence descriptor `R`. -/
theorem rightPriorityPoints_descriptor :
    CertifiedLocalizedCIPInput.descriptorOfPriorityOrderedPoints? rightPriorityPoints =
      some .R := by
  rw [priorityGeometry_reflection, leftPriorityPoints_descriptor]
  rfl

/-- The converted fixture contains only ordinary single bonds.  This small decision proves a
finite source fact; recursive Rule-3 and partition consequences are derived mathematically. -/
theorem source_no_ordinary_double_bond : source.NoAromaticCanonicalOrdinaryDoubleBond := by
  intro left right ordinary
  have noOrderTwo :
      ∀ first second : source.AromaticCanonicalAtom,
        source.molecule.aromaticCanonicalBondOrder first.val second.val ≠ 2 := by
    decide
  exact noOrderTwo left right ordinary.2

noncomputable def semantics : source.AromaticCanonicalRuleSemantics carrierFuel :=
  source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics carrierFuel ruleFuel

noncomputable def state : source.AromaticCanonicalAuxiliaryState carrierFuel :=
  source.aromaticCanonicalScheduledAuxiliaryState semantics

noncomputable def view : source.AromaticCanonicalDependencyView target :=
  source.aromaticCanonicalDependencyView state target

theorem roots_valid :
    ∀ cursor ∈ roots, source.AromaticCanonicalRerootCursorValid cursor :=
  source.aromaticCanonicalOccurrenceLigandFrame_cursor_valid target roots roots_computed

theorem root_inputs_resolved :
    source.AromaticCanonicalRule3Through5RootInputsResolved target view ruleFuel roots := by
  exact source.aromaticCanonicalRule3Through5RootInputsResolved_at_twice_of_noDouble
    source_no_ordinary_double_bond target view roots roots_length roots_valid

noncomputable def partition :
    source.AromaticCanonicalRule3Through5InitialPartition carrierFuel :=
  Classical.choose <|
    (source.exists_buildAromaticCanonicalRule3Through5InitialPartition_iff_inputsResolved
      target view ruleFuel roots).mpr root_inputs_resolved

theorem partition_computed :
    source.buildAromaticCanonicalRule3Through5InitialPartition?
      target view ruleFuel roots = some partition :=
  Classical.choose_spec <|
    (source.exists_buildAromaticCanonicalRule3Through5InitialPartition_iff_inputsResolved
      target view ruleFuel roots).mpr root_inputs_resolved

theorem partition_canonical :
    source.CanonicalAromaticCanonicalRule3Through5InitialPartition
      target view ruleFuel roots partition :=
  (source.buildAromaticCanonicalRule3Through5InitialPartition?_eq_some_iff_canonical
    target view ruleFuel roots partition).mp partition_computed

end Rule45CanonicalFamilyNonvacuity
end IUPACNormativeProvision
end TetraStereo.OneCenter
