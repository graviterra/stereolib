import TetraStereo.OneCenter.LocalizedCyclicInputWitness
import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6Analysis
import TetraStereo.KernelOnly

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
# Exact coordinates for the accepted nine-atom cyclic input

The accepted nonspatial fixture is unchanged: `cyclicSource.spatial?` stays `none`.
This module attaches one exact rational point to each atom of the same expanded
molecule, `NativeRingDomain.ringRaw 0` with anticlockwise root tag, and admits that
source at standard fuel `atomCount + 1 = 10`.

The core atoms `0`, `2`, and `4` lie in the plane `z = 0` and span a triangle of
nonzero area. Substituents leave that plane. The root written row `[5, 1, 2, 4]`
has oriented volume `24`, which the accepted rational convention reads as
`TetrahedralInputParity.anticlockwise`, the same tag carried by atom `0`.

Atom `2` is an untagged degree-four center. Its written row `[0, 6, 3, 4]` has
oriented volume `-22`. Atom `4` is also an untagged degree-four center, with
written row `[2, 7, 8, 0]` and oriented volume `-48`, but atoms `7` and `8` are
both fresh terminal hydrogens. No `RS` letter is derived: the written order is
not identified with CIP priority order.

The remaining root computation, not executed here, is the rule-major priority
permutation of the four root ligands, `descriptorOfOrientedVolume?` on that
ordered tuple, and equality of the result with `referenceState` at the root
occurrence of this spatial input. The all-ring theorem stays separate.
-/

namespace TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness

open TetraStereo.OneCenter
open TetraStereo.OneCenter.RawMolecule
open TetraStereo.OneCenter.CertifiedLocalizedCIPInput
open TetraStereo.OneCenter.AuthoritativeChemicalInput
open TetraStereo.OneCenter.LocalizedRuleMajorReference
open TetraStereo.OneCenter.LocalizedCyclicInputWitness
open TetraStereo.OneCenter.MoleculeGraph
open TetraStereo.OneCenter.CartesianPoint3
open TetraStereo.UniversalProof.NativeRingDomain
open TetraStereo.UniversalProof.NativeRingHydrogenFacts
open TetraStereo.UniversalProof.GeneralRingPhysicalAdmission

def P0 : CartesianPoint3 := { x := 0, y := 0, z := 0 }
def P1 : CartesianPoint3 := { x := 2, y := 0, z := -1 }
def P2 : CartesianPoint3 := { x := 4, y := 0, z := 0 }
def P3 : CartesianPoint3 := { x := 6, y := 1, z := 1 }
def P4 : CartesianPoint3 := { x := 1, y := 3, z := 0 }
def P5 : CartesianPoint3 := { x := 0, y := 0, z := 2 }
def P6 : CartesianPoint3 := { x := 4, y := 0, z := 2 }
def P7 : CartesianPoint3 := { x := 1, y := 3, z := 2 }
def P8 : CartesianPoint3 := { x := 1, y := 3, z := -2 }
def probeZ : CartesianPoint3 := { x := 0, y := 0, z := 1 }

def cyclicPositions : List CartesianPoint3 := [P0, P1, P2, P3, P4, P5, P6, P7, P8]

theorem positions_length : cyclicPositions.length = 9 := rfl

def cyclicSpatialConfiguration : SpatialConfiguration :=
  { positions := cyclicPositions }

def cyclicSpatialSource : AuthoritativeChemicalInput :=
  (cyclicExpanded.toAuthoritativeChemicalInputWithSpatial? cyclicSpatialConfiguration).getD
    { molecule := { atoms := [], interactions := [] } }

theorem spatial_conversion :
    cyclicExpanded.toAuthoritativeChemicalInputWithSpatial? cyclicSpatialConfiguration =
      some cyclicSpatialSource := by
  have semantic :=
    cyclicExpanded.toAuthoritativeChemicalInput?_molecule cyclicSource source_conversion
  cases observed : cyclicExpanded.toSemanticMolecule? with
  | none => simp [observed] at semantic
  | some _ =>
      simp [cyclicSpatialSource, RawMolecule.toAuthoritativeChemicalInputWithSpatial?, observed]

theorem spatial_agreement :
    cyclicExpanded.AuthoritativeStructureAgreement cyclicSpatialSource ∧
      cyclicSpatialSource.spatial? = some cyclicSpatialConfiguration :=
  cyclicExpanded.toAuthoritativeChemicalInputWithSpatial?_exact
    cyclicSpatialConfiguration cyclicSpatialSource spatial_conversion

theorem molecule_eq : cyclicSpatialSource.molecule = cyclicSource.molecule := by
  have spatialMolecule := spatial_agreement.1.1
  have sourceMolecule :=
    cyclicExpanded.toAuthoritativeChemicalInput?_molecule cyclicSource source_conversion
  exact Option.some.inj (spatialMolecule.symm.trans sourceMolecule)

theorem diagram_eq : cyclicSpatialSource.diagram? = cyclicSource.diagram? := by
  have spatialDiagram := spatial_agreement.1.2
  have sourceDiagram :=
    cyclicExpanded.toAuthoritativeChemicalInput?_diagram cyclicSource source_conversion
  exact spatialDiagram.trans sourceDiagram.symm

theorem diagram_coordinates_absent :
    ∀ diagram, cyclicSpatialSource.diagram? = some diagram → diagram.atomPositions? = none := by
  intro diagram observed
  have same : diagram = cyclicExpanded.toDiagramConfiguration :=
    Option.some.inj (observed.symm.trans spatial_agreement.1.2)
  subst same
  rfl

theorem nonspatial_spatial_absent : cyclicSource.spatial? = none := by
  cases observed : cyclicExpanded.toSemanticMolecule? with
  | none =>
      simp [cyclicSource, RawMolecule.toAuthoritativeChemicalInput?, observed]
  | some _ =>
      simp [cyclicSource, RawMolecule.toAuthoritativeChemicalInput?, observed]

theorem spatial_structurallyWellFormed : cyclicSpatialSource.StructurallyWellFormed := by
  refine ⟨?molecule, ?spatial, ?diagram⟩
  · rw [molecule_eq]
    exact source_structurallyWellFormed.1
  · have spatialSome := spatial_agreement.2
    simp only [SpatialIndicesWellFormed, spatialSome, cyclicSpatialConfiguration,
      positions_length, molecule_eq]
    exact atomCount_eq.symm
  · have well : cyclicSource.DiagramIndicesWellFormed := source_structurallyWellFormed.2.2
    unfold DiagramIndicesWellFormed at well ⊢
    rw [← diagram_eq, ← molecule_eq] at well
    exact well

theorem spatial_graphReady : cyclicSpatialSource.molecule.LocalizedCIPGraphReady := by
  rw [molecule_eq]
  exact source_graphReady

def cyclicSpatialCertified : CertifiedLocalizedCIPInput where
  certified :=
    { input := cyclicSpatialSource
      structurallyWellFormed := spatial_structurallyWellFormed }
  graphReady := spatial_graphReady

def cyclicSpatialReference : LocalizedRuleMajorReference.Input where
  certified := cyclicSpatialCertified

theorem carrierFuel_eq :
    carrierFuel cyclicSpatialReference =
      cyclicSpatialCertified.certified.input.molecule.atomCount + 1 :=
  rfl

theorem spatialAtomCount :
    cyclicSpatialCertified.certified.input.molecule.atomCount = 9 := by
  rw [show cyclicSpatialCertified.certified.input.molecule = cyclicSource.molecule by
    simpa [cyclicSpatialCertified] using molecule_eq]
  exact atomCount_eq

theorem standardFuel_eq_ten : carrierFuel cyclicSpatialReference = 10 := by
  rw [carrierFuel_eq, spatialAtomCount]

def SA (index : Fin 9) : cyclicSpatialCertified.Atom :=
  ⟨index.val, spatialAtomCount.symm ▸ index.isLt⟩

@[simp] theorem SA_val (index : Fin 9) : (SA index).val = index.val := rfl

private theorem neighborCard_transport
    {left right : SemanticMolecule} (equal : left = right) {index : ℕ}
    {bound : index < left.atomCount}
    (fact : (left.toLocalizedMoleculeGraph.neighborFinset ⟨index, bound⟩).card = 4) :
    (right.toLocalizedMoleculeGraph.neighborFinset ⟨index, equal ▸ bound⟩).card = 4 := by
  subst equal
  exact fact

private theorem simpleBonded_transport
    {left right : SemanticMolecule} (equal : left = right)
    (fact : left.toLocalizedMoleculeGraph.SimpleBonded) :
    right.toLocalizedMoleculeGraph.SimpleBonded := by
  subst equal
  exact fact

private theorem source_neighbor_card (index : Fin 9) (center : cyclicCertified.Atom)
    (same : center.val = index.val)
    (fact : (cyclicReferenceInput.certified.moleculeGraph.neighborFinset center).card = 4) :
    (cyclicSource.molecule.toLocalizedMoleculeGraph.neighborFinset
      ⟨index.val, atomCount_eq.symm ▸ index.isLt⟩).card = 4 := by
  have eqCenter : center = ⟨index.val, atomCount_eq.symm ▸ index.isLt⟩ := Fin.ext same
  simpa [cyclicReferenceInput, cyclicCertified, CertifiedLocalizedCIPInput.moleculeGraph,
    eqCenter] using fact

private theorem spatial_card (index : Fin 9)
    (fact : (cyclicSource.molecule.toLocalizedMoleculeGraph.neighborFinset
      ⟨index.val, atomCount_eq.symm ▸ index.isLt⟩).card = 4) :
    (cyclicSpatialCertified.moleculeGraph.neighborFinset (SA index)).card = 4 := by
  have transported := neighborCard_transport molecule_eq.symm fact
  have same :
      SA index = ⟨index.val, molecule_eq.symm ▸ (atomCount_eq.symm ▸ index.isLt)⟩ :=
    Fin.ext rfl
  simpa [cyclicSpatialCertified, CertifiedLocalizedCIPInput.moleculeGraph, same] using
    transported

private theorem detected_of_card (index : Fin 9)
    (fact : (cyclicSpatialCertified.moleculeGraph.neighborFinset (SA index)).card = 4) :
    SA index ∈ cyclicSpatialCertified.tetrahedralCenterSet := by
  rw [CertifiedLocalizedCIPInput.tetrahedralCenterSet, MoleculeGraph.mem_tetrahedralCenterSet,
    MoleculeGraph.isTetrahedralCenter_iff_neighborFinset_card]
  exact fact

theorem spatial_simpleBonded : cyclicSpatialCertified.moleculeGraph.SimpleBonded := by
  have fact : cyclicSource.molecule.toLocalizedMoleculeGraph.SimpleBonded := by
    simpa [cyclicReferenceInput, cyclicCertified, CertifiedLocalizedCIPInput.moleculeGraph]
      using input_simpleBonded
  simpa [cyclicSpatialCertified, CertifiedLocalizedCIPInput.moleculeGraph] using
    simpleBonded_transport molecule_eq.symm fact

theorem spatial_detected_inventory :
    (cyclicSpatialCertified.moleculeGraph.neighborFinset (SA ⟨0, by decide⟩)).card = 4 ∧
      (cyclicSpatialCertified.moleculeGraph.neighborFinset (SA ⟨2, by decide⟩)).card = 4 ∧
        (cyclicSpatialCertified.moleculeGraph.neighborFinset (SA ⟨4, by decide⟩)).card = 4 ∧
          SA ⟨0, by decide⟩ ∈ cyclicSpatialCertified.tetrahedralCenterSet ∧
            SA ⟨2, by decide⟩ ∈ cyclicSpatialCertified.tetrahedralCenterSet ∧
              SA ⟨4, by decide⟩ ∈ cyclicSpatialCertified.tetrahedralCenterSet := by
  have card0 := spatial_card ⟨0, by decide⟩
    (source_neighbor_card ⟨0, by decide⟩ A0 rfl degreeFourCentersOnCycle.1)
  have card2 := spatial_card ⟨2, by decide⟩
    (source_neighbor_card ⟨2, by decide⟩ A2 rfl degreeFourCentersOnCycle.2.1)
  have card4 := spatial_card ⟨4, by decide⟩
    (source_neighbor_card ⟨4, by decide⟩ A4 rfl degreeFourCentersOnCycle.2.2.1)
  exact ⟨card0, card2, card4, detected_of_card _ card0, detected_of_card _ card2,
    detected_of_card _ card4⟩

theorem spatial_ring :
    cyclicSpatialSource.molecule = cyclicSource.molecule ∧
      cyclicSpatialCertified.moleculeGraph.SimpleBonded ∧
        cyclicReferenceInput.certified.DeclarativeLocalizedSimpleCycleVertexSet cycleAtoms ∧
          (SA ⟨0, by decide⟩).val = 0 ∧ (SA ⟨2, by decide⟩).val = 2 ∧
            (SA ⟨4, by decide⟩).val = 4 :=
  ⟨molecule_eq, spatial_simpleBonded, molecularCycle, rfl, rfl, rfl⟩

theorem expandedAtomCount : cyclicExpanded.atomCount = 9 := by
  have raw := expanded_atom_count 0 TetrahedralInputParity.anticlockwise
  have arith : 3 * 0 + 9 = 9 := by decide
  rwa [arith] at raw

theorem only_root_tagged :
    ∀ index : Fin cyclicExpanded.atomCount, ∀ spec,
      cyclicExpanded.atomAt? index.val = some spec →
        spec.tetrahedral?.isSome = true → index.val = 0 :=
  expanded_only_root_tagged 0 TetrahedralInputParity.anticlockwise

theorem root_written_row : cyclicExpanded.writtenNeighbors 0 = [5, 1, 2, 4] := by
  simpa using expanded_root_written_row 0 TetrahedralInputParity.anticlockwise

theorem arm_written_row : cyclicExpanded.writtenNeighbors 2 = [0, 6, 3, 4] := by
  simpa using expanded_chlorinated_arm_row 0 TetrahedralInputParity.anticlockwise

theorem closing_written_row : cyclicExpanded.writtenNeighbors 4 = [2, 7, 8, 0] := by
  simpa using expanded_closing_arm_row 0 TetrahedralInputParity.anticlockwise

theorem arm_single_fresh_index :
    ([0, 6, 3, 4].filter (fun index => decide (5 ≤ index))) = [6] := by
  decide

theorem closing_twin_fresh_indices :
    ([2, 7, 8, 0].filter (fun index => decide (5 ≤ index))) = [7, 8] := by
  decide

private theorem expanded_of_raw (index : ℕ) (spec : AtomSpec)
    (raw : (ringRaw 0 TetrahedralInputParity.anticlockwise).atomAt? index = some spec) :
    cyclicExpanded.atomAt? index = some (materializedAtomSpec spec) :=
  expanded_original_atom 0 TetrahedralInputParity.anticlockwise index spec raw

theorem root_source_tag (spec : AtomSpec)
    (observed : cyclicExpanded.atomAt? 0 = some spec) :
    spec.element = .C ∧ spec.tetrahedral? = some TetrahedralInputParity.anticlockwise := by
  have expandedSpec := expanded_of_raw 0 (taggedCarbon TetrahedralInputParity.anticlockwise)
    (ringRaw_atomAt_zero 0 TetrahedralInputParity.anticlockwise)
  have equal := Option.some.inj (expandedSpec.symm.trans observed)
  subst spec
  simp [materializedAtomSpec_element, materializedAtomSpec_tetrahedral, taggedCarbon, carbon,
    AtomSpec.aliphatic]

theorem fluorine_source (spec : AtomSpec)
    (observed : cyclicExpanded.atomAt? 1 = some spec) :
    spec.element = .F ∧ spec.tetrahedral? = none := by
  have expandedSpec := expanded_of_raw 1
    { AtomSpec.aliphatic .F with explicitHydrogens? := some 0 }
    (ringRaw_atomAt_one 0 TetrahedralInputParity.anticlockwise)
  have equal := Option.some.inj (expandedSpec.symm.trans observed)
  subst spec
  simp [materializedAtomSpec_element, materializedAtomSpec_tetrahedral, AtomSpec.aliphatic]

theorem arm_source_spec (spec : AtomSpec)
    (observed : cyclicExpanded.atomAt? 2 = some spec) :
    spec.element = .C ∧ spec.tetrahedral? = none := by
  have expandedSpec := expanded_of_raw 2 (carbon 1)
    (ringRaw_atomAt_two 0 TetrahedralInputParity.anticlockwise)
  have equal := Option.some.inj (expandedSpec.symm.trans observed)
  subst spec
  simp [materializedAtomSpec_element, materializedAtomSpec_tetrahedral, carbon, AtomSpec.aliphatic]

theorem chlorine_source (spec : AtomSpec)
    (observed : cyclicExpanded.atomAt? 3 = some spec) :
    spec.element = .Cl ∧ spec.tetrahedral? = none := by
  have expandedSpec := expanded_of_raw 3
    { AtomSpec.aliphatic .Cl with explicitHydrogens? := some 0 }
    (ringRaw_atomAt_three 0 TetrahedralInputParity.anticlockwise)
  have equal := Option.some.inj (expandedSpec.symm.trans observed)
  subst spec
  simp [materializedAtomSpec_element, materializedAtomSpec_tetrahedral, AtomSpec.aliphatic]

theorem closing_source_spec (spec : AtomSpec)
    (observed : cyclicExpanded.atomAt? 4 = some spec) :
    spec.element = .C ∧ spec.tetrahedral? = none := by
  have raw := ringRaw_atomAt_chain 0 TetrahedralInputParity.anticlockwise 0 (Nat.le_refl _)
  have expandedSpec := expanded_of_raw 4 (carbon 2) (by simpa using raw)
  have equal := Option.some.inj (expandedSpec.symm.trans observed)
  subst spec
  simp [materializedAtomSpec_element, materializedAtomSpec_tetrahedral, carbon, AtomSpec.aliphatic]

theorem fresh_hydrogen (index : ℕ) (low : 5 ≤ index) (high : index < 9) :
    ∃ spec, cyclicExpanded.atomAt? index = some spec ∧
      spec = AtomSpec.aliphatic .H ∧ cyclicExpanded.incidentBondOrderSum index = 1 := by
  have length : cyclicExpanded.atoms.length = 9 := by
    simpa [RawMolecule.atomCount] using expandedAtomCount
  have bound : index < cyclicExpanded.atoms.length := by
    rw [length]
    exact high
  obtain ⟨spec, lookup⟩ := listGet?_exists_of_lt cyclicExpanded.atoms index bound
  have fresh := expanded_fresh_atom 0 TetrahedralInputParity.anticlockwise index spec low lookup
  exact ⟨spec, lookup, fresh.1, fresh.2⟩

private theorem position0 : cyclicPositions[0]? = some P0 := rfl
private theorem position1 : cyclicPositions[1]? = some P1 := rfl
private theorem position2 : cyclicPositions[2]? = some P2 := rfl
private theorem position3 : cyclicPositions[3]? = some P3 := rfl
private theorem position4 : cyclicPositions[4]? = some P4 := rfl
private theorem position5 : cyclicPositions[5]? = some P5 := rfl
private theorem position6 : cyclicPositions[6]? = some P6 := rfl
private theorem position7 : cyclicPositions[7]? = some P7 := rfl
private theorem position8 : cyclicPositions[8]? = some P8 := rfl

private theorem lookup (index : Fin 9) (expected : CartesianPoint3)
    (member : cyclicPositions[index.val]? = some expected) :
    cyclicSpatialCertified.spatialPointAt? (SA index) = some expected := by
  rw [spatialPointAt?_eq_some_iff]
  refine ⟨cyclicSpatialConfiguration, ?_, ?_⟩
  · simpa [cyclicSpatialCertified] using spatial_agreement.2
  · simpa [cyclicSpatialConfiguration, SA_val] using member

theorem coordinate_lookup :
    cyclicSpatialCertified.spatialPointAt? (SA ⟨0, by decide⟩) = some P0 ∧
      cyclicSpatialCertified.spatialPointAt? (SA ⟨1, by decide⟩) = some P1 ∧
        cyclicSpatialCertified.spatialPointAt? (SA ⟨2, by decide⟩) = some P2 ∧
          cyclicSpatialCertified.spatialPointAt? (SA ⟨3, by decide⟩) = some P3 ∧
            cyclicSpatialCertified.spatialPointAt? (SA ⟨4, by decide⟩) = some P4 ∧
              cyclicSpatialCertified.spatialPointAt? (SA ⟨5, by decide⟩) = some P5 ∧
                cyclicSpatialCertified.spatialPointAt? (SA ⟨6, by decide⟩) = some P6 ∧
                  cyclicSpatialCertified.spatialPointAt? (SA ⟨7, by decide⟩) = some P7 ∧
                    cyclicSpatialCertified.spatialPointAt? (SA ⟨8, by decide⟩) = some P8 :=
  ⟨lookup ⟨0, by decide⟩ P0 position0, lookup ⟨1, by decide⟩ P1 position1,
    lookup ⟨2, by decide⟩ P2 position2, lookup ⟨3, by decide⟩ P3 position3,
    lookup ⟨4, by decide⟩ P4 position4, lookup ⟨5, by decide⟩ P5 position5,
    lookup ⟨6, by decide⟩ P6 position6, lookup ⟨7, by decide⟩ P7 position7,
    lookup ⟨8, by decide⟩ P8 position8⟩

theorem substituent_heights :
    P1.z = -1 ∧ P3.z = 1 ∧ P5.z = 2 ∧ P6.z = 2 ∧ P7.z = 2 ∧ P8.z = -2 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem closing_hydrogen_mirror : P7.x = P8.x ∧ P7.y = P8.y ∧ P7.z = -P8.z := by
  refine ⟨rfl, rfl, ?_⟩
  decide

theorem ring_triangle_volume : orientedVolume P2 P4 probeZ P0 = 12 := by
  unfold orientedVolume
  norm_num [P2, P4, probeZ, P0]

theorem ring_core :
    P0.z = 0 ∧ P2.z = 0 ∧ P4.z = 0 ∧
      cyclicSpatialCertified.spatialPointAt? (SA ⟨0, by decide⟩) = some P0 ∧
        cyclicSpatialCertified.spatialPointAt? (SA ⟨2, by decide⟩) = some P2 ∧
          cyclicSpatialCertified.spatialPointAt? (SA ⟨4, by decide⟩) = some P4 ∧
            orientedVolume P2 P4 probeZ P0 = 12 ∧
              0 < orientedVolume P2 P4 probeZ P0 := by
  refine ⟨rfl, rfl, rfl, coordinate_lookup.1, coordinate_lookup.2.2.1, coordinate_lookup.2.2.2.2.1,
    ring_triangle_volume, ?_⟩
  rw [ring_triangle_volume]
  decide

theorem root_written_volume : orientedVolume P5 P1 P2 P4 = 24 := by
  unfold orientedVolume
  norm_num [P5, P1, P2, P4]

theorem root_written_parity :
    RationalTetrahedralInputParity [P5, P1, P2, P4] TetrahedralInputParity.anticlockwise := by
  unfold RationalTetrahedralInputParity
  refine ⟨P5, P1, P2, P4, rfl, ?_⟩
  rw [root_written_volume]
  decide

theorem root_written_parity_exec :
    tetrahedralInputParityOfPoints? [P5, P1, P2, P4] =
      some TetrahedralInputParity.anticlockwise :=
  (tetrahedralInputParityOfPoints?_eq_some_iff _ _).mpr root_written_parity

theorem root_frame :
    cyclicExpanded.writtenNeighbors 0 = [5, 1, 2, 4] ∧
      cyclicSpatialCertified.spatialPointAt? (SA ⟨5, by decide⟩) = some P5 ∧
        cyclicSpatialCertified.spatialPointAt? (SA ⟨1, by decide⟩) = some P1 ∧
          cyclicSpatialCertified.spatialPointAt? (SA ⟨2, by decide⟩) = some P2 ∧
            cyclicSpatialCertified.spatialPointAt? (SA ⟨4, by decide⟩) = some P4 ∧
              orientedVolume P5 P1 P2 P4 = 24 ∧
                0 < orientedVolume P5 P1 P2 P4 ∧
                  RationalTetrahedralInputParity [P5, P1, P2, P4]
                    TetrahedralInputParity.anticlockwise ∧
                    tetrahedralInputParityOfPoints? [P5, P1, P2, P4] =
                      some TetrahedralInputParity.anticlockwise ∧
                      ∀ spec, cyclicExpanded.atomAt? 0 = some spec →
                        spec.tetrahedral? = some TetrahedralInputParity.anticlockwise := by
  refine ⟨root_written_row, coordinate_lookup.2.2.2.2.2.1, coordinate_lookup.2.1,
    coordinate_lookup.2.2.1, coordinate_lookup.2.2.2.2.1, root_written_volume, ?_,
    root_written_parity, root_written_parity_exec, ?_⟩
  · rw [root_written_volume]
    decide
  · intro spec observed
    exact (root_source_tag spec observed).2

theorem arm_written_volume : orientedVolume P0 P6 P3 P4 = -22 := by
  unfold orientedVolume
  norm_num [P0, P6, P3, P4]

theorem arm_frame :
    cyclicExpanded.writtenNeighbors 2 = [0, 6, 3, 4] ∧
      ([0, 6, 3, 4].filter (fun index => decide (5 ≤ index))) = [6] ∧
        cyclicSpatialCertified.spatialPointAt? (SA ⟨0, by decide⟩) = some P0 ∧
          cyclicSpatialCertified.spatialPointAt? (SA ⟨6, by decide⟩) = some P6 ∧
            cyclicSpatialCertified.spatialPointAt? (SA ⟨3, by decide⟩) = some P3 ∧
              cyclicSpatialCertified.spatialPointAt? (SA ⟨4, by decide⟩) = some P4 ∧
                orientedVolume P0 P6 P3 P4 = -22 ∧
                  orientedVolume P0 P6 P3 P4 < 0 ∧
                    orientedVolume P0 P6 P3 P4 ≠ 0 ∧
                      (∀ spec, cyclicExpanded.atomAt? 2 = some spec →
                        spec.tetrahedral? = none) ∧
                        (∃ spec, cyclicExpanded.atomAt? 6 = some spec ∧
                          spec = AtomSpec.aliphatic .H ∧
                            cyclicExpanded.incidentBondOrderSum 6 = 1) ∧
                          (∀ spec, cyclicExpanded.atomAt? 0 = some spec → spec.element = .C) ∧
                            (∀ spec, cyclicExpanded.atomAt? 3 = some spec → spec.element = .Cl) ∧
                              (∀ spec, cyclicExpanded.atomAt? 4 = some spec → spec.element = .C) := by
  refine ⟨arm_written_row, arm_single_fresh_index, coordinate_lookup.1,
    coordinate_lookup.2.2.2.2.2.2.1, coordinate_lookup.2.2.2.1, coordinate_lookup.2.2.2.2.1,
    arm_written_volume, ?_, ?_, ?_, fresh_hydrogen 6 (by decide) (by decide), ?_, ?_, ?_⟩
  · rw [arm_written_volume]
    decide
  · rw [arm_written_volume]
    decide
  · intro spec observed
    exact (arm_source_spec spec observed).2
  · intro spec observed
    exact (root_source_tag spec observed).1
  · intro spec observed
    exact (chlorine_source spec observed).1
  · intro spec observed
    exact (closing_source_spec spec observed).1

theorem closing_written_volume : orientedVolume P2 P7 P8 P0 = -48 := by
  unfold orientedVolume
  norm_num [P2, P7, P8, P0]

theorem closing_frame :
    cyclicExpanded.writtenNeighbors 4 = [2, 7, 8, 0] ∧
      ([2, 7, 8, 0].filter (fun index => decide (5 ≤ index))) = [7, 8] ∧
        cyclicSpatialCertified.spatialPointAt? (SA ⟨2, by decide⟩) = some P2 ∧
          cyclicSpatialCertified.spatialPointAt? (SA ⟨7, by decide⟩) = some P7 ∧
            cyclicSpatialCertified.spatialPointAt? (SA ⟨8, by decide⟩) = some P8 ∧
              cyclicSpatialCertified.spatialPointAt? (SA ⟨0, by decide⟩) = some P0 ∧
                orientedVolume P2 P7 P8 P0 = -48 ∧
                  orientedVolume P2 P7 P8 P0 ≠ 0 ∧
                    (∀ spec, cyclicExpanded.atomAt? 4 = some spec → spec.tetrahedral? = none) ∧
                      (∃ spec, cyclicExpanded.atomAt? 7 = some spec ∧
                        spec = AtomSpec.aliphatic .H ∧
                          cyclicExpanded.incidentBondOrderSum 7 = 1) ∧
                        (∃ spec, cyclicExpanded.atomAt? 8 = some spec ∧
                          spec = AtomSpec.aliphatic .H ∧
                            cyclicExpanded.incidentBondOrderSum 8 = 1) ∧
                          P7.x = P8.x ∧ P7.y = P8.y ∧ P7.z = -P8.z ∧
                            (∀ spec, cyclicExpanded.atomAt? 2 = some spec → spec.element = .C) ∧
                              (∀ spec, cyclicExpanded.atomAt? 0 = some spec → spec.element = .C) := by
  refine ⟨closing_written_row, closing_twin_fresh_indices, coordinate_lookup.2.2.1,
    coordinate_lookup.2.2.2.2.2.2.2.1, coordinate_lookup.2.2.2.2.2.2.2.2,
    coordinate_lookup.1, closing_written_volume, ?_, ?_,
    fresh_hydrogen 7 (by decide) (by decide), fresh_hydrogen 8 (by decide) (by decide),
    closing_hydrogen_mirror.1, closing_hydrogen_mirror.2.1, closing_hydrogen_mirror.2.2,
    ?_, ?_⟩
  · rw [closing_written_volume]
    decide
  · intro spec observed
    exact (closing_source_spec spec observed).2
  · intro spec observed
    exact (arm_source_spec spec observed).1
  · intro spec observed
    exact (root_source_tag spec observed).1

end TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness

assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.positions_length
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.spatial_conversion
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.spatial_agreement
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.molecule_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.diagram_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.diagram_coordinates_absent
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.nonspatial_spatial_absent
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.spatial_structurallyWellFormed
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.spatial_graphReady
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.carrierFuel_eq
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.spatialAtomCount
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.standardFuel_eq_ten
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.SA_val
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.spatial_simpleBonded
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.spatial_detected_inventory
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.spatial_ring
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.expandedAtomCount
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.only_root_tagged
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.root_written_row
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.arm_written_row
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.closing_written_row
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.arm_single_fresh_index
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.closing_twin_fresh_indices
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.root_source_tag
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.fluorine_source
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.arm_source_spec
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.chlorine_source
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.closing_source_spec
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.fresh_hydrogen
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.coordinate_lookup
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.substituent_heights
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.closing_hydrogen_mirror
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.ring_triangle_volume
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.ring_core
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.root_written_volume
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.root_written_parity
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.root_written_parity_exec
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.root_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.arm_written_volume
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.arm_frame
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.closing_written_volume
assert_kernel_only TetraStereo.OneCenter.LocalizedCyclicSpatialInputWitness.closing_frame
