import TetraStereo.OneCenter.GeometryAnnotatedCIPConformance

set_option autoImplicit false

namespace TetraStereo.Examples.GeometryAnnotatedCIPAnalysis

open OneCenter

private def atom : AtomSpec :=
  { element := .H, explicitHydrogens? := some 0 }

private def molecule : RawMolecule where
  atoms := [atom, atom, atom, atom, atom, atom]
  bonds := []

private def normalized := normalizeRawMolecule molecule

private def observations : IndexedNoncenterStereoAnnotations where
  axes :=
    [{ axisStart := 0, axisEnd := 1, startHigh := 2, startLow := 3,
       endHigh := 4, endLow := 5, descriptor := .Ra }]
  planes :=
    [{ planeAtoms := [0, 1, 2], pilotAtom := 3, highReference := 4,
       lowReference := 5, descriptor := .Sp }]
  helices :=
    [{ helixPath := [0, 2, 4], frontReference := 1, backReference := 5,
       descriptor := .P }]

theorem validated_geometry_observations_reach_public_assignments :
    analyzeNormalizedWithGeometry normalized observations =
      [ { unit := StereoUnit.axis 0 1, outcome := StereoOutcome.axial .Ra },
        { unit := StereoUnit.plane [0, 1, 2], outcome := StereoOutcome.planar .Sp },
        { unit := StereoUnit.helix [0, 2, 4], outcome := StereoOutcome.helical .P } ] := by
  decide

private def outOfRange : IndexedNoncenterStereoAnnotations where
  helices :=
    [{ helixPath := [0, 7], frontReference := 1, backReference := 2,
       descriptor := .M }]

theorem out_of_range_geometry_observation_is_rejected :
    analyzeNormalizedWithGeometry normalized outOfRange = [] := by
  decide

private def conflictingPlane : IndexedNoncenterStereoAnnotations where
  planes :=
    [ { planeAtoms := [0, 1, 2], pilotAtom := 3, highReference := 4,
        lowReference := 5, descriptor := .Rp },
      { planeAtoms := [0, 1, 2], pilotAtom := 3, highReference := 4,
        lowReference := 5, descriptor := .Sp } ]

theorem conflicting_geometry_observations_are_rejected :
    analyzeNormalizedWithGeometry normalized conflictingPlane = [] := by
  decide

private def carbon : AtomSpec :=
  { element := .C, explicitHydrogens? := some 0 }

private def bromine : AtomSpec :=
  { element := .Br, explicitHydrogens? := some 0 }

private def chlorine : AtomSpec :=
  { element := .Cl, explicitHydrogens? := some 0 }

private def iodine : AtomSpec :=
  { element := .I, explicitHydrogens? := some 0 }

private def fluorine : AtomSpec :=
  { element := .F, explicitHydrogens? := some 0 }

private def observedAxisMolecule : RawMolecule where
  atoms := [carbon, carbon, bromine, chlorine, iodine, fluorine]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single },
      { source := 1, target := 4, kind := .single },
      { source := 1, target := 5, kind := .single } ]

private def observedAxisNormalized := normalizeRawMolecule observedAxisMolecule

private def rawGeometry : IndexedCIPGeometryObservations where
  axes :=
    [{ axisStart := 0, axisEnd := 1, startFirst := 2, startSecond := 3,
       endFirst := 4, endSecond := 5, sense := .positive }]
  planes :=
    [{ planeAtoms := [0, 1, 2], pilotAtom := 0, firstReference := 3,
       secondReference := 4, sense := .negative }]
  helices :=
    [{ helixPath := [2, 0, 1, 4], frontReference := 3,
       backReference := 5, sense := .positive }]

theorem raw_geometry_senses_construct_descriptors_after_CIP_axis_check :
    analyzeNormalizedWithObservedGeometry observedAxisNormalized rawGeometry =
      [ { unit := StereoUnit.axis 0 1, outcome := StereoOutcome.axial .Ra },
        { unit := StereoUnit.plane [0, 1, 2], outcome := StereoOutcome.planar .Sp },
        { unit := StereoUnit.helix [2, 0, 1, 4], outcome := StereoOutcome.helical .P } ] := by
  decide

private def observedAxisCertified : CertifiedChemistryNormalizationResult :=
  (normalizeRawMoleculeCertified? observedAxisMolecule).get (by decide)

theorem certified_entry_point_preserves_proved_intake_and_geometry_checks :
    analyzeCertifiedNormalizedWithObservedGeometry observedAxisCertified rawGeometry =
      [ { unit := StereoUnit.axis 0 1, outcome := StereoOutcome.axial .Ra },
        { unit := StereoUnit.plane [0, 1, 2], outcome := StereoOutcome.planar .Sp },
        { unit := StereoUnit.helix [2, 0, 1, 4], outcome := StereoOutcome.helical .P } ] := by
  decide

private def tiedAxisGeometry : IndexedCIPGeometryObservations where
  axes :=
    [{ axisStart := 0, axisEnd := 1, startFirst := 2, startSecond := 2,
       endFirst := 4, endSecond := 5, sense := .positive }]

theorem degenerate_axis_observation_is_rejected :
    analyzeNormalizedWithObservedGeometry observedAxisNormalized tiedAxisGeometry = [] := by
  decide

private def sulfur : AtomSpec :=
  { element := .S, explicitHydrogens? := some 0 }

private def observedSeeSawMolecule : RawMolecule where
  atoms := [sulfur, fluorine, chlorine, bromine, iodine]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single },
      { source := 0, target := 4, kind := .single } ]

private def observedSeeSawNormalized := normalizeRawMolecule observedSeeSawMolecule

private def seeSawGeometry : IndexedCIPGeometryObservations where
  polyhedra :=
    [{ center := 0
       geometry := .seeSaw
       recognition := .fourCoordinate .donorsNoncoplanarCenterOutsideDonorPolyhedron
       ligands := [1, 2, 3, 4]
       -- I and Cl occupy the two positions separated by the largest angle.  Lean derives their
       -- priority numbers as 1 and 3; the importer never supplies those numbers.
       configurationPositions := .seeSaw 3 1
       absoluteOrientation := .seeSawAC .clockwise }]

theorem observed_see_saw_derives_CIP_numbers_and_replaces_tetrahedral_hypothesis :
    analyzeNormalizedWithObservedGeometry observedSeeSawNormalized seeSawGeometry =
      [{ unit := StereoUnit.polyhedron 0
         outcome := StereoOutcome.polyhedral
           { geometry := .seeSaw
             configurationIndex := [[{ number := 1 }, { number := 3 }]]
             absolute? := some (.ac .C) } }] := by
  decide

/-- A geometry label cannot contradict its exact IR-9.3.2 qualitative observation. -/
private def mismatchedSeeSawGeometry : IndexedCIPGeometryObservations where
  polyhedra :=
    [{ center := 0
       geometry := .seeSaw
       recognition := .fourCoordinate .donorsNoncoplanarCenterInsideDonorPolyhedron
       ligands := [1, 2, 3, 4]
       configurationPositions := .seeSaw 3 1
       absoluteOrientation := .seeSawAC .clockwise }]

theorem contradictory_geometry_recognition_is_rejected :
    analyzeNormalizedWithObservedGeometry observedSeeSawNormalized mismatchedSeeSawGeometry =
      analyzeNormalized observedSeeSawNormalized := by
  decide

/-- A spatial-role constructor from a different geometry is rejected before index construction. -/
private def mismatchedSeeSawPositions : IndexedCIPGeometryObservations where
  polyhedra :=
    [{ center := 0
       geometry := .seeSaw
       recognition := .fourCoordinate .donorsNoncoplanarCenterOutsideDonorPolyhedron
       ligands := [1, 2, 3, 4]
       configurationPositions := .squarePlanar 3
       absoluteOrientation := .seeSawAC .clockwise }]

theorem contradictory_configuration_position_role_is_rejected :
    analyzeNormalizedWithObservedGeometry observedSeeSawNormalized mismatchedSeeSawPositions =
      analyzeNormalized observedSeeSawNormalized := by
  decide

/-- An `R/S` trigonal-pyramidal orientation cannot be reinterpreted as see-saw `A/C`. -/
private def mismatchedSeeSawOrientation : IndexedCIPGeometryObservations where
  polyhedra :=
    [{ center := 0
       geometry := .seeSaw
       recognition := .fourCoordinate .donorsNoncoplanarCenterOutsideDonorPolyhedron
       ligands := [1, 2, 3, 4]
       configurationPositions := .seeSaw 3 1
       absoluteOrientation := .trigonalPyramidRS .clockwise }]

theorem contradictory_absolute_orientation_convention_is_rejected :
    analyzeNormalizedWithObservedGeometry observedSeeSawNormalized mismatchedSeeSawOrientation =
      analyzeNormalized observedSeeSawNormalized := by
  decide

/-- The generic nearest-idealized observation is reserved for coordination five and above; it
cannot bypass the explicit three- and four-coordinate decision trees. -/
theorem higher_coordination_evidence_cannot_label_a_four_coordinate_geometry :
    RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?
        (.higherCoordinationNearestIdealized .seeSaw) = none := by
  decide

/-! ## Equal priority tiers and IR-9.3.5.3 grouping -/

private def tiedDonorMolecule : RawMolecule where
  atoms := [carbon, fluorine, fluorine, fluorine, fluorine]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single },
      { source := 0, target := 4, kind := .single } ]

private def tiedDonorNormalized := normalizeRawMolecule tiedDonorMolecule

/-- IR-9.3.5.2 assigns identical ligands the same dense base priority number. -/
theorem four_identical_donors_share_priority_one :
    tiedDonorNormalized.polyhedralPriorityNumbers?
        0 .tetrahedron [1, 2, 3, 4] [] =
      some (List.replicate 4 { number := 1 }) := by
  decide

/-- Family and group identifiers carry equality only.  Renaming them does not change the canonical
prime counts, and the first occurrence group in each family is the arbitrary unprimed choice. -/
private def member (family group : Nat) : Option RedBookIR9.PrimingMembership :=
  some { family := family, group := group }

theorem priming_family_group_identifiers_have_no_priority_meaning :
    canonicalPolyhedralPrimeCounts? 6
        [member 8 7, member 8 7, member 8 4, member 8 4, member 8 9, member 8 9] =
        some [0, 0, 1, 1, 2, 2] ∧
      canonicalPolyhedralPrimeCounts? 6
        [member 91 100, member 91 100, member 91 3, member 91 3,
          member 91 42, member 91 42] =
        some [0, 0, 1, 1, 2, 2] := by
  decide

/-- The words "of a particular kind" are load-bearing: two independent repeated families each
restart with an unprimed group, rather than forming one global prime hierarchy. -/
theorem independent_repeated_families_restart_priming :
    canonicalPolyhedralPrimeCounts? 8
        [member 10 7, member 10 7, member 10 4, member 10 4,
          member 20 9, member 20 9, member 20 3, member 20 3] =
      some [0, 0, 1, 1, 0, 0, 1, 1] := by
  decide

private def bidentateOxygen : AtomSpec :=
  { element := .O, explicitHydrogens? := some 0 }

/-- Two constitutionally and stereochemically identical O-O components, each attached twice to
the center.  No family/group assertion is supplied by this fixture. -/
private def bisBidentateMolecule : RawMolecule where
  atoms := [carbon, bidentateOxygen, bidentateOxygen, bidentateOxygen, bidentateOxygen]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single },
      { source := 0, target := 4, kind := .single },
      { source := 1, target := 2, kind := .single },
      { source := 3, target := 4, kind := .single } ]

private def bisBidentateNormalized := normalizeRawMolecule bisBidentateMolecule

/-- The regression is inside the admitted finite-molecule domain, not merely a malformed graph. -/
private def bisBidentateCertified : CertifiedChemistryNormalizationResult :=
  (normalizeRawMoleculeCertified? bisBidentateMolecule).get (by decide)

theorem bis_bidentate_fixture_is_structurally_and_valence_admissible :
    bisBidentateCertified.result.parsed.Admissible ∧
      bisBidentateCertified.result.parsed.ValenceOK :=
  ⟨bisBidentateCertified.admissible, bisBidentateCertified.valenceOK⟩

/-- The molecular layer deletes the center, discovers the two bidentate connected components,
proves them isomorphic by exhaustive labeled mapping, and derives occurrence groups `[0,0,2,2]` in
one ligand-kind family. -/
theorem repeated_bidentate_ligands_are_derived_from_the_molecule :
    let context := bisBidentateNormalized.geometryPriorityState
    bisBidentateNormalized.deriveRepeatedLigandPrimingMemberships?
        context.1 context.2.2 0 [1, 2, 3, 4] =
      some [member 0 0, member 0 0, member 0 2, member 0 2] := by
  decide

/-- The safe molecular priority ingress consumes that derived frame: donors in the first ligand
are unprimed and the corresponding donors in the second ligand receive one prime. -/
theorem repeated_bidentate_ligands_receive_derived_prime_counts :
    bisBidentateNormalized.molecularPolyhedralPriorityNumbers?
        0 .tetrahedron [1, 2, 3, 4] =
      some
        [ { number := 1, primes := 0 }, { number := 1, primes := 0 },
          { number := 1, primes := 1 }, { number := 1, primes := 1 } ] := by
  decide

/-! ## Symmetry-related coordinating fragments within one ligand -/

private def tetradentateNitrogen : AtomSpec :=
  { element := .N, explicitHydrogens? := some 0 }

/-- One connected tetradentate N4 ligand.  Its `[1,2]` and `[3,4]` donor fragments are exchanged by
a full automorphism of the center-deleted square component. -/
private def symmetricTetradentateMolecule : RawMolecule where
  atoms := [carbon, tetradentateNitrogen, tetradentateNitrogen,
    tetradentateNitrogen, tetradentateNitrogen]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single },
      { source := 0, target := 4, kind := .single },
      { source := 1, target := 2, kind := .single },
      { source := 2, target := 3, kind := .single },
      { source := 3, target := 4, kind := .single },
      { source := 4, target := 1, kind := .single } ]

private def symmetricTetradentateNormalized :=
  normalizeRawMolecule symmetricTetradentateMolecule

private def symmetricTetradentateCertified : CertifiedChemistryNormalizationResult :=
  (normalizeRawMoleculeCertified? symmetricTetradentateMolecule).get (by decide)

theorem symmetric_tetradentate_fixture_is_admissible :
    symmetricTetradentateCertified.result.parsed.Admissible ∧
      symmetricTetradentateCertified.result.parsed.ValenceOK :=
  ⟨symmetricTetradentateCertified.admissible, symmetricTetradentateCertified.valenceOK⟩

private theorem symmetric_tetradentate_initial_descriptor_state_empty :
    initialRawDescriptorState symmetricTetradentateNormalized
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens
      (analysisFuel symmetricTetradentateNormalized.parsed.withExplicitHydrogens) = [] := by
  decide

private theorem symmetric_tetradentate_annotated_centers_empty :
    rawAnnotatedCenters symmetricTetradentateNormalized = [] := by
  decide

private theorem symmetric_tetradentate_empty_discovery_pass :
    runRawDescriptorDiscoveryPass symmetricTetradentateNormalized
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens 100
      (analysisFuel symmetricTetradentateNormalized.parsed.withExplicitHydrogens) [] = [] := by
  decide

private theorem symmetric_tetradentate_empty_stabilizes :
    stabilizedRawDescriptorState? symmetricTetradentateNormalized
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens 100
      (analysisFuel symmetricTetradentateNormalized.parsed.withExplicitHydrogens)
      (symmetricTetradentateNormalized.parsed.atomCount + 1) [] = some [] := by
  unfold stabilizedRawDescriptorState?
  simp [discoverRawDescriptorsFromCertified, symmetric_tetradentate_empty_discovery_pass]

private theorem symmetric_tetradentate_empty_auxiliary_state :
    solveAuxiliaryDescriptorDependencies symmetricTetradentateNormalized
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens 100
      (analysisFuel symmetricTetradentateNormalized.parsed.withExplicitHydrogens) [] = [] := by
  unfold solveAuxiliaryDescriptorDependencies
  rw [symmetric_tetradentate_annotated_centers_empty]
  rfl

private theorem symmetric_tetradentate_empty_finished_state :
    finishRawDescriptorSource symmetricTetradentateNormalized
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens
      (analysisFuel symmetricTetradentateNormalized.parsed.withExplicitHydrogens) [] = [] := by
  unfold finishRawDescriptorSource
  rw [symmetric_tetradentate_annotated_centers_empty]
  rfl

private theorem symmetric_tetradentate_constructive_source_empty :
    (certifiedConstructiveRawDescriptorSource symmetricTetradentateNormalized
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens
      (analysisFuel symmetricTetradentateNormalized.parsed.withExplicitHydrogens) []).val = [] := by
  change constructiveRawDescriptorSourceValue symmetricTetradentateNormalized
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens
      (analysisFuel symmetricTetradentateNormalized.parsed.withExplicitHydrogens) [] = []
  unfold constructiveRawDescriptorSourceValue
  rw [symmetric_tetradentate_empty_stabilizes]
  dsimp only
  rw [symmetric_tetradentate_empty_auxiliary_state,
    symmetric_tetradentate_empty_stabilizes]
  dsimp only
  rw [symmetric_tetradentate_empty_auxiliary_state]
  unfold retainLastStableRawDescriptorState
  simpa only [beq_self_eq_true, if_true] using
    symmetric_tetradentate_empty_finished_state

private theorem symmetric_tetradentate_two_center_solver_none :
    solveExactCircularPositionDependencies? symmetricTetradentateNormalized
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens
      (analysisFuel symmetricTetradentateNormalized.parsed.withExplicitHydrogens)
      (rawAnnotatedCenters symmetricTetradentateNormalized) = none := by
  rw [symmetric_tetradentate_annotated_centers_empty]
  rfl

private theorem symmetric_tetradentate_four_center_solver_none :
    solveExactFourCenterCircularDependencies? symmetricTetradentateNormalized
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens
      (analysisFuel symmetricTetradentateNormalized.parsed.withExplicitHydrogens)
      (rawAnnotatedCenters symmetricTetradentateNormalized) = none := by
  rw [symmetric_tetradentate_annotated_centers_empty]
  rfl

private theorem symmetric_tetradentate_descriptor_state_empty :
    discoverRawDescriptors symmetricTetradentateNormalized
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens
      (analysisFuel symmetricTetradentateNormalized.parsed.withExplicitHydrogens) = [] := by
  have sourceEmpty :
      discoverRawDescriptorSource symmetricTetradentateNormalized
        symmetricTetradentateNormalized.parsed.withExplicitHydrogens
        (analysisFuel symmetricTetradentateNormalized.parsed.withExplicitHydrogens) = [] := by
    unfold discoverRawDescriptorSource certifiedRawDescriptorSource
    simp only [symmetric_tetradentate_initial_descriptor_state_empty,
      List.isEmpty_nil, ↓reduceIte]
    split
    · rename_i facts accepted
      simp [symmetric_tetradentate_two_center_solver_none] at accepted
    · split
      · rename_i facts accepted
        simp [symmetric_tetradentate_four_center_solver_none] at accepted
      · exact symmetric_tetradentate_constructive_source_empty
  simp [discoverRawDescriptors, sourceEmpty, normalizeTwoCyclicRule6AnchorCarrier]

private theorem symmetric_tetradentate_component_at_one :
    symmetricTetradentateNormalized.parsed.withExplicitHydrogens.coordinationLigandComponent
      0 1 = [1, 2, 4, 3] := by
  decide

private theorem symmetric_tetradentate_component_at_two :
    symmetricTetradentateNormalized.parsed.withExplicitHydrogens.coordinationLigandComponent
      0 2 = [2, 1, 3, 4] := by
  decide

private theorem symmetric_tetradentate_component_at_three :
    symmetricTetradentateNormalized.parsed.withExplicitHydrogens.coordinationLigandComponent
      0 3 = [3, 2, 4, 1] := by
  decide

private theorem symmetric_tetradentate_component_at_four :
    symmetricTetradentateNormalized.parsed.withExplicitHydrogens.coordinationLigandComponent
      0 4 = [4, 3, 1, 2] := by
  decide

private theorem symmetric_tetradentate_one_half_turn_permutation :
    ([3, 4, 2, 1] : List Nat) ∈ [1, 2, 4, 3].permutations := by
  rw [List.mem_permutations]
  decide

private theorem symmetric_tetradentate_two_half_turn_permutation :
    ([4, 3, 1, 2] : List Nat) ∈ [2, 1, 3, 4].permutations := by
  rw [List.mem_permutations]
  decide

private theorem symmetric_tetradentate_three_half_turn_permutation :
    ([1, 4, 2, 3] : List Nat) ∈ [3, 2, 4, 1].permutations := by
  rw [List.mem_permutations]
  decide

private theorem symmetric_tetradentate_four_half_turn_permutation :
    ([2, 1, 3, 4] : List Nat) ∈ [4, 3, 1, 2].permutations := by
  rw [List.mem_permutations]
  decide

private theorem symmetric_tetradentate_one_self_symmetry :
    symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [1, 2, 4, 3] [1, 2] [1, 2] = true := by
  apply ChemistryNormalizationResult.coordinatingFragmentsSymmetryRelated_of_witness
    (targetOrder := [1, 2, 4, 3])
  all_goals decide

private theorem symmetric_tetradentate_one_cross_symmetry :
    symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [1, 2, 4, 3] [1, 2] [3, 4] = true := by
  apply ChemistryNormalizationResult.coordinatingFragmentsSymmetryRelated_of_witness
    (targetOrder := [3, 4, 2, 1])
  all_goals first | exact symmetric_tetradentate_one_half_turn_permutation | decide

private theorem symmetric_tetradentate_two_self_symmetry :
    symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [2, 1, 3, 4] [1, 2] [1, 2] = true := by
  apply ChemistryNormalizationResult.coordinatingFragmentsSymmetryRelated_of_witness
    (targetOrder := [2, 1, 3, 4])
  all_goals decide

private theorem symmetric_tetradentate_two_cross_symmetry :
    symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [2, 1, 3, 4] [1, 2] [3, 4] = true := by
  apply ChemistryNormalizationResult.coordinatingFragmentsSymmetryRelated_of_witness
    (targetOrder := [4, 3, 1, 2])
  all_goals first | exact symmetric_tetradentate_two_half_turn_permutation | decide

private theorem symmetric_tetradentate_three_cross_symmetry :
    symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [3, 2, 4, 1] [3, 4] [1, 2] = true := by
  apply ChemistryNormalizationResult.coordinatingFragmentsSymmetryRelated_of_witness
    (targetOrder := [1, 4, 2, 3])
  all_goals first | exact symmetric_tetradentate_three_half_turn_permutation | decide

private theorem symmetric_tetradentate_three_self_symmetry :
    symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [3, 2, 4, 1] [3, 4] [3, 4] = true := by
  apply ChemistryNormalizationResult.coordinatingFragmentsSymmetryRelated_of_witness
    (targetOrder := [3, 2, 4, 1])
  all_goals decide

private theorem symmetric_tetradentate_four_cross_symmetry :
    symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [4, 3, 1, 2] [3, 4] [1, 2] = true := by
  apply ChemistryNormalizationResult.coordinatingFragmentsSymmetryRelated_of_witness
    (targetOrder := [2, 1, 3, 4])
  all_goals first | exact symmetric_tetradentate_four_half_turn_permutation | decide

private theorem symmetric_tetradentate_four_self_symmetry :
    symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [4, 3, 1, 2] [3, 4] [3, 4] = true := by
  apply ChemistryNormalizationResult.coordinatingFragmentsSymmetryRelated_of_witness
    (targetOrder := [4, 3, 1, 2])
  all_goals decide

private theorem filter_range_two_of_both_true (predicate : Nat → Bool)
    (zero : predicate 0 = true) (one : predicate 1 = true) :
    (List.range 2).filter predicate = [0, 1] := by
  change [0, 1].filter predicate = [0, 1]
  simp [zero, one]

private theorem find_range_two_of_zero_true (predicate : Nat → Bool)
    (zero : predicate 0 = true) :
    (List.range 2).find? predicate = some 0 := by
  change [0, 1].find? predicate = some 0
  simp [zero]

private theorem symmetric_tetradentate_one_related_positions :
    (List.range 2).filter (fun other =>
      symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
        symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
        [1, 2, 4, 3] [1, 2] (([[1, 2], [3, 4]][other]?).getD [])) = [0, 1] := by
  apply filter_range_two_of_both_true
  · simpa using symmetric_tetradentate_one_self_symmetry
  · simpa using symmetric_tetradentate_one_cross_symmetry

private theorem symmetric_tetradentate_one_first_related_position :
    (List.range 2).find? (fun other =>
      symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
        symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
        [1, 2, 4, 3] [1, 2] (([[1, 2], [3, 4]][other]?).getD [])) = some 0 := by
  apply find_range_two_of_zero_true
  simpa using symmetric_tetradentate_one_self_symmetry

private theorem symmetric_tetradentate_two_related_positions :
    (List.range 2).filter (fun other =>
      symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
        symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
        [2, 1, 3, 4] [1, 2] (([[1, 2], [3, 4]][other]?).getD [])) = [0, 1] := by
  apply filter_range_two_of_both_true
  · simpa using symmetric_tetradentate_two_self_symmetry
  · simpa using symmetric_tetradentate_two_cross_symmetry

private theorem symmetric_tetradentate_two_first_related_position :
    (List.range 2).find? (fun other =>
      symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
        symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
        [2, 1, 3, 4] [1, 2] (([[1, 2], [3, 4]][other]?).getD [])) = some 0 := by
  apply find_range_two_of_zero_true
  simpa using symmetric_tetradentate_two_self_symmetry

private theorem symmetric_tetradentate_three_related_positions :
    (List.range 2).filter (fun other =>
      symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
        symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
        [3, 2, 4, 1] [3, 4] (([[1, 2], [3, 4]][other]?).getD [])) = [0, 1] := by
  apply filter_range_two_of_both_true
  · simpa using symmetric_tetradentate_three_cross_symmetry
  · simpa using symmetric_tetradentate_three_self_symmetry

private theorem symmetric_tetradentate_three_first_related_position :
    (List.range 2).find? (fun other =>
      symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
        symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
        [3, 2, 4, 1] [3, 4] (([[1, 2], [3, 4]][other]?).getD [])) = some 0 := by
  apply find_range_two_of_zero_true
  simpa using symmetric_tetradentate_three_cross_symmetry

private theorem symmetric_tetradentate_four_related_positions :
    (List.range 2).filter (fun other =>
      symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
        symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
        [4, 3, 1, 2] [3, 4] (([[1, 2], [3, 4]][other]?).getD [])) = [0, 1] := by
  apply filter_range_two_of_both_true
  · simpa using symmetric_tetradentate_four_cross_symmetry
  · simpa using symmetric_tetradentate_four_self_symmetry

private theorem symmetric_tetradentate_four_first_related_position :
    (List.range 2).find? (fun other =>
      symmetricTetradentateNormalized.coordinatingFragmentsSymmetryRelated?
        symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
        [4, 3, 1, 2] [3, 4] (([[1, 2], [3, 4]][other]?).getD [])) = some 0 := by
  apply find_range_two_of_zero_true
  simpa using symmetric_tetradentate_four_cross_symmetry

private theorem symmetric_tetradentate_first_fragment_one :
    firstCoordinatingFragmentPosition? [[1, 2], [3, 4]] 1 = some 0 := by
  decide

private theorem symmetric_tetradentate_first_fragment_two :
    firstCoordinatingFragmentPosition? [[1, 2], [3, 4]] 2 = some 0 := by
  decide

private theorem symmetric_tetradentate_first_fragment_three :
    firstCoordinatingFragmentPosition? [[1, 2], [3, 4]] 3 = some 1 := by
  decide

private theorem symmetric_tetradentate_first_fragment_four :
    firstCoordinatingFragmentPosition? [[1, 2], [3, 4]] 4 = some 1 := by
  decide

private theorem symmetric_tetradentate_expected_fragment_membership_zero :
    symmetricTetradentateNormalized.expectedCoordinatingFragmentMembershipAt?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [1, 2, 3, 4] [[1, 2], [3, 4]] 0 = member 0 0 := by
  unfold ChemistryNormalizationResult.expectedCoordinatingFragmentMembershipAt?
  simp [member, symmetric_tetradentate_first_fragment_one,
    symmetric_tetradentate_component_at_one,
    symmetric_tetradentate_one_related_positions,
    symmetric_tetradentate_one_first_related_position]

private theorem symmetric_tetradentate_expected_fragment_membership_one :
    symmetricTetradentateNormalized.expectedCoordinatingFragmentMembershipAt?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [1, 2, 3, 4] [[1, 2], [3, 4]] 1 = member 0 0 := by
  unfold ChemistryNormalizationResult.expectedCoordinatingFragmentMembershipAt?
  simp [member, symmetric_tetradentate_first_fragment_two,
    symmetric_tetradentate_component_at_two,
    symmetric_tetradentate_two_related_positions,
    symmetric_tetradentate_two_first_related_position]

private theorem symmetric_tetradentate_expected_fragment_membership_two :
    symmetricTetradentateNormalized.expectedCoordinatingFragmentMembershipAt?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [1, 2, 3, 4] [[1, 2], [3, 4]] 2 = member 0 1 := by
  unfold ChemistryNormalizationResult.expectedCoordinatingFragmentMembershipAt?
  simp [member, symmetric_tetradentate_first_fragment_three,
    symmetric_tetradentate_component_at_three,
    symmetric_tetradentate_three_related_positions,
    symmetric_tetradentate_three_first_related_position]

private theorem symmetric_tetradentate_expected_fragment_membership_three :
    symmetricTetradentateNormalized.expectedCoordinatingFragmentMembershipAt?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [1, 2, 3, 4] [[1, 2], [3, 4]] 3 = member 0 1 := by
  unfold ChemistryNormalizationResult.expectedCoordinatingFragmentMembershipAt?
  simp [member, symmetric_tetradentate_first_fragment_four,
    symmetric_tetradentate_component_at_four,
    symmetric_tetradentate_four_related_positions,
    symmetric_tetradentate_four_first_related_position]

private theorem symmetric_tetradentate_fragment_candidate_exact :
    symmetricTetradentateNormalized.candidateCoordinatingFragmentPrimingMemberships
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [1, 2, 3, 4] [[1, 2], [3, 4]] =
      [member 0 0, member 0 0, member 0 1, member 0 1] := by
  unfold ChemistryNormalizationResult.candidateCoordinatingFragmentPrimingMemberships
  change
    [ symmetricTetradentateNormalized.expectedCoordinatingFragmentMembershipAt?
        symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
        [1, 2, 3, 4] [[1, 2], [3, 4]] 0,
      symmetricTetradentateNormalized.expectedCoordinatingFragmentMembershipAt?
        symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
        [1, 2, 3, 4] [[1, 2], [3, 4]] 1,
      symmetricTetradentateNormalized.expectedCoordinatingFragmentMembershipAt?
        symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
        [1, 2, 3, 4] [[1, 2], [3, 4]] 2,
      symmetricTetradentateNormalized.expectedCoordinatingFragmentMembershipAt?
        symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
        [1, 2, 3, 4] [[1, 2], [3, 4]] 3 ] =
      [member 0 0, member 0 0, member 0 1, member 0 1]
  rw [symmetric_tetradentate_expected_fragment_membership_zero,
    symmetric_tetradentate_expected_fragment_membership_one,
    symmetric_tetradentate_expected_fragment_membership_two,
    symmetric_tetradentate_expected_fragment_membership_three]

private theorem symmetric_tetradentate_component_one_donor_positions :
    (List.range [1, 2, 3, 4].length).filter (fun position =>
      [1, 2, 4, 3].contains (([1, 2, 3, 4][position]?).getD 0)) = [0, 1, 2, 3] := by
  rfl

private theorem symmetric_tetradentate_component_three_donor_positions :
    (List.range [1, 2, 3, 4].length).filter (fun position =>
      [3, 2, 4, 1].contains (([1, 2, 3, 4][position]?).getD 0)) = [0, 1, 2, 3] := by
  rfl

private theorem symmetric_tetradentate_fragment_observation_valid :
    symmetricTetradentateNormalized.coordinatingFragmentObservationOK?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [1, 2, 3, 4] [[1, 2], [3, 4]] = true := by
  unfold ChemistryNormalizationResult.coordinatingFragmentObservationOK?
  simp [RawMolecule.firstNatIndex?, sameFiniteAtomSet,
    symmetric_tetradentate_component_at_one,
    symmetric_tetradentate_component_at_two,
    symmetric_tetradentate_component_at_three,
    symmetric_tetradentate_component_at_four,
    symmetric_tetradentate_one_cross_symmetry,
    symmetric_tetradentate_three_cross_symmetry]
  simp [List.range, List.range.loop]
  decide

private theorem symmetric_tetradentate_fragment_candidate_valid :
    symmetricTetradentateNormalized.coordinatingFragmentPrimingMembershipsOK?
      symmetricTetradentateNormalized.parsed.withExplicitHydrogens [] 0
      [1, 2, 3, 4] [[1, 2], [3, 4]]
      [member 0 0, member 0 0, member 0 1, member 0 1] = true := by
  unfold ChemistryNormalizationResult.coordinatingFragmentPrimingMembershipsOK?
  simp only [symmetric_tetradentate_fragment_observation_valid, Bool.true_and,
    Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
  refine ⟨by decide, ?_⟩
  intro position positionLt
  have positionLtFour : position < 4 := by
    simpa using positionLt
  interval_cases position <;>
    simp [RedBookIR9.finitePrimingMembershipAt,
      symmetric_tetradentate_expected_fragment_membership_zero,
      symmetric_tetradentate_expected_fragment_membership_one,
      symmetric_tetradentate_expected_fragment_membership_two,
      symmetric_tetradentate_expected_fragment_membership_three]

theorem symmetry_related_fragments_are_checked_and_derived :
    let context := symmetricTetradentateNormalized.geometryPriorityState
    symmetricTetradentateNormalized.deriveCoordinatingFragmentPrimingMemberships?
        context.1 context.2.2 0 [1, 2, 3, 4] [[1, 2], [3, 4]] =
      some [member 0 0, member 0 0, member 0 1, member 0 1] := by
  simp only [ChemistryNormalizationResult.geometryPriorityState]
  rw [symmetric_tetradentate_descriptor_state_empty]
  unfold ChemistryNormalizationResult.deriveCoordinatingFragmentPrimingMemberships?
  rw [symmetric_tetradentate_fragment_candidate_exact]
  simp [symmetric_tetradentate_fragment_candidate_valid]

theorem symmetry_related_fragments_receive_derived_prime_counts :
    symmetricTetradentateNormalized.observedPolyhedralPriorityNumbers?
        0 .tetrahedron [1, 2, 3, 4]
        (.symmetryRelatedCoordinatingFragments [[1, 2], [3, 4]]) =
      some
        [ { number := 1, primes := 0 }, { number := 1, primes := 0 },
          { number := 1, primes := 1 }, { number := 1, primes := 1 } ] := by
  unfold ChemistryNormalizationResult.observedPolyhedralPriorityNumbers?
  simp only [ChemistryNormalizationResult.geometryPriorityState]
  rw [symmetric_tetradentate_descriptor_state_empty]
  have memberships := symmetry_related_fragments_are_checked_and_derived
  simp only [ChemistryNormalizationResult.geometryPriorityState] at memberships
  rw [symmetric_tetradentate_descriptor_state_empty] at memberships
  rw [memberships]
  decide

/-- Mere subset assertions are insufficient: fragments from different connected ligands are
rejected because no within-one-ligand automorphism can relate them. -/
theorem cross_ligand_fragment_claim_is_rejected :
    bisBidentateNormalized.observedPolyhedralPriorityNumbers?
        0 .tetrahedron [1, 2, 3, 4]
        (.symmetryRelatedCoordinatingFragments [[1, 2], [3, 4]]) = none := by
  decide

private def nitrogen : AtomSpec :=
  { element := .N, explicitHydrogens? := some 0 }

/-- A geometry-free graph with three distinct N substituents is deliberately not enough to infer
a pyramidal center. -/
private def observedTrigonalPyramidalMolecule : RawMolecule where
  atoms := [nitrogen, fluorine, chlorine, bromine]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single } ]
  neighborOrder := [[1, 2, 3], [0], [0], [0]]

private def observedTrigonalPyramidalNormalized :=
  normalizeRawMolecule observedTrigonalPyramidalMolecule

private def trigonalPyramidalGeometry : IndexedCIPGeometryObservations where
  polyhedra :=
    [{ center := 0
       geometry := .trigonalPyramid
       recognition := .threeCoordinate .centerSignificantlyOutOfDonorPlane
       ligands := [1, 2, 3]
       configurationPositions := .noDistinguishedPositions
       absoluteOrientation := .trigonalPyramidRS .clockwise }]

theorem three_coordinate_nitrogen_requires_geometry_but_then_receives_IR9_RS :
    analyzeNormalized observedTrigonalPyramidalNormalized = [] ∧
      analyzeNormalizedWithObservedGeometry observedTrigonalPyramidalNormalized
        trigonalPyramidalGeometry =
        [{ unit := StereoUnit.polyhedron 0
           outcome := StereoOutcome.polyhedral
             { geometry := .trigonalPyramid
               configurationIndex := []
               absolute? := some (.rs .R) } }] := by
  decide

private def tiedTrigonalPyramidalMolecule : RawMolecule where
  atoms := [nitrogen, fluorine, fluorine, chlorine]
  bonds :=
    [ { source := 0, target := 1, kind := .single },
      { source := 0, target := 2, kind := .single },
      { source := 0, target := 3, kind := .single } ]
  neighborOrder := [[1, 2, 3], [0], [0], [0]]

private def tiedTrigonalPyramidalNormalized :=
  normalizeRawMolecule tiedTrigonalPyramidalMolecule

private def tiedTrigonalPyramidalGeometry : IndexedCIPGeometryObservations where
  polyhedra :=
    [{ center := 0
       geometry := .trigonalPyramid
       recognition := .threeCoordinate .centerSignificantlyOutOfDonorPlane
       ligands := [1, 2, 3]
       configurationPositions := .noDistinguishedPositions
       absoluteOrientation := .trigonalPyramidRS .clockwise }]

/-- A raw clockwise sense cannot manufacture `R` when two final ligand priorities are equal. -/
theorem tied_trigonal_pyramid_refuses_absolute_descriptor :
    analyzeNormalizedWithObservedGeometry tiedTrigonalPyramidalNormalized
      tiedTrigonalPyramidalGeometry = [] := by
  decide

end TetraStereo.Examples.GeometryAnnotatedCIPAnalysis
