import TetraStereo.OneCenter.AuthoritativeLocalizedTetrahedralDescriptor
import TetraStereo.OneCenter.AuthoritativeLocalizedRuleMajorAnalysis

set_option autoImplicit false

namespace TetraStereo.Examples.AuthoritativeLocalizedCIPAnalysis

open OneCenter

private def element (atomicNumber : ℕ) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : PeriodicElement :=
  { atomicNumber := atomicNumber, positive := positive, atMost118 := bounded }

private def carbon : PeriodicElement := element 6 (by decide) (by decide)
private def fluorine : PeriodicElement := element 9 (by decide) (by decide)
private def chlorine : PeriodicElement := element 17 (by decide) (by decide)
private def bromine : PeriodicElement := element 35 (by decide) (by decide)
private def iodine : PeriodicElement := element 53 (by decide) (by decide)

/-- A format-neutral localized molecule with one constitutional four-neighbor center. -/
private def halomethaneInput : AuthoritativeChemicalInput :=
  { molecule :=
      { atoms :=
          [{ element := carbon }, { element := fluorine }, { element := chlorine },
           { element := bromine }, { element := iodine }]
        interactions :=
          [{ participants := [0, 1], kind := .covalent 1 },
           { participants := [0, 2], kind := .covalent 1 },
           { participants := [0, 3], kind := .covalent 1 },
           { participants := [0, 4], kind := .covalent 1 }] }
    spatial? := some
      { positions :=
          [{ x := 0, y := 0, z := 0 },
           { x := -1, y := -1, z := 1 },
           { x := -1, y := 1, z := -1 },
           { x := 1, y := -1, z := -1 },
           { x := 1, y := 1, z := 1 }] } }

private def certifiedHalomethaneInput : CertifiedAuthoritativeChemicalInput :=
  (halomethaneInput.certify?).get (by decide)

private def localizedHalomethaneInput : CertifiedLocalizedCIPInput :=
  (certifiedHalomethaneInput.certifyLocalizedCIP?).get (by decide)

private def center : localizedHalomethaneInput.Atom := ⟨0, by decide⟩
private def fluorineAtom : localizedHalomethaneInput.Atom := ⟨1, by decide⟩
private def chlorineAtom : localizedHalomethaneInput.Atom := ⟨2, by decide⟩
private def bromineAtom : localizedHalomethaneInput.Atom := ⟨3, by decide⟩
private def iodineAtom : localizedHalomethaneInput.Atom := ⟨4, by decide⟩

/-- Detection is automatic from the semantic bond records; no center index was supplied to it. -/
theorem carbon_is_automatically_detected :
    center ∈ localizedHalomethaneInput.tetrahedralCenterSet := by
  decide

private def detectedCenter : localizedHalomethaneInput.TetrahedralCenter :=
  ⟨center, carbon_is_automatically_detected⟩

private def emptyContext (_index : Fin 4) : CIPRuleEngine.OfficialLigandRuleContext :=
  CIPRuleEngine.OfficialLigandRuleContext.empty

/-- For this example, automatic detection finds the carbon and no terminal halogen. -/
theorem the_detected_center_set_is_exactly_carbon :
    localizedHalomethaneInput.tetrahedralCenterSet = {center} := by
  decide

/-- The abstract detection theorem exposes the exact semantic reason for that result: four
positive localized covalent records meet at carbon. -/
theorem carbon_has_exactly_four_semantic_neighbors :
    (localizedHalomethaneInput.semanticLocalizedNeighborFinset center).card = 4 :=
  (localizedHalomethaneInput.mem_tetrahedralCenterSet_iff_semantic_neighbor_count center).mp
    carbon_is_automatically_detected

private theorem carbon_neighbor_finset_is_exact :
    localizedHalomethaneInput.moleculeGraph.neighborFinset center =
      [fluorineAtom, chlorineAtom, bromineAtom, iodineAtom].toFinset := by
  ext atom
  fin_cases atom <;>
    simp [MoleculeGraph.mem_neighborFinset, MoleculeGraph.Adj,
      CertifiedLocalizedCIPInput.moleculeGraph,
      CertifiedAuthoritativeChemicalInput.certifyLocalizedCIP?,
      AuthoritativeChemicalInput.certify?, SemanticMolecule.toLocalizedMoleculeGraph,
      SemanticMolecule.atomCount,
      SemanticMolecule.localizedBondOrder, SemanticMolecule.localizedBondOrderAtKey,
      SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, semanticEdgeKey,
      localizedHalomethaneInput, certifiedHalomethaneInput, halomethaneInput,
      center, fluorineAtom, chlorineAtom, bromineAtom, iodineAtom]

private theorem canonical_neighbor_list_is_exact :
    localizedHalomethaneInput.canonicalNeighborList detectedCenter =
      [fluorineAtom, chlorineAtom, bromineAtom, iodineAtom] := by
  unfold CertifiedLocalizedCIPInput.canonicalNeighborList
  change (localizedHalomethaneInput.moleculeGraph.neighborFinset center).sort (· ≤ ·) =
    [fluorineAtom, chlorineAtom, bromineAtom, iodineAtom]
  rw [carbon_neighbor_finset_is_exact]
  exact (List.toFinset_sort (r := (· ≤ ·)) (by decide)).mpr (by decide)

private theorem canonical_ligand_atom_zero :
    localizedHalomethaneInput.canonicalLigandAtom detectedCenter 0 = fluorineAtom := by
  simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonical_neighbor_list_is_exact]

private theorem canonical_ligand_atom_one :
    localizedHalomethaneInput.canonicalLigandAtom detectedCenter 1 = chlorineAtom := by
  simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonical_neighbor_list_is_exact]

private theorem canonical_ligand_atom_two :
    localizedHalomethaneInput.canonicalLigandAtom detectedCenter 2 = bromineAtom := by
  simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonical_neighbor_list_is_exact]

private theorem canonical_ligand_atom_three :
    localizedHalomethaneInput.canonicalLigandAtom detectedCenter 3 = iodineAtom := by
  simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonical_neighbor_list_is_exact]

/-- The runtime ligand enumeration is canonical rather than choice-based: ascending atom indices
correspond to F, Cl, Br, and I. -/
theorem canonical_ligand_enumeration_is_executable :
    (List.finRange 4).map
        (fun index =>
          (localizedHalomethaneInput.canonicalLigandAtom detectedCenter index).val) =
      [1, 2, 3, 4] := by
  simp [CertifiedLocalizedCIPInput.canonicalLigandAtom, canonical_neighbor_list_is_exact,
    fluorineAtom, chlorineAtom, bromineAtom, iodineAtom]
  rfl'

/-- Ordinary iodine is monoisotopic, so its real root carries the exact 127-I nuclide mass from
the frozen CIAAW source rather than the abridged periodic-table display value. -/
theorem iodine_root_has_exact_source_label :
    localizedHalomethaneInput.moleculeGraph.officialNodeAtomLabel
        (OfficialCIPNode.rootFromEdge center iodineAtom) =
      toLex (53, 126904472592000) := by
  decide

/-- The official root trace ranks F below I by Rule 1a. Later mass/provenance entries cannot
override that decisive atomic-number result. -/
theorem fluorine_precedes_iodine_by_official_root_trace :
    cipTraceOutcome
      (localizedHalomethaneInput.moleculeGraph.compareOfficialNodeTrace
        (OfficialCIPNode.rootFromEdge center fluorineAtom)
        (OfficialCIPNode.rootFromEdge center iodineAtom)) = Ordering.lt := by
  apply localizedHalomethaneInput.official_root_trace_outcome_lt_of_atomicNumber_lt
  decide

/-- The full executable rule-major comparison reaches the same F-before-I result. The bounded
comparison returns an `Option`; a strict root atomic-number difference still forces a decisive
`lt` certificate projection. -/
theorem executable_hierarchy_ranks_fluorine_below_iodine :
    (localizedHalomethaneInput.compareAt detectedCenter emptyContext 0 3).map
        CIPTraceCertificate.outcome = some Ordering.lt := by
  apply localizedHalomethaneInput.compareAt_outcome_lt_of_root_atomicNumber_lt
  rw [canonical_ligand_atom_zero, canonical_ligand_atom_three]
  simp [
    CertifiedAuthoritativeChemicalInput.certifyLocalizedCIP?,
    AuthoritativeChemicalInput.certify?, SemanticMolecule.atomCount,
    localizedHalomethaneInput, certifiedHalomethaneInput, halomethaneInput,
    fluorineAtom, iodineAtom, fluorine, iodine, element]

private theorem canonical_ligand_atomicNumber_lt_of_lt
    {left right : Fin 4} (lower : left < right) :
    (localizedHalomethaneInput.certified.input.molecule.atoms.get
        (localizedHalomethaneInput.canonicalLigandAtom detectedCenter left)).element.atomicNumber <
      (localizedHalomethaneInput.certified.input.molecule.atoms.get
        (localizedHalomethaneInput.canonicalLigandAtom detectedCenter right)).element.atomicNumber := by
  fin_cases left <;> fin_cases right
  all_goals simp_all only [CertifiedLocalizedCIPInput.canonicalLigandAtom,
    canonical_neighbor_list_is_exact, List.get_eq_getElem]
  all_goals norm_num at lower
  all_goals norm_num [CertifiedAuthoritativeChemicalInput.certifyLocalizedCIP?,
    AuthoritativeChemicalInput.certify?, SemanticMolecule.atomCount,
    localizedHalomethaneInput, certifiedHalomethaneInput, halomethaneInput,
    fluorineAtom, chlorineAtom, bromineAtom, iodineAtom,
    fluorine, chlorine, bromine, iodine, element]

private theorem compareAt_outcome_lt_of_lt {left right : Fin 4} (lower : left < right) :
    (localizedHalomethaneInput.compareAt detectedCenter emptyContext left right).map
        CIPTraceCertificate.outcome = some Ordering.lt :=
  localizedHalomethaneInput.compareAt_outcome_lt_of_root_atomicNumber_lt
    detectedCenter emptyContext left right (canonical_ligand_atomicNumber_lt_of_lt lower)

private theorem compareAt_outcome_gt_of_gt {left right : Fin 4} (higher : right < left) :
    (localizedHalomethaneInput.compareAt detectedCenter emptyContext left right).map
        CIPTraceCertificate.outcome = some Ordering.gt :=
  localizedHalomethaneInput.compareAt_outcome_gt_of_root_atomicNumber_gt
    detectedCenter emptyContext left right (canonical_ligand_atomicNumber_lt_of_lt higher)

private theorem ligandBeforeAt_eq_descending_index (left right : Fin 4) :
    localizedHalomethaneInput.ligandBeforeAt detectedCenter emptyContext left right =
      decide (right ≤ left) := by
  rcases lt_trichotomy left right with lower | equal | higher
  · obtain ⟨certificate, computed, outcome⟩ := Option.map_eq_some_iff.mp
      (compareAt_outcome_lt_of_lt lower)
    simp [CertifiedLocalizedCIPInput.ligandBeforeAt, computed, outcome, not_le.mpr lower]
  · subst right
    obtain ⟨certificate, computed, outcome⟩ := Option.map_eq_some_iff.mp
      (localizedHalomethaneInput.compareAt_outcome_self
        detectedCenter emptyContext left)
    simp [CertifiedLocalizedCIPInput.ligandBeforeAt, computed, outcome]
  · obtain ⟨certificate, computed, outcome⟩ := Option.map_eq_some_iff.mp
      (compareAt_outcome_gt_of_gt higher)
    simp [CertifiedLocalizedCIPInput.ligandBeforeAt, computed, outcome, higher.le]

private theorem localizedHalomethane_resolved :
    localizedHalomethaneInput.resolvedAt? detectedCenter emptyContext = true := by
  apply (localizedHalomethaneInput.resolvedAt?_eq_true_iff
    detectedCenter emptyContext).mpr
  intro left right different
  rcases lt_trichotomy left right with lower | equal | higher
  · rw [compareAt_outcome_lt_of_lt lower]
    decide
  · exact (different equal).elim
  · rw [compareAt_outcome_gt_of_gt higher]
    decide

private theorem executable_ligand_order_is_exact :
    localizedHalomethaneInput.ligandOrderAt detectedCenter emptyContext = [3, 2, 1, 0] := by
  unfold CertifiedLocalizedCIPInput.ligandOrderAt
  have relation : localizedHalomethaneInput.ligandBeforeAt detectedCenter emptyContext =
      fun left right => decide (right ≤ left) := by
    funext left right
    exact ligandBeforeAt_eq_descending_index left right
  rw [relation]
  rw [List.mergeSort_eq_insertionSort]
  decide

private theorem executable_safe_order_is_exact :
    localizedHalomethaneInput.ligandOrderAt? detectedCenter emptyContext =
      some [3, 2, 1, 0] := by
  simp [CertifiedLocalizedCIPInput.ligandOrderAt?, localizedHalomethane_resolved,
    executable_ligand_order_is_exact]

/-- All six ligand comparisons resolve, and the safe runtime order is I > Br > Cl > F. -/
theorem executable_safe_order_is_iodine_bromine_chlorine_fluorine :
    (localizedHalomethaneInput.ligandOrderAt? detectedCenter emptyContext).map
      (List.map Fin.val) = some [3, 2, 1, 0] := by
  rw [executable_safe_order_is_exact]
  rfl

/-- The replacement arbitrary-width rule-major compiler independently reaches the same strict
Rule-1a result on this constitutional example. -/
theorem rule_major_comparison_ranks_fluorine_below_iodine :
    (localizedHalomethaneInput.compareRuleMajorAt?
      detectedCenter emptyContext 0 3).map CIPTraceCertificate.outcome =
      some Ordering.lt := by
  apply localizedHalomethaneInput.compareRuleMajorAt?_outcome_lt_of_root_atomicNumber_lt
  rw [canonical_ligand_atom_zero, canonical_ligand_atom_three]
  simp [
    CertifiedAuthoritativeChemicalInput.certifyLocalizedCIP?,
    AuthoritativeChemicalInput.certify?, SemanticMolecule.atomCount,
    localizedHalomethaneInput, certifiedHalomethaneInput, halomethaneInput,
    fluorineAtom, iodineAtom, fluorine, iodine, element]

private theorem compareRuleMajorAt_outcome_lt_of_lt
    {left right : Fin 4} (lower : left < right) :
    (localizedHalomethaneInput.compareRuleMajorAt?
      detectedCenter emptyContext left right).map CIPTraceCertificate.outcome =
      some Ordering.lt :=
  localizedHalomethaneInput.compareRuleMajorAt?_outcome_lt_of_root_atomicNumber_lt
    detectedCenter emptyContext left right (canonical_ligand_atomicNumber_lt_of_lt lower)

private theorem compareRuleMajorAt_outcome_gt_of_gt
    {left right : Fin 4} (higher : right < left) :
    (localizedHalomethaneInput.compareRuleMajorAt?
      detectedCenter emptyContext left right).map CIPTraceCertificate.outcome =
      some Ordering.gt :=
  localizedHalomethaneInput.compareRuleMajorAt?_outcome_gt_of_root_atomicNumber_gt
    detectedCenter emptyContext left right (canonical_ligand_atomicNumber_lt_of_lt higher)

private theorem compareRuleMajorAt_exists_gt_of_gt
    {left right : Fin 4} (higher : right < left) :
    ∃ certificate,
      localizedHalomethaneInput.compareRuleMajorAt?
          detectedCenter emptyContext left right = some certificate ∧
        certificate.outcome = Ordering.gt :=
  Option.map_eq_some_iff.mp (compareRuleMajorAt_outcome_gt_of_gt higher)

private theorem ruleMajorLigandBeforeAt_eq_descending_index (left right : Fin 4) :
    localizedHalomethaneInput.ruleMajorLigandBeforeAt
        detectedCenter emptyContext left right = decide (right ≤ left) := by
  rcases lt_trichotomy left right with lower | equal | higher
  · obtain ⟨certificate, computed, outcome⟩ := Option.map_eq_some_iff.mp
      (compareRuleMajorAt_outcome_lt_of_lt lower)
    simp [CertifiedLocalizedCIPInput.ruleMajorLigandBeforeAt, computed, outcome,
      not_le.mpr lower]
  · subst right
    obtain ⟨certificate, computed, outcome⟩ := Option.map_eq_some_iff.mp
      (localizedHalomethaneInput.compareRuleMajorAt?_outcome_self
        detectedCenter emptyContext left)
    simp [CertifiedLocalizedCIPInput.ruleMajorLigandBeforeAt, computed, outcome]
  · obtain ⟨certificate, computed, outcome⟩ := Option.map_eq_some_iff.mp
      (compareRuleMajorAt_outcome_gt_of_gt higher)
    simp [CertifiedLocalizedCIPInput.ruleMajorLigandBeforeAt, computed, outcome, higher.le]

private theorem ruleMajorPairResolvedAt_of_ne
    (left right : Fin 4) (different : left ≠ right) :
    localizedHalomethaneInput.ruleMajorPairResolvedAt?
      detectedCenter emptyContext left right = true := by
  rcases lt_trichotomy left right with lower | equal | higher
  · obtain ⟨certificate, computed, outcome⟩ := Option.map_eq_some_iff.mp
      (compareRuleMajorAt_outcome_lt_of_lt lower)
    simp [CertifiedLocalizedCIPInput.ruleMajorPairResolvedAt?, computed, outcome]
  · exact (different equal).elim
  · obtain ⟨certificate, computed, outcome⟩ := Option.map_eq_some_iff.mp
      (compareRuleMajorAt_outcome_gt_of_gt higher)
    simp [CertifiedLocalizedCIPInput.ruleMajorPairResolvedAt?, computed, outcome]

private theorem localizedHalomethane_ruleMajorResolved :
    localizedHalomethaneInput.ruleMajorResolvedAt? detectedCenter emptyContext = true := by
  unfold CertifiedLocalizedCIPInput.ruleMajorResolvedAt?
  apply List.all_eq_true.mpr
  intro left _leftPresent
  apply List.all_eq_true.mpr
  intro right _rightPresent
  by_cases equal : left = right
  · simp [equal]
  · simp [equal, ruleMajorPairResolvedAt_of_ne left right equal]

private theorem ruleMajor_ligand_order_is_exact :
    localizedHalomethaneInput.ruleMajorLigandOrderAt
      detectedCenter emptyContext = [3, 2, 1, 0] := by
  unfold CertifiedLocalizedCIPInput.ruleMajorLigandOrderAt
  have relation :
      localizedHalomethaneInput.ruleMajorLigandBeforeAt detectedCenter emptyContext =
        fun left right => decide (right ≤ left) := by
    funext left right
    exact ruleMajorLigandBeforeAt_eq_descending_index left right
  rw [relation]
  rw [List.mergeSort_eq_insertionSort]
  decide

private theorem localizedHalomethane_ruleMajorCoherent :
    localizedHalomethaneInput.ruleMajorOrderCoherentAt?
      detectedCenter emptyContext = true := by
  unfold CertifiedLocalizedCIPInput.ruleMajorOrderCoherentAt?
  rw [ruleMajor_ligand_order_is_exact]
  apply (localizedHalomethaneInput.ruleMajorOrderCoherentListAt?_eq_true_iff
    detectedCenter emptyContext [3, 2, 1, 0]).mpr
  simp only [List.pairwise_cons]
  constructor
  · intro right present
    obtain rfl | rfl | rfl := by simpa using present
    · exact compareRuleMajorAt_exists_gt_of_gt (by decide)
    · exact compareRuleMajorAt_exists_gt_of_gt (by decide)
    · exact compareRuleMajorAt_exists_gt_of_gt (by decide)
  constructor
  · intro right present
    obtain rfl | rfl := by simpa using present
    · exact compareRuleMajorAt_exists_gt_of_gt (by decide)
    · exact compareRuleMajorAt_exists_gt_of_gt (by decide)
  constructor
  · intro right present
    have : right = 0 := by simpa using present
    subst right
    exact compareRuleMajorAt_exists_gt_of_gt (by decide)
  · constructor
    · simp
    · exact List.Pairwise.nil

private theorem ruleMajor_safe_order_is_exact :
    localizedHalomethaneInput.ruleMajorLigandOrderAt?
      detectedCenter emptyContext = some [3, 2, 1, 0] := by
  simp [CertifiedLocalizedCIPInput.ruleMajorLigandOrderAt?,
    localizedHalomethane_ruleMajorResolved, localizedHalomethane_ruleMajorCoherent,
    ruleMajor_ligand_order_is_exact]

/-- All six comparisons also resolve through exhaustive rule-major keys, with the expected order. -/
theorem rule_major_safe_order_is_iodine_bromine_chlorine_fluorine :
    (localizedHalomethaneInput.ruleMajorLigandOrderAt?
      detectedCenter emptyContext).map (List.map Fin.val) = some [3, 2, 1, 0] := by
  rw [ruleMajor_safe_order_is_exact]
  rfl

private def iodinePoint : CartesianPoint3 := { x := 1, y := 1, z := 1 }
private def brominePoint : CartesianPoint3 := { x := 1, y := -1, z := -1 }
private def chlorinePoint : CartesianPoint3 := { x := -1, y := 1, z := -1 }
private def fluorinePoint : CartesianPoint3 := { x := -1, y := -1, z := 1 }

private theorem priority_ordered_points_are_exact :
    localizedHalomethaneInput.priorityOrderedSpatialPoints?
      detectedCenter emptyContext =
        some [iodinePoint, brominePoint, chlorinePoint, fluorinePoint] := by
  unfold CertifiedLocalizedCIPInput.priorityOrderedSpatialPoints?
  rw [executable_safe_order_is_exact]
  change List.mapM
    (fun index => localizedHalomethaneInput.spatialPointAt?
      (localizedHalomethaneInput.canonicalLigandAtom detectedCenter index))
    [3, 2, 1, 0] = some [iodinePoint, brominePoint, chlorinePoint, fluorinePoint]
  simp only [List.mapM_cons, List.mapM_nil]
  rw [canonical_ligand_atom_three, canonical_ligand_atom_two,
    canonical_ligand_atom_one, canonical_ligand_atom_zero]
  rfl

private theorem ruleMajor_priority_ordered_points_are_exact :
    localizedHalomethaneInput.ruleMajorPriorityOrderedSpatialPoints?
      detectedCenter emptyContext =
        some [iodinePoint, brominePoint, chlorinePoint, fluorinePoint] := by
  unfold CertifiedLocalizedCIPInput.ruleMajorPriorityOrderedSpatialPoints?
  rw [ruleMajor_safe_order_is_exact]
  change List.mapM
    (fun index => localizedHalomethaneInput.spatialPointAt?
      (localizedHalomethaneInput.canonicalLigandAtom detectedCenter index))
    [3, 2, 1, 0] = some [iodinePoint, brominePoint, chlorinePoint, fluorinePoint]
  simp only [List.mapM_cons, List.mapM_nil]
  rw [canonical_ligand_atom_three, canonical_ligand_atom_two,
    canonical_ligand_atom_one, canonical_ligand_atom_zero]
  rfl

/-- The exact priority-ordered fixture has positive oriented volume `+16`.  Under the corrected
calibration (positive volume is `S`) the descriptor is therefore `S`, not `R`. -/
private theorem exact_points_have_S_geometry :
    CertifiedLocalizedCIPInput.RationalTetrahedralDescriptor
      [iodinePoint, brominePoint, chlorinePoint, fluorinePoint] RS.S := by
  refine ⟨iodinePoint, brominePoint, chlorinePoint, fluorinePoint, rfl, ?_⟩
  norm_num [CartesianPoint3.orientedVolume, iodinePoint, brominePoint,
    chlorinePoint, fluorinePoint]

/-- Exact rational spatial evidence completes the localized path to a safe `S` descriptor. -/
theorem exact_spatial_pipeline_emits_S :
    localizedHalomethaneInput.tetrahedralSpatialDescriptorAt?
      detectedCenter emptyContext = some RS.S := by
  apply (localizedHalomethaneInput.tetrahedralSpatialDescriptorAt?_eq_some_iff
    detectedCenter emptyContext RS.S).mpr
  exact ⟨[iodinePoint, brominePoint, chlorinePoint, fluorinePoint],
    priority_ordered_points_are_exact, exact_points_have_S_geometry⟩

/-- Historical API key retained for downstream imports.  Under the corrected calibration the
fixture emits `S`; the accurate name is `exact_spatial_pipeline_emits_S`. -/
theorem exact_spatial_pipeline_emits_R :
    localizedHalomethaneInput.tetrahedralSpatialDescriptorAt?
      detectedCenter emptyContext = some RS.S :=
  exact_spatial_pipeline_emits_S

/-- The replacement exhaustive rule-major path uses the same exact geometry and emits `S`. -/
theorem rule_major_exact_spatial_pipeline_emits_S :
    localizedHalomethaneInput.ruleMajorTetrahedralSpatialDescriptorAt?
      detectedCenter emptyContext = some RS.S := by
  apply (localizedHalomethaneInput.ruleMajorTetrahedralSpatialDescriptorAt?_eq_some_iff
    detectedCenter emptyContext RS.S).mpr
  exact ⟨[iodinePoint, brominePoint, chlorinePoint, fluorinePoint],
    ruleMajor_priority_ordered_points_are_exact, exact_points_have_S_geometry⟩

/-- Historical API key retained for downstream imports.  Its statement follows the corrected
calibration (the fixture emits `S`); the accurate name is
`rule_major_exact_spatial_pipeline_emits_S`. -/
theorem rule_major_exact_spatial_pipeline_emits_R :
    localizedHalomethaneInput.ruleMajorTetrahedralSpatialDescriptorAt?
      detectedCenter emptyContext = some RS.S :=
  rule_major_exact_spatial_pipeline_emits_S

/-- The emitted result is not merely a calculation fixture: the general soundness theorem yields
the priority-ordered rational witness and its equality to real tetrahedral handedness. -/
theorem exact_spatial_pipeline_S_has_real_handedness_witness :
    ∃ points first second third fourth,
      localizedHalomethaneInput.priorityOrderedSpatialPoints?
          detectedCenter emptyContext = some points ∧
      points = [first, second, third, fourth] ∧
      RS.S = RS.ofHandedness
        (TetrahedralGeometry.handedness
          (CartesianPoint3.toRealTetrahedralGeometry first second third fourth)) := by
  exact localizedHalomethaneInput.tetrahedralSpatialDescriptorAt?_sound_real_handedness
    detectedCenter emptyContext RS.S exact_spatial_pipeline_emits_S

/-- Historical API key retained for downstream imports.  Under the corrected calibration the
witness handedness is `S`; the accurate name is
`exact_spatial_pipeline_S_has_real_handedness_witness`. -/
theorem exact_spatial_pipeline_R_has_real_handedness_witness :
    ∃ points first second third fourth,
      localizedHalomethaneInput.priorityOrderedSpatialPoints?
          detectedCenter emptyContext = some points ∧
      points = [first, second, third, fourth] ∧
      RS.S = RS.ofHandedness
        (TetrahedralGeometry.handedness
          (CartesianPoint3.toRealTetrahedralGeometry first second third fourth)) :=
  exact_spatial_pipeline_S_has_real_handedness_witness

private theorem canonical_tetrahedral_centers_are_exact :
    localizedHalomethaneInput.canonicalTetrahedralCenters = [detectedCenter] := by
  have lengthOne : localizedHalomethaneInput.canonicalTetrahedralCenters.length = 1 := by
    simp [CertifiedLocalizedCIPInput.canonicalTetrahedralCenters,
      the_detected_center_set_is_exactly_carbon]
  obtain ⟨onlyCenter, exactList⟩ := List.length_eq_one_iff.mp lengthOne
  rw [exactList]
  have valueEquality : onlyCenter.1 = center := by
    have detected : onlyCenter.1 ∈ ({center} : Finset localizedHalomethaneInput.Atom) := by
      rw [← the_detected_center_set_is_exactly_carbon]
      exact onlyCenter.2
    exact Finset.mem_singleton.mp detected
  have centerEquality : onlyCenter = detectedCenter := Subtype.ext valueEquality
  rw [centerEquality]

/-- Whole-molecule analysis detects the center and emits exactly its proved spatial descriptor. -/
theorem whole_molecule_exact_spatial_analysis :
    (localizedHalomethaneInput.analyzeTetrahedralSpatial
        (fun _center => emptyContext)).map
        (fun assignment => (assignment.center.val.val, assignment.descriptor)) =
      [(0, RS.S)] := by
  unfold CertifiedLocalizedCIPInput.analyzeTetrahedralSpatial
  rw [canonical_tetrahedral_centers_are_exact]
  simp only [List.filterMap_cons, exact_spatial_pipeline_emits_S, List.filterMap_nil]
  rfl

/-- The replacement rule-major whole-molecule analyzer likewise emits exactly the carbon `S`. -/
theorem whole_molecule_rule_major_exact_spatial_analysis :
    (localizedHalomethaneInput.analyzeRuleMajorTetrahedralSpatial
        (fun _center => emptyContext)).map
        (fun assignment => (assignment.center.val.val, assignment.descriptor)) =
      [(0, RS.S)] := by
  unfold CertifiedLocalizedCIPInput.analyzeRuleMajorTetrahedralSpatial
  rw [canonical_tetrahedral_centers_are_exact]
  simp only [List.filterMap_cons, rule_major_exact_spatial_pipeline_emits_S,
    List.filterMap_nil]
  rfl

end TetraStereo.Examples.AuthoritativeLocalizedCIPAnalysis
