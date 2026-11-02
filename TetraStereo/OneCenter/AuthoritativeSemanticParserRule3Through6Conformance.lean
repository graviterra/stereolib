import TetraStereo.OneCenter.AuthoritativeSemanticTetrahedralElementApplicability
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeRule3Through6GeometrySoundness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeCanonicalReadinessCompleteness
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeRichTetrahedralWholeMoleculeAnalysis
import TetraStereo.OneCenter.AuthoritativeSemanticMancudeMoleculeRule3Through6RSPseudoConservativeExtension
import TetraStereo.OneCenter.AuthoritativeMainGroupLewisGeneralHybridRichRepresentedPipeline

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Parser-backed semantic Rules 1a--6 descriptor conformance

This module composes the exact parser-to-semantic center/frame equivalence with the final
source-canonical Rules-1a--6 geometry theorem.  It closes a representation seam: a descriptor
emitted by the semantic analyzer is traced back to the same raw atom index and the independently
stated production perception frame, while the written ligand order is related to the semantic
canonical order by an explicit permutation.
-/

/-- Resolving one raw bond eliminates the `unspecified` constructor in every branch of the
normalizer, independently of endpoint validity. -/
theorem RawMolecule.normalizeUnspecifiedBond_kind_ne_unspecified
    (molecule : RawMolecule) (bond : RawBond) :
    (molecule.normalizeUnspecifiedBond bond).kind ≠ .unspecified := by
  rcases bond with ⟨source, target, kind⟩
  cases kind with
  | unspecified =>
      simp only [RawMolecule.normalizeUnspecifiedBond]
      cases sourceObserved : molecule.atomAt? source with
      | none => simp
      | some left =>
          cases targetObserved : molecule.atomAt? target with
          | none => simp
          | some right =>
              simp [RawMolecule.defaultBondKind]
              split <;> simp
  | single | double | triple | aromatic | up | down =>
      simp [RawMolecule.normalizeUnspecifiedBond]

/-- Every bond in the normalized raw molecule has a resolved kind. -/
theorem RawMolecule.normalizeUnspecifiedBonds_resolved (molecule : RawMolecule) :
    ∀ bond, bond ∈ molecule.normalizeUnspecifiedBonds.bonds →
      bond.kind ≠ .unspecified := by
  intro bond membership
  rw [RawMolecule.normalizeUnspecifiedBonds] at membership
  obtain ⟨original, _originalMembership, rfl⟩ := List.mem_map.mp membership
  exact molecule.normalizeUnspecifiedBond_kind_ne_unspecified original

/-- A successful structural/valence/mass certification retains exactly the result it certified;
the proof payload cannot substitute a different normalized molecule. -/
theorem ChemistryNormalizationResult.certify?_result_eq
    (result : ChemistryNormalizationResult)
    (certified : CertifiedChemistryNormalizationResult)
    (accepted : result.certify? = some certified) :
    certified.result = result := by
  have introduction := ChemistryNormalizationResult.certify?_introduction_valid
    result certified accepted
  unfold ChemistryNormalizationResult.certify? at accepted
  rw [if_pos introduction] at accepted
  split at accepted <;> simp_all
  rcases accepted with ⟨_writtenExact, _valence, _masses, equality⟩
  subst certified
  rfl

/-- A successful call to the production certified normalizer contains exactly
`normalizeRawMolecule molecule cycles`. -/
theorem normalizeRawMoleculeCertified?_result_eq
    (molecule : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (accepted : normalizeRawMoleculeCertified? molecule cycles = some certified) :
    certified.result = normalizeRawMolecule molecule cycles := by
  apply ChemistryNormalizationResult.certify?_result_eq
  simpa [normalizeRawMoleculeCertified?] using accepted

namespace AuthoritativeChemicalInput

/-- Every final concrete semantic assignment on a successfully converted parser molecule has a
raw production center with the full independent ordinary-tetrahedral frame, exact written-slot
lookup, an explicit `S₄` written-to-canonical permutation, and the complete source-coordinate
Rules-1a--6 geometric descriptor judgment. -/
theorem analyzeAromaticCanonicalConcreteRule3Through6_member_parser_geometry_sound
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (result : ChemistryNormalizationResult) (parsed : result.parsed = molecule)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6Assignment)
    (present : assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6
      carrierFuel ruleFuel) :
    ∃ (rawCenter : Fin molecule.atomCount)
      (four : (molecule.writtenNeighbors rawCenter.val).length = 4)
      (permutation : Equiv.Perm (Fin 4)),
      BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame
          result molecule rawCenter.val ∧
        molecule.convertedAtomIndex source converted rawCenter = assignment.center.val ∧
        (∀ position,
          listGet? (molecule.writtenNeighbors rawCenter.val) position.val =
            some (molecule.convertedWrittenTetrahedralLigandAtom
              source converted writtenExact rawCenter four position).val) ∧
        (∀ position,
          molecule.convertedWrittenTetrahedralLigandAtom
              source converted writtenExact rawCenter four position =
            source.aromaticCanonicalLigandAtom assignment.center
              (permutation position)) ∧
        source.AromaticCanonicalScheduledRule3Through6GeometricDescriptorJudgment
          (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
            carrierFuel ruleFuel) ruleFuel assignment.center assignment.descriptor := by
  let rawCenter : Fin molecule.atomCount :=
    Fin.cast (molecule.toSemanticMolecule?_atomCount source.molecule converted)
      assignment.center.val
  have centerReturned :
      molecule.convertedAtomIndex source converted rawCenter = assignment.center.val := by
    apply Fin.ext
    rfl
  have centerMember : molecule.convertedAtomIndex source converted rawCenter ∈
      source.aromaticCanonicalTetrahedralCenterSet := by
    rw [centerReturned]
    exact assignment.center.2
  have ordinaryFrame : molecule.OrdinaryConnectivityOnlyTetrahedralFrameAt rawCenter :=
    (molecule.ordinaryConnectivityOnlyTetrahedralFrameAt_iff_convertedCenter_mem
      source converted writtenExact resolved rawCenter).mpr centerMember
  have blueBookFrame : BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame
      result molecule rawCenter.val :=
    (molecule.ordinaryConnectivityOnlyTetrahedralFrameAt_iff_blueBookFrame
      result parsed rawCenter).mp ordinaryFrame
  rcases ordinaryFrame.1 with ⟨_spec, _atomAt, _elementEligible, four⟩
  obtain ⟨permutation, permutationEq⟩ :=
    molecule.exists_convertedWrittenToCanonicalPermutation
      source converted writtenExact resolved rawCenter four assignment.center centerReturned
  have slotLookup : ∀ position,
      listGet? (molecule.writtenNeighbors rawCenter.val) position.val =
        some (molecule.convertedWrittenTetrahedralLigandAtom
          source converted writtenExact rawCenter four position).val := by
    intro position
    have lookup := listGet?_eq_some_get
      (molecule.writtenNeighbors rawCenter.val) (Fin.cast four.symm position)
    simpa using lookup
  have geometry :=
    source.analyzeAromaticCanonicalConcreteRule3Through6_member_geometry_sound
      carrierFuel ruleFuel assignment present
  exact ⟨rawCenter, four, permutation, blueBookFrame, centerReturned,
    slotLookup, permutationEq, geometry⟩

/-- Public-ingestion form of
`analyzeAromaticCanonicalConcreteRule3Through6_member_parser_geometry_sound`: no separate
parser-to-semantic identity is assumed.  A successful call to the actual public converter
supplies that identity definitionally, so every emitted assignment is traced from the ingested
raw molecule all the way to the exact Rules-1a--6 geometric descriptor judgment. -/
theorem analyzeAromaticCanonicalConcreteRule3Through6_member_authoritativeParser_geometry_sound
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (ingested : molecule.toAuthoritativeChemicalInput? = some source)
    (writtenExact : molecule.WrittenNeighborExact)
    (resolved : ∀ bond, bond ∈ molecule.bonds → bond.kind ≠ .unspecified)
    (result : ChemistryNormalizationResult) (parsed : result.parsed = molecule)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6Assignment)
    (present : assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6
      carrierFuel ruleFuel) :
    ∃ (rawCenter : Fin molecule.atomCount)
      (four : (molecule.writtenNeighbors rawCenter.val).length = 4)
      (permutation : Equiv.Perm (Fin 4)),
      BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame
          result molecule rawCenter.val ∧
        molecule.convertedAtomIndex source
            (molecule.toAuthoritativeChemicalInput?_molecule source ingested) rawCenter =
          assignment.center.val ∧
        (∀ position,
          listGet? (molecule.writtenNeighbors rawCenter.val) position.val =
            some (molecule.convertedWrittenTetrahedralLigandAtom source
              (molecule.toAuthoritativeChemicalInput?_molecule source ingested)
              writtenExact rawCenter four position).val) ∧
        (∀ position,
          molecule.convertedWrittenTetrahedralLigandAtom source
              (molecule.toAuthoritativeChemicalInput?_molecule source ingested)
              writtenExact rawCenter four position =
            source.aromaticCanonicalLigandAtom assignment.center
              (permutation position)) ∧
        source.diagram? = some molecule.toDiagramConfiguration ∧
        source.AromaticCanonicalScheduledRule3Through6GeometricDescriptorJudgment
          (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
            carrierFuel ruleFuel) ruleFuel assignment.center assignment.descriptor := by
  let converted := molecule.toAuthoritativeChemicalInput?_molecule source ingested
  obtain ⟨rawCenter, four, permutation, frame, center, slots, order, geometry⟩ :=
    analyzeAromaticCanonicalConcreteRule3Through6_member_parser_geometry_sound
      molecule source converted writtenExact resolved result parsed carrierFuel ruleFuel
      assignment present
  exact ⟨rawCenter, four, permutation, frame, center, slots, order,
    molecule.toAuthoritativeChemicalInput?_diagram source ingested, geometry⟩

/-- Certified-normalization form of the complete parser-backed descriptor theorem.  The actual
normalization success discharges both written-neighbour exactness and bond-kind resolution; the
only ingestion premise is the successful public construction of the semantic source itself. -/
theorem analyzeAromaticCanonicalConcreteRule3Through6_member_certifiedNormalization_geometry_sound
    (raw : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (normalized : normalizeRawMoleculeCertified? raw cycles = some certified)
    (source : AuthoritativeChemicalInput)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (carrierFuel ruleFuel : Nat)
    (assignment : source.AromaticCanonicalScheduledRule3Through6Assignment)
    (present : assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6
      carrierFuel ruleFuel) :
    ∃ (rawCenter : Fin certified.result.parsed.atomCount)
      (four : (certified.result.parsed.writtenNeighbors rawCenter.val).length = 4)
      (permutation : Equiv.Perm (Fin 4)),
      BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame
          certified.result certified.result.parsed rawCenter.val ∧
        certified.result.parsed.convertedAtomIndex source
            (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
            rawCenter = assignment.center.val ∧
        (∀ position,
          listGet? (certified.result.parsed.writtenNeighbors rawCenter.val) position.val =
            some (certified.result.parsed.convertedWrittenTetrahedralLigandAtom source
              (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
              certified.writtenNeighborExact rawCenter four position).val) ∧
        (∀ position,
          certified.result.parsed.convertedWrittenTetrahedralLigandAtom source
              (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
              certified.writtenNeighborExact rawCenter four position =
            source.aromaticCanonicalLigandAtom assignment.center
              (permutation position)) ∧
        source.diagram? = some certified.result.parsed.toDiagramConfiguration ∧
        source.AromaticCanonicalScheduledRule3Through6GeometricDescriptorJudgment
          (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
            carrierFuel ruleFuel) ruleFuel assignment.center assignment.descriptor := by
  have resultEq : certified.result = normalizeRawMolecule raw cycles :=
    normalizeRawMoleculeCertified?_result_eq raw cycles certified normalized
  have parsedEq : certified.result.parsed = raw.normalizeUnspecifiedBonds := by
    rw [resultEq]
    rfl
  have resolved : ∀ bond, bond ∈ certified.result.parsed.bonds →
      bond.kind ≠ .unspecified := by
    intro bond membership
    have normalizedMembership : bond ∈ raw.normalizeUnspecifiedBonds.bonds := by
      rw [← parsedEq]
      exact membership
    exact raw.normalizeUnspecifiedBonds_resolved bond normalizedMembership
  exact analyzeAromaticCanonicalConcreteRule3Through6_member_authoritativeParser_geometry_sound
    certified.result.parsed source ingested certified.writtenNeighborExact resolved
    certified.result rfl carrierFuel ruleFuel assignment present

/-- Independent parser-backed judgment carried by one concrete Rules-1a--6 assignment at a
specified semantic center.  In addition to center identity, it records the raw production center,
the exact four written ligand slots, their explicit permutation into canonical priority order,
diagram preservation through ingestion, and the complete geometric descriptor judgment. -/
def CertifiedParserBackedConcreteRule3Through6AssignmentJudgment
    (source : AuthoritativeChemicalInput)
    (certified : CertifiedChemistryNormalizationResult)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (assignment : source.AromaticCanonicalScheduledRule3Through6Assignment) : Prop :=
  assignment.center = center ∧
    ∃ (rawCenter : Fin certified.result.parsed.atomCount)
      (four : (certified.result.parsed.writtenNeighbors rawCenter.val).length = 4)
      (permutation : Equiv.Perm (Fin 4)),
      BlueBookP92.Perception.ConnectivityOnlyTetrahedralFrame
          certified.result certified.result.parsed rawCenter.val ∧
        certified.result.parsed.convertedAtomIndex source
            (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
            rawCenter = assignment.center.val ∧
        (∀ position,
          listGet? (certified.result.parsed.writtenNeighbors rawCenter.val) position.val =
            some (certified.result.parsed.convertedWrittenTetrahedralLigandAtom source
              (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
              certified.writtenNeighborExact rawCenter four position).val) ∧
        (∀ position,
          certified.result.parsed.convertedWrittenTetrahedralLigandAtom source
              (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
              certified.writtenNeighborExact rawCenter four position =
            source.aromaticCanonicalLigandAtom assignment.center
              (permutation position)) ∧
        source.diagram? = some certified.result.parsed.toDiagramConfiguration ∧
        source.AromaticCanonicalScheduledRule3Through6GeometricDescriptorJudgment
          (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
            carrierFuel ruleFuel) ruleFuel assignment.center assignment.descriptor

/-- Canonical chemical readiness of a center yields exactly one emitted concrete assignment, and
that unique assignment is simultaneously certified against the raw parser frame and the
independent complete Rules-1a--6 geometric descriptor relation. -/
theorem existsUnique_mem_analyzeAromaticCanonicalConcreteRule3Through6_certifiedParserBacked_of_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput)
    (raw : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (normalized : normalizeRawMoleculeCertified? raw cycles = some certified)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
      carrierFuel ruleFuel center) :
    ∃! assignment,
      assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6
          carrierFuel ruleFuel ∧
        source.CertifiedParserBackedConcreteRule3Through6AssignmentJudgment
          certified ingested carrierFuel ruleFuel center assignment := by
  obtain ⟨assignment, ⟨present, centerIdentity⟩, unique⟩ :=
    (source.existsUnique_mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_canonicalChemicalReadiness
      carrierFuel ruleFuel center).mpr ready
  have parserBacked :=
    source.analyzeAromaticCanonicalConcreteRule3Through6_member_certifiedNormalization_geometry_sound
      raw cycles certified normalized ingested carrierFuel ruleFuel assignment present
  refine ⟨assignment, ⟨present, centerIdentity, parserBacked⟩, ?_⟩
  intro other otherProperty
  exact unique other ⟨otherProperty.1, otherProperty.2.1⟩

/-- Canonical readiness also produces exactly one parser-certified tetrahedral assignment after
injection into the actual five-family source result.  The count-one conclusion proves that the
ordinary-double-bond, odd/even open-cumulene, and fully cyclic branches neither remove nor collide
with the independently justified tetrahedral record. -/
theorem existsUnique_embeddedTetrahedral_certifiedParserBacked_of_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput)
    (raw : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (normalized : normalizeRawMoleculeCertified? raw cycles = some certified)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
      carrierFuel ruleFuel center) :
    ∃! assignment,
      source.CertifiedParserBackedConcreteRule3Through6AssignmentJudgment
          certified ingested carrierFuel ruleFuel center assignment ∧
        (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
          carrierFuel ruleFuel).count
            (source.embedTetrahedralInConcreteStereochemicalResult assignment) = 1 := by
  obtain ⟨assignment, ⟨present, parserBacked⟩, unique⟩ :=
    source.existsUnique_mem_analyzeAromaticCanonicalConcreteRule3Through6_certifiedParserBacked_of_canonicalChemicalReadiness
      raw cycles certified normalized ingested carrierFuel ruleFuel center ready
  have familyCount :
      (source.analyzeAromaticCanonicalConcreteRule3Through6
        carrierFuel ruleFuel).count assignment = 1 := by
    rw [(source.analyzeAromaticCanonicalConcreteRule3Through6_nodup
      carrierFuel ruleFuel).count]
    simp [present]
  have finalCount :
      (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
        carrierFuel ruleFuel).count
          (source.embedTetrahedralInConcreteStereochemicalResult assignment) = 1 := by
    rw [source.count_embedTetrahedralInConcreteStereochemicalResult]
    exact familyCount
  refine ⟨assignment, ⟨parserBacked, finalCount⟩, ?_⟩
  intro other otherProperty
  apply unique other
  refine ⟨?_, otherProperty.1⟩
  apply List.count_pos_iff.mp
  have finalPositive :
      0 < (source.analyzeAromaticCanonicalConcreteStereochemistryWithCyclicCumulenes
        carrierFuel ruleFuel).count
          (source.embedTetrahedralInConcreteStereochemicalResult other) := by
    rw [otherProperty.2]
    omega
  rwa [source.count_embedTetrahedralInConcreteStereochemicalResult] at finalPositive

/-- Complete parser-backed meaning of one rich `R/S/r/s` tetrahedral assignment.  The rich
executable judgment retains the exact pseudoasymmetric branch and comparison count, while its
case-erased assignment carries the independently certified raw frame and geometric handedness. -/
def CertifiedParserBackedConcreteRule3Through6RSPseudoAssignmentJudgment
    (source : AuthoritativeChemicalInput)
    (certified : CertifiedChemistryNormalizationResult)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (assignment : source.AromaticCanonicalRule3Through6RSPseudoAssignment) : Prop :=
  assignment.center = center ∧
    source.AromaticCanonicalConcreteRule3Through6RSPseudoExecutableJudgment
      carrierFuel ruleFuel assignment.center assignment.descriptor ∧
    source.CertifiedParserBackedConcreteRule3Through6AssignmentJudgment
      certified ingested carrierFuel ruleFuel center
        { center := assignment.center, descriptor := assignment.descriptor.eraseCase }

/-- Every canonically ready parser-backed center emits exactly one rich tetrahedral assignment.
Its `R/S/r/s` case is justified by the independent rich Rules-1a--6 branch relation, and erasing
only that case distinction yields the same raw-frame and determinant-certified handedness as the
base `R/S` pipeline. -/
theorem existsUnique_mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_certifiedParserBacked_of_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput)
    (raw : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (normalized : normalizeRawMoleculeCertified? raw cycles = some certified)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
      carrierFuel ruleFuel center) :
    ∃! assignment,
      assignment ∈ source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo
          carrierFuel ruleFuel ∧
        source.CertifiedParserBackedConcreteRule3Through6RSPseudoAssignmentJudgment
          certified ingested carrierFuel ruleFuel center assignment := by
  have baseReady : source.AromaticCanonicalConcreteRule3Through6Ready
      carrierFuel ruleFuel center :=
    (source.aromaticCanonicalConcreteRule3Through6Ready_iff_canonicalChemicalReadiness
      carrierFuel ruleFuel center).mpr ready
  have richReady : source.AromaticCanonicalConcreteRule3Through6RSPseudoReady
      carrierFuel ruleFuel center :=
    (source.aromaticCanonicalScheduledRule3Through6Ready_iff_rspseudoReady
      (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
        carrierFuel ruleFuel) ruleFuel center).mp baseReady
  obtain ⟨assignment, ⟨present, centerIdentity⟩, unique⟩ :=
    (source.existsUnique_mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff_ready
      carrierFuel ruleFuel center).mpr richReady
  have richExecutable :
      source.AromaticCanonicalConcreteRule3Through6RSPseudoExecutableJudgment
        carrierFuel ruleFuel assignment.center assignment.descriptor :=
    (source.mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_iff
      carrierFuel ruleFuel assignment).mp present
  let baseAssignment : source.AromaticCanonicalScheduledRule3Through6Assignment :=
    { center := assignment.center, descriptor := assignment.descriptor.eraseCase }
  have baseExecutable :
      source.AromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment
        carrierFuel ruleFuel baseAssignment.center baseAssignment.descriptor := by
    exact
      (source.aromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment_iff_exists_rspseudo_erasing_to
        (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
          carrierFuel ruleFuel) ruleFuel assignment.center assignment.descriptor.eraseCase).mpr
        ⟨assignment.descriptor, richExecutable, rfl⟩
  have basePresent : baseAssignment ∈
      source.analyzeAromaticCanonicalConcreteRule3Through6 carrierFuel ruleFuel :=
    (source.mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_executableJudgment
      carrierFuel ruleFuel baseAssignment).mpr baseExecutable
  have baseGeometry :=
    source.analyzeAromaticCanonicalConcreteRule3Through6_member_certifiedNormalization_geometry_sound
      raw cycles certified normalized ingested carrierFuel ruleFuel baseAssignment basePresent
  have baseParserBacked :
      source.CertifiedParserBackedConcreteRule3Through6AssignmentJudgment
        certified ingested carrierFuel ruleFuel center baseAssignment := by
    refine ⟨?_, baseGeometry⟩
    simpa [baseAssignment] using centerIdentity
  refine ⟨assignment,
    ⟨present, centerIdentity, richExecutable, baseParserBacked⟩, ?_⟩
  intro other otherProperty
  exact unique other ⟨otherProperty.1, otherProperty.2.1⟩

/-- The unique parser-certified `R/S/r/s` assignment survives with literal count one in the actual
electronic-inventory-aware rich five-family output.  Constructor disjointness therefore preserves
both its pseudoasymmetric branch proof and its raw-frame/determinant certificate. -/
theorem existsUnique_tetrahedral_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady_certifiedParserBacked_of_canonicalChemicalReadiness
    (source : AuthoritativeChemicalInput)
    (raw : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (normalized : normalizeRawMoleculeCertified? raw cycles = some certified)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (supplied : List source.AromaticCanonicalAtomElectronicStateRecord)
    (electronic : source.MainGroupLewisGeneralHybridCertificationReady supplied)
    (carrierFuel ruleFuel : Nat)
    (center : source.AromaticCanonicalTetrahedralCenter)
    (ready : source.AromaticCanonicalConcreteRule3Through6CanonicalChemicalReadiness
      carrierFuel ruleFuel center) :
    ∃! assignment,
      source.CertifiedParserBackedConcreteRule3Through6RSPseudoAssignmentJudgment
          certified ingested carrierFuel ruleFuel center assignment ∧
        (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
          supplied electronic carrierFuel ruleFuel).count (.tetrahedral assignment) = 1 := by
  obtain ⟨assignment, ⟨present, parserBacked⟩, unique⟩ :=
    source.existsUnique_mem_analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_certifiedParserBacked_of_canonicalChemicalReadiness
      raw cycles certified normalized ingested carrierFuel ruleFuel center ready
  have familyCount :
      (source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo
        carrierFuel ruleFuel).count assignment = 1 := by
    rw [(source.analyzeAromaticCanonicalConcreteRule3Through6RSPseudo_nodup
      carrierFuel ruleFuel).count]
    simp [present]
  have finalCount :
      (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
        supplied electronic carrierFuel ruleFuel).count (.tetrahedral assignment) = 1 := by
    rw [source.count_tetrahedral_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
    exact familyCount
  refine ⟨assignment, ⟨parserBacked, finalCount⟩, ?_⟩
  intro other otherProperty
  apply unique other
  refine ⟨?_, otherProperty.1⟩
  apply List.count_pos_iff.mp
  have finalPositive :
      0 < (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
        supplied electronic carrierFuel ruleFuel).count (.tetrahedral other) := by
    rw [otherProperty.2]
    omega
  rwa [source.count_tetrahedral_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
    at finalPositive

end AuthoritativeChemicalInput
end TetraStereo.OneCenter
