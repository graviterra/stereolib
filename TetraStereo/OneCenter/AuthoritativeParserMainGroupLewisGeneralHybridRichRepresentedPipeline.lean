import TetraStereo.OneCenter.AuthoritativeParserMainGroupLewisGeneralHybridEvidence
import TetraStereo.OneCenter.AuthoritativeMainGroupLewisGeneralHybridRichRepresentedPipeline
import TetraStereo.OneCenter.AuthoritativeSemanticOpenCumuleneExactReadiness
import TetraStereo.OneCenter.AuthoritativeSemanticParserRule3Through6Conformance
import TetraStereo.OneCenter.AuthoritativeSemanticCyclicCumuleneDescriptorPolicyClosure

set_option autoImplicit false

namespace TetraStereo.OneCenter
namespace RawMolecule

open AuthoritativeChemicalInput

/-!
# Parser-to-rich represented stereochemical pipeline

Raw-index validation and generalized-Lewis electronic certification now feed the represented
five-family result whose tetrahedral branch retains `R/S/r/s`.
-/

noncomputable def analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat) :
    List source.AromaticCanonicalHybridRichRepresentedResult :=
  source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
    (molecule.parserAtomElectronicStateRecords source converted annotations)
    ready.2 carrierFuel ruleFuel

/-- Total parser entry point for the case-preserving represented result. -/
noncomputable def analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel ruleFuel : Nat) :
    Option (List source.AromaticCanonicalHybridRichRepresentedResult) := by
  classical
  exact if ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations then
    some
      (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
        source converted annotations ready carrierFuel ruleFuel)
  else none

@[simp] theorem analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_eq_none_iff_refusal
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel ruleFuel : Nat) :
    molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
        source converted annotations carrierFuel ruleFuel = none ↔
      molecule.ParserMainGroupLewisGeneralHybridCertificationRefusal
        source converted annotations := by
  classical
  rw [← molecule.not_parserMainGroupLewisGeneralHybridCertificationReady_iff_refusal
    source converted annotations]
  simp [analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?]

theorem analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_eq_some_of_ready
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat) :
    molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
        source converted annotations carrierFuel ruleFuel =
      some
        (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
          source converted annotations ready carrierFuel ruleFuel) := by
  classical
  simp [analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?, ready]

/-- Every parser-produced rich result has its independent complete family judgment. -/
theorem analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_member_sound
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalHybridRichRepresentedResult)
    (present : result ∈
      molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
        source converted annotations ready carrierFuel ruleFuel) :
    source.DeclarativeAromaticCanonicalHybridRichRepresentedMember
      (molecule.parserAtomElectronicStateRecords source converted annotations)
      ready.2 carrierFuel ruleFuel result := by
  exact source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_member_sound
    (molecule.parserAtomElectronicStateRecords source converted annotations)
    ready.2 carrierFuel ruleFuel result present

/-- The successful parser result is duplicate-free. -/
theorem analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_nodup
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat) :
    (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
      source converted annotations ready carrierFuel ruleFuel).Nodup := by
  exact source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_nodup
    (molecule.parserAtomElectronicStateRecords source converted annotations)
    ready.2 carrierFuel ruleFuel

theorem analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_some_nodup
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel ruleFuel : Nat)
    (results : List source.AromaticCanonicalHybridRichRepresentedResult)
    (computed :
      molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
        source converted annotations carrierFuel ruleFuel = some results) :
    results.Nodup := by
  classical
  unfold analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
    at computed
  split at computed
  next ready =>
    simp only [Option.some.injEq] at computed
    subst results
    exact
      molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_nodup
        source converted annotations ready carrierFuel ruleFuel
  next notReady => contradiction

/-- Parser readiness for exact-once case-preserving represented analysis. -/
structure ParserMainGroupLewisGeneralHybridRichRepresentedPipelineReadyAtBound
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel : Nat) : Prop where
  parserElectronic : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
    source converted annotations
  represented : source.AromaticCanonicalHybridRichRepresentedPipelineReadyAtBound
    (molecule.parserAtomElectronicStateRecords source converted annotations) carrierFuel

/-- End-to-end parser theorem: exact success, emitted correctness, global `Nodup`, and literal
count one for every independently ready represented unit, including lowercase tetrahedral cases. -/
theorem analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence_complete_at_bound
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel : Nat)
    (ready : molecule.ParserMainGroupLewisGeneralHybridRichRepresentedPipelineReadyAtBound
      source converted annotations carrierFuel) :
    ∃ results,
      molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
          source converted annotations carrierFuel (2 * (carrierFuel + 1)) = some results ∧
        results =
          source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
            (molecule.parserAtomElectronicStateRecords source converted annotations)
            ready.represented.electronic carrierFuel (2 * (carrierFuel + 1)) ∧
        source.AromaticCanonicalHybridRichRepresentedPipelineCompleteAtBound
          (molecule.parserAtomElectronicStateRecords source converted annotations)
          carrierFuel ready.represented := by
  let results :=
    source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
      (molecule.parserAtomElectronicStateRecords source converted annotations)
      ready.represented.electronic carrierFuel (2 * (carrierFuel + 1))
  refine ⟨results, ?_, rfl,
    source.analyzeAromaticCanonicalHybridRichRepresented_complete_at_bound
      (molecule.parserAtomElectronicStateRecords source converted annotations)
      carrierFuel ready.represented⟩
  simpa [results] using
    molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_eq_some_of_ready
      source converted annotations ready.parserElectronic
      carrierFuel (2 * (carrierFuel + 1))

/-- Same-assignment parser judgment for an ordinary-double-bond member of the rich represented
pipeline.  The generalized-Lewis inventory judgment and final descriptor are tied to an original
raw `.double` record on the same unordered semantic endpoints. -/
def ParserMainGroupLewisGeneralHybridRichOrdinaryDoubleBondAssignmentJudgment
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier)
    (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment) : Prop :=
  let certified := source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
    (molecule.parserAtomElectronicStateRecords source converted annotations) ready.2
  let viewAt := source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel
  assignment.bond = bond ∧
    source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalSpatialJudgment
      carrierFuel certified.inventorySource bond
      (viewAt bond.left) (viewAt bond.right) assignment ∧
    ∃ rawBond ∈ molecule.bonds,
      rawBond.kind = .double ∧
        rawBond.connects bond.left.val bond.right.val = true

/-- Exact final parser-output boundary for one generalized-Lewis ordinary double bond. Readiness
is equivalent to a unique assignment occurring literally once in the rich five-family output and
carrying both its independent inventory/spatial descriptor judgment and original raw-bond
provenance. -/
theorem existsUnique_ordinaryDoubleBond_in_analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_parserBacked_iff_readiness
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat)
    (bond : source.AromaticCanonicalOrdinaryDoubleBondCarrier) :
    (∃! assignment,
        (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
          source converted annotations ready carrierFuel ruleFuel).count
            (.ordinaryDoubleBond assignment) = 1 ∧
          molecule.ParserMainGroupLewisGeneralHybridRichOrdinaryDoubleBondAssignmentJudgment
            source converted annotations ready carrierFuel ruleFuel bond assignment) ↔
      source.AromaticCanonicalOrdinaryDoubleBondElectronicInventoryCanonicalReadiness
        carrierFuel
        (source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
          (molecule.parserAtomElectronicStateRecords source converted annotations)
          ready.2).inventorySource
        bond
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel bond.left)
        (source.aromaticCanonicalConcreteDependencyViewAt
          carrierFuel ruleFuel bond.right) := by
  let supplied := molecule.parserAtomElectronicStateRecords source converted annotations
  let electronic := ready.2
  let certified := source.certifiedMainGroupLewisGeneralHybridAtomElectronicStatesOfReady
    supplied electronic
  let viewAt := source.aromaticCanonicalConcreteDependencyViewAt carrierFuel ruleFuel
  constructor
  · rintro ⟨assignment, property, _unique⟩
    exact ⟨assignment, property.2.2.1⟩
  · intro bondReady
    have baseUnique :
        ∃! assignment,
          assignment ∈ source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
              carrierFuel viewAt certified.inventorySource ∧
            assignment.bond = bond := by
      apply
        (source.existsUnique_mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_iff_readiness
          carrierFuel viewAt certified.inventorySource bond).mpr
      simpa [certified, supplied, electronic, viewAt] using bondReady
    obtain ⟨assignment, ⟨present, assignmentBond⟩, unique⟩ := baseUnique
    obtain ⟨rawBond, rawPresent, rawDouble, rawConnects⟩ :=
      rawDoubleBond_of_aromaticCanonicalOrdinaryDoubleBond
        molecule source converted bond.ordinary
    obtain ⟨observedBond, observedCanonical⟩ :=
      (source.mem_analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_iff_canonical
        carrierFuel viewAt certified.inventorySource assignment).mp present
    have observedAssignmentBond : assignment.bond = observedBond :=
      observedCanonical.1.sound.1
    have observedBondIdentity : observedBond = bond :=
      observedAssignmentBond.symm.trans assignmentBond
    subst observedBond
    rw [assignmentBond] at observedCanonical
    have familyCount :
        (source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory
          carrierFuel viewAt certified.inventorySource).count assignment = 1 := by
      rw [(source.analyzeAromaticCanonicalOrdinaryDoubleBondAutomaticSpatialWithElectronicInventory_nodup
        carrierFuel viewAt certified.inventorySource).count]
      simp [present]
    have finalCount :
        (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
          source converted annotations ready carrierFuel ruleFuel).count
            (.ordinaryDoubleBond assignment) = 1 := by
      change
        (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
          supplied electronic carrierFuel ruleFuel).count
            (.ordinaryDoubleBond assignment) = 1
      rw [source.count_ordinaryDoubleBond_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
      simpa [certified, viewAt] using familyCount
    refine ⟨assignment,
      ⟨finalCount, assignmentBond, observedCanonical,
        rawBond, rawPresent, rawDouble, rawConnects⟩, ?_⟩
    intro other otherProperty
    apply unique other
    refine ⟨?_, otherProperty.2.1⟩
    apply List.count_pos_iff.mp
    have finalPositive :
        0 < (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
          source converted annotations ready carrierFuel ruleFuel).count
            (.ordinaryDoubleBond other) := by
      rw [otherProperty.1]
      omega
    change
      0 < (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
        supplied electronic carrierFuel ruleFuel).count
          (.ordinaryDoubleBond other) at finalPositive
    rw [source.count_ordinaryDoubleBond_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
      at finalPositive
    simpa [certified, viewAt] using finalPositive

/-- Raw parser provenance for every adjacent pair of one semantic cumulene path. -/
def AromaticCanonicalPathHasRawDoubleBondChain
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (path : List source.AromaticCanonicalAtom) : Prop :=
  path.IsChain fun left right =>
    ∃ rawBond ∈ molecule.bonds,
      rawBond.kind = .double ∧ rawBond.connects left.val right.val = true

/-- Semantic ordinary-double path validity reflects pointwise to original raw order-two bond
records under checked parser conversion. -/
theorem aromaticCanonicalOrdinaryCumulenePath_hasRawDoubleBondChain
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (path : List source.AromaticCanonicalAtom)
    (valid : source.AromaticCanonicalOrdinaryCumulenePath path) :
    molecule.AromaticCanonicalPathHasRawDoubleBondChain source path := by
  exact valid.2.imp fun _left _right ordinary =>
    rawDoubleBond_of_aromaticCanonicalOrdinaryDoubleBond
      molecule source converted ordinary

/-- The production path normalizer chooses only the original orientation or its reversal. -/
theorem aromaticCanonicalNormalizeCumulenePath_eq_self_or_reverse
    {source : AuthoritativeChemicalInput}
    (path : List source.AromaticCanonicalAtom) :
    aromaticCanonicalNormalizeCumulenePath path = path ∨
      aromaticCanonicalNormalizeCumulenePath path = path.reverse := by
  unfold aromaticCanonicalNormalizeCumulenePath
  cases headObserved : path.head? with
  | none => simp
  | some first =>
      cases lastObserved : path.getLast? with
      | none => simp
      | some last =>
          by_cases ordered : first ≤ last <;>
            simp [ordered]

/-- Every canonical odd-open-cumulene unit perceived from a converted parser molecule is an
original raw double-bond chain, including when canonical orientation reverses the enumerated
semantic path. -/
theorem rawDoubleBondChain_of_mem_aromaticCanonicalOddOpenCumuleneUnits
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits) :
    molecule.AromaticCanonicalPathHasRawDoubleBondChain source unit := by
  obtain ⟨path, valid, normalized⟩ :=
    (source.mem_aromaticCanonicalOddOpenCumuleneUnits_iff unit).mp owner
  have pathChain :=
    molecule.aromaticCanonicalOrdinaryCumulenePath_hasRawDoubleBondChain
      source converted path valid.1.2.1
  rcases aromaticCanonicalNormalizeCumulenePath_eq_self_or_reverse path with
    normalizedSelf | normalizedReverse
  · have pathIdentity : path = unit := normalizedSelf.symm.trans normalized
    simpa [pathIdentity] using pathChain
  · have reverseIdentity : path.reverse = unit := normalizedReverse.symm.trans normalized
    rw [← reverseIdentity, AromaticCanonicalPathHasRawDoubleBondChain,
      List.isChain_reverse]
    unfold AromaticCanonicalPathHasRawDoubleBondChain at pathChain
    exact pathChain.imp fun left right witnessed => by
      obtain ⟨rawBond, rawPresent, rawDouble, rawConnects⟩ := witnessed
      refine ⟨rawBond, rawPresent, rawDouble, ?_⟩
      simpa [RawBond.connects, Bool.or_comm] using rawConnects

/-- Same-assignment parser meaning of one odd-open-cumulene member in the rich final result. -/
def ParserMainGroupLewisGeneralHybridRichOddOpenCumuleneAssignmentJudgment
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment) : Prop :=
  assignment.unit = unit ∧
    unit ∈ source.aromaticCanonicalOddOpenCumuleneUnits ∧
    source.AromaticCanonicalOddOpenCumuleneCanonicalSpatialJudgment
      carrierFuel ruleFuel unit assignment ∧
    molecule.AromaticCanonicalPathHasRawDoubleBondChain source unit

/-- Exact final parser-output boundary for one odd open cumulene. Canonical readiness is
equivalent to a unique count-one rich-parser member carrying the complete planar descriptor
judgment and original raw double-bond-chain provenance. -/
theorem existsUnique_oddOpenCumulene_in_analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_parserBacked_iff_readiness
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) :
    (∃! assignment,
        (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
          source converted annotations ready carrierFuel ruleFuel).count
            (.oddOpenCumulene assignment) = 1 ∧
          molecule.ParserMainGroupLewisGeneralHybridRichOddOpenCumuleneAssignmentJudgment
            source carrierFuel ruleFuel unit assignment) ↔
      source.AromaticCanonicalOddOpenCumuleneCanonicalReadiness
        carrierFuel ruleFuel unit := by
  let supplied := molecule.parserAtomElectronicStateRecords source converted annotations
  let electronic := ready.2
  constructor
  · rintro ⟨assignment, property, _unique⟩
    exact ⟨property.2.2.1, assignment, property.2.2.2.1⟩
  · rintro ⟨owner, assignment, canonical⟩
    have computed :
        source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
          carrierFuel ruleFuel unit = some assignment :=
      (source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_eq_some_iff_canonical
        carrierFuel ruleFuel unit assignment).mpr canonical
    have assignmentUnit : assignment.unit = unit :=
      source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_unit_eq
        carrierFuel ruleFuel unit assignment computed
    have familyPresent : assignment ∈
        source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
          carrierFuel ruleFuel :=
      (source.mem_analyzeAromaticCanonicalOddOpenCumuleneSpatial_iff
        carrierFuel ruleFuel assignment).mpr ⟨unit, owner, computed⟩
    have familyCount :
        (source.analyzeAromaticCanonicalOddOpenCumuleneSpatial
          carrierFuel ruleFuel).count assignment = 1 := by
      rw [(source.analyzeAromaticCanonicalOddOpenCumuleneSpatial_nodup
        carrierFuel ruleFuel).count]
      simp [familyPresent]
    have finalCount :
        (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
          source converted annotations ready carrierFuel ruleFuel).count
            (.oddOpenCumulene assignment) = 1 := by
      change
        (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
          supplied electronic carrierFuel ruleFuel).count
            (.oddOpenCumulene assignment) = 1
      rw [source.count_oddOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
      exact familyCount
    have rawChain :=
      molecule.rawDoubleBondChain_of_mem_aromaticCanonicalOddOpenCumuleneUnits
        source converted unit owner
    refine ⟨assignment,
      ⟨finalCount, assignmentUnit, owner, canonical, rawChain⟩, ?_⟩
    intro other otherProperty
    have otherComputed :
        source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?
          carrierFuel ruleFuel unit = some other :=
      (source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_eq_some_iff_canonical
        carrierFuel ruleFuel unit other).mpr otherProperty.2.2.2.1
    exact Option.some.inj (otherComputed.symm.trans computed)

/-- Every canonical even-open-cumulene unit perceived from a converted parser molecule is the
same original raw double-bond chain, up to the proved harmless orientation normalization. -/
theorem rawDoubleBondChain_of_mem_aromaticCanonicalEvenOpenCumuleneUnits
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (unit : List source.AromaticCanonicalAtom)
    (owner : unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits) :
    molecule.AromaticCanonicalPathHasRawDoubleBondChain source unit := by
  obtain ⟨path, valid, normalized⟩ :=
    (source.mem_aromaticCanonicalEvenOpenCumuleneUnits_iff unit).mp owner
  have pathChain :=
    molecule.aromaticCanonicalOrdinaryCumulenePath_hasRawDoubleBondChain
      source converted path valid.1.2.1
  rcases aromaticCanonicalNormalizeCumulenePath_eq_self_or_reverse path with
    normalizedSelf | normalizedReverse
  · have pathIdentity : path = unit := normalizedSelf.symm.trans normalized
    simpa [pathIdentity] using pathChain
  · have reverseIdentity : path.reverse = unit := normalizedReverse.symm.trans normalized
    rw [← reverseIdentity, AromaticCanonicalPathHasRawDoubleBondChain,
      List.isChain_reverse]
    unfold AromaticCanonicalPathHasRawDoubleBondChain at pathChain
    exact pathChain.imp fun left right witnessed => by
      obtain ⟨rawBond, rawPresent, rawDouble, rawConnects⟩ := witnessed
      refine ⟨rawBond, rawPresent, rawDouble, ?_⟩
      simpa [RawBond.connects, Bool.or_comm] using rawConnects

/-- Same-assignment parser meaning of one even-open-cumulene axial member in the rich result. -/
def ParserMainGroupLewisGeneralHybridRichEvenOpenCumuleneAssignmentJudgment
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom)
    (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment) : Prop :=
  assignment.unit = unit ∧
    unit ∈ source.aromaticCanonicalEvenOpenCumuleneUnits ∧
    source.AromaticCanonicalEvenOpenCumuleneCanonicalAxialJudgment
      carrierFuel ruleFuel unit assignment ∧
    molecule.AromaticCanonicalPathHasRawDoubleBondChain source unit

/-- Exact final parser-output boundary for one even open cumulene. Canonical axial readiness is
equivalent to a unique count-one rich-parser member carrying the rational axial descriptor
judgment and original raw double-bond-chain provenance. -/
theorem existsUnique_evenOpenCumulene_in_analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_parserBacked_iff_readiness
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat)
    (unit : List source.AromaticCanonicalAtom) :
    (∃! assignment,
        (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
          source converted annotations ready carrierFuel ruleFuel).count
            (.evenOpenCumulene assignment) = 1 ∧
          molecule.ParserMainGroupLewisGeneralHybridRichEvenOpenCumuleneAssignmentJudgment
            source carrierFuel ruleFuel unit assignment) ↔
      source.AromaticCanonicalEvenOpenCumuleneCanonicalReadiness
        carrierFuel ruleFuel unit := by
  let supplied := molecule.parserAtomElectronicStateRecords source converted annotations
  let electronic := ready.2
  constructor
  · rintro ⟨assignment, property, _unique⟩
    exact ⟨property.2.2.1, assignment, property.2.2.2.1⟩
  · rintro ⟨owner, assignment, canonical⟩
    have computed :
        source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
          carrierFuel ruleFuel unit = some assignment :=
      (source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_eq_some_iff_canonical
        carrierFuel ruleFuel unit assignment).mpr canonical
    have assignmentUnit : assignment.unit = unit :=
      source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_unit_eq
        carrierFuel ruleFuel unit assignment computed
    have familyPresent : assignment ∈
        source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
          carrierFuel ruleFuel :=
      (source.mem_analyzeAromaticCanonicalEvenOpenCumuleneAxial_iff
        carrierFuel ruleFuel assignment).mpr ⟨unit, owner, computed⟩
    have familyCount :
        (source.analyzeAromaticCanonicalEvenOpenCumuleneAxial
          carrierFuel ruleFuel).count assignment = 1 := by
      rw [(source.analyzeAromaticCanonicalEvenOpenCumuleneAxial_nodup
        carrierFuel ruleFuel).count]
      simp [familyPresent]
    have finalCount :
        (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
          source converted annotations ready carrierFuel ruleFuel).count
            (.evenOpenCumulene assignment) = 1 := by
      change
        (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
          supplied electronic carrierFuel ruleFuel).count
            (.evenOpenCumulene assignment) = 1
      rw [source.count_evenOpenCumulene_in_analyzeAromaticCanonicalHybridRichRepresentedOfReady]
      exact familyCount
    have rawChain :=
      molecule.rawDoubleBondChain_of_mem_aromaticCanonicalEvenOpenCumuleneUnits
        source converted unit owner
    refine ⟨assignment,
      ⟨finalCount, assignmentUnit, owner, canonical, rawChain⟩, ?_⟩
    intro other otherProperty
    have otherComputed :
        source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?
          carrierFuel ruleFuel unit = some other :=
      (source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_eq_some_iff_canonical
        carrierFuel ruleFuel unit other).mpr otherProperty.2.2.2.1
    exact Option.some.inj (otherComputed.symm.trans computed)

/-- Parser-backed meaning of a fully cyclic cumulene component boundary.  Every ordinary-double
edge internal to the complete declarative component is reflected by an original raw `.double`
record on the same unordered pair. -/
def ParserMainGroupLewisGeneralHybridRichFullyCyclicCumuleneComponentJudgment
    (molecule : RawMolecule) (source : AuthoritativeChemicalInput)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) : Prop :=
  source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component ∧
    ∀ left,
      left ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms component.representative →
      ∀ right,
        right ∈ source.aromaticCanonicalOrdinaryDoubleComponentAtoms component.representative →
        source.AromaticCanonicalOrdinaryDoubleBond left right →
          ∃ rawBond ∈ molecule.bonds,
            rawBond.kind = .double ∧ rawBond.connects left.val right.val = true

/-- Exact final parser boundary for a fully cyclic cumulene parent record.  Declarative P-31
component applicability is equivalent to count one in the rich parser result together with raw
provenance for every ordinary-double edge of that component. -/
theorem count_fullyCyclicCumuleneParent_in_analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_eq_one_and_parserBacked_iff_declarative
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    (carrierFuel ruleFuel : Nat)
    (component : source.AromaticCanonicalCyclicCumuleneComponent) :
    ((molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
        source converted annotations ready carrierFuel ruleFuel).count
          (.fullyCyclicCumuleneParent component) = 1 ∧
      molecule.ParserMainGroupLewisGeneralHybridRichFullyCyclicCumuleneComponentJudgment
        source component) ↔
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component := by
  let supplied := molecule.parserAtomElectronicStateRecords source converted annotations
  let electronic := ready.2
  constructor
  · exact fun property => property.2.1
  · intro derived
    have executable :
        source.AromaticCanonicalHybridRichRepresentedExecutableMember
          supplied electronic carrierFuel ruleFuel (.fullyCyclicCumuleneParent component) :=
      derived
    have present :
        (.fullyCyclicCumuleneParent component :
          source.AromaticCanonicalHybridRichRepresentedResult) ∈
        source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
          supplied electronic carrierFuel ruleFuel :=
      (source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
        supplied electronic carrierFuel ruleFuel
          (.fullyCyclicCumuleneParent component)).mpr executable
    have finalCount :
        (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
          source converted annotations ready carrierFuel ruleFuel).count
            (.fullyCyclicCumuleneParent component) = 1 := by
      change
        (source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
          supplied electronic carrierFuel ruleFuel).count
            (.fullyCyclicCumuleneParent component) = 1
      rw [(source.analyzeAromaticCanonicalHybridRichRepresentedOfReady_nodup
        supplied electronic carrierFuel ruleFuel).count]
      simp [present]
    refine ⟨finalCount, derived, ?_⟩
    intro left _leftMember right _rightMember ordinary
    exact rawDoubleBond_of_aromaticCanonicalOrdinaryDoubleBond
      molecule source converted ordinary

/-- Exhaustive constructor-indexed independent meaning of a result emitted by the certified rich
parser pipeline.  Tetrahedral results retain the raw four-slot frame and rich `R/S/r/s` semantics;
ordinary and open-cumulene results retain raw bond provenance and exact geometry judgments; the
fully cyclic boundary retains complete component provenance and the P-31 routing facts. -/
def CertifiedParserBackedMainGroupLewisGeneralHybridRichRepresentedMember
    (certified : CertifiedChemistryNormalizationResult)
    (source : AuthoritativeChemicalInput)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : certified.result.parsed.ParserMainGroupLewisGeneralHybridCertificationReady
      source
      (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
      annotations)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalHybridRichRepresentedResult) : Prop :=
  let molecule := certified.result.parsed
  match result with
  | .tetrahedral assignment =>
      source.CertifiedParserBackedConcreteRule3Through6RSPseudoAssignmentJudgment
        certified ingested carrierFuel ruleFuel assignment.center assignment
  | .ordinaryDoubleBond assignment =>
      molecule.ParserMainGroupLewisGeneralHybridRichOrdinaryDoubleBondAssignmentJudgment
        source
        (molecule.toAuthoritativeChemicalInput?_molecule source ingested)
        annotations ready carrierFuel ruleFuel assignment.bond assignment
  | .oddOpenCumulene assignment =>
      molecule.ParserMainGroupLewisGeneralHybridRichOddOpenCumuleneAssignmentJudgment
        source carrierFuel ruleFuel assignment.unit assignment
  | .evenOpenCumulene assignment =>
      molecule.ParserMainGroupLewisGeneralHybridRichEvenOpenCumuleneAssignmentJudgment
        source carrierFuel ruleFuel assignment.unit assignment
  | .fullyCyclicCumuleneParent component =>
      molecule.ParserMainGroupLewisGeneralHybridRichFullyCyclicCumuleneComponentJudgment
          source component ∧
        BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
        ¬BlueBookP93.Cyclic.OpenTerminalCumuleneSchemaApplies .fullyCyclicCumulene

/-- Every emitted member of the certified generalized-Lewis rich parser pipeline satisfies its
complete parser-backed independent judgment.  This is one exhaustive theorem over all five
represented constructors, rather than five disconnected postconditions. -/
theorem analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_certifiedNormalization_member_parserBacked
    (raw : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (normalized : normalizeRawMoleculeCertified? raw cycles = some certified)
    (source : AuthoritativeChemicalInput)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : certified.result.parsed.ParserMainGroupLewisGeneralHybridCertificationReady
      source
      (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
      annotations)
    (carrierFuel ruleFuel : Nat)
    (result : source.AromaticCanonicalHybridRichRepresentedResult)
    (present : result ∈
      certified.result.parsed.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
        source
        (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
        annotations ready carrierFuel ruleFuel) :
    CertifiedParserBackedMainGroupLewisGeneralHybridRichRepresentedMember
      certified source ingested annotations ready carrierFuel ruleFuel result := by
  let molecule := certified.result.parsed
  let converted := molecule.toAuthoritativeChemicalInput?_molecule source ingested
  let supplied := molecule.parserAtomElectronicStateRecords source converted annotations
  let electronic := ready.2
  have finalPresent : result ∈
      source.analyzeAromaticCanonicalHybridRichRepresentedOfReady
        supplied electronic carrierFuel ruleFuel := by
    simpa [molecule, converted, supplied, electronic,
      analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady]
      using present
  have finalExecutable :=
    (source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
      supplied electronic carrierFuel ruleFuel result).mp finalPresent
  cases result with
  | tetrahedral assignment =>
      have richExecutable :
          source.AromaticCanonicalConcreteRule3Through6RSPseudoExecutableJudgment
            carrierFuel ruleFuel assignment.center assignment.descriptor :=
        finalExecutable
      let baseAssignment : source.AromaticCanonicalScheduledRule3Through6Assignment :=
        { center := assignment.center, descriptor := assignment.descriptor.eraseCase }
      have baseExecutable :
          source.AromaticCanonicalConcreteRule3Through6ExecutableDescriptorJudgment
            carrierFuel ruleFuel baseAssignment.center baseAssignment.descriptor := by
        exact
          (source.aromaticCanonicalScheduledRule3Through6ExecutableDescriptorJudgment_iff_exists_rspseudo_erasing_to
            (source.aromaticCanonicalOccurrenceRule3Through5AuxiliarySemantics
              carrierFuel ruleFuel) ruleFuel assignment.center
              assignment.descriptor.eraseCase).mpr
            ⟨assignment.descriptor, richExecutable, rfl⟩
      have basePresent : baseAssignment ∈
          source.analyzeAromaticCanonicalConcreteRule3Through6 carrierFuel ruleFuel :=
        (source.mem_analyzeAromaticCanonicalConcreteRule3Through6_iff_executableJudgment
          carrierFuel ruleFuel baseAssignment).mpr baseExecutable
      have baseGeometry :=
        source.analyzeAromaticCanonicalConcreteRule3Through6_member_certifiedNormalization_geometry_sound
          raw cycles certified normalized ingested carrierFuel ruleFuel
          baseAssignment basePresent
      change
        source.CertifiedParserBackedConcreteRule3Through6RSPseudoAssignmentJudgment
          certified ingested carrierFuel ruleFuel assignment.center assignment
      refine ⟨rfl, richExecutable, ?_⟩
      exact ⟨rfl, baseGeometry⟩
  | ordinaryDoubleBond assignment =>
      obtain ⟨bond, canonical⟩ := finalExecutable
      have assignmentBond : assignment.bond = bond := canonical.1.sound.1
      subst bond
      obtain ⟨rawBond, rawPresent, rawDouble, rawConnects⟩ :=
        rawDoubleBond_of_aromaticCanonicalOrdinaryDoubleBond
          molecule source converted assignment.bond.ordinary
      change
        molecule.ParserMainGroupLewisGeneralHybridRichOrdinaryDoubleBondAssignmentJudgment
          source converted annotations ready carrierFuel ruleFuel assignment.bond assignment
      exact ⟨rfl, canonical, rawBond, rawPresent, rawDouble, rawConnects⟩
  | oddOpenCumulene assignment =>
      obtain ⟨unit, owner, computed⟩ := finalExecutable
      have assignmentUnit : assignment.unit = unit :=
        source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_unit_eq
          carrierFuel ruleFuel unit assignment computed
      have canonical :=
        (source.aromaticCanonicalOddOpenCumuleneSpatialAssignment?_eq_some_iff_canonical
          carrierFuel ruleFuel unit assignment).mp computed
      have rawChain :=
        molecule.rawDoubleBondChain_of_mem_aromaticCanonicalOddOpenCumuleneUnits
          source converted unit owner
      subst unit
      change
        molecule.ParserMainGroupLewisGeneralHybridRichOddOpenCumuleneAssignmentJudgment
          source carrierFuel ruleFuel assignment.unit assignment
      exact ⟨rfl, owner, canonical, rawChain⟩
  | evenOpenCumulene assignment =>
      obtain ⟨unit, owner, computed⟩ := finalExecutable
      have assignmentUnit : assignment.unit = unit :=
        source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_unit_eq
          carrierFuel ruleFuel unit assignment computed
      have canonical :=
        (source.aromaticCanonicalEvenOpenCumuleneAxialAssignment?_eq_some_iff_canonical
          carrierFuel ruleFuel unit assignment).mp computed
      have rawChain :=
        molecule.rawDoubleBondChain_of_mem_aromaticCanonicalEvenOpenCumuleneUnits
          source converted unit owner
      subst unit
      change
        molecule.ParserMainGroupLewisGeneralHybridRichEvenOpenCumuleneAssignmentJudgment
          source carrierFuel ruleFuel assignment.unit assignment
      exact ⟨rfl, owner, canonical, rawChain⟩
  | fullyCyclicCumuleneParent component =>
      have componentJudgment :
          molecule.ParserMainGroupLewisGeneralHybridRichFullyCyclicCumuleneComponentJudgment
            source component := by
        refine ⟨finalExecutable, ?_⟩
        intro left _leftMember right _rightMember ordinary
        exact rawDoubleBond_of_aromaticCanonicalOrdinaryDoubleBond
          molecule source converted ordinary
      change
        molecule.ParserMainGroupLewisGeneralHybridRichFullyCyclicCumuleneComponentJudgment
            source component ∧
          BlueBookP93.Cyclic.P31FullyCyclicCumuleneParentApplies .fullyCyclicCumulene ∧
          ¬BlueBookP93.Cyclic.OpenTerminalCumuleneSchemaApplies .fullyCyclicCumulene
      exact ⟨componentJudgment, finalExecutable.authority_topology.1,
        finalExecutable.authority_topology.2⟩

/-- The same exhaustive parser-backed conformance theorem holds at the actual optional total
entry point.  A successful result exposes the checked electronic-readiness witness used to build
that exact list, and every member of the returned list satisfies its constructor-indexed judgment
against the certified normalized raw molecule. -/
theorem analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?_some_member_certifiedNormalization_parserBacked
    (raw : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (normalized : normalizeRawMoleculeCertified? raw cycles = some certified)
    (source : AuthoritativeChemicalInput)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (carrierFuel ruleFuel : Nat)
    (results : List source.AromaticCanonicalHybridRichRepresentedResult)
    (computed :
      certified.result.parsed.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
          source
          (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
          annotations carrierFuel ruleFuel = some results)
    (result : source.AromaticCanonicalHybridRichRepresentedResult)
    (present : result ∈ results) :
    ∃ ready : certified.result.parsed.ParserMainGroupLewisGeneralHybridCertificationReady
        source
        (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
        annotations,
      results =
          certified.result.parsed.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
            source
            (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
            annotations ready carrierFuel ruleFuel ∧
        CertifiedParserBackedMainGroupLewisGeneralHybridRichRepresentedMember
          certified source ingested annotations ready carrierFuel ruleFuel result := by
  classical
  unfold analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidence?
    at computed
  split at computed
  next ready =>
    simp only [Option.some.injEq] at computed
    subst results
    refine ⟨ready, rfl, ?_⟩
    exact
      analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_certifiedNormalization_member_parserBacked
        raw cycles certified normalized source ingested annotations ready carrierFuel ruleFuel
        result present
  next notReady => contradiction

/-! ## Case-preserving parser closure for an independent fully cyclic descriptor policy -/

/-- Rich generalized-Lewis parser result after resolving the fully cyclic P-31 boundary through
an independent descriptor policy.  The descriptor-bearing families retain their exact assignment
types; only the former cyclic-parent constructor is split into an honest boundary or a policy
descriptor. -/
inductive ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult
    (source : AuthoritativeChemicalInput) (PolicyDescriptor : Type*) where
  | tetrahedral (assignment : source.AromaticCanonicalRule3Through6RSPseudoAssignment)
  | ordinaryDoubleBond
      (assignment : source.AromaticCanonicalOrdinaryDoubleBondSpatialAssignment)
  | oddOpenCumulene
      (assignment : source.AromaticCanonicalOddOpenCumuleneSpatialAssignment)
  | evenOpenCumulene
      (assignment : source.AromaticCanonicalEvenOpenCumuleneAxialAssignment)
  | fullyCyclicCumuleneBoundary
      (component : source.AromaticCanonicalCyclicCumuleneComponent)
  | fullyCyclicCumuleneDescriptor
      (assignment : source.AromaticCanonicalFullyCyclicCumulenePolicyAssignment
        PolicyDescriptor)
  deriving DecidableEq

/-- Resolve the one policy-sensitive constructor of the rich five-family result. -/
noncomputable def resolveParserMainGroupLewisGeneralHybridRichCyclicPolicy
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor) :
    source.AromaticCanonicalHybridRichRepresentedResult →
      ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor
  | .tetrahedral assignment => .tetrahedral assignment
  | .ordinaryDoubleBond assignment => .ordinaryDoubleBond assignment
  | .oddOpenCumulene assignment => .oddOpenCumulene assignment
  | .evenOpenCumulene assignment => .evenOpenCumulene assignment
  | .fullyCyclicCumuleneParent component =>
      match source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor? policy component with
      | none => .fullyCyclicCumuleneBoundary component
      | some descriptor => .fullyCyclicCumuleneDescriptor { component, descriptor }

/-- Forget policy resolution while preserving the exact original rich result. -/
def eraseParserMainGroupLewisGeneralHybridRichCyclicPolicy
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*} :
    ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor →
      source.AromaticCanonicalHybridRichRepresentedResult
  | .tetrahedral assignment => .tetrahedral assignment
  | .ordinaryDoubleBond assignment => .ordinaryDoubleBond assignment
  | .oddOpenCumulene assignment => .oddOpenCumulene assignment
  | .evenOpenCumulene assignment => .evenOpenCumulene assignment
  | .fullyCyclicCumuleneBoundary component => .fullyCyclicCumuleneParent component
  | .fullyCyclicCumuleneDescriptor assignment =>
      .fullyCyclicCumuleneParent assignment.component

@[simp] theorem eraseParserMainGroupLewisGeneralHybridRichCyclicPolicy_resolve
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (result : source.AromaticCanonicalHybridRichRepresentedResult) :
    eraseParserMainGroupLewisGeneralHybridRichCyclicPolicy source
        (resolveParserMainGroupLewisGeneralHybridRichCyclicPolicy source policy result) = result := by
  cases result with
  | tetrahedral assignment => rfl
  | ordinaryDoubleBond assignment => rfl
  | oddOpenCumulene assignment => rfl
  | evenOpenCumulene assignment => rfl
  | fullyCyclicCumuleneParent component =>
      cases selected : source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?
          policy component <;>
        simp [resolveParserMainGroupLewisGeneralHybridRichCyclicPolicy, selected,
          eraseParserMainGroupLewisGeneralHybridRichCyclicPolicy]

/-- Policy resolution cannot merge distinct physical results. -/
theorem resolveParserMainGroupLewisGeneralHybridRichCyclicPolicy_injective
    (source : AuthoritativeChemicalInput) {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor) :
    Function.Injective
      (resolveParserMainGroupLewisGeneralHybridRichCyclicPolicy source policy) := by
  intro left right equal
  have erased := congrArg
    (eraseParserMainGroupLewisGeneralHybridRichCyclicPolicy source) equal
  simpa using erased

/-- Checked rich parser result with every fully cyclic component resolved by the independent
policy. -/
noncomputable def analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat) :
    List (ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor) :=
  (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
    source converted annotations ready carrierFuel ruleFuel).map
      (resolveParserMainGroupLewisGeneralHybridRichCyclicPolicy source policy)

/-- Total optional entry for checked generalized-Lewis rich analysis plus cyclic-policy
resolution.  Policy resolution introduces no new parser refusal. -/
noncomputable def analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidence?
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat) :
    Option
      (List (ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor)) := by
  classical
  exact if ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations then
    some
      (molecule.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady
        source converted annotations ready policy carrierFuel ruleFuel)
  else none

@[simp] theorem analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidence?_eq_none_iff_refusal
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat) :
    molecule.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidence?
        source converted annotations policy carrierFuel ruleFuel = none ↔
      molecule.ParserMainGroupLewisGeneralHybridCertificationRefusal
        source converted annotations := by
  classical
  rw [← molecule.not_parserMainGroupLewisGeneralHybridCertificationReady_iff_refusal
    source converted annotations]
  simp [analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidence?]

theorem analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidence?_eq_some_of_ready
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat) :
    molecule.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidence?
        source converted annotations policy carrierFuel ruleFuel =
      some
        (molecule.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady
          source converted annotations ready policy carrierFuel ruleFuel) := by
  classical
  simp [analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidence?, ready]

/-- Injective policy resolution preserves duplicate freedom. -/
theorem analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady_nodup
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat) :
    (molecule.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady
      source converted annotations ready policy carrierFuel ruleFuel).Nodup := by
  exact
    (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_nodup
      source converted annotations ready carrierFuel ruleFuel).map
        (resolveParserMainGroupLewisGeneralHybridRichCyclicPolicy_injective source policy)

/-- Every successful total policy-resolved parser result remains duplicate-free. -/
theorem analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidence?_some_nodup
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat)
    (results :
      List (ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor))
    (computed :
      molecule.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidence?
        source converted annotations policy carrierFuel ruleFuel = some results) :
    results.Nodup := by
  classical
  unfold analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidence? at computed
  split at computed
  next ready =>
    simp only [Option.some.injEq] at computed
    subst results
    exact
      molecule.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady_nodup
        source converted annotations ready policy carrierFuel ruleFuel
  next notReady => contradiction

/-- Constructor-indexed independent meaning of one policy-resolved rich parser member.  Existing
descriptor branches retain the complete certified judgment proved above.  Both cyclic outcomes
retain the same raw component and P-31/open-terminal routing proof, then add respectively absence
or presence of the independently supplied policy relation. -/
def CertifiedParserBackedMainGroupLewisGeneralHybridRichCyclicPolicyMember
    (certified : CertifiedChemistryNormalizationResult)
    (source : AuthoritativeChemicalInput)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : certified.result.parsed.ParserMainGroupLewisGeneralHybridCertificationReady
      source
      (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
      annotations)
    {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat)
    (result :
      ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor) : Prop :=
  match result with
  | .tetrahedral assignment =>
      CertifiedParserBackedMainGroupLewisGeneralHybridRichRepresentedMember
        certified source ingested annotations ready carrierFuel ruleFuel (.tetrahedral assignment)
  | .ordinaryDoubleBond assignment =>
      CertifiedParserBackedMainGroupLewisGeneralHybridRichRepresentedMember
        certified source ingested annotations ready carrierFuel ruleFuel
          (.ordinaryDoubleBond assignment)
  | .oddOpenCumulene assignment =>
      CertifiedParserBackedMainGroupLewisGeneralHybridRichRepresentedMember
        certified source ingested annotations ready carrierFuel ruleFuel
          (.oddOpenCumulene assignment)
  | .evenOpenCumulene assignment =>
      CertifiedParserBackedMainGroupLewisGeneralHybridRichRepresentedMember
        certified source ingested annotations ready carrierFuel ruleFuel
          (.evenOpenCumulene assignment)
  | .fullyCyclicCumuleneBoundary component =>
      CertifiedParserBackedMainGroupLewisGeneralHybridRichRepresentedMember
          certified source ingested annotations ready carrierFuel ruleFuel
            (.fullyCyclicCumuleneParent component) ∧
        ¬∃ descriptor, policy component descriptor
  | .fullyCyclicCumuleneDescriptor assignment =>
      CertifiedParserBackedMainGroupLewisGeneralHybridRichRepresentedMember
          certified source ingested annotations ready carrierFuel ruleFuel
            (.fullyCyclicCumuleneParent assignment.component) ∧
        policy assignment.component assignment.descriptor

/-- Every member of the checked policy-resolved list has complete raw/parser provenance and its
independent family or cyclic-policy judgment. -/
theorem analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady_certifiedNormalization_member_parserBacked
    (raw : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (normalized : normalizeRawMoleculeCertified? raw cycles = some certified)
    (source : AuthoritativeChemicalInput)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : certified.result.parsed.ParserMainGroupLewisGeneralHybridCertificationReady
      source
      (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
      annotations)
    {PolicyDescriptor : Type*} [DecidableEq PolicyDescriptor]
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (functional :
      source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicyFunctional policy)
    (carrierFuel ruleFuel : Nat)
    (result :
      ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor)
    (present : result ∈
      certified.result.parsed.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady
        source
        (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
        annotations ready policy carrierFuel ruleFuel) :
    CertifiedParserBackedMainGroupLewisGeneralHybridRichCyclicPolicyMember
      certified source ingested annotations ready policy carrierFuel ruleFuel result := by
  unfold analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady at present
  obtain ⟨prior, priorPresent, resolved⟩ := List.mem_map.mp present
  have priorJudged :=
    analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady_certifiedNormalization_member_parserBacked
      raw cycles certified normalized source ingested annotations ready carrierFuel ruleFuel
      prior priorPresent
  cases prior with
  | tetrahedral assignment =>
      cases resolved
      exact priorJudged
  | ordinaryDoubleBond assignment =>
      cases resolved
      exact priorJudged
  | oddOpenCumulene assignment =>
      cases resolved
      exact priorJudged
  | evenOpenCumulene assignment =>
      cases resolved
      exact priorJudged
  | fullyCyclicCumuleneParent component =>
      cases selected : source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?
          policy component with
      | none =>
          have resolvedIdentity :
              (ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult.fullyCyclicCumuleneBoundary
                component :
                ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor) =
                result := by
            simpa [resolveParserMainGroupLewisGeneralHybridRichCyclicPolicy, selected] using
              resolved
          cases resolvedIdentity
          exact ⟨priorJudged,
            (source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?_eq_none_iff
              policy component).mp selected⟩
      | some descriptor =>
          have resolvedIdentity :
              (ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult.fullyCyclicCumuleneDescriptor
                { component, descriptor } :
                ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor) =
                result := by
            simpa [resolveParserMainGroupLewisGeneralHybridRichCyclicPolicy, selected] using
              resolved
          cases resolvedIdentity
          have applies :=
            (source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?_eq_some_iff
              policy functional component priorJudged.1.1 descriptor).mp selected
          exact ⟨priorJudged, applies⟩

/-- The actual optional total policy-resolved parser endpoint exposes the exact readiness witness
that built a successful list and certifies every returned member against normalization, raw input,
and the independent cyclic policy. -/
theorem analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidence?_some_member_certifiedNormalization_parserBacked
    (raw : RawMolecule) (cycles : List AromaticCycle)
    (certified : CertifiedChemistryNormalizationResult)
    (normalized : normalizeRawMoleculeCertified? raw cycles = some certified)
    (source : AuthoritativeChemicalInput)
    (ingested : certified.result.parsed.toAuthoritativeChemicalInput? = some source)
    (annotations : List ParserAtomElectronicStateAnnotation)
    {PolicyDescriptor : Type*} [DecidableEq PolicyDescriptor]
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (functional :
      source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicyFunctional policy)
    (carrierFuel ruleFuel : Nat)
    (results :
      List (ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor))
    (computed :
      certified.result.parsed.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidence?
          source
          (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
          annotations policy carrierFuel ruleFuel = some results)
    (result :
      ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor)
    (present : result ∈ results) :
    ∃ ready : certified.result.parsed.ParserMainGroupLewisGeneralHybridCertificationReady
        source
        (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
        annotations,
      results =
          certified.result.parsed.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady
            source
            (certified.result.parsed.toAuthoritativeChemicalInput?_molecule source ingested)
            annotations ready policy carrierFuel ruleFuel ∧
        CertifiedParserBackedMainGroupLewisGeneralHybridRichCyclicPolicyMember
          certified source ingested annotations ready policy carrierFuel ruleFuel result := by
  classical
  unfold analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidence? at computed
  split at computed
  next ready =>
    simp only [Option.some.injEq] at computed
    subst results
    refine ⟨ready, rfl, ?_⟩
    exact
      analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady_certifiedNormalization_member_parserBacked
        raw cycles certified normalized source ingested annotations ready policy functional
        carrierFuel ruleFuel result present
  next notReady => contradiction

/-- Exact independent executable meaning of every constructor in the policy-resolved rich parser
result.  The first four cases reuse the established generalized-Lewis executable judgment; the two
cyclic cases expose the declarative component and respectively policy absence or applicability. -/
def ParserMainGroupLewisGeneralHybridRichCyclicPolicyExecutableMember
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat)
    (result :
      ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor) : Prop :=
  match result with
  | .tetrahedral assignment =>
      source.AromaticCanonicalHybridRichRepresentedExecutableMember
        (molecule.parserAtomElectronicStateRecords source converted annotations)
        ready.2 carrierFuel ruleFuel (.tetrahedral assignment)
  | .ordinaryDoubleBond assignment =>
      source.AromaticCanonicalHybridRichRepresentedExecutableMember
        (molecule.parserAtomElectronicStateRecords source converted annotations)
        ready.2 carrierFuel ruleFuel (.ordinaryDoubleBond assignment)
  | .oddOpenCumulene assignment =>
      source.AromaticCanonicalHybridRichRepresentedExecutableMember
        (molecule.parserAtomElectronicStateRecords source converted annotations)
        ready.2 carrierFuel ruleFuel (.oddOpenCumulene assignment)
  | .evenOpenCumulene assignment =>
      source.AromaticCanonicalHybridRichRepresentedExecutableMember
        (molecule.parserAtomElectronicStateRecords source converted annotations)
        ready.2 carrierFuel ruleFuel (.evenOpenCumulene assignment)
  | .fullyCyclicCumuleneBoundary component =>
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent component ∧
        ¬∃ descriptor, policy component descriptor
  | .fullyCyclicCumuleneDescriptor assignment =>
      source.DeclarativeAromaticCanonicalCyclicCumuleneComponent assignment.component ∧
        policy assignment.component assignment.descriptor

/-- Flattened exact membership for all six policy-resolved constructors. -/
theorem mem_analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady_iff
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    {PolicyDescriptor : Type*} [DecidableEq PolicyDescriptor]
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (functional :
      source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicyFunctional policy)
    (carrierFuel ruleFuel : Nat)
    (result :
      ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor) :
    result ∈ molecule.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady
        source converted annotations ready policy carrierFuel ruleFuel ↔
      molecule.ParserMainGroupLewisGeneralHybridRichCyclicPolicyExecutableMember
        source converted annotations ready policy carrierFuel ruleFuel result := by
  classical
  let supplied := molecule.parserAtomElectronicStateRecords source converted annotations
  constructor
  · intro present
    unfold analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady at present
    obtain ⟨prior, priorPresent, resolved⟩ := List.mem_map.mp present
    have executable :=
      (source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
        supplied ready.2 carrierFuel ruleFuel prior).mp priorPresent
    cases prior with
    | tetrahedral assignment =>
        cases resolved
        exact executable
    | ordinaryDoubleBond assignment =>
        cases resolved
        exact executable
    | oddOpenCumulene assignment =>
        cases resolved
        exact executable
    | evenOpenCumulene assignment =>
        cases resolved
        exact executable
    | fullyCyclicCumuleneParent component =>
        cases selected : source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?
            policy component with
        | none =>
            have resolvedIdentity :
                (ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult.fullyCyclicCumuleneBoundary
                  component :
                  ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult
                    source PolicyDescriptor) = result := by
              simpa [resolveParserMainGroupLewisGeneralHybridRichCyclicPolicy, selected] using
                resolved
            cases resolvedIdentity
            exact ⟨executable,
              (source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?_eq_none_iff
                policy component).mp selected⟩
        | some descriptor =>
            have resolvedIdentity :
                (ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult.fullyCyclicCumuleneDescriptor
                  { component, descriptor } :
                  ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult
                    source PolicyDescriptor) = result := by
              simpa [resolveParserMainGroupLewisGeneralHybridRichCyclicPolicy, selected] using
                resolved
            cases resolvedIdentity
            exact ⟨executable,
              (source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?_eq_some_iff
                policy functional component executable descriptor).mp selected⟩
  · intro executable
    unfold analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady
    apply List.mem_map.mpr
    cases result with
    | tetrahedral assignment =>
        refine ⟨.tetrahedral assignment, ?_, rfl⟩
        exact
          (source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
            supplied ready.2 carrierFuel ruleFuel (.tetrahedral assignment)).mpr executable
    | ordinaryDoubleBond assignment =>
        refine ⟨.ordinaryDoubleBond assignment, ?_, rfl⟩
        exact
          (source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
            supplied ready.2 carrierFuel ruleFuel (.ordinaryDoubleBond assignment)).mpr executable
    | oddOpenCumulene assignment =>
        refine ⟨.oddOpenCumulene assignment, ?_, rfl⟩
        exact
          (source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
            supplied ready.2 carrierFuel ruleFuel (.oddOpenCumulene assignment)).mpr executable
    | evenOpenCumulene assignment =>
        refine ⟨.evenOpenCumulene assignment, ?_, rfl⟩
        exact
          (source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
            supplied ready.2 carrierFuel ruleFuel (.evenOpenCumulene assignment)).mpr executable
    | fullyCyclicCumuleneBoundary component =>
        refine ⟨.fullyCyclicCumuleneParent component, ?_, ?_⟩
        · exact
            (source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
              supplied ready.2 carrierFuel ruleFuel
                (.fullyCyclicCumuleneParent component)).mpr executable.1
        · have selectedNone :=
            (source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?_eq_none_iff
              policy component).mpr executable.2
          simp [resolveParserMainGroupLewisGeneralHybridRichCyclicPolicy, selectedNone]
    | fullyCyclicCumuleneDescriptor assignment =>
        refine ⟨.fullyCyclicCumuleneParent assignment.component, ?_, ?_⟩
        · exact
            (source.mem_analyzeAromaticCanonicalHybridRichRepresentedOfReady_iff
              supplied ready.2 carrierFuel ruleFuel
                (.fullyCyclicCumuleneParent assignment.component)).mpr executable.1
        · have selected :=
            (source.aromaticCanonicalFullyCyclicCumulenePolicyDescriptor?_eq_some_iff
              policy functional assignment.component executable.1 assignment.descriptor).mpr
                executable.2
          simp [resolveParserMainGroupLewisGeneralHybridRichCyclicPolicy, selected]

/-- Every eligible policy-resolved result occurs literally once, and no ineligible result does. -/
theorem count_analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady_eq_one_iff
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    {PolicyDescriptor : Type*} [DecidableEq PolicyDescriptor]
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (functional :
      source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicyFunctional policy)
    (carrierFuel ruleFuel : Nat)
    (result :
      ParserMainGroupLewisGeneralHybridRichCyclicPolicyResult source PolicyDescriptor) :
    (molecule.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady
      source converted annotations ready policy carrierFuel ruleFuel).count result = 1 ↔
      molecule.ParserMainGroupLewisGeneralHybridRichCyclicPolicyExecutableMember
        source converted annotations ready policy carrierFuel ruleFuel result := by
  rw [(molecule.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady_nodup
    source converted annotations ready policy carrierFuel ruleFuel).count]
  simpa using
    (molecule.mem_analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady_iff
      source converted annotations ready policy functional carrierFuel ruleFuel result)

/-- Policy resolution changes one constructor but neither adds nor removes a physical result. -/
theorem length_analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady_eq_prior
    (molecule : RawMolecule)
    (source : AuthoritativeChemicalInput)
    (converted : molecule.toSemanticMolecule? = some source.molecule)
    (annotations : List ParserAtomElectronicStateAnnotation)
    (ready : molecule.ParserMainGroupLewisGeneralHybridCertificationReady
      source converted annotations)
    {PolicyDescriptor : Type*}
    (policy : source.AromaticCanonicalFullyCyclicCumuleneDescriptorPolicy PolicyDescriptor)
    (carrierFuel ruleFuel : Nat) :
    (molecule.analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady
      source converted annotations ready policy carrierFuel ruleFuel).length =
      (molecule.analyzeRichRepresentedStereochemistryOfParserMainGroupLewisGeneralHybridEvidenceOfReady
        source converted annotations ready carrierFuel ruleFuel).length := by
  simp [analyzeRichCyclicPolicyOfParserMainGroupLewisGeneralHybridEvidenceOfReady]

end RawMolecule
end TetraStereo.OneCenter
