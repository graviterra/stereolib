import TetraStereo.OneCenter.IUPACP93CanonicalSourceClaims

set_option autoImplicit false

/-!
# Provenance-bearing canonical P-93.4 acyclic examples

This module transcribes one distinct printed Blue Book example for each of the eleven P-93.4
acyclic clauses.  Every source is the complete heavy-atom constitutional graph of the named
compound.  The two cumulene entries additionally pass through the independent molecule-wide
source-only maximal-terminal and parity carrier; an arbitrary connected path or parity-mismatched
subchain is not accepted as an axis.  Computed analyzer results bridge into this carrier in the
separate analyzer module.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Acyclic
open IUPACNormativeProvision

namespace P93CanonicalProgramAcyclic

def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
def nitrogen : PeriodicElement := ⟨7, by decide, by decide⟩
def oxygen : PeriodicElement := ⟨8, by decide, by decide⟩
def chlorine : PeriodicElement := ⟨17, by decide, by decide⟩
def bromine : PeriodicElement := ⟨35, by decide, by decide⟩
def iodine : PeriodicElement := ⟨53, by decide, by decide⟩

def carbonAtom : SemanticAtom where element := carbon
def nitrogenAtom : SemanticAtom where element := nitrogen
def oxygenAtom : SemanticAtom where element := oxygen
def chlorineAtom : SemanticAtom where element := chlorine
def bromineAtom : SemanticAtom where element := bromine
def iodineAtom : SemanticAtom where element := iodine

def bond (left right : Nat) (order : Nat := 1) : SemanticInteraction where
  participants := [left, right]
  kind := .covalent order

def aromaticBond (left right : Nat) : SemanticInteraction where
  participants := [left, right]
  kind := .aromatic

def citation (value : Nat) : P93AuthorityCitationToken where
  components := [{ value := value, primes := 0 }]

def parentComponent : P93CanonicalNameComponent :=
  { role := .parent, path := [0] }

def prefixComponent : P93CanonicalNameComponent :=
  { role := .prefix, path := [1] }

def citedBase (unit : P93AuthorityPhysicalUnit) (locant : Nat)
    (component : P93CanonicalNameComponent) (kind : UnitKind)
    (descriptor : Descriptor) : P93AcyclicBasePayload where
  unit := unit
  citation? := some (citation locant)
  component := component
  kind := kind
  descriptor := descriptor

def uncitedBase (unit : P93AuthorityPhysicalUnit)
    (component : P93CanonicalNameComponent) (kind : UnitKind)
    (descriptor : Descriptor) : P93AcyclicBasePayload where
  unit := unit
  citation? := none
  component := component
  kind := kind
  descriptor := descriptor

theorem citedBase_intrinsic
    (unit : P93AuthorityPhysicalUnit) (locant : Nat)
    (component : P93CanonicalNameComponent) (kind : UnitKind)
    (descriptor : Descriptor)
    (componentValid : component.Valid)
    (kindMatches : P93AcyclicUnitKindMatchesPhysical kind unit)
    (descriptorApplies : DescriptorApplies kind descriptor) :
    (citedBase unit locant component kind descriptor).Intrinsic := by
  exact ⟨componentValid, kindMatches, descriptorApplies, by
    intro candidate candidateMem
    have candidateEq : candidate = citation locant := by
      have reverse : citation locant = candidate := by
        simpa [citedBase] using candidateMem
      exact reverse.symm
    subst candidate
    simp [citation, P93AuthorityCitationToken.Valid]⟩

theorem uncitedBase_intrinsic
    (unit : P93AuthorityPhysicalUnit)
    (component : P93CanonicalNameComponent) (kind : UnitKind)
    (descriptor : Descriptor)
    (componentValid : component.Valid)
    (kindMatches : P93AcyclicUnitKindMatchesPhysical kind unit)
    (descriptorApplies : DescriptorApplies kind descriptor) :
    (uncitedBase unit component kind descriptor).Intrinsic := by
  exact ⟨componentValid, kindMatches, descriptorApplies, by simp [uncitedBase]⟩

theorem baseClaims_sourceEnvelope
    (source : AuthoritativeChemicalInput) (base : P93AcyclicBasePayload)
    (envelope : P93CanonicalPhysicalUnitEnvelope source base.unit)
    (intrinsic : base.Intrinsic)
    (classification :
      match base.kind, base.unit with
      | .evenDoubleBondCumulene, .axis path =>
          P93AuthorityCanonicalEvenCumuleneAxisPerceived source path
      | .oddDoubleBondCumulene, .axis path =>
          P93AuthorityCanonicalOddCumuleneAxisPerceived source path
      | _, _ => True) :
    ∀ claim ∈ base.baseClaims, claim.SourceEnvelope source := by
  intro claim claimMem
  rcases intrinsic with ⟨componentValid, kindMatches, _descriptorApplies, citationValid⟩
  cases citationEq : base.citation? with
  | none =>
      simp [P93AcyclicBasePayload.baseClaims, citationEq] at claimMem
      rcases claimMem with rfl | rfl | rfl | rfl
      · exact ⟨componentValid, envelope⟩
      · exact envelope
      · exact ⟨envelope, kindMatches, classification⟩
      · exact envelope
  | some sourceCitation =>
      simp [P93AcyclicBasePayload.baseClaims, citationEq] at claimMem
      rcases claimMem with rfl | rfl | rfl | rfl | rfl
      · exact ⟨citationValid sourceCitation (by simp [citationEq]), envelope⟩
      · exact ⟨componentValid, envelope⟩
      · exact envelope
      · exact ⟨envelope, kindMatches, classification⟩
      · exact envelope

/-! ## P-93.4.1: acyclic stereogenic centers -/

/-- Full heavy-atom graph of `(2R,3S)-3-chloro-2-hydroxybutanoic acid`. -/
def centersSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [carbonAtom, carbonAtom, carbonAtom, carbonAtom, oxygenAtom, oxygenAtom,
          oxygenAtom, chlorineAtom]
      interactions :=
        [bond 0 1, bond 0 4 2, bond 0 5, bond 1 2, bond 1 6, bond 2 3, bond 2 7] }

theorem centersSource_structurallyWellFormed : centersSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff centersSource).mp
    (by decide)

theorem centersUnit_envelope :
    P93CanonicalPhysicalUnitEnvelope centersSource (.atomCenter 1) := by
  refine ⟨by decide, [0, 2, 6], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, centersSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, centersSource, bond,
        P93AuthorityBinaryInteractionKind]

def centersBase : P93AcyclicBasePayload :=
  citedBase (.atomCenter 1) 2 parentComponent .chiralCenter .R

theorem centersBase_intrinsic : centersBase.Intrinsic := by
  apply citedBase_intrinsic
  · simp [parentComponent, P93CanonicalNameComponent.Valid]
  · trivial
  · trivial

def centersPayload : P93AcyclicClausePayload .acyclicCenters := .centers centersBase

theorem centersPayload_valid :
    (P93ClausePayloadData.acyclic centersPayload).ValidFor centersSource := by
  refine ⟨?_, centersBase_intrinsic, Or.inl rfl⟩
  simpa [P93ClausePayloadData.toClaims, centersPayload,
    P93AcyclicClausePayload.toClaims] using
      baseClaims_sourceEnvelope centersSource centersBase centersUnit_envelope
        centersBase_intrinsic (by simp [centersBase, citedBase])

def centersObservation : P93ClauseObservation centersSource (.acyclic .acyclicCenters) where
  payload := .acyclic centersPayload
  validFor := centersPayload_valid

def centersTranscription : P93CanonicalSourceTranscription centersSource
    (.acyclic .acyclicCenters) centersObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 51
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.4.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.4.1.2"
  observationSubsectionNonempty := by decide
  printedObservation := "(2R,3S)-3-chloro-2-hydroxybutanoic acid (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 51, P-93.4.1.2, first named example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "(2R,3S)-3-chloro-2-hydroxybutanoic acid (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def centersEntry : P93CanonicalClauseObservationEntry where
  source := centersSource
  sourceAdmitted := centersSource_structurallyWellFormed
  clause := .acyclic .acyclicCenters
  clauseListed := by decide
  observation := centersObservation
  transcription := centersTranscription

/-! ## P-93.4.1.1: one stereogenic center -/

/-- Full heavy-atom graph of `(2S)-butan-2-ol`. -/
def singleSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom, oxygenAtom]
      interactions := [bond 0 1, bond 1 2, bond 2 3, bond 1 4] }

theorem singleSource_structurallyWellFormed : singleSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff singleSource).mp
    (by decide)

theorem singleUnit_envelope :
    P93CanonicalPhysicalUnitEnvelope singleSource (.atomCenter 1) := by
  refine ⟨by decide, [0, 2, 4], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, singleSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, singleSource, bond,
        P93AuthorityBinaryInteractionKind]

def singleBase : P93AcyclicBasePayload :=
  citedBase (.atomCenter 1) 2 parentComponent .chiralCenter .S

theorem singleBase_intrinsic : singleBase.Intrinsic := by
  apply citedBase_intrinsic
  · simp [parentComponent, P93CanonicalNameComponent.Valid]
  · trivial
  · trivial

def singlePayload : P93AcyclicClausePayload .singleAcyclicCenter :=
  .single singleBase true false [.stereochemical]

theorem singlePayload_valid :
    (P93ClausePayloadData.acyclic singlePayload).ValidFor singleSource := by
  constructor
  · intro claim claimMem
    simp only [P93ClausePayloadData.toClaims, singlePayload,
      P93AcyclicClausePayload.toClaims, List.mem_append] at claimMem
    rcases claimMem with baseMem | specialMem
    · exact baseClaims_sourceEnvelope singleSource singleBase singleUnit_envelope
        singleBase_intrinsic (by simp [singleBase, citedBase]) claim baseMem
    · simp at specialMem
      subst claim
      exact ⟨singleUnit_envelope,
        by simp [singleBase, citedBase, citation, P93AuthorityCitationToken.Valid],
        by simp [P93AcyclicAffixOrderConforms]⟩
  · exact ⟨singleBase_intrinsic, Or.inl rfl, by
      simp [singleBase, citedBase, SingleCenterLocantConforms], by
      simp [P93AcyclicAffixOrderConforms], by simp, by simp⟩

def singleObservation :
    P93ClauseObservation singleSource (.acyclic .singleAcyclicCenter) where
  payload := .acyclic singlePayload
  validFor := singlePayload_valid

def singleTranscription : P93CanonicalSourceTranscription singleSource
    (.acyclic .singleAcyclicCenter) singleObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 50
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.4.1.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.4.1.1"
  observationSubsectionNonempty := by decide
  printedObservation := "(2S)-butan-2-ol (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 50, P-93.4.1.1, second named example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "(2S)-butan-2-ol (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def singleEntry : P93CanonicalClauseObservationEntry where
  source := singleSource
  sourceAdmitted := singleSource_structurallyWellFormed
  clause := .acyclic .singleAcyclicCenter
  clauseListed := by decide
  observation := singleObservation
  transcription := singleTranscription

/-! ## P-93.4.1.2: several center descriptors in one structure -/

/-- Full heavy-atom graph of `(2R,3s,4S)-2,3,4-trichloropentanedioic acid`. -/
def multipleCentersSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [ carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom
        , oxygenAtom, oxygenAtom, oxygenAtom, oxygenAtom
        , chlorineAtom, chlorineAtom, chlorineAtom ]
      interactions :=
        [ bond 0 1, bond 0 5 2, bond 0 6, bond 1 2, bond 1 9
        , bond 2 3, bond 2 10, bond 3 4, bond 3 11, bond 4 7 2, bond 4 8 ] }

theorem multipleCentersSource_structurallyWellFormed :
    multipleCentersSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    multipleCentersSource).mp (by decide)

theorem multipleCentersUnit2_envelope :
    P93CanonicalPhysicalUnitEnvelope multipleCentersSource (.atomCenter 1) := by
  refine ⟨by decide, [0, 2, 9], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, multipleCentersSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, multipleCentersSource, bond,
        P93AuthorityBinaryInteractionKind]

theorem multipleCentersUnit3_envelope :
    P93CanonicalPhysicalUnitEnvelope multipleCentersSource (.atomCenter 2) := by
  refine ⟨by decide, [1, 3, 10], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, multipleCentersSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, multipleCentersSource, bond,
        P93AuthorityBinaryInteractionKind]

theorem multipleCentersUnit4_envelope :
    P93CanonicalPhysicalUnitEnvelope multipleCentersSource (.atomCenter 3) := by
  refine ⟨by decide, [2, 4, 11], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, multipleCentersSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, multipleCentersSource, bond,
        P93AuthorityBinaryInteractionKind]

def multipleCentersBase2 : P93AcyclicBasePayload :=
  citedBase (.atomCenter 1) 2 parentComponent .chiralCenter .R
def multipleCentersBase3 : P93AcyclicBasePayload :=
  citedBase (.atomCenter 2) 3 parentComponent .pseudoasymmetricCenter .s
def multipleCentersBase4 : P93AcyclicBasePayload :=
  citedBase (.atomCenter 3) 4 parentComponent .chiralCenter .S

theorem multipleCentersBase2_intrinsic : multipleCentersBase2.Intrinsic := by
  apply citedBase_intrinsic <;>
    simp [parentComponent, P93CanonicalNameComponent.Valid,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies]
theorem multipleCentersBase3_intrinsic : multipleCentersBase3.Intrinsic := by
  apply citedBase_intrinsic <;>
    simp [parentComponent, P93CanonicalNameComponent.Valid,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies]
theorem multipleCentersBase4_intrinsic : multipleCentersBase4.Intrinsic := by
  apply citedBase_intrinsic <;>
    simp [parentComponent, P93CanonicalNameComponent.Valid,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies]

def multipleCentersPayload : P93AcyclicClausePayload .multipleDescriptorsOneCenter :=
  .multipleCenters [multipleCentersBase2, multipleCentersBase3, multipleCentersBase4]

theorem multipleCentersPayload_valid :
    (P93ClausePayloadData.acyclic multipleCentersPayload).ValidFor
      multipleCentersSource := by
  constructor
  · intro claim claimMem
    simp only [P93ClausePayloadData.toClaims, multipleCentersPayload,
      P93AcyclicClausePayload.toClaims, List.mem_append, List.mem_flatMap] at claimMem
    rcases claimMem with baseMem | specialMem
    · rcases baseMem with ⟨base, baseListMem, baseClaimMem⟩
      simp at baseListMem
      rcases baseListMem with rfl | rfl | rfl
      · exact baseClaims_sourceEnvelope multipleCentersSource multipleCentersBase2
          multipleCentersUnit2_envelope multipleCentersBase2_intrinsic
            (by simp [multipleCentersBase2, citedBase]) claim baseClaimMem
      · exact baseClaims_sourceEnvelope multipleCentersSource multipleCentersBase3
          multipleCentersUnit3_envelope multipleCentersBase3_intrinsic
            (by simp [multipleCentersBase3, citedBase]) claim baseClaimMem
      · exact baseClaims_sourceEnvelope multipleCentersSource multipleCentersBase4
          multipleCentersUnit4_envelope multipleCentersBase4_intrinsic
            (by simp [multipleCentersBase4, citedBase]) claim baseClaimMem
    · simp [P93AcyclicBasePayload.triple] at specialMem
      subst claim
      simp [P93SourceClaim.SourceEnvelope, P93AcyclicClaim.SourceEnvelope,
        multipleCentersBase2, multipleCentersBase3, multipleCentersBase4, citedBase,
        multipleCentersUnit2_envelope, multipleCentersUnit3_envelope,
        multipleCentersUnit4_envelope, DescriptorApplies]
  · simp [multipleCentersPayload, P93AcyclicClausePayload.Intrinsic,
      multipleCentersBase2, multipleCentersBase3, multipleCentersBase4,
      citedBase, parentComponent, citation, P93CanonicalNameComponent.Valid,
      P93AcyclicBasePayload.Intrinsic, P93AcyclicBasePresentCitations,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies,
      P93AuthorityCitationToken.Valid, P93AuthorityCitationToken.CitationLE,
      P93AuthorityCitationToken.key, P93AuthorityNatListLexLE]

def multipleCentersObservation : P93ClauseObservation multipleCentersSource
    (.acyclic .multipleDescriptorsOneCenter) where
  payload := .acyclic multipleCentersPayload
  validFor := multipleCentersPayload_valid

def multipleCentersTranscription : P93CanonicalSourceTranscription multipleCentersSource
    (.acyclic .multipleDescriptorsOneCenter) multipleCentersObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 51
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.4.1.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.4.1.2"
  observationSubsectionNonempty := by decide
  printedObservation := "(2R,3s,4S)-2,3,4-trichloropentanedioic acid (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 51, P-93.4.1.2, fifth named example, note, and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "(2R,3s,4S)-2,3,4-trichloropentanedioic acid (PIN); printed note identifies C-3 as s"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def multipleCentersEntry : P93CanonicalClauseObservationEntry where
  source := multipleCentersSource
  sourceAdmitted := multipleCentersSource_structurallyWellFormed
  clause := .acyclic .multipleDescriptorsOneCenter
  clauseListed := by decide
  observation := multipleCentersObservation
  transcription := multipleCentersTranscription

/-! ## P-93.4.1.3: descriptors attached to name components -/

/-- Full heavy-atom graph of `(2S)-butan-2-yl (4S)-4-chlorohexanoate`. -/
def prefixSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [ carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom
        , oxygenAtom, oxygenAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom
        , chlorineAtom ]
      interactions :=
        [ bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 5, bond 0 6 2
        , bond 0 7, bond 7 8, bond 8 9, bond 8 10, bond 10 11, bond 3 12 ] }

theorem prefixSource_structurallyWellFormed : prefixSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff prefixSource).mp
    (by decide)

theorem prefixUnit_envelope :
    P93CanonicalPhysicalUnitEnvelope prefixSource (.atomCenter 8) := by
  refine ⟨by decide, [7, 9, 10], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, prefixSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, prefixSource, bond,
        P93AuthorityBinaryInteractionKind]

def prefixBase : P93AcyclicBasePayload :=
  citedBase (.atomCenter 8) 2 prefixComponent .chiralCenter .S

theorem prefixBase_intrinsic : prefixBase.Intrinsic := by
  apply citedBase_intrinsic
  · simp [prefixComponent, P93CanonicalNameComponent.Valid]
  · trivial
  · trivial

def prefixPayload : P93AcyclicClausePayload .prefixComponentCenters :=
  .prefix prefixBase (.immediatelyBeforeComponent prefixComponent)

theorem prefixPayload_valid :
    (P93ClausePayloadData.acyclic prefixPayload).ValidFor prefixSource := by
  refine ⟨?_, prefixBase_intrinsic, Or.inl rfl, rfl⟩
  simpa [P93ClausePayloadData.toClaims, prefixPayload,
    P93AcyclicClausePayload.toClaims] using
      baseClaims_sourceEnvelope prefixSource prefixBase prefixUnit_envelope
        prefixBase_intrinsic (by simp [prefixBase, citedBase])

def prefixObservation :
    P93ClauseObservation prefixSource (.acyclic .prefixComponentCenters) where
  payload := .acyclic prefixPayload
  validFor := prefixPayload_valid

def prefixTranscription : P93CanonicalSourceTranscription prefixSource
    (.acyclic .prefixComponentCenters) prefixObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 52
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.4.1.3"
  clauseSectionExact := rfl
  observationSubsection := "P-93.4.1.3"
  observationSubsectionNonempty := by decide
  printedObservation := "(2S)-butan-2-yl (4S)-4-chlorohexanoate (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 52, P-93.4.1.3, first named example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "(2S)-butan-2-yl (4S)-4-chlorohexanoate (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def prefixEntry : P93CanonicalClauseObservationEntry where
  source := prefixSource
  sourceAdmitted := prefixSource_structurallyWellFormed
  clause := .acyclic .prefixComponentCenters
  clauseListed := by decide
  observation := prefixObservation
  transcription := prefixTranscription

/-! ## P-93.4.2.1: ordinary double bonds -/

/-- Full heavy-atom graph of `(1Z)-1,2-dibromo-1-chloro-2-iodoethene`. -/
def ordinaryDoubleSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [carbonAtom, carbonAtom, bromineAtom, bromineAtom, chlorineAtom, iodineAtom]
      interactions := [bond 0 1 2, bond 0 2, bond 0 4, bond 1 3, bond 1 5] }

theorem ordinaryDoubleSource_structurallyWellFormed :
    ordinaryDoubleSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    ordinaryDoubleSource).mp (by decide)

theorem ordinaryDoubleUnit_envelope :
    P93CanonicalPhysicalUnitEnvelope ordinaryDoubleSource (.bond 0 1) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [P93AuthorityBinaryBond, ordinaryDoubleSource, bond,
    P93AuthorityBinaryInteractionKind]

def ordinaryDoubleBase : P93AcyclicBasePayload :=
  citedBase (.bond 0 1) 1 parentComponent .ordinaryDoubleBond .Z

theorem ordinaryDoubleBase_intrinsic : ordinaryDoubleBase.Intrinsic := by
  apply citedBase_intrinsic <;>
    simp [parentComponent, P93CanonicalNameComponent.Valid,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies]

def ordinaryDoublePayload : P93AcyclicClausePayload .ordinaryDoubleBonds :=
  .ordinaryDouble ordinaryDoubleBase

theorem ordinaryDoublePayload_valid :
    (P93ClausePayloadData.acyclic ordinaryDoublePayload).ValidFor
      ordinaryDoubleSource := by
  refine ⟨?_, ordinaryDoubleBase_intrinsic, rfl⟩
  simpa [P93ClausePayloadData.toClaims, ordinaryDoublePayload,
    P93AcyclicClausePayload.toClaims] using
      baseClaims_sourceEnvelope ordinaryDoubleSource ordinaryDoubleBase
        ordinaryDoubleUnit_envelope ordinaryDoubleBase_intrinsic
          (by simp [ordinaryDoubleBase, citedBase])

def ordinaryDoubleObservation : P93ClauseObservation ordinaryDoubleSource
    (.acyclic .ordinaryDoubleBonds) where
  payload := .acyclic ordinaryDoublePayload
  validFor := ordinaryDoublePayload_valid

def ordinaryDoubleTranscription : P93CanonicalSourceTranscription ordinaryDoubleSource
    (.acyclic .ordinaryDoubleBonds) ordinaryDoubleObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 52
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.4.2.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.4.2.1.1"
  observationSubsectionNonempty := by decide
  printedObservation := "(1Z)-1,2-dibromo-1-chloro-2-iodoethene (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 52, P-93.4.2.1.1, third named example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "(1Z)-1,2-dibromo-1-chloro-2-iodoethene (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def ordinaryDoubleEntry : P93CanonicalClauseObservationEntry where
  source := ordinaryDoubleSource
  sourceAdmitted := ordinaryDoubleSource_structurallyWellFormed
  clause := .acyclic .ordinaryDoubleBonds
  clauseListed := by decide
  observation := ordinaryDoubleObservation
  transcription := ordinaryDoubleTranscription

/-! ## P-93.4.2.1.1: E/Z and cis/trans context -/

/-- Full heavy-atom graph of `(2E)-but-2-ene`. -/
def ezSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom]
      interactions := [bond 0 1, bond 1 2 2, bond 2 3] }

theorem ezSource_structurallyWellFormed : ezSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff ezSource).mp
    (by decide)

theorem ezUnit_envelope : P93CanonicalPhysicalUnitEnvelope ezSource (.bond 1 2) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [P93AuthorityBinaryBond, ezSource, bond, P93AuthorityBinaryInteractionKind]

def ezBase : P93AcyclicBasePayload :=
  citedBase (.bond 1 2) 2 parentComponent .ordinaryDoubleBond .E

theorem ezBase_intrinsic : ezBase.Intrinsic := by
  apply citedBase_intrinsic <;>
    simp [parentComponent, P93CanonicalNameComponent.Valid,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies]

def ezCarbonContext : CarbonDoubleBondContext where
  firstCarbonHasHydrogen := true
  secondCarbonHasHydrogen := true

def ezPayload : P93AcyclicClausePayload .doubleBondEZCisTrans :=
  .ezCisTrans ezBase .preferredIUPACName ezCarbonContext

theorem ezPayload_valid :
    (P93ClausePayloadData.acyclic ezPayload).ValidFor ezSource := by
  constructor
  · intro claim claimMem
    simp only [P93ClausePayloadData.toClaims, ezPayload,
      P93AcyclicClausePayload.toClaims, List.mem_append] at claimMem
    rcases claimMem with baseMem | specialMem
    · exact baseClaims_sourceEnvelope ezSource ezBase ezUnit_envelope
        ezBase_intrinsic (by simp [ezBase, citedBase]) claim baseMem
    · simp at specialMem
      subst claim
      exact ezUnit_envelope
  · exact ⟨ezBase_intrinsic, rfl, by
      simp [ezBase, citedBase, DescriptorRecommended], by
      intro impossible
      simp [ezBase, citedBase] at impossible⟩

def ezObservation : P93ClauseObservation ezSource (.acyclic .doubleBondEZCisTrans) where
  payload := .acyclic ezPayload
  validFor := ezPayload_valid

def ezTranscription : P93CanonicalSourceTranscription ezSource
    (.acyclic .doubleBondEZCisTrans) ezObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 52
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.4.2.1.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.4.2.1.1"
  observationSubsectionNonempty := by decide
  printedObservation := "(2E)-but-2-ene (PIN); trans-but-2-ene"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 52, P-93.4.2.1.1, second named example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "(2E)-but-2-ene (PIN); trans-but-2-ene"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def ezEntry : P93CanonicalClauseObservationEntry where
  source := ezSource
  sourceAdmitted := ezSource_structurallyWellFormed
  clause := .acyclic .doubleBondEZCisTrans
  clauseListed := by decide
  observation := ezObservation
  transcription := ezTranscription

/-! ## P-93.4.2.1.2: more than one double bond -/

/-- Full heavy-atom graph of `(2Z,4E)-octa-2,4-diene`. -/
def multipleDoubleSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom,
        carbonAtom, carbonAtom]
      interactions :=
        [bond 0 1, bond 1 2 2, bond 2 3, bond 3 4 2, bond 4 5, bond 5 6, bond 6 7] }

theorem multipleDoubleSource_structurallyWellFormed :
    multipleDoubleSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    multipleDoubleSource).mp (by decide)

theorem multipleDoubleUnit2_envelope :
    P93CanonicalPhysicalUnitEnvelope multipleDoubleSource (.bond 1 2) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [P93AuthorityBinaryBond, multipleDoubleSource, bond,
    P93AuthorityBinaryInteractionKind]

theorem multipleDoubleUnit4_envelope :
    P93CanonicalPhysicalUnitEnvelope multipleDoubleSource (.bond 3 4) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [P93AuthorityBinaryBond, multipleDoubleSource, bond,
    P93AuthorityBinaryInteractionKind]

def multipleDoubleBase2 : P93AcyclicBasePayload :=
  citedBase (.bond 1 2) 2 parentComponent .ordinaryDoubleBond .Z
def multipleDoubleBase4 : P93AcyclicBasePayload :=
  citedBase (.bond 3 4) 4 parentComponent .ordinaryDoubleBond .E

theorem multipleDoubleBase2_intrinsic : multipleDoubleBase2.Intrinsic := by
  apply citedBase_intrinsic <;>
    simp [parentComponent, P93CanonicalNameComponent.Valid,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies]
theorem multipleDoubleBase4_intrinsic : multipleDoubleBase4.Intrinsic := by
  apply citedBase_intrinsic <;>
    simp [parentComponent, P93CanonicalNameComponent.Valid,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies]

def multipleDoublePayload : P93AcyclicClausePayload .multipleDoubleBonds :=
  .multipleDouble [multipleDoubleBase2, multipleDoubleBase4]

theorem multipleDoublePayload_valid :
    (P93ClausePayloadData.acyclic multipleDoublePayload).ValidFor
      multipleDoubleSource := by
  constructor
  · intro claim claimMem
    simp only [P93ClausePayloadData.toClaims, multipleDoublePayload,
      P93AcyclicClausePayload.toClaims, List.mem_append, List.mem_flatMap] at claimMem
    rcases claimMem with baseMem | specialMem
    · rcases baseMem with ⟨base, baseListMem, baseClaimMem⟩
      simp at baseListMem
      rcases baseListMem with rfl | rfl
      · exact baseClaims_sourceEnvelope multipleDoubleSource multipleDoubleBase2
          multipleDoubleUnit2_envelope multipleDoubleBase2_intrinsic
            (by simp [multipleDoubleBase2, citedBase]) claim baseClaimMem
      · exact baseClaims_sourceEnvelope multipleDoubleSource multipleDoubleBase4
          multipleDoubleUnit4_envelope multipleDoubleBase4_intrinsic
            (by simp [multipleDoubleBase4, citedBase]) claim baseClaimMem
    · simp [P93AcyclicBasePayload.triple] at specialMem
      rcases specialMem with rfl | rfl
      · simp [P93SourceClaim.SourceEnvelope, P93AcyclicClaim.SourceEnvelope,
          multipleDoubleBase2, multipleDoubleBase4, citedBase,
          multipleDoubleUnit2_envelope, multipleDoubleUnit4_envelope]
      · simp [P93SourceClaim.SourceEnvelope, P93AcyclicClaim.SourceEnvelope,
          multipleDoubleBase2, multipleDoubleBase4, citedBase,
          multipleDoubleUnit2_envelope, multipleDoubleUnit4_envelope, DescriptorApplies]
  · simp [multipleDoublePayload, P93AcyclicClausePayload.Intrinsic,
      multipleDoubleBase2, multipleDoubleBase4, citedBase, parentComponent, citation,
      P93CanonicalNameComponent.Valid, P93AcyclicBasePayload.Intrinsic,
      P93AcyclicBasePresentCitations, P93AcyclicUnitKindMatchesPhysical,
      DescriptorApplies, P93AuthorityCitationToken.Valid,
      P93AuthorityCitationToken.CitationLE, P93AuthorityCitationToken.key,
      P93AuthorityNatListLexLE]

def multipleDoubleObservation : P93ClauseObservation multipleDoubleSource
    (.acyclic .multipleDoubleBonds) where
  payload := .acyclic multipleDoublePayload
  validFor := multipleDoublePayload_valid

def multipleDoubleTranscription : P93CanonicalSourceTranscription multipleDoubleSource
    (.acyclic .multipleDoubleBonds) multipleDoubleObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 53
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.4.2.1.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.4.2.1.2"
  observationSubsectionNonempty := by decide
  printedObservation := "(2Z,4E)-octa-2,4-diene (PIN); 2-cis,4-trans-octa-2,4-diene"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 53, P-93.4.2.1.2, first named example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "(2Z,4E)-octa-2,4-diene (PIN); 2-cis,4-trans-octa-2,4-diene"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def multipleDoubleEntry : P93CanonicalClauseObservationEntry where
  source := multipleDoubleSource
  sourceAdmitted := multipleDoubleSource_structurallyWellFormed
  clause := .acyclic .multipleDoubleBonds
  clauseListed := by decide
  observation := multipleDoubleObservation
  transcription := multipleDoubleTranscription

/-! ## P-93.4.2.1.3: double bonds involving heteroatoms -/

/-- Full heavy-atom graph of `(Z)-diphenyldiazene`; aromatic ring bonds remain aromatic. -/
def heteroDoubleSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [ nitrogenAtom, nitrogenAtom
        , carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom
        , carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom ]
      interactions :=
        [ bond 0 1 2, bond 0 2, bond 1 8
        , aromaticBond 2 3, aromaticBond 3 4, aromaticBond 4 5
        , aromaticBond 5 6, aromaticBond 6 7, aromaticBond 7 2
        , aromaticBond 8 9, aromaticBond 9 10, aromaticBond 10 11
        , aromaticBond 11 12, aromaticBond 12 13, aromaticBond 13 8 ] }

theorem heteroDoubleSource_structurallyWellFormed :
    heteroDoubleSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    heteroDoubleSource).mp (by decide)

theorem heteroDoubleUnit_envelope :
    P93CanonicalPhysicalUnitEnvelope heteroDoubleSource (.bond 0 1) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [P93AuthorityBinaryBond, heteroDoubleSource, bond, aromaticBond,
    P93AuthorityBinaryInteractionKind]

def heteroDoubleBase : P93AcyclicBasePayload :=
  uncitedBase (.bond 0 1) parentComponent .heteroatomDoubleBond .Z

theorem heteroDoubleBase_intrinsic : heteroDoubleBase.Intrinsic := by
  apply uncitedBase_intrinsic <;>
    simp [parentComponent, P93CanonicalNameComponent.Valid,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies]

def heteroDoublePayload : P93AcyclicClausePayload .heteroatomDoubleBonds :=
  .heteroDouble heteroDoubleBase .preferredIUPACName

theorem heteroDoublePayload_valid :
    (P93ClausePayloadData.acyclic heteroDoublePayload).ValidFor
      heteroDoubleSource := by
  refine ⟨?_, heteroDoubleBase_intrinsic, rfl, ?_⟩
  · simpa [P93ClausePayloadData.toClaims, heteroDoublePayload,
      P93AcyclicClausePayload.toClaims] using
        baseClaims_sourceEnvelope heteroDoubleSource heteroDoubleBase
          heteroDoubleUnit_envelope heteroDoubleBase_intrinsic
            (by simp [heteroDoubleBase, uncitedBase])
  · simp [heteroDoubleBase, uncitedBase, HeteroDoubleBondDescriptorRecommended]

def heteroDoubleObservation : P93ClauseObservation heteroDoubleSource
    (.acyclic .heteroatomDoubleBonds) where
  payload := .acyclic heteroDoublePayload
  validFor := heteroDoublePayload_valid

def heteroDoubleTranscription : P93CanonicalSourceTranscription heteroDoubleSource
    (.acyclic .heteroatomDoubleBonds) heteroDoubleObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 54
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.4.2.1.3"
  clauseSectionExact := rfl
  observationSubsection := "P-93.4.2.1.3"
  observationSubsectionNonempty := by decide
  printedObservation := "(Z)-diphenyldiazene (PIN); not cis-diphenyldiazene"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 54, P-93.4.2.1.3, first named example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "(Z)-diphenyldiazene (PIN); not cis-diphenyldiazene"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def heteroDoubleEntry : P93CanonicalClauseObservationEntry where
  source := heteroDoubleSource
  sourceAdmitted := heteroDoubleSource_structurallyWellFormed
  clause := .acyclic .heteroatomDoubleBonds
  clauseListed := by decide
  observation := heteroDoubleObservation
  transcription := heteroDoubleTranscription

/-! ## P-93.4.2.2: even-double-bond cumulenes -/

/-- Full heavy-atom graph of `(1M)-1,3-dichloropropa-1,2-diene`. -/
def evenCumuleneSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [carbonAtom, carbonAtom, carbonAtom, chlorineAtom, chlorineAtom]
      interactions := [bond 0 1 2, bond 1 2 2, bond 0 3, bond 2 4] }

theorem evenCumuleneSource_structurallyWellFormed :
    evenCumuleneSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    evenCumuleneSource).mp (by decide)

theorem evenCumuleneTerminal0 :
    P93AuthorityCumuleneTerminal evenCumuleneSource 0 := by
  refine ⟨by decide, 1, by decide, ?_, ?_⟩
  · simp [P93AuthorityExactDoubleBond, evenCumuleneSource,
      SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey]
  · intro other bounded exact
    simp [evenCumuleneSource, SemanticMolecule.atomCount] at bounded
    interval_cases other <;>
      simp [P93AuthorityExactDoubleBond, evenCumuleneSource,
        SemanticMolecule.localizedCovalentRecords,
        SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey] at exact ⊢

theorem evenCumuleneTerminal2 :
    P93AuthorityCumuleneTerminal evenCumuleneSource 2 := by
  refine ⟨by decide, 1, by decide, ?_, ?_⟩
  · simp [P93AuthorityExactDoubleBond, evenCumuleneSource,
      SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey]
  · intro other bounded exact
    simp [evenCumuleneSource, SemanticMolecule.atomCount] at bounded
    interval_cases other <;>
      simp [P93AuthorityExactDoubleBond, evenCumuleneSource,
        SemanticMolecule.localizedCovalentRecords,
        SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey] at exact ⊢

theorem evenCumuleneInternal1 :
    P93AuthorityCumuleneInternal evenCumuleneSource 1 := by
  refine ⟨by decide, 0, 2, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · simp [P93AuthorityExactDoubleBond, evenCumuleneSource,
      SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey]
  · simp [P93AuthorityExactDoubleBond, evenCumuleneSource,
      SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey]
  · intro other bounded exact
    simp [evenCumuleneSource, SemanticMolecule.atomCount] at bounded
    interval_cases other <;>
      simp [P93AuthorityExactDoubleBond, evenCumuleneSource,
        SemanticMolecule.localizedCovalentRecords,
        SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey] at exact ⊢

theorem evenCumuleneUnit_envelope :
    P93CanonicalPhysicalUnitEnvelope evenCumuleneSource (.axis [0, 1, 2]) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, evenCumuleneSource,
      SemanticMolecule.atomCount]
  · exact ⟨by decide, by decide, 0, 2, rfl, rfl, by decide⟩
  · simp [P93AuthorityExactDoubleBond, evenCumuleneSource,
      SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey]
    exact ⟨evenCumuleneTerminal0, evenCumuleneTerminal2, evenCumuleneInternal1⟩

def evenCumuleneBase : P93AcyclicBasePayload :=
  citedBase (.axis [0, 1, 2]) 1 parentComponent .evenDoubleBondCumulene .M

theorem evenCumuleneBase_intrinsic : evenCumuleneBase.Intrinsic := by
  apply citedBase_intrinsic <;>
    simp [parentComponent, P93CanonicalNameComponent.Valid,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies]

def evenCumulenePayload : P93AcyclicClausePayload .evenCumulenes :=
  .evenCumulene evenCumuleneBase .preferredIUPACName .Ra .M

theorem evenCumulenePayload_valid :
    (P93ClausePayloadData.acyclic evenCumulenePayload).ValidFor
      evenCumuleneSource := by
  refine ⟨?_, evenCumuleneBase_intrinsic, rfl, ?_, rfl, ?_⟩
  · simpa [P93ClausePayloadData.toClaims, evenCumulenePayload,
      P93AcyclicClausePayload.toClaims] using
        baseClaims_sourceEnvelope evenCumuleneSource evenCumuleneBase
          evenCumuleneUnit_envelope evenCumuleneBase_intrinsic
            ⟨evenCumuleneUnit_envelope, by decide⟩
  · simp [EvenCumuleneAxialDescriptorCorrespondence]
  · simp [evenCumuleneBase, citedBase, DescriptorRecommended]

def evenCumuleneObservation : P93ClauseObservation evenCumuleneSource
    (.acyclic .evenCumulenes) where
  payload := .acyclic evenCumulenePayload
  validFor := evenCumulenePayload_valid

def evenCumuleneTranscription : P93CanonicalSourceTranscription evenCumuleneSource
    (.acyclic .evenCumulenes) evenCumuleneObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 55
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.4.2.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.4.2.2"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(1M)-1,3-dichloropropa-1,2-diene (PIN); (1Ra)-1,3-dichloropropa-1,2-diene"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 55, P-93.4.2.2, first named example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "(1M)-1,3-dichloropropa-1,2-diene (PIN); (1Ra)-1,3-dichloropropa-1,2-diene"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def evenCumuleneEntry : P93CanonicalClauseObservationEntry where
  source := evenCumuleneSource
  sourceAdmitted := evenCumuleneSource_structurallyWellFormed
  clause := .acyclic .evenCumulenes
  clauseListed := by decide
  observation := evenCumuleneObservation
  transcription := evenCumuleneTranscription

/-! ## P-93.4.2.3: odd-double-bond cumulenes -/

/-- Full heavy-atom graph of `(2Z)-hexa-2,3,4-triene`. -/
def oddCumuleneSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom]
      interactions := [bond 0 1, bond 1 2 2, bond 2 3 2, bond 3 4 2, bond 4 5] }

theorem oddCumuleneSource_structurallyWellFormed :
    oddCumuleneSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    oddCumuleneSource).mp (by decide)

theorem oddCumuleneTerminal1 :
    P93AuthorityCumuleneTerminal oddCumuleneSource 1 := by
  refine ⟨by decide, 2, by decide, ?_, ?_⟩
  · simp [P93AuthorityExactDoubleBond, oddCumuleneSource,
      SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey]
  · intro other bounded exact
    simp [oddCumuleneSource, SemanticMolecule.atomCount] at bounded
    interval_cases other <;>
      simp [P93AuthorityExactDoubleBond, oddCumuleneSource,
        SemanticMolecule.localizedCovalentRecords,
        SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey] at exact ⊢

theorem oddCumuleneTerminal4 :
    P93AuthorityCumuleneTerminal oddCumuleneSource 4 := by
  refine ⟨by decide, 3, by decide, ?_, ?_⟩
  · simp [P93AuthorityExactDoubleBond, oddCumuleneSource,
      SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey]
  · intro other bounded exact
    simp [oddCumuleneSource, SemanticMolecule.atomCount] at bounded
    interval_cases other <;>
      simp [P93AuthorityExactDoubleBond, oddCumuleneSource,
        SemanticMolecule.localizedCovalentRecords,
        SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey] at exact ⊢

theorem oddCumuleneInternal2 :
    P93AuthorityCumuleneInternal oddCumuleneSource 2 := by
  refine ⟨by decide, 1, 3, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · simp [P93AuthorityExactDoubleBond, oddCumuleneSource,
      SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey]
  · simp [P93AuthorityExactDoubleBond, oddCumuleneSource,
      SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey]
  · intro other bounded exact
    simp [oddCumuleneSource, SemanticMolecule.atomCount] at bounded
    interval_cases other <;>
      simp [P93AuthorityExactDoubleBond, oddCumuleneSource,
        SemanticMolecule.localizedCovalentRecords,
        SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey] at exact ⊢

theorem oddCumuleneInternal3 :
    P93AuthorityCumuleneInternal oddCumuleneSource 3 := by
  refine ⟨by decide, 2, 4, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · simp [P93AuthorityExactDoubleBond, oddCumuleneSource,
      SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey]
  · simp [P93AuthorityExactDoubleBond, oddCumuleneSource,
      SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey]
  · intro other bounded exact
    simp [oddCumuleneSource, SemanticMolecule.atomCount] at bounded
    interval_cases other <;>
      simp [P93AuthorityExactDoubleBond, oddCumuleneSource,
        SemanticMolecule.localizedCovalentRecords,
        SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey] at exact ⊢

theorem oddCumuleneUnit_envelope :
    P93CanonicalPhysicalUnitEnvelope oddCumuleneSource (.axis [1, 2, 3, 4]) := by
  refine ⟨by decide, ?_, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, oddCumuleneSource,
      SemanticMolecule.atomCount]
  · exact ⟨by decide, by decide, 1, 4, rfl, rfl, by decide⟩
  · simp [P93AuthorityExactDoubleBond, oddCumuleneSource,
      SemanticMolecule.localizedCovalentRecords,
      SemanticInteraction.localizedCovalentRecord?, bond, semanticEdgeKey]
    exact ⟨oddCumuleneTerminal1, oddCumuleneTerminal4,
      oddCumuleneInternal2, oddCumuleneInternal3⟩

def oddCumuleneBase : P93AcyclicBasePayload :=
  citedBase (.axis [1, 2, 3, 4]) 2 parentComponent .oddDoubleBondCumulene .Z

theorem oddCumuleneBase_intrinsic : oddCumuleneBase.Intrinsic := by
  apply citedBase_intrinsic <;>
    simp [parentComponent, P93CanonicalNameComponent.Valid,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies]

def oddCumulenePayload : P93AcyclicClausePayload .oddCumulenes :=
  .oddCumulene oddCumuleneBase [1, 2, 3, 4] .together

theorem oddCumulenePayload_valid :
    (P93ClausePayloadData.acyclic oddCumulenePayload).ValidFor oddCumuleneSource := by
  constructor
  · intro claim claimMem
    simp only [P93ClausePayloadData.toClaims, oddCumulenePayload,
      P93AcyclicClausePayload.toClaims, List.mem_append] at claimMem
    rcases claimMem with baseMem | specialMem
    · exact baseClaims_sourceEnvelope oddCumuleneSource oddCumuleneBase
        oddCumuleneUnit_envelope oddCumuleneBase_intrinsic
          ⟨oddCumuleneUnit_envelope, by decide⟩ claim baseMem
    · simp at specialMem
      subst claim
      exact ⟨oddCumuleneUnit_envelope, by decide⟩
  · exact ⟨oddCumuleneBase_intrinsic, rfl, rfl, by
      simp [oddCumuleneBase, citedBase, OddCumuleneEZAssignment]⟩

def oddCumuleneObservation : P93ClauseObservation oddCumuleneSource
    (.acyclic .oddCumulenes) where
  payload := .acyclic oddCumulenePayload
  validFor := oddCumulenePayload_valid

def oddCumuleneTranscription : P93CanonicalSourceTranscription oddCumuleneSource
    (.acyclic .oddCumulenes) oddCumuleneObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 55
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.4.2.3"
  clauseSectionExact := rfl
  observationSubsection := "P-93.4.2.3"
  observationSubsectionNonempty := by decide
  printedObservation := "(2Z)-hexa-2,3,4-triene (PIN); cis-hexa-2,3,4-triene"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 55, P-93.4.2.3, first named example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "(2Z)-hexa-2,3,4-triene (PIN); cis-hexa-2,3,4-triene"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def oddCumuleneEntry : P93CanonicalClauseObservationEntry where
  source := oddCumuleneSource
  sourceAdmitted := oddCumuleneSource_structurallyWellFormed
  clause := .acyclic .oddCumulenes
  clauseListed := by decide
  observation := oddCumuleneObservation
  transcription := oddCumuleneTranscription

/-! ## P-93.4.2.4: multiple kinds of stereogenic unit -/

/-- Full heavy-atom graph of `(2Z,5R,7E)-nona-2,7-dien-5-ol`. -/
def multipleUnitsSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom,
          carbonAtom, carbonAtom, carbonAtom, oxygenAtom]
      interactions :=
        [ bond 0 1, bond 1 2 2, bond 2 3, bond 3 4, bond 4 5, bond 4 9
        , bond 5 6, bond 6 7 2, bond 7 8 ] }

theorem multipleUnitsSource_structurallyWellFormed :
    multipleUnitsSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    multipleUnitsSource).mp (by decide)

theorem multipleUnitsBond2_envelope :
    P93CanonicalPhysicalUnitEnvelope multipleUnitsSource (.bond 1 2) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [P93AuthorityBinaryBond, multipleUnitsSource, bond,
    P93AuthorityBinaryInteractionKind]

theorem multipleUnitsCenter5_envelope :
    P93CanonicalPhysicalUnitEnvelope multipleUnitsSource (.atomCenter 4) := by
  refine ⟨by decide, [3, 5, 9], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, multipleUnitsSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, multipleUnitsSource, bond,
        P93AuthorityBinaryInteractionKind]

theorem multipleUnitsBond7_envelope :
    P93CanonicalPhysicalUnitEnvelope multipleUnitsSource (.bond 6 7) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [P93AuthorityBinaryBond, multipleUnitsSource, bond,
    P93AuthorityBinaryInteractionKind]

def multipleUnitsBase2 : P93AcyclicBasePayload :=
  citedBase (.bond 1 2) 2 parentComponent .ordinaryDoubleBond .Z
def multipleUnitsBase5 : P93AcyclicBasePayload :=
  citedBase (.atomCenter 4) 5 parentComponent .chiralCenter .R
def multipleUnitsBase7 : P93AcyclicBasePayload :=
  citedBase (.bond 6 7) 7 parentComponent .ordinaryDoubleBond .E

theorem multipleUnitsBase2_intrinsic : multipleUnitsBase2.Intrinsic := by
  apply citedBase_intrinsic <;>
    simp [parentComponent, P93CanonicalNameComponent.Valid,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies]
theorem multipleUnitsBase5_intrinsic : multipleUnitsBase5.Intrinsic := by
  apply citedBase_intrinsic <;>
    simp [parentComponent, P93CanonicalNameComponent.Valid,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies]
theorem multipleUnitsBase7_intrinsic : multipleUnitsBase7.Intrinsic := by
  apply citedBase_intrinsic <;>
    simp [parentComponent, P93CanonicalNameComponent.Valid,
      P93AcyclicUnitKindMatchesPhysical, DescriptorApplies]

def multipleUnitsPayload : P93AcyclicClausePayload .multipleAcyclicStereogenicUnits :=
  .multipleUnits
    [ ⟨multipleUnitsBase2, .frontOfCompleteName⟩
    , ⟨multipleUnitsBase5, .frontOfCompleteName⟩
    , ⟨multipleUnitsBase7, .frontOfCompleteName⟩ ]
    (.competing [citation 7, citation 5, citation 2] .cis)

theorem multipleUnitsPayload_valid :
    (P93ClausePayloadData.acyclic multipleUnitsPayload).ValidFor
      multipleUnitsSource := by
  constructor
  · intro claim claimMem
    simp only [P93ClausePayloadData.toClaims, multipleUnitsPayload,
      P93AcyclicClausePayload.toClaims, List.mem_append, List.mem_flatMap] at claimMem
    rcases claimMem with baseMem | specialMem
    · rcases baseMem with ⟨placed, placedListMem, baseClaimMem⟩
      simp at placedListMem
      rcases placedListMem with rfl | rfl | rfl
      · exact baseClaims_sourceEnvelope multipleUnitsSource multipleUnitsBase2
          multipleUnitsBond2_envelope multipleUnitsBase2_intrinsic
            (by simp [multipleUnitsBase2, citedBase]) claim baseClaimMem
      · exact baseClaims_sourceEnvelope multipleUnitsSource multipleUnitsBase5
          multipleUnitsCenter5_envelope multipleUnitsBase5_intrinsic
            (by simp [multipleUnitsBase5, citedBase]) claim baseClaimMem
      · exact baseClaims_sourceEnvelope multipleUnitsSource multipleUnitsBase7
          multipleUnitsBond7_envelope multipleUnitsBase7_intrinsic
            (by simp [multipleUnitsBase7, citedBase]) claim baseClaimMem
    · simp at specialMem
      subst claim
      simp [P93SourceClaim.SourceEnvelope, P93AcyclicClaim.SourceEnvelope,
        multipleUnitsBase2, multipleUnitsBase5, multipleUnitsBase7, citedBase,
        multipleUnitsBond2_envelope, multipleUnitsCenter5_envelope,
        multipleUnitsBond7_envelope, citation, P93AuthorityCitationToken.Valid]
  · simp [multipleUnitsPayload, P93AcyclicClausePayload.Intrinsic,
      multipleUnitsBase2, multipleUnitsBase5, multipleUnitsBase7, citedBase,
      parentComponent, citation, P93CanonicalNameComponent.Valid,
      P93AcyclicBasePayload.Intrinsic, P93AcyclicGroupedDescriptorPlacement,
      P93AcyclicPayloadPresentCitations, P93AcyclicUnitKindMatchesPhysical,
      DescriptorApplies, P93AuthorityCitationToken.Valid,
      P93AuthorityCitationToken.CitationLE, P93AuthorityCitationToken.key,
      P93AuthorityNatListLexLE]
    decide

def multipleUnitsObservation : P93ClauseObservation multipleUnitsSource
    (.acyclic .multipleAcyclicStereogenicUnits) where
  payload := .acyclic multipleUnitsPayload
  validFor := multipleUnitsPayload_valid

def multipleUnitsTranscription : P93CanonicalSourceTranscription multipleUnitsSource
    (.acyclic .multipleAcyclicStereogenicUnits) multipleUnitsObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 56
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.4.2.4"
  clauseSectionExact := rfl
  observationSubsection := "P-93.4.2.4"
  observationSubsectionNonempty := by decide
  printedObservation := "(2Z,5R,7E)-nona-2,7-dien-5-ol (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    by_cases numberingClaim :
        claim.field? = some .acyclicNumberingCompetition
    · exact
        { supportingLocator :=
            "PDF p53 P-93.4.2.1.2 cis/Z rule; p56 P-93.4.2.4 nona example"
          supportingLocatorNonempty := by decide
          supportingObservation := "(2Z,5R,7E)-nona-2,7-dien-5-ol (PIN)"
          supportingObservationNonempty := by decide
          mode := .textAndFigure }
    · exact
        { supportingLocator :=
            "PDF page 56, P-93.4.2.4, third named example, printed descriptor order, and adjacent structure"
          supportingLocatorNonempty := by decide
          supportingObservation := "(2Z,5R,7E)-nona-2,7-dien-5-ol (PIN)"
          supportingObservationNonempty := by decide
          mode := .textAndFigure }

def multipleUnitsEntry : P93CanonicalClauseObservationEntry where
  source := multipleUnitsSource
  sourceAdmitted := multipleUnitsSource_structurallyWellFormed
  clause := .acyclic .multipleAcyclicStereogenicUnits
  clauseListed := by decide
  observation := multipleUnitsObservation
  transcription := multipleUnitsTranscription

/-! ## Exact eleven-row block invariants -/

def entries : List P93CanonicalClauseObservationEntry :=
  [ centersEntry
  , singleEntry
  , multipleCentersEntry
  , prefixEntry
  , ordinaryDoubleEntry
  , ezEntry
  , multipleDoubleEntry
  , heteroDoubleEntry
  , evenCumuleneEntry
  , oddCumuleneEntry
  , multipleUnitsEntry ]

def coveredClauses : List P93Clause := entries.map fun entry => entry.clause

@[simp] theorem entries_length : entries.length = 11 := rfl

theorem coveredClauses_exact :
    coveredClauses =
      Remaining71P93AcyclicAuthorityRow.all.map fun row => (.acyclic row : P93Clause) := rfl

theorem coveredClauses_nodup : coveredClauses.Nodup := by
  rw [coveredClauses_exact]
  decide

def sources : List AuthoritativeChemicalInput := entries.map fun entry => entry.source

theorem sources_nodup : sources.Nodup := by
  decide

theorem observationSourceUnique :
    ∀ first ∈ entries, ∀ second ∈ entries,
      first.source = second.source → first = second := by
  have entriesNodup : entries.Nodup := by
    exact List.Nodup.of_map (fun entry : P93CanonicalClauseObservationEntry => entry.source)
      sources_nodup
  exact (List.nodup_map_iff_inj_on entriesNodup).mp sources_nodup

end P93CanonicalProgramAcyclic
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.centersPayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.singlePayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.multipleCentersPayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.prefixPayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.ordinaryDoublePayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.ezPayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.multipleDoublePayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.heteroDoublePayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.evenCumuleneUnit_envelope
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.oddCumuleneUnit_envelope
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.evenCumulenePayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.oddCumulenePayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.multipleUnitsPayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.coveredClauses_exact
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.sources_nodup
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramAcyclic.observationSourceUnique
