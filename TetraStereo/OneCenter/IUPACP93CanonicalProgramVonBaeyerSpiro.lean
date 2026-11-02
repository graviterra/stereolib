import TetraStereo.OneCenter.IUPACP93CanonicalSourceClaims

set_option autoImplicit false

/-!
# Canonical source entries for the von Baeyer and spiro P-93 blocks

These nine entries transcribe the complete constitutional graphs of printed examples on PDF
pages 67--74 of the frozen Blue Book P-9 artifact.  The nontetrahedral entry deliberately splits
the qualitative printed `TBPY-5-12-C` observation from its exact executable coordinate frame.
No Cartesian coordinate is presented as a source transcription.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Acyclic
open BlueBookP93.Cyclic
open IUPACNormativeProvision

namespace P93CanonicalProgramVonBaeyerSpiro

def element (atomicNumber : Nat) (positive : 0 < atomicNumber)
    (bounded : atomicNumber ≤ 118) : PeriodicElement where
  atomicNumber := atomicNumber
  positive := positive
  atMost118 := bounded

def hydrogen : PeriodicElement := element 1 (by decide) (by decide)
def carbon : PeriodicElement := element 6 (by decide) (by decide)
def nitrogen : PeriodicElement := element 7 (by decide) (by decide)
def oxygen : PeriodicElement := element 8 (by decide) (by decide)
def fluorine : PeriodicElement := element 9 (by decide) (by decide)
def phosphorus : PeriodicElement := element 15 (by decide) (by decide)
def sulfur : PeriodicElement := element 16 (by decide) (by decide)
def chlorine : PeriodicElement := element 17 (by decide) (by decide)
def bromine : PeriodicElement := element 35 (by decide) (by decide)

def atom (value : PeriodicElement) : SemanticAtom where element := value
def H := atom hydrogen
def C := atom carbon
def N := atom nitrogen
def O := atom oxygen
def F := atom fluorine
def P := atom phosphorus
def S := atom sulfur
def Cl := atom chlorine
def Br := atom bromine

def bond (first second : Nat) (order : Nat := 1) : SemanticInteraction where
  participants := [first, second]
  kind := .covalent order

def aromaticBond (first second : Nat) : SemanticInteraction where
  participants := [first, second]
  kind := .aromatic

def citation (locant : Nat) : P93AuthorityCitationToken where
  components := [{ value := locant, primes := 0 }]

def structurallyWellFormedOfComputed (source : AuthoritativeChemicalInput)
    (computed : source.structurallyWellFormed? = true) : source.StructurallyWellFormed :=
  (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp computed

/-! ## P-93.5.2: von Baeyer systems -/

def bicyclo221 : P93AuthorityVonBaeyerSystem where
  firstBridgehead := 0
  secondBridgehead := 3
  xBridgeInternal := [1, 2]
  yBridgeInternal := [5, 4]
  zBridgeInternal := [6]

/-- `(1S,3R,4R,7S)-3-bromo-7-methylbicyclo[2.2.1]heptan-2-one`. -/
def vonBaeyerCIPSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [C, C, C, C, C, C, C, O, Br, C]
      interactions :=
        [bond 0 1, bond 1 2, bond 2 3, bond 0 5, bond 5 4, bond 4 3,
          bond 0 6, bond 6 3, bond 1 7 2, bond 2 8, bond 6 9] }

def vonBaeyerCIPPayload : P93VonBaeyerClausePayload .vonBaeyerCIPCenters :=
  .cip { system := bicyclo221, unit := .atomCenter 0, citation := citation 1 }
    0 .chiralCenter .S .absolute .CIP

theorem bicyclo221_valid_for_CIP : bicyclo221.MechanicallyValidFor vonBaeyerCIPSource := by
  simp [P93AuthorityVonBaeyerSystem.MechanicallyValidFor, bicyclo221,
    P93AuthorityVonBaeyerSystem.atoms, P93AuthorityVonBaeyerSystem.bridgePath,
    P93AuthorityAtomsBounded, P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    vonBaeyerCIPSource, SemanticMolecule.atomCount, bond, P93AuthorityBinaryInteractionKind]

theorem vonBaeyerCIPCenterEnvelope :
    P93CanonicalPhysicalUnitEnvelope vonBaeyerCIPSource (.atomCenter 0) := by
  refine ⟨by decide, [1, 5, 6], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, vonBaeyerCIPSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, vonBaeyerCIPSource, bond,
        P93AuthorityBinaryInteractionKind]

theorem vonBaeyerCIPValid :
    (P93ClausePayloadData.vonBaeyer vonBaeyerCIPPayload).ValidFor vonBaeyerCIPSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, vonBaeyerCIPPayload,
      P93VonBaeyerClausePayload.toClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl
    · exact bicyclo221_valid_for_CIP
    · exact ⟨bicyclo221_valid_for_CIP, vonBaeyerCIPCenterEnvelope, by
        simp [P93VonBaeyerUnitSupported, bicyclo221, P93AuthorityVonBaeyerSystem.atoms]⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid],
        vonBaeyerCIPCenterEnvelope⟩
    · exact ⟨by simp [vonBaeyerCIPSource, SemanticMolecule.atomCount],
        by simp [DescriptorApplies]⟩
  · refine ⟨bicyclo221_valid_for_CIP, rfl, ?_, Or.inl rfl, ?_, rfl, rfl, ?_⟩
    · simp [P93VonBaeyerUnitSupported, bicyclo221, P93AuthorityVonBaeyerSystem.atoms]
    · simp [DescriptorApplies]
    · simp [citation, P93AuthorityCitationToken.Valid]

def vonBaeyerCIPObservation :
    P93ClauseObservation vonBaeyerCIPSource (.vonBaeyer .vonBaeyerCIPCenters) where
  payload := .vonBaeyer vonBaeyerCIPPayload
  validFor := vonBaeyerCIPValid

def vonBaeyerCIPTranscription : P93CanonicalSourceTranscription vonBaeyerCIPSource
    (.vonBaeyer .vonBaeyerCIPCenters) vonBaeyerCIPObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 67
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.2.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.2.1, third displayed example"
  observationSubsectionNonempty := by decide
  printedObservation := "(1S,3R,4R,7S)-3-bromo-7-methylbicyclo[2.2.1]heptan-2-one (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 67, P-93.5.2.1, third displayed example and structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "(1S,3R,4R,7S)-3-bromo-7-methylbicyclo[2.2.1]heptan-2-one (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

/-- `2-endo-bromo-7-anti-fluorobicyclo[2.2.1]heptane`. -/
def vonBaeyerBridgeSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [C, C, C, C, C, C, C, Br, F]
      interactions :=
        [bond 0 1, bond 1 2, bond 2 3, bond 0 5, bond 5 4, bond 4 3,
          bond 0 6, bond 6 3, bond 1 7, bond 6 8] }

def vonBaeyerBridgePayload : P93VonBaeyerClausePayload .vonBaeyerEndoExoSynAnti :=
  .bridge bicyclo221 1 7 (citation 2)
    .nonHighestBridgeAtomAwayFromHighestBridge .endo

theorem bicyclo221_valid_for_bridge :
    bicyclo221.MechanicallyValidFor vonBaeyerBridgeSource := by
  simp [P93AuthorityVonBaeyerSystem.MechanicallyValidFor, bicyclo221,
    P93AuthorityVonBaeyerSystem.atoms, P93AuthorityVonBaeyerSystem.bridgePath,
    P93AuthorityAtomsBounded, P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    vonBaeyerBridgeSource, SemanticMolecule.atomCount, bond, P93AuthorityBinaryInteractionKind]

theorem vonBaeyerBridgeCenterEnvelope :
    P93CanonicalPhysicalUnitEnvelope vonBaeyerBridgeSource (.atomCenter 1) := by
  refine ⟨by decide, [0, 2, 7], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, vonBaeyerBridgeSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, vonBaeyerBridgeSource, bond,
        P93AuthorityBinaryInteractionKind]

theorem vonBaeyerBridgeValid :
    (P93ClausePayloadData.vonBaeyer vonBaeyerBridgePayload).ValidFor
      vonBaeyerBridgeSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, vonBaeyerBridgePayload,
      P93VonBaeyerClausePayload.toClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl
    · exact bicyclo221_valid_for_bridge
    · exact ⟨bicyclo221_valid_for_bridge, vonBaeyerBridgeCenterEnvelope, by
        simp [P93VonBaeyerUnitSupported, bicyclo221, P93AuthorityVonBaeyerSystem.atoms]⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid],
        vonBaeyerBridgeCenterEnvelope⟩
    · exact ⟨bicyclo221_valid_for_bridge, by
        simp [bicyclo221, P93AuthorityVonBaeyerSystem.atoms], by
        simp [bicyclo221, P93AuthorityVonBaeyerSystem.atoms], by
        simp [P93AuthorityBinaryBond, vonBaeyerBridgeSource, bond,
          P93AuthorityBinaryInteractionKind]⟩
  · refine ⟨bicyclo221_valid_for_bridge, ?_, ?_, ?_, ?_, rfl, ?_, ?_⟩
    · simp [EndoExoSynAntiApplicable, P93AuthorityVonBaeyerSystem.dimensions, bicyclo221]
    · simp [bicyclo221, P93AuthorityVonBaeyerSystem.atoms]
    · simp [bicyclo221, P93AuthorityVonBaeyerSystem.atoms]
    · simp [P93AuthorityBinaryBond, vonBaeyerBridgeSource, bond,
        P93AuthorityBinaryInteractionKind]
    · simp [BridgeDescriptorDeterminesAbsolute]
    · simp [citation, P93AuthorityCitationToken.Valid]

def vonBaeyerBridgeObservation : P93ClauseObservation vonBaeyerBridgeSource
    (.vonBaeyer .vonBaeyerEndoExoSynAnti) where
  payload := .vonBaeyer vonBaeyerBridgePayload
  validFor := vonBaeyerBridgeValid

def vonBaeyerBridgeTranscription : P93CanonicalSourceTranscription vonBaeyerBridgeSource
    (.vonBaeyer .vonBaeyerEndoExoSynAnti) vonBaeyerBridgeObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 68
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.2.2.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.2.2.1, first displayed example"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "2-endo-bromo-7-anti-fluorobicyclo[2.2.1]heptane; rel-(1R,2S,4R,7R)-2-bromo-7-fluorobicyclo[2.2.1]heptane (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 68, P-93.5.2.2.1, first displayed example and structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "2-endo-bromo-7-anti-fluorobicyclo[2.2.1]heptane; rel-(1R,2S,4R,7R)-2-bromo-7-fluorobicyclo[2.2.1]heptane (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def bicyclo831 : P93AuthorityVonBaeyerSystem where
  firstBridgehead := 0
  secondBridgehead := 9
  xBridgeInternal := [1, 2, 3, 4, 5, 6, 7, 8]
  yBridgeInternal := [11, 10, 9 + 3]
  zBridgeInternal := [13]

/-- The figure explicitly draws the bridgehead hydrogen used as the second relative ligand. -/
def vonBaeyerRelativeSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [C, C, C, C, C, C, C, C, C, C, C, C, C, C, C, H]
      interactions :=
        [bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 5, bond 5 6,
          bond 6 7, bond 7 8, bond 8 9, bond 0 11, bond 11 10, bond 10 12,
          bond 12 9, bond 0 13, bond 13 9, bond 0 14, bond 9 15] }

def vonBaeyerRelativePayload : P93VonBaeyerClausePayload .vonBaeyerCisTrans :=
  .relative bicyclo831 14 15 (some (citation 1)) (some (citation 10))
    .negative .positive .trans true .relCIP

theorem bicyclo831_valid : bicyclo831.MechanicallyValidFor vonBaeyerRelativeSource := by
  simp [P93AuthorityVonBaeyerSystem.MechanicallyValidFor, bicyclo831,
    P93AuthorityVonBaeyerSystem.atoms, P93AuthorityVonBaeyerSystem.bridgePath,
    P93AuthorityAtomsBounded, P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    vonBaeyerRelativeSource, SemanticMolecule.atomCount, bond, P93AuthorityBinaryInteractionKind]

theorem vonBaeyerRelativeFirstEnvelope :
    P93CanonicalPhysicalUnitEnvelope vonBaeyerRelativeSource (.atomCenter 0) := by
  refine ⟨by decide, [1, 11, 13, 14], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, vonBaeyerRelativeSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, vonBaeyerRelativeSource, bond,
        P93AuthorityBinaryInteractionKind]

theorem vonBaeyerRelativeSecondEnvelope :
    P93CanonicalPhysicalUnitEnvelope vonBaeyerRelativeSource (.atomCenter 9) := by
  refine ⟨by decide, [8, 12, 13, 15], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, vonBaeyerRelativeSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, vonBaeyerRelativeSource, bond,
        P93AuthorityBinaryInteractionKind]

theorem vonBaeyerRelativeValid :
    (P93ClausePayloadData.vonBaeyer vonBaeyerRelativePayload).ValidFor
      vonBaeyerRelativeSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, vonBaeyerRelativePayload,
      P93VonBaeyerClausePayload.toClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bicyclo831_valid
    · exact ⟨bicyclo831_valid, by
        simp [bicyclo831, P93AuthorityVonBaeyerSystem.atoms], by
        simp [bicyclo831, P93AuthorityBinaryBond, vonBaeyerRelativeSource, bond,
          P93AuthorityBinaryInteractionKind]⟩
    · exact ⟨bicyclo831_valid, by
        simp [bicyclo831, P93AuthorityVonBaeyerSystem.atoms], by
        simp [bicyclo831, P93AuthorityBinaryBond, vonBaeyerRelativeSource, bond,
          P93AuthorityBinaryInteractionKind]⟩
    · exact bicyclo831_valid
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid],
        vonBaeyerRelativeFirstEnvelope⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid],
        vonBaeyerRelativeSecondEnvelope⟩
  · refine ⟨bicyclo831_valid, by simp, by
      simp [bicyclo831, P93AuthorityVonBaeyerSystem.atoms], by
      simp [bicyclo831, P93AuthorityVonBaeyerSystem.atoms], ?_, ?_, by
      simp [RelativeRingSide], by simp [PreferredBridgeheadRelativeNotation], ?_, ?_, ?_⟩
    · simp [bicyclo831, P93AuthorityBinaryBond, vonBaeyerRelativeSource, bond,
        P93AuthorityBinaryInteractionKind]
    · simp [bicyclo831, P93AuthorityBinaryBond, vonBaeyerRelativeSource, bond,
        P93AuthorityBinaryInteractionKind]
    · intro sourceCitation sourceMem
      have : sourceCitation = citation 1 := Option.some.inj sourceMem.symm
      subst sourceCitation
      simp [citation, P93AuthorityCitationToken.Valid]
    · intro sourceCitation sourceMem
      have : sourceCitation = citation 10 := Option.some.inj sourceMem.symm
      subst sourceCitation
      simp [citation, P93AuthorityCitationToken.Valid]
    · intro _
      exact ⟨citation 1, citation 10, rfl, rfl⟩

def vonBaeyerRelativeObservation : P93ClauseObservation vonBaeyerRelativeSource
    (.vonBaeyer .vonBaeyerCisTrans) where
  payload := .vonBaeyer vonBaeyerRelativePayload
  validFor := vonBaeyerRelativeValid

def vonBaeyerRelativeTranscription : P93CanonicalSourceTranscription vonBaeyerRelativeSource
    (.vonBaeyer .vonBaeyerCisTrans) vonBaeyerRelativeObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 69
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.2.2.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.2.2.2, sole displayed example"
  observationSubsectionNonempty := by decide
  printedObservation := "rel-(1R,10R)-1-methylbicyclo[8.3.1]tetradecane (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 69, P-93.5.2.2.2, sole example and adjacent bridgehead-H structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "rel-(1R,10R)-1-methylbicyclo[8.3.1]tetradecane (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def vonBaeyerDoubleSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [C, C, C, C, C, C, C]
      interactions :=
        [bond 0 1, bond 1 2 2, bond 2 3, bond 0 5, bond 5 4, bond 4 3,
          bond 0 6, bond 6 3] }

def vonBaeyerDoublePayload : P93VonBaeyerClausePayload .vonBaeyerDoubleBonds :=
  .doubleBond { system := bicyclo221, unit := .bond 1 2, citation := citation 2 }
    (.ordinary true false .together none)

theorem bicyclo221_valid_for_double :
    bicyclo221.MechanicallyValidFor vonBaeyerDoubleSource := by
  simp [P93AuthorityVonBaeyerSystem.MechanicallyValidFor, bicyclo221,
    P93AuthorityVonBaeyerSystem.atoms, P93AuthorityVonBaeyerSystem.bridgePath,
    P93AuthorityAtomsBounded, P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    vonBaeyerDoubleSource, SemanticMolecule.atomCount, bond, P93AuthorityBinaryInteractionKind]

theorem vonBaeyerDoubleEnvelope :
    P93CanonicalPhysicalUnitEnvelope vonBaeyerDoubleSource (.bond 1 2) := by
  simp [P93CanonicalPhysicalUnitEnvelope, P93AuthorityBinaryBond,
    vonBaeyerDoubleSource, SemanticMolecule.atomCount, bond, P93AuthorityBinaryInteractionKind]

theorem vonBaeyerDoubleValid :
    (P93ClausePayloadData.vonBaeyer vonBaeyerDoublePayload).ValidFor
      vonBaeyerDoubleSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, vonBaeyerDoublePayload,
      P93VonBaeyerClausePayload.toClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact bicyclo221_valid_for_double
    · exact ⟨bicyclo221_valid_for_double, vonBaeyerDoubleEnvelope, by
        simp [P93VonBaeyerUnitSupported, bicyclo221, P93AuthorityVonBaeyerSystem.atoms]⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid],
        vonBaeyerDoubleEnvelope⟩
    · exact bicyclo221_valid_for_double
    · exact vonBaeyerDoubleEnvelope
    · exact ⟨bicyclo221_valid_for_double, vonBaeyerDoubleEnvelope⟩
  · refine ⟨bicyclo221_valid_for_double, ?_, ⟨1, 2, rfl⟩, ?_, ?_, ?_⟩
    · simp [P93VonBaeyerUnitSupported, bicyclo221, P93AuthorityVonBaeyerSystem.atoms]
    · simp [citation, P93AuthorityCitationToken.Valid]
    · simp [P93VonBaeyerOrdinaryDescriptorAllowed]
    · simp [P93VonBaeyerOrdinaryDoubleBondExpected, VonBaeyerDoubleBondDescriptorRequired]

def vonBaeyerDoubleObservation : P93ClauseObservation vonBaeyerDoubleSource
    (.vonBaeyer .vonBaeyerDoubleBonds) where
  payload := .vonBaeyer vonBaeyerDoublePayload
  validFor := vonBaeyerDoubleValid

def vonBaeyerDoubleTranscription : P93CanonicalSourceTranscription vonBaeyerDoubleSource
    (.vonBaeyer .vonBaeyerDoubleBonds) vonBaeyerDoubleObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 69
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.2.3"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.2.3, first displayed example"
  observationSubsectionNonempty := by decide
  printedObservation := "bicyclo[2.2.1]hept-2-ene (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 69, P-93.5.2.3, first example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "bicyclo[2.2.1]hept-2-ene (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

/-! ## P-93.5.3: tetrahedral and axial spiro systems -/

def xabcdSystem : P93AuthoritySpiroSystem where
  center := 0
  firstRingInternal := [1, 2, 3, 4]
  secondRingInternal := [5, 6, 7, 8, 9]

def xabcdSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [C, C, C, C, C, C, C, C, C, C, C, C]
      interactions :=
        [bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 0,
          bond 0 5, bond 5 6, bond 6 7, bond 7 8, bond 8 9, bond 9 0,
          bond 1 10, bond 6 11] }

def xabcdPayload : P93SpiroClausePayload .spiroXabcd :=
  .xabcd xabcdSystem (citation 5) .R

theorem xabcdSystemValid : xabcdSystem.MechanicallyValidFor xabcdSource := by
  simp [P93AuthoritySpiroSystem.MechanicallyValidFor, xabcdSystem,
    P93AuthoritySpiroSystem.atoms, P93AuthoritySpiroSystem.closedPath,
    P93AuthorityAtomsBounded, P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    xabcdSource, SemanticMolecule.atomCount, bond, P93AuthorityBinaryInteractionKind]

theorem xabcdCenterEnvelope :
    P93CanonicalPhysicalUnitEnvelope xabcdSource (.atomCenter 0) := by
  refine ⟨by decide, [1, 4, 5, 9], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, xabcdSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, xabcdSource, bond,
        P93AuthorityBinaryInteractionKind]

theorem xabcdValid :
    (P93ClausePayloadData.spiro xabcdPayload).ValidFor xabcdSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, xabcdPayload,
      P93SpiroClausePayload.toClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl | rfl
    · exact xabcdSystemValid
    · exact ⟨xabcdSystemValid, xabcdCenterEnvelope, by
        simp [P93SpiroUnitSupported, xabcdSystem, P93AuthoritySpiroSystem.atoms]⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid], xabcdCenterEnvelope⟩
    · exact xabcdSystemValid
    · exact xabcdSystemValid
  · refine ⟨xabcdSystemValid, ?_, ?_, ?_⟩
    · simp [SpiroFamilySupported]
    · exact Or.inl rfl
    · simp [citation, P93AuthorityCitationToken.Valid]

def xabcdObservation : P93ClauseObservation xabcdSource (.spiro .spiroXabcd) where
  payload := .spiro xabcdPayload
  validFor := xabcdValid

def xabcdTranscription : P93CanonicalSourceTranscription xabcdSource
    (.spiro .spiroXabcd) xabcdObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 71
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.3.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.3.1, Example 3"
  observationSubsectionNonempty := by decide
  printedObservation := "(1S,5R,7S)-1,7-dimethylspiro[4.5]decane (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 71, P-93.5.3.1, Example 3 and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "(1S,5R,7S)-1,7-dimethylspiro[4.5]decane (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def xababSystem : P93AuthoritySpiroSystem where
  center := 0
  firstRingInternal := [1, 2, 3, 4]
  secondRingInternal := [5, 6, 7, 8]

def xababSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [C, N, C, C, C, N, C, C, C, O, O]
      interactions :=
        [bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 0,
          bond 0 5, bond 5 6, bond 6 7, bond 7 8, bond 8 0,
          bond 4 9 2, bond 8 10 2] }

def xababOrder : XababOccurrenceOrder where
  firstSeniorChosen := True
  secondSeniorDistinguishedByTraversal := True
  juniorOnFirstSeniorBranchChosenFirst := True

def xababPayload : P93SpiroClausePayload .spiroXabab :=
  .xabab xababSystem (citation 5) .centerRS .R xababOrder

theorem xababSystemValid : xababSystem.MechanicallyValidFor xababSource := by
  simp [P93AuthoritySpiroSystem.MechanicallyValidFor, xababSystem,
    P93AuthoritySpiroSystem.atoms, P93AuthoritySpiroSystem.closedPath,
    P93AuthorityAtomsBounded, P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    xababSource, SemanticMolecule.atomCount, bond, P93AuthorityBinaryInteractionKind]

theorem xababCenterEnvelope :
    P93CanonicalPhysicalUnitEnvelope xababSource (.atomCenter 0) := by
  refine ⟨by decide, [1, 4, 5, 8], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, xababSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, xababSource, bond,
        P93AuthorityBinaryInteractionKind]

theorem xababValid :
    (P93ClausePayloadData.spiro xababPayload).ValidFor xababSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, xababPayload,
      P93SpiroClausePayload.toClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact xababSystemValid
    · exact ⟨xababSystemValid, xababCenterEnvelope, by
        simp [P93SpiroUnitSupported, xababSystem, P93AuthoritySpiroSystem.atoms]⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid], xababCenterEnvelope⟩
    · exact xababSystemValid
    · exact xababSystemValid
    · exact xababSystemValid
  · refine ⟨xababSystemValid, ?_, Or.inl rfl, ?_, Or.inl rfl, ?_⟩
    · simp [SpiroFamilySupported]
    · simp [ValidXababOccurrenceOrder, xababOrder]
    · simp [citation, P93AuthorityCitationToken.Valid]

def xababObservation : P93ClauseObservation xababSource (.spiro .spiroXabab) where
  payload := .spiro xababPayload
  validFor := xababValid

def xababTranscription : P93CanonicalSourceTranscription xababSource
    (.spiro .spiroXabab) xababObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 72
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.3.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.3.2, Example 1"
  observationSubsectionNonempty := by decide
  printedObservation := "(5R)-1,6-diazaspiro[4.4]nonane-4,9-dione (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 72, P-93.5.3.2, Example 1, structure, and occurrence-order explanation"
        supportingLocatorNonempty := by decide
        supportingObservation := "(5R)-1,6-diazaspiro[4.4]nonane-4,9-dione (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def spiroDoubleSystem : P93AuthoritySpiroSystem where
  center := 0
  firstRingInternal := [1, 2, 3, 4]
  secondRingInternal := [5, 6, 7, 8, 9, 10, 11]

def spiroDoubleSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 12 C
      interactions :=
        [bond 0 1, bond 1 2, bond 2 3 2, bond 3 4, bond 4 0,
          bond 0 5, bond 5 6 2, bond 6 7, bond 7 8, bond 8 9,
          bond 9 10, bond 10 11, bond 11 0] }

def spiroDoublePayload : P93SpiroClausePayload .spiroDoubleBonds :=
  .doubleBond
    { system := spiroDoubleSystem, unit := .bond 5 6, citation := citation 6 }
    spiroDoubleSystem.secondRing .together .preferredIUPACName (some .Z)

theorem spiroDoubleSystemValid :
    spiroDoubleSystem.MechanicallyValidFor spiroDoubleSource := by
  simp [P93AuthoritySpiroSystem.MechanicallyValidFor, spiroDoubleSystem,
    P93AuthoritySpiroSystem.atoms, P93AuthoritySpiroSystem.closedPath,
    P93AuthorityAtomsBounded, P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    spiroDoubleSource, SemanticMolecule.atomCount, bond, P93AuthorityBinaryInteractionKind]

theorem spiroDoubleEnvelope :
    P93CanonicalPhysicalUnitEnvelope spiroDoubleSource (.bond 5 6) := by
  simp [P93CanonicalPhysicalUnitEnvelope, P93AuthorityBinaryBond,
    spiroDoubleSource, SemanticMolecule.atomCount, bond, P93AuthorityBinaryInteractionKind]

theorem spiroDoubleValid :
    (P93ClausePayloadData.spiro spiroDoublePayload).ValidFor spiroDoubleSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, spiroDoublePayload,
      P93SpiroClausePayload.toClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact spiroDoubleSystemValid
    · exact ⟨spiroDoubleSystemValid, spiroDoubleEnvelope, by
        simp [P93SpiroUnitSupported, spiroDoubleSystem, P93AuthoritySpiroSystem.atoms]⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid], spiroDoubleEnvelope⟩
    · exact ⟨spiroDoubleSystemValid, spiroDoubleEnvelope, Or.inr rfl⟩
    · exact spiroDoubleEnvelope
    · exact ⟨spiroDoubleSystemValid, spiroDoubleEnvelope⟩
  · refine ⟨spiroDoubleSystemValid, ?_, ⟨5, 6, rfl, by
      simp [P93AuthoritySpiroSystem.secondRing, spiroDoubleSystem], by
      simp [P93AuthoritySpiroSystem.secondRing, spiroDoubleSystem]⟩,
      Or.inr rfl, ?_, ?_, ?_⟩
    · simp [P93SpiroUnitSupported, spiroDoubleSystem, P93AuthoritySpiroSystem.atoms]
    · simp [P93SpiroGeneralDoubleBondDescriptorAllowed, DescriptorApplies]
    · simp [P93SpiroDoubleBondExpected, SpiroDoubleBondDescriptorRequired,
        P93AuthoritySpiroSystem.secondRing, spiroDoubleSystem]
    · simp [citation, P93AuthorityCitationToken.Valid]

def spiroDoubleObservation : P93ClauseObservation spiroDoubleSource
    (.spiro .spiroDoubleBonds) where
  payload := .spiro spiroDoublePayload
  validFor := spiroDoubleValid

def spiroDoubleTranscription : P93CanonicalSourceTranscription spiroDoubleSource
    (.spiro .spiroDoubleBonds) spiroDoubleObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 73
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.3.3"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.3.3, second displayed example"
  observationSubsectionNonempty := by decide
  printedObservation := "(2Z,6Z)-spiro[4.7]dodeca-2,6-diene (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 73, P-93.5.3.3, second example and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "(2Z,6Z)-spiro[4.7]dodeca-2,6-diene (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def axialSystem : P93AuthoritySpiroSystem where
  center := 0
  firstRingInternal := [1, 2, 3]
  secondRingInternal := [4, 5, 6]

def axialSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := [C, C, C, C, C, C, C, Cl, Cl]
      interactions :=
        [bond 0 1, bond 1 2, bond 2 3, bond 3 0,
          bond 0 4, bond 4 5, bond 5 6, bond 6 0,
          bond 2 7, bond 5 8] }

def axialPayload : P93SpiroClausePayload .spiroAxialChirality :=
  .axial axialSystem (citation 2) .S .P

theorem axialSystemValid : axialSystem.MechanicallyValidFor axialSource := by
  simp [P93AuthoritySpiroSystem.MechanicallyValidFor, axialSystem,
    P93AuthoritySpiroSystem.atoms, P93AuthoritySpiroSystem.closedPath,
    P93AuthorityAtomsBounded, P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    axialSource, SemanticMolecule.atomCount, bond, P93AuthorityBinaryInteractionKind]

theorem axialCenterEnvelope :
    P93CanonicalPhysicalUnitEnvelope axialSource (.atomCenter 0) := by
  refine ⟨by decide, [1, 3, 4, 6], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, axialSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, axialSource, bond,
        P93AuthorityBinaryInteractionKind]

theorem axialValid :
    (P93ClausePayloadData.spiro axialPayload).ValidFor axialSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, axialPayload,
      P93SpiroClausePayload.toClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact axialSystemValid
    · exact ⟨axialSystemValid, axialCenterEnvelope, by
        simp [P93SpiroUnitSupported, axialSystem, P93AuthoritySpiroSystem.atoms]⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid], axialCenterEnvelope⟩
    · exact axialSystemValid
    · exact axialSystemValid
    · exact axialSystemValid
  · refine ⟨axialSystemValid, ?_, ?_, Or.inr rfl, Or.inr rfl, ?_, ?_, ?_⟩
    · simp [SpiroFamilySupported]
    · simp [SpiroFamilySupported]
    · simp [P93SpiroCenterAxialCorrespondence]
    · simp [DescriptorRecommended]
    · simp [citation, P93AuthorityCitationToken.Valid]

def axialObservation : P93ClauseObservation axialSource (.spiro .spiroAxialChirality) where
  payload := .spiro axialPayload
  validFor := axialValid

def axialTranscription : P93CanonicalSourceTranscription axialSource
    (.spiro .spiroAxialChirality) axialObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 74
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.3.5"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.3.5, Example 1"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(2R,4S,6R)-2,6-dichlorospiro[3.3]heptane (PIN); (2P)-2,6-dichlorospiro[3.3]heptane"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 74, P-93.5.3.5, Example 1, structure, and Xaabb explanation"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "(2R,4S,6R)-2,6-dichlorospiro[3.3]heptane (PIN); (2P)-2,6-dichlorospiro[3.3]heptane"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

/-! ## P-93.5.3.4: printed TBPY observation and separate executable witness -/

def point (x y z : Int) : CartesianPoint3 where
  x := x
  y := y
  z := z

def zeroPoint := point 0 0 0

def tbpySpatial : SpatialConfiguration where
  positions :=
    [ point 0 0 0, point 0 0 1, zeroPoint, zeroPoint, zeroPoint,
      point 0 0 (-1), point 1 0 0, zeroPoint, zeroPoint, point 0 1 0,
      zeroPoint, zeroPoint, zeroPoint, zeroPoint, zeroPoint, zeroPoint,
      zeroPoint, zeroPoint, zeroPoint, zeroPoint, zeroPoint, zeroPoint,
      point (-1) (-1) 0, zeroPoint, zeroPoint, zeroPoint, zeroPoint,
      zeroPoint, zeroPoint ]

def tbpyMolecule : SemanticMolecule where
  atoms :=
    [P, S, C, C, C, S, O, C, C, O,
      C, C, C, C, C, C, C, C, C, C, C, C,
      O, C, C, C, C, C, C]
  interactions :=
    [ bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 5, bond 5 0,
      bond 0 6, bond 6 7, aromaticBond 7 8, bond 8 9, bond 9 0,
      aromaticBond 7 10, aromaticBond 10 11, aromaticBond 11 12,
      aromaticBond 12 13, aromaticBond 13 8,
      aromaticBond 12 14, aromaticBond 14 15, aromaticBond 15 16,
      aromaticBond 16 17, aromaticBond 17 13,
      aromaticBond 10 18, aromaticBond 18 19, aromaticBond 19 20,
      aromaticBond 20 21, aromaticBond 21 11,
      bond 0 22, bond 22 23, aromaticBond 23 24, aromaticBond 24 25,
      aromaticBond 25 26, aromaticBond 26 27, aromaticBond 27 28,
      aromaticBond 28 23 ]

def tbpySource : AuthoritativeChemicalInput where
  molecule := tbpyMolecule
  spatial? := some tbpySpatial

def tbpySystem : P93AuthoritySpiroSystem where
  center := 0
  firstRingInternal := [1, 2, 3, 4, 5]
  secondRingInternal := [6, 7, 8, 9]

def tbpyPositions : Finset Nat := [1, 5, 6, 9, 22].toFinset

def tbpyFrame : P93AuthorityPolyhedralFrame where
  record :=
    { center := 0
      geometry := .trigonalBipyramid
      recognition := .higherCoordinationNearestIdealized .trigonalBipyramid
      ligands := [1, 5, 6, 9, 22]
      configurationPositions := .trigonalBipyramid 0 1
      absoluteOrientation := .trigonalBipyramidAC .clockwise }
  spatial := tbpySpatial
  centerPoint := point 0 0 0
  positionPoints :=
    [point 0 0 1, point 0 0 (-1), point 1 0 0, point 0 1 0, point (-1) (-1) 0]

def tbpyPrinted : P93CanonicalSpiroPrintedPolyhedralObservation where
  molecule := tbpyMolecule
  system := tbpySystem
  positions := tbpyPositions
  citation := citation 2
  geometry := .trigonalBipyramid
  coordination := .lambda5
  knowledge := .absolute
  descriptor := .C

def tbpyExecutable : P93CanonicalSpiroPolyhedralExecutableWitness where
  geometry := .trigonalBipyramid
  frame := tbpyFrame

def tbpyPayload : P93SpiroNontetrahedralPayload where
  printed := tbpyPrinted
  executable := tbpyExecutable

theorem tbpySystemValid : tbpySystem.MechanicallyValidFor tbpySource := by
  simp [P93AuthoritySpiroSystem.MechanicallyValidFor, tbpySystem,
    P93AuthoritySpiroSystem.atoms, P93AuthoritySpiroSystem.closedPath,
    P93AuthorityAtomsBounded, P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    tbpySource, tbpyMolecule, SemanticMolecule.atomCount, bond, aromaticBond,
    P93AuthorityBinaryInteractionKind]

theorem tbpyCarrierEnvelope :
    P93CanonicalPrintedPolyhedralCarrierEnvelope tbpySource 0 tbpyPositions := by
  simp [P93CanonicalPrintedPolyhedralCarrierEnvelope, tbpyPositions,
    P93AuthorityAtomsBounded, P93AuthorityBinaryBond, tbpySource, tbpyMolecule,
    SemanticMolecule.atomCount, bond, aromaticBond, P93AuthorityBinaryInteractionKind]

theorem tbpyFrameValid :
    P93AuthorityPolyhedralFrame.ValidFor tbpySource 0 tbpyPositions
      .trigonalBipyramid tbpyFrame := by
  simp [P93AuthorityPolyhedralFrame.ValidFor, tbpyFrame, tbpyPositions,
    tbpySource, tbpySpatial, tbpyMolecule, point, zeroPoint,
    BlueBookP94.CoordinateRing.SpatialPointAt,
    BlueBookP94.CoordinateRing.SpatialPointsAt,
    P93AuthorityBinaryBond, bond, aromaticBond, P93AuthorityBinaryInteractionKind,
    P93AuthorityConfigurationRoleFrameComplete,
    RedBookIR9.ConfigurationPositionsRecognized,
    RedBookIR9.ConfigurationPositionObservation.positionsFor?,
    RedBookIR9.GeometryRecognized,
    RedBookIR9.GeometryRecognitionObservation.recognizedGeometry?,
    RedBookIR9.AbsoluteOrientationRecognized,
    RedBookIR9.AbsoluteOrientationObservation.rotationFor?,
    BlueBookP93.geometryOfProduction, Geometry.coordinationNumber]

theorem tbpyExecutableValid : tbpyExecutable.ValidFor tbpySource tbpyPrinted := by
  refine ⟨rfl, rfl, tbpyFrameValid, .clockwise, rfl, rfl⟩

theorem tbpyValid :
    (P93ClausePayloadData.spiroNontetrahedral tbpyPayload).ValidFor tbpySource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, tbpyPayload,
      P93SpiroNontetrahedralPayload.toClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl | rfl
    · exact tbpySystemValid
    · exact ⟨tbpySystemValid, tbpyCarrierEnvelope, by
        simp [P93SpiroUnitSupported, P93SpiroNontetrahedralPayload.system,
          tbpyPrinted, tbpySystem]⟩
    · exact ⟨by simp [P93SpiroNontetrahedralPayload.citation,
        tbpyPrinted, citation, P93AuthorityCitationToken.Valid], tbpyCarrierEnvelope⟩
    · exact ⟨tbpySystemValid, by
        simp [P93SpiroNontetrahedralPayload.positions,
          tbpyPrinted, tbpyPositions]⟩
    · exact ⟨tbpySystemValid, by
        simp [P93SpiroNontetrahedralPayload.positions,
          tbpyPrinted, tbpyPositions]⟩
  · refine ⟨tbpySystemValid, ?_, tbpyCarrierEnvelope, ?_, ?_, ?_, ?_,
      tbpyExecutableValid⟩
    · simp [P93SpiroUnitSupported, P93SpiroNontetrahedralPayload.system]
    · simp [tbpyPositions, tbpyPayload, P93SpiroNontetrahedralPayload.positions,
        P93SpiroNontetrahedralPayload.geometry, tbpyPrinted, Geometry.coordinationNumber]
    · simp [P93SpiroCoordinationMatchesGeometry, tbpyPayload,
        P93SpiroNontetrahedralPayload.coordination,
        P93SpiroNontetrahedralPayload.geometry, tbpyPrinted, Geometry.coordinationNumber]
    · simp [PolyhedralACApplicable, tbpyPayload,
        P93SpiroNontetrahedralPayload.coordination, tbpyPrinted]
    · simp [tbpyPayload, P93SpiroNontetrahedralPayload.citation,
        tbpyPrinted, citation, P93AuthorityCitationToken.Valid]

def tbpyObservation : P93ClauseObservation tbpySource .spiroNontetrahedral where
  payload := .spiroNontetrahedral tbpyPayload
  validFor := tbpyValid

def tbpyTranscription : P93CanonicalSourceTranscription tbpySource
    .spiroNontetrahedral tbpyObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 74
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.3.4"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.3.4, first displayed example"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(TBPY-5-12-C)-2-phenoxy-2H-2λ5-spiro[[1,3,2]dithiaphosphinane-2,2′-phenanthro[9,10-d][1,3,2]dioxaphosphole] (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 74, P-93.5.3.4, first example, structure, and TBPY-5-12-C diagram"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "(TBPY-5-12-C)-2-phenoxy-2H-2λ5-spiro[[1,3,2]dithiaphosphinane-2,2′-phenanthro[9,10-d][1,3,2]dioxaphosphole] (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

/-! ## Proof-carrying entries and exact combined coverage -/

def mkEntry (source : AuthoritativeChemicalInput) (sourceAdmitted : source.StructurallyWellFormed)
    (clause : P93Clause) (clauseListed : clause ∈ P93Clause.all)
    (observation : P93ClauseObservation source clause)
    (transcription : P93CanonicalSourceTranscription source clause observation) :
    P93CanonicalClauseObservationEntry where
  source := source
  sourceAdmitted := sourceAdmitted
  clause := clause
  clauseListed := clauseListed
  observation := observation
  transcription := transcription

def vonBaeyerCIPEntry := mkEntry vonBaeyerCIPSource
  (structurallyWellFormedOfComputed vonBaeyerCIPSource (by decide))
  (.vonBaeyer .vonBaeyerCIPCenters)
  (by decide) vonBaeyerCIPObservation vonBaeyerCIPTranscription
def vonBaeyerBridgeEntry := mkEntry vonBaeyerBridgeSource
  (structurallyWellFormedOfComputed vonBaeyerBridgeSource (by decide))
  (.vonBaeyer .vonBaeyerEndoExoSynAnti)
  (by decide) vonBaeyerBridgeObservation vonBaeyerBridgeTranscription
def vonBaeyerRelativeEntry := mkEntry vonBaeyerRelativeSource
  (structurallyWellFormedOfComputed vonBaeyerRelativeSource (by decide))
  (.vonBaeyer .vonBaeyerCisTrans)
  (by decide) vonBaeyerRelativeObservation vonBaeyerRelativeTranscription
def vonBaeyerDoubleEntry := mkEntry vonBaeyerDoubleSource
  (structurallyWellFormedOfComputed vonBaeyerDoubleSource (by decide))
  (.vonBaeyer .vonBaeyerDoubleBonds)
  (by decide) vonBaeyerDoubleObservation vonBaeyerDoubleTranscription
def xabcdEntry := mkEntry xabcdSource (structurallyWellFormedOfComputed xabcdSource (by decide))
  (.spiro .spiroXabcd) (by decide) xabcdObservation xabcdTranscription
def xababEntry := mkEntry xababSource (structurallyWellFormedOfComputed xababSource (by decide))
  (.spiro .spiroXabab) (by decide) xababObservation xababTranscription
def spiroDoubleEntry := mkEntry spiroDoubleSource
  (structurallyWellFormedOfComputed spiroDoubleSource (by decide))
  (.spiro .spiroDoubleBonds) (by decide) spiroDoubleObservation spiroDoubleTranscription
def tbpyEntry := mkEntry tbpySource (structurallyWellFormedOfComputed tbpySource (by decide))
  .spiroNontetrahedral (by decide) tbpyObservation tbpyTranscription
def axialEntry := mkEntry axialSource (structurallyWellFormedOfComputed axialSource (by decide))
  (.spiro .spiroAxialChirality) (by decide) axialObservation axialTranscription

def entries : List P93CanonicalClauseObservationEntry :=
  [vonBaeyerCIPEntry, vonBaeyerBridgeEntry, vonBaeyerRelativeEntry,
    vonBaeyerDoubleEntry, xabcdEntry, xababEntry, spiroDoubleEntry, tbpyEntry, axialEntry]

def coveredClauses : List P93Clause :=
  [ .vonBaeyer .vonBaeyerCIPCenters
  , .vonBaeyer .vonBaeyerEndoExoSynAnti
  , .vonBaeyer .vonBaeyerCisTrans
  , .vonBaeyer .vonBaeyerDoubleBonds
  , .spiro .spiroXabcd
  , .spiro .spiroXabab
  , .spiro .spiroDoubleBonds
  , .spiroNontetrahedral
  , .spiro .spiroAxialChirality ]

@[simp] theorem entries_length : entries.length = 9 := rfl

@[simp] theorem entries_clause_exact : entries.map (·.clause) = coveredClauses := rfl

theorem coveredClauses_nodup : coveredClauses.Nodup := by decide

theorem entries_family_source_nodup :
    (entries.map fun entry => (entry.clause.family, entry.source)).Nodup := by
  decide

end P93CanonicalProgramVonBaeyerSpiro
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramVonBaeyerSpiro.entries_family_source_nodup
