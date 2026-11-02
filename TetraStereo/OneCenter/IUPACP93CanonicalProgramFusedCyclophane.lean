import TetraStereo.OneCenter.IUPACP93CanonicalSourceClaims

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

/-!
# Canonical P-93.5.4--5 source observations

This module transcribes the coordinate-free fused and cyclophane examples whose complete
constitutional graphs and printed assignments are recoverable from the frozen P-9 artifact.
Exact coordinate realizations for the planar row are deliberately kept out of this source block;
the carrier/compiler boundary now treats such a realization as executable evidence rather than a
fact printed by the Blue Book.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Acyclic
open BlueBookP93.Cyclic
open IUPACNormativeProvision

namespace P93CanonicalProgramFusedCyclophane

def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
def nitrogen : PeriodicElement := ⟨7, by decide, by decide⟩
def oxygen : PeriodicElement := ⟨8, by decide, by decide⟩

def carbonAtom : SemanticAtom where element := carbon
def nitrogenAtom : SemanticAtom where element := nitrogen
def oxygenAtom : SemanticAtom where element := oxygen

def bond (left right : Nat) (order : Nat := 1) : SemanticInteraction where
  participants := [left, right]
  kind := .covalent order

def citation (value : Nat) (primes : Nat := 0) : P93AuthorityCitationToken where
  components := [{ value := value, primes := primes }]

def locant3a : P93FusedLocant := ⟨3, ⟨1, by decide⟩⟩
def locant4a : P93FusedLocant := ⟨4, ⟨1, by decide⟩⟩
def locant7a : P93FusedLocant := ⟨7, ⟨1, by decide⟩⟩
def locant8a : P93FusedLocant := ⟨8, ⟨1, by decide⟩⟩
def locant9a : P93FusedLocant := ⟨9, ⟨1, by decide⟩⟩
def locant10a : P93FusedLocant := ⟨10, ⟨1, by decide⟩⟩

def claimTranscription (locator observation : String)
    (locatorNonempty : locator ≠ "") (observationNonempty : observation ≠ "")
    (claim : P93SourceClaim) :
    P93CanonicalClaimTranscription claim where
  supportingLocator := locator
  supportingLocatorNonempty := locatorNonempty
  supportingObservation := observation
  supportingObservationNonempty := observationNonempty
  mode := .textAndFigure

/-! ## P-93.5.4.1: fused-system CIP assignment -/

/-- Full heavy-atom graph of `(3aR,7aS)-octahydro-1H-indole`: a pyrrolidine and cyclohexane
sharing the fusion bond `0--1`. -/
def fusedCIPSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [carbonAtom, carbonAtom, nitrogenAtom, carbonAtom, carbonAtom,
          carbonAtom, carbonAtom, carbonAtom, carbonAtom]
      interactions :=
        [bond 0 1, bond 0 2, bond 2 3, bond 3 4, bond 4 1,
          bond 1 5, bond 5 6, bond 6 7, bond 7 8, bond 8 0] }

theorem fusedCIPSource_structurallyWellFormed : fusedCIPSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff fusedCIPSource).mp
    (by decide)

def fusedCIPSystem : P93AuthorityFusedSystem where
  atoms := [0, 1, 2, 3, 4, 5, 6, 7, 8]
  fusionEdges := [{ first := 0, second := 1 }]
  fusionLocants := [(0, locant3a), (1, locant7a)]

theorem fusedCIPSystem_valid : fusedCIPSystem.MechanicallyValidFor fusedCIPSource := by
  simp [P93AuthorityFusedSystem.MechanicallyValidFor, fusedCIPSystem,
    P93AuthorityFusionEdge.ValidFor, P93AuthorityAtomsBounded,
    P93AuthorityBinaryBond, fusedCIPSource, bond, P93AuthorityBinaryInteractionKind,
    SemanticMolecule.atomCount, locant3a, locant7a]

theorem fusedCIPCenter_envelope :
    P93CanonicalPhysicalUnitEnvelope fusedCIPSource (.atomCenter 0) := by
  refine ⟨by decide, [1, 2, 8], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, fusedCIPSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, fusedCIPSource, bond,
        P93AuthorityBinaryInteractionKind]

def fusedCIPCanonicalObservation : P93CanonicalFusedCIPObservation where
  system := fusedCIPSystem
  unit := .physical (.atomCenter 0)
  citation := locant3a
  descriptor := .R

theorem fusedCIPCanonicalObservation_valid :
    fusedCIPCanonicalObservation.ValidFor fusedCIPSource := by
  unfold P93CanonicalFusedCIPObservation.ValidFor fusedCIPCanonicalObservation
  exact ⟨fusedCIPSystem_valid,
    ⟨fusedCIPCenter_envelope,
      by simp [P93FusedPhysicalUnitSupported, fusedCIPSystem]⟩,
    by trivial, by simp [P93FusedLocant.Valid, P93FusedLocant.CitesUnit,
      P93FusedAuthorityUnit.ContainsAtom, P93FusedPhysicalUnitContainsAtom,
      fusedCIPSystem, locant3a]⟩

def fusedCIPPayload : P93FusedCyclophaneClausePayload .fusedBridgedCIP :=
  .fusedCIP fusedCIPCanonicalObservation

theorem fusedCIPPayload_valid :
    (P93ClausePayloadData.fusedCyclophane fusedCIPPayload).ValidFor fusedCIPSource := by
  constructor
  · intro claim claimMem
    have claimEq : claim = .fused (.cipObservation fusedCIPCanonicalObservation) := by
      simpa [P93ClausePayloadData.toClaims, fusedCIPPayload,
        P93FusedCyclophaneClausePayload.toClaims] using claimMem
    subst claim
    exact fusedCIPCanonicalObservation_valid
  · exact fusedCIPCanonicalObservation_valid

def fusedCIPObservation :
    P93ClauseObservation fusedCIPSource (.fusedCyclophane .fusedBridgedCIP) where
  payload := .fusedCyclophane fusedCIPPayload
  validFor := fusedCIPPayload_valid

def fusedCIPTranscription : P93CanonicalSourceTranscription fusedCIPSource
    (.fusedCyclophane .fusedBridgedCIP) fusedCIPObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 76
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.4.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.4.1"
  observationSubsectionNonempty := by decide
  printedObservation := "(3aR,7aS)-octahydro-1H-indole (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact claimTranscription
      "PDF page 76, P-93.5.4.1, fifth named example and adjacent fused-ring drawing"
      "(3aR,7aS)-octahydro-1H-indole (PIN)" (by decide) (by decide) claim

def fusedCIPEntry : P93CanonicalClauseObservationEntry where
  source := fusedCIPSource
  sourceAdmitted := fusedCIPSource_structurallyWellFormed
  clause := .fusedCyclophane .fusedBridgedCIP
  clauseListed := by decide
  observation := fusedCIPObservation
  transcription := fusedCIPTranscription

/-! ## P-93.5.4.2: cisoid/transoid and preferred relative-CIP replacement -/

/-- Full fourteen-carbon fused-ring graph of tetradecahydroanthracene. -/
def fusedRelationSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 14 carbonAtom
      interactions :=
        [bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 5, bond 5 0,
          bond 5 6, bond 6 7, bond 7 8, bond 8 9, bond 9 4,
          bond 9 10, bond 10 11, bond 11 12, bond 12 13, bond 13 8] }

theorem fusedRelationSource_structurallyWellFormed :
    fusedRelationSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    fusedRelationSource).mp (by decide)

def fusedRelationSystem : P93AuthorityFusedSystem where
  atoms := List.range 14
  fusionEdges := [{ first := 4, second := 5 }, { first := 8, second := 9 }]
  fusionLocants :=
    [(4, locant4a), (5, locant9a), (8, locant8a), (9, locant10a)]

theorem fusedRelationSystem_valid :
    fusedRelationSystem.MechanicallyValidFor fusedRelationSource := by
  simp [P93AuthorityFusedSystem.MechanicallyValidFor, fusedRelationSystem,
    P93AuthorityFusionEdge.ValidFor, P93AuthorityAtomsBounded,
    P93AuthorityBinaryBond, fusedRelationSource, bond,
    P93AuthorityBinaryInteractionKind, SemanticMolecule.atomCount, List.nodup_range,
    locant4a, locant8a, locant9a, locant10a]

def selectedNearestCandidate : P93CanonicalFusedNearestCandidate where
  candidate :=
    { firstFusionAtom := 4
      secondFusionAtom := 9
      firstFusionLocant := locant4a
      secondFusionLocant := locant10a
      graphDistance := 1
      lowerAtomLocant := locant4a }
  shortestPath := [4, 9]

theorem selectedNearestCandidate_valid :
    selectedNearestCandidate.ValidFor fusedRelationSource fusedRelationSystem := by
  unfold P93CanonicalFusedNearestCandidate.ValidFor selectedNearestCandidate
  refine ⟨by decide, ?_, ?_, by decide, by decide, ?_, rfl, ?_, ?_⟩
  · exact ⟨{ first := 4, second := 5 }, by simp [fusedRelationSystem], Or.inl rfl⟩
  · exact ⟨{ first := 8, second := 9 }, by simp [fusedRelationSystem], Or.inr rfl⟩
  · refine ⟨[], rfl, by decide, ?_, ?_, ?_⟩
    · simp [P93AuthorityAtomsBounded, fusedRelationSource,
        SemanticMolecule.atomCount]
    · simp [P93AuthorityConnectedPath, P93AuthorityBinaryBond,
        fusedRelationSource, bond, P93AuthorityBinaryInteractionKind]
    · simp [fusedRelationSystem]
  · simp [locant4a, locant10a,
      P93FusedLocant.min, P93FusedLocant.LE]
  · intro alternative path
    rcases path with ⟨middle, rfl, _nodup, _bounded, _connected, _carried⟩
    simp

def fusedRelationCanonicalObservation : P93CanonicalFusedRelationObservation where
  system := fusedRelationSystem
  candidates := [selectedNearestCandidate]
  selected := selectedNearestCandidate
  relation :=
    { firstJunction := .cis
      secondJunction := .cis
      nearestAtomsRelation := .cis
      legacyDescriptor := .cisoid
      preferredDescriptor := .relCIP
      citation := locant4a }

theorem fusedRelationCanonicalObservation_valid :
    fusedRelationCanonicalObservation.ValidFor fusedRelationSource := by
  refine ⟨fusedRelationSystem_valid, by decide, by decide, ?_, by simp
    [fusedRelationCanonicalObservation], ?_, ?_⟩
  · intro evidence evidenceMem
    have evidenceEq : evidence = selectedNearestCandidate := by
      simpa [fusedRelationCanonicalObservation] using evidenceMem
    subst evidence
    exact selectedNearestCandidate_valid
  · simp [fusedRelationCanonicalObservation, P93FusedIsUniqueSelectedNearestPair]
  · simp [fusedRelationCanonicalObservation, P93CanonicalFusedRelationSourceFact.Judged,
      P93CanonicalFusionLegacyDescriptor, P93FusedLocant.Valid, locant4a,
      selectedNearestCandidate,
      PreferredFusionDescription]

def fusedRelationPayload : P93FusedCyclophaneClausePayload .cisoidTransoid :=
  .fusedRelation fusedRelationCanonicalObservation

theorem fusedRelationPayload_valid :
    (P93ClausePayloadData.fusedCyclophane fusedRelationPayload).ValidFor
      fusedRelationSource := by
  constructor
  · intro claim claimMem
    have claimEq : claim = .fused (.relationObservation fusedRelationCanonicalObservation) := by
      simpa [P93ClausePayloadData.toClaims, fusedRelationPayload,
        P93FusedCyclophaneClausePayload.toClaims] using claimMem
    subst claim
    exact fusedRelationCanonicalObservation_valid
  · exact fusedRelationCanonicalObservation_valid

def fusedRelationObservation :
    P93ClauseObservation fusedRelationSource (.fusedCyclophane .cisoidTransoid) where
  payload := .fusedCyclophane fusedRelationPayload
  validFor := fusedRelationPayload_valid

def fusedRelationTranscription : P93CanonicalSourceTranscription fusedRelationSource
    (.fusedCyclophane .cisoidTransoid) fusedRelationObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 77
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.4.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.4.2"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "cis-cisoid-cis-tetradecahydroanthracene; rel-CIP is the preferred replacement"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact claimTranscription
      "PDF page 77, P-93.5.4.2, rule paragraph and first named example"
      "cis-cisoid-cis-tetradecahydroanthracene; rel-CIP is the preferred replacement"
      (by decide) (by decide) claim

def fusedRelationEntry : P93CanonicalClauseObservationEntry where
  source := fusedRelationSource
  sourceAdmitted := fusedRelationSource_structurallyWellFormed
  clause := .fusedCyclophane .cisoidTransoid
  clauseListed := by decide
  observation := fusedRelationObservation
  transcription := fusedRelationTranscription

/-! ## P-93.5.5.2: pseudoasymmetric cyclophane centers -/

def indexBlock (base count : Nat) : List Nat :=
  (List.range count).map (base + ·)

def benzeneNode (base : Nat) : Finset Nat :=
  (indexBlock base 6).toFinset

def benzeneBonds (base : Nat) : List SemanticInteraction :=
  [ bond base (base + 1) 2
  , bond (base + 1) (base + 2)
  , bond (base + 2) (base + 3) 2
  , bond (base + 3) (base + 4)
  , bond (base + 4) (base + 5) 2
  , bond (base + 5) base ]

def chainBonds (base : Nat) : List SemanticInteraction :=
  (List.range 8).map fun offset => bond (base + offset) (base + offset + 1)

def cyclophaneCenterMacrocycle : List Nat :=
  [0, 1, 2, 24, 6, 7, 8, 25, 12, 13, 14, 26, 18, 19, 20, 27]

/-- Full heavy-atom graph of the P-93.5.5.2 PIN example.  Atoms `0..23` are the four
1,3-linked benzene units, `24..27` are phane nodes 2/4/6/8, `28..63` are their four nonyl
chains, and `64..71` are the eight hydroxy oxygens.  The cyclophane parent carrier excludes the
acyclic substituent atoms but the authoritative molecule does not. -/
def cyclophaneCenterSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 64 carbonAtom ++ List.replicate 8 oxygenAtom
      interactions :=
        ([0, 6, 12, 18].flatMap benzeneBonds) ++
        [ bond 2 24, bond 24 6, bond 8 25, bond 25 12
        , bond 14 26, bond 26 18, bond 20 27, bond 27 0
        , bond 24 28, bond 25 37, bond 26 46, bond 27 55 ] ++
        ([28, 37, 46, 55].flatMap chainBonds) ++
        [ bond 3 64, bond 5 65, bond 9 66, bond 11 67
        , bond 15 68, bond 17 69, bond 21 70, bond 23 71 ] }

theorem cyclophaneCenterSource_structurallyWellFormed :
    cyclophaneCenterSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    cyclophaneCenterSource).mp (by decide)

def cyclophaneCenterSystem : P93AuthorityCyclophaneSystem where
  atomCarrier := List.range 28
  phaneNodes :=
    [ {0, 1, 2, 3, 4, 5}, {24}, {6, 7, 8, 9, 10, 11}, {25}
    , {12, 13, 14, 15, 16, 17}, {26}, {18, 19, 20, 21, 22, 23}, {27} ]
  rings :=
    [ [0, 1, 2, 3, 4, 5], [6, 7, 8, 9, 10, 11]
    , [12, 13, 14, 15, 16, 17], [18, 19, 20, 21, 22, 23]
    , cyclophaneCenterMacrocycle ]
  ringPhaneCycles := [(cyclophaneCenterMacrocycle, List.range 8)]

theorem cyclophaneCenterRing0_closed :
    P93AuthorityCyclophaneClosedRing cyclophaneCenterSource [0, 1, 2, 3, 4, 5] := by
  simp [P93AuthorityCyclophaneClosedRing, P93AuthorityAtomsBounded,
    P93AuthorityConnectedPath, P93AuthorityBinaryBond, cyclophaneCenterSource,
    benzeneBonds, chainBonds, bond, P93AuthorityBinaryInteractionKind,
    SemanticMolecule.atomCount]

theorem cyclophaneCenterRing1_closed :
    P93AuthorityCyclophaneClosedRing cyclophaneCenterSource [6, 7, 8, 9, 10, 11] := by
  simp [P93AuthorityCyclophaneClosedRing, P93AuthorityAtomsBounded,
    P93AuthorityConnectedPath, P93AuthorityBinaryBond, cyclophaneCenterSource,
    benzeneBonds, chainBonds, bond, P93AuthorityBinaryInteractionKind,
    SemanticMolecule.atomCount]

theorem cyclophaneCenterRing2_closed :
    P93AuthorityCyclophaneClosedRing cyclophaneCenterSource [12, 13, 14, 15, 16, 17] := by
  simp [P93AuthorityCyclophaneClosedRing, P93AuthorityAtomsBounded,
    P93AuthorityConnectedPath, P93AuthorityBinaryBond, cyclophaneCenterSource,
    benzeneBonds, chainBonds, bond, P93AuthorityBinaryInteractionKind,
    SemanticMolecule.atomCount]

theorem cyclophaneCenterRing3_closed :
    P93AuthorityCyclophaneClosedRing cyclophaneCenterSource [18, 19, 20, 21, 22, 23] := by
  simp [P93AuthorityCyclophaneClosedRing, P93AuthorityAtomsBounded,
    P93AuthorityConnectedPath, P93AuthorityBinaryBond, cyclophaneCenterSource,
    benzeneBonds, chainBonds, bond, P93AuthorityBinaryInteractionKind,
    SemanticMolecule.atomCount]

theorem cyclophaneCenterMacrocycle_closed :
    P93AuthorityCyclophaneClosedRing cyclophaneCenterSource
      cyclophaneCenterMacrocycle := by
  simp [P93AuthorityCyclophaneClosedRing, P93AuthorityAtomsBounded,
    P93AuthorityConnectedPath, P93AuthorityBinaryBond, cyclophaneCenterSource,
    cyclophaneCenterMacrocycle, benzeneBonds, chainBonds, bond,
    P93AuthorityBinaryInteractionKind, SemanticMolecule.atomCount]

theorem cyclophaneCenterSystem_valid :
    cyclophaneCenterSystem.MechanicallyValidFor cyclophaneCenterSource := by
  unfold P93AuthorityCyclophaneSystem.MechanicallyValidFor
  refine ⟨by decide, List.nodup_range, ?_, by decide, by decide, ?_, ?_, ?_,
    by decide, by decide, ?_, ?_, by decide, by decide, ?_⟩
  · simp [P93AuthorityAtomsBounded, cyclophaneCenterSystem,
      cyclophaneCenterSource, SemanticMolecule.atomCount]
    omega
  · intro node nodeMem
    change node ∈
      [{0, 1, 2, 3, 4, 5}, {24}, {6, 7, 8, 9, 10, 11}, {25},
        {12, 13, 14, 15, 16, 17}, {26}, {18, 19, 20, 21, 22, 23}, {27}] at nodeMem
    simp at nodeMem
    rcases nodeMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [cyclophaneCenterSystem]
  · intro atom atomMem
    change atom ∈ List.range 28 at atomMem
    simp at atomMem
    interval_cases atom <;> simp [cyclophaneCenterSystem]
  · intro first firstMem second secondMem distinct
    change first ∈
      [{0, 1, 2, 3, 4, 5}, {24}, {6, 7, 8, 9, 10, 11}, {25},
        {12, 13, 14, 15, 16, 17}, {26}, {18, 19, 20, 21, 22, 23}, {27}] at firstMem
    change second ∈
      [{0, 1, 2, 3, 4, 5}, {24}, {6, 7, 8, 9, 10, 11}, {25},
        {12, 13, 14, 15, 16, 17}, {26}, {18, 19, 20, 21, 22, 23}, {27}] at secondMem
    simp at firstMem secondMem
    rcases firstMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases secondMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      try simp at distinct <;> decide
  · intro ring ringMem
    change ring ∈
      [[0, 1, 2, 3, 4, 5], [6, 7, 8, 9, 10, 11],
        [12, 13, 14, 15, 16, 17], [18, 19, 20, 21, 22, 23],
        cyclophaneCenterMacrocycle] at ringMem
    simp at ringMem
    rcases ringMem with rfl | rfl | rfl | rfl | rfl
    · exact ⟨cyclophaneCenterRing0_closed, by simp [cyclophaneCenterSystem]⟩
    · exact ⟨cyclophaneCenterRing1_closed, by simp [cyclophaneCenterSystem]⟩
    · exact ⟨cyclophaneCenterRing2_closed, by simp [cyclophaneCenterSystem]⟩
    · exact ⟨cyclophaneCenterRing3_closed, by simp [cyclophaneCenterSystem]⟩
    · exact ⟨cyclophaneCenterMacrocycle_closed,
        by simp [cyclophaneCenterSystem, cyclophaneCenterMacrocycle]⟩
  · intro atom atomMem
    change atom ∈ List.range 28 at atomMem
    simp at atomMem
    by_cases firstRing : atom < 6
    · refine ⟨[0, 1, 2, 3, 4, 5], by decide, ?_⟩
      simp
      omega
    by_cases secondRing : atom < 12
    · refine ⟨[6, 7, 8, 9, 10, 11], by decide, ?_⟩
      simp
      omega
    by_cases thirdRing : atom < 18
    · refine ⟨[12, 13, 14, 15, 16, 17], by decide, ?_⟩
      simp
      omega
    by_cases fourthRing : atom < 24
    · refine ⟨[18, 19, 20, 21, 22, 23], by decide, ?_⟩
      simp
      omega
    refine ⟨cyclophaneCenterMacrocycle, by decide, ?_⟩
    interval_cases atom <;> simp [cyclophaneCenterMacrocycle]
  · intro mapping mappingMem
    change mapping ∈ [(cyclophaneCenterMacrocycle, List.range 8)] at mappingMem
    simp at mappingMem
    subst mapping
    refine ⟨by decide, by decide, List.nodup_range, ?_⟩
    intro nodeIndex nodeIndexMem
    simp at nodeIndexMem
    interval_cases nodeIndex
    · exact ⟨{0, 1, 2, 3, 4, 5}, rfl, 0, by decide, by decide⟩
    · exact ⟨{24}, rfl, 24, by decide, by decide⟩
    · exact ⟨{6, 7, 8, 9, 10, 11}, rfl, 6, by decide, by decide⟩
    · exact ⟨{25}, rfl, 25, by decide, by decide⟩
    · exact ⟨{12, 13, 14, 15, 16, 17}, rfl, 12, by decide, by decide⟩
    · exact ⟨{26}, rfl, 26, by decide, by decide⟩
    · exact ⟨{18, 19, 20, 21, 22, 23}, rfl, 18, by decide, by decide⟩
    · exact ⟨{27}, rfl, 27, by decide, by decide⟩

theorem cyclophaneCenter_envelope :
    P93CanonicalPhysicalUnitEnvelope cyclophaneCenterSource (.atomCenter 24) := by
  refine ⟨by decide, [2, 6, 28], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, cyclophaneCenterSource,
      SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, cyclophaneCenterSource, benzeneBonds, chainBonds,
        bond, P93AuthorityBinaryInteractionKind]

def cyclophaneCenterPayload : P93FusedCyclophaneClausePayload .cyclophaneCenters :=
  .cyclophaneCenters cyclophaneCenterSystem (.atomCenter 24) (citation 2)
    (.cip .preferredIUPACName .pseudoasymmetricCenter .r)

theorem cyclophaneCenterPayload_valid :
    (P93ClausePayloadData.fusedCyclophane cyclophaneCenterPayload).ValidFor
      cyclophaneCenterSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, cyclophaneCenterPayload,
      P93FusedCyclophaneClausePayload.toClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl
    · exact cyclophaneCenterSystem_valid
    · exact ⟨cyclophaneCenterSystem_valid, cyclophaneCenter_envelope,
        by simp [P93CyclophaneUnitSupported, cyclophaneCenterSystem]⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid],
        cyclophaneCenter_envelope⟩
    · exact ⟨cyclophaneCenterSystem_valid, by decide, by trivial⟩
  · exact ⟨cyclophaneCenterSystem_valid,
      by simp [P93CyclophaneUnitSupported, cyclophaneCenterSystem], ⟨24, rfl⟩, by trivial,
      by trivial, by trivial, by simp [citation, P93AuthorityCitationToken.Valid]⟩

def cyclophaneCenterObservation : P93ClauseObservation cyclophaneCenterSource
    (.fusedCyclophane .cyclophaneCenters) where
  payload := .fusedCyclophane cyclophaneCenterPayload
  validFor := cyclophaneCenterPayload_valid

def cyclophaneCenterTranscription : P93CanonicalSourceTranscription cyclophaneCenterSource
    (.fusedCyclophane .cyclophaneCenters) cyclophaneCenterObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 78
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.5.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.5.2"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(2r,4r,6r,8r)-2,4,6,8-tetranonyl-1,3,5,7(1,3)-tetrabenzenacyclooctaphane-1⁴,1⁶,3⁴,3⁶,5⁴,5⁶,7⁴,7⁶-octol (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact claimTranscription
      "PDF page 78, P-93.5.5.2, sole named example and adjacent structure"
      "The PIN prints pseudoasymmetric centers 2r,4r,6r,8r on the complete tetrabenzenacyclooctaphane example."
      (by decide) (by decide) claim

def cyclophaneCenterEntry : P93CanonicalClauseObservationEntry where
  source := cyclophaneCenterSource
  sourceAdmitted := cyclophaneCenterSource_structurallyWellFormed
  clause := .fusedCyclophane .cyclophaneCenters
  clauseListed := by decide
  observation := cyclophaneCenterObservation
  transcription := cyclophaneCenterTranscription

/-! ## P-93.5.5.3: six-node cyclophane double-bond omission -/

def cyclophaneDoubleMacrocycle : List Nat :=
  [0, 1, 2, 3, 12, 13, 6, 7, 8, 9, 14, 15]

/-- Full heavy-atom graph of `1,4(1,4)-dibenzenacyclohexaphane-2,5-diene`: two para-linked
benzene phane nodes and the four carbon nodes carrying the two printed double bonds. -/
def cyclophaneDoubleSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 16 carbonAtom
      interactions :=
        benzeneBonds 0 ++ benzeneBonds 6 ++
        [bond 3 12, bond 12 13 2, bond 13 6,
          bond 9 14, bond 14 15 2, bond 15 0] }

theorem cyclophaneDoubleSource_structurallyWellFormed :
    cyclophaneDoubleSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    cyclophaneDoubleSource).mp (by decide)

def cyclophaneDoubleSystem : P93AuthorityCyclophaneSystem where
  atomCarrier := List.range 16
  phaneNodes :=
    [{0, 1, 2, 3, 4, 5}, {12}, {13}, {6, 7, 8, 9, 10, 11}, {14}, {15}]
  rings :=
    [[0, 1, 2, 3, 4, 5], [6, 7, 8, 9, 10, 11], cyclophaneDoubleMacrocycle]
  ringPhaneCycles := [(cyclophaneDoubleMacrocycle, List.range 6)]

theorem cyclophaneDoubleSystem_valid :
    cyclophaneDoubleSystem.MechanicallyValidFor cyclophaneDoubleSource := by
  unfold P93AuthorityCyclophaneSystem.MechanicallyValidFor
  refine ⟨by decide, List.nodup_range, ?_, by decide, by decide, ?_, ?_, ?_,
    by decide, by decide, ?_, ?_, by decide, by decide, ?_⟩
  · simp [P93AuthorityAtomsBounded, cyclophaneDoubleSystem,
      cyclophaneDoubleSource, SemanticMolecule.atomCount]
  · intro node nodeMem
    change node ∈
      [{0, 1, 2, 3, 4, 5}, {12}, {13}, {6, 7, 8, 9, 10, 11}, {14}, {15}] at nodeMem
    simp at nodeMem
    rcases nodeMem with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [cyclophaneDoubleSystem]
  · intro atom atomMem
    change atom ∈ List.range 16 at atomMem
    simp at atomMem
    interval_cases atom <;>
      simp [cyclophaneDoubleSystem, cyclophaneDoubleMacrocycle]
  · intro first firstMem second secondMem distinct
    change first ∈
      [{0, 1, 2, 3, 4, 5}, {12}, {13}, {6, 7, 8, 9, 10, 11}, {14}, {15}] at firstMem
    change second ∈
      [{0, 1, 2, 3, 4, 5}, {12}, {13}, {6, 7, 8, 9, 10, 11}, {14}, {15}] at secondMem
    simp at firstMem secondMem
    rcases firstMem with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases secondMem with rfl | rfl | rfl | rfl | rfl | rfl <;>
      try simp at distinct <;> decide
  · set_option maxHeartbeats 600000 in
    intro ring ringMem
    change ring ∈
      [[0, 1, 2, 3, 4, 5], [6, 7, 8, 9, 10, 11], cyclophaneDoubleMacrocycle] at ringMem
    simp at ringMem
    rcases ringMem with rfl | rfl | rfl <;>
      simp [P93AuthorityCyclophaneClosedRing, P93AuthorityAtomsBounded,
        P93AuthorityConnectedPath, P93AuthorityBinaryBond, cyclophaneDoubleSource,
        cyclophaneDoubleMacrocycle, benzeneBonds, bond,
        P93AuthorityBinaryInteractionKind, SemanticMolecule.atomCount,
        cyclophaneDoubleSystem]
  · intro atom atomMem
    change atom ∈ List.range 16 at atomMem
    simp at atomMem
    by_cases firstRing : atom < 6
    · refine ⟨[0, 1, 2, 3, 4, 5], by decide, ?_⟩
      simp
      omega
    by_cases secondRing : atom < 12
    · refine ⟨[6, 7, 8, 9, 10, 11], by decide, ?_⟩
      simp
      omega
    refine ⟨cyclophaneDoubleMacrocycle, by decide, ?_⟩
    interval_cases atom <;> simp [cyclophaneDoubleMacrocycle]
  · intro mapping mappingMem
    change mapping ∈ [(cyclophaneDoubleMacrocycle, List.range 6)] at mappingMem
    simp at mappingMem
    subst mapping
    refine ⟨by decide, by decide, List.nodup_range, ?_⟩
    intro nodeIndex nodeIndexMem
    simp at nodeIndexMem
    interval_cases nodeIndex
    · exact ⟨{0, 1, 2, 3, 4, 5}, rfl, 0, by decide, by decide⟩
    · exact ⟨{12}, rfl, 12, by decide, by decide⟩
    · exact ⟨{13}, rfl, 13, by decide, by decide⟩
    · exact ⟨{6, 7, 8, 9, 10, 11}, rfl, 6, by decide, by decide⟩
    · exact ⟨{14}, rfl, 14, by decide, by decide⟩
    · exact ⟨{15}, rfl, 15, by decide, by decide⟩

theorem cyclophaneDoubleBond_envelope :
    P93CanonicalPhysicalUnitEnvelope cyclophaneDoubleSource (.bond 12 13) := by
  exact ⟨by decide, by decide, by decide, by
    simp [P93AuthorityBinaryBond, cyclophaneDoubleSource, benzeneBonds,
      bond, P93AuthorityBinaryInteractionKind]⟩

def cyclophaneDoublePayload :
    P93FusedCyclophaneClausePayload .cyclophaneDoubleBonds :=
  .cyclophaneDoubleBonds cyclophaneDoubleSystem (.bond 12 13) (citation 2)
    cyclophaneDoubleMacrocycle (List.range 6) .together
    { firstCarbonHasHydrogen := true, secondCarbonHasHydrogen := true }
    .preferredIUPACName none

theorem cyclophaneDoublePayload_valid :
    (P93ClausePayloadData.fusedCyclophane cyclophaneDoublePayload).ValidFor
      cyclophaneDoubleSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, cyclophaneDoublePayload,
      P93FusedCyclophaneClausePayload.toClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cyclophaneDoubleSystem_valid
    · exact ⟨cyclophaneDoubleSystem_valid, cyclophaneDoubleBond_envelope,
        by simp [P93CyclophaneUnitSupported, cyclophaneDoubleSystem]⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid],
        cyclophaneDoubleBond_envelope⟩
    · exact ⟨cyclophaneDoubleSystem_valid, cyclophaneDoubleBond_envelope,
        by decide, by decide⟩
    · exact cyclophaneDoubleBond_envelope
    · exact cyclophaneDoubleBond_envelope
    · exact ⟨cyclophaneDoubleSystem_valid, cyclophaneDoubleBond_envelope⟩
  · refine ⟨cyclophaneDoubleSystem_valid, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [P93CyclophaneUnitSupported, cyclophaneDoubleSystem]
    · exact ⟨12, 13, rfl, by decide, by decide⟩
    · decide
    · decide
    · trivial
    · intro impossible
      simp at impossible
    · simp [CyclophaneDoubleBondDescriptorRequired, cyclophaneDoubleSystem]
    · simp [P93CyclophaneDoubleBondExpected,
        CyclophaneDoubleBondDescriptorRequired, cyclophaneDoubleSystem]
    · simp [citation, P93AuthorityCitationToken.Valid]

def cyclophaneDoubleObservation : P93ClauseObservation cyclophaneDoubleSource
    (.fusedCyclophane .cyclophaneDoubleBonds) where
  payload := .fusedCyclophane cyclophaneDoublePayload
  validFor := cyclophaneDoublePayload_valid

def cyclophaneDoubleTranscription : P93CanonicalSourceTranscription cyclophaneDoubleSource
    (.fusedCyclophane .cyclophaneDoubleBonds) cyclophaneDoubleObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 79
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.5.3"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.5.3"
  observationSubsectionNonempty := by decide
  printedObservation := "1,4(1,4)-dibenzenacyclohexaphane-2,5-diene (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact claimTranscription
      "PDF page 79, P-93.5.5.3, first named example and adjacent six-node structure"
      "The six-node PIN is printed without E/Z descriptors; its two side double bonds are shown in the structure."
      (by decide) (by decide) claim

def cyclophaneDoubleEntry : P93CanonicalClauseObservationEntry where
  source := cyclophaneDoubleSource
  sourceAdmitted := cyclophaneDoubleSource_structurallyWellFormed
  clause := .fusedCyclophane .cyclophaneDoubleBonds
  clauseListed := by decide
  observation := cyclophaneDoubleObservation
  transcription := cyclophaneDoubleTranscription

/-! ## P-93.5.5.1: printed cyclophane plane and separate rational reconstruction -/

def planePoint (x y z : Int) : CartesianPoint3 where
  x := x
  y := y
  z := z

def planeZeroPoint : CartesianPoint3 := planePoint 0 0 0

/-- Exact rational reconstruction of the first page-78 drawing.  These coordinates are an
executable witness only; the Blue Book prints the molecular diagram and `M`/`Sₚ` descriptors, not
this Cartesian realization. -/
def cyclophanePlaneSpatial : SpatialConfiguration where
  positions :=
    [ planePoint 0 0 0, planePoint 1 0 0, planePoint 0 2 0,
      planePoint (-2) 0 0, planePoint 0 (-2) 0, planePoint 0 1 0,
      planeZeroPoint, planeZeroPoint, planeZeroPoint, planeZeroPoint,
      planeZeroPoint, planeZeroPoint, planeZeroPoint, planeZeroPoint,
      planePoint 0 0 (-1), planePoint (-1) 0 0, planeZeroPoint,
      planeZeroPoint, planeZeroPoint ]

/-- Full heavy-atom graph of the printed
`1,4(1,4)-dibenzenacyclohexaphane-1²-carboxylic acid`: two para-linked benzene phane nodes,
four methylene phane nodes, and the carboxylic-acid carbon and oxygens. -/
def cyclophanePlaneSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 17 carbonAtom ++ [oxygenAtom, oxygenAtom]
      interactions :=
        benzeneBonds 0 ++ benzeneBonds 6 ++
        [bond 3 12, bond 12 13, bond 13 6,
          bond 9 14, bond 14 15, bond 15 0,
          bond 1 16, bond 16 17 2, bond 16 18] }
  spatial? := some cyclophanePlaneSpatial

theorem cyclophanePlaneSource_structurallyWellFormed :
    cyclophanePlaneSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    cyclophanePlaneSource).mp (by decide)

def cyclophanePlaneSystem : P93AuthorityCyclophaneSystem := cyclophaneDoubleSystem

theorem cyclophanePlaneSystem_valid :
    cyclophanePlaneSystem.MechanicallyValidFor cyclophanePlaneSource := by
  unfold P93AuthorityCyclophaneSystem.MechanicallyValidFor
  refine ⟨by decide, List.nodup_range, ?_, by decide, by decide, ?_, ?_, ?_,
    by decide, by decide, ?_, ?_, by decide, by decide, ?_⟩
  · simp [P93AuthorityAtomsBounded, cyclophanePlaneSystem, cyclophaneDoubleSystem,
      cyclophanePlaneSource, SemanticMolecule.atomCount]
    omega
  · intro node nodeMem
    change node ∈
      [{0, 1, 2, 3, 4, 5}, {12}, {13}, {6, 7, 8, 9, 10, 11}, {14}, {15}] at nodeMem
    simp at nodeMem
    rcases nodeMem with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [cyclophanePlaneSystem, cyclophaneDoubleSystem]
  · intro atom atomMem
    change atom ∈ List.range 16 at atomMem
    simp at atomMem
    interval_cases atom <;>
      simp [cyclophanePlaneSystem, cyclophaneDoubleSystem, cyclophaneDoubleMacrocycle]
  · intro first firstMem second secondMem distinct
    change first ∈
      [{0, 1, 2, 3, 4, 5}, {12}, {13}, {6, 7, 8, 9, 10, 11}, {14}, {15}] at firstMem
    change second ∈
      [{0, 1, 2, 3, 4, 5}, {12}, {13}, {6, 7, 8, 9, 10, 11}, {14}, {15}] at secondMem
    simp at firstMem secondMem
    rcases firstMem with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases secondMem with rfl | rfl | rfl | rfl | rfl | rfl <;>
      try simp at distinct <;> decide
  · set_option maxHeartbeats 600000 in
    intro ring ringMem
    change ring ∈
      [[0, 1, 2, 3, 4, 5], [6, 7, 8, 9, 10, 11], cyclophaneDoubleMacrocycle] at ringMem
    simp at ringMem
    rcases ringMem with rfl | rfl | rfl <;>
      simp [P93AuthorityCyclophaneClosedRing, P93AuthorityAtomsBounded,
        P93AuthorityConnectedPath, P93AuthorityBinaryBond, cyclophanePlaneSource,
        cyclophaneDoubleMacrocycle, benzeneBonds, bond,
        P93AuthorityBinaryInteractionKind, SemanticMolecule.atomCount,
        cyclophanePlaneSystem, cyclophaneDoubleSystem]
  · intro atom atomMem
    change atom ∈ List.range 16 at atomMem
    simp at atomMem
    by_cases firstRing : atom < 6
    · refine ⟨[0, 1, 2, 3, 4, 5], by decide, ?_⟩
      simp
      omega
    by_cases secondRing : atom < 12
    · refine ⟨[6, 7, 8, 9, 10, 11], by decide, ?_⟩
      simp
      omega
    refine ⟨cyclophaneDoubleMacrocycle, by decide, ?_⟩
    interval_cases atom <;> simp [cyclophaneDoubleMacrocycle]
  · intro mapping mappingMem
    change mapping ∈ [(cyclophaneDoubleMacrocycle, List.range 6)] at mappingMem
    simp at mappingMem
    subst mapping
    refine ⟨by decide, by decide, List.nodup_range, ?_⟩
    intro nodeIndex nodeIndexMem
    simp at nodeIndexMem
    interval_cases nodeIndex
    · exact ⟨{0, 1, 2, 3, 4, 5}, rfl, 0, by decide, by decide⟩
    · exact ⟨{12}, rfl, 12, by decide, by decide⟩
    · exact ⟨{13}, rfl, 13, by decide, by decide⟩
    · exact ⟨{6, 7, 8, 9, 10, 11}, rfl, 6, by decide, by decide⟩
    · exact ⟨{14}, rfl, 14, by decide, by decide⟩
    · exact ⟨{15}, rfl, 15, by decide, by decide⟩

def cyclophanePlaneMembers : Finset Nat := [0, 1, 2, 3, 4, 5, 15].toFinset

def cyclophanePlaneFrame : P93AuthorityPlaneFrame where
  record :=
    { planeAtoms := [0, 1, 5, 2, 3, 4, 15]
      pilotAtom := 0
      firstReference := 1
      secondReference := 5
      inPlaneBondAtom := 15
      outOfPlaneAtom := 14
      torsionRestricted := true
      planeCannotBeSymmetryPlane := true }

def cyclophanePlaneReference : CyclophanePlaneReference where
  chosenLigandIsCIPHighest := True
  locantIsCompositeRingLocantViewedFromPilotAtom := True

/-- Exact atom-to-diagram role map audited against P-92.1.2.1.3 and the first page-78 inset.
Atom `0` is the derived-tetrahedron center `x = C-1¹`; atoms `1` and `5` are the two adjacent
amplificant references `a,b` (the carboxylic acid at atom `1` makes that direction CIP-high);
atom `15` is bridge atom `y`, directly bonded to `x`; and atom `14` is the following bridge atom
`z`.  The page-78 viewing pilot is phane node 2, represented here by atom `15 = y`, not atom `0`.
The executable carrier includes `y` in `planeAtoms` because `P93AuthorityPlaneFrame.ValidFor`
records the in-plane bond atom there.  This does not relabel `y` as one of the printed in-plane
references: those are exactly `a,b = 1,5`. -/
def cyclophanePlanePrinted : P93CanonicalCyclophanePrintedPlaneObservation where
  molecule := cyclophanePlaneSource.molecule
  system := cyclophanePlaneSystem
  members := cyclophanePlaneMembers
  citation := citation 1
  reference := cyclophanePlaneReference
  high := 1
  low := 5
  pilotAtom := 0
  inPlaneBondAtom := 15
  outOfPlaneAtom := 14
  context := .preferredIUPACName
  descriptor := .M
  torsionRestricted := true
  planeCannotBeSymmetryPlane := true

def cyclophanePlaneExecutable : P93CanonicalCyclophanePlaneExecutableWitness where
  frame := cyclophanePlaneFrame

theorem cyclophanePlaneFrame_valid :
    cyclophanePlaneFrame.ValidFor cyclophanePlaneSource cyclophanePlaneMembers := by
  unfold P93AuthorityPlaneFrame.ValidFor
  refine ⟨by decide, by decide, by decide, ?_, by decide, by decide, by decide,
    by decide, by decide, by decide, ?_, ?_, ?_, ?_, rfl, rfl, ?_⟩
  · simp [P93AuthorityAtomsBounded, cyclophanePlaneFrame, cyclophanePlaneSource,
      SemanticMolecule.atomCount]
  · simp [cyclophanePlaneFrame, P93AuthorityBinaryBond, cyclophanePlaneSource,
      benzeneBonds, bond, P93AuthorityBinaryInteractionKind]
  · simp [cyclophanePlaneFrame, P93AuthorityBinaryBond, cyclophanePlaneSource,
      benzeneBonds, bond, P93AuthorityBinaryInteractionKind]
  · simp [cyclophanePlaneFrame, P93AuthorityBinaryBond, cyclophanePlaneSource,
      benzeneBonds, bond, P93AuthorityBinaryInteractionKind]
  · simp [cyclophanePlaneFrame, P93AuthorityBinaryBond, cyclophanePlaneSource,
      benzeneBonds, bond, P93AuthorityBinaryInteractionKind]
  · unfold P93AuthorityPlaneSpatiallyResolved
    refine ⟨by decide, by decide, cyclophanePlaneSpatial,
      [planePoint 0 0 0, planePoint 1 0 0, planePoint 0 1 0,
        planePoint 0 2 0, planePoint (-2) 0 0, planePoint 0 (-2) 0,
        planePoint (-1) 0 0], planePoint 0 0 (-1), rfl, ?_, ?_, ?_⟩
    · simp [BlueBookP94.CoordinateRing.SpatialPointsAt,
        BlueBookP94.CoordinateRing.SpatialPointAt, cyclophanePlaneSpatial,
        cyclophanePlaneFrame, planePoint, planeZeroPoint]
    · simp [BlueBookP94.CoordinateRing.SpatialPointAt, cyclophanePlaneSpatial,
        cyclophanePlaneFrame, planePoint, planeZeroPoint]
    · simp [P93AuthorityPlanePointsResolved,
        BlueBookP94.CoordinateRing.ExactPlane.Nondegenerate,
        BlueBookP94.CoordinateRing.ExactPlane.PointHasSide,
        BlueBookP94.CoordinateRing.ExactPlane.normal,
        BlueBookP94.CoordinateRing.ExactPlane.signedMeasure,
        CartesianPoint3.orientedVolume, CartesianPoint3.displacement,
        RationalVector3.cross, planePoint]

def cyclophanePlanePayload : P93FusedCyclophaneClausePayload .cyclophanePlanes :=
  .cyclophanePlanes cyclophanePlanePrinted cyclophanePlaneExecutable

theorem cyclophanePlaneCarrierEnvelope :
    P93CanonicalPrintedPlaneCarrierEnvelope cyclophanePlaneSource
      cyclophanePlaneMembers 0 1 5 15 14 := by
  simp [P93CanonicalPrintedPlaneCarrierEnvelope, cyclophanePlaneMembers,
    P93AuthorityAtomsBounded, cyclophanePlaneSource, SemanticMolecule.atomCount,
    P93AuthorityBinaryBond, benzeneBonds, bond, P93AuthorityBinaryInteractionKind]

theorem cyclophanePlanePrinted_valid :
    cyclophanePlanePrinted.ValidFor cyclophanePlaneSource := by
  refine ⟨rfl, cyclophanePlaneSystem_valid, cyclophanePlaneCarrierEnvelope, ?_, rfl,
    rfl, by simp [cyclophanePlanePrinted, cyclophanePlaneReference,
      ValidCyclophanePlaneReference], by simp [cyclophanePlanePrinted,
      PreferredCyclophanePlaneDescriptor], by simp [cyclophanePlanePrinted, citation,
      P93AuthorityCitationToken.Valid]⟩
  simp [cyclophanePlanePrinted, P93CyclophaneUnitSupported, cyclophanePlaneSystem,
    cyclophaneDoubleSystem, cyclophanePlaneMembers]

theorem cyclophanePlaneExecutable_valid :
    cyclophanePlaneExecutable.ValidFor cyclophanePlaneSource cyclophanePlanePrinted := by
  refine ⟨by decide, rfl, Or.inl ⟨rfl, rfl⟩, rfl, rfl, rfl, rfl,
    cyclophanePlaneFrame_valid, ?_⟩
  refine ⟨cyclophanePlaneSpatial, planePoint 1 0 0, planePoint 0 1 0,
    planePoint (-1) 0 0, planePoint 0 0 (-1), .Sp, rfl, ?_, ?_, ?_, ?_, ?_, rfl⟩
  all_goals
    simp [cyclophanePlanePrinted, cyclophanePlaneSpatial,
      BlueBookP94.CoordinateRing.SpatialPointAt,
      BlueBookP92.PlanarDerivedTetrahedron.RationalDescriptor,
      CartesianPoint3.orientedVolume, planePoint, planeZeroPoint]

theorem cyclophanePlanePayload_valid :
    (P93ClausePayloadData.fusedCyclophane cyclophanePlanePayload).ValidFor
      cyclophanePlaneSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, cyclophanePlanePayload,
      P93FusedCyclophaneClausePayload.toClaims, cyclophanePlanePrinted] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl | rfl | rfl
    · exact cyclophanePlaneSystem_valid
    · exact ⟨cyclophanePlaneSystem_valid,
        ⟨0, 1, 5, 15, 14, cyclophanePlaneCarrierEnvelope⟩,
        cyclophanePlanePrinted_valid.2.2.2.1⟩
    · exact ⟨cyclophanePlanePrinted_valid.2.2.2.2.2.2.2.2,
        ⟨0, 1, 5, 15, 14, cyclophanePlaneCarrierEnvelope⟩⟩
    all_goals
      exact ⟨cyclophanePlaneSystem_valid,
        ⟨0, 1, 5, 15, 14, cyclophanePlaneCarrierEnvelope⟩,
        cyclophanePlanePrinted_valid.2.2.2.1⟩
  · exact ⟨cyclophanePlanePrinted_valid, cyclophanePlaneExecutable_valid⟩

def cyclophanePlaneObservation : P93ClauseObservation cyclophanePlaneSource
    (.fusedCyclophane .cyclophanePlanes) where
  payload := .fusedCyclophane cyclophanePlanePayload
  validFor := cyclophanePlanePayload_valid

def cyclophanePlaneTranscription : P93CanonicalSourceTranscription cyclophanePlaneSource
    (.fusedCyclophane .cyclophanePlanes) cyclophanePlaneObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 78
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.5.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.5.1"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(1¹M)-1,4(1,4)-dibenzenacyclohexaphane-1²-carboxylic acid (PIN); general form (1¹Sₚ)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact claimTranscription
      "PDF page 78, P-93.5.5.1, first named example, pilot-view inset, and adjacent structure"
      "The drawing and names print the 1¹M preferred assignment and 1¹Sₚ general assignment; the exact rational coordinates are a separate executable reconstruction, not printed source data."
      (by decide) (by decide) claim

def cyclophanePlaneEntry : P93CanonicalClauseObservationEntry where
  source := cyclophanePlaneSource
  sourceAdmitted := cyclophanePlaneSource_structurallyWellFormed
  clause := .fusedCyclophane .cyclophanePlanes
  clauseListed := by decide
  observation := cyclophanePlaneObservation
  transcription := cyclophanePlaneTranscription

/-! ## Exact coordinate-free block surface -/

def entries : List P93CanonicalClauseObservationEntry :=
  [fusedCIPEntry, fusedRelationEntry, cyclophanePlaneEntry,
    cyclophaneCenterEntry, cyclophaneDoubleEntry]

def coveredClauses : List P93Clause := entries.map (·.clause)

@[simp] theorem entries_length : entries.length = 5 := rfl

@[simp] theorem entries_clause_exact : entries.map (·.clause) =
    [ .fusedCyclophane .fusedBridgedCIP
    , .fusedCyclophane .cisoidTransoid
    , .fusedCyclophane .cyclophanePlanes
    , .fusedCyclophane .cyclophaneCenters
    , .fusedCyclophane .cyclophaneDoubleBonds ] := rfl

theorem entry_sources_nodup : (entries.map fun entry => entry.source).Nodup := by
  decide

theorem entries_source_unique :
    ∀ first ∈ entries, ∀ second ∈ entries,
      first.source = second.source → first = second := by
  exact List.inj_on_of_nodup_map entry_sources_nodup

end P93CanonicalProgramFusedCyclophane
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFusedCyclophane.fusedCIPPayload_valid
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFusedCyclophane.fusedRelationPayload_valid
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFusedCyclophane.cyclophanePlanePayload_valid
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFusedCyclophane.cyclophaneCenterPayload_valid
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramFusedCyclophane.cyclophaneDoublePayload_valid
