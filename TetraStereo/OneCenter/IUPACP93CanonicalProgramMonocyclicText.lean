import TetraStereo.OneCenter.IUPACP93CanonicalSourceClaims

set_option autoImplicit false

/-!
# Seven audited monocyclic P-93 source entries

This module transcribes seven examples from the frozen Blue Book P-9 artifact, PDF pages 57--65.
Every source is the complete heavy-atom constitution shown by the adjacent figure.  Wedge-derived
ring-side facts are recorded as `textAndFigure`; no rational coordinates or unprinted spatial
model are attributed to the source.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Acyclic
open BlueBookP93.Cyclic
open IUPACNormativeProvision

namespace P93CanonicalProgramMonocyclicText

def carbon : PeriodicElement where
  atomicNumber := 6
  positive := by decide
  atMost118 := by decide

def nitrogen : PeriodicElement where
  atomicNumber := 7
  positive := by decide
  atMost118 := by decide

def oxygen : PeriodicElement where
  atomicNumber := 8
  positive := by decide
  atMost118 := by decide

def chlorine : PeriodicElement where
  atomicNumber := 17
  positive := by decide
  atMost118 := by decide

def bromine : PeriodicElement where
  atomicNumber := 35
  positive := by decide
  atMost118 := by decide

def carbonAtom : SemanticAtom where element := carbon
def nitrogenAtom : SemanticAtom where element := nitrogen
def oxygenAtom : SemanticAtom where element := oxygen
def chlorineAtom : SemanticAtom where element := chlorine
def bromineAtom : SemanticAtom where element := bromine

def bond (left right : Nat) (order : Nat := 1) : SemanticInteraction where
  participants := [left, right]
  kind := .covalent order

def citation (value : Nat) : P93AuthorityCitationToken where
  components := [{ value := value, primes := 0 }]

def meanPlaneObservation : RingPlaneObservation where
  usesMeanPlane := True
  firstSubstitutedPositionNotReentrant := True
  secondSubstitutedPositionNotReentrant := True

theorem meanPlaneObservation_applicable : CisTransPlaneApplicable meanPlaneObservation := by
  trivial

/-! ## P-93.5 general cyclic configuration -/

/-- Full heavy-atom graph of `(1R,2R)-1,2,4-trimethylcyclopentane`: ring atoms `0..4`,
with methyl carbons `5`, `6`, and `7` at positions 1, 2, and 4. -/
def configurationSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 8 carbonAtom
      interactions :=
        [ bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 0
        , bond 0 5, bond 1 6, bond 3 7 ] }

def configurationRing : List Nat := [0, 1, 2, 3, 4]

theorem configurationSource_wellFormed : configurationSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    configurationSource).mp (by decide)

theorem configurationRing_closed :
    P93AuthorityClosedCycle configurationSource configurationRing := by
  simp [P93AuthorityClosedCycle, configurationRing, configurationSource, bond,
    P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    P93AuthorityBinaryInteractionKind, P93AuthorityAtomsBounded,
    SemanticMolecule.atomCount]

theorem configurationCenter_envelope :
    P93CanonicalPhysicalUnitEnvelope configurationSource (.atomCenter 0) := by
  refine ⟨by decide, [1, 4, 5], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, configurationSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, configurationSource, bond,
        P93AuthorityBinaryInteractionKind]

def configurationPayload : P93MonocyclicClausePayload .cyclicConfigurations :=
  .configurations
    { ring := configurationRing, unit := .atomCenter 0, citation := citation 1 }
    (.acyclic .R) .absolute .CIP

theorem configurationPayload_valid :
    (P93ClausePayloadData.monocyclic configurationPayload).ValidFor configurationSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, configurationPayload,
      P93MonocyclicClausePayload.toClaims, P93MonocyclicCitedPayload.baseClaims,
      P93MonocyclicPhysicalPayload.baseClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl | rfl
    · exact configurationRing_closed
    · exact ⟨configurationRing_closed, configurationCenter_envelope⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid],
        configurationCenter_envelope⟩
    · exact configurationCenter_envelope
    · exact configurationCenter_envelope
  · exact ⟨configurationRing_closed,
      by simp [citation, P93AuthorityCitationToken.Valid], rfl⟩

/-! ## P-93.5.1.1.1 absolute center -/

/-- Full heavy-atom graph of
`(1R,2S,5R)-5-methyl-2-(propan-2-yl)cyclohexan-1-ol`. -/
def absoluteSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 11 carbonAtom |>.set 6 oxygenAtom
      interactions :=
        [ bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 5, bond 5 0
        , bond 0 6, bond 4 7, bond 1 8, bond 8 9, bond 8 10 ] }

def absoluteRing : List Nat := [0, 1, 2, 3, 4, 5]

theorem absoluteSource_wellFormed : absoluteSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    absoluteSource).mp (by decide)

theorem absoluteRing_closed : P93AuthorityClosedCycle absoluteSource absoluteRing := by
  simp [P93AuthorityClosedCycle, absoluteRing, absoluteSource, bond,
    P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    P93AuthorityBinaryInteractionKind, P93AuthorityAtomsBounded,
    SemanticMolecule.atomCount]

theorem absoluteCenter_envelope :
    P93CanonicalPhysicalUnitEnvelope absoluteSource (.atomCenter 0) := by
  refine ⟨by decide, [1, 5, 6], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, absoluteSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, absoluteSource, bond,
        P93AuthorityBinaryInteractionKind]

def absolutePayload : P93MonocyclicClausePayload .monocyclicAbsoluteCenters :=
  .absoluteCenter
    { ring := absoluteRing, unit := .atomCenter 0, citation := citation 1 }
    0 .chiralCenter .R .absolute .CIP

theorem absolutePayload_valid :
    (P93ClausePayloadData.monocyclic absolutePayload).ValidFor absoluteSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, absolutePayload,
      P93MonocyclicClausePayload.toClaims, P93MonocyclicCitedPayload.baseClaims,
      P93MonocyclicPhysicalPayload.baseClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl
    · exact absoluteRing_closed
    · exact ⟨absoluteRing_closed, absoluteCenter_envelope⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid], absoluteCenter_envelope⟩
    · exact ⟨by decide, by simp [DescriptorApplies]⟩
  · exact ⟨absoluteRing_closed, rfl, Or.inl rfl, by simp [DescriptorApplies], rfl, rfl,
      by simp [citation, P93AuthorityCitationToken.Valid]⟩

/-! ## P-93.5.1.1.2 achiral cyclic compound -/

/-- Full heavy-atom graph of `(1s,4s)-cyclohexane-1,4-diol`. -/
def achiralSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 8 carbonAtom |>.set 6 oxygenAtom |>.set 7 oxygenAtom
      interactions :=
        [ bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 5, bond 5 0
        , bond 0 6, bond 3 7 ] }

def achiralRing : List Nat := [0, 1, 2, 3, 4, 5]

theorem achiralSource_wellFormed : achiralSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    achiralSource).mp (by decide)

theorem achiralRing_closed : P93AuthorityClosedCycle achiralSource achiralRing := by
  simp [P93AuthorityClosedCycle, achiralRing, achiralSource, bond,
    P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    P93AuthorityBinaryInteractionKind, P93AuthorityAtomsBounded,
    SemanticMolecule.atomCount]

theorem achiralCenter_envelope :
    P93CanonicalPhysicalUnitEnvelope achiralSource (.atomCenter 0) := by
  refine ⟨by decide, [1, 5, 6], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, achiralSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, achiralSource, bond,
        P93AuthorityBinaryInteractionKind]

def achiralPayload : P93MonocyclicClausePayload .monocyclicAchiralCenters :=
  .achiralCenter
    { ring := achiralRing, unit := .atomCenter 0, citation := citation 1 }
    0 .pseudoasymmetricCenter .s .absolute .CIP

theorem achiralPayload_valid :
    (P93ClausePayloadData.monocyclic achiralPayload).ValidFor achiralSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, achiralPayload,
      P93MonocyclicClausePayload.toClaims, P93MonocyclicCitedPayload.baseClaims,
      P93MonocyclicPhysicalPayload.baseClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl | rfl
    · exact achiralRing_closed
    · exact ⟨achiralRing_closed, achiralCenter_envelope⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid], achiralCenter_envelope⟩
    · exact ⟨by decide, by simp [DescriptorApplies]⟩
    · change 0 < achiralSource.molecule.atomCount
      simp [achiralSource, SemanticMolecule.atomCount]
  · exact ⟨achiralRing_closed, rfl, Or.inr rfl, by simp [DescriptorApplies], rfl,
      by simp [citation, P93AuthorityCitationToken.Valid]⟩

/-! ## P-93.5.1.2 cis/trans -/

/-- Full heavy-atom graph of `cis-2-chlorocyclopentane-1-carboxylic acid`: ring `0..4`,
carboxyl carbon `5`, oxygens `6,7`, and chlorine `8`. -/
def cisTransSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom,
          carbonAtom, oxygenAtom, oxygenAtom, chlorineAtom]
      interactions :=
        [ bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 0
        , bond 0 5, bond 5 6 2, bond 5 7, bond 1 8 ] }

def cisTransRing : List Nat := [0, 1, 2, 3, 4]

theorem cisTransSource_wellFormed : cisTransSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    cisTransSource).mp (by decide)

theorem cisTransRing_closed : P93AuthorityClosedCycle cisTransSource cisTransRing := by
  simp [P93AuthorityClosedCycle, cisTransRing, cisTransSource, bond,
    P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    P93AuthorityBinaryInteractionKind, P93AuthorityAtomsBounded,
    SemanticMolecule.atomCount]

theorem cisTransFirstBond : P93AuthorityBinaryBond cisTransSource 0 5 := by
  simp [P93AuthorityBinaryBond, cisTransSource, bond, P93AuthorityBinaryInteractionKind]

theorem cisTransSecondBond : P93AuthorityBinaryBond cisTransSource 1 8 := by
  simp [P93AuthorityBinaryBond, cisTransSource, bond, P93AuthorityBinaryInteractionKind]

def cisTransPayload : P93MonocyclicClausePayload .monocyclicCisTrans :=
  .cisTrans cisTransRing 0 1 5 8 meanPlaneObservation .positive .positive .cis

theorem cisTransPayload_valid :
    (P93ClausePayloadData.monocyclic cisTransPayload).ValidFor cisTransSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, cisTransPayload,
      P93MonocyclicClausePayload.toClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl
    · exact cisTransRing_closed
    · exact ⟨cisTransRing_closed, by simp [cisTransRing], by simp [cisTransRing], by decide⟩
    · exact ⟨cisTransRing_closed, by decide⟩
    · exact ⟨cisTransRing_closed, by decide⟩
  · exact ⟨cisTransRing_closed, by simp [cisTransRing], by simp [cisTransRing], by decide,
      by decide, by simp [cisTransRing], by simp [cisTransRing], cisTransFirstBond,
      cisTransSecondBond, meanPlaneObservation_applicable, by simp [RelativeRingSide]⟩

/-! ## P-93.5.1.3 r/c/t -/

/-- Full heavy-atom graph of `1r,2c,4c-tribromocyclohexane`. -/
def rctSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom,
          bromineAtom, bromineAtom, bromineAtom]
      interactions :=
        [ bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 5, bond 5 0
        , bond 0 6, bond 1 7, bond 3 8 ] }

def rctRing : List Nat := [0, 1, 2, 3, 4, 5]

def rctCandidate1 : P93MonocyclicRCTReferenceCandidate where
  ringPosition := 0
  substituent := 6
  citation := citation 1
  namedAsSuffix := false
  sequencePriority := 1

def rctCandidate2 : P93MonocyclicRCTReferenceCandidate where
  ringPosition := 1
  substituent := 7
  citation := citation 2
  namedAsSuffix := false
  sequencePriority := 1

def rctCandidate4 : P93MonocyclicRCTReferenceCandidate where
  ringPosition := 3
  substituent := 8
  citation := citation 4
  namedAsSuffix := false
  sequencePriority := 1

def rctAssignment1 : P93MonocyclicRCTLocatedAssignment where
  ringPosition := 0
  substituent := 6
  side := .positive
  descriptor := .reference

def rctAssignment2 : P93MonocyclicRCTLocatedAssignment where
  ringPosition := 1
  substituent := 7
  side := .positive
  descriptor := .cisToReference

def rctAssignment4 : P93MonocyclicRCTLocatedAssignment where
  ringPosition := 3
  substituent := 8
  side := .positive
  descriptor := .cisToReference

theorem rctSource_wellFormed : rctSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    rctSource).mp (by decide)

theorem rctRing_closed : P93AuthorityClosedCycle rctSource rctRing := by
  simp [P93AuthorityClosedCycle, rctRing, rctSource, bond,
    P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    P93AuthorityBinaryInteractionKind, P93AuthorityAtomsBounded,
    SemanticMolecule.atomCount]

def rctPayload : P93MonocyclicClausePayload .monocyclicRCT :=
  .rct rctRing [rctCandidate1, rctCandidate2, rctCandidate4] rctCandidate1 .positive
    [rctAssignment1, rctAssignment2, rctAssignment4]

theorem rctPayload_valid :
    (P93ClausePayloadData.monocyclic rctPayload).ValidFor rctSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, rctPayload,
      P93MonocyclicClausePayload.toClaims, rctCandidate1, rctCandidate2, rctCandidate4,
      rctAssignment1, rctAssignment2, rctAssignment4] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact rctRing_closed
    · exact ⟨rctRing_closed, by decide⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid], by
        refine ⟨by decide, [1, 5, 6], by decide, by decide, ?_, ?_⟩
        · simp [P93AuthorityAtomsBounded, rctSource, SemanticMolecule.atomCount]
        · intro neighbor member
          simp at member
          rcases member with rfl | rfl | rfl <;> left <;>
            simp [P93AuthorityBinaryBond, rctSource, bond,
              P93AuthorityBinaryInteractionKind]⟩
    · exact ⟨rctRing_closed, by simp [rctRing], by simp [rctRing], by
        simp [P93AuthorityBinaryBond, rctSource, bond, P93AuthorityBinaryInteractionKind],
        by simp [citation, P93AuthorityCitationToken.Valid]⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid], by
        refine ⟨by decide, [0, 2, 7], by decide, by decide, ?_, ?_⟩
        · simp [P93AuthorityAtomsBounded, rctSource, SemanticMolecule.atomCount]
        · intro neighbor member
          simp at member
          rcases member with rfl | rfl | rfl <;> left <;>
            simp [P93AuthorityBinaryBond, rctSource, bond,
              P93AuthorityBinaryInteractionKind]⟩
    · exact ⟨rctRing_closed, by simp [rctRing], by simp [rctRing], by
        simp [P93AuthorityBinaryBond, rctSource, bond, P93AuthorityBinaryInteractionKind],
        by simp [citation, P93AuthorityCitationToken.Valid]⟩
    · exact ⟨by simp [citation, P93AuthorityCitationToken.Valid], by
        refine ⟨by decide, [2, 4, 8], by decide, by decide, ?_, ?_⟩
        · simp [P93AuthorityAtomsBounded, rctSource, SemanticMolecule.atomCount]
        · intro neighbor member
          simp at member
          rcases member with rfl | rfl | rfl <;> left <;>
            simp [P93AuthorityBinaryBond, rctSource, bond,
              P93AuthorityBinaryInteractionKind]⟩
    · exact ⟨rctRing_closed, by simp [rctRing], by simp [rctRing], by
        simp [P93AuthorityBinaryBond, rctSource, bond, P93AuthorityBinaryInteractionKind],
        by simp [citation, P93AuthorityCitationToken.Valid]⟩
    · exact ⟨rctRing_closed, by decide⟩
    · exact ⟨rctRing_closed, by decide⟩
    · exact ⟨rctRing_closed, by decide⟩
  · change P93AuthorityClosedCycle rctSource rctRing ∧ _
    refine ⟨rctRing_closed, ?_⟩
    simp [rctCandidate1, rctCandidate2, rctCandidate4,
      rctAssignment1, rctAssignment2, rctAssignment4, rctRing,
      P93MonocyclicIsRCTReference, citation, P93AuthorityCitationToken.Valid,
      P93AuthorityCitationToken.CitationLE, P93AuthorityCitationToken.key,
      P93AuthorityNatListLexLE, rctDescriptor, rctSource, bond,
      P93AuthorityBinaryBond, P93AuthorityBinaryInteractionKind]

/-! ## P-93.5.1.4.2.1 exocyclic E/Z -/

/-- Full heavy-atom graph of `(1Z,3E)-1,3-diethylidenecyclopentane`: ring `0..4`,
exocyclic alkene carbons `5,7`, and their methyl carbons `6,8`. -/
def exocyclicEZSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 9 carbonAtom
      interactions :=
        [ bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 0
        , bond 0 5 2, bond 5 6, bond 2 7 2, bond 7 8 ] }

def exocyclicEZRing : List Nat := [0, 1, 2, 3, 4]

theorem exocyclicEZSource_wellFormed : exocyclicEZSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    exocyclicEZSource).mp (by decide)

theorem exocyclicEZRing_closed :
    P93AuthorityClosedCycle exocyclicEZSource exocyclicEZRing := by
  simp [P93AuthorityClosedCycle, exocyclicEZRing, exocyclicEZSource, bond,
    P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    P93AuthorityBinaryInteractionKind, P93AuthorityAtomsBounded,
    SemanticMolecule.atomCount]

theorem exocyclicEZBond_envelope :
    P93CanonicalPhysicalUnitEnvelope exocyclicEZSource (.bond 0 5) := by
  exact ⟨by decide, by decide, by decide, by
    simp [P93AuthorityBinaryBond, exocyclicEZSource, bond,
      P93AuthorityBinaryInteractionKind]⟩

def exocyclicEZPayload : P93MonocyclicClausePayload .exocyclicDoubleBondEZ :=
  .exocyclicEZ { ring := exocyclicEZRing, unit := .bond 0 5 }
    2 false true .integralParentDoubleBond .individualStereogenicUnits (some .Z)

theorem exocyclicEZPayload_valid :
    (P93ClausePayloadData.monocyclic exocyclicEZPayload).ValidFor exocyclicEZSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, exocyclicEZPayload,
      P93MonocyclicClausePayload.toClaims, P93MonocyclicPhysicalPayload.baseClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl
    · exact exocyclicEZRing_closed
    · exact ⟨exocyclicEZRing_closed, exocyclicEZBond_envelope⟩
    · exact ⟨exocyclicEZRing_closed, exocyclicEZBond_envelope⟩
    · exact exocyclicEZBond_envelope
  · exact ⟨exocyclicEZRing_closed, trivial, ⟨0, 5, rfl⟩, by simp [P93ExocyclicEZDescriptor]⟩

/-! ## P-93.5.1.4.2.2 non-E/Z exocyclic descriptor -/

/-- Full heavy-atom graph of `(M)-(4-methylcyclohexylidene)hydroxylamine`: ring `0..5`,
exocyclic imine nitrogen `6`, hydroxyl oxygen `7`, and the 4-methyl carbon `8`. -/
def exocyclicOtherSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        [carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom, carbonAtom,
          nitrogenAtom, oxygenAtom, carbonAtom]
      interactions :=
        [ bond 0 1, bond 1 2, bond 2 3, bond 3 4, bond 4 5, bond 5 0
        , bond 0 6 2, bond 6 7, bond 3 8 ] }

def exocyclicOtherRing : List Nat := [0, 1, 2, 3, 4, 5]

theorem exocyclicOtherSource_wellFormed : exocyclicOtherSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff
    exocyclicOtherSource).mp (by decide)

theorem exocyclicOtherRing_closed :
    P93AuthorityClosedCycle exocyclicOtherSource exocyclicOtherRing := by
  simp [P93AuthorityClosedCycle, exocyclicOtherRing, exocyclicOtherSource, bond,
    P93AuthorityConnectedPath, P93AuthorityBinaryBond,
    P93AuthorityBinaryInteractionKind, P93AuthorityAtomsBounded,
    SemanticMolecule.atomCount]

theorem exocyclicOtherBond_envelope :
    P93CanonicalPhysicalUnitEnvelope exocyclicOtherSource (.bond 0 6) := by
  exact ⟨by decide, by decide, by decide, by
    simp [P93AuthorityBinaryBond, exocyclicOtherSource, bond,
      P93AuthorityBinaryInteractionKind]⟩

def exocyclicOtherPayload : P93MonocyclicClausePayload .exocyclicDoubleBondOther :=
  .exocyclicOther { ring := exocyclicOtherRing, unit := .bond 0 6 }
    1 false false .ylideneSubstituent .wholeAlleneSystem (some .M)

theorem exocyclicOtherPayload_valid :
    (P93ClausePayloadData.monocyclic exocyclicOtherPayload).ValidFor
      exocyclicOtherSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, exocyclicOtherPayload,
      P93MonocyclicClausePayload.toClaims, P93MonocyclicPhysicalPayload.baseClaims] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl
    · exact exocyclicOtherRing_closed
    · exact ⟨exocyclicOtherRing_closed, exocyclicOtherBond_envelope⟩
    · exact ⟨exocyclicOtherRing_closed, exocyclicOtherBond_envelope⟩
    · exact exocyclicOtherBond_envelope
  · exact ⟨exocyclicOtherRing_closed, rfl, ⟨0, 6, rfl⟩,
      by simp [P93ExocyclicOtherDescriptor]⟩

/-! ## Dependent observations and claim-complete provenance -/

def configurationObservation :
    P93ClauseObservation configurationSource (.monocyclic .cyclicConfigurations) where
  payload := .monocyclic configurationPayload
  validFor := configurationPayload_valid

def configurationTranscription : P93CanonicalSourceTranscription configurationSource
    (.monocyclic .cyclicConfigurations) configurationObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 58
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.1.1.1"
  observationSubsectionNonempty := by decide
  printedObservation := "(1R,2R)-1,2,4-trimethylcyclopentane (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _claimMem
    exact
      { supportingLocator :=
          "PDF page 58, P-93.5.1.1.1, named example and adjacent complete structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "(1R,2R)-1,2,4-trimethylcyclopentane (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def absoluteObservation :
    P93ClauseObservation absoluteSource (.monocyclic .monocyclicAbsoluteCenters) where
  payload := .monocyclic absolutePayload
  validFor := absolutePayload_valid

def absoluteTranscription : P93CanonicalSourceTranscription absoluteSource
    (.monocyclic .monocyclicAbsoluteCenters) absoluteObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 57
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.1.1.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.1.1.1"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(1R,2S,5R)-5-methyl-2-(propan-2-yl)cyclohexan-1-ol (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _claimMem
    exact
      { supportingLocator :=
          "PDF page 57, P-93.5.1.1.1, first named example and adjacent complete structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "(1R,2S,5R)-5-methyl-2-(propan-2-yl)cyclohexan-1-ol (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def achiralObservation :
    P93ClauseObservation achiralSource (.monocyclic .monocyclicAchiralCenters) where
  payload := .monocyclic achiralPayload
  validFor := achiralPayload_valid

def achiralTranscription : P93CanonicalSourceTranscription achiralSource
    (.monocyclic .monocyclicAchiralCenters) achiralObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 58
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.1.1.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.1.1.2(a)"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(1s,4s)-cyclohexane-1,4-diol (PIN); cis-cyclohexane-1,4-diol"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _claimMem
    exact
      { supportingLocator :=
          "PDF page 58, P-93.5.1.1.2(a), first named example and adjacent complete structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "(1s,4s)-cyclohexane-1,4-diol (PIN); cis-cyclohexane-1,4-diol"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def cisTransObservation :
    P93ClauseObservation cisTransSource (.monocyclic .monocyclicCisTrans) where
  payload := .monocyclic cisTransPayload
  validFor := cisTransPayload_valid

def cisTransTranscription : P93CanonicalSourceTranscription cisTransSource
    (.monocyclic .monocyclicCisTrans) cisTransObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 60
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.1.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.1.2"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "cis-2-chlorocyclopentane-1-carboxylic acid; rel-(1R,2R)-2-chlorocyclopentane-1-carboxylic acid (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _claimMem
    exact
      { supportingLocator :=
          "PDF page 60, P-93.5.1.2, first named example and adjacent complete wedge structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "cis-2-chlorocyclopentane-1-carboxylic acid; rel-(1R,2R)-2-chlorocyclopentane-1-carboxylic acid (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def rctObservation : P93ClauseObservation rctSource (.monocyclic .monocyclicRCT) where
  payload := .monocyclic rctPayload
  validFor := rctPayload_valid

def rctTranscription : P93CanonicalSourceTranscription rctSource
    (.monocyclic .monocyclicRCT) rctObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 61
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.1.3"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.1.3.1, Example 1"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "1r,2c,4c-tribromocyclohexane; rel-(1R,2S,4S)-1,2,4-tribromocyclohexane (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _claimMem
    exact
      { supportingLocator :=
          "PDF page 61, P-93.5.1.3.1 Example 1, named example and adjacent complete wedge structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "1r,2c,4c-tribromocyclohexane; rel-(1R,2S,4S)-1,2,4-tribromocyclohexane (PIN)"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def exocyclicEZObservation :
    P93ClauseObservation exocyclicEZSource (.monocyclic .exocyclicDoubleBondEZ) where
  payload := .monocyclic exocyclicEZPayload
  validFor := exocyclicEZPayload_valid

def exocyclicEZTranscription : P93CanonicalSourceTranscription exocyclicEZSource
    (.monocyclic .exocyclicDoubleBondEZ) exocyclicEZObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 64
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.1.4.2.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.1.4.2.1(2), Example 1"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(1Z,3E)-1,3-diethylidenecyclopentane (PIN); 1-[(Z)-ethylidene]-3-[(E)-ethylidene]cyclopentane"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _claimMem
    exact
      { supportingLocator :=
          "PDF page 64, P-93.5.1.4.2.1(2) Example 1, named example and adjacent complete structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "(1Z,3E)-1,3-diethylidenecyclopentane (PIN); 1-[(Z)-ethylidene]-3-[(E)-ethylidene]cyclopentane"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def exocyclicOtherObservation :
    P93ClauseObservation exocyclicOtherSource (.monocyclic .exocyclicDoubleBondOther) where
  payload := .monocyclic exocyclicOtherPayload
  validFor := exocyclicOtherPayload_valid

def exocyclicOtherTranscription : P93CanonicalSourceTranscription exocyclicOtherSource
    (.monocyclic .exocyclicDoubleBondOther) exocyclicOtherObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 :=
    "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 65
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.1.4.2.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.1.4.2.2, Example 1"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(M)-(4-methylcyclohexylidene)hydroxylamine"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _claimMem
    exact
      { supportingLocator :=
          "PDF page 65, P-93.5.1.4.2.2 Example 1, named alternative and adjacent complete structure"
        supportingLocatorNonempty := by decide
        supportingObservation := "(M)-(4-methylcyclohexylidene)hydroxylamine"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

/-! ## Proof-carrying entries and exact seven-row coverage -/

def configurationEntry : P93CanonicalClauseObservationEntry where
  source := configurationSource
  sourceAdmitted := configurationSource_wellFormed
  clause := .monocyclic .cyclicConfigurations
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.monocyclicRows,
      Remaining71P93MonocyclicAuthorityRow.all]
  observation := configurationObservation
  transcription := configurationTranscription

def absoluteEntry : P93CanonicalClauseObservationEntry where
  source := absoluteSource
  sourceAdmitted := absoluteSource_wellFormed
  clause := .monocyclic .monocyclicAbsoluteCenters
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.monocyclicRows,
      Remaining71P93MonocyclicAuthorityRow.all]
  observation := absoluteObservation
  transcription := absoluteTranscription

def achiralEntry : P93CanonicalClauseObservationEntry where
  source := achiralSource
  sourceAdmitted := achiralSource_wellFormed
  clause := .monocyclic .monocyclicAchiralCenters
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.monocyclicRows,
      Remaining71P93MonocyclicAuthorityRow.all]
  observation := achiralObservation
  transcription := achiralTranscription

def cisTransEntry : P93CanonicalClauseObservationEntry where
  source := cisTransSource
  sourceAdmitted := cisTransSource_wellFormed
  clause := .monocyclic .monocyclicCisTrans
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.monocyclicRows,
      Remaining71P93MonocyclicAuthorityRow.all]
  observation := cisTransObservation
  transcription := cisTransTranscription

def rctEntry : P93CanonicalClauseObservationEntry where
  source := rctSource
  sourceAdmitted := rctSource_wellFormed
  clause := .monocyclic .monocyclicRCT
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.monocyclicRows,
      Remaining71P93MonocyclicAuthorityRow.all]
  observation := rctObservation
  transcription := rctTranscription

def exocyclicEZEntry : P93CanonicalClauseObservationEntry where
  source := exocyclicEZSource
  sourceAdmitted := exocyclicEZSource_wellFormed
  clause := .monocyclic .exocyclicDoubleBondEZ
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.monocyclicRows,
      Remaining71P93MonocyclicAuthorityRow.all]
  observation := exocyclicEZObservation
  transcription := exocyclicEZTranscription

def exocyclicOtherEntry : P93CanonicalClauseObservationEntry where
  source := exocyclicOtherSource
  sourceAdmitted := exocyclicOtherSource_wellFormed
  clause := .monocyclic .exocyclicDoubleBondOther
  clauseListed := by
    simp [P93Clause.all, Remaining71P93ClosedProductionRow.all,
      Remaining71P93ClosedProductionRow.monocyclicRows,
      Remaining71P93MonocyclicAuthorityRow.all]
  observation := exocyclicOtherObservation
  transcription := exocyclicOtherTranscription

def entries : List P93CanonicalClauseObservationEntry :=
  [ configurationEntry, absoluteEntry, achiralEntry, cisTransEntry, rctEntry,
    exocyclicEZEntry, exocyclicOtherEntry ]

def coveredClauses : List P93Clause :=
  [ .monocyclic .cyclicConfigurations
  , .monocyclic .monocyclicAbsoluteCenters
  , .monocyclic .monocyclicAchiralCenters
  , .monocyclic .monocyclicCisTrans
  , .monocyclic .monocyclicRCT
  , .monocyclic .exocyclicDoubleBondEZ
  , .monocyclic .exocyclicDoubleBondOther ]

@[simp] theorem entries_length : entries.length = 7 := rfl

@[simp] theorem entries_clause_exact : entries.map (·.clause) = coveredClauses := rfl

theorem coveredClauses_nodup : coveredClauses.Nodup := by
  decide

theorem entries_family_source_nodup :
    (entries.map fun entry => (entry.clause.family, entry.source)).Nodup := by
  decide

theorem coveredClause_has_entry (clause : P93Clause) (member : clause ∈ coveredClauses) :
    ∃ entry ∈ entries, entry.clause = clause := by
  simp [coveredClauses] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨configurationEntry, by simp [entries], rfl⟩
  · exact ⟨absoluteEntry, by simp [entries], rfl⟩
  · exact ⟨achiralEntry, by simp [entries], rfl⟩
  · exact ⟨cisTransEntry, by simp [entries], rfl⟩
  · exact ⟨rctEntry, by simp [entries], rfl⟩
  · exact ⟨exocyclicEZEntry, by simp [entries], rfl⟩
  · exact ⟨exocyclicOtherEntry, by simp [entries], rfl⟩

/-- The package covers exactly the seven monocyclic rows left out of the earlier two-entry cyclic
source module.  The two already-covered unsaturation rows are not duplicated here. -/
theorem coveredClauses_exact_remaining_seven :
    coveredClauses =
      [ .monocyclic .cyclicConfigurations
      , .monocyclic .monocyclicAbsoluteCenters
      , .monocyclic .monocyclicAchiralCenters
      , .monocyclic .monocyclicCisTrans
      , .monocyclic .monocyclicRCT
      , .monocyclic .exocyclicDoubleBondEZ
      , .monocyclic .exocyclicDoubleBondOther ] := rfl

end P93CanonicalProgramMonocyclicText
end TetraStereo.OneCenter
