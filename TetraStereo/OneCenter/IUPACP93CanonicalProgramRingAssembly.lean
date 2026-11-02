import TetraStereo.OneCenter.IUPACP93CanonicalSourceClaims

set_option autoImplicit false
set_option maxRecDepth 4096

/-!
# Canonical P-93.5.7 source observations

This module transcribes the complete constitutional graphs for the source examples used by the
axial, stereogenic-center, and double-bond rows.  For the axial row, the printed molecule,
diagram roles, and descriptors remain independent of the exact rational reconstruction used by
the executable geometry theorem; the reconstruction is explicitly not attributed to the source.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Acyclic
open BlueBookP93.Cyclic
open IUPACNormativeProvision

namespace P93CanonicalProgramRingAssembly

def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
def nitrogen : PeriodicElement := ⟨7, by decide, by decide⟩
def oxygen : PeriodicElement := ⟨8, by decide, by decide⟩

def carbonAtom : SemanticAtom where element := carbon
def nitrogenPositiveAtom : SemanticAtom where element := nitrogen; formalCharge := 1
def oxygenAtom : SemanticAtom where element := oxygen
def oxygenNegativeAtom : SemanticAtom where element := oxygen; formalCharge := -1

def bond (left right : Nat) (order : Nat := 1) : SemanticInteraction where
  participants := [left, right]
  kind := .covalent order

def citation (value : Nat) (primes : Nat := 0) : P93AuthorityCitationToken where
  components := [{ value := value, primes := primes }]

def claimTranscription (locator observation : String)
    (locatorNonempty : locator ≠ "") (observationNonempty : observation ≠ "")
    (claim : P93SourceClaim) : P93CanonicalClaimTranscription claim where
  supportingLocator := locator
  supportingLocatorNonempty := locatorNonempty
  supportingObservation := observation
  supportingObservationNonempty := observationNonempty
  mode := .textAndFigure

def sixRingBonds (base : Nat) : List SemanticInteraction :=
  [ bond base (base + 1), bond (base + 1) (base + 2),
    bond (base + 2) (base + 3), bond (base + 3) (base + 4),
    bond (base + 4) (base + 5), bond (base + 5) base ]

def eightRingBonds (base : Nat) : List SemanticInteraction :=
  [ bond base (base + 1), bond (base + 1) (base + 2),
    bond (base + 2) (base + 3), bond (base + 3) (base + 4),
    bond (base + 4) (base + 5), bond (base + 5) (base + 6),
    bond (base + 6) (base + 7), bond (base + 7) base ]

def firstUnsaturatedEightRingBonds : List SemanticInteraction :=
  [ bond 0 1, bond 1 2, bond 2 3 2, bond 3 4,
    bond 4 5, bond 5 6, bond 6 7, bond 7 0 ]

/-! ## P-93.5.7.1: stereogenic axes -/

def rawAtom (element : Element) (charge : Int := 0) : AtomSpec where
  element := element
  charge := charge

def rawBond (source target : Nat) (kind : ParsedBondKind := .single) : RawBond where
  source := source
  target := target
  kind := kind

/-- Full raw heavy-atom graph of the first page-83 example,
`(1M)-6,6'-dinitro[1,1'-biphenyl]-2,2'-dicarboxylic acid`, whose general descriptor is `(1Ra)`.
Atoms `0..5` and `6..11` are the two benzene rings; `0--6` is axis 1.  Carboxyl groups begin at
`12` and `15`, and nitro groups begin at `18` and `21`.
-/
def axisRaw : RawMolecule where
  atoms := List.replicate 12 (rawAtom .C) ++
    [rawAtom .C, rawAtom .O, rawAtom .O,
     rawAtom .C, rawAtom .O, rawAtom .O,
     rawAtom .N 1, rawAtom .O, rawAtom .O (-1),
     rawAtom .N 1, rawAtom .O, rawAtom .O (-1)]
  bonds :=
    [ rawBond 0 1 .double, rawBond 1 2, rawBond 2 3 .double,
      rawBond 3 4, rawBond 4 5 .double, rawBond 5 0,
      rawBond 6 7 .double, rawBond 7 8, rawBond 8 9 .double,
      rawBond 9 10, rawBond 10 11 .double, rawBond 11 6,
      rawBond 0 6,
      rawBond 1 12, rawBond 12 13 .double, rawBond 12 14,
      rawBond 7 15, rawBond 15 16 .double, rawBond 15 17,
      rawBond 5 18, rawBond 18 19 .double, rawBond 18 20,
      rawBond 11 21, rawBond 21 22 .double, rawBond 21 23 ]

def alternatingSixRingBonds (base : Nat) : List SemanticInteraction :=
  [ bond base (base + 1) 2, bond (base + 1) (base + 2),
    bond (base + 2) (base + 3) 2, bond (base + 3) (base + 4),
    bond (base + 4) (base + 5) 2, bond (base + 5) base ]

/-- The source channel contains the printed molecular graph and its parser-derived diagram.
The exact rational coordinates below are a reconstruction and are not printed coordinates. -/
def axisSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 12 carbonAtom ++
        [carbonAtom, oxygenAtom, oxygenAtom,
         carbonAtom, oxygenAtom, oxygenAtom,
         nitrogenPositiveAtom, oxygenAtom, oxygenNegativeAtom,
         nitrogenPositiveAtom, oxygenAtom, oxygenNegativeAtom]
      interactions := alternatingSixRingBonds 0 ++ alternatingSixRingBonds 6 ++
        [bond 0 6,
         bond 1 12, bond 12 13 2, bond 12 14,
         bond 7 15, bond 15 16 2, bond 15 17,
         bond 5 18, bond 18 19 2, bond 18 20,
         bond 11 21, bond 21 22 2, bond 21 23] }
  spatial? := some
    { positions := (List.range 24).map fun atom =>
        match atom with
        | 0 => { x := 0, y := 0, z := 0 }
        | 1 => { x := 0, y := -1, z := 0 }
        | 5 => { x := 0, y := 1, z := 0 }
        | 6 => { x := 1, y := 0, z := 0 }
        | 7 => { x := 1, y := 0, z := 1 }
        | 11 => { x := 1, y := 0, z := -1 }
        | n => { x := n, y := 0, z := 0 } }
  diagram? := some axisRaw.toDiagramConfiguration

theorem axisSource_structurallyWellFormed : axisSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff axisSource).mp
    (by decide)

def axisRing0 : List Nat := [0, 1, 2, 3, 4, 5]
def axisRing1 : List Nat := [6, 7, 8, 9, 10, 11]

def axisJunction : P93RingAssemblyJunction where
  leftRingIndex := 0
  rightRingIndex := 1
  leftAtom := 0
  rightAtom := 6

def axisAssembly : P93AuthorityRingAssembly where
  rings := [axisRing0, axisRing1]
  junctions := [axisJunction]

theorem axisRing0_closed : P93AuthorityClosedCycle axisSource axisRing0 := by
  simp [P93AuthorityClosedCycle, P93AuthorityAtomsBounded, P93AuthorityConnectedPath,
    P93AuthorityBinaryBond, axisSource, axisRing0, alternatingSixRingBonds, bond,
    P93AuthorityBinaryInteractionKind, SemanticMolecule.atomCount]

theorem axisRing1_closed : P93AuthorityClosedCycle axisSource axisRing1 := by
  simp [P93AuthorityClosedCycle, P93AuthorityAtomsBounded, P93AuthorityConnectedPath,
    P93AuthorityBinaryBond, axisSource, axisRing1, alternatingSixRingBonds, bond,
    P93AuthorityBinaryInteractionKind, SemanticMolecule.atomCount]

theorem axisAssembly_connected : P93RingAssemblyConnected axisAssembly := by
  intro first firstBound second secondBound
  simp [axisAssembly] at firstBound secondBound
  interval_cases first <;> interval_cases second
  · exact ⟨[0], by decide, by simp [axisAssembly], rfl, rfl, by trivial⟩
  · exact ⟨[0, 1], by decide, by simp [axisAssembly], rfl, rfl, by
      simp [P93RingAssemblyIndexPath, P93RingAssemblyIndicesJoined,
        axisAssembly, axisJunction]⟩
  · exact ⟨[1, 0], by decide, by simp [axisAssembly], rfl, rfl, by
      simp [P93RingAssemblyIndexPath, P93RingAssemblyIndicesJoined,
        axisAssembly, axisJunction]⟩
  · exact ⟨[1], by decide, by simp [axisAssembly], rfl, rfl, by trivial⟩

theorem axisAssembly_valid : axisAssembly.MechanicallyValidFor axisSource := by
  unfold P93AuthorityRingAssembly.MechanicallyValidFor
  refine ⟨by decide, by decide, ?_, ?_, by decide, by decide, ?_,
    axisAssembly_connected⟩
  · intro ring ringMem
    simp [axisAssembly] at ringMem
    rcases ringMem with rfl | rfl
    · exact axisRing0_closed
    · exact axisRing1_closed
  · intro leftIndex leftRing leftLookup rightIndex rightRing rightLookup distinct
    have leftBound : leftIndex < 2 := by
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp leftLookup
      simpa [axisAssembly] using bound
    have rightBound : rightIndex < 2 := by
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp rightLookup
      simpa [axisAssembly] using bound
    interval_cases leftIndex <;> interval_cases rightIndex <;>
      simp [axisAssembly] at leftLookup rightLookup <;>
      subst leftRing <;> subst rightRing <;>
      simp_all [axisRing0, axisRing1, Finset.disjoint_left]
  · intro junction junctionMem
    simp [axisAssembly] at junctionMem
    subst junction
    simp [P93RingAssemblyJunction.ValidFor, axisAssembly, axisJunction,
      axisRing0, axisRing1, P93AuthorityBinaryBond, axisSource,
      alternatingSixRingBonds, bond, P93AuthorityBinaryInteractionKind]

/-- Exact diagram-role map for the printed first example on page 83:
`0--6` is axis 1; `1/5` and `7/11` are the two adjacent ring-atom pairs.  The carboxyl directions
are `1` and `7`; the nitro directions are `5` and `11`.  The official comparator independently
selects the nitro direction at both ends.
-/
def axisPrintedAssignment : P93CanonicalRingAssemblyPrintedAxisAssignment where
  junction := axisJunction
  startFirst := 1
  startSecond := 5
  endFirst := 7
  endSecond := 11
  citation := citation 1
  cipDescriptor := .Ra
  preferredDescriptor := .M
  generalDescriptor := .Ra

def axisPrinted : P93CanonicalRingAssemblyPrintedAxesObservation where
  molecule := axisSource.molecule
  assembly := axisAssembly
  assignments := [axisPrintedAssignment]

def axisSpatial : SpatialConfiguration := axisSource.spatial?.getD { positions := [] }

theorem axisRaw_converted : axisRaw.toSemanticMolecule? = some axisSource.molecule := by
  decide

def axisNormalization : CertifiedChemistryNormalizationResult where
  result := normalizeRawMolecule axisRaw
  admissible := by
    exact ((normalizeRawMolecule axisRaw).parsed.admissible?_eq_true_iff).mp (by decide)
  writtenNeighborExact := by
    exact ((normalizeRawMolecule axisRaw).parsed.writtenNeighborExact?_eq_true_iff).mp
      (by decide)
  valenceOK := by
    exact ((normalizeRawMolecule axisRaw).parsed.valenceOK?_eq_true_iff).mp (by decide)
  rule2MassesKnown := by
    exact ((normalizeRawMolecule axisRaw).parsed.rule2MassesKnown?_eq_true_iff).mp (by decide)

def axisAssignment : P93RingAssemblyAxisAssignment where
  junction := axisJunction
  record := axisPrintedAssignment.record
  citation := citation 1
  cipDescriptor := .Ra
  preferredDescriptor := .M
  generalDescriptor := .Ra

def axisExecutable : P93CanonicalRingAssemblyAxesExecutableWitness where
  normalization := axisNormalization
  spatial := axisSpatial
  assignments := [axisAssignment]

set_option maxHeartbeats 1000000 in
/-- Kernel reduction of the official Rules-1a--5 comparator.  `lt` means the first listed
carboxyl-side reference is junior to the second listed nitro-side reference. -/
theorem axisStartPriority_exact :
    compareBranchesThroughOfficialContext? axisNormalization.result
      axisNormalization.result.geometryPriorityState.1
      axisNormalization.result.geometryPriorityState.2.2
      axisNormalization.result.geometryPriorityState.2.1 0 1 5 = some .lt := by
  rfl

set_option maxHeartbeats 1000000 in
theorem axisEndPriority_exact :
    compareBranchesThroughOfficialContext? axisNormalization.result
      axisNormalization.result.geometryPriorityState.1
      axisNormalization.result.geometryPriorityState.2.2
      axisNormalization.result.geometryPriorityState.2.1 6 7 11 = some .lt := by
  rfl

theorem axisFrame_valid :
    P93RingAssemblyAxisFrameValid axisSource axisAssembly axisJunction
      axisPrintedAssignment.record := by
  simp [P93RingAssemblyAxisFrameValid, axisPrintedAssignment,
    P93CanonicalRingAssemblyPrintedAxisAssignment.record, axisJunction, axisAssembly,
    axisRing0, axisRing1, P93AuthorityBinaryBond, axisSource,
    alternatingSixRingBonds, bond, P93AuthorityBinaryInteractionKind]

theorem axisPrinted_valid : axisPrinted.ValidFor axisSource := by
  refine ⟨rfl, axisAssembly_valid, by decide, by decide, by decide, ?_⟩
  intro assignment assignmentMem
  have assignmentEq : assignment = axisPrintedAssignment := by simpa [axisPrinted] using assignmentMem
  subst assignment
  exact ⟨by simp [axisPrinted, axisAssembly, axisPrintedAssignment], axisFrame_valid, rfl, rfl, rfl,
    by trivial, by simp [axisPrintedAssignment, citation, P93AuthorityCitationToken.Valid]⟩

theorem axisGeometry_exact :
    BlueBookP93.GeometryIngress.RationalAxialObservationJudgment
      axisNormalization.result axisSpatial axisAssignment.record axisAssignment.cipDescriptor := by
  refine ⟨5, 11,
    { x := 0, y := 0, z := 0 }, { x := 1, y := 0, z := 0 },
    { x := 0, y := 1, z := 0 }, { x := 1, y := 0, z := -1 }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact Or.inr ⟨axisStartPriority_exact, rfl⟩
  · exact Or.inr ⟨axisEndPriority_exact, rfl⟩
  · simp [BlueBookP93.GeometryIngress.SpatialPointAt, axisAssignment,
      axisPrintedAssignment, P93CanonicalRingAssemblyPrintedAxisAssignment.record,
      axisJunction, axisSpatial, axisSource]
  · simp [BlueBookP93.GeometryIngress.SpatialPointAt, axisAssignment,
      axisPrintedAssignment, P93CanonicalRingAssemblyPrintedAxisAssignment.record,
      axisJunction, axisSpatial, axisSource]
  · simp [BlueBookP93.GeometryIngress.SpatialPointAt, axisSpatial, axisSource]
  · simp [BlueBookP93.GeometryIngress.SpatialPointAt, axisSpatial, axisSource]
  · norm_num [axisAssignment,
      RationalAxialSpatialDescriptor, CartesianPoint3.axialChiralityMeasure,
      CartesianPoint3.displacement, RationalVector3.dot, RationalVector3.cross]

theorem axisExecutable_valid : axisExecutable.ValidFor axisSource axisPrinted := by
  refine ⟨rfl, ?_, rfl, rfl, ?_⟩
  · exact ⟨axisRaw_converted, rfl⟩
  · intro assignment assignmentMem
    have assignmentEq : assignment = axisAssignment := by simpa [axisExecutable] using assignmentMem
    subst assignment
    exact ⟨rfl, axisGeometry_exact⟩

def axisPayload : P93RingAssemblyClausePayload .axes := .axes axisPrinted axisExecutable

theorem axisPayload_valid :
    (P93ClausePayloadData.ringAssembly axisPayload).ValidFor axisSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, axisPayload, axisPrinted,
      P93RingAssemblyClausePayload.toClaims, axisPrintedAssignment] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl
    · exact axisAssembly_valid
    · exact ⟨axisAssembly_valid, by simp [axisAssembly]⟩
    · exact ⟨axisAssembly_valid, by simp [axisAssembly],
        by simp [citation, P93AuthorityCitationToken.Valid]⟩
    · exact ⟨axisAssembly_valid, by simp [axisAssembly], by trivial, Or.inl rfl⟩
  · exact ⟨axisPrinted_valid, axisExecutable_valid⟩

def axisObservation : P93ClauseObservation axisSource (.ringAssembly .axes) where
  payload := .ringAssembly axisPayload
  validFor := axisPayload_valid

def axisTranscription : P93CanonicalSourceTranscription axisSource
    (.ringAssembly .axes) axisObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 83
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.7.1"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.7.1"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "First page-83 dinitro-biphenyl example: preferred (1M), general (1Ra). The source prints a structure, not Cartesian coordinates; axisSpatial is an explicitly disclaimed exact rational reconstruction."
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact claimTranscription
      "PDF page 83, P-93.5.7.1, first named biphenyl axis example and adjacent diagram"
      "The printed structure fixes axis 1, adjacent ring references 1/5 and 7/11, and descriptors (1M)/(1Ra); rational coordinates are reconstructed and are not printed source facts."
      (by decide) (by decide) claim

def axisEntry : P93CanonicalClauseObservationEntry where
  source := axisSource
  sourceAdmitted := axisSource_structurallyWellFormed
  clause := .ringAssembly .axes
  clauseListed := by decide
  observation := axisObservation
  transcription := axisTranscription

/-! ## P-93.5.7.2: stereogenic centers -/

/-- Full heavy-atom graph of
`(1S,1's,2S,4S,4'R)-4,4'-dimethyl-[1,1'-bi(cyclohexan)]-2-ol`: two disjoint
six-membered molecular rings joined by `0--6`, methyl carbons `12,13`, and hydroxy oxygen `14`.
-/
def centerSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 14 carbonAtom ++ [oxygenAtom]
      interactions := sixRingBonds 0 ++ sixRingBonds 6 ++
        [bond 0 6, bond 3 12, bond 9 13, bond 1 14] }

theorem centerSource_structurallyWellFormed : centerSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff centerSource).mp
    (by decide)

def centerRing0 : List Nat := [0, 1, 2, 3, 4, 5]
def centerRing1 : List Nat := [6, 7, 8, 9, 10, 11]

def centerJunction : P93RingAssemblyJunction where
  leftRingIndex := 0
  rightRingIndex := 1
  leftAtom := 0
  rightAtom := 6

def centerAssembly : P93AuthorityRingAssembly where
  rings := [centerRing0, centerRing1]
  junctions := [centerJunction]

theorem centerRing0_closed : P93AuthorityClosedCycle centerSource centerRing0 := by
  simp [P93AuthorityClosedCycle, P93AuthorityAtomsBounded, P93AuthorityConnectedPath,
    P93AuthorityBinaryBond, centerSource, centerRing0, sixRingBonds, bond,
    P93AuthorityBinaryInteractionKind, SemanticMolecule.atomCount]

theorem centerRing1_closed : P93AuthorityClosedCycle centerSource centerRing1 := by
  simp [P93AuthorityClosedCycle, P93AuthorityAtomsBounded, P93AuthorityConnectedPath,
    P93AuthorityBinaryBond, centerSource, centerRing1, sixRingBonds, bond,
    P93AuthorityBinaryInteractionKind, SemanticMolecule.atomCount]

theorem centerAssembly_connected : P93RingAssemblyConnected centerAssembly := by
  intro first firstBound second secondBound
  simp [centerAssembly] at firstBound secondBound
  interval_cases first <;> interval_cases second
  · exact ⟨[0], by decide, by simp [centerAssembly], rfl, rfl, by trivial⟩
  · exact ⟨[0, 1], by decide, by simp [centerAssembly], rfl, rfl, by
      simp [P93RingAssemblyIndexPath, P93RingAssemblyIndicesJoined,
        centerAssembly, centerJunction]⟩
  · exact ⟨[1, 0], by decide, by simp [centerAssembly], rfl, rfl, by
      simp [P93RingAssemblyIndexPath, P93RingAssemblyIndicesJoined,
        centerAssembly, centerJunction]⟩
  · exact ⟨[1], by decide, by simp [centerAssembly], rfl, rfl, by trivial⟩

theorem centerAssembly_valid : centerAssembly.MechanicallyValidFor centerSource := by
  unfold P93AuthorityRingAssembly.MechanicallyValidFor
  refine ⟨by decide, by decide, ?_, ?_, by decide, by decide, ?_,
    centerAssembly_connected⟩
  · intro ring ringMem
    simp [centerAssembly] at ringMem
    rcases ringMem with rfl | rfl
    · exact centerRing0_closed
    · exact centerRing1_closed
  · intro leftIndex leftRing leftLookup rightIndex rightRing rightLookup distinct
    have leftBound : leftIndex < 2 := by
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp leftLookup
      simpa [centerAssembly] using bound
    have rightBound : rightIndex < 2 := by
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp rightLookup
      simpa [centerAssembly] using bound
    interval_cases leftIndex <;> interval_cases rightIndex <;>
      simp [centerAssembly] at leftLookup rightLookup <;>
      subst leftRing <;> subst rightRing <;>
      simp_all [centerRing0, centerRing1, Finset.disjoint_left]
  · intro junction junctionMem
    simp [centerAssembly] at junctionMem
    subst junction
    simp [P93RingAssemblyJunction.ValidFor, centerAssembly, centerJunction,
      centerRing0, centerRing1, P93AuthorityBinaryBond, centerSource,
      sixRingBonds, bond, P93AuthorityBinaryInteractionKind]

theorem center0_exactlyOneRing :
    P93RingAssemblyCenterInExactlyOneRing centerAssembly 0 := by
  refine ⟨0, centerRing0, by simp [centerAssembly], by simp [centerRing0], ?_⟩
  intro otherIndex otherRing lookup member
  have otherBound : otherIndex < 2 := by
    obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp lookup
    simpa [centerAssembly] using bound
  interval_cases otherIndex
  · rfl
  · simp [centerAssembly] at lookup
    subst otherRing
    simp [centerRing1] at member

theorem center0_envelope :
    P93CanonicalPhysicalUnitEnvelope centerSource (.atomCenter 0) := by
  refine ⟨by decide, [1, 5, 6], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, centerSource, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, centerSource, sixRingBonds, bond,
        P93AuthorityBinaryInteractionKind]

def centerAssignment : P93RingAssemblyCenterAssignment where
  center := 0
  citation := citation 1
  preferredDescriptor := .S
  generalDescriptor? := none

def centerPayload : P93RingAssemblyClausePayload .centers :=
  .centers centerAssembly [centerAssignment]

theorem centerPayload_valid :
    (P93ClausePayloadData.ringAssembly centerPayload).ValidFor centerSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, centerPayload,
      P93RingAssemblyClausePayload.toClaims, centerAssignment] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl
    · exact centerAssembly_valid
    · exact ⟨centerAssembly_valid, by decide⟩
    · exact ⟨centerAssembly_valid, by decide,
        by simp [citation, P93AuthorityCitationToken.Valid]⟩
    · exact ⟨centerAssembly_valid, by decide⟩
  · exact ⟨centerAssembly_valid, by decide, by decide, by decide, by
      intro assignment assignmentMem
      have assignmentEq : assignment = centerAssignment := by simpa using assignmentMem
      subst assignment
      exact ⟨center0_exactlyOneRing, center0_envelope, by trivial,
        by simp [centerAssignment, citation, P93AuthorityCitationToken.Valid], trivial⟩⟩

def centerObservation : P93ClauseObservation centerSource (.ringAssembly .centers) where
  payload := .ringAssembly centerPayload
  validFor := centerPayload_valid

def centerTranscription : P93CanonicalSourceTranscription centerSource
    (.ringAssembly .centers) centerObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 84
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.7.2"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.7.2"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(1S,1's,2S,4S,4'R)-4,4'-dimethyl-[1,1'-bi(cyclohexan)]-2-ol (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact claimTranscription
      "PDF page 84, P-93.5.7.2, first named center example and adjacent structure"
      "The PIN prints the preferred 1S center assignment on the complete bi(cyclohexan)-2-ol example."
      (by decide) (by decide) claim

def centerEntry : P93CanonicalClauseObservationEntry where
  source := centerSource
  sourceAdmitted := centerSource_structurallyWellFormed
  clause := .ringAssembly .centers
  clauseListed := by decide
  observation := centerObservation
  transcription := centerTranscription

/-! ## P-93.5.7.3: a stereogenic double bond in an eight-membered ring -/

/-- Full heavy-atom graph of `(3Z)-[1,1'-bi(cyclooctan)]-3-ene (PIN)`. -/
def doubleSource : AuthoritativeChemicalInput where
  molecule :=
    { atoms := List.replicate 16 carbonAtom
      interactions := firstUnsaturatedEightRingBonds ++ eightRingBonds 8 ++ [bond 0 8] }

theorem doubleSource_structurallyWellFormed : doubleSource.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff doubleSource).mp
    (by decide)

def doubleRing0 : List Nat := [0, 1, 2, 3, 4, 5, 6, 7]
def doubleRing1 : List Nat := [8, 9, 10, 11, 12, 13, 14, 15]

def doubleJunction : P93RingAssemblyJunction where
  leftRingIndex := 0
  rightRingIndex := 1
  leftAtom := 0
  rightAtom := 8

def doubleAssembly : P93AuthorityRingAssembly where
  rings := [doubleRing0, doubleRing1]
  junctions := [doubleJunction]

theorem doubleRing0_closed : P93AuthorityClosedCycle doubleSource doubleRing0 := by
  simp [P93AuthorityClosedCycle, P93AuthorityAtomsBounded, P93AuthorityConnectedPath,
    P93AuthorityBinaryBond, doubleSource, doubleRing0, firstUnsaturatedEightRingBonds,
    eightRingBonds, bond,
    P93AuthorityBinaryInteractionKind, SemanticMolecule.atomCount]

theorem doubleRing1_closed : P93AuthorityClosedCycle doubleSource doubleRing1 := by
  simp [P93AuthorityClosedCycle, P93AuthorityAtomsBounded, P93AuthorityConnectedPath,
    P93AuthorityBinaryBond, doubleSource, doubleRing1, firstUnsaturatedEightRingBonds,
    eightRingBonds, bond,
    P93AuthorityBinaryInteractionKind, SemanticMolecule.atomCount]

theorem doubleAssembly_connected : P93RingAssemblyConnected doubleAssembly := by
  intro first firstBound second secondBound
  simp [doubleAssembly] at firstBound secondBound
  interval_cases first <;> interval_cases second
  · exact ⟨[0], by decide, by simp [doubleAssembly], rfl, rfl, by trivial⟩
  · exact ⟨[0, 1], by decide, by simp [doubleAssembly], rfl, rfl, by
      simp [P93RingAssemblyIndexPath, P93RingAssemblyIndicesJoined,
        doubleAssembly, doubleJunction]⟩
  · exact ⟨[1, 0], by decide, by simp [doubleAssembly], rfl, rfl, by
      simp [P93RingAssemblyIndexPath, P93RingAssemblyIndicesJoined,
        doubleAssembly, doubleJunction]⟩
  · exact ⟨[1], by decide, by simp [doubleAssembly], rfl, rfl, by trivial⟩

theorem doubleAssembly_valid : doubleAssembly.MechanicallyValidFor doubleSource := by
  unfold P93AuthorityRingAssembly.MechanicallyValidFor
  refine ⟨by decide, by decide, ?_, ?_, by decide, by decide, ?_,
    doubleAssembly_connected⟩
  · intro ring ringMem
    simp [doubleAssembly] at ringMem
    rcases ringMem with rfl | rfl
    · exact doubleRing0_closed
    · exact doubleRing1_closed
  · intro leftIndex leftRing leftLookup rightIndex rightRing rightLookup distinct
    have leftBound : leftIndex < 2 := by
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp leftLookup
      simpa [doubleAssembly] using bound
    have rightBound : rightIndex < 2 := by
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp rightLookup
      simpa [doubleAssembly] using bound
    interval_cases leftIndex <;> interval_cases rightIndex <;>
      simp [doubleAssembly] at leftLookup rightLookup <;>
      subst leftRing <;> subst rightRing <;>
      simp_all [doubleRing0, doubleRing1, Finset.disjoint_left]
  · intro junction junctionMem
    simp [doubleAssembly] at junctionMem
    subst junction
    simp [P93RingAssemblyJunction.ValidFor, doubleAssembly, doubleJunction,
      doubleRing0, doubleRing1, P93AuthorityBinaryBond, doubleSource,
      firstUnsaturatedEightRingBonds, eightRingBonds, bond,
      P93AuthorityBinaryInteractionKind]

theorem doubleBondInRing :
    P93RingAssemblyBondInRing doubleSource doubleAssembly 0 2 3 := by
  refine ⟨by decide, doubleRing0, by simp [doubleAssembly], by decide, by decide, ?_, ?_⟩
  · refine ⟨by decide, Or.inl ?_⟩
    decide
  · simp [P93AuthorityBinaryBond, doubleSource, eightRingBonds, bond,
      firstUnsaturatedEightRingBonds, P93AuthorityBinaryInteractionKind]

def doubleAssignment : P93RingAssemblyDoubleBondAssignment where
  ringIndex := 0
  first := 2
  second := 3
  citation := citation 3
  descriptor := .Z

def doublePayload : P93RingAssemblyClausePayload .doubleBonds :=
  .doubleBonds doubleAssembly [doubleAssignment]

theorem doublePayload_valid :
    (P93ClausePayloadData.ringAssembly doublePayload).ValidFor doubleSource := by
  constructor
  · intro claim claimMem
    simp [P93ClausePayloadData.toClaims, doublePayload,
      P93RingAssemblyClausePayload.toClaims, doubleAssignment] at claimMem
    rcases claimMem with rfl | rfl | rfl | rfl | rfl
    · exact doubleAssembly_valid
    · exact ⟨doubleAssembly_valid, doubleBondInRing⟩
    · exact ⟨doubleAssembly_valid, doubleBondInRing⟩
    · exact ⟨doubleAssembly_valid, doubleBondInRing,
        by simp [citation, P93AuthorityCitationToken.Valid]⟩
    · exact ⟨doubleAssembly_valid, doubleBondInRing⟩
  · exact ⟨doubleAssembly_valid, by decide, by decide, by decide, by
      intro assignment assignmentMem
      have assignmentEq : assignment = doubleAssignment := by simpa using assignmentMem
      subst assignment
      exact ⟨doubleBondInRing, by trivial,
        by simp [doubleAssignment, citation, P93AuthorityCitationToken.Valid]⟩⟩

def doubleObservation : P93ClauseObservation doubleSource (.ringAssembly .doubleBonds) where
  payload := .ringAssembly doublePayload
  validFor := doublePayload_valid

def doubleTranscription : P93CanonicalSourceTranscription doubleSource
    (.ringAssembly .doubleBonds) doubleObservation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 85
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.5.7.3"
  clauseSectionExact := rfl
  observationSubsection := "P-93.5.7.3"
  observationSubsectionNonempty := by decide
  printedObservation := "(3Z)-[1,1'-bi(cyclooctan)]-3-ene (PIN)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact claimTranscription
      "PDF page 85, P-93.5.7.3, first named example and adjacent structure"
      "The PIN prints the 3Z descriptor on the complete bi(cyclooctan)-3-ene example."
      (by decide) (by decide) claim

def doubleEntry : P93CanonicalClauseObservationEntry where
  source := doubleSource
  sourceAdmitted := doubleSource_structurallyWellFormed
  clause := .ringAssembly .doubleBonds
  clauseListed := by decide
  observation := doubleObservation
  transcription := doubleTranscription

def entries : List P93CanonicalClauseObservationEntry := [axisEntry, centerEntry, doubleEntry]

def coveredClauses : List P93Clause := entries.map (·.clause)

@[simp] theorem entries_length : entries.length = 3 := rfl

@[simp] theorem entries_clause_exact : entries.map (·.clause) =
    [.ringAssembly .axes, .ringAssembly .centers, .ringAssembly .doubleBonds] := rfl

theorem entry_sources_nodup : (entries.map fun entry => entry.source).Nodup := by
  decide

theorem entries_source_unique :
    ∀ first ∈ entries, ∀ second ∈ entries,
      first.source = second.source → first = second := by
  exact List.inj_on_of_nodup_map entry_sources_nodup

end P93CanonicalProgramRingAssembly
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramRingAssembly.centerPayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramRingAssembly.doublePayload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramRingAssembly.axisPayload_valid
