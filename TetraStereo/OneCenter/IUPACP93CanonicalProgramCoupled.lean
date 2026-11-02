import TetraStereo.OneCenter.IUPACP93CanonicalSourceClaims

set_option autoImplicit false
set_option maxRecDepth 4096

/-!
# Canonical P-93.6 rings-and-chains source entry

This module transcribes P-93.6 Example 5, the explicit case in which a multiplicative name is
not allowed.  The complete heavy-atom constitution carries the two stereogenic centers and both
alkene units printed in the PIN.  The coupled payload therefore records all four assignments,
not a representative subset, while `multiplicativeSelected = false` reflects the source's stated
failure of identical repeated parent structures and equal stereodescriptors.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Acyclic
open IUPACNormativeProvision

namespace P93CanonicalProgramCoupled

def carbon : PeriodicElement := ⟨6, by decide, by decide⟩
def oxygen : PeriodicElement := ⟨8, by decide, by decide⟩
def bromine : PeriodicElement := ⟨35, by decide, by decide⟩

def carbonAtom : SemanticAtom where element := carbon
def oxygenAtom : SemanticAtom where element := oxygen
def bromineAtom : SemanticAtom where element := bromine

def bond (left right : Nat) (order : Nat := 1) : SemanticInteraction where
  participants := [left, right]
  kind := .covalent order

def aromaticBond (left right : Nat) : SemanticInteraction where
  participants := [left, right]
  kind := .aromatic

def citation (value primes : Nat := 0) : P93AuthorityCitationToken where
  components := [{ value := value, primes := primes }]

def nameComponent (index : Nat) : P93CanonicalNameComponent :=
  { role := .parent, path := [index] }

def citedBase (unit : P93AuthorityPhysicalUnit) (locant componentIndex : Nat)
    (kind : UnitKind) (descriptor : Descriptor) : P93AcyclicBasePayload where
  unit := unit
  citation? := some (citation locant)
  component := nameComponent componentIndex
  kind := kind
  descriptor := descriptor

def uncitedBase (unit : P93AuthorityPhysicalUnit) (componentIndex : Nat)
    (kind : UnitKind) (descriptor : Descriptor) : P93AcyclicBasePayload where
  unit := unit
  citation? := none
  component := nameComponent componentIndex
  kind := kind
  descriptor := descriptor

/-! ## Complete constitution of P-93.6 Example 5

Atom layout follows the displayed structure from left to right.  Atoms `0` and `22` are the
printed `2R` and embedded `1S` centers; `11=12` and `14=15` are the two printed `E` units; atom
`13` is the central ether oxygen; and atom `27` is the bromine unique to the left parent.
-/

def source : AuthoritativeChemicalInput where
  molecule :=
    { atoms :=
        (List.replicate 28 carbonAtom).set 3 oxygenAtom |>.set 4 oxygenAtom
          |>.set 13 oxygenAtom |>.set 25 oxygenAtom |>.set 26 oxygenAtom
          |>.set 27 bromineAtom
      interactions :=
        [ bond 0 1, bond 0 2, bond 2 3 2, bond 2 4, bond 0 5, bond 0 27
        , aromaticBond 5 6, aromaticBond 6 7, aromaticBond 7 8
        , aromaticBond 8 9, aromaticBond 9 10, aromaticBond 10 5
        , bond 8 11, bond 11 12 2, bond 12 13, bond 13 14, bond 14 15 2
        , bond 15 16
        , aromaticBond 16 17, aromaticBond 17 18, aromaticBond 18 19
        , aromaticBond 19 20, aromaticBond 20 21, aromaticBond 21 16
        , bond 19 22, bond 22 23, bond 22 24, bond 24 25 2, bond 24 26 ] }

theorem source_structurallyWellFormed : source.StructurallyWellFormed := by
  exact (AuthoritativeChemicalInput.structurallyWellFormed?_eq_true_iff source).mp (by decide)

theorem leftCenter_envelope :
    P93CanonicalPhysicalUnitEnvelope source (.atomCenter 0) := by
  refine ⟨by decide, [1, 2, 5, 27], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, source, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, source, bond, P93AuthorityBinaryInteractionKind]

theorem rightCenter_envelope :
    P93CanonicalPhysicalUnitEnvelope source (.atomCenter 22) := by
  refine ⟨by decide, [19, 23, 24], by decide, by decide, ?_, ?_⟩
  · simp [P93AuthorityAtomsBounded, source, SemanticMolecule.atomCount]
  · intro neighbor member
    simp at member
    rcases member with rfl | rfl | rfl <;> left <;>
      simp [P93AuthorityBinaryBond, source, bond, P93AuthorityBinaryInteractionKind]

theorem leftDouble_envelope :
    P93CanonicalPhysicalUnitEnvelope source (.bond 11 12) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [P93AuthorityBinaryBond, source, bond, P93AuthorityBinaryInteractionKind]

theorem rightDouble_envelope :
    P93CanonicalPhysicalUnitEnvelope source (.bond 14 15) := by
  refine ⟨by decide, by decide, by decide, ?_⟩
  simp [P93AuthorityBinaryBond, source, bond, P93AuthorityBinaryInteractionKind]

def leftCenterBase : P93AcyclicBasePayload :=
  citedBase (.atomCenter 0) 2 0 .chiralCenter .R

def rightCenterBase : P93AcyclicBasePayload :=
  citedBase (.atomCenter 22) 1 1 .chiralCenter .S

def leftDoubleBase : P93AcyclicBasePayload :=
  uncitedBase (.bond 11 12) 2 .ordinaryDoubleBond .E

def rightDoubleBase : P93AcyclicBasePayload :=
  uncitedBase (.bond 14 15) 3 .ordinaryDoubleBond .E

def alkeneContext : CarbonDoubleBondContext where
  firstCarbonHasHydrogen := true
  secondCarbonHasHydrogen := true

def leftCenterPayload : P93AcyclicClausePayload .singleAcyclicCenter :=
  .single leftCenterBase true false [.stereochemical]

def rightCenterPayload : P93AcyclicClausePayload .singleAcyclicCenter :=
  .single rightCenterBase true false [.stereochemical]

def leftDoublePayload : P93AcyclicClausePayload .doubleBondEZCisTrans :=
  .ezCisTrans leftDoubleBase .preferredIUPACName alkeneContext

def rightDoublePayload : P93AcyclicClausePayload .doubleBondEZCisTrans :=
  .ezCisTrans rightDoubleBase .preferredIUPACName alkeneContext

theorem leftCenterBase_intrinsic : leftCenterBase.Intrinsic := by
  refine ⟨by simp [leftCenterBase, citedBase, nameComponent,
      P93CanonicalNameComponent.Valid], trivial, trivial, ?_⟩
  intro token tokenMem
  have tokenEq : token = citation 2 := by
    simpa [leftCenterBase, citedBase] using tokenMem.symm
  subst token
  simp [citation, P93AuthorityCitationToken.Valid]

theorem rightCenterBase_intrinsic : rightCenterBase.Intrinsic := by
  refine ⟨by simp [rightCenterBase, citedBase, nameComponent,
      P93CanonicalNameComponent.Valid], trivial, trivial, ?_⟩
  intro token tokenMem
  have tokenEq : token = citation 1 := by
    simpa [rightCenterBase, citedBase] using tokenMem.symm
  subst token
  simp [citation, P93AuthorityCitationToken.Valid]

theorem leftDoubleBase_intrinsic : leftDoubleBase.Intrinsic := by
  exact ⟨by simp [leftDoubleBase, uncitedBase, nameComponent,
      P93CanonicalNameComponent.Valid], trivial, trivial,
    by simp [leftDoubleBase, uncitedBase]⟩

theorem rightDoubleBase_intrinsic : rightDoubleBase.Intrinsic := by
  exact ⟨by simp [rightDoubleBase, uncitedBase, nameComponent,
      P93CanonicalNameComponent.Valid], trivial, trivial,
    by simp [rightDoubleBase, uncitedBase]⟩

theorem baseClaims_sourceEnvelope
    (base : P93AcyclicBasePayload)
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

theorem leftCenterPayload_valid :
    (P93ClausePayloadData.acyclic leftCenterPayload).ValidFor source := by
  constructor
  · intro claim claimMem
    simp only [P93ClausePayloadData.toClaims, leftCenterPayload,
      P93AcyclicClausePayload.toClaims, List.mem_append] at claimMem
    rcases claimMem with baseMem | specialMem
    · exact baseClaims_sourceEnvelope leftCenterBase leftCenter_envelope
        leftCenterBase_intrinsic (by trivial) claim baseMem
    · simp at specialMem
      subst claim
      exact ⟨leftCenter_envelope,
        by simp [leftCenterBase, citedBase, citation, P93AuthorityCitationToken.Valid],
        by simp [P93AcyclicAffixOrderConforms]⟩
  · exact ⟨leftCenterBase_intrinsic, Or.inl rfl,
      by simp [leftCenterBase, citedBase, SingleCenterLocantConforms],
      by simp [P93AcyclicAffixOrderConforms], by simp, by simp⟩

theorem rightCenterPayload_valid :
    (P93ClausePayloadData.acyclic rightCenterPayload).ValidFor source := by
  constructor
  · intro claim claimMem
    simp only [P93ClausePayloadData.toClaims, rightCenterPayload,
      P93AcyclicClausePayload.toClaims, List.mem_append] at claimMem
    rcases claimMem with baseMem | specialMem
    · exact baseClaims_sourceEnvelope rightCenterBase rightCenter_envelope
        rightCenterBase_intrinsic (by trivial) claim baseMem
    · simp at specialMem
      subst claim
      exact ⟨rightCenter_envelope,
        by simp [rightCenterBase, citedBase, citation, P93AuthorityCitationToken.Valid],
        by simp [P93AcyclicAffixOrderConforms]⟩
  · exact ⟨rightCenterBase_intrinsic, Or.inl rfl,
      by simp [rightCenterBase, citedBase, SingleCenterLocantConforms],
      by simp [P93AcyclicAffixOrderConforms], by simp, by simp⟩

theorem leftDoublePayload_valid :
    (P93ClausePayloadData.acyclic leftDoublePayload).ValidFor source := by
  constructor
  · intro claim claimMem
    simp only [P93ClausePayloadData.toClaims, leftDoublePayload,
      P93AcyclicClausePayload.toClaims, List.mem_append] at claimMem
    rcases claimMem with baseMem | contextMem
    · exact baseClaims_sourceEnvelope leftDoubleBase leftDouble_envelope
        leftDoubleBase_intrinsic (by trivial) claim baseMem
    · simp at contextMem
      subst claim
      exact leftDouble_envelope
  · exact ⟨leftDoubleBase_intrinsic, rfl,
      by simp [leftDoubleBase, uncitedBase, DescriptorRecommended], by
        intro impossible
        simp [leftDoubleBase, uncitedBase] at impossible⟩

theorem rightDoublePayload_valid :
    (P93ClausePayloadData.acyclic rightDoublePayload).ValidFor source := by
  constructor
  · intro claim claimMem
    simp only [P93ClausePayloadData.toClaims, rightDoublePayload,
      P93AcyclicClausePayload.toClaims, List.mem_append] at claimMem
    rcases claimMem with baseMem | contextMem
    · exact baseClaims_sourceEnvelope rightDoubleBase rightDouble_envelope
        rightDoubleBase_intrinsic (by trivial) claim baseMem
    · simp at contextMem
      subst claim
      exact rightDouble_envelope
  · exact ⟨rightDoubleBase_intrinsic, rfl,
      by simp [rightDoubleBase, uncitedBase, DescriptorRecommended], by
        intro impossible
        simp [rightDoubleBase, uncitedBase] at impossible⟩

def assignments : List P93CanonicalReviewedDescriptorEvidence :=
  [ .acyclicCenter leftCenterPayload
  , .acyclicDoubleBond leftDoublePayload
  , .acyclicDoubleBond rightDoublePayload
  , .acyclicCenter rightCenterPayload ]

def baseName : P93RingChainBaseName where
  tokens :=
    ["2-bromo-2-{4-[2-{[2-{4-(1-carboxyethyl)phenyl}ethen-1-yl]oxy}ethen-1-yl]phenyl}propanoic acid"]

/-- The reviewed name/constitution pair printed in P-93.6 Example 5.  The frozen records make this
certificate unusable for a different source graph; the canonical transcription below independently
binds the observation to the frozen Blue Book artifact and page. -/
def baseNameCertificate : P93RingChainReviewedBaseNameCertificate where
  frozenName := baseName
  frozenAtoms := source.molecule.atoms
  frozenInteractions := source.molecule.interactions

theorem baseNameCertificate_valid :
    baseNameCertificate.ValidFor source baseName := by
  exact ⟨by simp [baseName, P93RingChainBaseName.Valid],
    source_structurallyWellFormed, rfl, rfl, rfl⟩

def leftParent : P93RingChainRepeatedComponent where
  atoms := {0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 27}

def rightParent : P93RingChainRepeatedComponent where
  atoms := {14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26}

def repeatedComponents : List P93RingChainRepeatedComponent := [leftParent, rightParent]

/-- Every printed stereogenic assignment is owned by the parent structure that contains its
physical unit.  This makes the different `R`/`S` center descriptors a statement about the two
parents, not merely two unrelated assignments in the whole molecule. -/
def assignmentOwnerships : List P93RingChainAssignmentOwnership :=
  [ { assignmentIndex := 0, componentIndex := 0 }
  , { assignmentIndex := 1, componentIndex := 0 }
  , { assignmentIndex := 2, componentIndex := 1 }
  , { assignmentIndex := 3, componentIndex := 1 } ]

theorem repeatedComponents_valid :
    P93RingChainRepeatedComponentsValid source repeatedComponents := by
  unfold P93RingChainRepeatedComponentsValid
  refine ⟨by decide, by decide, ?_, ?_⟩
  · intro component componentMem
    simp [repeatedComponents] at componentMem
    rcases componentMem with rfl | rfl <;>
      simp [P93RingChainRepeatedComponent.ValidFor, leftParent, rightParent,
        source, SemanticMolecule.atomCount]
  · intro leftIndex left leftLookup rightIndex right rightLookup distinct
    have leftBound : leftIndex < 2 := by
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp leftLookup
      simpa [repeatedComponents] using bound
    have rightBound : rightIndex < 2 := by
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp rightLookup
      simpa [repeatedComponents] using bound
    interval_cases leftIndex <;> interval_cases rightIndex <;>
      simp [repeatedComponents] at leftLookup rightLookup <;>
      subst left <;> subst right <;>
      simp_all [leftParent, rightParent, Finset.disjoint_left]

def payload : P93CoupledClausePayload where
  reviewedBaseName := baseName
  baseNameCertificate := baseNameCertificate
  assignments := assignments
  multiplicativeSelected := false
  repeatedComponents := repeatedComponents
  componentCorrespondences := []
  assignmentOwnerships := assignmentOwnerships

theorem assignmentOwnerships_complete :
    P93CanonicalAssignmentOwnershipsComplete repeatedComponents assignments
      assignmentOwnerships := by
  unfold P93CanonicalAssignmentOwnershipsComplete
  refine ⟨by decide, ?_, ?_⟩
  · intro ownership ownershipMem
    simp [assignmentOwnerships] at ownershipMem
    rcases ownershipMem with rfl | rfl | rfl | rfl
    · refine ⟨.acyclicCenter leftCenterPayload, leftParent, by simp [assignments],
        by simp [repeatedComponents], ?_⟩
      simp [P93CanonicalAssignmentTouchesComponent,
        P93CanonicalReviewedDescriptorEvidence.unit,
        P93RingChainStereogenicUnit.ofAuthorityPhysical,
        leftCenterPayload, leftCenterBase, citedBase,
        P93RingChainStereogenicUnit.atoms, leftParent]
    · refine ⟨.acyclicDoubleBond leftDoublePayload, leftParent, by simp [assignments],
        by simp [repeatedComponents], ?_⟩
      simp [P93CanonicalAssignmentTouchesComponent,
        P93CanonicalReviewedDescriptorEvidence.unit,
        P93RingChainStereogenicUnit.ofAuthorityPhysical,
        leftDoublePayload, leftDoubleBase, uncitedBase,
        P93RingChainStereogenicUnit.atoms, leftParent, Finset.disjoint_left]
    · refine ⟨.acyclicDoubleBond rightDoublePayload, rightParent, by simp [assignments],
        by simp [repeatedComponents], ?_⟩
      simp [P93CanonicalAssignmentTouchesComponent,
        P93CanonicalReviewedDescriptorEvidence.unit,
        P93RingChainStereogenicUnit.ofAuthorityPhysical,
        rightDoublePayload, rightDoubleBase, uncitedBase,
        P93RingChainStereogenicUnit.atoms, rightParent]
    · refine ⟨.acyclicCenter rightCenterPayload, rightParent, by simp [assignments],
        by simp [repeatedComponents], ?_⟩
      simp [P93CanonicalAssignmentTouchesComponent,
        P93CanonicalReviewedDescriptorEvidence.unit,
        P93RingChainStereogenicUnit.ofAuthorityPhysical,
        rightCenterPayload, rightCenterBase, citedBase,
        P93RingChainStereogenicUnit.atoms, rightParent]
  · intro assignmentIndex assignment assignmentLookup componentIndex component componentLookup
      touches
    have assignmentBound : assignmentIndex < 4 := by
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp assignmentLookup
      simpa [assignments] using bound
    have componentBound : componentIndex < 2 := by
      obtain ⟨bound, _⟩ := List.getElem?_eq_some_iff.mp componentLookup
      simpa [repeatedComponents] using bound
    interval_cases assignmentIndex <;> interval_cases componentIndex <;>
      simp [assignments] at assignmentLookup <;> subst assignment <;>
      simp [repeatedComponents] at componentLookup <;> subst component <;>
      simp [P93CanonicalAssignmentTouchesComponent,
        P93CanonicalReviewedDescriptorEvidence.unit,
        leftCenterPayload, leftCenterBase, rightCenterPayload, rightCenterBase,
        leftDoublePayload, leftDoubleBase, rightDoublePayload, rightDoubleBase,
        citedBase, uncitedBase, P93RingChainStereogenicUnit.ofAuthorityPhysical,
        P93RingChainStereogenicUnit.atoms,
        leftParent, rightParent, Finset.disjoint_left] at touches ⊢ <;>
      simp [assignmentOwnerships]

theorem ownedDescriptorMismatch :
    P93CanonicalOwnedDescriptorMismatch assignments assignmentOwnerships := by
  refine ⟨{ assignmentIndex := 0, componentIndex := 0 }, by simp [assignmentOwnerships],
    { assignmentIndex := 3, componentIndex := 1 }, by simp [assignmentOwnerships], by decide,
    .acyclicCenter leftCenterPayload, .acyclicCenter rightCenterPayload,
    by simp [assignments], by simp [assignments], ?_⟩
  simp [P93CanonicalReviewedDescriptorEvidence.ringDescriptor,
    P93CanonicalReviewedDescriptorEvidence.descriptor,
    leftCenterPayload, leftCenterBase, rightCenterPayload, rightCenterBase, citedBase]

theorem componentNonisomorphism :
    ∃ leftOwnership ∈ assignmentOwnerships,
      ∃ rightOwnership ∈ assignmentOwnerships,
        leftOwnership.componentIndex ≠ rightOwnership.componentIndex ∧
          ∃ leftComponent rightComponent,
            repeatedComponents[leftOwnership.componentIndex]? = some leftComponent ∧
              repeatedComponents[rightOwnership.componentIndex]? = some rightComponent ∧
                P93RingChainComponentsConstitutionallyNonisomorphic
                  source leftComponent rightComponent := by
  refine ⟨{ assignmentIndex := 0, componentIndex := 0 }, by simp [assignmentOwnerships],
    { assignmentIndex := 3, componentIndex := 1 }, by simp [assignmentOwnerships],
    by decide, leftParent, rightParent, by simp [repeatedComponents],
    by simp [repeatedComponents], ?_⟩
  exact .atomCardinality (by decide)

theorem multiplicativeRejectionEvidence :
    P93CanonicalMultiplicativeRejectionEvidence source repeatedComponents assignments
      assignmentOwnerships :=
  { componentsValid := repeatedComponents_valid
    ownershipsComplete := assignmentOwnerships_complete
    descriptorMismatch := ownedDescriptorMismatch
    componentNonisomorphism := componentNonisomorphism }

theorem multiplicativeDecision :
    P93CanonicalMultiplicativeDecisionValid source repeatedComponents [] assignments
      assignmentOwnerships false :=
  .rejected multiplicativeRejectionEvidence

theorem assignment_valid
    (evidence : P93CanonicalReviewedDescriptorEvidence)
    (member : evidence ∈ assignments) : evidence.ValidFor source := by
  simp [assignments] at member
  rcases member with rfl | rfl | rfl | rfl
  · simpa [P93CanonicalReviewedDescriptorEvidence.ValidFor,
      P93CanonicalReviewedDescriptorEvidence.upstreamClaims] using leftCenterPayload_valid
  · simpa [P93CanonicalReviewedDescriptorEvidence.ValidFor,
      P93CanonicalReviewedDescriptorEvidence.upstreamClaims] using leftDoublePayload_valid
  · simpa [P93CanonicalReviewedDescriptorEvidence.ValidFor,
      P93CanonicalReviewedDescriptorEvidence.upstreamClaims] using rightDoublePayload_valid
  · simpa [P93CanonicalReviewedDescriptorEvidence.ValidFor,
      P93CanonicalReviewedDescriptorEvidence.upstreamClaims] using rightCenterPayload_valid

theorem assignment_unit_atoms_bounded
    (evidence : P93CanonicalReviewedDescriptorEvidence)
    (member : evidence ∈ assignments) :
    ∀ atom ∈ evidence.unit.atoms, atom < source.molecule.atomCount := by
  simp [assignments] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [P93CanonicalReviewedDescriptorEvidence.unit,
      P93RingChainStereogenicUnit.atoms,
      P93RingChainStereogenicUnit.ofAuthorityPhysical,
      leftCenterPayload, leftCenterBase,
      rightCenterPayload, rightCenterBase, leftDoublePayload, leftDoubleBase,
      rightDoublePayload, rightDoubleBase, citedBase, uncitedBase,
      source, SemanticMolecule.atomCount]

theorem assignment_citation_valid
    (evidence : P93CanonicalReviewedDescriptorEvidence)
    (member : evidence ∈ assignments) :
    ∀ token, token ∈ evidence.citation? → token.Valid := by
  simp [assignments] at member
  rcases member with rfl | rfl | rfl | rfl <;>
    simp [P93CanonicalReviewedDescriptorEvidence.citation?, leftCenterPayload,
      leftCenterBase, rightCenterPayload, rightCenterBase, leftDoublePayload,
      leftDoubleBase, rightDoublePayload, rightDoubleBase, citedBase, uncitedBase,
      citation, P93AuthorityCitationToken.Valid]

theorem payload_intrinsic : payload.Intrinsic source := by
  refine ⟨by simpa [payload] using baseNameCertificate_valid, by decide, by decide,
    by decide, ?_, ?_, ?_⟩
  · intro evidence member
    exact assignment_valid evidence (by simpa [payload] using member)
  · intro consumer consumerMem producer producerMem fact factMem
    simp [payload, assignments] at consumerMem producerMem
    rcases consumerMem with rfl | rfl | rfl | rfl <;>
      rcases producerMem with rfl | rfl | rfl | rfl <;>
      simp [P93CanonicalReviewedDescriptorEvidence.closedWorldFacts] at factMem
  · simpa [payload] using multiplicativeDecision

theorem payload_valid : (P93ClausePayloadData.coupled payload).ValidFor source := by
  refine ⟨?_, payload_intrinsic⟩
  intro claim claimMem
  change claim ∈ payload.toClaims at claimMem
  rw [P93CoupledClausePayload.toClaims] at claimMem
  rcases List.mem_append.mp claimMem with beforeTerminal | terminal
  · rcases List.mem_append.mp beforeTerminal with base | nested
    · simp only [List.mem_singleton] at base
      subst claim
      simpa [P93SourceClaim.SourceEnvelope, P93CoupledClaim.SourceEnvelope, payload] using
        baseNameCertificate_valid
    · rcases List.mem_flatMap.mp nested with ⟨evidence, evidenceMem, evidenceClaim⟩
      have evidenceValid := assignment_valid evidence (by simpa [payload] using evidenceMem)
      have atomsBounded :=
        assignment_unit_atoms_bounded evidence (by simpa [payload] using evidenceMem)
      have citationsValid :=
        assignment_citation_valid evidence (by simpa [payload] using evidenceMem)
      rcases List.mem_append.mp evidenceClaim with upstreamOrOwn | citationMem
      · rcases List.mem_append.mp upstreamOrOwn with upstream | own
        · exact evidenceValid.1 claim upstream
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at own
          rcases own with rfl | rfl
          · exact ⟨by simp [payload, baseName, P93RingChainBaseName.Valid], atomsBounded⟩
          · exact ⟨by simp [payload, baseName, P93RingChainBaseName.Valid], by
              intro atom atomMem
              exact ⟨atomsBounded atom atomMem, citationsValid⟩⟩
      · rcases List.mem_map.mp citationMem with ⟨token, tokenMem, claimEq⟩
        subst claim
        exact ⟨by simp [payload, baseName, P93RingChainBaseName.Valid],
          citationsValid token (by simpa using tokenMem), atomsBounded⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at terminal
    rcases terminal with rfl | rfl
    · exact ⟨by simp [payload, baseName, P93RingChainBaseName.Valid],
        by simpa [payload] using repeatedComponents_valid⟩
    · simp [P93SourceClaim.SourceEnvelope, P93CoupledClaim.SourceEnvelope,
        payload, baseName, P93RingChainBaseName.Valid]

def observation : P93ClauseObservation source (.coupledRingChain .configurations) where
  payload := .coupled payload
  validFor := payload_valid

def transcription : P93CanonicalSourceTranscription source
    (.coupledRingChain .configurations) observation where
  normativeSource := .blueBook2013P9
  sourceIsBlueBookP9 := rfl
  artifactSha256 := "9fa1a8372b44d039f61edeed72c9b23be341d21c789447f793a392852afbe450"
  artifactSha256Exact := rfl
  pdfPage := 87
  pdfPagePositive := by decide
  pdfPageWithinFrozenArtifact := by decide
  clauseSection := "P-93.6"
  clauseSectionExact := rfl
  observationSubsection := "P-93.6, Example 5"
  observationSubsectionNonempty := by decide
  printedObservation :=
    "(2R)-2-bromo-2-{4-[(E)-2-{[(E)-2-{4-[(1S)-1-carboxyethyl]phenyl}ethen-1-yl]oxy}ethen-1-yl]phenyl}propanoic acid (PIN; a multiplicative name is not allowed, because of the different stereodescriptors and nonidentical repeated parent structures)"
  printedObservationNonempty := by decide
  claimTranscriptions := by
    intro claim _
    exact
      { supportingLocator := "PDF page 87, P-93.6, Example 5, name and adjacent structure"
        supportingLocatorNonempty := by decide
        supportingObservation :=
          "(2R)-2-bromo-2-{4-[(E)-2-{[(E)-2-{4-[(1S)-1-carboxyethyl]phenyl}ethen-1-yl]oxy}ethen-1-yl]phenyl}propanoic acid; multiplicative name not allowed"
        supportingObservationNonempty := by decide
        mode := .textAndFigure }

def entry : P93CanonicalClauseObservationEntry where
  source := source
  sourceAdmitted := source_structurallyWellFormed
  clause := .coupledRingChain .configurations
  clauseListed := by decide
  observation := observation
  transcription := transcription

def entries : List P93CanonicalClauseObservationEntry := [entry]

@[simp] theorem entries_length : entries.length = 1 := rfl

@[simp] theorem entries_clause_exact : entries.map (·.clause) =
    Remaining71P93CoupledRingChainAuthorityRow.all.map
      (fun row => (.coupledRingChain row : P93Clause)) := rfl

end P93CanonicalProgramCoupled
end TetraStereo.OneCenter

assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramCoupled.payload_valid
assert_kernel_only TetraStereo.OneCenter.P93CanonicalProgramCoupled.entries_clause_exact
