import TetraStereo.OneCenter.IUPACP93CanonicalSourceClaims
import TetraStereo.OneCenter.IUPACRemaining56P93ReviewedNonvacuity

set_option autoImplicit false

/-!
# Canonical P-93 source-policy compiler

This module compiles the finite canonical source program into the authority-policy relations used
by the 56 reviewed P-93 rows.  Source identity is inverted through
`P93CanonicalSourceProgram.observationSourceUnique`; physical relations are witnessed only by the
separate audited physical-support table.  Coupled nested evidence uses one proof-dependent erasure,
so no legacy evidence can be synthesized from an ill-formed canonical constructor.

General-configuration authority is bound to **whole** configurations actually carried by one
dependent general-clause payload.  It is deliberately not derived from a union of per-unit claims:
`(R,R)` and `(S,S)` payloads never authorize the pointwise configuration `(R,S)`.  Physical
descriptor computation and paired-configuration correlation remain separate obligations in the
reviewed `Judged` relations.

The clause-indexed legacy observations, their `ValidFor` proofs (including the four closed-world
coupled cases), exhaustive 56-row dispatch, and final global nonvacuity transport intentionally
belong to the downstream observation compiler.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Acyclic
open BlueBookP93.Cyclic
open BlueBookP93.NoncarbonTetrahedra
open IUPACNormativeProvision

namespace P93CanonicalSourceProgram

def HasClaim
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily)
    (source : AuthoritativeChemicalInput)
    (claim : P93SourceClaim) : Prop :=
  ∃ entry ∈ program.observations,
    entry.source = source ∧ entry.clause.family = scope ∧
      claim ∈ entry.observation.auditClaims

def HasPhysicalSupport
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily)
    (source : AuthoritativeChemicalInput)
    (claim : P93PhysicalClaim) : Prop :=
  ∃ support ∈ program.physicalSupports,
    support.source = source ∧ support.clause.family = scope ∧
      support.claim = claim

theorem hasClaim_iff
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (claim : P93SourceClaim) :
    program.HasClaim entry.clause.family entry.source claim ↔
      claim ∈ entry.observation.auditClaims := by
  constructor
  · rintro ⟨other, otherMem, sourceEq, familyEq, claimMem⟩
    have entryEq : other = entry :=
      program.entry_eq_of_source_eq otherMem entryMem sourceEq familyEq
    subst other
    exact claimMem
  · intro claimMem
    exact ⟨entry, entryMem, rfl, rfl, claimMem⟩

theorem hasClaim_of_mem
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    {claim : P93SourceClaim}
    (claimMem : claim ∈ entry.observation.auditClaims) :
    program.HasClaim entry.clause.family entry.source claim :=
  (program.hasClaim_iff entryMem claim).2 claimMem

theorem hasPhysicalSupport_of_exact
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    {claim : P93PhysicalClaim}
    (claimMem : claim ∈ entry.exactQualitativePhysicalClaims) :
    program.HasPhysicalSupport entry.clause.family entry.source claim := by
  rcases program.exact_qualitative_support_for entryMem claimMem with
    ⟨support, supportMem, sourceEq, clauseEq, claimEq⟩
  exact ⟨support, supportMem, sourceEq,
    congrArg P93Clause.family clauseEq, claimEq⟩

/-! ## Whole-configuration source carriers for the general clauses -/

/-- The whole configurations actually carried by one dependent general-clause payload.

This closed, typed projection is the only source of general-configuration authorization.  It never
flattens a configuration into per-unit claims: a payload carrying the whole configuration `(R,R)`
yields `(R,R)` itself (together with its paired partner where the clause carries two
configurations), not the pointwise union of its unit claims.  A mixed configuration `(R,S)` built
only from claims appearing in `(R,R)` and `(S,S)` payloads is therefore not a member. -/
def P93GeneralClausePayload.wholeConfigurations
    {row : Remaining71P93GeneralAuthorityRow}
    (payload : P93GeneralClausePayload row) : List P93CanonicalGeneralConfiguration :=
  match payload with
  | .absolute configuration => [configuration]
  | .relative first second _ => [first, second]
  | .mixed configuration _ _ => [configuration]
  | .racemate mixture _ => [mixture.first, mixture.second]
  | .ambo _ mixture => [mixture.first, mixture.second]

/-- Extraction guards for the general payload projection.  They record the exact intended list for
each general row: whole configurations only, with the paired partner for the racemate and `ambo`
mixtures. -/
@[simp] theorem P93GeneralClausePayload.wholeConfigurations_absolute
    (configuration : P93CanonicalGeneralConfiguration) :
    P93GeneralClausePayload.wholeConfigurations (.absolute configuration) =
      [configuration] :=
  rfl

@[simp] theorem P93GeneralClausePayload.wholeConfigurations_relative
    (first second : P93CanonicalGeneralConfiguration)
    (leading : P93AuthorityLocatedAssignment P93CanonicalDescriptor) :
    P93GeneralClausePayload.wholeConfigurations (.relative first second leading) =
      [first, second] :=
  rfl

@[simp] theorem P93GeneralClausePayload.wholeConfigurations_mixed
    (configuration : P93CanonicalGeneralConfiguration)
    (plan : P93CanonicalGeneralScopePlan)
    (observedTypography : List
      (P93AuthorityCitationToken × GeneralConfiguration.DescriptorTypography)) :
    P93GeneralClausePayload.wholeConfigurations
        (.mixed configuration plan observedTypography) =
      [configuration] :=
  rfl

@[simp] theorem P93GeneralClausePayload.wholeConfigurations_racemate
    (mixture : GeneralConfiguration.BinaryMixture P93CanonicalGeneralConfiguration)
    (leading : P93AuthorityLocatedAssignment P93CanonicalDescriptor) :
    P93GeneralClausePayload.wholeConfigurations (.racemate mixture leading) =
      [mixture.first, mixture.second] :=
  rfl

@[simp] theorem P93GeneralClausePayload.wholeConfigurations_ambo
    (citation : P93AuthorityCitationToken)
    (mixture : GeneralConfiguration.QualitativeBinaryMixture
      P93CanonicalGeneralConfiguration) :
    P93GeneralClausePayload.wholeConfigurations (.ambo citation mixture) =
      [mixture.first, mixture.second] :=
  rfl

/-- The actual general configurations carried by one canonical clause-observation entry.

The clause projection is eliminated *together with* the dependent payload, so the `.general`
pattern on the payload is typed at the clause it actually refines rather than at the opaque
projection `entry.clause`.  Only a dependent `.general` payload carries whole configurations;
every other family payload carries none.  The list is read directly out of the payload, so it
cannot be enlarged by per-unit claims. -/
def P93CanonicalClauseObservationEntry.wholeConfigurations
    (entry : P93CanonicalClauseObservationEntry) : List P93CanonicalGeneralConfiguration :=
  match entry.clause, entry.observation.payload with
  | .general _, .general payload => P93GeneralClausePayload.wholeConfigurations payload
  | _, _ => []

/-- Entry-level extraction guard: for an entry whose clause is literally the listed general row and
whose payload is the dependent `.general` constructor, the entry projection is exactly the payload's
whole-configuration list. -/
theorem P93CanonicalClauseObservationEntry.wholeConfigurations_general
    (source : AuthoritativeChemicalInput)
    (sourceAdmitted : source.StructurallyWellFormed)
    (row : Remaining71P93GeneralAuthorityRow)
    (clauseListed : (.general row) ∈ P93Clause.all)
    (sourceObservation : P93ClauseObservation source (.general row))
    (transcription : P93CanonicalSourceTranscription source (.general row) sourceObservation)
    (payload : P93GeneralClausePayload row)
    (payloadEq : sourceObservation.payload = .general payload) :
    P93CanonicalClauseObservationEntry.wholeConfigurations
        ⟨source, sourceAdmitted, (.general row), clauseListed, sourceObservation,
          transcription⟩ =
      P93GeneralClausePayload.wholeConfigurations payload := by
  simp [P93CanonicalClauseObservationEntry.wholeConfigurations, payloadEq]

def physicalPolicy
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) : P93AuthorityPhysicalObservationPolicy where
  HelixIdentified source path frame :=
    program.HasPhysicalSupport scope source (.helix path frame)
  PlanarRestrictionAndAsymmetryObserved source members frame :=
    program.HasPhysicalSupport scope source (.plane members frame)
  PolyhedralQualitativeFrameObserved source center positions geometry frame :=
    program.HasPhysicalSupport scope source (.polyhedron center positions geometry frame)

def generalPolicy
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) : P93GeneralAuthorityPolicy where
  Descriptor := P93CanonicalDescriptor
  mirrorAction := P93CanonicalDescriptor.mirrorAction
  localAction := P93CanonicalDescriptor.localAction
  RepresentativeEligible := P93CanonicalDescriptor.GeneralRepresentativeEligible
  representativeEligible_mirror_iff :=
    P93CanonicalDescriptor.representativeEligible_mirror_iff
  PreferredAtLowest := P93CanonicalDescriptor.PreferredAtLowest
  mirrorPreferredAtLowest := P93CanonicalDescriptor.mirrorPreferredAtLowest
  physicalObservation := program.physicalPolicy scope
  CitationAuthorized source citation unit :=
    program.HasClaim scope source (.general (.citation citation unit))
  DescriptorAuthorized source unit descriptor :=
    program.HasClaim scope source (.general (.descriptor unit descriptor)) ∨
      program.HasClaim scope source
        (.general (.descriptor unit descriptor.mirror))
  descriptorAuthorized_mirror_iff source unit descriptor := by
    change
      (program.HasClaim scope source (.general (.descriptor unit descriptor.mirror)) ∨
        program.HasClaim scope source (.general (.descriptor unit descriptor.mirror.mirror))) ↔ _
    rw [P93CanonicalDescriptor.mirror_mirror]
    exact or_comm
  ConfigurationAuthorized source configuration :=
    ∃ entry ∈ program.observations,
      entry.source = source ∧ entry.clause.family = scope ∧
        configuration ∈ P93CanonicalClauseObservationEntry.wholeConfigurations entry

/-- The compiled policy's local action is the canonical `localInvert` table. -/
@[simp] theorem generalPolicy_localAction_mirror
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily)
    (descriptor : P93CanonicalDescriptor) :
    (program.generalPolicy scope).localAction.mirror descriptor =
      P93CanonicalDescriptor.localInvert descriptor :=
  rfl

/-- The generic compiled one-citation inversion is exactly the canonical `ambo` inversion, so
the generic policy API and the canonical payload witness use the same local descriptor action
and the same retained units and citations. -/
theorem generalConfigurationInvertedAtCitation_eq_canonical
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily)
    (citation : P93AuthorityCitationToken)
    (configuration : P93CanonicalGeneralConfiguration) :
    p93GeneralConfigurationInvertedAtCitation (program.generalPolicy scope) citation
        configuration =
      P93CanonicalGeneralInvertAt citation configuration :=
  rfl

/-- Selected pseudoasymmetric local swaps at the compiled policy level.  Global reflection fixes
these descriptors; exchanging the two ligands at the stated centre swaps them. -/
theorem generalPolicy_localAction_acyclic_r
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) :
    (program.generalPolicy scope).localAction.mirror (.acyclic .r) = .acyclic .s :=
  rfl

theorem generalPolicy_localAction_acyclic_s
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) :
    (program.generalPolicy scope).localAction.mirror (.acyclic .s) = .acyclic .r :=
  rfl

theorem generalPolicy_localAction_fused_r
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) :
    (program.generalPolicy scope).localAction.mirror (.fused .r) = .fused .s :=
  rfl

theorem generalPolicy_localAction_fused_s
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) :
    (program.generalPolicy scope).localAction.mirror (.fused .s) = .fused .r :=
  rfl

theorem generalPolicy_localAction_ringAssemblyCenter_r
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) :
    (program.generalPolicy scope).localAction.mirror (.ringAssemblyCenter .r) =
      .ringAssemblyCenter .s :=
  rfl

theorem generalPolicy_localAction_ringAssemblyCenter_s
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) :
    (program.generalPolicy scope).localAction.mirror (.ringAssemblyCenter .s) =
      .ringAssemblyCenter .r :=
  rfl

/-- Double local inversion of a canonical configuration is the identity. -/
theorem P93CanonicalGeneralInvertAt_involutive
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily)
    (citation : P93AuthorityCitationToken)
    (configuration : P93CanonicalGeneralConfiguration) :
    P93CanonicalGeneralInvertAt citation
        (P93CanonicalGeneralInvertAt citation configuration) =
      configuration := by
  have inverted := p93GeneralConfigurationInvertedAtCitation_involutive
    (program.generalPolicy scope) citation configuration
  simpa only [generalConfigurationInvertedAtCitation_eq_canonical] using inverted

/-- The canonical inversion is the identity when no assignment carries the selected citation. -/
theorem P93CanonicalGeneralInvertAt_eq_self_of_absent
    (citation : P93AuthorityCitationToken)
    (configuration : P93CanonicalGeneralConfiguration)
    (absent : ∀ assignment ∈ configuration.assignments,
      assignment.citation ≠ citation) :
    P93CanonicalGeneralInvertAt citation configuration = configuration := by
  apply P93AuthorityConfiguration.ext
  simp only [P93CanonicalGeneralInvertAt]
  trans configuration.assignments.map id
  · apply List.map_congr_left
    intro assignment member
    simp [absent assignment member]
  · exact List.map_id configuration.assignments

/-- Whole-configuration authorization produced constructively from the one actual general-clause
entry that carries the payload.  The entry is presented with its clause already specialized to the
row, so the equality against its dependent payload is a genuine typed equality; neither a per-unit
claim union nor a caller-supplied correctness premise is involved. -/
theorem generalConfigurationAuthorized_of_generalPayload
    (program : P93CanonicalSourceProgram)
    (source : AuthoritativeChemicalInput)
    (sourceAdmitted : source.StructurallyWellFormed)
    (row : Remaining71P93GeneralAuthorityRow)
    (clauseListed : (.general row) ∈ P93Clause.all)
    (sourceObservation : P93ClauseObservation source (.general row))
    (transcription : P93CanonicalSourceTranscription source (.general row) sourceObservation)
    (payload : P93GeneralClausePayload row)
    (payloadEq : sourceObservation.payload = .general payload)
    (entryMem :
      (⟨source, sourceAdmitted, (.general row), clauseListed, sourceObservation,
        transcription⟩ : P93CanonicalClauseObservationEntry) ∈ program.observations)
    {configuration : P93CanonicalGeneralConfiguration}
    (mem : configuration ∈ P93GeneralClausePayload.wholeConfigurations payload) :
    (program.generalPolicy .general).ConfigurationAuthorized source configuration := by
  change ∃ entry ∈ program.observations,
    entry.source = source ∧ entry.clause.family = .general ∧
      configuration ∈ P93CanonicalClauseObservationEntry.wholeConfigurations entry
  refine ⟨⟨source, sourceAdmitted, (.general row), clauseListed, sourceObservation,
    transcription⟩, entryMem, rfl, rfl, ?_⟩
  simpa [P93CanonicalClauseObservationEntry.wholeConfigurations, payloadEq] using mem

def noncarbonPolicy
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) : P93NoncarbonTetrahedralAuthorityPolicy where
  Descriptor := P93CanonicalDescriptor
  TetrahedralArrangementObserved source center ligands :=
    program.HasClaim scope source (.noncarbon (.tetrahedral center ligands))
  CitationAuthorized source citation unit :=
    program.HasClaim scope source (.noncarbon (.citation citation unit))
  DescriptorAuthorized source unit descriptor :=
    program.HasClaim scope source (.noncarbon (.descriptor unit descriptor))
  OxideBondingVariantAuthorized source center oxygen family bonding :=
    program.HasClaim scope source
      (.noncarbon (.oxideVariant center oxygen family bonding))
  PhosphorusOxoVariantAuthorized source center oxygen family double charges :=
    program.HasClaim scope source
      (.noncarbon (.phosphorusOxo center oxygen family double charges))
  ChalcogenOxoVariantAuthorized source center oxygen family double charges :=
    program.HasClaim scope source
      (.noncarbon (.chalcogenOxo center oxygen family double charges))

def acyclicPolicy
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) : P93AcyclicAuthorityPolicy where
  Component := P93CanonicalNameComponent
  physicalObservation := program.physicalPolicy scope
  CitationAuthorized source citation unit :=
    program.HasClaim scope source (.acyclic (.citation citation unit))
  ComponentAuthorized source component unit :=
    program.HasClaim scope source (.acyclic (.component component unit))
  AcyclicUnitObserved source unit :=
    program.HasClaim scope source (.acyclic (.unit unit))
  UnitKindObserved source unit kind :=
    program.HasClaim scope source (.acyclic (.unitKind unit kind))
  DescriptorAuthorized source unit descriptor :=
    program.HasClaim scope source (.acyclic (.descriptor unit descriptor))
  CarbonDoubleBondContextObserved source unit context :=
    program.HasClaim scope source (.acyclic (.carbonDoubleBondContext unit context))
  SingleCenterNamingObserved source unit citation needsLocant isotopePresent affixes :=
    program.HasClaim scope source
      (.acyclic (.singleCenterNaming unit citation needsLocant isotopePresent affixes))
  OddCumuleneTerminalGeometryObserved source path geometry :=
    program.HasClaim scope source (.acyclic (.oddCumuleneGeometry path geometry))
  MultipleCenterDescriptorsAuthorized source assignments :=
    program.HasClaim scope source (.acyclic (.multipleCenterDescriptors assignments))
  MultipleDoubleBondDescriptorsAuthorized source assignments :=
    program.HasClaim scope source (.acyclic (.multipleDoubleBondDescriptors assignments))
  NumberingCompetitionObserved source units competition :=
    program.HasClaim scope source (.acyclic (.numberingCompetition units competition))

def monocyclicPolicy
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) : P93MonocyclicAuthorityPolicy where
  GeneralDescriptor := P93CanonicalDescriptor
  physicalObservation := program.physicalPolicy scope
  CitationAuthorized source citation unit :=
    program.HasClaim scope source (.monocyclic (.citation citation unit))
  MonocyclicRingObserved source atoms :=
    program.HasClaim scope source (.monocyclic (.ring atoms))
  UnitInRingSystemObserved source atoms unit :=
    program.HasClaim scope source (.monocyclic (.unitInRing atoms unit))
  GeneralDescriptorAuthorized source unit descriptor :=
    program.HasClaim scope source (.monocyclic (.generalDescriptor unit descriptor))
  CenterKindObserved source center kind :=
    ∃ descriptor knowledge notationValue,
      program.HasClaim scope source
        (.monocyclic (.center center kind descriptor knowledge notationValue))
  CenterDescriptorAuthorized source center descriptor :=
    ∃ kind knowledge notationValue,
      program.HasClaim scope source
        (.monocyclic (.center center kind descriptor knowledge notationValue))
  CenterConfigurationKnowledgeObserved source center knowledge :=
    ∃ kind descriptor notationValue,
      program.HasClaim scope source
        (.monocyclic (.center center kind descriptor knowledge notationValue))
  MonocycleNotationObserved source unit knowledge notationValue :=
    program.HasClaim scope source (.monocyclic (.generalNotation unit knowledge notationValue)) ∨
      ∃ center kind descriptor,
        unit = .atomCenter center ∧
          program.HasClaim scope source
            (.monocyclic (.center center kind descriptor knowledge notationValue))
  AchiralMonocyclicCenterObserved source center :=
    program.HasClaim scope source (.monocyclic (.achiralCenter center))
  RingPlaneObserved source atoms first second plane :=
    program.HasClaim scope source (.monocyclic (.ringPlane atoms first second plane))
  RingLigandSideObserved source atoms ligand side :=
    program.HasClaim scope source (.monocyclic (.ringSide atoms ligand side))
  RCTReferenceCandidateObserved source atoms position substituent citation suffix priority :=
    program.HasClaim scope source
      (.monocyclic (.rctCandidate atoms position substituent citation suffix priority))
  CyclicUnsaturationObserved source atoms unit topology count :=
    program.HasClaim scope source (.monocyclic (.unsaturation atoms unit topology count))
  MonocyclicSeniorLigandGeometryObserved source unit geometry :=
    program.HasClaim scope source (.monocyclic (.seniorGeometry unit geometry))
  ChiralCycloalkeneDescriptorAuthorized source unit descriptor :=
    ∃ pin, program.HasClaim scope source
      (.monocyclic (.chiralCycloalkene unit descriptor pin))
  ChiralCycloalkeneNamingContextObserved source unit pin :=
    ∃ descriptor, program.HasClaim scope source
      (.monocyclic (.chiralCycloalkene unit descriptor pin))
  ExocyclicSystemObserved source atoms unit count opposite :=
    program.HasClaim scope source
      (.monocyclic (.exocyclicSystem atoms unit count opposite))
  ExocyclicNamingObservationAuthorized source unit pin method treatment descriptor :=
    program.HasClaim scope source
      (.monocyclic (.exocyclicNaming unit pin method treatment descriptor))

def vonBaeyerPolicy
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) : P93VonBaeyerAuthorityPolicy where
  physicalObservation := program.physicalPolicy scope
  SystemObserved source system :=
    program.HasClaim scope source (.vonBaeyer (.system system))
  UnitInSystemObserved source system unit :=
    program.HasClaim scope source (.vonBaeyer (.unit system unit))
  CitationAuthorized source citation unit :=
    program.HasClaim scope source (.vonBaeyer (.citation citation unit))
  CenterKindObserved source center kind :=
    ∃ descriptor knowledge notationValue, program.HasClaim scope source
      (.vonBaeyer (.center center kind descriptor knowledge notationValue))
  CenterDescriptorAuthorized source center descriptor :=
    ∃ kind knowledge notationValue, program.HasClaim scope source
      (.vonBaeyer (.center center kind descriptor knowledge notationValue))
  CenterConfigurationKnowledgeObserved source center knowledge :=
    ∃ kind descriptor notationValue, program.HasClaim scope source
      (.vonBaeyer (.center center kind descriptor knowledge notationValue))
  CenterNotationObserved source center knowledge notationValue :=
    ∃ kind descriptor, program.HasClaim scope source
      (.vonBaeyer (.center center kind descriptor knowledge notationValue))
  BridgeAttachmentObserved source system attachment substituent kind :=
    program.HasClaim scope source
      (.vonBaeyer (.bridgeAttachment system attachment substituent kind))
  BridgeheadLigandSideObserved source system bridgehead ligand side :=
    program.HasClaim scope source
      (.vonBaeyer (.bridgeheadSide system bridgehead ligand side))
  BridgeheadRelativeNotationObserved source system pin notationValue :=
    program.HasClaim scope source (.vonBaeyer (.relativeNotation system pin notationValue))
  LargerThanBicyclo333Observed source system value :=
    program.HasClaim scope source (.vonBaeyer (.largerThanBicyclo333 system value))
  SeniorLigandGeometryObserved source unit geometry :=
    program.HasClaim scope source (.vonBaeyer (.seniorGeometry unit geometry))
  OrdinaryDoubleBondNamingAuthorized source system unit pin larger descriptor :=
    program.HasClaim scope source
      (.vonBaeyer (.doubleBondNaming system unit pin larger descriptor))
  IncludedCumuleneNumberingObserved source system path citation :=
    program.HasClaim scope source
      (.vonBaeyer (.includedCumuleneNumbering system path citation))
  IncludedCumuleneNamingContextObserved source system unit context :=
    program.HasClaim scope source
      (.vonBaeyer (.includedCumuleneContext system unit context))

def spiroPolicy
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) : P93SpiroAuthorityPolicy where
  physicalObservation := program.physicalPolicy scope
  SystemObserved source system := program.HasClaim scope source (.spiro (.system system))
  UnitInSystemObserved source system unit :=
    program.HasClaim scope source (.spiro (.unit system unit))
  CitationAuthorized source citation unit :=
    program.HasClaim scope source (.spiro (.citation citation unit))
  SpiroPatternObserved source system pattern :=
    program.HasClaim scope source (.spiro (.pattern system pattern))
  CenterDescriptorAuthorized source system pattern family descriptor :=
    program.HasClaim scope source
      (.spiro (.centerDescriptor system pattern family descriptor))
  XababOccurrenceOrderObserved source system order :=
    program.HasClaim scope source (.spiro (.xababOrder system order))
  DoubleBondRingObserved source system unit ring :=
    program.HasClaim scope source (.spiro (.doubleBondRing system unit ring))
  DoubleBondGeometryObserved source unit geometry :=
    program.HasClaim scope source (.spiro (.doubleBondGeometry unit geometry))
  DoubleBondNamingAuthorized source system unit context descriptor :=
    program.HasClaim scope source (.spiro (.doubleBondNaming system unit context descriptor))
  CoordinationObserved source system positions coordination :=
    program.HasClaim scope source (.spiro (.coordination system positions coordination))
  PolyhedralDescriptorAuthorized source system positions knowledge descriptor :=
    program.HasClaim scope source
      (.spiro (.polyhedralDescriptor system positions knowledge descriptor))
  AxialCenterDescriptorAuthorized source system descriptor :=
    program.HasClaim scope source (.spiro (.axialCenterDescriptor system descriptor))
  AxialDescriptorAuthorized source system descriptor :=
    program.HasClaim scope source (.spiro (.axialDescriptor system descriptor))

def HasFusedCIP
    (program : P93CanonicalSourceProgram) (scope : P93ClaimFamily)
    (source : AuthoritativeChemicalInput) (observation : P93CanonicalFusedCIPObservation) : Prop :=
  program.HasClaim scope source (.fused (.cipObservation observation))

def HasFusedRelation
    (program : P93CanonicalSourceProgram) (scope : P93ClaimFamily)
    (source : AuthoritativeChemicalInput)
    (observation : P93CanonicalFusedRelationObservation) : Prop :=
  program.HasClaim scope source (.fused (.relationObservation observation))

def fusedPolicy
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) : P93FusedAuthorityPolicy where
  physicalObservation := program.physicalPolicy scope
  SystemObserved source system :=
    (∃ observation, program.HasFusedCIP scope source observation ∧
      observation.system = system) ∨
    (∃ observation, program.HasFusedRelation scope source observation ∧
      observation.system = system)
  UnitInSystemObserved source system unit :=
    ∃ observation, program.HasFusedCIP scope source observation ∧
      observation.system = system ∧ observation.unit = unit
  CitationAuthorized source citation unit :=
    ∃ observation, program.HasFusedCIP scope source observation ∧
      observation.citation = citation ∧ observation.unit = unit
  FusedAxisObserved source system path :=
    ∃ observation, program.HasFusedCIP scope source observation ∧
      observation.system = system ∧ observation.unit = .fusedAxis path
  UnitDescriptorAuthorized source system unit descriptor :=
    ∃ observation, program.HasFusedCIP scope source observation ∧
      observation.system = system ∧ observation.unit = unit ∧
        observation.descriptor = descriptor
  FusionPairEligible source system first second :=
    ∃ observation, program.HasFusedRelation scope source observation ∧
      observation.system = system ∧ ∃ evidence ∈ observation.candidates,
        evidence.candidate.firstFusionAtom = first ∧
          evidence.candidate.secondFusionAtom = second
  FusionPairCandidateObserved source system first second distance lower :=
    ∃ observation, program.HasFusedRelation scope source observation ∧
      observation.system = system ∧ ∃ evidence ∈ observation.candidates,
        evidence.candidate.firstFusionAtom = first ∧
          evidence.candidate.secondFusionAtom = second ∧
          evidence.candidate.graphDistance = distance ∧
          evidence.candidate.lowerAtomLocant = lower
  FusionPairCitationAuthorized source system first second citation :=
    ∃ observation, program.HasFusedRelation scope source observation ∧
      observation.system = system ∧
      observation.selected.candidate.firstFusionAtom = first ∧
      observation.selected.candidate.secondFusionAtom = second ∧
      observation.relation.citation = citation
  FusionRelationObserved source system first second firstJunction secondJunction relation :=
    ∃ observation, program.HasFusedRelation scope source observation ∧
      observation.system = system ∧
      observation.selected.candidate.firstFusionAtom = first ∧
      observation.selected.candidate.secondFusionAtom = second ∧
      observation.relation.firstJunction = firstJunction ∧
      observation.relation.secondJunction = secondJunction ∧
      observation.relation.legacyDescriptor = relation

def cyclophanePolicy
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) : P93CyclophaneAuthorityPolicy where
  physicalObservation := program.physicalPolicy scope
  SystemObserved source system := program.HasClaim scope source (.cyclophane (.system system))
  UnitInSystemObserved source system unit :=
    program.HasClaim scope source (.cyclophane (.unit system unit))
  CitationAuthorized source citation unit :=
    program.HasClaim scope source (.cyclophane (.citation citation unit))
  PlaneReferenceObserved source system unit reference :=
    program.HasClaim scope source (.cyclophane (.planeReference system unit reference))
  PlaneReferenceOrderObserved source system unit high low :=
    program.HasClaim scope source (.cyclophane (.planeOrder system unit high low))
  PlaneDescriptorAuthorized source system unit context descriptor :=
    program.HasClaim scope source
      (.cyclophane (.planeDescriptor system unit context descriptor))
  CenterKindObserved source system center kind :=
    ∃ context descriptor, program.HasClaim scope source
      (.cyclophane (.center system center kind context descriptor))
  CenterDescriptorAuthorized source system center context descriptor :=
    ∃ kind, program.HasClaim scope source
      (.cyclophane (.center system center kind context descriptor))
  RCTReferenceCenterEligible source system center :=
    program.HasClaim scope source (.cyclophane (.rctEligible system center))
  RCTReferenceCandidateObserved source system center citation suffix priority :=
    program.HasClaim scope source
      (.cyclophane (.rctCandidate system center citation suffix priority))
  RCTCenterSideObserved source system center side :=
    program.HasClaim scope source (.cyclophane (.rctSide system center side))
  DoubleBondRingObserved source system unit ring phaneRing :=
    program.HasClaim scope source
      (.cyclophane (.doubleBondRing system unit ring phaneRing))
  DoubleBondGeometryObserved source unit geometry :=
    program.HasClaim scope source (.cyclophane (.doubleBondGeometry unit geometry))
  CarbonDoubleBondContextObserved source unit context :=
    program.HasClaim scope source (.cyclophane (.carbonDoubleBondContext unit context))
  DoubleBondNamingAuthorized source system unit context descriptor :=
    program.HasClaim scope source
      (.cyclophane (.doubleBondNaming system unit context descriptor))

def HasFullerenePrintedObservation
    (program : P93CanonicalSourceProgram) (scope : P93ClaimFamily)
    (source : AuthoritativeChemicalInput)
    (observation : P93CanonicalFullerenePrintedObservation) : Prop :=
  program.HasClaim scope source (.fullerene (.printedObservation observation)) ∨
    program.HasClaim scope source (.fullerene (.printedSuperimposedObservation observation))

def HasFullereneObservation
    (program : P93CanonicalSourceProgram) (scope : P93ClaimFamily)
    (source : AuthoritativeChemicalInput)
    (observation : P93CanonicalFullereneObservation) : Prop :=
  ∃ printed, program.HasFullerenePrintedObservation scope source printed ∧
    printed.AgreesWith observation

def HasFullereneType4Observation
    (program : P93CanonicalSourceProgram) (scope : P93ClaimFamily)
    (source : AuthoritativeChemicalInput)
    (observation : P93CanonicalFullereneType4Observation) : Prop :=
  ∃ printed, program.HasFullerenePrintedObservation scope source printed ∧
    printed.AgreesWithType4 observation

def fullerenePolicy
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) : P93FullereneAuthorityPolicy where
  physicalObservation := program.physicalPolicy scope
  MethodologyRuleObserved source :=
    program.HasClaim scope source (.fullerene .methodologyDecisionRule)
  RawMoleculeObserved source molecule :=
    ∃ observation, program.HasFullerenePrintedObservation scope source observation ∧
      observation.molecule = molecule
  InputFamilyObserved source molecule inputs :=
    ∃ observation, program.HasFullereneObservation scope source observation ∧
      observation.molecule = molecule ∧ observation.inputs = inputs
  SubstitutionEvidenceObserved source molecule input evidence :=
    (∃ observation, program.HasFullereneObservation scope source observation ∧
      observation.molecule = molecule ∧ ∃ strictInput ∈ observation.inputs,
        strictInput.symmetryInput.cage = input ∧
          strictInput.symmetryInput.substitutionEvidence = evidence) ∨
    ∃ observation, program.HasFullereneType4Observation scope source observation ∧
      observation.molecule = molecule ∧ observation.input.cage = input ∧
        observation.input.substitutionEvidence = evidence
  PreferredNumberingSelected source input numbering :=
    ∃ observation, program.HasFullereneObservation scope source observation ∧
      ∃ strictInput ∈ observation.inputs,
        strictInput.symmetryInput.cage = input ∧ strictInput.numberingEvidence = numbering
  OriginalDerivativeChiralityObserved source input value :=
    (∃ observation, program.HasFullereneObservation scope source observation ∧
      ∃ strictInput ∈ observation.inputs,
        strictInput.symmetryInput.cage = input ∧
          strictInput.symmetryInput.substitutionEvidence.originalDerivativeChiral = value) ∨
    ∃ observation, program.HasFullereneType4Observation scope source observation ∧
      observation.input.cage = input ∧
        observation.input.substitutionEvidence.originalDerivativeChiral = value
  PrintedCageHandednessObserved source molecule input numberingKind handedness :=
    ∃ observation, program.HasFullerenePrintedObservation scope source observation ∧
      observation.molecule = molecule ∧ observation.cageCarrier = input.carrier ∧
      observation.substitutionTest = input.substitutionTest ∧
      observation.numberingKind? = some numberingKind ∧
      observation.handedness? = some handedness
  SubstituentUnitAtSiteEligible source molecule input evidence site unit :=
    ∃ observation, program.HasFullerenePrintedObservation scope source observation ∧
      observation.molecule = molecule ∧ observation.cageCarrier = input.carrier ∧
      observation.substitutionTest = input.substitutionTest ∧
      observation.chiralSubstituentSites = evidence.chiralSubstituentSites ∧
      ∃ entry ∈ observation.unitInventory,
        entry.substitutedSite = site ∧ entry.unit = unit
  SubstituentCitationAuthorized source input site citation unit :=
    ∃ observation, program.HasFullerenePrintedObservation scope source observation ∧
      observation.cageCarrier = input.carrier ∧
      observation.substitutionTest = input.substitutionTest ∧
      ∃ assignment ∈ observation.substituentAssignments,
        assignment.substitutedSite = site ∧ assignment.citation = citation ∧
          assignment.unit = unit
  SubstituentDescriptorAuthorized source input site unit descriptor :=
    ∃ observation, program.HasFullerenePrintedObservation scope source observation ∧
      observation.cageCarrier = input.carrier ∧
      observation.substitutionTest = input.substitutionTest ∧
      ∃ assignment ∈ observation.substituentAssignments,
        assignment.substitutedSite = site ∧ assignment.unit = unit ∧
          assignment.descriptor = descriptor




noncomputable def relationalFullerenePolicy
    (_program : P93CanonicalSourceProgram) : P93RelationalFullereneAuthorityPolicy :=
  P93CanonicalProgramFullerene.iupacP93CanonicalFullereneRelationalAuthorityPolicy

def ringAssemblyPolicy
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily) : P93RingAssemblyAuthorityPolicy where
  physicalObservation := program.physicalPolicy scope
  AssemblyObserved source assembly :=
    program.HasClaim scope source (.ringAssembly (.assembly assembly))
  AxisEligible source assembly junction :=
    program.HasClaim scope source (.ringAssembly (.axisEligible assembly junction))
  AxisCitationAuthorized source assembly junction citation :=
    program.HasClaim scope source
      (.ringAssembly (.axisCitation assembly junction citation))
  AxisDescriptorsObserved source assembly junction preferred general :=
    program.HasClaim scope source
      (.ringAssembly (.axisDescriptors assembly junction preferred general))
  CenterEligible source assembly center :=
    program.HasClaim scope source (.ringAssembly (.centerEligible assembly center))
  CenterCitationAuthorized source assembly center citation :=
    program.HasClaim scope source
      (.ringAssembly (.centerCitation assembly center citation))
  CenterCIPDescriptorAuthorized source assembly center descriptor :=
    program.HasClaim scope source
      (.ringAssembly (.centerDescriptor assembly center descriptor))
  CenterGeneralDescriptorEquivalent source assembly center preferred general :=
    program.HasClaim scope source
      (.ringAssembly (.centerGeneralEquivalent assembly center preferred general))
  DoubleBondStereogenic source assembly ringIndex first second :=
    program.HasClaim scope source
      (.ringAssembly (.doubleBondStereogenic assembly ringIndex first second))
  DoubleBondNeedsSpecificationUnderP9122 source assembly ringIndex first second :=
    program.HasClaim scope source
      (.ringAssembly (.doubleBondNeedsSpecification assembly ringIndex first second))
  DoubleBondCitationAuthorized source assembly ringIndex first second citation :=
    program.HasClaim scope source
      (.ringAssembly (.doubleBondCitation assembly ringIndex first second citation))
  DoubleBondDescriptorAuthorized source assembly ringIndex first second descriptor :=
    program.HasClaim scope source
      (.ringAssembly (.doubleBondDescriptor assembly ringIndex first second descriptor))

/-! ## Payload erasure into the reviewed observation carriers -/

def acyclicAssignment
    (base : P93AcyclicBasePayload)
    (program : P93CanonicalSourceProgram) (scope : P93ClaimFamily) :
    P93AcyclicAuthorityAssignment (program.acyclicPolicy scope) where
  unit := base.unit
  citation? := base.citation?
  component := base.component
  kind := base.kind
  descriptor := base.descriptor

def monocyclicPhysical
    (base : P93MonocyclicPhysicalPayload) : P93MonocyclicPhysicalUnit where
  ringAtoms := base.ring
  unit := base.unit

def fusedCIPObservation
    (observation : P93CanonicalFusedCIPObservation)
    (policy : P93FusedAuthorityPolicy) : P93FusedCIPAuthorityObservation policy where
  system := observation.system
  unit := observation.unit
  citation := observation.citation
  descriptor := observation.descriptor

/-- Erase one valid canonical nested-evidence value into its legacy dependent carrier.  Validity is
an input precisely because `cyclophaneCenterCIP`'s payload index alone still admits the wrong
specification constructor; the proof eliminates that impossible branch rather than fabricating an
observation. -/
def P93CanonicalReviewedDescriptorEvidence.toAuthority
    (program : P93CanonicalSourceProgram)
    (source : AuthoritativeChemicalInput)
    (evidence : P93CanonicalReviewedDescriptorEvidence)
    (valid : evidence.ValidFor source) :
    P93RingChainReviewedDescriptorEvidence
      { acyclic := program.acyclicPolicy .coupled
        monocyclic := program.monocyclicPolicy .coupled
        fused := program.fusedPolicy .coupled
        cyclophane := program.cyclophanePolicy .coupled
        spiro := program.spiroPolicy .coupled
        ringAssembly := program.ringAssemblyPolicy .coupled } :=
  match evidence with
  | .acyclicCenter (.single base needs isotope affixes) =>
      .acyclicCenter
        { assignment := acyclicAssignment base program .coupled
          centerNeedsLocantInBaseName := needs
          isotopicAffixPresent := isotope
          observedAffixOrder := affixes }
  | .acyclicDoubleBond (.ezCisTrans base context carbonContext) =>
      .acyclicDoubleBond
        { assignment := acyclicAssignment base program .coupled
          context := context, carbonContext := carbonContext }
  | .acyclicEvenCumulene (.evenCumulene base context general preferred) =>
      .acyclicEvenCumulene
        { assignment := acyclicAssignment base program .coupled
          context := context, generalDescriptor := general, preferredDescriptor := preferred }
  | .acyclicOddCumulene (.oddCumulene base _path geometry) =>
      .acyclicOddCumulene
        { assignment := acyclicAssignment base program .coupled
          geometry := geometry }
  | .monocyclicAbsoluteCenter (.absoluteCenter base _center kind descriptor knowledge notationValue) =>
      .monocyclicCenter
        { physical := monocyclicPhysical base.toP93MonocyclicPhysicalPayload
          citation := base.citation, kind := kind, descriptor := descriptor
          knowledge := knowledge, «notation» := notationValue }
  | .monocyclicAchiralCenter (.achiralCenter base _center kind descriptor knowledge notationValue) =>
      .monocyclicCenter
        { physical := monocyclicPhysical base.toP93MonocyclicPhysicalPayload
          citation := base.citation, kind := kind, descriptor := descriptor
          knowledge := knowledge, «notation» := notationValue }
  | .monocyclicDoubleBond (.cyclicDouble base count geometry descriptor?) citation descriptor =>
      .monocyclicDoubleBond
        { physical := monocyclicPhysical base, doubleBondCount := count
          geometry := geometry, descriptor? := descriptor? } citation descriptor
  | .fusedCIP observation => .fusedCIP
      (fusedCIPObservation observation (program.fusedPolicy .coupled))
  | .cyclophanePlane (.cyclophanePlanes printed executable) =>
      .cyclophanePlane
        { system := printed.system, unit := .plane printed.members, frame := executable.frame
          citation := printed.citation, reference := printed.reference
          context := printed.context, descriptor := printed.descriptor }
  | .cyclophaneCenterCIP
      (.cyclophaneCenters system unit citation specification) =>
      match specification with
      | .cip context kind descriptor =>
          .cyclophaneCenterCIP
            { system := system, unit := unit, citation := citation
              specification := specification } context kind descriptor
      | .relativeRCT .. =>
          False.elim (by
            rcases valid.2.2 with ⟨context, kind, descriptor, impossible⟩
            cases impossible)
  | .cyclophaneCenterRelative
      (.cyclophaneCenters system unit citation specification) assignment =>
      .cyclophaneCenterRelative
        { system := system, unit := unit, citation := citation
          specification := specification } assignment
  | .cyclophaneDoubleBond
      (.cyclophaneDoubleBonds system unit citation ring phaneRing geometry carbonContext context
        descriptor?) descriptor =>
      .cyclophaneDoubleBond
        { system := system, unit := unit, ring := ring, phaneRing := phaneRing
          citation := citation
          geometry := geometry, carbonContext := carbonContext, context := context
          descriptor? := descriptor? } descriptor
  | .spiroPolyhedral payload => .spiroPolyhedral
      { system := payload.system
        unit := .polyhedron payload.system.center payload.positions
        citation := payload.citation, coordination := payload.coordination
        knowledge := payload.knowledge, descriptor := payload.descriptor }
  | .ringAssemblyAxis (.axes printed executable) assignment =>
      .ringAssemblyAxis
        { assembly := printed.assembly, normalization := executable.normalization.result
          spatial := executable.spatial, assignments := executable.assignments } assignment
  | .ringAssemblyCenter (.centers assembly assignments) assignment =>
      .ringAssemblyCenter { assembly := assembly, assignments := assignments } assignment
  | .ringAssemblyDoubleBond (.doubleBonds assembly assignments) assignment =>
      .ringAssemblyDoubleBond { assembly := assembly, assignments := assignments } assignment

def coupledDescriptorPolicies
    (program : P93CanonicalSourceProgram) : P93CoupledRingChainDescriptorPolicies where
  acyclic := program.acyclicPolicy .coupled
  monocyclic := program.monocyclicPolicy .coupled
  fused := program.fusedPolicy .coupled
  cyclophane := program.cyclophanePolicy .coupled
  spiro := program.spiroPolicy .coupled
  ringAssembly := program.ringAssemblyPolicy .coupled

def P93CanonicalClauseObservationEntry.ContainsCoupledEvidence
    (entry : P93CanonicalClauseObservationEntry)
    (name : P93RingChainBaseName)
    (evidence : P93CanonicalReviewedDescriptorEvidence) : Prop :=
  match entry.clause, entry.observation.payload with
  | .coupledRingChain .configurations, .coupled payload =>
      payload.reviewedBaseName = name ∧ evidence ∈ payload.assignments
  | _, _ => False

def HasCoupledEvidence
    (program : P93CanonicalSourceProgram)
    (source : AuthoritativeChemicalInput) (name : P93RingChainBaseName)
    (evidence : P93CanonicalReviewedDescriptorEvidence) : Prop :=
  ∃ entry ∈ program.observations, entry.source = source ∧
    P93CanonicalSourceProgram.P93CanonicalClauseObservationEntry.ContainsCoupledEvidence
      entry name evidence

def coupledPolicy
    (program : P93CanonicalSourceProgram) : P93CoupledRingChainAuthorityPolicy where
  descriptorPolicies := program.coupledDescriptorPolicies
  ReviewedBaseNameMatchesSource source name :=
    ∃ certificate, program.HasClaim .coupled source (.coupled (.baseName name certificate))
  StereogenicUnitEligible source name unit :=
    program.HasClaim .coupled source (.coupled (.eligibleUnit name unit))
  EvidenceBelongsToName source name evidence :=
    ∃ canonical, ∃ valid : canonical.ValidFor source,
      program.HasCoupledEvidence source name canonical ∧
      P93CanonicalSourceProgram.P93CanonicalReviewedDescriptorEvidence.toAuthority
        program source canonical valid = evidence
  CitationConformsToBaseNumbering source name citation unit :=
    program.HasClaim .coupled source (.coupled (.citation name citation unit))
  RepeatedComponentsObserved source name components :=
    program.HasClaim .coupled source (.coupled (.repeatedComponents name components))
  MultiplicativeNameSelected source name :=
    program.HasClaim .coupled source (.coupled (.multiplicativeDecision name true))

noncomputable def compiledPolicies
    (program : P93CanonicalSourceProgram) : Remaining56P93ReviewedPolicies where
  general := program.generalPolicy .general
  noncarbon := program.noncarbonPolicy .noncarbon
  acyclic := program.acyclicPolicy .acyclic
  cyclic :=
    { monocyclic := program.monocyclicPolicy .monocyclic
      vonBaeyer := program.vonBaeyerPolicy .vonBaeyer
      spiro := program.spiroPolicy .spiro
      fused := program.fusedPolicy .fused
      cyclophane := program.cyclophanePolicy .cyclophane
      fullerene := program.fullerenePolicy .fullerene
      relationalFullerene := program.relationalFullerenePolicy
      ringAssembly := program.ringAssemblyPolicy .ringAssembly
      coupledRingChain := program.coupledPolicy }

end P93CanonicalSourceProgram
end TetraStereo.OneCenter
