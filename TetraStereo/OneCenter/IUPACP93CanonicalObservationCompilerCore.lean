import TetraStereo.OneCenter.IUPACP93CanonicalPolicyCompiler

set_option autoImplicit false

/-!
# Canonical P-93 observation compiler: non-cyclic core

This module erases the canonical payloads for the five general, seven noncarbon, and eleven
acyclic rows into their legacy reviewed observation carriers and proves them against the policies
compiled from the same finite source-program entry.

The general judgments below are driven by the **actual** dependent payload stored in the program
entry.  `generalObservation_judged` and `generalObservation_productionJudges` therefore take the
typed equality `sourceObservation.payload = .general payload` (obtained constructively by `cases`
in `entry_general_productionJudges`) instead of a caller-supplied per-unit claim subset plus
`Intrinsic`.  Whole-configuration authorization is then read from that same payload's
`wholeConfigurations` extraction.  This rules out the previous gap in which an arbitrary `(R,S)`
payload passed a pointwise claim-subset check justified by unrelated `(R,R)`/`(S,S)` evidence.
-/

namespace TetraStereo.OneCenter

open BlueBookP93
open BlueBookP93.Acyclic
open BlueBookP93.NoncarbonTetrahedra
open IUPACNormativeProvision

namespace P93CanonicalSourceProgram

theorem claimEnvelope_of_mem
    {source : AuthoritativeChemicalInput} {clause : P93Clause}
    (observation : P93ClauseObservation source clause)
    {claim : P93SourceClaim} (claimMem : claim ∈ observation.auditClaims) :
    claim.SourceEnvelope source :=
  observation.validFor.1 claim claimMem

theorem physicalUnit_validFor
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (unit : P93AuthorityPhysicalUnit)
    (envelope : P93CanonicalPhysicalUnitEnvelope entry.source unit)
    (qualitative : ∀ candidate ∈ unit.qualitativeOnly,
      candidate ∈ entry.qualitativePhysicalUnits) :
    unit.ValidFor (program.physicalPolicy entry.clause.family) entry.source := by
  cases unit with
  | atomCenter center => exact envelope
  | bond first second => exact envelope
  | axis path => exact envelope
  | plane members =>
      have unitMem : P93AuthorityPhysicalUnit.plane members ∈
          entry.qualitativePhysicalUnits :=
        qualitative (.plane members) (by simp [P93AuthorityPhysicalUnit.qualitativeOnly])
      rcases program.qualitative_support_for entryMem unitMem with
        ⟨support, supportMem, sourceEq, clauseEq, unitEq⟩
      cases hclaim : support.claim with
      | plane supportedMembers frame =>
          simp only [hclaim, P93PhysicalClaim.unit] at unitEq
          injection unitEq with membersEq
          subst supportedMembers
          refine ⟨frame, ?_, ?_⟩
          · have sourceEnvelope := support.sourceEnvelope
            simp only [hclaim, P93PhysicalClaim.SourceEnvelope] at sourceEnvelope
            simpa [sourceEq] using sourceEnvelope
          · exact ⟨support, supportMem, sourceEq,
              congrArg P93Clause.family clauseEq, hclaim⟩
      | helix path frame => simp [hclaim, P93PhysicalClaim.unit] at unitEq
      | polyhedron center positions geometry frame =>
          simp [hclaim, P93PhysicalClaim.unit] at unitEq
  | helix path =>
      have unitMem : P93AuthorityPhysicalUnit.helix path ∈
          entry.qualitativePhysicalUnits :=
        qualitative (.helix path) (by simp [P93AuthorityPhysicalUnit.qualitativeOnly])
      rcases program.qualitative_support_for entryMem unitMem with
        ⟨support, supportMem, sourceEq, clauseEq, unitEq⟩
      cases hclaim : support.claim with
      | helix supportedPath frame =>
          simp only [hclaim, P93PhysicalClaim.unit] at unitEq
          injection unitEq with pathEq
          subst supportedPath
          refine ⟨frame, ?_, ?_⟩
          · have sourceEnvelope := support.sourceEnvelope
            simp only [hclaim, P93PhysicalClaim.SourceEnvelope] at sourceEnvelope
            simpa [sourceEq] using sourceEnvelope
          · exact ⟨support, supportMem, sourceEq,
              congrArg P93Clause.family clauseEq, hclaim⟩
      | plane members frame => simp [hclaim, P93PhysicalClaim.unit] at unitEq
      | polyhedron center positions geometry frame =>
          simp [hclaim, P93PhysicalClaim.unit] at unitEq
  | polyhedron center positions =>
      have unitMem : P93AuthorityPhysicalUnit.polyhedron center positions ∈
          entry.qualitativePhysicalUnits :=
        qualitative (.polyhedron center positions)
          (by simp [P93AuthorityPhysicalUnit.qualitativeOnly])
      rcases program.qualitative_support_for entryMem unitMem with
        ⟨support, supportMem, sourceEq, clauseEq, unitEq⟩
      cases hclaim : support.claim with
      | polyhedron supportedCenter supportedPositions geometry frame =>
          simp only [hclaim, P93PhysicalClaim.unit] at unitEq
          injection unitEq with centerEq positionsEq
          subst supportedCenter
          subst supportedPositions
          refine ⟨geometry, frame, ?_, ?_⟩
          · have sourceEnvelope := support.sourceEnvelope
            simp only [hclaim, P93PhysicalClaim.SourceEnvelope] at sourceEnvelope
            simpa [sourceEq] using sourceEnvelope
          · exact ⟨support, supportMem, sourceEq,
              congrArg P93Clause.family clauseEq, hclaim⟩
      | helix path frame => simp [hclaim, P93PhysicalClaim.unit] at unitEq
      | plane members frame => simp [hclaim, P93PhysicalClaim.unit] at unitEq

def generalObservation
    (program : P93CanonicalSourceProgram)
    {row : Remaining71P93GeneralAuthorityRow}
    (payload : P93GeneralClausePayload row) :
    (row.reference (program.generalPolicy .general)).Observation :=
  match payload with
  | .absolute configuration => { configuration := configuration }
  | .relative first second _ => { first := first, second := second }
  | .mixed configuration plan typography =>
      { configuration := configuration
        plan := { assignments := plan.assignments.map fun assignment =>
          { located := assignment.located, scope := assignment.scope } }
        observedTypography := typography }
  | .racemate mixture _ => mixture
  | .ambo citation mixture => { citation := citation, mixture := mixture }

def noncarbonAssignment
    (program : P93CanonicalSourceProgram) (scope : P93ClaimFamily)
    (assignment : P93NoncarbonAssignmentPayload) :
    P93NoncarbonTetrahedralAssignment (program.noncarbonPolicy scope) where
  frame := assignment.frame
  descriptor := assignment.descriptor

def noncarbonObservation
    (program : P93CanonicalSourceProgram)
    {row : Remaining71P93NoncarbonAuthorityRow}
    (payload : P93NoncarbonClausePayload row) :
    (row.reference (program.noncarbonPolicy .noncarbon)).Observation :=
  match payload with
  | .tetrahedra assignment => noncarbonAssignment program .noncarbon assignment
  | .methodology assignment citation? rule =>
      { assignment := noncarbonAssignment program .noncarbon assignment
        citation? := citation?, citationRule := rule }
  | .onic assignment family =>
      { assignment := noncarbonAssignment program .noncarbon assignment, family := family }
  | .oxide assignment oxygen family first second =>
      { assignment := noncarbonAssignment program .noncarbon assignment
        family := family, oxygen := oxygen, firstBonding := first, secondBonding := second }
  | .phosphorus assignment oxygen family firstDouble secondDouble firstCharges secondCharges =>
      { assignment := noncarbonAssignment program .noncarbon assignment
        family := family, oxygen := oxygen, firstWrittenAsDouble := firstDouble
        secondWrittenAsDouble := secondDouble, firstCharges := firstCharges
        secondCharges := secondCharges }
  | .chalcogen assignment oxygen family firstDouble secondDouble firstCharges secondCharges =>
      { assignment := noncarbonAssignment program .noncarbon assignment
        family := family, oxygen := oxygen, firstWrittenAsDouble := firstDouble
        secondWrittenAsDouble := secondDouble, firstCharges := firstCharges
        secondCharges := secondCharges }
  | .group14 assignment family =>
      { assignment := noncarbonAssignment program .noncarbon assignment, family := family }

def acyclicObservationAt
    (program : P93CanonicalSourceProgram)
    (scope : P93ClaimFamily)
    {row : Remaining71P93AcyclicAuthorityRow}
    (payload : P93AcyclicClausePayload row) :
    (row.reference (program.acyclicPolicy scope)).Observation :=
  match payload with
  | .centers base | .ordinaryDouble base => acyclicAssignment base program scope
  | .single base needs isotope affixes =>
      { assignment := acyclicAssignment base program scope
        centerNeedsLocantInBaseName := needs
        isotopicAffixPresent := isotope
        observedAffixOrder := affixes }
  | .multipleCenters assignments =>
      { assignments := assignments.map fun assignment =>
          acyclicAssignment assignment program scope }
  | .prefix base position =>
      { assignment := acyclicAssignment base program scope
        observedPosition := position }
  | .ezCisTrans base context carbonContext =>
      { assignment := acyclicAssignment base program scope
        context := context, carbonContext := carbonContext }
  | .multipleDouble assignments =>
      { assignments := assignments.map fun assignment =>
          acyclicAssignment assignment program scope }
  | .heteroDouble base context =>
      { assignment := acyclicAssignment base program scope, context := context }
  | .evenCumulene base context general preferred =>
      { assignment := acyclicAssignment base program scope
        context := context, generalDescriptor := general, preferredDescriptor := preferred }
  | .oddCumulene base _ geometry =>
      { assignment := acyclicAssignment base program scope, geometry := geometry }
  | .multipleUnits assignments competition =>
      { assignments := assignments.map fun placed =>
          { assignment := acyclicAssignment placed.assignment program scope
            observedPosition := placed.observedPosition }
        numberingCompetition := competition }

def acyclicObservation
    (program : P93CanonicalSourceProgram)
    {row : Remaining71P93AcyclicAuthorityRow}
    (payload : P93AcyclicClausePayload row) :
    (row.reference (program.acyclicPolicy .acyclic)).Observation :=
  acyclicObservationAt program .acyclic payload

theorem acyclicUnit_validFor
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (scope : P93ClaimFamily) (familyEq : entry.clause.family = scope)
    (unit : P93AuthorityPhysicalUnit)
    (unitClaimMem : P93SourceClaim.acyclic (.unit unit) ∈
      entry.observation.auditClaims) :
    unit.ValidFor (program.physicalPolicy scope) entry.source := by
  have unitEnvelope : P93CanonicalPhysicalUnitEnvelope entry.source unit := by
    simpa [P93SourceClaim.SourceEnvelope, P93AcyclicClaim.SourceEnvelope] using
      claimEnvelope_of_mem entry.observation unitClaimMem
  simpa [familyEq] using program.physicalUnit_validFor entryMem unit unitEnvelope (by
    intro candidate candidateMem
    unfold P93CanonicalClauseObservationEntry.qualitativePhysicalUnits
    rw [List.mem_flatMap]
    refine ⟨.acyclic (.unit unit), unitClaimMem, ?_⟩
    simpa [P93SourceClaim.qualitativePhysicalUnits, P93SourceClaim.physicalUnits,
      P93AcyclicClaim.physicalUnits] using candidateMem)

theorem acyclicAssignment_validFor
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (scope : P93ClaimFamily)
    (familyEq : entry.clause.family = scope)
    (base : P93AcyclicBasePayload)
    (claims : ∀ claim ∈ base.baseClaims, claim ∈ entry.observation.auditClaims)
    (intrinsic : base.Intrinsic) :
    (acyclicAssignment base program scope).ValidFor
      (program.acyclicPolicy scope) entry.source := by
  rcases intrinsic with ⟨componentValid, kindMatches, descriptorApplies, citationValid⟩
  have unitClaimMem :
      P93SourceClaim.acyclic (.unit base.unit) ∈ entry.observation.auditClaims :=
    claims _ (by simp [P93AcyclicBasePayload.baseClaims])
  have unitValid := program.acyclicUnit_validFor entryMem scope familyEq base.unit unitClaimMem
  simp only [P93AcyclicAuthorityAssignment.ValidFor, acyclicAssignment]
  refine ⟨?_, kindMatches, ?_, ?_, descriptorApplies, ?_, ?_, ?_⟩
  · exact unitValid
  · simpa [familyEq] using program.hasClaim_of_mem entryMem unitClaimMem
  · simpa [familyEq] using program.hasClaim_of_mem entryMem
      (claims _ (by simp [P93AcyclicBasePayload.baseClaims]))
  · simpa [familyEq] using program.hasClaim_of_mem entryMem
      (claims _ (by simp [P93AcyclicBasePayload.baseClaims]))
  · simpa [familyEq] using program.hasClaim_of_mem entryMem
      (claims _ (by simp [P93AcyclicBasePayload.baseClaims]))
  · cases citationEq : base.citation? with
    | none => simp [P93AcyclicAuthorityAssignment.CitationValidFor]
    | some citation =>
        have citationClaimMem :
            P93SourceClaim.acyclic (.citation citation base.unit) ∈
              entry.observation.auditClaims :=
          claims _ (by simp [P93AcyclicBasePayload.baseClaims, citationEq])
        refine ⟨citationValid citation ?_, ?_⟩
        · exact citationEq
        · simpa [familyEq] using program.hasClaim_of_mem entryMem citationClaimMem

theorem generalConfiguration_inputFaithful
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .general)
    (configuration : P93CanonicalGeneralConfiguration)
    (claims : ∀ claim ∈ configuration.toClaims,
      claim ∈ entry.observation.auditClaims)
    (complete : configuration.StructurallyComplete) :
    P93GeneralConfigurationInputFaithful
      (program.generalPolicy .general) entry.source configuration := by
  rcases complete with ⟨nonempty, unitsNodup, citationsNodup⟩
  refine ⟨⟨nonempty, unitsNodup, citationsNodup, ?_⟩, ?_⟩
  · intro assignment assignmentMem
    have citationClaimMem :
        P93SourceClaim.general (.citation assignment.citation assignment.unit) ∈
          entry.observation.auditClaims :=
      claims _ (by
        simp only [P93CanonicalGeneralConfiguration.toClaims, List.mem_flatMap]
        exact ⟨assignment, assignmentMem, by simp⟩)
    have citationEnvelope := claimEnvelope_of_mem entry.observation citationClaimMem
    have citationEnvelope' :
        assignment.citation.Valid ∧
          P93CanonicalPhysicalUnitEnvelope entry.source assignment.unit := by
      simpa [P93SourceClaim.SourceEnvelope, P93GeneralClaim.SourceEnvelope] using
        citationEnvelope
    have unitEnvelope :
        P93CanonicalPhysicalUnitEnvelope entry.source assignment.unit := by
      exact citationEnvelope'.2
    refine ⟨?_, ?_, ?_⟩
    · simpa [familyEq] using
        program.physicalUnit_validFor entryMem assignment.unit unitEnvelope (by
          intro candidate candidateMem
          unfold P93CanonicalClauseObservationEntry.qualitativePhysicalUnits
          rw [List.mem_flatMap]
          refine ⟨.general (.citation assignment.citation assignment.unit),
            citationClaimMem, ?_⟩
          simpa [P93SourceClaim.qualitativePhysicalUnits, P93SourceClaim.physicalUnits,
            P93GeneralClaim.physicalUnits] using candidateMem)
    · exact citationEnvelope'.1
    · simpa [familyEq] using program.hasClaim_of_mem entryMem citationClaimMem
  · intro assignment assignmentMem
    left
    simpa [familyEq] using program.hasClaim_of_mem entryMem (claims _ (by
        simp only [P93CanonicalGeneralConfiguration.toClaims, List.mem_flatMap]
        exact ⟨assignment, assignmentMem, by simp⟩))

/-- Judge one general observation from the **actual** dependent payload of the entry.

This is the strengthened replacement for the old interface, which accepted an arbitrary payload
together with a per-unit claim-subset proof and `Intrinsic`.  Here the entry is presented with its
clause already specialized to `row`, so the typed equality `payloadEq` is checkable, and every
authorization conjunct is derived from the payload's `wholeConfigurations` list.  No new
desired-correctness hypothesis is introduced: the structural facts (`payloadClaims`, `intrinsic`)
are read off the entry's own `validFor` field. -/
theorem generalObservation_judged
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
        transcription⟩ : P93CanonicalClauseObservationEntry) ∈ program.observations) :
    (row.reference (program.generalPolicy .general)).Judges source
      (program.generalObservation payload) := by
  have payloadClaims : ∀ claim ∈ payload.toClaims,
      claim ∈ sourceObservation.auditClaims := by
    intro claim claimMem
    simpa [P93ClauseObservation.auditClaims, payloadEq] using claimMem
  have intrinsic : payload.Intrinsic := by
    simpa [P93ClausePayloadData.ValidFor, payloadEq] using sourceObservation.validFor.2
  have inputFaithful : ∀ configuration : P93CanonicalGeneralConfiguration,
      (∀ claim ∈ configuration.toClaims,
        claim ∈ sourceObservation.auditClaims) →
      configuration.StructurallyComplete →
      P93GeneralConfigurationInputFaithful
        (program.generalPolicy .general) source configuration := by
    intro configuration claims complete
    exact program.generalConfiguration_inputFaithful entryMem rfl configuration claims complete
  have authorized : ∀ configuration,
      configuration ∈ P93GeneralClausePayload.wholeConfigurations payload →
      (program.generalPolicy .general).ConfigurationAuthorized source configuration := by
    intro configuration mem
    exact program.generalConfigurationAuthorized_of_generalPayload
      source sourceAdmitted row clauseListed sourceObservation transcription payload
      payloadEq entryMem mem
  cases payload with
  | absolute configuration =>
      simp only [generalObservation]
      refine ⟨?_, ?_⟩
      · exact inputFaithful configuration
          (fun claim claimMem => payloadClaims claim (by
            simpa [P93GeneralClausePayload.toClaims] using claimMem))
          intrinsic
      · exact authorized configuration (by
          simp [P93GeneralClausePayload.wholeConfigurations])
  | relative first second leading =>
      simp only [generalObservation]
      rcases intrinsic with ⟨firstComplete, leadingValid, relative⟩
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact inputFaithful first
          (fun claim claimMem => payloadClaims claim (by
            simp only [P93GeneralClausePayload.toClaims, List.mem_append]
            exact Or.inl (Or.inl claimMem)))
          firstComplete
      · rcases leadingValid with
          ⟨leadingMem, eligible, mirrorNe, preferred, lowest⟩
        exact ⟨leading, leadingMem, eligible, mirrorNe,
          (fun assignment assignmentMem assignmentEligible assignmentMirrorNe =>
            lowest assignment assignmentMem ⟨assignmentEligible, assignmentMirrorNe⟩), preferred⟩
      · simpa [generalPolicy] using relative
      · exact authorized first (by
          simp [P93GeneralClausePayload.wholeConfigurations])
      · exact authorized second (by
          simp [P93GeneralClausePayload.wholeConfigurations])
  | mixed configuration plan typography =>
      simp only [generalObservation]
      rcases intrinsic with
        ⟨complete, planEq, hasAbsolute, hasRelative, groups, typographyEq⟩
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact inputFaithful configuration
          (fun claim claimMem => payloadClaims claim (by
            simpa [P93GeneralClausePayload.toClaims] using claimMem))
          complete
      · simpa using planEq
      · constructor
        · rcases hasAbsolute with ⟨assignment, assignmentMem, assignmentScope⟩
          exact ⟨{ located := assignment.located, scope := assignment.scope },
            List.mem_map.2 ⟨assignment, assignmentMem, rfl⟩, assignmentScope⟩
        · rcases hasRelative with ⟨assignment, assignmentMem, group, assignmentScope⟩
          exact ⟨{ located := assignment.located, scope := assignment.scope },
            List.mem_map.2 ⟨assignment, assignmentMem, rfl⟩, group, assignmentScope⟩
      · intro group groupPresent
        rcases groupPresent with ⟨assignment, assignmentMem, assignmentScope⟩
        rcases List.mem_map.1 assignmentMem with ⟨canonical, canonicalMem, canonicalEq⟩
        subst assignment
        rcases groups group ⟨canonical, canonicalMem, assignmentScope⟩ with
          ⟨count, witness, witnessMem, witnessScope, _eligible, witnessMirrorNe⟩
        refine ⟨?_, ⟨{ located := witness.located, scope := witness.scope }, ?_,
          witnessScope, ?_⟩⟩
        · simpa [List.filter_map] using count
        · exact List.mem_map.2 ⟨witness, witnessMem, rfl⟩
        · simpa [generalPolicy] using witnessMirrorNe
      · simpa [P93GeneralMixedTypography] using typographyEq
      · exact authorized configuration (by
          simp [P93GeneralClausePayload.wholeConfigurations])
  | racemate mixture leading =>
      simp only [generalObservation]
      rcases intrinsic with
        ⟨firstComplete, leadingValid, mixtureValid, mirrored, distinct, half⟩
      refine ⟨?_, ?_, ⟨mixtureValid, ?_, distinct, half⟩, ?_, ?_⟩
      · exact inputFaithful mixture.first
          (fun claim claimMem => payloadClaims claim (by
            simp only [P93GeneralClausePayload.toClaims, List.mem_append]
            exact Or.inl (Or.inl claimMem)))
          firstComplete
      · rcases leadingValid with
          ⟨leadingMem, eligible, mirrorNe, preferred, lowest⟩
        exact ⟨leading, leadingMem, eligible, mirrorNe,
          (fun assignment assignmentMem assignmentEligible assignmentMirrorNe =>
            lowest assignment assignmentMem ⟨assignmentEligible, assignmentMirrorNe⟩), preferred⟩
      · simpa [generalPolicy] using mirrored
      · exact authorized mixture.first (by
          simp [P93GeneralClausePayload.wholeConfigurations])
      · exact authorized mixture.second (by
          simp [P93GeneralClausePayload.wholeConfigurations])
  | ambo citation mixture =>
      simp only [generalObservation]
      rcases intrinsic with
        ⟨firstComplete, nonEquimolar, changed, inverted, notRelative, distinct⟩
      refine ⟨?_, ⟨nonEquimolar, ?_, ?_, ?_, distinct⟩, ?_, ?_⟩
      · exact inputFaithful mixture.first
          (fun claim claimMem => payloadClaims claim (by
            simp only [P93GeneralClausePayload.toClaims, List.mem_append]
            exact Or.inl claimMem))
          firstComplete
      · simpa only [generalPolicy_localAction_mirror] using changed
      · simpa only [generalConfigurationInvertedAtCitation_eq_canonical] using inverted
      · simpa [generalPolicy] using notRelative
      · exact authorized mixture.first (by
          simp [P93GeneralClausePayload.wholeConfigurations])
      · exact authorized mixture.second (by
          simp [P93GeneralClausePayload.wholeConfigurations])

theorem noncarbonAssignment_validFor
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .noncarbon)
    (assignment : P93NoncarbonAssignmentPayload)
    (claims : ∀ claim ∈ assignment.baseClaims,
      claim ∈ entry.observation.auditClaims)
    (structural : assignment.frame.StructurallyValidFor entry.source) :
    (noncarbonAssignment program .noncarbon assignment).ValidFor
      (program.noncarbonPolicy .noncarbon) entry.source := by
  simp only [P93NoncarbonTetrahedralAssignment.ValidFor,
    P93NoncarbonTetrahedralFrame.ValidFor, noncarbonAssignment]
  refine ⟨⟨structural, ?_⟩, ?_⟩
  · simpa [familyEq] using program.hasClaim_of_mem entryMem
      (claims _ (by simp [P93NoncarbonAssignmentPayload.baseClaims]))
  · simpa [familyEq] using program.hasClaim_of_mem entryMem
      (claims _ (by simp [P93NoncarbonAssignmentPayload.baseClaims]))

theorem noncarbonObservation_judged
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .noncarbon)
    {row : Remaining71P93NoncarbonAuthorityRow}
    (payload : P93NoncarbonClausePayload row)
    (claims : ∀ claim ∈ payload.toClaims, claim ∈ entry.observation.auditClaims)
    (intrinsic : payload.Intrinsic entry.source) :
    (row.reference (program.noncarbonPolicy .noncarbon)).Judges entry.source
      (program.noncarbonObservation payload) := by
  cases payload with
  | tetrahedra assignment =>
      simpa [noncarbonObservation] using
        program.noncarbonAssignment_validFor entryMem familyEq assignment claims intrinsic
  | methodology assignment citation? rule =>
      rcases intrinsic with ⟨structural, element, citationBinding, conforms⟩
      simp only [noncarbonObservation, noncarbonAssignment]
      refine ⟨program.noncarbonAssignment_validFor entryMem familyEq assignment
        (fun claim claimMem => claims claim (by
          simp only [P93NoncarbonClausePayload.toClaims, List.mem_append]
          exact Or.inl claimMem)) structural, element, ?_, conforms⟩
      cases locantEq : rule.locant with
      | none => simpa [P93NoncarbonCitationBindingValid, locantEq] using citationBinding
      | letter =>
          simp [locantEq] at citationBinding
      | numerical =>
          simp only [locantEq] at citationBinding
          rcases citationBinding with ⟨citation, citationEq, citationValid⟩
          simp only [P93NoncarbonCitationBindingValid, locantEq]
          refine ⟨citation, citationEq, citationValid, ?_⟩
          simpa [familyEq] using program.hasClaim_of_mem entryMem (claims _ (by
            simp [P93NoncarbonClausePayload.toClaims, citationEq]))
  | onic assignment family =>
      simp only [noncarbonObservation, noncarbonAssignment]
      rcases intrinsic with ⟨structural, element⟩
      exact ⟨program.noncarbonAssignment_validFor entryMem familyEq assignment claims structural,
        element⟩
  | oxide assignment oxygen family first second =>
      simp only [noncarbonObservation, noncarbonAssignment]
      rcases intrinsic with
        ⟨structural, centerElement, oxygenMem, oxygenElement, bond, distinct, countEq⟩
      refine ⟨⟨program.noncarbonAssignment_validFor entryMem familyEq assignment
        (fun claim claimMem => claims claim (by
          simp only [P93NoncarbonClausePayload.toClaims, List.mem_append]
          exact Or.inl claimMem)) structural,
        centerElement, oxygenMem, oxygenElement, bond, ?_, ?_, distinct⟩, countEq⟩
      · simpa [familyEq] using program.hasClaim_of_mem entryMem
          (claims _ (by simp [P93NoncarbonClausePayload.toClaims]))
      · simpa [familyEq] using program.hasClaim_of_mem entryMem
          (claims _ (by simp [P93NoncarbonClausePayload.toClaims]))
  | phosphorus assignment oxygen family firstDouble secondDouble firstCharges secondCharges =>
      simp only [noncarbonObservation, noncarbonAssignment]
      rcases intrinsic with
        ⟨structural, centerElement, oxygenMem, oxygenElement, bond, distinct,
          orderEq, chargeEq⟩
      refine ⟨⟨program.noncarbonAssignment_validFor entryMem familyEq assignment
        (fun claim claimMem => claims claim (by
          simp only [P93NoncarbonClausePayload.toClaims, List.mem_append]
          exact Or.inl claimMem)) structural,
        centerElement, oxygenMem, oxygenElement, bond, ?_, ?_, distinct⟩, orderEq, chargeEq⟩
      · simpa [familyEq] using program.hasClaim_of_mem entryMem
          (claims _ (by simp [P93NoncarbonClausePayload.toClaims]))
      · simpa [familyEq] using program.hasClaim_of_mem entryMem
          (claims _ (by simp [P93NoncarbonClausePayload.toClaims]))
  | chalcogen assignment oxygen family firstDouble secondDouble firstCharges secondCharges =>
      simp only [noncarbonObservation, noncarbonAssignment]
      rcases intrinsic with
        ⟨structural, centerElement, oxygenMem, oxygenElement, bond, distinct,
          treatment, orderEq, chargeEq⟩
      refine ⟨⟨program.noncarbonAssignment_validFor entryMem familyEq assignment
        (fun claim claimMem => claims claim (by
          simp only [P93NoncarbonClausePayload.toClaims, List.mem_append]
          exact Or.inl claimMem)) structural,
        centerElement, oxygenMem, oxygenElement, bond, ?_, ?_, distinct⟩,
        treatment, orderEq, chargeEq⟩
      · simpa [familyEq] using program.hasClaim_of_mem entryMem
          (claims _ (by simp [P93NoncarbonClausePayload.toClaims]))
      · simpa [familyEq] using program.hasClaim_of_mem entryMem
          (claims _ (by simp [P93NoncarbonClausePayload.toClaims]))
  | group14 assignment family =>
      simp only [noncarbonObservation, noncarbonAssignment]
      rcases intrinsic with ⟨structural, element, method⟩
      exact ⟨⟨program.noncarbonAssignment_validFor entryMem familyEq assignment claims structural,
        element⟩, method⟩

theorem acyclicObservation_judgedAt
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (scope : P93ClaimFamily)
    (familyEq : entry.clause.family = scope)
    {row : Remaining71P93AcyclicAuthorityRow}
    (payload : P93AcyclicClausePayload row)
    (claims : ∀ claim ∈ payload.toClaims, claim ∈ entry.observation.auditClaims)
    (intrinsic : payload.Intrinsic) :
    (row.reference (program.acyclicPolicy scope)).Judges entry.source
      (program.acyclicObservationAt scope payload) := by
  cases payload with
  | centers base =>
      rcases intrinsic with ⟨baseIntrinsic, centerKind⟩
      exact ⟨program.acyclicAssignment_validFor entryMem scope familyEq base claims
        baseIntrinsic, centerKind⟩
  | single base needs isotope affixes =>
      rcases intrinsic with
        ⟨baseIntrinsic, centerKind, locant, affixOrder, stereoMem, isotopeIff⟩
      simp only [acyclicObservationAt, acyclicAssignment]
      refine ⟨program.acyclicAssignment_validFor entryMem scope familyEq base
        (fun claim claimMem => claims claim (by
          simp only [P93AcyclicClausePayload.toClaims, List.mem_append]
          exact Or.inl claimMem)) baseIntrinsic,
        centerKind, locant, ?_, affixOrder, stereoMem, isotopeIff⟩
      simpa [familyEq] using program.hasClaim_of_mem entryMem
        (claims _ (by simp [P93AcyclicClausePayload.toClaims]))
  | multipleCenters assignments =>
      rcases intrinsic with
        ⟨length, assignmentIntrinsic, unitNodup, citationNodup, citationSorted⟩
      simp only [acyclicObservationAt]
      have nonempty : assignments.map (fun assignment =>
          acyclicAssignment assignment program scope) ≠ [] := by
        intro empty
        have : assignments = [] := by simpa using empty
        simp [this] at length
      refine ⟨⟨nonempty, ?_⟩, by simpa using length, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro authority authorityMem
        rcases List.mem_map.1 authorityMem with ⟨assignment, assignmentMem, rfl⟩
        exact program.acyclicAssignment_validFor entryMem scope familyEq assignment
          (fun claim claimMem => claims claim (by
            simp only [P93AcyclicClausePayload.toClaims, List.mem_append,
              List.mem_flatMap]
            exact Or.inl ⟨assignment, assignmentMem, claimMem⟩))
          (assignmentIntrinsic assignment assignmentMem).1
      · intro authority authorityMem
        rcases List.mem_map.1 authorityMem with ⟨assignment, assignmentMem, rfl⟩
        simpa [acyclicAssignment] using (assignmentIntrinsic assignment assignmentMem).2.1
      · simpa [acyclicAssignment] using unitNodup
      · intro authority authorityMem
        rcases List.mem_map.1 authorityMem with ⟨assignment, assignmentMem, rfl⟩
        simpa [acyclicAssignment] using (assignmentIntrinsic assignment assignmentMem).2.2
      · simpa [P93AcyclicPresentCitations, P93AcyclicBasePresentCitations,
          acyclicAssignment, List.filterMap_map] using citationNodup
      · simpa [P93AcyclicPresentCitations, P93AcyclicBasePresentCitations,
          acyclicAssignment, List.filterMap_map] using citationSorted
      · simpa [familyEq, acyclicAssignment, P93AcyclicAssignmentTriples,
          P93AcyclicBasePayload.triple] using program.hasClaim_of_mem entryMem
          (claims _ (by simp [P93AcyclicClausePayload.toClaims,
            P93AcyclicBasePayload.triple]))
  | «prefix» base position =>
      rcases intrinsic with ⟨baseIntrinsic, centerKind, placement⟩
      exact ⟨⟨program.acyclicAssignment_validFor entryMem scope familyEq base claims
        baseIntrinsic, placement⟩, centerKind⟩
  | ordinaryDouble base =>
      rcases intrinsic with ⟨baseIntrinsic, kindEq⟩
      exact ⟨program.acyclicAssignment_validFor entryMem scope familyEq base claims
        baseIntrinsic, kindEq⟩
  | ezCisTrans base context carbonContext =>
      rcases intrinsic with
        ⟨baseIntrinsic, kindEq, recommended, cisTrans⟩
      simp only [acyclicObservationAt, acyclicAssignment]
      refine ⟨program.acyclicAssignment_validFor entryMem scope familyEq base
        (fun claim claimMem => claims claim (by
          simp only [P93AcyclicClausePayload.toClaims, List.mem_append]
          exact Or.inl claimMem)) baseIntrinsic,
        kindEq, ?_, recommended, cisTrans⟩
      simpa [familyEq] using program.hasClaim_of_mem entryMem
        (claims _ (by simp [P93AcyclicClausePayload.toClaims]))
  | heteroDouble base context =>
      rcases intrinsic with ⟨baseIntrinsic, kindEq, recommended⟩
      exact ⟨⟨program.acyclicAssignment_validFor entryMem scope familyEq base claims
        baseIntrinsic, kindEq⟩, recommended⟩
  | evenCumulene base context general preferred =>
      rcases intrinsic with
        ⟨baseIntrinsic, kindEq, correspondence, descriptorEq, recommended⟩
      exact ⟨program.acyclicAssignment_validFor entryMem scope familyEq base claims
        baseIntrinsic, kindEq, correspondence, descriptorEq, recommended⟩
  | oddCumulene base path geometry =>
      rcases intrinsic with ⟨baseIntrinsic, kindEq, unitEq, assignment⟩
      simp only [acyclicObservationAt, acyclicAssignment]
      refine ⟨program.acyclicAssignment_validFor entryMem scope familyEq base
        (fun claim claimMem => claims claim (by
          simp only [P93AcyclicClausePayload.toClaims, List.mem_append]
          exact Or.inl claimMem)) baseIntrinsic,
        kindEq, ⟨path, unitEq, ?_⟩, assignment⟩
      simpa [familyEq] using program.hasClaim_of_mem entryMem
        (claims _ (by simp [P93AcyclicClausePayload.toClaims]))
  | multipleDouble assignments =>
      rcases intrinsic with
        ⟨length, assignmentIntrinsic, unitNodup, citationNodup, citationSorted⟩
      simp only [acyclicObservationAt]
      have nonempty : assignments.map (fun assignment =>
          acyclicAssignment assignment program scope) ≠ [] := by
        intro empty
        have : assignments = [] := by simpa using empty
        simp [this] at length
      refine ⟨⟨nonempty, ?_⟩, by simpa using length, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro authority authorityMem
        rcases List.mem_map.1 authorityMem with ⟨assignment, assignmentMem, rfl⟩
        exact program.acyclicAssignment_validFor entryMem scope familyEq assignment
          (fun claim claimMem => claims claim (by
            simp only [P93AcyclicClausePayload.toClaims, List.mem_append,
              List.mem_flatMap]
            exact Or.inl ⟨assignment, assignmentMem, claimMem⟩))
          (assignmentIntrinsic assignment assignmentMem).1
      · intro authority authorityMem
        rcases List.mem_map.1 authorityMem with ⟨assignment, assignmentMem, rfl⟩
        simpa [acyclicAssignment] using (assignmentIntrinsic assignment assignmentMem).2.1
      · simpa [acyclicAssignment] using unitNodup
      · intro authority authorityMem
        rcases List.mem_map.1 authorityMem with ⟨assignment, assignmentMem, rfl⟩
        simpa [acyclicAssignment] using (assignmentIntrinsic assignment assignmentMem).2.2
      · simpa [P93AcyclicPresentCitations, P93AcyclicBasePresentCitations,
          acyclicAssignment, List.filterMap_map] using citationNodup
      · simpa [P93AcyclicPresentCitations, P93AcyclicBasePresentCitations,
          acyclicAssignment, List.filterMap_map] using citationSorted
      · simpa [familyEq, acyclicAssignment, P93AcyclicAssignmentTriples,
          P93AcyclicBasePayload.triple] using program.hasClaim_of_mem entryMem
          (claims _ (by simp [P93AcyclicClausePayload.toClaims,
            P93AcyclicBasePayload.triple]))
  | multipleUnits assignments competition =>
      rcases intrinsic with
        ⟨length, assignmentIntrinsic, unitNodup, citationNodup, citationSorted,
          competitionValid⟩
      simp only [acyclicObservationAt]
      refine ⟨by simpa using length, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro placed placedMem
        rcases List.mem_map.1 placedMem with ⟨canonical, canonicalMem, rfl⟩
        rcases assignmentIntrinsic canonical canonicalMem with
          ⟨baseIntrinsic, citation, citationEq, placement⟩
        refine ⟨program.acyclicAssignment_validFor entryMem scope familyEq
          canonical.assignment (fun claim claimMem => claims claim (by
            simp only [P93AcyclicClausePayload.toClaims, List.mem_append,
              List.mem_flatMap]
            exact Or.inl ⟨canonical, canonicalMem, claimMem⟩)) baseIntrinsic,
          citation, citationEq, ?_⟩
        simpa [acyclicAssignment] using placement
      · simpa [acyclicAssignment] using unitNodup
      · simpa [P93AcyclicPresentCitations, P93AcyclicPayloadPresentCitations,
          acyclicAssignment, List.filterMap_map] using citationNodup
      · simpa [P93AcyclicPresentCitations, P93AcyclicPayloadPresentCitations,
          acyclicAssignment, List.filterMap_map] using citationSorted
      · simpa [familyEq, acyclicAssignment] using program.hasClaim_of_mem entryMem
          (claims _ (by simp [P93AcyclicClausePayload.toClaims]))
      · cases competition with
        | unique => trivial
        | competing alternativeCitations firstDifference =>
            simpa [P93AcyclicPresentCitations, P93AcyclicPayloadPresentCitations,
              acyclicAssignment, List.filterMap_map, Function.comp_apply] using competitionValid

theorem generalObservation_productionJudges
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
        transcription⟩ : P93CanonicalClauseObservationEntry) ∈ program.observations) :
    row.ProductionJudges (program.generalPolicy .general) source
      (program.generalObservation payload) :=
  (row.production_eq_reference (program.generalPolicy .general) source
    (program.generalObservation payload)).2
      (program.generalObservation_judged source sourceAdmitted row clauseListed
        sourceObservation transcription payload payloadEq entryMem)

theorem noncarbonObservation_productionJudges
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .noncarbon)
    {row : Remaining71P93NoncarbonAuthorityRow}
    (payload : P93NoncarbonClausePayload row)
    (claims : ∀ claim ∈ payload.toClaims, claim ∈ entry.observation.auditClaims)
    (intrinsic : payload.Intrinsic entry.source) :
    row.ProductionJudges (program.noncarbonPolicy .noncarbon) entry.source
      (program.noncarbonObservation payload) :=
  (row.production_eq_reference (program.noncarbonPolicy .noncarbon) entry.source
    (program.noncarbonObservation payload)).2
      (program.noncarbonObservation_judged entryMem familyEq payload claims intrinsic)

theorem acyclicObservation_productionJudgesAt
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (scope : P93ClaimFamily)
    (familyEq : entry.clause.family = scope)
    {row : Remaining71P93AcyclicAuthorityRow}
    (payload : P93AcyclicClausePayload row)
    (claims : ∀ claim ∈ payload.toClaims, claim ∈ entry.observation.auditClaims)
    (intrinsic : payload.Intrinsic) :
    row.ProductionJudges (program.acyclicPolicy scope) entry.source
      (program.acyclicObservationAt scope payload) :=
  (row.production_eq_reference (program.acyclicPolicy scope) entry.source
    (program.acyclicObservationAt scope payload)).2
      (program.acyclicObservation_judgedAt entryMem scope familyEq payload claims intrinsic)

theorem acyclicObservation_productionJudges
    (program : P93CanonicalSourceProgram)
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ program.observations)
    (familyEq : entry.clause.family = .acyclic)
    {row : Remaining71P93AcyclicAuthorityRow}
    (payload : P93AcyclicClausePayload row)
    (claims : ∀ claim ∈ payload.toClaims, claim ∈ entry.observation.auditClaims)
    (intrinsic : payload.Intrinsic) :
    row.ProductionJudges (program.acyclicPolicy .acyclic) entry.source
      (program.acyclicObservation payload) :=
  program.acyclicObservation_productionJudgesAt entryMem .acyclic familyEq payload claims
    intrinsic

/-- Entry-level general production judging.  The actual payload is obtained by `cases` on the
entry's own dependent payload, so the typed equality passed downstream is a real equality rather
than a caller-chosen payload paired with a pointwise claim subset. -/
theorem entry_general_productionJudges
    (program : P93CanonicalSourceProgram)
    (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    {row : Remaining71P93GeneralAuthorityRow}
    (clauseEq : entry.clause = .general row) :
    ∃ observation : (row.reference (program.generalPolicy .general)).Observation,
      row.ProductionJudges (program.generalPolicy .general) entry.source observation := by
  rcases entry with ⟨source, admitted, clause, listed, sourceObservation, transcription⟩
  dsimp only at clauseEq
  subst clause
  cases payloadEq : sourceObservation.payload with
  | general payload =>
      refine ⟨program.generalObservation payload, ?_⟩
      exact program.generalObservation_productionJudges source admitted row listed
        sourceObservation transcription payload payloadEq entryMem

theorem entry_noncarbon_productionJudges
    (program : P93CanonicalSourceProgram)
    (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    {row : Remaining71P93NoncarbonAuthorityRow}
    (clauseEq : entry.clause = .noncarbon row) :
    ∃ observation : (row.reference (program.noncarbonPolicy .noncarbon)).Observation,
      row.ProductionJudges (program.noncarbonPolicy .noncarbon) entry.source observation := by
  rcases entry with ⟨source, admitted, clause, listed, sourceObservation, transcription⟩
  dsimp only at clauseEq
  subst clause
  cases payloadEq : sourceObservation.payload with
  | noncarbon payload =>
      refine ⟨program.noncarbonObservation payload, ?_⟩
      apply program.noncarbonObservation_productionJudges entryMem rfl payload
      · intro claim claimMem
        simpa [P93ClauseObservation.auditClaims, payloadEq] using claimMem
      · simpa [P93ClausePayloadData.ValidFor, payloadEq] using sourceObservation.validFor.2

theorem entry_acyclic_productionJudges
    (program : P93CanonicalSourceProgram)
    (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    {row : Remaining71P93AcyclicAuthorityRow}
    (clauseEq : entry.clause = .acyclic row) :
    ∃ observation : (row.reference (program.acyclicPolicy .acyclic)).Observation,
      row.ProductionJudges (program.acyclicPolicy .acyclic) entry.source observation := by
  rcases entry with ⟨source, admitted, clause, listed, sourceObservation, transcription⟩
  dsimp only at clauseEq
  subst clause
  cases payloadEq : sourceObservation.payload with
  | acyclic payload =>
      refine ⟨program.acyclicObservation payload, ?_⟩
      apply program.acyclicObservation_productionJudges entryMem rfl payload
      · intro claim claimMem
        simpa [P93ClauseObservation.auditClaims, payloadEq] using claimMem
      · simpa [P93ClausePayloadData.ValidFor, payloadEq] using sourceObservation.validFor.2

/-- The single entry-level interface consumed by the exhaustive observation compiler. -/
def NoncyclicProductionWitness
    (program : P93CanonicalSourceProgram)
    (entry : P93CanonicalClauseObservationEntry) : Prop :=
  match entry.clause with
  | .general row =>
      ∃ observation : (row.reference (program.generalPolicy .general)).Observation,
        row.ProductionJudges (program.generalPolicy .general) entry.source observation
  | .noncarbon row =>
      ∃ observation : (row.reference (program.noncarbonPolicy .noncarbon)).Observation,
        row.ProductionJudges (program.noncarbonPolicy .noncarbon) entry.source observation
  | .acyclic row =>
      ∃ observation : (row.reference (program.acyclicPolicy .acyclic)).Observation,
        row.ProductionJudges (program.acyclicPolicy .acyclic) entry.source observation
  | _ => False

theorem entry_productionJudges_of_noncyclic
    (program : P93CanonicalSourceProgram)
    (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ program.observations)
    (family : entry.clause.family = .general ∨
      entry.clause.family = .noncarbon ∨ entry.clause.family = .acyclic) :
    program.NoncyclicProductionWitness entry := by
  generalize clauseEq : entry.clause = clause
  cases clause with
  | general row =>
      simpa [NoncyclicProductionWitness, clauseEq] using
        program.entry_general_productionJudges entry entryMem clauseEq
  | noncarbon row =>
      simpa [NoncyclicProductionWitness, clauseEq] using
        program.entry_noncarbon_productionJudges entry entryMem clauseEq
  | acyclic row =>
      simpa [NoncyclicProductionWitness, clauseEq] using
        program.entry_acyclic_productionJudges entry entryMem clauseEq
  | fullerene row | monocyclic row | vonBaeyer row | ringAssembly row | spiro row
  | coupledRingChain row =>
      simp [P93Clause.family, clauseEq] at family
  | fusedCyclophane row =>
      cases row <;> simp [P93Clause.family, clauseEq] at family
  | spiroNontetrahedral =>
      simp [P93Clause.family, clauseEq] at family

end P93CanonicalSourceProgram
end TetraStereo.OneCenter
