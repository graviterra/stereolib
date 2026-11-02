import TetraStereo.OneCenter.IUPACP93CanonicalSourceClaims

set_option autoImplicit false
















namespace TetraStereo.OneCenter

open IUPACNormativeProvision

namespace P93CanonicalSourceProgram

private theorem spiroExactClaim_sourceEnvelope
    {source : AuthoritativeChemicalInput}
    (payload : P93SpiroNontetrahedralPayload)
    (valid : payload.Intrinsic source)
    {claim : P93PhysicalClaim}
    (claimMem : claim ∈ payload.exactQualitativePhysicalClaims) :
    claim.SourceEnvelope source := by
  simp only [P93SpiroNontetrahedralPayload.exactQualitativePhysicalClaims,
    List.mem_cons, List.not_mem_nil, or_false] at claimMem
  subst claim
  exact valid.2.2.2.2.2.2.2.2.2.1

private theorem fusedCyclophaneExactClaim_sourceEnvelope
    {source : AuthoritativeChemicalInput}
    {row : Remaining71P93FusedCyclophaneAuthorityRow}
    (payload : P93FusedCyclophaneClausePayload row)
    (valid : payload.Intrinsic source)
    {claim : P93PhysicalClaim}
    (claimMem : claim ∈ payload.exactQualitativePhysicalClaims) :
    claim.SourceEnvelope source := by
  cases payload <;>
    simp_all [P93FusedCyclophaneClausePayload.exactQualitativePhysicalClaims,
      P93FusedCyclophaneClausePayload.Intrinsic,
      P93CanonicalCyclophanePlaneExecutableWitness.ValidFor,
      P93PhysicalClaim.SourceEnvelope]

private theorem reviewedEvidenceExactClaim_sourceEnvelope
    {source : AuthoritativeChemicalInput}
    (evidence : P93CanonicalReviewedDescriptorEvidence)
    (valid : evidence.ValidFor source)
    {claim : P93PhysicalClaim}
    (claimMem : claim ∈ evidence.exactQualitativePhysicalClaims) :
    claim.SourceEnvelope source := by
  cases evidence with
  | cyclophanePlane payload =>
      exact fusedCyclophaneExactClaim_sourceEnvelope payload valid.2 claimMem
  | spiroPolyhedral payload =>
      exact spiroExactClaim_sourceEnvelope payload valid.2 claimMem
  | acyclicCenter _ | acyclicDoubleBond _ | acyclicEvenCumulene _ | acyclicOddCumulene _
  | monocyclicAbsoluteCenter _ | monocyclicAchiralCenter _ | monocyclicDoubleBond _ _ _
  | fusedCIP _ | cyclophaneCenterCIP _ | cyclophaneCenterRelative _ _
  | cyclophaneDoubleBond _ _ | ringAssemblyAxis _ _ | ringAssemblyCenter _ _
  | ringAssemblyDoubleBond _ _ =>
      simp [P93CanonicalReviewedDescriptorEvidence.exactQualitativePhysicalClaims] at claimMem

private theorem coupledExactClaim_sourceEnvelope
    {source : AuthoritativeChemicalInput}
    (payload : P93CoupledClausePayload)
    (valid : payload.Intrinsic source)
    {claim : P93PhysicalClaim}
    (claimMem : claim ∈ payload.exactQualitativePhysicalClaims) :
    claim.SourceEnvelope source := by
  rcases List.mem_flatMap.mp claimMem with ⟨evidence, evidenceMem, exactMem⟩
  exact reviewedEvidenceExactClaim_sourceEnvelope evidence
    (valid.2.2.2.2.1 evidence evidenceMem) exactMem

theorem exactQualitativePhysicalClaim_sourceEnvelope
    {source : AuthoritativeChemicalInput} {clause : P93Clause}
    (observation : P93ClauseObservation source clause)
    {claim : P93PhysicalClaim}
    (claimMem : claim ∈ observation.payload.exactQualitativePhysicalClaims) :
    claim.SourceEnvelope source := by
  rcases observation with ⟨payload, valid⟩
  cases payload with
  | spiroNontetrahedral payload =>
      exact spiroExactClaim_sourceEnvelope payload valid.2 claimMem
  | fusedCyclophane payload =>
      exact fusedCyclophaneExactClaim_sourceEnvelope payload valid.2 claimMem
  | coupled payload =>
      exact coupledExactClaim_sourceEnvelope payload valid.2 claimMem
  | fullerene _ | noncarbon _ | general _ | monocyclic _ | vonBaeyer _
  | ringAssembly _ | acyclic _ | spiro _ =>
      simp [P93ClausePayloadData.exactQualitativePhysicalClaims] at claimMem

theorem physicalSupports_of_exactQualitativePhysicalClaim
    {source : AuthoritativeChemicalInput} {clause : P93Clause}
    (observation : P93ClauseObservation source clause)
    {claim : P93PhysicalClaim}
    (claimMem : claim ∈ observation.payload.exactQualitativePhysicalClaims) :
    P93SourceClaim.PhysicalSupports clause.family := by
  rcases observation with ⟨payload, _valid⟩
  cases payload with
  | spiroNontetrahedral _ => exact .spiro
  | coupled _ => exact .coupled
  | fusedCyclophane payload =>
      cases payload <;>
        simp_all [P93ClausePayloadData.exactQualitativePhysicalClaims,
          P93FusedCyclophaneClausePayload.exactQualitativePhysicalClaims]
      exact .cyclophane
  | fullerene _ | noncarbon _ | general _ | monocyclic _ | vonBaeyer _
  | ringAssembly _ | acyclic _ | spiro _ =>
      simp [P93ClausePayloadData.exactQualitativePhysicalClaims] at claimMem

/-- The irreducible local witness needed to synthesize supports for one observation.  It is
strictly smaller than a hand-written support list: the source, clause, unit inventory, exact-claim
inventory, and every list-membership proof are all fixed by `entry`. -/
structure ObservationSupportSynthesis
    (entry : P93CanonicalClauseObservationEntry) where
  qualitativeClaim : ∀ unit, unit ∈ entry.qualitativePhysicalUnits →
    { claim : P93PhysicalClaim //
      claim.unit = unit ∧ claim.SourceEnvelope entry.source ∧
        P93SourceClaim.PhysicalSupports entry.clause.family }

namespace ObservationSupportSynthesis

/-- Exact retained frames already contain every ingredient needed for qualitative support.  This
constructor removes the last local witness choice whenever the exact-frame inventory covers the
qualitative unit inventory by physical-unit projection. -/
def ofExactCoverage
    (entry : P93CanonicalClauseObservationEntry)
    (covered : ∀ unit, unit ∈ entry.qualitativePhysicalUnits →
      { claim : P93PhysicalClaim //
        claim ∈ entry.exactQualitativePhysicalClaims ∧ claim.unit = unit }) :
    ObservationSupportSynthesis entry where
  qualitativeClaim := by
    intro unit unitMem
    rcases covered unit unitMem with ⟨claim, claimMem, unitEq⟩
    exact ⟨claim, unitEq,
      exactQualitativePhysicalClaim_sourceEnvelope entry.observation claimMem,
      physicalSupports_of_exactQualitativePhysicalClaim entry.observation claimMem⟩

end ObservationSupportSynthesis

def qualitativeSupportsFor
    (entry : P93CanonicalClauseObservationEntry)
    (synthesis : ObservationSupportSynthesis entry) :
    List P93CanonicalPhysicalSupportEntry :=
  entry.qualitativePhysicalUnits.attach.map fun attached =>
    let selected := synthesis.qualitativeClaim attached.1 attached.2
    { source := entry.source
      sourceAdmitted := entry.sourceAdmitted
      clause := entry.clause
      claim := selected.1
      clauseListed := entry.clauseListed
      supports := selected.2.2.2
      sourceEnvelope := selected.2.2.1 }

def exactSupportsFor
    (entry : P93CanonicalClauseObservationEntry) :
    List P93CanonicalPhysicalSupportEntry :=
  entry.exactQualitativePhysicalClaims.attach.map fun attached =>
    { source := entry.source
      sourceAdmitted := entry.sourceAdmitted
      clause := entry.clause
      claim := attached.1
      clauseListed := entry.clauseListed
      supports := physicalSupports_of_exactQualitativePhysicalClaim
        entry.observation attached.2
      sourceEnvelope := exactQualitativePhysicalClaim_sourceEnvelope
        entry.observation attached.2 }

def supportsFor
    (entry : P93CanonicalClauseObservationEntry)
    (synthesis : ObservationSupportSynthesis entry) :
    List P93CanonicalPhysicalSupportEntry :=
  qualitativeSupportsFor entry synthesis ++ exactSupportsFor entry

def assembledPhysicalSupports
    (observations : List P93CanonicalClauseObservationEntry)
    (synthesis : ∀ entry, entry ∈ observations → ObservationSupportSynthesis entry) :
    List P93CanonicalPhysicalSupportEntry :=
  observations.attach.flatMap fun attached => supportsFor attached.1 (synthesis attached.1 attached.2)

theorem mem_qualitativeSupportsFor
    (entry : P93CanonicalClauseObservationEntry)
    (synthesis : ObservationSupportSynthesis entry)
    {unit : P93AuthorityPhysicalUnit}
    (unitMem : unit ∈ entry.qualitativePhysicalUnits) :
    ∃ support ∈ qualitativeSupportsFor entry synthesis,
      support.source = entry.source ∧ support.clause = entry.clause ∧
        support.claim.unit = unit := by
  let attached : { candidate // candidate ∈ entry.qualitativePhysicalUnits } := ⟨unit, unitMem⟩
  let selected := synthesis.qualitativeClaim unit unitMem
  let support : P93CanonicalPhysicalSupportEntry :=
    { source := entry.source
      sourceAdmitted := entry.sourceAdmitted
      clause := entry.clause
      claim := selected.1
      clauseListed := entry.clauseListed
      supports := selected.2.2.2
      sourceEnvelope := selected.2.2.1 }
  refine ⟨support, ?_, rfl, rfl, selected.2.1⟩
  exact List.mem_map.mpr ⟨attached, by simp [attached], rfl⟩

theorem mem_exactSupportsFor
    (entry : P93CanonicalClauseObservationEntry)
    {claim : P93PhysicalClaim}
    (claimMem : claim ∈ entry.exactQualitativePhysicalClaims) :
    ∃ support ∈ exactSupportsFor entry,
      support.source = entry.source ∧ support.clause = entry.clause ∧
        support.claim = claim := by
  let attached : { candidate // candidate ∈ entry.exactQualitativePhysicalClaims } :=
    ⟨claim, claimMem⟩
  let support : P93CanonicalPhysicalSupportEntry :=
    { source := entry.source
      sourceAdmitted := entry.sourceAdmitted
      clause := entry.clause
      claim := claim
      clauseListed := entry.clauseListed
      supports := physicalSupports_of_exactQualitativePhysicalClaim
        entry.observation claimMem
      sourceEnvelope := exactQualitativePhysicalClaim_sourceEnvelope
        entry.observation claimMem }
  refine ⟨support, ?_, rfl, rfl, rfl⟩
  exact List.mem_map.mpr ⟨attached, by simp [attached], rfl⟩

theorem mem_supportsFor_origin
    (entry : P93CanonicalClauseObservationEntry)
    (synthesis : ObservationSupportSynthesis entry)
    {support : P93CanonicalPhysicalSupportEntry}
    (supportMem : support ∈ supportsFor entry synthesis) :
    support.source = entry.source ∧ support.clause = entry.clause := by
  rcases List.mem_append.mp supportMem with qualitativeMem | exactMem
  · rcases List.mem_map.mp qualitativeMem with ⟨attached, _, supportEq⟩
    subst support
    exact ⟨rfl, rfl⟩
  · rcases List.mem_map.mp exactMem with ⟨attached, _, supportEq⟩
    subst support
    exact ⟨rfl, rfl⟩

theorem mem_assembledPhysicalSupports_origin
    {observations : List P93CanonicalClauseObservationEntry}
    (synthesis : ∀ entry, entry ∈ observations → ObservationSupportSynthesis entry)
    {support : P93CanonicalPhysicalSupportEntry}
    (supportMem : support ∈ assembledPhysicalSupports observations synthesis) :
    ∃ attached : { entry // entry ∈ observations },
      support ∈ supportsFor attached.1 (synthesis attached.1 attached.2) ∧
        support.source = attached.1.source ∧ support.clause = attached.1.clause := by
  rcases List.mem_flatMap.mp supportMem with ⟨attached, _attachedMem, localMem⟩
  have origin := mem_supportsFor_origin attached.1 (synthesis attached.1 attached.2) localMem
  exact ⟨attached, localMem, origin⟩

theorem mem_assembledPhysicalSupports_of_qualitative
    {observations : List P93CanonicalClauseObservationEntry}
    (synthesis : ∀ entry, entry ∈ observations → ObservationSupportSynthesis entry)
    {entry : P93CanonicalClauseObservationEntry} (entryMem : entry ∈ observations)
    {unit : P93AuthorityPhysicalUnit} (unitMem : unit ∈ entry.qualitativePhysicalUnits) :
    ∃ support ∈ assembledPhysicalSupports observations synthesis,
      support.source = entry.source ∧ support.clause = entry.clause ∧
        support.claim.unit = unit := by
  let attached : { candidate // candidate ∈ observations } := ⟨entry, entryMem⟩
  rcases mem_qualitativeSupportsFor entry (synthesis entry entryMem) unitMem with
    ⟨support, localMem, sourceEq, clauseEq, unitEq⟩
  refine ⟨support, ?_, sourceEq, clauseEq, unitEq⟩
  apply List.mem_flatMap.mpr
  refine ⟨attached, by simp [attached], ?_⟩
  exact List.mem_append_left _ localMem

theorem mem_assembledPhysicalSupports_of_exact
    {observations : List P93CanonicalClauseObservationEntry}
    (synthesis : ∀ entry, entry ∈ observations → ObservationSupportSynthesis entry)
    {entry : P93CanonicalClauseObservationEntry} (entryMem : entry ∈ observations)
    {claim : P93PhysicalClaim} (claimMem : claim ∈ entry.exactQualitativePhysicalClaims) :
    ∃ support ∈ assembledPhysicalSupports observations synthesis,
      support.source = entry.source ∧ support.clause = entry.clause ∧
        support.claim = claim := by
  let attached : { candidate // candidate ∈ observations } := ⟨entry, entryMem⟩
  rcases mem_exactSupportsFor entry claimMem with
    ⟨support, localMem, sourceEq, clauseEq, claimEq⟩
  refine ⟨support, ?_, sourceEq, clauseEq, claimEq⟩
  apply List.mem_flatMap.mpr
  refine ⟨attached, by simp [attached], ?_⟩
  exact List.mem_append_right _ localMem

/-- Build the complete finite source program without a separately maintained support list.

The family-scoped observation uniqueness invariant permits a source to be reused across distinct
families.  `supportedSourceClauseUnique` preserves that documented behavior: it constrains only a
second observation whose synthesized support list is nonempty, exactly when the source-program's
observation/support separation invariant needs the stronger conclusion. -/
def ofCompleteObservations
    (observations : List P93CanonicalClauseObservationEntry)
    (clausesCovered : ∀ clause ∈ P93Clause.all,
      ∃ entry ∈ observations, entry.clause = clause)
    (observationSourceUnique :
      ∀ first ∈ observations, ∀ second ∈ observations,
        first.source = second.source → first.clause.family = second.clause.family →
          first = second)
    (synthesis : ∀ entry, entry ∈ observations → ObservationSupportSynthesis entry)
    (supportedSourceClauseUnique :
      ∀ first (_firstMem : first ∈ observations),
        ∀ second (secondMem : second ∈ observations),
          supportsFor second (synthesis second secondMem) ≠ [] →
            first.source = second.source → first.clause = second.clause) :
    P93CanonicalSourceProgram where
  observations := observations
  physicalSupports := assembledPhysicalSupports observations synthesis
  clausesCovered := clausesCovered
  observationSourceUnique := observationSourceUnique
  supportSourceSeparated := by
    intro first firstMem second secondMem sourceEq
    rcases mem_assembledPhysicalSupports_origin synthesis firstMem with
      ⟨firstAttached, _firstLocalMem, firstSource, firstClause⟩
    rcases mem_assembledPhysicalSupports_origin synthesis secondMem with
      ⟨secondAttached, secondLocalMem, secondSource, secondClause⟩
    rw [firstClause, secondClause]
    apply supportedSourceClauseUnique firstAttached.1 firstAttached.2
      secondAttached.1 secondAttached.2
    · exact List.ne_nil_of_mem secondLocalMem
    rw [← firstSource, ← secondSource]
    exact sourceEq
  observationSupportSeparated := by
    intro observation observationMem support supportMem sourceEq
    rcases mem_assembledPhysicalSupports_origin synthesis supportMem with
      ⟨supportAttached, localMem, supportSource, supportClause⟩
    rw [supportClause]
    apply supportedSourceClauseUnique observation observationMem
      supportAttached.1 supportAttached.2
    · exact List.ne_nil_of_mem localMem
    rw [← supportSource]
    exact sourceEq
  qualitativePhysicalCovered := by
    intro observation observationMem unit unitMem
    exact mem_assembledPhysicalSupports_of_qualitative synthesis observationMem unitMem
  exactQualitativePhysicalCovered := by
    intro observation observationMem claim claimMem
    exact mem_assembledPhysicalSupports_of_exact synthesis observationMem claimMem

end P93CanonicalSourceProgram

end TetraStereo.OneCenter
