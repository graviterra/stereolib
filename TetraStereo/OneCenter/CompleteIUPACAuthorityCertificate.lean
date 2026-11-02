import TetraStereo.OneCenter.IUPACFixedGlobalProductionRefinement
import TetraStereo.OneCenter.IUPACGlobalNonDescriptorCanonicalSourceProgram
import TetraStereo.OneCenter.IUPACP94CanonicalAdoption

set_option autoImplicit false

/-!
# Generated complete IUPAC authority certificate

This is the root of the provision compiler.  Unlike the earlier abstract certificate, it does
not accept an independently authored ledger status function or a hand-maintained maturity tag.
Every terminal status is generated from the total compiler's audited disposition, a proof-relevant
whole-provision transcription certificate, and the seven semantic-family production/reference
correctness theorems.  The legacy maturity manifest is a downstream project-management view,
never an input to the complete authority theorem.
-/

namespace TetraStereo.OneCenter
namespace IUPACNormativeProvision

/-! ## Whole-provision transcription boundary -/











structure WholeProvisionTranscriptionComplete
    (reviewed : ReviewedProvisionSemanticsTable)
    (provision : IUPACNormativeProvision) : Prop where
  private mk ::
  sourceAudited : IUPACNormativeSource.ProvisionAuditComplete provision.source
  sourcePresent : (reviewed.row provision).sourceSuppliesRule = true
  referenceNonvacuous :
    ∃ input, ∃ observation : (reviewed.row provision).reference.Observation,
      reviewed.ChemicallyAdmitted input ∧
        (reviewed.row provision).reference.Applicable input ∧
          (reviewed.row provision).reference.Judges input observation

/-- The exact 152-row positive transcription certificate is audited in the three strategic work
units that own the implementation: primitive-35, the 46 descriptor-bearing rows of next-54, and
remaining-71. Its constructor is private; the 140 non-P-94 seals and twelve canonically adopted
P-94 seals are combined below into the sole full inhabitant issued by this module. -/
structure DescriptorBearingTranscriptionComplete
    (reviewed : ReviewedProvisionSemanticsTable) : Prop where
  private mk ::
  primitive35 : ∀ {provision}, provision ∈ primitive35Provisions →
    WholeProvisionTranscriptionComplete reviewed provision
  next54 : ∀ {provision}, provision ∈ next54DescriptorBearingProvisions →
    WholeProvisionTranscriptionComplete reviewed provision
  remaining71 : ∀ {provision}, provision ∈ remaining71DescriptorBearingProvisions →
    WholeProvisionTranscriptionComplete reviewed provision

namespace DescriptorBearingTranscriptionComplete

/-- Project the three nonempty, disjoint family audits to any of the exact 152 positive rows. -/
theorem every_descriptorBearing
    {reviewed : ReviewedProvisionSemanticsTable}
    (complete : DescriptorBearingTranscriptionComplete reviewed)
    (provision : IUPACNormativeProvision)
    (bearing : DescriptorAssignmentBearing provision) :
    WholeProvisionTranscriptionComplete reviewed provision := by
  rcases descriptorBearing_mem_reviewed81_or_remaining71 bearing with reviewed81 | remaining71
  · have firstTwo : provision ∈ primitive35Provisions ∨
        provision ∈ next54DescriptorBearingProvisions := by
      simpa [reviewed81DescriptorBearingProvisions] using reviewed81
    cases firstTwo with
    | inl primitive => exact complete.primitive35 primitive
    | inr next54 => exact complete.next54 next54
  · exact complete.remaining71 remaining71

end DescriptorBearingTranscriptionComplete

/-! ## Exact current transcription-seal issuance frontier -/

/-- The 140 descriptor-bearing rows whose reviewed authority programs are already frozen:
primitive-35, descriptor-bearing next-54, the canonical 56-row P-93 program, and the three
authority-data rows.  The twelve P-94 rows are deliberately absent. -/
def issuedNonP94DescriptorBearingProvisions : List IUPACNormativeProvision :=
  reviewed81DescriptorBearingProvisions ++
    remainingP93DescriptorProvisions ++
      descriptorAssignmentAuthorityDataProvisions

/-- The exact twelve-row P-94 transcription-seal scope. -/
def p94TranscriptionSealProvisions : List IUPACNormativeProvision :=
  p94SemanticsSlice

@[simp] theorem issued_nonP94_descriptorBearing_count :
    issuedNonP94DescriptorBearingProvisions.length = 140 := by
  simp [issuedNonP94DescriptorBearingProvisions,
    descriptorAssignmentAuthorityDataProvisions]

@[simp] theorem p94_transcription_seal_count :
    p94TranscriptionSealProvisions.length = 12 := by
  simp [p94TranscriptionSealProvisions]

set_option maxRecDepth 16384 in
theorem issued_nonP94_descriptorBearing_nodup :
    issuedNonP94DescriptorBearingProvisions.Nodup := by
  decide

theorem issued_nonP94_disjoint_p94 :
    issuedNonP94DescriptorBearingProvisions.Disjoint
      p94TranscriptionSealProvisions := by
  have remainingNodup :
      (remainingP93DescriptorProvisions ++
        (p94SemanticsSlice ++ descriptorAssignmentAuthorityDataProvisions)).Nodup := by
    simpa [remaining71DescriptorBearingProvisions] using
      remaining71DescriptorBearingProvisions_nodup
  have remainingP93DisjointTail :
      remainingP93DescriptorProvisions.Disjoint
        (p94SemanticsSlice ++ descriptorAssignmentAuthorityDataProvisions) :=
    List.disjoint_of_nodup_append remainingNodup
  have p94DisjointAuthority :
      p94SemanticsSlice.Disjoint descriptorAssignmentAuthorityDataProvisions :=
    List.disjoint_of_nodup_append (List.Nodup.of_append_right remainingNodup)
  rw [List.disjoint_left]
  intro provision issued p94
  change provision ∈ p94SemanticsSlice at p94
  simp only [issuedNonP94DescriptorBearingProvisions, List.mem_append] at issued
  rcases issued with (reviewed81 | remainingP93) | authorityData
  · exact (List.disjoint_left.mp reviewed81_disjoint_remaining71) reviewed81 (by
      simp [remaining71DescriptorBearingProvisions, p94])
  · exact (List.disjoint_left.mp remainingP93DisjointTail) remainingP93
      (List.mem_append_left _ p94)
  · exact (List.disjoint_left.mp p94DisjointAuthority) p94 authorityData

/-- Exact present seal partition: 140 issued family rows plus precisely the twelve P-94 rows. -/
theorem mem_issued_nonP94_or_p94_iff_descriptorBearing
    (provision : IUPACNormativeProvision) :
    provision ∈ issuedNonP94DescriptorBearingProvisions ∨
        provision ∈ p94TranscriptionSealProvisions ↔
      DescriptorAssignmentBearing provision := by
  have descriptorMembership :
      provision ∈ descriptorBearingReviewedSemanticsSlice ↔
        provision ∈ descriptorAssignmentBearingProvisions := by
    simpa using congrArg (fun provisions : Finset IUPACNormativeProvision =>
      provision ∈ provisions) descriptorBearingReviewedSemanticsScope_exact
  rw [← mem_descriptorAssignmentBearingProvisions_iff, ← descriptorMembership]
  simp only [issuedNonP94DescriptorBearingProvisions,
    p94TranscriptionSealProvisions,
    descriptorBearingReviewedSemanticsSlice_exact,
    reviewed81DescriptorBearingProvisions,
    remaining71DescriptorBearingProvisions, List.mem_append]
  aesop





noncomputable def issuedNonP94WholeProvisionTranscriptionComplete
    (negative : GlobalNonDescriptorReviewedSemantics)
    {provision : IUPACNormativeProvision}
    (member : provision ∈ issuedNonP94DescriptorBearingProvisions) :
    WholeProvisionTranscriptionComplete
      (parameterizedGlobalReviewedSemantics
        IUPACCanonicalDescriptorBearingPolicies negative).reviewed provision := by
  let global := parameterizedGlobalReviewedSemantics
    IUPACCanonicalDescriptorBearingPolicies negative
  have bearing : DescriptorAssignmentBearing provision :=
    (mem_issued_nonP94_or_p94_iff_descriptorBearing provision).1 (Or.inl member)
  have descriptorMember :
      provision ∈ descriptorBearingReviewedSemanticsSlice.toFinset := by
    rw [descriptorBearingReviewedSemanticsScope_exact]
    simpa using (mem_descriptorAssignmentBearingProvisions_iff provision).2 bearing
  exact WholeProvisionTranscriptionComplete.mk
    (global.source_audited provision)
    (global.descriptorBearing_source_present provision bearing)
    ((iupacCanonicalGlobalReviewedNonvacuity negative).nonvacuous
      provision descriptorMember)

/-- One proof-relevant package containing all 140 currently issuable private seals. -/
structure IssuedNonP94DescriptorBearingTranscriptionComplete
    (negative : GlobalNonDescriptorReviewedSemantics) : Prop where
  complete : ∀ {provision : IUPACNormativeProvision},
    provision ∈ issuedNonP94DescriptorBearingProvisions →
      WholeProvisionTranscriptionComplete
        (parameterizedGlobalReviewedSemantics
          IUPACCanonicalDescriptorBearingPolicies negative).reviewed provision

noncomputable def issuedNonP94DescriptorBearingTranscriptionComplete
    (negative : GlobalNonDescriptorReviewedSemantics) :
    IssuedNonP94DescriptorBearingTranscriptionComplete negative where
  complete := issuedNonP94WholeProvisionTranscriptionComplete negative

/-! ## Canonical P-94 and complete 152-row issuance -/




private noncomputable def issuedP94WholeProvisionTranscriptionComplete
    (negative : GlobalNonDescriptorReviewedSemantics)
    {provision : IUPACNormativeProvision}
    (member : provision ∈ p94TranscriptionSealProvisions) :
    WholeProvisionTranscriptionComplete
      (parameterizedGlobalReviewedSemantics
        IUPACCanonicalDescriptorBearingPolicies negative).reviewed provision := by
  let global := parameterizedGlobalReviewedSemantics
    IUPACCanonicalDescriptorBearingPolicies negative
  have bearing : DescriptorAssignmentBearing provision :=
    (mem_issued_nonP94_or_p94_iff_descriptorBearing provision).1 (Or.inr member)
  have descriptorMember :
      provision ∈ descriptorBearingReviewedSemanticsSlice.toFinset := by
    rw [descriptorBearingReviewedSemanticsScope_exact]
    simpa using (mem_descriptorAssignmentBearingProvisions_iff provision).2 bearing
  exact WholeProvisionTranscriptionComplete.mk
    (global.source_audited provision)
    (global.descriptorBearing_source_present provision bearing)
    ((iupacCanonicalGlobalReviewedNonvacuity negative).nonvacuous
      provision descriptorMember)

/-- The exact twelve-seal package produced by canonical P-94 adoption. -/
structure IssuedP94DescriptorBearingTranscriptionComplete
    (negative : GlobalNonDescriptorReviewedSemantics) : Prop where
  sourceProgramAdopted : P94CanonicalAdoption.AssembledProgramSourceFaithful
    P94CanonicalAdoption.canonicalSourceProgram.reviews
    P94CanonicalAdoption.canonicalSourceProgram.program
  complete : ∀ {provision : IUPACNormativeProvision},
    provision ∈ p94TranscriptionSealProvisions →
      WholeProvisionTranscriptionComplete
        (parameterizedGlobalReviewedSemantics
          IUPACCanonicalDescriptorBearingPolicies negative).reviewed provision

noncomputable def issuedP94DescriptorBearingTranscriptionComplete
    (negative : GlobalNonDescriptorReviewedSemantics) :
    IssuedP94DescriptorBearingTranscriptionComplete negative where
  sourceProgramAdopted := P94CanonicalAdoption.canonicalSourceProgram.sourceFaithful
  complete := issuedP94WholeProvisionTranscriptionComplete negative

private noncomputable def issuedWholeProvisionTranscriptionCompleteOfPartition
    (negative : GlobalNonDescriptorReviewedSemantics)
    {provision : IUPACNormativeProvision}
    (member : provision ∈ issuedNonP94DescriptorBearingProvisions ∨
      provision ∈ p94TranscriptionSealProvisions) :
    WholeProvisionTranscriptionComplete
      (parameterizedGlobalReviewedSemantics
        IUPACCanonicalDescriptorBearingPolicies negative).reviewed provision := by
  rcases member with issued | p94
  · exact issuedNonP94WholeProvisionTranscriptionComplete negative issued
  · exact (issuedP94DescriptorBearingTranscriptionComplete negative).complete p94

/-- Concrete private-constructor certificate for all 152 descriptor-bearing rows. The three family
fields are discharged by the exact 140/12 partition; no row-local seal is supplied by a caller. -/
noncomputable def iupacDescriptorBearingTranscriptionComplete
    (negative : GlobalNonDescriptorReviewedSemantics) :
    DescriptorBearingTranscriptionComplete
      (parameterizedGlobalReviewedSemantics
        IUPACCanonicalDescriptorBearingPolicies negative).reviewed where
  primitive35 := by
    intro provision member
    apply issuedWholeProvisionTranscriptionCompleteOfPartition negative
    left
    simp only [issuedNonP94DescriptorBearingProvisions,
      reviewed81DescriptorBearingProvisions, List.mem_append]
    exact Or.inl (Or.inl (Or.inl member))
  next54 := by
    intro provision member
    apply issuedWholeProvisionTranscriptionCompleteOfPartition negative
    left
    simp only [issuedNonP94DescriptorBearingProvisions,
      reviewed81DescriptorBearingProvisions, List.mem_append]
    exact Or.inl (Or.inl (Or.inr member))
  remaining71 := by
    intro provision member
    apply issuedWholeProvisionTranscriptionCompleteOfPartition negative
    simp only [issuedNonP94DescriptorBearingProvisions,
      p94TranscriptionSealProvisions,
      reviewed81DescriptorBearingProvisions,
      remaining71DescriptorBearingProvisions, List.mem_append] at member ⊢
    aesop

/-- Root certificate for the complete authority theorem.

The derived closure semantics is fixed by `compiler` and `interpreter`.  Constructing this
certificate requires the global 2,452-row compiler, proof-relevant whole-provision transcription
of all 152 positive rows, seven family correctness theorems, exact agreement with the independently
reviewed global table, and the exact 152/2,300 operational disposition partition.

The constructor is private to this module. Public clients can consume the fixed certificate issued
below but cannot manufacture one with an arbitrary interpreter. -/
structure CompleteIUPACAuthorityCertificate
    (reviewed : ReviewedProvisionSemanticsTable)
    {sourceCorpus : FrozenProvisionCorpus}
    (compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus)
    (interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus) : Prop where
  private mk ::
  sourceReferenceFaithful : ReviewedCorpusFaithful reviewed sourceCorpus
  transcriptionComplete : DescriptorBearingTranscriptionComplete reviewed
  kindClassificationExact : ∀ provision,
    (reviewed.row provision).kind = globalProvisionKind provision
  compilerCorrect : ProvisionCompilerCorrect compiler interpreter
  conformantExactlyDescriptorBearing : ∀ provision,
    (compiler.spec provision).disposition.IsConformant ↔
      DescriptorAssignmentBearing provision
  nonDescriptorNotApplicableExactlySourcePresent : ∀ provision,
    ¬DescriptorAssignmentBearing provision →
      ((compiler.spec provision).disposition.IsNotApplicable ↔
        sourceCorpus.SourceSuppliesRule provision)
  nonDescriptorSourceAbsentExactlySourceAbsent : ∀ provision,
    ¬DescriptorAssignmentBearing provision →
      ((compiler.spec provision).disposition.IsSourceAbsent ↔
        ¬sourceCorpus.SourceSuppliesRule provision)

/-! ## Fixed root issuer -/

noncomputable abbrev iupacCanonicalGlobalReviewedSemantics
    (negative : GlobalNonDescriptorReviewedSemantics) :=
  parameterizedGlobalReviewedSemantics IUPACCanonicalDescriptorBearingPolicies negative

noncomputable abbrev iupacCanonicalReviewedSemanticsTable
    (negative : GlobalNonDescriptorReviewedSemantics) : ReviewedProvisionSemanticsTable :=
  (iupacCanonicalGlobalReviewedSemantics negative).reviewed

noncomputable abbrev iupacCanonicalFrozenCorpus
    (negative : GlobalNonDescriptorReviewedSemantics) : FrozenProvisionCorpus :=
  (iupacCanonicalGlobalReviewedSemantics negative).toFrozenCorpus

noncomputable def iupacCanonicalProvisionCompiler
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ProvisionCompiler
      (globalDescriptorAssignmentProjection
        (iupacCanonicalFrozenCorpus negative)).toCorpus :=
  fixedGlobalProvisionCompiler IUPACCanonicalDescriptorBearingPolicies negative
    (iupacCanonicalGlobalReviewedNonvacuity negative)

noncomputable def iupacCanonicalProvisionInterpreter
    (negative : GlobalNonDescriptorReviewedSemantics) :
    ProvisionInterpreter
      (globalDescriptorAssignmentProjection
        (iupacCanonicalFrozenCorpus negative)).toCorpus :=
  fixedGlobalProvisionInterpreter IUPACCanonicalDescriptorBearingPolicies negative

/-- The only constructor call for the root certificate. It is private so callers cannot substitute
an arbitrary reviewed table, corpus, compiler, or interpreter. -/
private noncomputable def issueCompleteIUPACAuthorityCertificate
    (negative : GlobalNonDescriptorReviewedSemantics) :
    CompleteIUPACAuthorityCertificate
      (iupacCanonicalReviewedSemanticsTable negative)
      (iupacCanonicalProvisionCompiler negative)
      (iupacCanonicalProvisionInterpreter negative) := by
  let global := iupacCanonicalGlobalReviewedSemantics negative
  exact CompleteIUPACAuthorityCertificate.mk
    global.corpusFaithful
    (iupacDescriptorBearingTranscriptionComplete negative)
    global.classifier_exact
    (fixedGlobalProvisionCompilerCorrect
      IUPACCanonicalDescriptorBearingPolicies negative
      (iupacCanonicalGlobalReviewedNonvacuity negative))
    (fixedGlobalProvisionCompiler_conformant_iff_descriptorBearing
      IUPACCanonicalDescriptorBearingPolicies negative
      (iupacCanonicalGlobalReviewedNonvacuity negative))
    (fixedGlobalProvisionCompiler_notApplicable_iff_sourcePresent
      IUPACCanonicalDescriptorBearingPolicies negative
      (iupacCanonicalGlobalReviewedNonvacuity negative))
    (fixedGlobalProvisionCompiler_sourceAbsent_iff_sourceAbsent
      IUPACCanonicalDescriptorBearingPolicies negative
      (iupacCanonicalGlobalReviewedNonvacuity negative))

/-- Publicly consumable root certificate for the fixed canonical P-93/P-94 positive program and
the supplied independently reviewed non-descriptor semantics. Construction remains private. -/
noncomputable def completeIUPACAuthorityCertificate
    (negative : GlobalNonDescriptorReviewedSemantics) :
    CompleteIUPACAuthorityCertificate
      (iupacCanonicalReviewedSemanticsTable negative)
      (iupacCanonicalProvisionCompiler negative)
      (iupacCanonicalProvisionInterpreter negative) :=
  issueCompleteIUPACAuthorityCertificate negative

namespace CompleteIUPACAuthorityCertificate

/-- The corpus-owned family classifier of a complete certificate is the concrete exhaustive,
disjoint 2,452-row classifier, not a caller-selected total function. -/
theorem sourceGlobalKind_exact {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision) :
    sourceCorpus.kind provision = globalProvisionKind provision := by
  exact (certificate.sourceReferenceFaithful.exact provision).1.trans
    (certificate.kindClassificationExact provision)

/-- The operational projection inherits the same fixed classifier from its source corpus. -/
theorem operationalGlobalKind_exact {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision) :
    (globalDescriptorAssignmentProjection sourceCorpus).toCorpus.kind provision =
      globalProvisionKind provision :=
  certificate.sourceGlobalKind_exact provision

/-- Every positive compiler disposition carries the independent whole-provision transcription
seal for that exact row.  This projection is intentionally separate from compiler correctness. -/
theorem transcriptionComplete_of_conformant {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision)
    (conformant : (compiler.spec provision).disposition.IsConformant) :
    WholeProvisionTranscriptionComplete reviewed provision :=
  certificate.transcriptionComplete.every_descriptorBearing provision
    ((certificate.conformantExactlyDescriptorBearing provision).1 conformant)

/-- A compiler disposition is source-absent exactly when the independently reviewed source
program says that the authority supplies no rule.  Descriptor-bearing rows cannot enter this
branch because conformance itself carries source-presence evidence. -/
theorem disposition_sourceAbsent_iff_sourceAbsent {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision) :
    (compiler.spec provision).disposition.IsSourceAbsent ↔
      ¬sourceCorpus.SourceSuppliesRule provision := by
  by_cases bearing : DescriptorAssignmentBearing provision
  · have conformant :=
      (certificate.conformantExactlyDescriptorBearing provision).2 bearing
    constructor
    · intro sourceAbsent
      exact False.elim
        (ProvisionDisposition.not_conformant_of_sourceAbsent sourceAbsent conformant)
    · intro sourceAbsent
      have sourcePresent : sourceCorpus.SourceSuppliesRule provision := by
        change (globalDescriptorAssignmentProjection sourceCorpus).toCorpus.SourceSuppliesRule
          provision
        exact ProvisionDisposition.source_present_of_conformant conformant
      exact False.elim (sourceAbsent sourcePresent)
  · exact certificate.nonDescriptorSourceAbsentExactlySourceAbsent provision bearing

/-- A compiler disposition is not-applicable exactly for an operationally negative provision
whose independently reviewed authority rule is present. -/
theorem disposition_notApplicable_iff_nonDescriptor_sourcePresent
    {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision) :
    (compiler.spec provision).disposition.IsNotApplicable ↔
      ¬DescriptorAssignmentBearing provision ∧
        sourceCorpus.SourceSuppliesRule provision := by
  by_cases bearing : DescriptorAssignmentBearing provision
  · have conformant :=
      (certificate.conformantExactlyDescriptorBearing provision).2 bearing
    constructor
    · intro notApplicable
      exact False.elim
        (ProvisionDisposition.not_conformant_of_notApplicable notApplicable conformant)
    · intro impossible
      exact False.elim (impossible.1 bearing)
  · rw [certificate.nonDescriptorNotApplicableExactlySourcePresent provision bearing]
    simp [bearing]

private structure GeneratedAuthorityTerminalStatus
    {sourceCorpus : FrozenProvisionCorpus}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (provision : IUPACNormativeProvision) where
  status : ProvisionTerminalStatus (interpreter.toClosureSemantics compiler) provision
  isConformant_iff : status.IsConformant ↔
    (compiler.spec provision).disposition.IsConformant
  isNotApplicable_iff : status.IsNotApplicable ↔
    (compiler.spec provision).disposition.IsNotApplicable
  isSourceAbsent_iff : status.IsSourceAbsent ↔
    (compiler.spec provision).disposition.IsSourceAbsent

private def generatedAuthorityTerminalStatus {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision) :
    GeneratedAuthorityTerminalStatus (compiler := compiler)
      (interpreter := interpreter) provision := by
  cases dispositionEq : (compiler.spec provision).disposition with
  | conformant _sourcePresent _nonvacuous =>
      let conformant : (compiler.spec provision).disposition.IsConformant := by
        simp [ProvisionDisposition.IsConformant, dispositionEq]
      let transcription := certificate.transcriptionComplete_of_conformant
        provision conformant
      let status : ProvisionTerminalStatus
          (interpreter.toClosureSemantics compiler) provision :=
        .conformant transcription.sourceAudited
          ⟨conformant, certificate.compilerCorrect.every_provision_correct provision⟩
      exact
        { status := status
          isConformant_iff := by
            simp [status, ProvisionTerminalStatus.IsConformant,
              ProvisionDisposition.IsConformant, dispositionEq]
          isNotApplicable_iff := by
            simp [status, ProvisionTerminalStatus.IsNotApplicable,
              ProvisionDisposition.IsNotApplicable, dispositionEq]
          isSourceAbsent_iff := by
            simp [status, ProvisionTerminalStatus.IsSourceAbsent,
              ProvisionDisposition.IsSourceAbsent, dispositionEq] }
  | notApplicable _sourcePresent evidence =>
      let status : ProvisionTerminalStatus
          (interpreter.toClosureSemantics compiler) provision :=
        .notApplicable (compiler.spec provision).sourceAudited evidence
      exact
        { status := status
          isConformant_iff := by
            simp [status, ProvisionTerminalStatus.IsConformant,
              ProvisionDisposition.IsConformant, dispositionEq]
          isNotApplicable_iff := by
            simp [status, ProvisionTerminalStatus.IsNotApplicable,
              ProvisionDisposition.IsNotApplicable, dispositionEq]
          isSourceAbsent_iff := by
            simp [status, ProvisionTerminalStatus.IsSourceAbsent,
              ProvisionDisposition.IsSourceAbsent, dispositionEq] }
  | sourceAbsent evidence _inapplicable =>
      let status : ProvisionTerminalStatus
          (interpreter.toClosureSemantics compiler) provision :=
        .sourceAbsent (compiler.spec provision).sourceAudited evidence
      exact
        { status := status
          isConformant_iff := by
            simp [status, ProvisionTerminalStatus.IsConformant,
              ProvisionDisposition.IsConformant, dispositionEq]
          isNotApplicable_iff := by
            simp [status, ProvisionTerminalStatus.IsNotApplicable,
              ProvisionDisposition.IsNotApplicable, dispositionEq]
          isSourceAbsent_iff := by
            simp [status, ProvisionTerminalStatus.IsSourceAbsent,
              ProvisionDisposition.IsSourceAbsent, dispositionEq] }

/-- Generate the terminal proof object for one row directly from the compiler disposition.  No
coverage or semantic-maturity manifest is consulted.  The conformant branch can be reached only
after projecting both whole-provision transcription and production/reference correctness. -/
def terminalStatus {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision) :
    ProvisionTerminalStatus (interpreter.toClosureSemantics compiler) provision :=
  (generatedAuthorityTerminalStatus certificate provision).status


theorem sourceCoverage {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (_certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision) :
    IUPACNormativeSource.ProvisionAuditComplete provision.source :=
  (compiler.spec provision).sourceAudited







theorem noProvisionCompiler_under_current_source_audit
    {corpus : FrozenProvisionCorpus}
    (compiler : ProvisionCompiler corpus) : False := by
  have audited := (compiler.spec
    (.p10 .p101StereoparentCommonConfiguration)).sourceAudited
  have sourceEq :
      IUPACNormativeProvision.source
          (.p10 .p101StereoparentCommonConfiguration) =
        .blueBook2013P10 := rfl
  rw [sourceEq] at audited
  unfold IUPACNormativeSource.ProvisionAuditComplete at audited
  rw [IUPACNormativeSource.currentProvisionAuditChecklist] at audited
  unfold IUPACNormativeSource.ProvisionAuditChecklist.Complete at audited
  have figureReviewed := audited.2.2.1
  change false = true at figureReviewed
  exact Bool.noConfusion figureReviewed

/-- Direct root-level form of the current non-issuability theorem. -/
theorem impossible_under_current_source_audit {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (_certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter) : False :=
  noProvisionCompiler_under_current_source_audit compiler

/-- Every compiled row has a proof-bearing source-presence or source-absence disposition. -/
theorem independentRuleTranscription {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (_certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision) :
    (interpreter.toClosureSemantics compiler).SourceSuppliesRule provision ∨
      (interpreter.toClosureSemantics compiler).SourceAbsent provision := by
  cases dispositionEq : (compiler.spec provision).disposition with
  | conformant sourcePresent _ => exact Or.inl sourcePresent
  | notApplicable sourcePresent _ => exact Or.inl sourcePresent
  | sourceAbsent evidence _inapplicable => exact Or.inr evidence

/-- The requested root refinement equation.  This is extensional equality of the actual
`ProvisionInterpreter.Produces` relation and the canonical descriptor-assignment projection of
the independently reviewed source relation, not an equality between caller-selected functions. -/
theorem pipeline_eq_reference {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision)
    (input : AuthoritativeChemicalInput)
    (admitted : ((globalDescriptorAssignmentProjection sourceCorpus).toCorpus).ChemicallyAdmitted
      input) :
    interpreter.productionAssignments provision input =
      FrozenProvisionCorpus.referenceAssignments
        (globalDescriptorAssignmentProjection sourceCorpus).toCorpus provision input := by
  exact certificate.compilerCorrect.pipeline_eq_reference provision input admitted

/-- A compiled `notApplicable` row is operationally silent on every admitted input.  The
negative ledger status therefore cannot conceal production output. -/
theorem productionAssignments_eq_empty_of_notApplicable
    {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision)
    (notApplicable : (compiler.spec provision).disposition.IsNotApplicable)
    (input : AuthoritativeChemicalInput)
    (admitted : ((globalDescriptorAssignmentProjection sourceCorpus).toCorpus).ChemicallyAdmitted
      input) :
    interpreter.productionAssignments provision input = ∅ := by
  apply Set.ext
  intro observation
  change interpreter.Produces provision input observation ↔ False
  constructor
  · intro produced
    have expected := (certificate.compilerCorrect.every_provision_correct
      provision input admitted observation).mp produced
    exact (ProvisionDisposition.inapplicable_of_notApplicable notApplicable input admitted)
      expected.1
  · exact False.elim

/-- A compiled `sourceAbsent` row is also operationally silent on every admitted input.  Source
absence now freezes both authority inapplicability and empty production. -/
theorem productionAssignments_eq_empty_of_sourceAbsent
    {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision)
    (sourceAbsent : (compiler.spec provision).disposition.IsSourceAbsent)
    (input : AuthoritativeChemicalInput)
    (admitted : ((globalDescriptorAssignmentProjection sourceCorpus).toCorpus).ChemicallyAdmitted
      input) :
    interpreter.productionAssignments provision input = ∅ := by
  apply Set.ext
  intro observation
  change interpreter.Produces provision input observation ↔ False
  constructor
  · intro produced
    have expected := (certificate.compilerCorrect.every_provision_correct
      provision input admitted observation).mp produced
    exact (ProvisionDisposition.inapplicable_of_sourceAbsent sourceAbsent input admitted)
      expected.1
  · exact False.elim

/-- Generate the release proof-bearing ledger directly from the total operational compiler.  The
result contains exactly one terminal proof object for each of the 2,452 manifest rows. -/
def toTerminalLedger {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter) :
    ProvisionTerminalLedger (interpreter.toClosureSemantics compiler) where
  status := certificate.terminalStatus

/-- The generated status is conformant exactly for the audited 152-row descriptor-bearing
partition. -/
theorem toTerminalLedger_conformant_iff_descriptorBearing
    {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter) :
    ∀ provision,
      (certificate.toTerminalLedger.status provision).IsConformant ↔
        DescriptorAssignmentBearing provision := by
  intro provision
  exact (generatedAuthorityTerminalStatus certificate provision).isConformant_iff.trans
    (certificate.conformantExactlyDescriptorBearing provision)

/-- Generated terminal status is not-applicable exactly for a non-descriptor operation whose
source rule is present. -/
theorem toTerminalLedger_notApplicable_iff_nonDescriptor_sourcePresent
    {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision) :
    (certificate.toTerminalLedger.status provision).IsNotApplicable ↔
      ¬DescriptorAssignmentBearing provision ∧
        sourceCorpus.SourceSuppliesRule provision :=
  (generatedAuthorityTerminalStatus certificate provision).isNotApplicable_iff.trans
    (certificate.disposition_notApplicable_iff_nonDescriptor_sourcePresent provision)

/-- Generated terminal status is source-absent exactly when the audited source program supplies
no rule. -/
theorem toTerminalLedger_sourceAbsent_iff_sourceAbsent
    {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision) :
    (certificate.toTerminalLedger.status provision).IsSourceAbsent ↔
      ¬sourceCorpus.SourceSuppliesRule provision :=
  (generatedAuthorityTerminalStatus certificate provision).isSourceAbsent_iff.trans
    (certificate.disposition_sourceAbsent_iff_sourceAbsent provision)

/-- Every row is structurally terminal; there is no `open` constructor in the generated ledger. -/
theorem toTerminalLedger_complete {sourceCorpus : FrozenProvisionCorpus}
    {reviewed : ReviewedProvisionSemanticsTable}
    {compiler : ProvisionCompiler
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    {interpreter : ProvisionInterpreter
      (globalDescriptorAssignmentProjection sourceCorpus).toCorpus}
    (certificate : CompleteIUPACAuthorityCertificate reviewed compiler interpreter)
    (provision : IUPACNormativeProvision) :
    (certificate.toTerminalLedger.status provision).IsConformant ∨
      (certificate.toTerminalLedger.status provision).IsNotApplicable ∨
      (certificate.toTerminalLedger.status provision).IsSourceAbsent :=
  certificate.toTerminalLedger.complete provision

/-! The root issuer above is parameterized only by the independently reviewed non-descriptor
semantics. Canonical P-93/P-94 policies, all 152 positive transcription seals, the frozen corpus,
the compiler, and the interpreter are fixed internally. -/

end CompleteIUPACAuthorityCertificate














theorem nonempty_nonDescriptorSemantics_iff_completedSourceAudits
    (manifest : GlobalNonDescriptorCanonicalSourceManifest) :
    Nonempty GlobalNonDescriptorReviewedSemantics ↔
      Nonempty GlobalNonDescriptorCanonicalSourceManifest.CompletedSourceAudits := by
  constructor
  · rintro ⟨negative⟩
    exact ⟨{ complete := fun provision member => negative.reviewed.sourceAudited member }⟩
  · rintro ⟨audits⟩
    exact ⟨manifest.toReviewedSemantics audits⟩



theorem nonempty_completeIUPACAuthorityCertificate_of_completedSourceAudits
    (manifest : GlobalNonDescriptorCanonicalSourceManifest)
    (audits : GlobalNonDescriptorCanonicalSourceManifest.CompletedSourceAudits) :
    Nonempty
      (CompleteIUPACAuthorityCertificate
        (iupacCanonicalReviewedSemanticsTable (manifest.toReviewedSemantics audits))
        (iupacCanonicalProvisionCompiler (manifest.toReviewedSemantics audits))
        (iupacCanonicalProvisionInterpreter (manifest.toReviewedSemantics audits))) :=
  ⟨completeIUPACAuthorityCertificate (manifest.toReviewedSemantics audits)⟩





theorem not_nonempty_completedSourceAudits_of_open_source
    (provision : IUPACNormativeProvision)
    (member : provision ∈ globalNonDescriptorProvisions.toFinset)
    (openAudit : ¬IUPACNormativeSource.ProvisionAuditComplete provision.source) :
    ¬Nonempty GlobalNonDescriptorCanonicalSourceManifest.CompletedSourceAudits := by
  rintro ⟨audits⟩
  exact openAudit (audits.complete provision member)







theorem not_nonempty_completedSourceAudits_of_current_audit
    (manifest : GlobalNonDescriptorCanonicalSourceManifest) :
    ¬Nonempty GlobalNonDescriptorCanonicalSourceManifest.CompletedSourceAudits := by
  rintro ⟨audits⟩
  exact CompleteIUPACAuthorityCertificate.noProvisionCompiler_under_current_source_audit
    (iupacCanonicalProvisionCompiler (manifest.toReviewedSemantics audits))

end IUPACNormativeProvision
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.WholeProvisionTranscriptionComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.DescriptorBearingTranscriptionComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.DescriptorBearingTranscriptionComplete.every_descriptorBearing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.mem_issued_nonP94_or_p94_iff_descriptorBearing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.issuedNonP94WholeProvisionTranscriptionComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.issuedNonP94DescriptorBearingTranscriptionComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.issuedP94DescriptorBearingTranscriptionComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.iupacDescriptorBearingTranscriptionComplete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.completeIUPACAuthorityCertificate
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.sourceGlobalKind_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.noProvisionCompiler_under_current_source_audit
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.impossible_under_current_source_audit
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.operationalGlobalKind_exact
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.transcriptionComplete_of_conformant
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.disposition_sourceAbsent_iff_sourceAbsent
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.disposition_notApplicable_iff_nonDescriptor_sourcePresent
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.sourceCoverage
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.independentRuleTranscription
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.pipeline_eq_reference
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.productionAssignments_eq_empty_of_notApplicable
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.productionAssignments_eq_empty_of_sourceAbsent
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.toTerminalLedger_complete
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.toTerminalLedger_conformant_iff_descriptorBearing
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.toTerminalLedger_notApplicable_iff_nonDescriptor_sourcePresent
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.CompleteIUPACAuthorityCertificate.toTerminalLedger_sourceAbsent_iff_sourceAbsent
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.nonempty_nonDescriptorSemantics_iff_completedSourceAudits
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.nonempty_completeIUPACAuthorityCertificate_of_completedSourceAudits
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.not_nonempty_completedSourceAudits_of_open_source
assert_kernel_only
  TetraStereo.OneCenter.IUPACNormativeProvision.not_nonempty_completedSourceAudits_of_current_audit
