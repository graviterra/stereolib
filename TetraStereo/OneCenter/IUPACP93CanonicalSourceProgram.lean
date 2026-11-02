import TetraStereo.OneCenter.IUPACP93CanonicalProgramReadiness
import TetraStereo.OneCenter.IUPACP93CanonicalSourceProgramAssembly

set_option autoImplicit false

/-!
# Frozen complete P-93 canonical source program

This module closes the source-program assembly boundary over the exact fifty-six-entry readiness
ledger.  Physical support is generated from retained exact frames; no caller supplies a support
list, semantic policy, or completeness premise.
-/

namespace TetraStereo.OneCenter

open IUPACNormativeProvision

namespace P93CanonicalSourceProgram

open P93CanonicalProgramReadiness

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
private theorem qualitative_entry_eq_tbpy
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ sourceAuditedEntries)
    {unit : P93AuthorityPhysicalUnit}
    (unitMem : unit ∈ entry.qualitativePhysicalUnits) :
    entry = P93CanonicalProgramVonBaeyerSpiro.tbpyEntry := by
  simp only [sourceAuditedEntries, nonFullereneEntries, fullereneEntries,
    P93CanonicalProgramGeneralComplete.entries,
    P93CanonicalProgramGeneral.entries,
    P93CanonicalProgramNoncarbonTextComplete.entries,
    P93CanonicalProgramNoncarbonTextComplete.remainingEntries,
    P93CanonicalProgramNoncarbonText.entries,
    P93CanonicalProgramAcyclic.entries,
    P93CanonicalProgramCyclic.entries,
    P93CanonicalProgramFusedCyclophane.entries,
    P93CanonicalProgramRingAssembly.entries,
    P93CanonicalProgramCoupled.entries,
    P93CanonicalProgramFullerene.entries,
    P93CanonicalProgramFullerene.relationalEntries,
    P93RelationalFullereneReleaseRow.all,
    List.map, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at entryMem
  repeat'
    first
    | rcases entryMem with entryMem | entryMem
  all_goals first | rfl | (change unit ∈ [] at unitMem; simp at unitMem)

private def sourceAuditedSupportSynthesis
    (entry : P93CanonicalClauseObservationEntry)
    (entryMem : entry ∈ sourceAuditedEntries) :
    ObservationSupportSynthesis entry :=
  ObservationSupportSynthesis.ofExactCoverage entry (by
    intro unit unitMem
    have entryEq := qualitative_entry_eq_tbpy entryMem unitMem
    subst entry
    refine ⟨P93PhysicalClaim.polyhedron 0 P93CanonicalProgramVonBaeyerSpiro.tbpyPositions
      .trigonalBipyramid P93CanonicalProgramVonBaeyerSpiro.tbpyFrame, ?_, ?_⟩
    · change (P93PhysicalClaim.polyhedron 0 P93CanonicalProgramVonBaeyerSpiro.tbpyPositions
        .trigonalBipyramid P93CanonicalProgramVonBaeyerSpiro.tbpyFrame) ∈
          [(P93PhysicalClaim.polyhedron 0 P93CanonicalProgramVonBaeyerSpiro.tbpyPositions
            .trigonalBipyramid P93CanonicalProgramVonBaeyerSpiro.tbpyFrame)]
      simp
    · symm
      simpa [P93CanonicalClauseObservationEntry.qualitativePhysicalUnits,
        P93ClauseObservation.auditClaims, P93ClausePayloadData.toClaims,
        P93SpiroNontetrahedralPayload.toClaims,
        P93SourceClaim.qualitativePhysicalUnits, P93SourceClaim.physicalUnits,
        P93SpiroClaim.physicalUnits,
        P93AuthorityPhysicalUnit.qualitativeOnly,
        P93CanonicalProgramVonBaeyerSpiro.tbpyEntry,
        P93CanonicalProgramVonBaeyerSpiro.mkEntry,
        P93CanonicalProgramVonBaeyerSpiro.tbpyObservation,
        P93CanonicalProgramVonBaeyerSpiro.tbpyPayload,
        P93SpiroNontetrahedralPayload.toClaims,
        P93SpiroNontetrahedralPayload.system,
        P93SpiroNontetrahedralPayload.positions,
        P93CanonicalProgramVonBaeyerSpiro.tbpyPrinted,
        P93CanonicalProgramVonBaeyerSpiro.tbpySystem] using unitMem)

set_option maxRecDepth 8192 in
private theorem supportBearing_entry
    {entry : P93CanonicalClauseObservationEntry}
    (entryMem : entry ∈ sourceAuditedEntries)
    (nonempty : supportsFor entry (sourceAuditedSupportSynthesis entry entryMem) ≠ []) :
    entry = P93CanonicalProgramVonBaeyerSpiro.tbpyEntry ∨
      entry = P93CanonicalProgramFusedCyclophane.cyclophanePlaneEntry := by
  simp only [sourceAuditedEntries, nonFullereneEntries, fullereneEntries,
    P93CanonicalProgramGeneralComplete.entries,
    P93CanonicalProgramGeneral.entries,
    P93CanonicalProgramNoncarbonTextComplete.entries,
    P93CanonicalProgramNoncarbonTextComplete.remainingEntries,
    P93CanonicalProgramNoncarbonText.entries,
    P93CanonicalProgramAcyclic.entries,
    P93CanonicalProgramCyclic.entries,
    P93CanonicalProgramFusedCyclophane.entries,
    P93CanonicalProgramRingAssembly.entries,
    P93CanonicalProgramCoupled.entries,
    P93CanonicalProgramFullerene.entries,
    P93CanonicalProgramFullerene.relationalEntries,
    P93RelationalFullereneReleaseRow.all,
    List.map, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at entryMem
  repeat'
    first
    | rcases entryMem with entryMem | entryMem
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | (exfalso; apply nonempty; rfl)

private theorem nonFullerene_support_source_clause :
    nonFullereneEntries.Forall fun entry =>
      (entry.source = P93CanonicalProgramVonBaeyerSpiro.tbpyEntry.source →
          entry.clause = P93CanonicalProgramVonBaeyerSpiro.tbpyEntry.clause) ∧
        (entry.source = P93CanonicalProgramFusedCyclophane.cyclophanePlaneEntry.source →
          entry.clause = P93CanonicalProgramFusedCyclophane.cyclophanePlaneEntry.clause) := by
  decide

set_option maxRecDepth 8192 in
private theorem fullerene_support_atomCount_separated :
    fullereneEntries.Forall fun entry =>
      (entry.source.molecule.atomCount ≠
          P93CanonicalProgramVonBaeyerSpiro.tbpyEntry.source.molecule.atomCount) ∧
        (entry.source.molecule.atomCount ≠
          P93CanonicalProgramFusedCyclophane.cyclophanePlaneEntry.source.molecule.atomCount) := by
  decide

private theorem supportedSourceClauseUnique :
    ∀ first (_firstMem : first ∈ sourceAuditedEntries),
      ∀ second (secondMem : second ∈ sourceAuditedEntries),
        supportsFor second (sourceAuditedSupportSynthesis second secondMem) ≠ [] →
          first.source = second.source → first.clause = second.clause := by
  intro first firstMem second secondMem nonempty sourceEq
  rcases supportBearing_entry secondMem nonempty with secondEq | secondEq
  · subst second
    simp only [sourceAuditedEntries, List.mem_append] at firstMem
    rcases firstMem with firstNonFullerene | firstFullerene
    · exact ((List.forall_iff_forall_mem.mp nonFullerene_support_source_clause)
        first firstNonFullerene).1 sourceEq
    · have separated :=
        ((List.forall_iff_forall_mem.mp fullerene_support_atomCount_separated)
          first firstFullerene).1
      exact False.elim (separated (congrArg (fun input => input.molecule.atomCount) sourceEq))
  · subst second
    simp only [sourceAuditedEntries, List.mem_append] at firstMem
    rcases firstMem with firstNonFullerene | firstFullerene
    · exact ((List.forall_iff_forall_mem.mp nonFullerene_support_source_clause)
        first firstNonFullerene).2 sourceEq
    · have separated :=
        ((List.forall_iff_forall_mem.mp fullerene_support_atomCount_separated)
          first firstFullerene).2
      exact False.elim (separated (congrArg (fun input => input.molecule.atomCount) sourceEq))

/-- The frozen, assumption-free source program over all fifty-six descriptor-bearing P-93 rows. -/
noncomputable def iupacP93CanonicalSourceProgram : P93CanonicalSourceProgram :=
  ofCompleteObservations sourceAuditedEntries sourceAudited_clause_covered
    sourceAuditedEntries_source_unique sourceAuditedSupportSynthesis
      supportedSourceClauseUnique

end P93CanonicalSourceProgram
end TetraStereo.OneCenter
