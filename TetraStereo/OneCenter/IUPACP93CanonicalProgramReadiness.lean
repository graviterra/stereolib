import TetraStereo.OneCenter.IUPACP93CanonicalProgramGeneralComplete
import TetraStereo.OneCenter.IUPACP93CanonicalProgramNoncarbonTextComplete
import TetraStereo.OneCenter.IUPACP93CanonicalProgramAcyclic
import TetraStereo.OneCenter.IUPACP93CanonicalProgramCyclic
import TetraStereo.OneCenter.IUPACP93CanonicalProgramCoupled
import TetraStereo.OneCenter.IUPACP93CanonicalProgramFullerene

set_option autoImplicit false










namespace TetraStereo.OneCenter

open IUPACNormativeProvision

namespace P93CanonicalProgramReadiness

noncomputable section

/-- The fifty audited non-fullerene entries. -/
def nonFullereneEntries : List P93CanonicalClauseObservationEntry :=
  P93CanonicalProgramGeneralComplete.entries ++
    P93CanonicalProgramNoncarbonTextComplete.entries ++
      P93CanonicalProgramAcyclic.entries ++ P93CanonicalProgramCyclic.entries ++
        P93CanonicalProgramCoupled.entries

/-- The six complete fullerene entries: methodology plus five relational release rows. -/
def fullereneEntries : List P93CanonicalClauseObservationEntry :=
  P93CanonicalProgramFullerene.entries

/-- All fifty-six provenance-bearing canonical entries. -/
def sourceAuditedEntries : List P93CanonicalClauseObservationEntry :=
  nonFullereneEntries ++ fullereneEntries

def nonFullereneClauses : List P93Clause :=
  nonFullereneEntries.map fun entry => entry.clause

def fullereneClauses : List P93Clause :=
  fullereneEntries.map fun entry => entry.clause

def sourceAuditedClauses : List P93Clause :=
  sourceAuditedEntries.map fun entry => entry.clause

/-- No source transcription remains externally blocked. -/
def externalGapClauses : List P93Clause := []

def readinessClauses : List P93Clause := sourceAuditedClauses ++ externalGapClauses

@[simp] theorem nonFullereneEntries_length : nonFullereneEntries.length = 50 := by
  simp [nonFullereneEntries]

@[simp] theorem fullereneEntries_length : fullereneEntries.length = 6 := by
  simp [fullereneEntries]

@[simp] theorem sourceAuditedEntries_length : sourceAuditedEntries.length = 56 := by
  simp [sourceAuditedEntries]

@[simp] theorem sourceAuditedClauses_length : sourceAuditedClauses.length = 56 := by
  simp [sourceAuditedClauses]

@[simp] theorem externalGapClauses_length : externalGapClauses.length = 0 := by
  rfl

@[simp] theorem readinessClauses_length : readinessClauses.length = 56 := by
  simp [readinessClauses]

/-- Clause identity is exact: the audited ledger and canonical universe have the same finite
carrier.  Order is intentionally family-module assembly order, not claimed to be canonical order. -/
theorem sourceAuditedClauses_canonical_exact :
    sourceAuditedClauses.toFinset = P93Clause.all.toFinset := by
  decide

theorem sourceAuditedClauses_nodup : sourceAuditedClauses.Nodup := by
  decide

/-- Exact canonical coverage, stated in the form consumed by `P93CanonicalSourceProgram`. -/
theorem sourceAudited_clause_covered
    (clause : P93Clause) (listed : clause ∈ P93Clause.all) :
    ∃ entry ∈ sourceAuditedEntries, entry.clause = clause := by
  have clauseInCanonical : clause ∈ P93Clause.all.toFinset := by
    simpa using listed
  have clauseInAudited : clause ∈ sourceAuditedClauses.toFinset := by
    rw [sourceAuditedClauses_canonical_exact]
    exact clauseInCanonical
  have clauseInList : clause ∈ sourceAuditedClauses := by
    simpa using clauseInAudited
  exact List.mem_map.mp clauseInList

/-! ## Family/source uniqueness without deciding relational source equality -/

/-- The legacy fifty-entry block remains a closed finite key table.  This decision never sees the
proof-carrying relational fullerene sources. -/
theorem nonFullereneEntryKeys_nodup :
    (nonFullereneEntries.map fun entry => (entry.clause.family, entry.source)).Nodup := by
  decide

theorem nonFullereneEntries_source_unique :
    ∀ first ∈ nonFullereneEntries, ∀ second ∈ nonFullereneEntries,
      first.source = second.source → first.clause.family = second.clause.family →
        first = second := by
  intro first firstMem second secondMem sourceEq familyEq
  exact (List.inj_on_of_nodup_map nonFullereneEntryKeys_nodup firstMem secondMem)
    (Prod.ext familyEq sourceEq)

/-- Every entry in the fifty-row block is definitionally outside the fullerene family. -/
private theorem nonFullereneEntry_family_ne_fullerene
    (entry : P93CanonicalClauseObservationEntry) (member : entry ∈ nonFullereneEntries) :
    entry.clause.family ≠ .fullerene := by
  have clauseMember : entry.clause ∈ nonFullereneClauses :=
    List.mem_map_of_mem member
  have allNonfullerene :
      ∀ clause ∈ nonFullereneClauses, clause.family ≠ .fullerene := by
    decide
  exact allNonfullerene entry.clause clauseMember

/-- Every entry in the six-row block belongs to the fullerene family. -/
private theorem fullereneEntry_family_exact
    (entry : P93CanonicalClauseObservationEntry) (member : entry ∈ fullereneEntries) :
    entry.clause.family = .fullerene := by
  have clauseMember : entry.clause ∈ fullereneClauses :=
    List.mem_map_of_mem member
  have allFullerene : ∀ clause ∈ fullereneClauses, clause.family = .fullerene := by
    decide
  exact allFullerene entry.clause clauseMember



theorem fullereneSources_nodup :
    (fullereneEntries.map fun entry => entry.source).Nodup := by
  exact P93CanonicalProgramFullerene.sources_nodup

/-- Exact `(family, source)` uniqueness for all fifty-six audited entries.  Same-source comparisons
never cross into the relational block: cross-block cases are eliminated by family discrimination,
and the six fullerene rows reuse their structural source-injectivity theorem. -/
theorem sourceAuditedEntries_source_unique :
    ∀ first ∈ sourceAuditedEntries, ∀ second ∈ sourceAuditedEntries,
      first.source = second.source → first.clause.family = second.clause.family →
        first = second := by
  intro first firstMem second secondMem sourceEq familyEq
  simp only [sourceAuditedEntries, List.mem_append] at firstMem secondMem
  rcases firstMem with firstNonfullerene | firstFullerene
  · rcases secondMem with secondNonfullerene | secondFullerene
    · exact nonFullereneEntries_source_unique first firstNonfullerene second
        secondNonfullerene sourceEq familyEq
    · exfalso
      exact nonFullereneEntry_family_ne_fullerene first firstNonfullerene
        (familyEq.trans (fullereneEntry_family_exact second secondFullerene))
  · rcases secondMem with secondNonfullerene | secondFullerene
    · exfalso
      exact nonFullereneEntry_family_ne_fullerene second secondNonfullerene
        (familyEq.symm.trans (fullereneEntry_family_exact first firstFullerene))
    · exact P93CanonicalProgramFullerene.observationSourceUnique first firstFullerene second
        secondFullerene sourceEq

theorem sourceAuditedEntryKeys_nodup :
    (sourceAuditedEntries.map fun entry => (entry.clause.family, entry.source)).Nodup := by
  have entriesNodup : sourceAuditedEntries.Nodup := by
    exact List.Nodup.of_map
      (fun entry : P93CanonicalClauseObservationEntry => entry.clause)
      sourceAuditedClauses_nodup
  apply (List.nodup_map_iff_inj_on entriesNodup).mpr
  intro first firstMem second secondMem keyEq
  exact sourceAuditedEntries_source_unique first firstMem second secondMem
    (congrArg Prod.snd keyEq) (congrArg Prod.fst keyEq)

@[simp] theorem externalGapClauses_exact : externalGapClauses = [] := rfl

theorem readinessClauses_nodup : readinessClauses.Nodup := by
  simpa [readinessClauses, externalGapClauses] using sourceAuditedClauses_nodup

/-- Readiness is now extensionally the complete canonical fifty-six-clause universe. -/
theorem readinessClauses_canonical_exact :
    readinessClauses.toFinset = P93Clause.all.toFinset := by
  simpa [readinessClauses, externalGapClauses] using sourceAuditedClauses_canonical_exact

end
end P93CanonicalProgramReadiness
end TetraStereo.OneCenter

assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramReadiness.sourceAuditedClauses_canonical_exact
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramReadiness.sourceAudited_clause_covered
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramReadiness.sourceAuditedEntries_source_unique
assert_kernel_only
  TetraStereo.OneCenter.P93CanonicalProgramReadiness.readinessClauses_canonical_exact
