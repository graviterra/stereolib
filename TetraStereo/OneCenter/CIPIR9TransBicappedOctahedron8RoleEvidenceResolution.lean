import TetraStereo.OneCenter.CIPIR9TransBicappedOctahedron8MathematicalIndexIntegration

set_option autoImplicit false

namespace TetraStereo.OneCenter

namespace OCT8Executable

abbrev placementJudgment? :=
  RedBookIR9.TransBicappedOctahedron8ExecutableSpatialPerception.placementJudgment?

abbrev placementJudgment?_eq_true_iff :=
  RedBookIR9.TransBicappedOctahedron8ExecutableSpatialPerception.placementJudgment?_eq_true_iff

end OCT8Executable

/-!
# Explicit role-evidence resolution for molecular OCT-8

Exact affine OCT-8 coordinates can have more than one cap/base decomposition.  Choosing the
first accepted permutation would therefore be chemically unjustified.  This module makes the
missing information an explicit input: a duplicate-free ledger may contain one structural-role
placement for a canonical coordination-eight source record.  The placement is still checked by
the independent exact coordinate recognizer, and every molecular priority is still derived by the
IR-9.3.5/CIP pipeline.

The resulting analyzer resolves exactly the selected, validated placement.  Missing or ambiguous
ledger evidence, coordinate-ingress failure, priority failure, placement construction failure, and
geometric rejection are exposed as exhaustive refusal stages.  The emitted word remains the
complete mathematical OCT-8 symmetry index; no unpublished short index or `A`/`C` convention is
introduced.
-/

/-- An explicit structural-role placement attached to one canonical molecular source record. -/
structure TransBicappedOctahedron8RoleEvidence where
  record : IndexedIR9CoordinationSourceRecord
  placement : OCT8Executable.Placement
  deriving DecidableEq

/-- A proof-carrying ledger.  `Nodup` prevents a repeated identical entry from masquerading as a
unique observation; two different placements for one record are rejected by the unique lookup. -/
structure TransBicappedOctahedron8RoleEvidenceLedger where
  entries : List TransBicappedOctahedron8RoleEvidence
  nodup : entries.Nodup

/-- Independent meaning of one uniquely keyed role-evidence entry. -/
def TransBicappedOctahedron8RoleEvidenceJudgment
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (record : IndexedIR9CoordinationSourceRecord)
    (evidence : TransBicappedOctahedron8RoleEvidence) : Prop :=
  evidence ∈ ledger.entries ∧ evidence.record = record ∧
    ∀ other,
      other ∈ ledger.entries → other.record = record → other = evidence

/-- Return role evidence only when exactly one ledger entry is keyed by the source record. -/
def TransBicappedOctahedron8RoleEvidenceLedger.evidenceFor?
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (record : IndexedIR9CoordinationSourceRecord) :
    Option TransBicappedOctahedron8RoleEvidence :=
  RedBookIR9.FourCoordinateSpatialRoles.uniqueSatisfying? ledger.entries
    (fun evidence => evidence.record == record)

theorem transBicappedOctahedron8RoleEvidenceFor?_eq_some_iff
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (record : IndexedIR9CoordinationSourceRecord)
    (evidence : TransBicappedOctahedron8RoleEvidence) :
    ledger.evidenceFor? record = some evidence ↔
      TransBicappedOctahedron8RoleEvidenceJudgment ledger record evidence := by
  rw [TransBicappedOctahedron8RoleEvidenceLedger.evidenceFor?,
    RedBookIR9.FourCoordinateSpatialRoles.uniqueSatisfying?_eq_some_iff
      ledger.entries (fun current => current.record == record) ledger.nodup evidence]
  simp only [beq_iff_eq]
  exact Iff.rfl

/-- Semantic absence of a unique record-keyed role observation. -/
def TransBicappedOctahedron8RoleEvidenceUnavailable
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (record : IndexedIR9CoordinationSourceRecord) : Prop :=
  ∀ evidence,
    ¬ TransBicappedOctahedron8RoleEvidenceJudgment ledger record evidence

theorem transBicappedOctahedron8RoleEvidenceFor?_eq_none_iff_unavailable
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (record : IndexedIR9CoordinationSourceRecord) :
    ledger.evidenceFor? record = none ↔
      TransBicappedOctahedron8RoleEvidenceUnavailable ledger record := by
  cases computed : ledger.evidenceFor? record with
  | none =>
      refine ⟨fun _ evidence judged => ?_, fun _ => rfl⟩
      have present :=
        (transBicappedOctahedron8RoleEvidenceFor?_eq_some_iff
          ledger record evidence).mpr judged
      rw [computed] at present
      cases present
  | some evidence =>
      have judged :=
        (transBicappedOctahedron8RoleEvidenceFor?_eq_some_iff
          ledger record evidence).mp computed
      constructor
      · intro impossible
        cases impossible
      · intro unavailable
        exact (unavailable evidence judged).elim

/-! ## Exact per-record resolution -/

/-- Resolve the complete mathematical OCT-8 word for the unique explicit role placement, after
validating every preceding molecular and spatial stage. -/
noncomputable def IndexedIR9CoordinationSourceRecord.transBicappedOctahedron8RoleResolvedMathematicalIndex?
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger) :
    Option (List OCT8SourceIndex.PriorityDigit) := do
  let evidence ← ledger.evidenceFor? record
  let frame ← spatial.transBicappedOctahedron8Frame? record
  let priorities ← result.molecularPolyhedralPriorityNumbers?
    record.center .transBicappedOctahedron record.ligands
  let priorityPlacement ← eightPriorityPlacement? priorities
  if OCT8Executable.placementJudgment? frame evidence.placement then
    some (OCT8SourceIndex.completeIndex fun position =>
      priorityPlacement (OCT8Executable.donorIndexAt evidence.placement position))
  else
    none

/-- Independent conjunction for one successfully resolved role-evidence result. -/
def TransBicappedOctahedron8RoleResolvedMathematicalIndexJudgment
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (index : List OCT8SourceIndex.PriorityDigit) : Prop :=
  ∃ evidence frame priorities priorityPlacement,
    TransBicappedOctahedron8RoleEvidenceJudgment ledger record evidence ∧
    TransBicappedOctahedron8FrameJudgment spatial record frame ∧
    result.molecularPolyhedralPriorityNumbers?
      record.center .transBicappedOctahedron record.ligands = some priorities ∧
    EightPriorityPlacementJudgment priorities priorityPlacement ∧
    OCT8Executable.IsExactPlacement frame evidence.placement ∧
    index = OCT8SourceIndex.completeIndex (fun position =>
      priorityPlacement (OCT8Executable.donorIndexAt evidence.placement position))

theorem transBicappedOctahedron8RoleResolvedMathematicalIndex?_eq_some_iff
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (index : List OCT8SourceIndex.PriorityDigit) :
    record.transBicappedOctahedron8RoleResolvedMathematicalIndex?
        result spatial ledger = some index ↔
      TransBicappedOctahedron8RoleResolvedMathematicalIndexJudgment
        record result spatial ledger index := by
  constructor
  · intro computed
    unfold IndexedIR9CoordinationSourceRecord.transBicappedOctahedron8RoleResolvedMathematicalIndex? at computed
    cases evidenceEq : ledger.evidenceFor? record with
    | none => simp [evidenceEq] at computed
    | some evidence =>
        cases frameEq : spatial.transBicappedOctahedron8Frame? record with
        | none => simp [evidenceEq, frameEq] at computed
        | some frame =>
            cases prioritiesEq : result.molecularPolyhedralPriorityNumbers?
                record.center .transBicappedOctahedron record.ligands with
            | none => simp [evidenceEq, frameEq, prioritiesEq] at computed
            | some priorities =>
                cases placementEq : eightPriorityPlacement? priorities with
                | none => simp [evidenceEq, frameEq, prioritiesEq, placementEq] at computed
                | some priorityPlacement =>
                    have geometryTrue :
                        OCT8Executable.placementJudgment? frame evidence.placement = true := by
                      by_contra rejected
                      have geometryFalse :
                          OCT8Executable.placementJudgment? frame evidence.placement = false :=
                        Bool.eq_false_of_not_eq_true rejected
                      simp [evidenceEq, frameEq, prioritiesEq, placementEq,
                        geometryFalse] at computed
                    have indexEq :
                        OCT8SourceIndex.completeIndex (fun position =>
                          priorityPlacement
                            (OCT8Executable.donorIndexAt evidence.placement position)) = index := by
                      have computed' :
                          some (OCT8SourceIndex.completeIndex (fun position =>
                            priorityPlacement
                              (OCT8Executable.donorIndexAt evidence.placement position))) =
                            some index := by
                        simpa [evidenceEq, frameEq, prioritiesEq, placementEq,
                          geometryTrue] using computed
                      exact Option.some.inj computed'
                    exact ⟨evidence, frame, priorities, priorityPlacement,
                      (transBicappedOctahedron8RoleEvidenceFor?_eq_some_iff
                        ledger record evidence).mp evidenceEq,
                      (transBicappedOctahedron8Frame?_eq_some_iff
                        spatial record frame).mp frameEq,
                      prioritiesEq,
                      (eightPriorityPlacement?_eq_some_iff
                        priorities priorityPlacement).mp placementEq,
                      (OCT8Executable.placementJudgment?_eq_true_iff
                        frame evidence.placement).mp geometryTrue,
                      indexEq.symm⟩
  · rintro ⟨evidence, frame, priorities, priorityPlacement, evidenceJudged,
      frameJudged, prioritiesEq, placementJudged, geometryJudged, rfl⟩
    have evidenceEq :=
      (transBicappedOctahedron8RoleEvidenceFor?_eq_some_iff
        ledger record evidence).mpr evidenceJudged
    have frameEq :=
      (transBicappedOctahedron8Frame?_eq_some_iff
        spatial record frame).mpr frameJudged
    have placementEq :=
      (eightPriorityPlacement?_eq_some_iff
        priorities priorityPlacement).mpr placementJudged
    have geometryTrue :=
      (OCT8Executable.placementJudgment?_eq_true_iff
        frame evidence.placement).mpr geometryJudged
    simp [IndexedIR9CoordinationSourceRecord.transBicappedOctahedron8RoleResolvedMathematicalIndex?,
      evidenceEq, frameEq, prioritiesEq, placementEq, geometryTrue]

/-- Independent refusal: no complete role-evidence semantic judgment exists for any index. -/
def TransBicappedOctahedron8RoleResolvedMathematicalIndexRefused
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger) : Prop :=
  ∀ index,
    ¬ TransBicappedOctahedron8RoleResolvedMathematicalIndexJudgment
      record result spatial ledger index

theorem transBicappedOctahedron8RoleResolvedMathematicalIndex?_eq_none_iff_refused
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger) :
    record.transBicappedOctahedron8RoleResolvedMathematicalIndex?
        result spatial ledger = none ↔
      TransBicappedOctahedron8RoleResolvedMathematicalIndexRefused
        record result spatial ledger := by
  cases computed : record.transBicappedOctahedron8RoleResolvedMathematicalIndex?
      result spatial ledger with
  | none =>
      refine ⟨fun _ index judged => ?_, fun _ => rfl⟩
      have resolved :=
        (transBicappedOctahedron8RoleResolvedMathematicalIndex?_eq_some_iff
          record result spatial ledger index).mpr judged
      rw [computed] at resolved
      cases resolved
  | some index =>
      have judged :=
        (transBicappedOctahedron8RoleResolvedMathematicalIndex?_eq_some_iff
          record result spatial ledger index).mp computed
      constructor
      · intro impossible
        cases impossible
      · intro refused
        exact (refused index judged).elim

/-- The five exact operational refusal stages for role-evidence resolution. -/
def TransBicappedOctahedron8RoleResolvedOperationalRefusal
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger) : Prop :=
  ledger.evidenceFor? record = none ∨
  ∃ evidence,
    ledger.evidenceFor? record = some evidence ∧
    (spatial.transBicappedOctahedron8Frame? record = none ∨
    ∃ frame,
      spatial.transBicappedOctahedron8Frame? record = some frame ∧
      (result.molecularPolyhedralPriorityNumbers?
          record.center .transBicappedOctahedron record.ligands = none ∨
      ∃ priorities,
        result.molecularPolyhedralPriorityNumbers?
            record.center .transBicappedOctahedron record.ligands = some priorities ∧
        (eightPriorityPlacement? priorities = none ∨
        ∃ priorityPlacement,
          eightPriorityPlacement? priorities = some priorityPlacement ∧
          OCT8Executable.placementJudgment? frame evidence.placement = false)))

theorem transBicappedOctahedron8RoleResolvedMathematicalIndex?_eq_none_iff_operationalRefusal
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger) :
    record.transBicappedOctahedron8RoleResolvedMathematicalIndex?
        result spatial ledger = none ↔
      TransBicappedOctahedron8RoleResolvedOperationalRefusal
        record result spatial ledger := by
  unfold IndexedIR9CoordinationSourceRecord.transBicappedOctahedron8RoleResolvedMathematicalIndex?
  unfold TransBicappedOctahedron8RoleResolvedOperationalRefusal
  cases evidenceEq : ledger.evidenceFor? record with
  | none => simp
  | some evidence =>
      cases frameEq : spatial.transBicappedOctahedron8Frame? record with
      | none => simp
      | some frame =>
          cases prioritiesEq : result.molecularPolyhedralPriorityNumbers?
              record.center .transBicappedOctahedron record.ligands with
          | none => simp
          | some priorities =>
              cases placementEq : eightPriorityPlacement? priorities with
              | none => simp [placementEq]
              | some priorityPlacement =>
                  cases geometryEq :
                      OCT8Executable.placementJudgment? frame evidence.placement <;>
                    simp [placementEq, geometryEq]

theorem transBicappedOctahedron8RoleResolvedRefused_iff_operationalRefusal
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger) :
    TransBicappedOctahedron8RoleResolvedMathematicalIndexRefused
        record result spatial ledger ↔
      TransBicappedOctahedron8RoleResolvedOperationalRefusal
        record result spatial ledger := by
  rw [← transBicappedOctahedron8RoleResolvedMathematicalIndex?_eq_none_iff_refused,
    transBicappedOctahedron8RoleResolvedMathematicalIndex?_eq_none_iff_operationalRefusal]

/-! ## Conformance to the ambiguity-preserving candidate layer -/

/-- Every explicitly role-resolved result is one of the already exhaustive admitted candidates. -/
theorem transBicappedOctahedron8RoleResolved_candidate_mem
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (index : List OCT8SourceIndex.PriorityDigit)
    (resolved : record.transBicappedOctahedron8RoleResolvedMathematicalIndex?
      result spatial ledger = some index) :
    ∃ evidence candidate,
      TransBicappedOctahedron8RoleEvidenceJudgment ledger record evidence ∧
      candidate ∈ record.transBicappedOctahedron8MathematicalIndexCandidates result spatial ∧
      candidate.placement = evidence.placement ∧ candidate.index = index := by
  rcases (transBicappedOctahedron8RoleResolvedMathematicalIndex?_eq_some_iff
      record result spatial ledger index).mp resolved with
    ⟨evidence, frame, priorities, priorityPlacement, evidenceJudged, frameJudged,
      prioritiesEq, placementJudged, geometryJudged, indexEq⟩
  let candidate := transBicappedOctahedron8MathematicalIndexCandidateOf
    priorityPlacement evidence.placement
  have candidateJudged :
      TransBicappedOctahedron8MathematicalIndexCandidateJudgment
        record result spatial candidate :=
    ⟨frame, priorities, priorityPlacement, evidence.placement,
      frameJudged, prioritiesEq, placementJudged, geometryJudged, rfl⟩
  refine ⟨evidence, candidate, evidenceJudged,
    (mem_transBicappedOctahedron8MathematicalIndexCandidates_iff
      record result spatial candidate).mpr candidateJudged, rfl, ?_⟩
  exact indexEq.symm

/-- Every role-resolved result retains the full proof-relevant molecular IR-9.3.5 priority
certificate inherited from the admitted candidate layer. -/
theorem transBicappedOctahedron8RoleResolved_has_IR9_priority_certificate
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (index : List OCT8SourceIndex.PriorityDigit)
    (resolved : record.transBicappedOctahedron8RoleResolvedMathematicalIndex?
      result spatial ledger = some index) :
    ∃ candidate,
      candidate ∈ record.transBicappedOctahedron8MathematicalIndexCandidates result spatial ∧
      candidate.index = index ∧
      ∃ frame priorities priorityPlacement placement,
        TransBicappedOctahedron8FrameJudgment spatial record frame ∧
        TransBicappedOctahedron8MolecularIR9PriorityCertificate result record priorities ∧
        EightPriorityPlacementJudgment priorities priorityPlacement ∧
        OCT8Executable.IsExactPlacement frame placement ∧
        candidate = transBicappedOctahedron8MathematicalIndexCandidateOf
          priorityPlacement placement := by
  rcases transBicappedOctahedron8RoleResolved_candidate_mem
      record result spatial ledger index resolved with
    ⟨_evidence, candidate, _evidenceJudged, candidatePresent,
      _placementEq, candidateIndex⟩
  exact ⟨candidate, candidatePresent, candidateIndex,
    transBicappedOctahedron8MathematicalIndexCandidate_has_IR9_priority_certificate
      record result spatial candidate candidatePresent⟩

/-! ## Whole-molecule exact-once analysis -/

structure TransBicappedOctahedron8RoleResolvedMathematicalIndexAssignment where
  record : IndexedIR9CoordinationSourceRecord
  index : List OCT8SourceIndex.PriorityDigit
  deriving DecidableEq

noncomputable def IndexedIR9CoordinationSourceRecord.transBicappedOctahedron8RoleResolvedMathematicalIndexAssignment?
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger) :
    Option TransBicappedOctahedron8RoleResolvedMathematicalIndexAssignment :=
  (record.transBicappedOctahedron8RoleResolvedMathematicalIndex?
    result spatial ledger).map fun index => { record := record, index := index }

theorem transBicappedOctahedron8RoleResolvedMathematicalIndexAssignment?_eq_some_iff
    (record : IndexedIR9CoordinationSourceRecord)
    (result : ChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (assignment : TransBicappedOctahedron8RoleResolvedMathematicalIndexAssignment) :
    record.transBicappedOctahedron8RoleResolvedMathematicalIndexAssignment?
        result spatial ledger = some assignment ↔
      assignment.record = record ∧
      record.transBicappedOctahedron8RoleResolvedMathematicalIndex?
        result spatial ledger = some assignment.index := by
  rcases assignment with ⟨assignmentRecord, assignmentIndex⟩
  unfold IndexedIR9CoordinationSourceRecord.transBicappedOctahedron8RoleResolvedMathematicalIndexAssignment?
  cases computed : record.transBicappedOctahedron8RoleResolvedMathematicalIndex?
      result spatial ledger with
  | none => simp
  | some index => simp [eq_comm]

noncomputable def CertifiedChemistryNormalizationResult.analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger) :
    List TransBicappedOctahedron8RoleResolvedMathematicalIndexAssignment :=
  (certified.ir9CoordinationSourceRecords 8).filterMap fun record =>
    record.transBicappedOctahedron8RoleResolvedMathematicalIndexAssignment?
      certified.result spatial ledger

theorem mem_analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_iff
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (record : IndexedIR9CoordinationSourceRecord)
    (index : List OCT8SourceIndex.PriorityDigit) :
    ({ record := record, index := index } :
        TransBicappedOctahedron8RoleResolvedMathematicalIndexAssignment) ∈
        certified.analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices
          spatial ledger ↔
      record ∈ certified.ir9CoordinationSourceRecords 8 ∧
      record.transBicappedOctahedron8RoleResolvedMathematicalIndex?
        certified.result spatial ledger = some index := by
  unfold CertifiedChemistryNormalizationResult.analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨otherRecord, otherPresent, computed⟩
    have packaged :=
      (transBicappedOctahedron8RoleResolvedMathematicalIndexAssignment?_eq_some_iff
        otherRecord certified.result spatial ledger
        { record := record, index := index }).mp computed
    have recordEq : record = otherRecord := packaged.1
    subst otherRecord
    exact ⟨otherPresent, packaged.2⟩
  · rintro ⟨recordPresent, computed⟩
    exact ⟨record, recordPresent,
      (transBicappedOctahedron8RoleResolvedMathematicalIndexAssignment?_eq_some_iff
        record certified.result spatial ledger
        { record := record, index := index }).mpr ⟨rfl, computed⟩⟩

theorem mem_analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_iff_semantic
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (record : IndexedIR9CoordinationSourceRecord)
    (index : List OCT8SourceIndex.PriorityDigit) :
    ({ record := record, index := index } :
        TransBicappedOctahedron8RoleResolvedMathematicalIndexAssignment) ∈
        certified.analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices
          spatial ledger ↔
      record ∈ certified.ir9CoordinationSourceRecords 8 ∧
      TransBicappedOctahedron8RoleResolvedMathematicalIndexJudgment
        record certified.result spatial ledger index := by
  rw [mem_analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_iff,
    transBicappedOctahedron8RoleResolvedMathematicalIndex?_eq_some_iff]

theorem analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_nodup
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger) :
    (certified.analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices
      spatial ledger).Nodup := by
  unfold CertifiedChemistryNormalizationResult.analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices
  apply List.Nodup.filterMap
  · intro left right assignment leftComputed rightComputed
    have leftRecord :=
      (transBicappedOctahedron8RoleResolvedMathematicalIndexAssignment?_eq_some_iff
        left certified.result spatial ledger assignment).mp leftComputed |>.1
    have rightRecord :=
      (transBicappedOctahedron8RoleResolvedMathematicalIndexAssignment?_eq_some_iff
        right certified.result spatial ledger assignment).mp rightComputed |>.1
    exact leftRecord.symm.trans rightRecord
  · exact certified.ir9CoordinationSourceRecords_nodup 8

theorem analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_records_nodup
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger) :
    ((certified.analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices
      spatial ledger).map
        TransBicappedOctahedron8RoleResolvedMathematicalIndexAssignment.record).Nodup := by
  apply (analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_nodup
    certified spatial ledger).map_on
  intro left leftPresent right rightPresent recordEq
  rcases left with ⟨leftRecord, leftIndex⟩
  rcases right with ⟨rightRecord, rightIndex⟩
  simp only at recordEq ⊢
  have leftComputed :=
    (mem_analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_iff
      certified spatial ledger leftRecord leftIndex).mp leftPresent |>.2
  have rightComputed :=
    (mem_analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_iff
      certified spatial ledger rightRecord rightIndex).mp rightPresent |>.2
  subst rightRecord
  have indexEq : leftIndex = rightIndex :=
    Option.some.inj (leftComputed.symm.trans rightComputed)
  subst rightIndex
  rfl

theorem analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_count_eq_one
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (assignment : TransBicappedOctahedron8RoleResolvedMathematicalIndexAssignment)
    (present : assignment ∈
      certified.analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices
        spatial ledger) :
    List.count assignment
      (certified.analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices
        spatial ledger) = 1 := by
  exact List.count_eq_one_of_mem
    (analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_nodup
      certified spatial ledger) present

theorem scheduledRoleResolvedTransBicappedOctahedron8MathematicalIndex_refused_iff_operationalRefusal
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (record : IndexedIR9CoordinationSourceRecord)
    (recordPresent : record ∈ certified.ir9CoordinationSourceRecords 8) :
    (¬ ∃ index,
      ({ record := record, index := index } :
        TransBicappedOctahedron8RoleResolvedMathematicalIndexAssignment) ∈
        certified.analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices
          spatial ledger) ↔
      TransBicappedOctahedron8RoleResolvedOperationalRefusal
        record certified.result spatial ledger := by
  rw [← transBicappedOctahedron8RoleResolvedMathematicalIndex?_eq_none_iff_operationalRefusal]
  constructor
  · intro noEmission
    cases computed : record.transBicappedOctahedron8RoleResolvedMathematicalIndex?
        certified.result spatial ledger with
    | none => rfl
    | some index =>
        exfalso
        exact noEmission ⟨index,
          (mem_analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_iff
            certified spatial ledger record index).mpr ⟨recordPresent, computed⟩⟩
  · intro computed
    rintro ⟨index, emitted⟩
    have resolved :=
      (mem_analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_iff
        certified spatial ledger record index).mp emitted |>.2
    rw [computed] at resolved
    cases resolved

theorem scheduledRoleResolvedTransBicappedOctahedron8MathematicalIndex_refused_iff
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (record : IndexedIR9CoordinationSourceRecord)
    (recordPresent : record ∈ certified.ir9CoordinationSourceRecords 8) :
    (¬ ∃ index,
      ({ record := record, index := index } :
        TransBicappedOctahedron8RoleResolvedMathematicalIndexAssignment) ∈
        certified.analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices
          spatial ledger) ↔
      TransBicappedOctahedron8RoleResolvedMathematicalIndexRefused
        record certified.result spatial ledger := by
  rw [scheduledRoleResolvedTransBicappedOctahedron8MathematicalIndex_refused_iff_operationalRefusal
      certified spatial ledger record recordPresent,
    ← transBicappedOctahedron8RoleResolvedRefused_iff_operationalRefusal]

theorem scheduledRoleResolvedTransBicappedOctahedron8MathematicalIndex_exhaustive_operational
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (record : IndexedIR9CoordinationSourceRecord)
    (recordPresent : record ∈ certified.ir9CoordinationSourceRecords 8) :
    (∃! index,
      ({ record := record, index := index } :
        TransBicappedOctahedron8RoleResolvedMathematicalIndexAssignment) ∈
        certified.analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices
          spatial ledger) ∨
      TransBicappedOctahedron8RoleResolvedOperationalRefusal
        record certified.result spatial ledger := by
  cases computed : record.transBicappedOctahedron8RoleResolvedMathematicalIndex?
      certified.result spatial ledger with
  | none =>
      exact .inr
        ((transBicappedOctahedron8RoleResolvedMathematicalIndex?_eq_none_iff_operationalRefusal
          record certified.result spatial ledger).mp computed)
  | some index =>
      left
      refine ⟨index,
        (mem_analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_iff
          certified spatial ledger record index).mpr ⟨recordPresent, computed⟩, ?_⟩
      intro other otherPresent
      have otherComputed :=
        (mem_analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices_iff
          certified spatial ledger record other).mp otherPresent |>.2
      exact Option.some.inj (otherComputed.symm.trans computed)

theorem scheduledRoleResolvedTransBicappedOctahedron8MathematicalIndex_exhaustive
    (certified : CertifiedChemistryNormalizationResult) (spatial : SpatialConfiguration)
    (ledger : TransBicappedOctahedron8RoleEvidenceLedger)
    (record : IndexedIR9CoordinationSourceRecord)
    (recordPresent : record ∈ certified.ir9CoordinationSourceRecords 8) :
    (∃! index,
      ({ record := record, index := index } :
        TransBicappedOctahedron8RoleResolvedMathematicalIndexAssignment) ∈
        certified.analyzeRoleResolvedTransBicappedOctahedron8MathematicalIndices
          spatial ledger) ∨
      TransBicappedOctahedron8RoleResolvedMathematicalIndexRefused
        record certified.result spatial ledger := by
  rcases scheduledRoleResolvedTransBicappedOctahedron8MathematicalIndex_exhaustive_operational
      certified spatial ledger record recordPresent with emitted | refused
  · exact .inl emitted
  · exact .inr
      ((transBicappedOctahedron8RoleResolvedRefused_iff_operationalRefusal
        record certified.result spatial ledger).mpr refused)

end TetraStereo.OneCenter
