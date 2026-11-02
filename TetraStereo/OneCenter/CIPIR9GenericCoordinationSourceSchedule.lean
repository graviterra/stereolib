import TetraStereo.OneCenter.CIPIR9PentagonalBipyramid7SourcePerception
import TetraStereo.OneCenter.CIPIR9HexagonalBipyramid8SourcePerception
import TetraStereo.OneCenter.CIPIR9HeptagonalBipyramid9SourcePerception

set_option autoImplicit false

namespace TetraStereo.OneCenter

/-!
# Generic finite molecular source schedule for IR-9 coordination geometry

Shape-specific coordinate recognizers should not each reimplement molecular traversal.  This
module schedules, for an arbitrary coordination number `n`, exactly the bounded centers having
`n` canonical written bonded neighbours in the certified normalized graph.  It proves finite
exhaustiveness, record and ligand uniqueness, and atom bounds once.  Geometry remains an
independent coordinate judgment: the schedule supplies candidates, never a shape assertion.

The final three theorems prove that the generic schedule at coordination numbers seven, eight,
and nine is literally the already certified PBPY-7/HBPY-8/HBPY-9 source schedule after erasing the
generic coordination-number tag.  Thus future non-bipyramidal recognizers can share the same
molecule-to-coordinate seam without changing the behavior of existing analyzers.
-/

/-- A generic graph-derived IR-9 candidate.  The coordination-number field records which finite
schedule produced the record; `ligands` is always the canonical written-neighbour list. -/
structure IndexedIR9CoordinationSourceRecord where
  coordinationNumber : Nat
  center : Nat
  ligands : List Nat
  deriving DecidableEq, Repr

/-- Independent source-topology condition at arbitrary coordination number. -/
def SourceIR9CoordinationCenter
    (certified : CertifiedChemistryNormalizationResult)
    (coordinationNumber center : Nat) : Prop :=
  center < certified.result.parsed.atomCount ∧
    (certified.result.parsed.exactWrittenNeighbors center).length = coordinationNumber

instance (certified : CertifiedChemistryNormalizationResult)
    (coordinationNumber center : Nat) :
    Decidable (SourceIR9CoordinationCenter certified coordinationNumber center) := by
  unfold SourceIR9CoordinationCenter
  infer_instance

/-- Canonical generic source record at one center. -/
def CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecordAt
    (certified : CertifiedChemistryNormalizationResult)
    (coordinationNumber center : Nat) : IndexedIR9CoordinationSourceRecord :=
  { coordinationNumber := coordinationNumber
    center := center
    ligands := certified.result.parsed.exactWrittenNeighbors center }

/-- Exhaustive finite schedule at coordination number `coordinationNumber`. -/
def CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecords
    (certified : CertifiedChemistryNormalizationResult)
    (coordinationNumber : Nat) : List IndexedIR9CoordinationSourceRecord :=
  ((List.range certified.result.parsed.atomCount).filter fun center =>
      (certified.result.parsed.exactWrittenNeighbors center).length == coordinationNumber).map
    (certified.ir9CoordinationSourceRecordAt coordinationNumber)

/-- Exact membership in the arbitrary-coordination source schedule. -/
theorem CertifiedChemistryNormalizationResult.mem_ir9CoordinationSourceRecords_iff
    (certified : CertifiedChemistryNormalizationResult)
    (coordinationNumber : Nat)
    (record : IndexedIR9CoordinationSourceRecord) :
    record ∈ certified.ir9CoordinationSourceRecords coordinationNumber ↔
      ∃ center,
        SourceIR9CoordinationCenter certified coordinationNumber center ∧
        record = certified.ir9CoordinationSourceRecordAt coordinationNumber center := by
  unfold CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecords
  rw [List.mem_map]
  constructor
  · rintro ⟨center, centerPresent, rfl⟩
    have filtered := List.mem_filter.mp centerPresent
    exact ⟨center,
      ⟨by simpa using (List.mem_range.mp filtered.1), by simpa using filtered.2⟩,
      rfl⟩
  · rintro ⟨center, ⟨centerBound, exactLength⟩, rfl⟩
    exact ⟨center, List.mem_filter.mpr
      ⟨List.mem_range.mpr centerBound, by simp [exactLength]⟩, rfl⟩

/-- The canonical record at one center is present exactly when the independent source predicate
holds. -/
theorem CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecordAt_mem_iff
    (certified : CertifiedChemistryNormalizationResult)
    (coordinationNumber center : Nat) :
    certified.ir9CoordinationSourceRecordAt coordinationNumber center ∈
        certified.ir9CoordinationSourceRecords coordinationNumber ↔
      SourceIR9CoordinationCenter certified coordinationNumber center := by
  rw [certified.mem_ir9CoordinationSourceRecords_iff]
  constructor
  · rintro ⟨other, source, same⟩
    have centerEq : center = other := congrArg IndexedIR9CoordinationSourceRecord.center same
    simpa [centerEq] using source
  · intro source
    exact ⟨center, source, rfl⟩

/-- No generic schedule contains duplicate center/ligand records. -/
theorem CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecords_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (coordinationNumber : Nat) :
    (certified.ir9CoordinationSourceRecords coordinationNumber).Nodup := by
  unfold CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecords
  apply List.Nodup.map
  · intro first second same
    exact congrArg IndexedIR9CoordinationSourceRecord.center same
  · exact List.nodup_range.filter _

/-- Every scheduled center lies in the parsed atom range. -/
theorem SourceIR9CoordinationCenter.center_bounded
    (certified : CertifiedChemistryNormalizationResult)
    (coordinationNumber center : Nat)
    (source : SourceIR9CoordinationCenter certified coordinationNumber center) :
    center < certified.result.parsed.atomCount :=
  source.1

/-- A scheduled record has exactly its declared coordination number of ligands. -/
theorem SourceIR9CoordinationCenter.ligands_length
    (certified : CertifiedChemistryNormalizationResult)
    (coordinationNumber center : Nat)
    (source : SourceIR9CoordinationCenter certified coordinationNumber center) :
    (certified.ir9CoordinationSourceRecordAt coordinationNumber center).ligands.length =
      coordinationNumber :=
  source.2

/-- Every generic source record has a duplicate-free ligand list. -/
theorem SourceIR9CoordinationCenter.ligands_nodup
    (certified : CertifiedChemistryNormalizationResult)
    (coordinationNumber center : Nat)
    (_source : SourceIR9CoordinationCenter certified coordinationNumber center) :
    (certified.ir9CoordinationSourceRecordAt coordinationNumber center).ligands.Nodup := by
  exact certified.result.parsed.exactWrittenNeighbors_nodup center

/-- Every ligand in a generic source record lies in the parsed atom range. -/
theorem SourceIR9CoordinationCenter.ligands_bounded
    (certified : CertifiedChemistryNormalizationResult)
    (coordinationNumber center ligand : Nat)
    (_source : SourceIR9CoordinationCenter certified coordinationNumber center)
    (member : ligand ∈
      (certified.ir9CoordinationSourceRecordAt coordinationNumber center).ligands) :
    ligand < certified.result.parsed.atomCount := by
  exact certified.result.parsed.exactWrittenNeighbors_bound center ligand member

/-! ## Exact bridges to the existing higher-bipyramidal schedules -/

theorem sourceIR9CoordinationCenter_seven_iff_pentagonalBipyramid7
    (certified : CertifiedChemistryNormalizationResult) (center : Nat) :
    SourceIR9CoordinationCenter certified 7 center ↔
      SourcePentagonalBipyramid7Center certified center :=
  Iff.rfl

theorem sourceIR9CoordinationCenter_eight_iff_hexagonalBipyramid8
    (certified : CertifiedChemistryNormalizationResult) (center : Nat) :
    SourceIR9CoordinationCenter certified 8 center ↔
      SourceHexagonalBipyramid8Center certified center :=
  Iff.rfl

theorem sourceIR9CoordinationCenter_nine_iff_heptagonalBipyramid9
    (certified : CertifiedChemistryNormalizationResult) (center : Nat) :
    SourceIR9CoordinationCenter certified 9 center ↔
      SourceHeptagonalBipyramid9Center certified center :=
  Iff.rfl

/-- Forget the generic tag and expose the existing PBPY-7 raw-record type. -/
def IndexedIR9CoordinationSourceRecord.toPentagonalBipyramid7SpatialObservation
    (record : IndexedIR9CoordinationSourceRecord) :
    IndexedPentagonalBipyramid7SpatialObservation :=
  { center := record.center, ligands := record.ligands }

/-- Forget the generic tag and expose the existing HBPY-8 raw-record type. -/
def IndexedIR9CoordinationSourceRecord.toHexagonalBipyramid8SpatialObservation
    (record : IndexedIR9CoordinationSourceRecord) :
    IndexedHexagonalBipyramid8SpatialObservation :=
  { center := record.center, ligands := record.ligands }

/-- Forget the generic tag and expose the existing HBPY-9 raw-record type. -/
def IndexedIR9CoordinationSourceRecord.toHeptagonalBipyramid9SpatialObservation
    (record : IndexedIR9CoordinationSourceRecord) :
    IndexedHeptagonalBipyramid9SpatialObservation :=
  { center := record.center, ligands := record.ligands }

/-- The generic coordination-seven schedule is literally the existing PBPY-7 schedule after
erasing its generic tag. -/
theorem CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecords_seven_map_eq_pentagonalBipyramid7
    (certified : CertifiedChemistryNormalizationResult) :
    (certified.ir9CoordinationSourceRecords 7).map
        IndexedIR9CoordinationSourceRecord.toPentagonalBipyramid7SpatialObservation =
      certified.pentagonalBipyramid7SourceRecords := by
  simp [CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecords,
    CertifiedChemistryNormalizationResult.pentagonalBipyramid7SourceRecords,
    CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecordAt,
    CertifiedChemistryNormalizationResult.pentagonalBipyramid7SourceRecordAt,
    IndexedIR9CoordinationSourceRecord.toPentagonalBipyramid7SpatialObservation,
    List.map_map, Function.comp_def]

/-- The generic coordination-eight schedule is literally the existing HBPY-8 schedule after
erasing its generic tag. -/
theorem CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecords_eight_map_eq_hexagonalBipyramid8
    (certified : CertifiedChemistryNormalizationResult) :
    (certified.ir9CoordinationSourceRecords 8).map
        IndexedIR9CoordinationSourceRecord.toHexagonalBipyramid8SpatialObservation =
      certified.hexagonalBipyramid8SourceRecords := by
  simp [CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecords,
    CertifiedChemistryNormalizationResult.hexagonalBipyramid8SourceRecords,
    CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecordAt,
    CertifiedChemistryNormalizationResult.hexagonalBipyramid8SourceRecordAt,
    IndexedIR9CoordinationSourceRecord.toHexagonalBipyramid8SpatialObservation,
    List.map_map, Function.comp_def]

/-- The generic coordination-nine schedule is literally the existing HBPY-9 schedule after
erasing its generic tag. -/
theorem CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecords_nine_map_eq_heptagonalBipyramid9
    (certified : CertifiedChemistryNormalizationResult) :
    (certified.ir9CoordinationSourceRecords 9).map
        IndexedIR9CoordinationSourceRecord.toHeptagonalBipyramid9SpatialObservation =
      certified.heptagonalBipyramid9SourceRecords := by
  simp [CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecords,
    CertifiedChemistryNormalizationResult.heptagonalBipyramid9SourceRecords,
    CertifiedChemistryNormalizationResult.ir9CoordinationSourceRecordAt,
    CertifiedChemistryNormalizationResult.heptagonalBipyramid9SourceRecordAt,
    IndexedIR9CoordinationSourceRecord.toHeptagonalBipyramid9SpatialObservation,
    List.map_map, Function.comp_def]

end TetraStereo.OneCenter
